/*
   Based on https://github.com/jackjack-jj/jeeq, GPLv3.
   Specifically designed to use Smileycoin key pairs for encoding/decoding so
   this is not as general as jeeq.py.

   */
#include <assert.h>
#include <string.h>
#include <stdio.h>
#include <stdbool.h>
#include <endian.h>

#include <openssl/ec.h>
#include <openssl/bn.h>
#include <openssl/obj_mac.h>
#include <openssl/crypto.h>
#include <openssl/rand.h>
#include <openssl/sha.h>
#include <openssl/bio.h>

//#include "key.h"
#include "jeeq.h"

// our secp256k1 curve and bitcoin generator
static BIO *out;
static EC_GROUP *group;
static BN_CTX *ctx;
static BIGNUM *order;

#define PRIVATE_HEADER_LEN      9
#define PUBLIC_HEADER_LEN       7
#define PRIV_KEY_LEN            32
#define COMPR_PUBLIC_KEY_LEN    33
#define UNCOMPR_PUBLIC_KEY_LEN  65
#define CHUNK_SIZE              32
#define VERSION                 0
#define GX_HEX                  "79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798"
#define GY_HEX                  "483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8"
#define GCOFACTOR_HEX           "01"
#define GORDER_HEX              "FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141"

int printn(uint8_t *str, int n)
{
    for (int i = 0; i < n; i++)
        putchar(str[i]);
    puts("");
}

int init()
{
    BIGNUM *cofactor;
//    BIGNUM *order;
    EC_POINT *generator;

    ctx = BN_CTX_new();
    group = EC_GROUP_new_by_curve_name(NID_secp256k1);

    int rc = RAND_load_file("/dev/random", 32);
    assert(rc == 32);

    generator = EC_POINT_new(group);
    order = BN_new();
    cofactor = BN_new();

    BN_hex2bn(&order, GORDER_HEX);
    BN_hex2bn(&cofactor, GCOFACTOR_HEX);

    BIGNUM *Gx = BN_new();
    BIGNUM *Gy = BN_new();

    BN_hex2bn(&Gx, GX_HEX);
    BN_hex2bn(&Gy, GY_HEX);

    EC_POINT_set_affine_coordinates_GFp(group, generator, Gx, Gy, ctx);
    EC_GROUP_set_generator(group, generator, order, cofactor);

    BN_free(Gx);
    BN_free(Gy);
    BN_free(order);
    BN_free(cofactor);
    
    return 1;
}

int cleanup()
{
    BN_CTX_free(ctx);
    EC_GROUP_free(group);
    RAND_cleanup();

    return 1;
}

// return private header on the form [version,1][length of checksum,2][checksum,6]
    static uint8_t *write_private_header(uint8_t *ret, uint8_t *nmsg, uint32_t msg_length)
{
    uint8_t hash[SHA256_DIGEST_LENGTH];
    SHA256(nmsg, msg_length, hash);

    ret[0] = VERSION;
    ret[1] = 0x00;
    ret[2] = 0x06;
    // msg_length in big endian
    *(uint32_t*)&ret[3] = htobe32(msg_length);
    ret[7] = hash[0];
    ret[8] = hash[1];

    return ret;
}

// return a header on the form 6A6A[version,1][length of checksum,2][checksum,2]
static uint8_t *write_public_header(uint8_t *ret, uint8_t *pub, int32_t pub_length)
{
    uint8_t hash[SHA256_DIGEST_LENGTH];

    SHA256(pub, pub_length, hash);

    ret[0] = 0x6a;
    ret[1] = 0x6a;
    ret[2] = VERSION;
    ret[3] = 0x00;
    ret[4] = 0x02;
    ret[5] = hash[0];
    ret[6] = hash[1];

    return ret;
}

// return the message's length
static uint32_t read_private_header(uint8_t *str, BIGNUM* bn_prvkey, uint16_t pubkey_checksum)
{
    assert(str[0] == VERSION);
    assert(str[1] == 0x00);
    assert(str[2] == 0x06);

    uint32_t msg_length = be32toh(*(uint32_t*)&str[3]);
    uint16_t msg_hash = *(uint16_t*)&str[7];

    EC_POINT *pubkey_point = EC_POINT_new(group);
    EC_POINT_mul(group, pubkey_point, bn_prvkey, NULL, NULL, ctx);

    uint8_t *pubkey_compressed = OPENSSL_malloc(COMPR_PUBLIC_KEY_LEN);
    EC_POINT_point2oct(group, pubkey_point, POINT_CONVERSION_COMPRESSED, pubkey_compressed, COMPR_PUBLIC_KEY_LEN, ctx);

    uint8_t *pubkey_uncompressed = OPENSSL_malloc(UNCOMPR_PUBLIC_KEY_LEN);
    EC_POINT_point2oct(group, pubkey_point, POINT_CONVERSION_UNCOMPRESSED, pubkey_uncompressed, UNCOMPR_PUBLIC_KEY_LEN, ctx);

    uint8_t comppub_hash[SHA256_DIGEST_LENGTH];
    SHA256(pubkey_compressed, COMPR_PUBLIC_KEY_LEN, comppub_hash);
    uint16_t comppub_checksum = *((uint16_t*)comppub_hash);

    uint8_t uncomppub_hash[SHA256_DIGEST_LENGTH];
    SHA256(pubkey_uncompressed, UNCOMPR_PUBLIC_KEY_LEN, uncomppub_hash);
    uint16_t uncomppub_checksum = *((uint16_t*)uncomppub_hash);

    assert(uncomppub_checksum == pubkey_checksum || comppub_checksum == pubkey_checksum);

    OPENSSL_free(pubkey_compressed);
    OPENSSL_free(pubkey_uncompressed);
    EC_POINT_free(pubkey_point);
}

// take in the encoded byte vector and return the pubkey checksum
static uint16_t read_public_header(uint8_t *enc)
{
    assert(enc[0] == 0x6a);
    assert(enc[1] == 0x6a);
    assert(enc[2] == VERSION);
    assert(enc[3] == 0x00);
    assert(enc[4] == 0x02);

    return *(uint16_t*)&enc[5];
}

static int y_from_x(BIGNUM *y, size_t *offset, BIGNUM *x, const bool odd)
{
    EC_POINT *M = EC_POINT_new(group);

    // try to find y the easy way
    if (EC_POINT_set_compressed_coordinates_GFp(group, M, x, odd, ctx) == 1) 
    {
        EC_POINT_get_affine_coordinates_GFp(group, M, x, y, ctx);
        *offset = 0;
        EC_POINT_free(M);
        return 0;
    }

    BIGNUM *p = BN_new();
    BIGNUM *a = BN_new();
    BIGNUM *b = BN_new();

    EC_GROUP_get_curve_GFp(group, p, a, b, ctx);

    BIGNUM *Mx = BN_new();
    BIGNUM *My = BN_new();
    BIGNUM *My2 = BN_new();
    BIGNUM *aMx2 = BN_new();

    BIGNUM *half = BN_dup(p); // by putting a bignum into the special half power we get a square root
    BN_add_word(half, 1); 
    BN_div_word(half, 4);

    BN_copy(Mx, x);

    for (int i = 1; i < 128; i++)
    {
        BN_add_word(Mx, 1);   

        // My2 = (Mx^2 * Mx mod p)
        BN_sqr(My2, Mx, ctx);
        BN_mod_mul(My2, My2, Mx, p, ctx);

        BN_mod_sqr(aMx2, Mx, p, ctx);
        BN_mul(aMx2, aMx2, a, ctx);

        BN_mod(b, b, p, ctx);

        BN_add(My2, My2, aMx2);
        BN_add(My2, My2, b);

        BN_mod_exp(My, My2, half, p, ctx);

        EC_POINT_set_affine_coordinates_GFp(group, M, Mx, My, ctx);
        if (EC_POINT_is_on_curve(group, M, ctx))
        {
            if (odd == BN_is_bit_set(My, 0))
            {
                BN_copy(y, My);
                *offset = i;
            } 
            else 
            {
                BN_sub(y, p, My);
                *offset = i;
            }

            // collate
            BN_free(p);
            BN_free(a);
            BN_free(b);
            BN_free(Mx);
            BN_free(My);
            BN_free(My2);
            BN_free(aMx2);
            BN_free(half);

            return 0;
        }
    }

    BN_free(p);
    BN_free(a);
    BN_free(b);
    BN_free(Mx);
    BN_free(My);
    BN_free(My2);
    BN_free(aMx2);
    BN_free(half);

    return -1;
}


// enc needs to be of size PUBLIC_HEADER_LEN + 66*chunk_count
// return how many bytes written
size_t encrypt_message(uint8_t *enc, uint8_t *pubkey, size_t pubkey_len, uint8_t *msg, size_t msg_len)
{
    assert(pubkey_len == COMPR_PUBLIC_KEY_LEN || pubkey_len == UNCOMPR_PUBLIC_KEY_LEN);
    assert(pubkey[0] == '\x02' || pubkey[0] == '\x3' || pubkey[0] == '\x04');

    EC_POINT *pk = EC_POINT_new(group);

    // get so many blocks of 32B blocks that msg will fit
    // could be done with shifting but who cares
    int chunk_count = (PRIVATE_HEADER_LEN + msg_len)/CHUNK_SIZE + 1;

    uint8_t *m = OPENSSL_zalloc(chunk_count * CHUNK_SIZE);

    write_private_header(m, msg, msg_len);
    memcpy(&m[PRIVATE_HEADER_LEN], msg, msg_len);

    BIGNUM *bn_pubkey = BN_new();
    BN_bin2bn(&pubkey[1], 32, bn_pubkey);

    if (pubkey_len == 33)
    {
        EC_POINT_set_compressed_coordinates_GFp(group, pk, bn_pubkey, pubkey[0]=='\x03', ctx);
    }
    else if (pubkey_len == 65)
    {
        BIGNUM *bn_pubkey_extra = BN_new();

        BN_bin2bn(&pubkey[33], 32, bn_pubkey_extra);
        EC_POINT_set_affine_coordinates_GFp(group, pk, bn_pubkey, bn_pubkey_extra, ctx);

        BN_free(bn_pubkey_extra);
    }

    BIGNUM *rand = BN_new();
    BIGNUM *rand_range = BN_new();
    BIGNUM *Mx = BN_new();
    BIGNUM *My = BN_new();
    EC_POINT *M = EC_POINT_new(group);
    EC_POINT *T = EC_POINT_new(group);
    EC_POINT *U = EC_POINT_new(group);

    write_public_header(enc, pubkey, pubkey_len);
    int enc_loc = PUBLIC_HEADER_LEN;
    size_t xoffset = 0;

    // go through each 32byte block and encode it
    for (int i = 0; i < chunk_count; i++)
    {
        BN_copy(rand_range, order);
        BN_sub_word(rand_range, 1);
        BN_rand_range(rand, rand_range); 

        // since rand must be in [1,...,q-1]
        BN_add_word(rand, 1);
        //BN_mod(rand, rand, norder, ctx);

        BN_bin2bn(&m[i*CHUNK_SIZE], CHUNK_SIZE, Mx);

        int ret = y_from_x(My, &xoffset, Mx, true);
        assert(ret != -1);

        BN_add_word(Mx, xoffset);

        EC_POINT_set_affine_coordinates_GFp(group, M, Mx, My, ctx);

        EC_POINT_mul(group, T, rand, NULL, NULL, ctx);
        EC_POINT_mul(group, U, NULL, pk, rand, ctx);
        EC_POINT_add(group, U, U, M, ctx);

        EC_POINT_point2oct(group, T, POINT_CONVERSION_COMPRESSED, &enc[enc_loc], 33, ctx);
        EC_POINT_point2oct(group, U, POINT_CONVERSION_COMPRESSED, &enc[enc_loc+33], 33, ctx);
        
        enc[enc_loc] = enc[enc_loc] - 2 + (xoffset << 1);

        enc_loc += 66;
    }

    OPENSSL_clear_free(m, chunk_count * CHUNK_SIZE);
    BN_free(rand);
    BN_free(Mx);
    BN_free(My);
    BN_free(bn_pubkey);
    EC_POINT_free(M);
    EC_POINT_free(T);
    EC_POINT_free(U);
    EC_POINT_free(pk);

    return enc_loc;
}

// return how many bytes written
size_t decrypt_message(uint8_t *msg, uint8_t *prvkey, uint8_t *enc, size_t enc_len)
{
    BIGNUM *bn_prvkey = BN_new();
    BN_bin2bn(prvkey, PRIV_KEY_LEN, bn_prvkey);

    int chunk_count = (enc_len - PUBLIC_HEADER_LEN) / 66;

    uint8_t *r = OPENSSL_malloc(chunk_count * 32);

    uint8_t *Tser = OPENSSL_zalloc(33);
    uint8_t *User = OPENSSL_zalloc(33);
    int xoffset = 0;

    EC_POINT *T = EC_POINT_new(group);
    EC_POINT *U = EC_POINT_new(group);
    EC_POINT *M = EC_POINT_new(group);
    EC_POINT *V = EC_POINT_new(group);

    BIGNUM *Mx = BN_new();

    // assume that there is an subgroup order
    //BN_mod(bn_prvkey, bn_prvkey, norder, ctx);

    int enc_loc = PUBLIC_HEADER_LEN;
    int r_loc = 0;
    for (int i = 0; i < chunk_count; i++)
    {
        memcpy(Tser, &enc[enc_loc], 33);
        memcpy(User, &enc[enc_loc+33], 33);
        xoffset = Tser[0] >> 1;
        Tser[0] = 2 + (xoffset&1);
        EC_POINT_oct2point(group, T, Tser, 33, ctx);
        EC_POINT_oct2point(group, U, User, 33, ctx);

        EC_POINT_mul(group, V, NULL, T, bn_prvkey, ctx);
        EC_POINT_invert(group, V, ctx);
        EC_POINT_add(group, M, U, V, ctx);
        
        EC_POINT_get_affine_coordinates_GFp(group, M, Mx, NULL, ctx);

        BN_sub_word(Mx, xoffset);

        BN_bn2binpad(Mx, &r[r_loc], CHUNK_SIZE);

        r_loc += CHUNK_SIZE;
        enc_loc += 66;
    }


    assert(r[0] == '\x00'); 

    uint16_t pvh_len = be16toh(*(uint16_t*)(r+1));
    assert(pvh_len != 0);
    uint8_t *pvh = OPENSSL_malloc(pvh_len);
    memcpy(pvh, r+3, pvh_len);
    uint8_t size[4];
    size[3] = 0;
    size[2] = pvh[1];
    size[1] = pvh[2];
    size[0] = pvh[3];

    int32_t s = *(uint32_t*)size;

    uint16_t checksum = *(uint16_t*)(pvh + 4);
    memcpy(msg, r+3+pvh_len, s);
    uint8_t msghash[SHA256_DIGEST_LENGTH];
    SHA256(msg, s, msghash);
    assert(checksum == *((uint16_t*)msghash));

    return s;
}

int main(int argc, char *argv[])
{
    uint8_t *priv = "\x6a\x2a\xa3\x49\x8a\xaa\x46\xa2\xaa\x34\x98\xaa\xa4\x6a\x2a\xa3\x49\x8a\xaa\x46\xa2\xaa\x34\x98\xaa\xa4\x6a\x2a\xa3\x49\x8a\xaa";
    uint8_t *pub = "\03\x5c\xf3\x16\x10\xc5\x76\xd7\xe9\x47\xcc\x55\x09\xd3\x27\x27\x3e\xaa\x41\xc8\x1e\x2a\x73\x20\x93\x36\x02\x18\x6e\x04\x3d\x21\xc6";

    uint8_t enc[300];
    uint8_t dec[40];
    size_t enc_len, dec_len;

    char *msg = "Seagulls.";
    char *encstr;

    init();

    enc_len = encrypt_message(enc, pub, strlen(pub), msg, strlen(msg));
    encstr = OPENSSL_buf2hexstr(enc, enc_len);

    dec_len = decrypt_message(dec, priv, enc, enc_len);
    dec[dec_len] = '\0';

 //   printf("original:  %s\n", msg);
 //   printf("encrypted:\n%s\n", encstr);
    printf("decrypted: %s\n", dec);

    cleanup();

    return 0;
}

