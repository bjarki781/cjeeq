/*
   Based on https://github.com/jackjack-jj/jeeq, GPLv3.
   Specifically designed to use Smileycoin key pairs for encoding/decoding so
   this is not as general as jeeq.py.

   */
#include <assert.h>
#include <string.h>
#include <stdio.h>
#include <stdbool.h>

#include <openssl/ec.h>
#include <openssl/bn.h>
#include <openssl/obj_mac.h>
#include <openssl/crypto.h>
#include <openssl/rand.h>
#include <openssl/sha.h>

//#include "key.h"
#include "jeeq.h"

// our secp256k1 curve
static EC_GROUP *group;

#define PRIVATE_HEADER_LEN      9
#define PUBLIC_HEADER_LEN       7
#define COMPR_PUBLIC_KEY_LEN    33
#define UNCOMPR_PUBLIC_KEY_LEN  65
#define CHUNK_SIZE              32
#define ORDER_HEX               "FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141"
#define MAX_256BIT_HEX          "FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF" 
#define MX_HEX                  "0379BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798"
// return private header on the form [version,1][length of checksum,2][checksum,6]
static unsigned char *PrivateHeader(unsigned char *ret, unsigned char *nmsg, int32_t msg_length, int8_t version)
{
    assert(version == 0);

    unsigned char hash[SHA256_DIGEST_LENGTH];
    SHA256(nmsg, msg_length, hash);

    ret[0] = version;
    ret[1] = 0x00;
    ret[2] = 0x06;
    // msg_length in big endian, find macros
    ret[3] = *((unsigned char*)&msg_length+3);
    ret[4] = *((unsigned char*)&msg_length+2);
    ret[5] = *((unsigned char*)&msg_length+1);
    ret[6] = *((unsigned char*)&msg_length+0);
    ret[7] = hash[0];
    ret[8] = hash[1];

    return ret;
}

// return a header on the form 6A6A[version,1][length of checksum,2][checksum,2]
static unsigned char *PublicHeader(unsigned char *ret, unsigned char *pub, int32_t pub_length, int8_t version)
{
    assert(version == 0);
    unsigned char hash[SHA256_DIGEST_LENGTH];

    SHA256(pub, pub_length, hash);

    ret[0] = 0x6a;
    ret[1] = 0x6a;
    ret[2] = version;
    ret[3] = 0x00;
    ret[4] = 0x02;
    ret[5] = hash[0];
    ret[6] = hash[1];

    return ret;
}


// enc needs to be of size PUBLIC_HEADER_LEN + 66*chunk_count
// return how many bytes written
size_t EncryptMessage(uint8_t *enc, uint8_t *pubkey, size_t pubkey_len, uint8_t *msg, size_t msg_len)
{
    assert(pubkey_len == COMPR_PUBLIC_KEY_LEN || pubkey_len == UNCOMPR_PUBLIC_KEY_LEN);

    BN_CTX *ctx = BN_CTX_new(); // used through the whole function as a temporary variable

    group = EC_GROUP_new_by_curve_name(NID_secp256k1);
    EC_POINT *pk = EC_POINT_new(group);

    // get so many blocks of 32B blocks that msg will fit
    // could be done with shifting but who cares
    int chunk_count = (PRIVATE_HEADER_LEN + msg_len)/32 + 1;

    uint8_t *m = OPENSSL_zalloc(chunk_count * CHUNK_SIZE);

    PrivateHeader(m, msg, msg_len, 0);
    memcpy(m, &msg[PRIVATE_HEADER_LEN], msg_len);

    BIGNUM *bn_pubkey = BN_new();

    BN_bin2bn(&pubkey[1], 32, bn_pubkey);
    //printf("bin2bn: %s\n", BN_bn2hex(bn_pubkey));

    if (pubkey_len == 33)
    {
        EC_POINT_set_compressed_coordinates_GFp(group, pk, bn_pubkey, pubkey[0]=='\x03', ctx);
     //   printf("pubkey: %s\n", EC_POINT_point2hex(group, pk, POINT_CONVERSION_COMPRESSED, ctx));
    }
    else if (pubkey_len == 65)
    {
        BIGNUM *bn_pubkey_extra = BN_new();

        BN_bin2bn(&pubkey[33], 32, bn_pubkey_extra);
        EC_POINT_set_affine_coordinates_GFp(group, pk, bn_pubkey, bn_pubkey_extra, ctx);

        BN_free(bn_pubkey_extra);
    }

    BIGNUM *rand = BN_new();

    PublicHeader(enc, pubkey, pubkey_len, 0);

    BIGNUM *order = BN_new();
    BN_hex2bn(&order, ORDER_HEX);
    EC_POINT *P = EC_POINT_new(group);
    EC_POINT_hex2point(group, MX_HEX, P, ctx);
    BIGNUM *cofactor = BN_new();
    BN_hex2bn(&cofactor, MAX_256BIT_HEX);
    BN_div(cofactor, NULL, cofactor, order, ctx);
    EC_GROUP_set_generator(group, P, order, cofactor);
    
    BIGNUM *Mx = BN_new();
    BIGNUM *My = BN_new();
    EC_POINT *M = EC_POINT_new(group);
    EC_POINT *T = EC_POINT_new(group);
    EC_POINT *U = EC_POINT_new(group);

    int enc_loc = PUBLIC_HEADER_LEN;
    size_t xoffset;

    // go through each 32byte block and encode it
    for (int i = 0; i < chunk_count; i++)
    {
        enc_loc += i*66;

        // double check correctness of these arguments
        BN_rand(rand, 250, -1, 0); 
        BN_bin2bn(m + i*32, 32, Mx);

        EC_POINT_set_compressed_coordinates_GFp(group, pk, Mx, true, ctx);

        EC_POINT_mul(group, T, NULL, P, rand, ctx);
        EC_POINT_mul(group, U, NULL, pk, rand, ctx);
        EC_POINT_add(group, U, U, M, ctx);

        EC_POINT_point2oct(group, T, POINT_CONVERSION_COMPRESSED, &enc[enc_loc], 33, ctx);
        EC_POINT_point2oct(group, U, POINT_CONVERSION_COMPRESSED, &enc[enc_loc+33], 33, ctx);

        //enc[enc_loc] = enc[enc_loc] - 2 + 2*xoffset; what happens here?
    }

    OPENSSL_clear_free(m, chunk_count * CHUNK_SIZE);
    EC_POINT_free(P);
    BN_free(rand);
    BN_free(Mx);
    BN_free(My);
    BN_free(bn_pubkey);
    BN_free(order);
    BN_free(cofactor);
    EC_POINT_free(M);
    EC_POINT_free(T);
    EC_POINT_free(U);
    EC_POINT_free(pk);
    BN_CTX_free(ctx);
    EC_GROUP_free(group);

    return enc_loc + 66;
}

// return how many bytes written
size_t DecryptMessage(uint8_t *msg, uint8_t *prvkey, uint8_t *enc, size_t enc_len)
{
    return -1;
}

int printn(unsigned char *str, int n)
{
    for (int i = 0; i < n; i++)
        putchar(str[i]);
    puts("");
}

int main(int argc, char *argv[])
{
    uint8_t *priv = "\x96\xf6\x82\x44\x02\xe3\xc9\x6f\x68\x24\x40\x2e\x3c\x96\xf6\x82\x44\x02\xe3\xc9\x6f\x68\x24\x40\x2e\x3c\x96\xf6\x82\x44\x02\xe3";
    uint8_t *pub = "\x03\x78\x30\xa7\x72\xda\xeb\x30\x1f\xdc\x53\x22\xc3\x17\x06\xd0\x71\x6c\x1a\x50\xe2\x73\xc6\x1b\x56\x3f\x62\x44\xb5\x14\x5b\x10\xdf";

    uint8_t enc[300];
    uint8_t dec[40];
    size_t enc_len, dec_len;

    char *msg = "Seagulls are green and blue.";
    char *encstr;
    char *decstr;

    enc_len = EncryptMessage(enc, pub, 33, msg, strlen(msg));
    encstr = OPENSSL_buf2hexstr(enc, enc_len);

    dec_len = DecryptMessage(dec, priv, enc, enc_len);
    decstr = OPENSSL_buf2hexstr(dec, dec_len);

    printf("original:  %s\n", msg);
    printf("encrypted:\n%s\n", encstr);
    printf("decrypted:\n%s\n", decstr);

    return 0;
}

