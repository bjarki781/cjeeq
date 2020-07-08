/*
   Built on jeeq.py by jjack??? (link). GPLv3
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
#include <openssl/rand.h>
#include <openssl/sha.h>

//#include "key.h"
#include "jeeq.h"

// our secp256k1 curve
static EC_GROUP *group;

#define PRIVATE_HEADER_LEN      9
#define PUBLIC_HEADER_LEN       7

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

// y^2 - (x^3 + a*x + b) mod p == 0
static int curve_contains_point(BIGNUM *a, BIGNUM *b, BIGNUM *p, BIGNUM *x, BIGNUM *y)
{
    BIGNUM *y2 = BN_new();
    BIGNUM *x3 = BN_new();
    BIGNUM *ax = BN_new();

    BN_CTX *ctx = BN_CTX_new();
    
    BN_sqr(y2, y, ctx);
    BN_sqr(x3, x, ctx);
    BN_mul(x3, x3, x, ctx);
    BN_mul(ax, a, x, ctx);

    BN_sub(y2, y2, x3);
    BN_sub(y2, y2, ax);
    BN_sub(y2, y2, b);

    BN_mod(y2, y2, p, ctx);

    return BN_is_zero(y2);
}

static int YfromX(BIGNUM *y, size_t *offset, BIGNUM *x, bool odd)
{
    BIGNUM *p = BN_new();
    BIGNUM *a = BN_new();
    BIGNUM *b = BN_new();
    BIGNUM *bn_i = BN_new();
    BN_CTX *ctx = BN_CTX_new();

    EC_GROUP_get_curve_GFp(group, p, a, b, ctx);

    BIGNUM *Mx = BN_new();
    BIGNUM *My = BN_new();
    BIGNUM *My2 = BN_new();

    BIGNUM *tmp = BN_new();
    BIGNUM *half = BN_dup(p); // by putting a bignum into the special half power we get a square root
    BN_add_word(half, 1); 
    BN_div_word(half, 4);

    // why 128?
    BN_zero(bn_i);
    for (int i = 0; i < 128; i++)
    {
        // redo algorithm
        BN_add(Mx, x, bn_i);   
        BN_mod_mul(My2, Mx, Mx, p, ctx);
        BN_mod_mul(My2, My2, Mx, p, ctx);
        BN_mod_mul(My2, My2, Mx, p, ctx);

        BN_mod_sqr(tmp, Mx, tmp, ctx);
        BN_mul(tmp, tmp, a, ctx);
        BN_mod(b, b, p, ctx);
        BN_add(My2, My2, tmp);
        BN_add(My2, My2, b);

        BN_mod_exp(My, My2, half, p, ctx);

        if (curve_contains_point(a, b, p, Mx, My))
        {
            if (odd && BN_is_bit_set(My, 0))
            {
                BN_copy(y, My);
                *offset = i;
                return 0;
            } 
            else if (!odd && !BN_is_bit_set(My, 0))
            {
                BN_sub(y, p, My);
                *offset = i;
                return 0;
            }
        }

        BN_add_word(bn_i, 1);
    }

    assert("no y found");
    return -1;
}

// enc needs to be of size PUBLIC_HEADER_LEN + 66*chunk_count
// return how many bytes written
size_t EncryptMessage(uint8_t *enc, uint8_t *pubkey, size_t pubkey_len, uint8_t *msg, size_t msg_len)
{
    BN_CTX *ctx = BN_CTX_new(); // used through the whole function as a temporary variable

    group = EC_GROUP_new_by_curve_name(NID_secp256k1);
    EC_POINT *pk = EC_POINT_new(group);

    // consider openssl_malloc
    uint8_t *m = malloc(msg_len + PRIVATE_HEADER_LEN);
    PrivateHeader(m, msg, msg_len, 0);
    memcpy(m, msg + PRIVATE_HEADER_LEN, msg_len);

    BIGNUM *bn_pubkey = BN_new();
    size_t xoffset;

    BN_bin2bn(pubkey + 1, 33, bn_pubkey);

    if (pubkey_len == 33)
    {
        BIGNUM *y_from_pubkey = BN_new();

        YfromX(y_from_pubkey, &xoffset, bn_pubkey, pubkey[0]=='\x03');
        EC_POINT_set_affine_coordinates_GFp(group, pk, bn_pubkey, y_from_pubkey, ctx);

        BN_free(y_from_pubkey);
    }
    else if (pubkey_len == 65)
    {
        BIGNUM *bn_pubkey_extra = BN_new();

        BN_bin2bn(pubkey + 33, 32, bn_pubkey);
        //EC_POINT_set_affine_coordinates_GFp(group, pk, bn_pubkey, bn_pubkey_extra);

        BN_free(bn_pubkey_extra);
    }
    else
    {
        assert(false);
    }

    BIGNUM *rand = BN_new();

    PublicHeader(enc, pubkey, pubkey_len, 0);

    EC_POINT *p = EC_POINT_new(group);
    BIGNUM *n = BN_new();
    BIGNUM *Mx = BN_new();
    BIGNUM *My = BN_new();
    EC_POINT *M = EC_POINT_new(group);
    EC_POINT *T = EC_POINT_new(group);
    EC_POINT *U = EC_POINT_new(group);

    size_t chunk_count = (PRIVATE_HEADER_LEN + msg_len) / 32;
    // go through each 32byte block and encode it
    for (int i = 0; i < chunk_count; i++)
    {
        int loc = PUBLIC_HEADER_LEN + i*66;
        BN_rand(rand, 63, -1, 0); // double check that 63 bytes encompasses bitcoin curve order
        BN_bin2bn(&m[i*32], 32, Mx);

        assert(YfromX(My, &xoffset, Mx, true) != -1);

        EC_POINT_mul(group, T, NULL, p, n, ctx);
        EC_POINT_mul(group, U, NULL, pk, n, ctx);
        EC_POINT_add(group, U, U, M, ctx);

        EC_POINT_point2oct(group, T, POINT_CONVERSION_COMPRESSED, enc, 33, ctx);
        EC_POINT_point2oct(group, U, POINT_CONVERSION_COMPRESSED, enc+33, 33, ctx);
        enc[loc] = enc[loc] - 2 + 2*xoffset; 
    }

    free(m);
    EC_POINT_free(p);
    BN_free(n);
    BN_free(Mx);
    BN_free(My);
    EC_POINT_free(M);
    EC_POINT_free(T);
    EC_POINT_free(U);
    BN_CTX_free(ctx);
    EC_GROUP_free(group);

    return chunk_count*66;
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
    unsigned char *priv = "\x96\xf6\x82\x44\x02\xe3\xc9\x6f\x68\x24\x40\x2e\x3c\x96\xf6\x82\x44\x02\xe3\xc9\x6f\x68\x24\x40\x2e\x3c\x96\xf6\x82\x44\x02\xe3";
    unsigned char *pub = "\x03\x78\x30\xa7\x72\xda\xeb\x30\x1f\xdc\x53\x22\xc3\x17\x06\xd0\x71\x6c\x1a\x50\xe2\x73\xc6\x1b\x56\x3f\x62\x44\xb5\x14\x5b\x10\xdf";
    unsigned char enc[100];
    unsigned char dec[40];
    size_t enc_len, dec_len;
    char *msg = "Seagulls are green and blue.";

    for (int i = 0; i < 100; i++)
    {
        enc[i] = 'X';
    }

    enc_len = EncryptMessage(enc, pub, 33, msg, strlen(msg));

    //printf("original:  %s\n", msg);
    //printf("encrypted: ");
    printn(enc, 100);
    return 0;
}

