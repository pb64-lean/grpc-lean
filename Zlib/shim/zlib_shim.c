/* FFI shim marshalling Lean ByteArray <-> zlib gzip streams. */

#include <lean/lean.h>
#include <zlib.h>

#include <stdint.h>
#include <stdlib.h>
#include <string.h>

/* grpc_zlib_gzip_compress : ByteArray -> ByteArray */
LEAN_EXPORT lean_obj_res grpc_zlib_gzip_compress(b_lean_obj_arg data) {
    size_t src_len = lean_sarray_size(data);
    uint8_t *src = lean_sarray_cptr(data);

    z_stream strm;
    memset(&strm, 0, sizeof(strm));
    /* windowBits 15 + 16 selects the gzip wrapper. */
    if (deflateInit2(&strm, Z_DEFAULT_COMPRESSION, Z_DEFLATED, 15 + 16, 8,
                     Z_DEFAULT_STRATEGY) != Z_OK) {
        /* Out of memory is the only realistic failure; return empty. */
        return lean_alloc_sarray(1, 0, 0);
    }

    size_t cap = deflateBound(&strm, (uLong)src_len);
    if (cap < 64) cap = 64;
    uint8_t *out = (uint8_t *)malloc(cap);
    size_t out_len = 0;

    strm.next_in = (Bytef *)src;
    strm.avail_in = (uInt)src_len;

    int ret = Z_OK;
    do {
        if (out_len == cap) {
            cap *= 2;
            out = (uint8_t *)realloc(out, cap);
        }
        strm.next_out = out + out_len;
        strm.avail_out = (uInt)(cap - out_len);
        ret = deflate(&strm, Z_FINISH);
        out_len = cap - strm.avail_out;
    } while (ret == Z_OK || ret == Z_BUF_ERROR);

    deflateEnd(&strm);

    lean_object *res = lean_alloc_sarray(1, out_len, out_len);
    memcpy(lean_sarray_cptr(res), out, out_len);
    free(out);
    return res;
}

/* grpc_zlib_gzip_decompress : ByteArray -> UInt32 -> Option ByteArray
   Returns none on corrupt input or if inflated size would exceed maxLen. */
LEAN_EXPORT lean_obj_res grpc_zlib_gzip_decompress(b_lean_obj_arg data,
                                                   uint32_t max_len) {
    size_t src_len = lean_sarray_size(data);
    uint8_t *src = lean_sarray_cptr(data);

    z_stream strm;
    memset(&strm, 0, sizeof(strm));
    if (inflateInit2(&strm, 15 + 16) != Z_OK) {
        return lean_box(0); /* none */
    }

    size_t cap = src_len * 2 + 64;
    if (cap > (size_t)max_len + 1) cap = (size_t)max_len + 1;
    if (cap < 64) cap = 64;
    uint8_t *out = (uint8_t *)malloc(cap);
    size_t out_len = 0;

    strm.next_in = (Bytef *)src;
    strm.avail_in = (uInt)src_len;

    int ok = 0;
    for (;;) {
        if (out_len == cap) {
            if (out_len > (size_t)max_len) break; /* bomb guard */
            cap = cap * 2;
            if (cap > (size_t)max_len + 1) cap = (size_t)max_len + 1;
            if (cap <= out_len) break;
            out = (uint8_t *)realloc(out, cap);
        }
        strm.next_out = out + out_len;
        strm.avail_out = (uInt)(cap - out_len);
        int ret = inflate(&strm, Z_NO_FLUSH);
        out_len = cap - strm.avail_out;
        if (ret == Z_STREAM_END) {
            if (out_len <= (size_t)max_len) ok = 1;
            break;
        }
        if (ret == Z_OK || ret == Z_BUF_ERROR) {
            if (out_len > (size_t)max_len) break; /* exceeded cap */
            if (ret == Z_BUF_ERROR && strm.avail_in == 0 && out_len < cap) {
                break; /* truncated input */
            }
            continue;
        }
        break; /* corrupt input */
    }

    inflateEnd(&strm);

    if (!ok) {
        free(out);
        return lean_box(0); /* none */
    }

    lean_object *bytes = lean_alloc_sarray(1, out_len, out_len);
    memcpy(lean_sarray_cptr(bytes), out, out_len);
    free(out);

    lean_object *some = lean_alloc_ctor(1, 1, 0);
    lean_ctor_set(some, 0, bytes);
    return some;
}
