// Header-only inline definitions of the `Bytes.*` C fast paths.
//
// Two consumers:
//   * `bytes_ffi.c` defines `LEAN_BYTES_IMPL` before including this header
//     and produces the external (`LEAN_EXPORT`) symbols linked into the
//     final binary via `libBytesFFI.a`.
//   * Every Lean-generated `.c` file that calls one of these primitives
//     includes this header (via clang's `-include` flag in
//     `moreLeancArgs`) and gets `extern inline __attribute__((gnu_inline,
//     always_inline))` definitions. The bodies are visible to the
//     compiler at the call site, so calls inline; no external symbol is
//     emitted from those TUs (the linker resolves them against
//     `bytes_ffi.c`'s out-of-line copies).
//
// This sidesteps Lean's per-call FFI overhead without needing LTO, which
// is currently broken on macOS arm64 in the bundled Lean toolchain.
//
// Behaviour for any in-bounds offset must match the Lean body bit-for-bit,
// including the OOB conventions documented in Bytes.lean (loads → 0 fill,
// stores → no-op, etc.).
//
// Endianness: the `__builtin_memcpy` (load) and `__builtin_memcpy + bswap` (BE) fast paths
// are gated on a compile-time check that the host is little-endian.

#ifndef LEAN_BYTES_FFI_H
#define LEAN_BYTES_FFI_H

#include <lean/lean.h>
// `<lean/lean.h>` already pulls in `<stddef.h>` / `<stdint.h>`. We avoid
// `<string.h>` because Lean's `leanc` invocation uses `-nostdinc` and
// only exposes the compiler's freestanding headers; the libc string
// header isn't on the path. Use clang/gcc builtins instead — same
// codegen, no header dependency.

#if defined(__BYTE_ORDER__) && defined(__ORDER_LITTLE_ENDIAN__) && \
    __BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__
#define LEAN_BYTES_HOST_IS_LE 1
#else
#define LEAN_BYTES_HOST_IS_LE 0
#endif

#ifdef LEAN_BYTES_IMPL
// bytes_ffi.c builds with this defined; produce one external definition
// per primitive for the static library.
#define LBI LEAN_EXPORT
#else
// All other consumers (Lean-generated C via -include): visible body for
// inlining, no external symbol emitted from this TU. Requires gcc/clang;
// the Lean toolchain ships clang, so this is safe.
#define LBI extern inline __attribute__((gnu_inline, always_inline))
#endif

// ---------------------------------------------------------------------------
// Helpers (always file-local; trivially inlined either way)
// ---------------------------------------------------------------------------

static inline lean_object * lean_bytes_ensure_exclusive(lean_obj_arg data) {
    if (lean_is_exclusive(data)) return data;
    return lean_copy_byte_array(data);
}

// Decode an offset from a boxed Nat. Returns 1 on success, 0 on failure
// (i.e. the boxed value is a big-Nat that can't fit a size_t — treat as
// "definitely out of bounds" since no realistic ByteArray reaches that
// size). Caller checks against array size.
static inline int lean_bytes_unbox_off(b_lean_obj_arg n, size_t * out) {
    if (!lean_is_scalar(n)) return 0;
    *out = lean_unbox(n);
    return 1;
}

// ---------------------------------------------------------------------------
// Loads
// ---------------------------------------------------------------------------

LBI uint8_t lean_bytes_load_u8(b_lean_obj_arg data, b_lean_obj_arg off_box) {
    size_t off;
    if (!lean_bytes_unbox_off(off_box, &off)) return 0;
    size_t size = lean_sarray_size(data);
    if (off >= size) return 0;
    return lean_sarray_cptr(data)[off];
}

LBI uint16_t lean_bytes_load_u16_le(b_lean_obj_arg data, b_lean_obj_arg off_box) {
    size_t off;
    if (!lean_bytes_unbox_off(off_box, &off)) return 0;
    size_t size = lean_sarray_size(data);
    const uint8_t *p = lean_sarray_cptr(data);
#if LEAN_BYTES_HOST_IS_LE
    if (size >= 2 && off <= size - 2) {
        uint16_t v;
        __builtin_memcpy(&v, p + off, 2);
        return v;
    }
#endif
    uint16_t v = 0;
    for (size_t i = 0; i < 2; i++) {
        if (off + i < size) v |= ((uint16_t)p[off + i]) << (i * 8);
    }
    return v;
}

LBI uint16_t lean_bytes_load_u16_be(b_lean_obj_arg data, b_lean_obj_arg off_box) {
    size_t off;
    if (!lean_bytes_unbox_off(off_box, &off)) return 0;
    size_t size = lean_sarray_size(data);
    const uint8_t *p = lean_sarray_cptr(data);
#if LEAN_BYTES_HOST_IS_LE
    if (size >= 2 && off <= size - 2) {
        uint16_t v;
        __builtin_memcpy(&v, p + off, 2);
        return __builtin_bswap16(v);
    }
#endif
    uint16_t v = 0;
    for (size_t i = 0; i < 2; i++) {
        if (off + i < size) v |= ((uint16_t)p[off + i]) << ((1 - i) * 8);
    }
    return v;
}

LBI uint32_t lean_bytes_load_u32_le(b_lean_obj_arg data, b_lean_obj_arg off_box) {
    size_t off;
    if (!lean_bytes_unbox_off(off_box, &off)) return 0;
    size_t size = lean_sarray_size(data);
    const uint8_t *p = lean_sarray_cptr(data);
#if LEAN_BYTES_HOST_IS_LE
    if (size >= 4 && off <= size - 4) {
        uint32_t v;
        __builtin_memcpy(&v, p + off, 4);
        return v;
    }
#endif
    uint32_t v = 0;
    for (size_t i = 0; i < 4; i++) {
        if (off + i < size) v |= ((uint32_t)p[off + i]) << (i * 8);
    }
    return v;
}

LBI uint32_t lean_bytes_load_u32_be(b_lean_obj_arg data, b_lean_obj_arg off_box) {
    size_t off;
    if (!lean_bytes_unbox_off(off_box, &off)) return 0;
    size_t size = lean_sarray_size(data);
    const uint8_t *p = lean_sarray_cptr(data);
#if LEAN_BYTES_HOST_IS_LE
    if (size >= 4 && off <= size - 4) {
        uint32_t v;
        __builtin_memcpy(&v, p + off, 4);
        return __builtin_bswap32(v);
    }
#endif
    uint32_t v = 0;
    for (size_t i = 0; i < 4; i++) {
        if (off + i < size) v |= ((uint32_t)p[off + i]) << ((3 - i) * 8);
    }
    return v;
}

LBI uint64_t lean_bytes_load_u64_le(b_lean_obj_arg data, b_lean_obj_arg off_box) {
    size_t off;
    if (!lean_bytes_unbox_off(off_box, &off)) return 0;
    size_t size = lean_sarray_size(data);
    const uint8_t *p = lean_sarray_cptr(data);
#if LEAN_BYTES_HOST_IS_LE
    if (size >= 8 && off <= size - 8) {
        uint64_t v;
        __builtin_memcpy(&v, p + off, 8);
        return v;
    }
#endif
    uint64_t v = 0;
    for (size_t i = 0; i < 8; i++) {
        if (off + i < size) v |= ((uint64_t)p[off + i]) << (i * 8);
    }
    return v;
}

LBI uint64_t lean_bytes_load_u64_be(b_lean_obj_arg data, b_lean_obj_arg off_box) {
    size_t off;
    if (!lean_bytes_unbox_off(off_box, &off)) return 0;
    size_t size = lean_sarray_size(data);
    const uint8_t *p = lean_sarray_cptr(data);
#if LEAN_BYTES_HOST_IS_LE
    if (size >= 8 && off <= size - 8) {
        uint64_t v;
        __builtin_memcpy(&v, p + off, 8);
        return __builtin_bswap64(v);
    }
#endif
    uint64_t v = 0;
    for (size_t i = 0; i < 8; i++) {
        if (off + i < size) v |= ((uint64_t)p[off + i]) << ((7 - i) * 8);
    }
    return v;
}

// ---------------------------------------------------------------------------
// Stores
// ---------------------------------------------------------------------------

LBI lean_obj_res lean_bytes_store_u8(lean_obj_arg data,
                                      b_lean_obj_arg off_box,
                                      uint8_t val) {
    size_t off;
    if (!lean_bytes_unbox_off(off_box, &off)) return data;
    size_t size = lean_sarray_size(data);
    if (off >= size) return data;
    data = lean_bytes_ensure_exclusive(data);
    lean_sarray_cptr(data)[off] = val;
    return data;
}

LBI lean_obj_res lean_bytes_store_u16_le(lean_obj_arg data,
                                          b_lean_obj_arg off_box,
                                          uint16_t val) {
    size_t off;
    if (!lean_bytes_unbox_off(off_box, &off)) return data;
    size_t size = lean_sarray_size(data);
    if (size < 2 || off > size - 2) return data;
    data = lean_bytes_ensure_exclusive(data);
    uint8_t *p = lean_sarray_cptr(data) + off;
#if LEAN_BYTES_HOST_IS_LE
    __builtin_memcpy(p, &val, 2);
#else
    p[0] = (uint8_t)val;
    p[1] = (uint8_t)(val >> 8);
#endif
    return data;
}

LBI lean_obj_res lean_bytes_store_u16_be(lean_obj_arg data,
                                          b_lean_obj_arg off_box,
                                          uint16_t val) {
    size_t off;
    if (!lean_bytes_unbox_off(off_box, &off)) return data;
    size_t size = lean_sarray_size(data);
    if (size < 2 || off > size - 2) return data;
    data = lean_bytes_ensure_exclusive(data);
    uint8_t *p = lean_sarray_cptr(data) + off;
#if LEAN_BYTES_HOST_IS_LE
    uint16_t swapped = __builtin_bswap16(val);
    __builtin_memcpy(p, &swapped, 2);
#else
    p[0] = (uint8_t)(val >> 8);
    p[1] = (uint8_t)val;
#endif
    return data;
}

LBI lean_obj_res lean_bytes_store_u32_le(lean_obj_arg data,
                                          b_lean_obj_arg off_box,
                                          uint32_t val) {
    size_t off;
    if (!lean_bytes_unbox_off(off_box, &off)) return data;
    size_t size = lean_sarray_size(data);
    if (size < 4 || off > size - 4) return data;
    data = lean_bytes_ensure_exclusive(data);
    uint8_t *p = lean_sarray_cptr(data) + off;
#if LEAN_BYTES_HOST_IS_LE
    __builtin_memcpy(p, &val, 4);
#else
    for (size_t i = 0; i < 4; i++) p[i] = (uint8_t)(val >> (i * 8));
#endif
    return data;
}

LBI lean_obj_res lean_bytes_store_u32_be(lean_obj_arg data,
                                          b_lean_obj_arg off_box,
                                          uint32_t val) {
    size_t off;
    if (!lean_bytes_unbox_off(off_box, &off)) return data;
    size_t size = lean_sarray_size(data);
    if (size < 4 || off > size - 4) return data;
    data = lean_bytes_ensure_exclusive(data);
    uint8_t *p = lean_sarray_cptr(data) + off;
#if LEAN_BYTES_HOST_IS_LE
    uint32_t swapped = __builtin_bswap32(val);
    __builtin_memcpy(p, &swapped, 4);
#else
    for (size_t i = 0; i < 4; i++) p[i] = (uint8_t)(val >> ((3 - i) * 8));
#endif
    return data;
}

LBI lean_obj_res lean_bytes_store_u64_le(lean_obj_arg data,
                                          b_lean_obj_arg off_box,
                                          uint64_t val) {
    size_t off;
    if (!lean_bytes_unbox_off(off_box, &off)) return data;
    size_t size = lean_sarray_size(data);
    if (size < 8 || off > size - 8) return data;
    data = lean_bytes_ensure_exclusive(data);
    uint8_t *p = lean_sarray_cptr(data) + off;
#if LEAN_BYTES_HOST_IS_LE
    __builtin_memcpy(p, &val, 8);
#else
    for (size_t i = 0; i < 8; i++) p[i] = (uint8_t)(val >> (i * 8));
#endif
    return data;
}

LBI lean_obj_res lean_bytes_store_u64_be(lean_obj_arg data,
                                          b_lean_obj_arg off_box,
                                          uint64_t val) {
    size_t off;
    if (!lean_bytes_unbox_off(off_box, &off)) return data;
    size_t size = lean_sarray_size(data);
    if (size < 8 || off > size - 8) return data;
    data = lean_bytes_ensure_exclusive(data);
    uint8_t *p = lean_sarray_cptr(data) + off;
#if LEAN_BYTES_HOST_IS_LE
    uint64_t swapped = __builtin_bswap64(val);
    __builtin_memcpy(p, &swapped, 8);
#else
    for (size_t i = 0; i < 8; i++) p[i] = (uint8_t)(val >> ((7 - i) * 8));
#endif
    return data;
}

// ---------------------------------------------------------------------------
// Bulk operations
// ---------------------------------------------------------------------------

LBI lean_obj_res lean_bytes_copy(b_lean_obj_arg src,
                                  b_lean_obj_arg src_off_box,
                                  lean_obj_arg dst,
                                  b_lean_obj_arg dst_off_box,
                                  b_lean_obj_arg len_box) {
    size_t src_off, dst_off, len;
    if (!lean_bytes_unbox_off(src_off_box, &src_off)) return dst;
    if (!lean_bytes_unbox_off(dst_off_box, &dst_off)) return dst;
    if (!lean_bytes_unbox_off(len_box, &len)) return dst;
    if (len == 0) return dst;
    size_t src_size = lean_sarray_size(src);
    size_t dst_size = lean_sarray_size(dst);
    if (src_off > src_size || src_size - src_off < len) return dst;
    if (dst_off > dst_size || dst_size - dst_off < len) return dst;
    // __builtin_memmove handles aliasing; if `src == dst` (same Lean object) the
    // ensure-exclusive copy below makes them distinct, and __builtin_memmove is
    // safe either way at negligible cost vs __builtin_memcpy.
    dst = lean_bytes_ensure_exclusive(dst);
    __builtin_memmove(lean_sarray_cptr(dst) + dst_off,
            lean_sarray_cptr(src) + src_off, len);
    return dst;
}

LBI lean_obj_res lean_bytes_fill(lean_obj_arg data,
                                  b_lean_obj_arg off_box,
                                  b_lean_obj_arg len_box,
                                  uint8_t val) {
    size_t off, len;
    if (!lean_bytes_unbox_off(off_box, &off)) return data;
    if (!lean_bytes_unbox_off(len_box, &len)) return data;
    if (len == 0) return data;
    size_t size = lean_sarray_size(data);
    if (off > size || size - off < len) return data;
    data = lean_bytes_ensure_exclusive(data);
    __builtin_memset(lean_sarray_cptr(data) + off, val, len);
    return data;
}

LBI uint8_t lean_bytes_equal(b_lean_obj_arg a, b_lean_obj_arg a_off_box,
                              b_lean_obj_arg b, b_lean_obj_arg b_off_box,
                              b_lean_obj_arg len_box) {
    size_t a_off, b_off, len;
    if (!lean_bytes_unbox_off(a_off_box, &a_off)) return 0;
    if (!lean_bytes_unbox_off(b_off_box, &b_off)) return 0;
    if (!lean_bytes_unbox_off(len_box, &len)) return 0;
    size_t a_size = lean_sarray_size(a);
    size_t b_size = lean_sarray_size(b);
    if (a_off > a_size || a_size - a_off < len) return 0;
    if (b_off > b_size || b_size - b_off < len) return 0;
    if (len == 0) return 1;
    return __builtin_memcmp(lean_sarray_cptr(a) + a_off,
                  lean_sarray_cptr(b) + b_off, len) == 0 ? 1 : 0;
}

// Returns Ordering as a scalar enum: 0 = .lt, 1 = .eq, 2 = .gt.
LBI uint8_t lean_bytes_compare(b_lean_obj_arg a, b_lean_obj_arg a_off_box,
                                b_lean_obj_arg b, b_lean_obj_arg b_off_box,
                                b_lean_obj_arg len_box) {
    size_t a_off, b_off, len;
    if (!lean_bytes_unbox_off(a_off_box, &a_off)) return 1;
    if (!lean_bytes_unbox_off(b_off_box, &b_off)) return 1;
    if (!lean_bytes_unbox_off(len_box, &len)) return 1;
    size_t a_size = lean_sarray_size(a);
    size_t b_size = lean_sarray_size(b);
    if (a_off > a_size || a_size - a_off < len) return 1;
    if (b_off > b_size || b_size - b_off < len) return 1;
    if (len == 0) return 1;
    int r = __builtin_memcmp(lean_sarray_cptr(a) + a_off,
                   lean_sarray_cptr(b) + b_off, len);
    if (r < 0) return 0;
    if (r > 0) return 2;
    return 1;
}

#endif // LEAN_BYTES_FFI_H
