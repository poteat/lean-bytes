// Provides the external (`LEAN_EXPORT`) symbols for the `Bytes.*` C
// fast paths. The bodies live in `bytes_ffi.h`, where they're also
// `extern inline __attribute__((gnu_inline, always_inline))` for any
// translation unit that includes the header (the Lean-generated C does
// so via clang's `-include` flag, set in `lakefile.lean`'s
// `moreLeancArgs`). This file is the only TU that produces external
// definitions; the linker resolves any non-inlined call against these.

#define LEAN_BYTES_IMPL
#include "bytes_ffi.h"
