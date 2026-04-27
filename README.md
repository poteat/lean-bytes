# bytes

Verified `ByteArray` primitives in C.

Each operation has a Lean reference body and algebraic laws for use in proofs;
runtime calls route through `@[extern]` to a C fast path.

Loads and stores at 8/16/32/64-bit widths in little- and big-endian, plus
`copy`, `fill`, `equal`, and `compare`.

## Installation

```lean
require "poteat" / "bytes" @ git "main"

package «myapp» where
  moreLeancArgs := #["-I", ".lake/packages/bytes/c", "-include", "bytes_ffi.h"]
```

| Import           | What you get   | Axiom cost                               |
| ---------------- | -------------- | ---------------------------------------- |
| `Bytes`          | runtime API    | standard                                 |
| `Bytes.Theorems` | algebraic laws | per-call `_native.bv_decide.ax_*` (LRAT) |

## Performance

`lake exe bytes-bench` compares each `Bytes.*` primitive against a pure-Lean
reimplementation on a 1 MiB buffer. Apple M-series, single-threaded:

| Primitive     | C extern | Lean reference | Speedup |
| ------------- | -------: | -------------: | ------: |
| `loadU8`      |   1.3 ns |         1.2 ns |    1.0× |
| `loadU64LE`   |   1.1 ns |         5.2 ns |    4.4× |
| `storeU64LE`  |   1.9 ns |         8.5 ns |    4.4× |
| `copy 1 MiB`  |    15 µs |         1.8 ms |    120× |
| `fill 1 MiB`  |    14 µs |         1.5 ms |    110× |
| `equal 1 MiB` |    30 µs |         1.6 ms |     55× |

Two mechanisms: width-N loads/stores collapse 8 byte-ops into one `memcpy`, and
bulk ops drop into `memmove`/`memset`/`memcmp`.

The C bodies live in `c/bytes_ffi.h` and are force-included into every
Lean-generated `.c`, so calls inline at the call site rather than paying
per-call FFI overhead.

## License

Apache-2.0.
