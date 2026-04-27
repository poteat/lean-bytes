import Lake
open Lake DSL System

/-- Force-include `bytes_ffi.h` in every Lean-generated `.c` file built
within this package. The header exposes our `@[extern]` C bodies as
`extern inline __attribute__((gnu_inline, always_inline))`, so callers
inline the body instead of paying per-call FFI overhead. The external
symbols still come from `bytes_ffi.c` via `libBytesFFI.a`. -/
package «bytes» where
  moreLeancArgs := #["-I", "c", "-include", "bytes_ffi.h"]

@[default_target]
lean_lib Bytes where

lean_lib BytesTest where
  globs := #[.submodules `BytesTest]

@[test_driver]
lean_exe «bytes-test» where
  root := `BytesTest.Driver

lean_exe «bytes-bench» where
  root := `BytesBench.Main

/-! ## C FFI

The `Bytes.*` `@[extern]` declarations route through `c/bytes_ffi.c`
for the runtime fast paths; the Lean bodies remain the spec for kernel
reduction. The target below compiles that file and the `extern_lib`
packages it as a static library so anything depending on this package
links it. -/

def cFlags : Array String :=
  #["-O3", "-DNDEBUG", "-fPIC"]

target bytes_ffi.o pkg : FilePath := do
  let oFile := pkg.buildDir / "c" / "bytes_ffi.o"
  let srcJob ← inputTextFile <| pkg.dir / "c" / "bytes_ffi.c"
  let leanInc := (← getLeanIncludeDir).toString
  buildO oFile srcJob #[] (cFlags ++ #["-I", leanInc]) "cc"

extern_lib libBytesFFI pkg := do
  let name := nameToStaticLib "BytesFFI"
  let oJob ← fetch <| pkg.target ``bytes_ffi.o
  buildStaticLib (pkg.staticLibDir / name) #[oJob]
