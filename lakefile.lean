import Lake
open Lake DSL

/-!
# lakefile.lean — IDE project model for the rules_lean_grpc runtime.

This file exists solely to feed `lake serve` the module graph for the pure Lean
gRPC runtime. Bazel owns the real build and test actions in this repository;
Lake is only used here by editors and LSP clients so that imports such as
`Grpc.Http2.Connection` and `Grpc.Server` resolve from the repo root.

Use Bazel for validation:

  bazel test //:grpc_runtime_test
-/

package «rules-lean-grpc» where
  leanOptions := #[⟨`experimental.module, true⟩]

require «tls13-lean» from git
  "https://github.com/pb64-lean/tls13-lean.git" @
  "0c61f21f3f0e46aa8789cd10f4e03871d1c002db"
require «http2-lean» from git
  "https://github.com/pb64-lean/http2-lean.git" @
  "6ab07dd24d35a2bcef1cdefadba4c2bd6dd640f7"

/- Keep the editor's Lake module graph aligned with MODULE.bazel. Bazel remains
   the authoritative build system. -/
lean_lib «Binary» where
  srcDir := "third_party/Lean-zh/binary"

lean_lib «Protobuf» where
  srcDir := "third_party/Lean-zh/protobuf"

lean_lib «Zlib» where
  srcDir := "."
  roots := #[`Zlib.Gzip]

lean_lib «Grpc» where
  srcDir := "."
  roots := #[`Grpc]
