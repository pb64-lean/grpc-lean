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

require «tls13-lean» from "../tls13-lean"

/- Keep the editor's Lake module graph aligned with the local repositories in
   MODULE.bazel.  These are source roots only; Bazel remains the build system. -/
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
