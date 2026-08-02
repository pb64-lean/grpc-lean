import Lake
open Lake DSL

/-!
# lakefile.lean - IDE project model for the grpc_service example.

Bazel owns the real builds. This file exists so `lake serve` can resolve the
handwritten example modules, the Bazel-generated pure Lean proto modules, and
the local runtime/protobuf sources used by those modules.

Populate generated sources first:

  bazel build //proto:user_service_lean_proto //proto:analytics_service_lean_proto //lean:server
-/

package «grpc-service» where
  leanOptions := #[⟨`experimental.module, true⟩]

lean_lib «Handwritten» where
  srcDir := "lean"
  roots := #[
    `Handlers,
    `UserService,
    `Analytics,
    `EmailAnalyticsService,
    `ProofTransport,
    `Main
  ]

lean_lib «Generated» where
  srcDir := "bazel-bin/proto"
  roots := #[
    `GrpcServiceExample.user_service,
    `GrpcServiceExample.analytics_service
  ]

lean_lib «GrpcRuntime» where
  srcDir := "../.."
  roots := #[`Grpc]

lean_lib «Protobuf» where
  srcDir := "../../third_party/Lean-zh/protobuf"
  roots := #[`Protobuf]

lean_lib «Binary» where
  srcDir := "../../third_party/Lean-zh/binary"
  roots := #[`Binary]
