# rules_lean_grpc/defs.bzl
"""Public API for rules_lean_grpc (pure Lean gRPC / proto codegen).

    load("@rules_lean_grpc//:defs.bzl", "lean_proto_library")
"""

load(":proto.bzl", _lean_proto_library = "lean_proto_library")

lean_proto_library = _lean_proto_library
