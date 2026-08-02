module

public import Protobuf.Encoding
public import Protobuf.Base64
meta import Protobuf.Notation

/-!
Well-known types provided by the runtime rather than generated per target.

protoc-gen-lean4 maps imports of `google/protobuf/timestamp.proto` and
`google/protobuf/duration.proto` to this module, so any target's generated
code shares these definitions (mirroring how `google/protobuf/descriptor.proto`
maps to `Protobuf.Internal.Desc`).
-/

@[expose] public section

namespace google.protobuf

open Protobuf Encoding
open scoped Protobuf.Notation

message Timestamp {
  int64 seconds = 1;
  int32 nanos = 2;
}

message Duration {
  int64 seconds = 1;
  int32 nanos = 2;
}

end google.protobuf
