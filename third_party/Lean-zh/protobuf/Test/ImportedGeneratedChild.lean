module

public import Protobuf.Encoding
public import Protobuf.Notation

public section

open Protobuf Encoding
open scoped Protobuf.Notation

namespace ImportedGenerated

message Child {
  uint64 id = 1;
  string label = 2;
}

end ImportedGenerated
