/-
Optional JSON support for `Routing.Response`. This module is outside the default `Routing`
library because it imports the Lean package for `Lean.ToJson`; importing it makes a consumer's
binary carry the frontend. Use it when JSON matters more than the Lean-free guarantee.
-/
module

public import Routing.Server
public import Lean

public section

namespace Routing

namespace Response

def json [Lean.ToJson α] (r : Response) (a : α) : Response :=
  r.header (.mk "content-type") (.mk "application/json") |>.text
    (Lean.ToJson.toJson a).compress

end Response

end Routing
