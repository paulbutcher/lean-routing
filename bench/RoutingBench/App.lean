/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Routing

/-!
The application both engines serve, written once. Its routes cover what dispatch does: a literal, a
typed capture, a mounted index and its slash redirect, a miss, and enough literal routes that the
trie has something to skip. One middleware layer stands for an application's stack.
-/

namespace RoutingBench

open Routing
open Std.Http

/-- Publishes the matched template as `x-route`, as tracing middleware would read it. -/
def withRouteHeader {e : Engine} (h : StatelessHandler e) : StatelessHandler e :=
  { h with onRequest := fun request => do
      let response ← h.onRequest request
      match (matchedPattern? response.extensions).bind Header.Value.ofString? with
      | some route =>
        return { response with
          line := { response.line with
            headers := response.line.headers.insert (.mk "x-route") route } }
      | none => return response }

def ok {e : Engine} (body : String) : Result e := fun _ => e.text Response.ok body

/-- `/items/0` … `/items/63`, each its own literal route. -/
def items {e : Engine} : List (Entry e) :=
  (List.range 64).filterMap fun i =>
    if h : dotSegment (toString i) = false then
      some (.get [.lit "items", .lit (toString i) h] (ok s!"item {i}"))
    else none

def router {e : Engine} : Router e :=
  { middlewares := [withRouteHeader]
    routes :=
      [ .get [.lit "bench"] (ok "hello"),
        .get [.lit "users", .capture "id" .nat] fun (id : Nat) => ok s!"user {id}",
        .mount (.mk ["blog"]) [ .get [] (ok "blog") ] ] ++ items }

/-- The paths `run.sh` and `Dispatch` request, and what each exercises. -/
def targets : List (String × String) :=
  [ ("/bench", "literal"), ("/users/7", "capture"), ("/items/63", "64 literals"),
    ("/blog", "slash redirect"), ("/nope", "miss") ]

def handler (e : Engine) : IO (StatelessHandler e) :=
  match router.toHandlerChecked with
  | .ok h => pure h
  | .error report => throw (IO.userError s!"the benchmark's routes shadow each other:\n{report}")

end RoutingBench
