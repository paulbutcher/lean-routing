/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Routing

/-!
A whole consumer of this library, built as an executable, exercising both macros: a
`route_table` with a `mount` row, and `mount_routes` over the corresponding routes.
`scripts/check-runtime.sh` builds it and reads the Lean package's absence off the binary,
which is the form the claim is actually about.

It is a `module`, and so is everything else linked into the executable, because that is what
the claim requires of a consumer: a legacy (non-`module`) file's initialiser runs the *meta*
initialiser of everything it imports, which starts the frontend at run time and drags it into
the binary along the way.
-/

public section

open Routing

namespace LeanFree

route_table Blog
  [ index := "/",
    post := "/posts/:slug:String" ]

route_table App
  [ home := "/",
    user := "/users/:id:Nat",
    blog := mount "/blog" Blog ]

def blogRoutes : List (Route String) :=
  [ .get Blog.patterns.post (handler := fun (slug : String) => s!"post {slug}") ]

def ownRoutes : List (Route String) :=
  [ .get App.patterns.home (handler := "home"),
    .get App.patterns.user (handler := fun (id : Nat) => s!"user {id}") ]

def routes : List (Route String) :=
  ownRoutes ++ mount_routes "/blog" blogRoutes

end LeanFree

def main : IO Unit := do
  let dispatch (path : List String) : String :=
    (dispatchTable LeanFree.routes .get path).getD "no match"
  IO.println (dispatch ["users", "7"])
  IO.println (dispatch ["blog", "posts", "hi"])
  IO.println (dispatch ["nope"])
  IO.println LeanFree.App.links.blog.index
  IO.println (LeanFree.App.links.blog.post "hi")
  IO.println (LeanFree.App.links.user 7)
