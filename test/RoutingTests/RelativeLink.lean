/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Routing.RelativeLink
import Routing.Handler

namespace Routing

-- Descending: item page linking to a nested action on itself.
#guard relativeUrl "/posts/5" "/posts/5/edit" = "5/edit"

-- Sideways: index linking to an item (and back).
#guard relativeUrl "/posts" "/posts/5" = "posts/5"

-- Same page: not "", which per RFC 3986 means "same-document reference" (a same-page fragment
-- jump), not "reload this document"; repeating the current page's own last segment is what
-- actually resolves back to itself.
#guard relativeUrl "/posts/5" "/posts/5" = "5"

-- Up to the ancestor "directory": renders as ".", with the integration test below for why that's
-- still safe to serve.
#guard relativeUrl "/posts/5/edit" "/posts/5" = "."

-- The key property at the URL level, where the string plumbing (`pathSegments`, `dropLast`) has to
-- preserve it: a shared literal prefix, exactly what a `mount` row adds, cancels out.
#guard relativeUrl "/blog/posts/5" "/blog/posts/5/edit" = relativeUrl "/posts/5" "/posts/5/edit"
#guard relativeUrl "/admin/blog/posts/5" "/admin/blog/posts/5/edit" =
  relativeUrl "/posts/5" "/posts/5/edit"

/-! ## Mount-prefix cancellation

The `#guard`s above are instances of a statement about *any* prefix, which is what makes a module
safe to mount anywhere: proved here of `relativeSegments`, the level at which a mount prefix is
literally a shared list prefix. -/

private theorem commonPrefixLen_append (p a b : List String) :
    commonPrefixLen (p ++ a) (p ++ b) = p.length + commonPrefixLen a b := by
  induction p with
  | nil => simp
  | cons c p' ih =>
    show (if c = c then 1 + commonPrefixLen (p' ++ a) (p' ++ b) else 0)
        = (c :: p').length + commonPrefixLen a b
    rw [ite_eq_left rfl, ih, List.length_cons]
    omega

theorem relativeSegments_prefix (p fromDir toSegs : List String) :
    relativeSegments (p ++ fromDir) (p ++ toSegs) = relativeSegments fromDir toSegs := by
  have hdrop : ∀ k : Nat, List.drop (p.length + k) (p ++ toSegs) = List.drop k toSegs := by
    intro k
    rw [List.drop_append]
    simp
  simp only [relativeSegments, commonPrefixLen_append, List.length_append, Nat.add_sub_add_left,
    hdrop]

-- Integration: an upward relative link ("." above) resolves, per RFC 3986, to a trailing-slash
-- request path; confirm `dispatch` (`Handler.lean`) actually serves that path against the
-- ancestor's own (trailing-slash-free) pattern, rather than 404ing.
private def itemPattern : List PathSeg := [.lit "posts", .capture "id" .nat]
private def editPattern : List PathSeg := [.lit "posts", .capture "id" .nat, .lit "edit"]

private def itemHandler : HandlerType itemPattern String :=
  fun (id : Nat) => s!"item #{id}"

#guard relativeUrl (linkFor editPattern 5) (linkFor itemPattern 5) = "."
#guard dispatch itemPattern itemHandler ["posts", "5", ""] = some "item #5"

end Routing
