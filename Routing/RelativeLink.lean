/-!
`Routing.relativeUrl current to` computes a relative reference from the page currently being
served (`current`) to a link target (`to`), both already-rendered absolute paths (e.g. from
`linkFor`). The key property: it depends only on `current` and `to`, not on any external
mount-prefix knowledge, and prepending the *same* literal prefix to both cancels out of the result
(`relativeUrl` only ever looks at where the two paths first diverge). So code inside a mounted
module can self-link using its own *unprefixed* `Module.links` values -- no need to thread the
mount's prefix or the mounted (`App.links.blog`-style) `Links` struct through at all.
-/

namespace Routing

/-- Splits a `"/"`-separated absolute path into its segments, e.g. `"/posts/5/edit"` ↦
`["posts", "5", "edit"]`, and `"/"` ↦ `[]`. -/
def pathSegments (path : String) : List String :=
  path.splitOn "/" |>.filter (· ≠ "")

private def commonPrefixLen : List String → List String → Nat
  | a :: as, b :: bs => if a = b then 1 + commonPrefixLen as bs else 0
  | _, _ => 0

/-- A relative reference from `current` (the page currently being served) to `to` (the link
target), both absolute `"/"`-rooted paths, such that any RFC 3986 §5.3-compliant resolver -- a
browser resolving `<a href>`, or an HTTP client following a relative `Location:` redirect --
resolves it back to exactly `to`.

Resolution always treats the *last* segment of `current` as a "file", not a directory (that's the
standard rule -- it's what makes e.g. `href="edit"` on the page `/posts/5` mean `/posts/edit`, not
`/posts/5/edit`), so linking to a strict descendant of the current page needs its own segment
repeated (`relativeUrl "/posts/5" "/posts/5/edit" = "5/edit"`, not `"edit"`).

Linking *up* to an ancestor page renders as a directory reference (`"."`/`".."`/etc.), which
resolves with a *trailing* slash the ancestor's own pattern never has (`"."` from `/posts/5` means
`/posts/5/`, not `/posts/5`) -- `dispatch` (`Handler.lean`) tolerates exactly that trailing empty
segment once a pattern is otherwise fully matched, precisely so this case reaches its target
instead of 404ing. -/
def relativeUrl (current to : String) : String :=
  let fromDir := (pathSegments current).dropLast
  let toSegs := pathSegments to
  let common := commonPrefixLen fromDir toSegs
  let ups := fromDir.length - common
  let downs := toSegs.drop common
  if ups == 0 && downs == [] then
    "."
  else
    String.intercalate "/" (List.replicate ups ".." ++ downs)

end Routing
