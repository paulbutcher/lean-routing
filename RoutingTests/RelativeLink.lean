import Routing.RelativeLink
import Routing.Handler

namespace Routing

-- Descending: item page linking to a nested action on itself.
#guard relativeUrl "/posts/5" "/posts/5/edit" = "5/edit"

-- Sideways: index linking to an item (and back).
#guard relativeUrl "/posts" "/posts/5" = "posts/5"

-- Same page: not "", which per RFC 3986 means "same-document reference" (a same-page fragment
-- jump), not "reload this document" -- repeating the current page's own last segment is what
-- actually resolves back to itself.
#guard relativeUrl "/posts/5" "/posts/5" = "5"

-- Up to the ancestor "directory": renders as "." -- see the integration test below for why that's
-- still safe to serve.
#guard relativeUrl "/posts/5/edit" "/posts/5" = "."

-- The key property: a shared literal prefix (exactly what a `mount` row adds) cancels out.
#guard relativeUrl "/blog/posts/5" "/blog/posts/5/edit" = relativeUrl "/posts/5" "/posts/5/edit"
#guard relativeUrl "/admin/blog/posts/5" "/admin/blog/posts/5/edit" =
  relativeUrl "/posts/5" "/posts/5/edit"

-- Integration: an upward relative link ("." above) resolves, per RFC 3986, to a trailing-slash
-- request path -- confirm `dispatch` (`Handler.lean`) actually serves that path against the
-- ancestor's own (trailing-slash-free) pattern, rather than 404ing.
private def itemPattern : List PathSeg := [.lit "posts", .capture "id" .nat]
private def editPattern : List PathSeg := [.lit "posts", .capture "id" .nat, .lit "edit"]

private def itemHandler : HandlerType itemPattern String :=
  fun (id : Nat) => s!"item #{id}"

#guard relativeUrl (linkFor editPattern 5) (linkFor itemPattern 5) = "."
#guard dispatch itemPattern itemHandler ["posts", "5", ""] = some "item #5"

end Routing
