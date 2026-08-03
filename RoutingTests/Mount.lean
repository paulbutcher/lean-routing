import Routing.RouteTable
import Routing.Route

namespace Routing

routeTable! MountLeafRoutes
  [ index := "/",
    item := "/:slug:String" ]

routeTable! MountTest
  [ home := "/",
    blog := mount "/blog" MountLeafRoutes ]

#guard MountTest.patterns.home = []
#guard MountTest.patterns.blog.index = [.lit "blog"]
#guard MountTest.patterns.blog.item = [.lit "blog", .capture "slug" .string]
#guard MountTest.links.home = "/"
#guard MountTest.links.blog.index = "/blog"
#guard MountTest.links.blog.item "hi" = "/blog/hi"

-- A handler for a mounted route needs no extra wrapping for a literal prefix: `HandlerType`
-- reduces through `.lit` segments, so this is exactly the handler `MountLeafRoutes.patterns.item`
-- itself would need.
private def blogItemRoute : Route String :=
  .get MountTest.patterns.blog.item (handler := fun (slug : String) => s!"item {slug}")

#guard dispatchTable [blogItemRoute] .get ["blog", "hi"] = some "item hi"
#guard dispatchTable [blogItemRoute] .get ["hi"] = none

-- Mounting nests to arbitrary depth: `MountMiddleRoutes` mounts `MountInnerRoutes` under "/mid"
-- (alongside a leaf route of its own), and `MountOuterTest` mounts `MountMiddleRoutes` under
-- "/outer" -- exercising `mountFieldsSrc`'s recursive case (`RouteTable.lean`).
routeTable! MountInnerRoutes
  [ leaf1 := "/leaf1" ]

routeTable! MountMiddleRoutes
  [ innerMount := mount "/mid" MountInnerRoutes,
    ownLeaf := "/own" ]

routeTable! MountOuterTest
  [ midMount := mount "/outer" MountMiddleRoutes ]

#guard MountOuterTest.patterns.midMount.innerMount.leaf1 = [.lit "outer", .lit "mid", .lit "leaf1"]
#guard MountOuterTest.patterns.midMount.ownLeaf = [.lit "outer", .lit "own"]
#guard MountOuterTest.links.midMount.innerMount.leaf1 = "/outer/mid/leaf1"
#guard MountOuterTest.links.midMount.ownLeaf = "/outer/own"

-- Negative-compile regression: a mount prefix with a capture is a command-time error
-- (`prefixSegsSrcFor`, `RouteTable.lean`) -- captured mount prefixes aren't supported yet.
/--
error: mount prefix must not contain captures (got "/orgs/:orgId:Nat"); captured mount prefixes are not yet supported
-/
#guard_msgs in
routeTable! MountCaptureTest
  [ bad := mount "/orgs/:orgId:Nat" MountLeafRoutes ]

-- Negative-compile regression: the duplicate-name check (`RouteTable.lean`) applies uniformly
-- across leaf and mount rows.
/--
error: route name 'index' already declared at `index
-/
#guard_msgs in
routeTable! MountDupTest
  [ index := "/",
    index := mount "/x" MountLeafRoutes ]

end Routing
