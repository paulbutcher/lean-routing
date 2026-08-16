/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Routing.RouteTable
import Routing.Route
import Routing.RouteMount

namespace Routing

route_table MountLeafRoutes
  [ index := "/",
    item := "/:slug:String" ]

route_table MountTest
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
-- "/outer", exercising `mountFieldsSrc`'s recursive case (`RouteTable.lean`).
route_table MountInnerRoutes
  [ leaf1 := "/leaf1" ]

route_table MountMiddleRoutes
  [ innerMount := mount "/mid" MountInnerRoutes,
    ownLeaf := "/own" ]

route_table MountOuterTest
  [ midMount := mount "/outer" MountMiddleRoutes ]

#guard MountOuterTest.patterns.midMount.innerMount.leaf1 = [.lit "outer", .lit "mid", .lit "leaf1"]
#guard MountOuterTest.patterns.midMount.ownLeaf = [.lit "outer", .lit "own"]
#guard MountOuterTest.links.midMount.innerMount.leaf1 = "/outer/mid/leaf1"
#guard MountOuterTest.links.midMount.ownLeaf = "/outer/own"

-- Negative-compile regression: a mount prefix with a capture is a command-time error
-- (`prefixSegsSrcFor`, `RouteTable.lean`); mount prefixes must be literal.
/--
error: mount prefix must not contain captures (got "/orgs/:orgId:Nat"); captured mount prefixes are not yet supported
-/
#guard_msgs in
route_table MountCaptureTest
  [ bad := mount "/orgs/:orgId:Nat" MountLeafRoutes ]

-- Negative-compile regression: the duplicate-name check (`RouteTable.lean`) applies uniformly
-- across leaf and mount rows.
/--
error: route name 'index' already declared at `index
-/
#guard_msgs in
route_table MountDupTest
  [ index := "/",
    index := mount "/x" MountLeafRoutes ]

-- `mount_routes` is the `Route`-level analogue of `mount`: routes declared once against a
-- sub-app's own unprefixed `patterns` are reused unmodified; only `segs` is rewritten, exactly
-- mirroring `MountTest.patterns.blog` above.
private def leafRoutes : List (Route String) :=
  [ .get MountLeafRoutes.patterns.index (handler := "index"),
    .get MountLeafRoutes.patterns.item (handler := fun (slug : String) => s!"item {slug}") ]

private def blogMountedRoutes : List (Route String) := mount_routes "/blog" leafRoutes

#guard dispatchTable blogMountedRoutes .get ["blog"] = some "index"
#guard dispatchTable blogMountedRoutes .get ["blog", "hi"] = some "item hi"
#guard dispatchTable blogMountedRoutes .get [] = none
#guard dispatchTable blogMountedRoutes .get ["hi"] = none

-- A mounted route reports its *prefixed* pattern, not the unprefixed one its handler was
-- declared against: `mount_routes` rewrote `segs` itself, so there's nothing left to re-apply.
#guard matchTable blogMountedRoutes .get ["blog"] = some ({ method := .get, segs := [.lit "blog"] }, "index")
#guard matchTable blogMountedRoutes .get ["blog", "hi"]
     = some ({ method := .get, segs := [.lit "blog", .capture "slug" .string] }, "item hi")
#guard matchTable blogMountedRoutes .get ["hi"] = none

-- Nesting is just repeated prefixing and `++`; no structural recursion needed, unlike `mount`.
private def innerRoutes : List (Route String) :=
  [ .get MountInnerRoutes.patterns.leaf1 (handler := "leaf1") ]

private def middleOwnRoutes : List (Route String) :=
  [ .get MountMiddleRoutes.patterns.ownLeaf (handler := "own") ]

private def middleRoutes : List (Route String) :=
  mount_routes "/mid" innerRoutes ++ middleOwnRoutes

private def outerRoutes : List (Route String) := mount_routes "/outer" middleRoutes

#guard dispatchTable outerRoutes .get ["outer", "mid", "leaf1"] = some "leaf1"
#guard dispatchTable outerRoutes .get ["outer", "own"] = some "own"

-- Both mount levels' prefixes are present in the reported pattern.
#guard matchTable outerRoutes .get ["outer", "mid", "leaf1"]
     = some ({ method := .get, segs := [.lit "outer", .lit "mid", .lit "leaf1"] }, "leaf1")
#guard matchTable outerRoutes .get ["outer", "own"]
     = some ({ method := .get, segs := [.lit "outer", .lit "own"] }, "own")
#guard matchTable outerRoutes .get ["mid", "leaf1"] = none

-- Negative-compile regression: same capture restriction, and same error message, as `mount`
-- (`mountPrefixSegs`, `RouteMount.lean`).
/--
error: mount prefix must not contain captures (got "/orgs/:orgId:Nat"); captured mount prefixes are not yet supported
-/
#guard_msgs in
def badMountRoutes : List (Route String) := mount_routes "/orgs/:orgId:Nat" leafRoutes

-- Negative-compile regression: a malformed prefix pattern is a macro-time error, not a
-- silently-accepted bad mount.
/--
error: invalid route pattern "not-a-valid-pattern"
-/
#guard_msgs in
def badPatternRoutes : List (Route String) := mount_routes "not-a-valid-pattern" leafRoutes

end Routing
