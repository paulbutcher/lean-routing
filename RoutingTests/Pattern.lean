import Routing.Pattern

namespace Routing

-- #guard tests: well-formed patterns.
#guard parsePattern "/" = some []
#guard parsePattern "/users" = some [.lit "users"]
#guard parsePattern "/users/:id:Nat" = some [.lit "users", .capture "id" .nat]
#guard parsePattern "/users/:id:Nat/posts/:slug:String"
  = some [.lit "users", .capture "id" .nat, .lit "posts", .capture "slug" .string]

-- #guard tests: malformed patterns fail via `none`, never a panic (§3/§6).
#guard parsePattern "" = none                        -- no leading '/'
#guard parsePattern "users/:id:Nat" = none            -- no leading '/'
#guard parsePattern "/users//id" = none                -- doubled '/' ⇒ empty segment
#guard parsePattern "/users/" = none                   -- trailing '/' ⇒ empty segment
#guard parsePattern "/users/:id:Bool" = none           -- unknown capture kind
#guard parsePattern "/users/:id" = none                -- missing capture kind
#guard parsePattern "/users/::Nat" = none              -- empty capture name

end Routing
