/-
The explicit slow-path compatibility layer: upstream's `ContextAsync`/`Body.Any` handler and
router, unchanged in shape. Import this instead of `Routing.Server`/`Routing.Router` for source
compatibility; the native LeanIn path is the fast one.
-/
module

public import Routing.Compat.Server
public import Routing.Compat.Router
