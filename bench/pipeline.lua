-- Copyright (c) 2026 Paul Butcher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
--
-- `wrk -s pipeline.lua -- <depth>`: each connection keeps <depth> requests in flight, sent together.

init = function(args)
  local depth = tonumber(args[1]) or 1
  local batch = {}
  for i = 1, depth do batch[i] = wrk.format() end
  req = table.concat(batch)
end

request = function()
  return req
end
