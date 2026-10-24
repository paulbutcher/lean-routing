/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Routing
public import LeanIn.Http.StdHandler

public section

@[expose] section

namespace Routing

open Std.Http
open LeanIn.Http

/-- LeanIn: handlers and hooks in its `VM`, over its streaming `BodyReader`, answering with its
`ResponseBody`, buffered or streamed. -/
@[reducible] def Engine.leanin : Engine where
  M := LeanIn.Runtime.VM
  Hook := LeanIn.Runtime.VM
  ReqBody := Server.BodyReader
  RespBody := LeanIn.Http.ResponseBody
  text builder content := pure <|
    builder.header Header.Name.contentType (.mk "text/plain; charset=utf-8")
      |>.body (.bytes content.toUTF8)

/-- What `Server.serveConnStd` serves. Its `Config.continuePolicy` must be `.application`, so that
`onContinue` makes the decision. -/
def StatelessHandler.toLeanIn (h : StatelessHandler .leanin) : StdHandler :=
  { onRequest := h.onRequest, onFailure := h.onFailure, onContinue := h.onContinue }

end Routing
