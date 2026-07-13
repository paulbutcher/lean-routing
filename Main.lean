import Std.Http.Server
import Html
import Htmx
import Routing

open Std Async
open Std Http Server
open Html
open Routing

def htmxScript : ScriptAttrs :=
  { src := "https://cdn.jsdelivr.net/npm/htmx.org@2.0.10/dist/htmx.min.js"
    integrity := some "sha384-H5SrcfygHmAuTDZphMHqBJLc3FhssKjG7w/CeCpFReSfwBWDTKpkzPP8c+cLsK+V"
    crossorigin := some "anonymous" }

def page : String :=
  document (pretty := true) "Hey there ;-)"
    [ h1 ["Hey there ;-)"],
      p ["Served by a ", strong ["typed"], " HTML library." ],
      Htmx.button ["Ping"] { hxGet := some "/ping", hxTarget := some "#result", hxSwap := some .innerHTML },
      div [] { id := some "result" } ]
    (scripts := [htmxScript])
    (lang := some "en")

def pingFragment : String :=
  Node.render (strong ["pong"])

def helloPage (name : String) : String :=
  document (pretty := true) s!"Hello, {name}"
    [ h1 [s!"Hello, {name}!"],
      p [ "This page came from a ", strong ["typed path capture"],
          s!": /hello/:name:String matched \"{name}\"." ] ]
    (lang := some "en")

def routes : List (Route Result) :=
  [ route .get "/" (Response.ok.html page : Result),
    route .get "/ping" (Response.ok.html pingFragment : Result),
    route .get "/hello/:name:String" (fun (name : String) => (Response.ok.html (helloPage name) : Result)) ]

def main : IO Unit := Async.block do
  let addr : Net.SocketAddress := .v4 ⟨.ofParts 127 0 0 1, 2000⟩
  let server ← Server.serve addr (toHandler routes)
  server.waitShutdown
