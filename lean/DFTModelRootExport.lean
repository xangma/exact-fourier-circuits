import DFTModelRootProgram
import Lean

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelRootExport
open Lean OAI.PowerSaving.RAM

def node (kind : String) (fields : List (String × Json) := []) : Json :=
  Json.mkObj (("kind", toJson kind) :: fields)

def atomJson {s t : Ty} : Atom false s t → Json
  | .lit n => node "lit" [("value", toJson n)]
  | .int op => node "int" [("op", toJson (match op with
      | .add => "add" | .sub => "sub" | .mul => "mul"
      | .div => "div" | .mod => "mod" | .lt => "lt"))]
  | .id => node "id"
  | .fst => node "fst"
  | .snd => node "snd"
  | _ => node "unsupportedAtom"

def codeJson {r : Port} {s t : Ty} : Code false r s t → Json
  | .atom op => atomJson op
  | .comp f g => node "comp" [("first", codeJson f), ("second", codeJson g)]
  | .fork f g => node "fork" [("left", codeJson f), ("right", codeJson g)]
  | .ifz q f g => node "ifz" [("test", codeJson q), ("zero", codeJson f), ("nonzero", codeJson g)]
  | .importClosed f => node "closed" [("body", codeJson f)]
  | .call => node "call"
  | .descend base body => node "descend" [("base", codeJson base), ("body", codeJson body)]
  | _ => node "unsupportedCode"

#eval IO.println ((codeJson ExactFourierCircuits.DFTModelRoot.program).compress)

end ExactFourierCircuits.DFTModelRootExport
