import Noperthedron.Nopert229.TestEvalRealCage

open Noperthedron Noperthedron.Nopert229

#eval (List.range 3).map (fun i => (List.range 24).map (fun k => box.supportUpper 0 ⟨i, by decide⟩ ⟨k, by decide⟩))
