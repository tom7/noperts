import Noperthedron.Nopert229.TestEvalRealCage

open Noperthedron Noperthedron.Nopert229

def main : IO Unit := do
  let vals := (List.range 20).filterMap (fun k =>
    if h : k < 20 then
      let s := box.supportUpper 0 2 ⟨k, h⟩
      if s > 0 then some (k, s) else none
    else none)
  for (k, s) in vals do
    IO.println s!"k = {k}: supportUpper = {s}"
