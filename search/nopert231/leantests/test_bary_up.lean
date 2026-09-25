import Noperthedron.Nopert229.TestEvalRealCage

open Noperthedron Noperthedron.Nopert229

def main : IO Unit := do
  for num in [25, 29, 30, 32, 35, 40, 45, 50] do
    let c_cone : ℚ := num / 1000
    let ok := decide (box.decomposedBarycentricValid c_cone)
    IO.println s!"c_cone = {num}/1000: {ok}"
