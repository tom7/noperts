import Noperthedron.Nopert229.TestEvalRealCage

open Noperthedron Noperthedron.Nopert229
open AtlasProjectiveLocalCertificate

def newAx0 : AxisCertificate := {
  edgeStart := ![3, 1, 14],
  edgeFinish := ![2, 4, 15],
  edgeStart₂ := ![2, 4, 15],
  edgeFinish₂ := ![1, 8, 19],
  mix := ![800, 800, 400],
  index := ![2, 4, 15],
  nonzeroWitness := ![9, 15, 1],
  B := 549469387/500000000
}

def newBox : Box where
  interval := box.interval
  root := box.root
  triangle := box.triangle
  chart := box.chart
  symmetryIndex := box.symmetryIndex
  certificate := fun j => if j = 0 then newAx0 else box.certificate j
  c := box.c
  δ := 260 / 1000000
  r := box.r

def main : IO Unit := do
  let var := newBox.variationRadiusSum 0 + 3 * variationError
  let bud := newAx0.B * newBox.δ
  IO.println s!"variation: {var}"
  IO.println s!"budget:    {bud}"
  IO.println s!"slack:     {bud - var}"
  IO.println s!"weightBudget: {newBox.weightBudget 0} vs B: {newAx0.B}"
  IO.println s!"weightLower: {newBox.weightLower 0 0}, {newBox.weightLower 0 1}, {newBox.weightLower 0 2}"
