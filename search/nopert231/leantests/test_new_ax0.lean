import Noperthedron.Nopert229.TestEvalRealCage

open Noperthedron Noperthedron.Nopert229
open AtlasProjectiveLocalCertificate

-- Let us define the new zero-defect ax0:
def newAx0 : AxisCertificate := {
  edgeStart := ![3, 1, 14],
  edgeFinish := ![2, 4, 15],
  edgeStart₂ := ![2, 4, 15],
  edgeFinish₂ := ![1, 8, 19],
  mix := ![800, 800, 400],
  index := ![2, 4, 15],
  nonzeroWitness := ![9, 15, 1], -- let us check
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
  IO.println s!"supportUpper 0 0: {newBox.supportUpper 0 0 (newAx0.nonzeroWitness 0)}"
  IO.println s!"supportUpper 0 1: {newBox.supportUpper 0 1 (newAx0.nonzeroWitness 1)}"
  IO.println s!"supportUpper 0 2 (witness 1): {newBox.supportUpper 0 2 (newAx0.nonzeroWitness 2)}"
  for k in (List.finRange 20) do
    let s := newBox.supportUpper 0 2 k
    if s > 0 then
      IO.println s!"FAIL: supportUpper 0 2 {k.val} = {s} > 0"
  IO.println "Done checking supportUpper 0 2!"
