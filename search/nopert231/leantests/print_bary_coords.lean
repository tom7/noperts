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
  B := 7/5
}

def newBox : Box where
  interval := box.interval
  root := box.root
  triangle := box.triangle
  chart := box.chart
  symmetryIndex := box.symmetryIndex
  certificate := fun j => if j = 0 then newAx0 else box.certificate j
  c := 265 / 1000000
  δ := 260 / 1000000
  r := 4 / 100000

def main : IO Unit := do
  let c_cone : ℚ := 25 / 1000
  IO.println s!"det: {LocalCertificate.tetraDetQ (newBox.decomposedCenter c_cone)}"
  for k in (List.finRange 6) do
    let b := newBox.decomposedBarycentric c_cone k
    IO.println s!"target {k.val}: {b 0}, {b 1}, {b 2}, {b 3}"
