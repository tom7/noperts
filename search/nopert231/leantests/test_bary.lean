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
  c := box.c
  δ := 260 / 1000000
  r := box.r

def main : IO Unit := do
  IO.println s!"c_cone = 15/1000: barycentricValid = {decide (newBox.decomposedBarycentricValid (15/1000))}"
  IO.println s!"c_cone = 18/1000: barycentricValid = {decide (newBox.decomposedBarycentricValid (18/1000))}"
  IO.println s!"c_cone = 20/1000: barycentricValid = {decide (newBox.decomposedBarycentricValid (20/1000))}"
  IO.println s!"c_cone = 25/1000: barycentricValid = {decide (newBox.decomposedBarycentricValid (25/1000))}"
