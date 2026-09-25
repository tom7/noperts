import Noperthedron.Nopert229.AtlasProjectiveLocalViewTree
import Noperthedron.Nopert229.AtlasProjectiveAnnularCertificate

open Noperthedron.Nopert229
open Noperthedron.Nopert229.AtlasProjectiveLocalViewTree
open Noperthedron.Nopert229.AtlasProjectiveLocalCertificate
open Noperthedron.SnubCube.ProjectiveView

def getTriangleForPath (digits : List (Fin 4)) : AtlasProjectiveView.Triangle ℚ :=
  digits.foldl (fun t d => split t d) AtlasProjectiveView.upperWedgeTriangle

def main : IO Unit := do
  let pathDigits : List (Fin 4) := [0, 3, 1, 2, 1, 3, 0, 0]
  let tri := getTriangleForPath pathDigits

  let ax0 : AxisCertificate := {
    edgeStart := ![3, 1, 13],
    edgeFinish := ![2, 4, 14],
    edgeStart₂ := ![2, 4, 14],
    edgeFinish₂ := ![1, 8, 15],
    mix := ![800, 800, 200],
    index := ![2, 4, 14],
    nonzeroWitness := ![9, 15, 1],
    B := 700862849 / 500000000
  }
  let ax1 : AxisCertificate := {
    edgeStart := ![15, 2, 8],
    edgeFinish := ![19, 1, 9],
    edgeStart₂ := ![19, 1, 9],
    edgeFinish₂ := ![3, 4, 10],
    mix := ![200, 200, 200],
    index := ![19, 1, 9],
    nonzeroWitness := ![8, 15, 2],
    B := 900388537 / 1000000000
  }
  let ax2 : AxisCertificate := {
    edgeStart := ![2, 10, 10],
    edgeFinish := ![1, 15, 15],
    edgeStart₂ := ![1, 15, 15],
    edgeFinish₂ := ![4, 19, 19],
    mix := ![0, 333, 0],
    index := ![1, 15, 15],
    nonzeroWitness := ![15, 1, 4],
    B := 50983457 / 100000000
  }
  let ax3 : AxisCertificate := {
    edgeStart := ![3, 4, 14],
    edgeFinish := ![2, 8, 15],
    edgeStart₂ := ![2, 8, 15],
    edgeFinish₂ := ![1, 9, 19],
    mix := ![800, 800, 800],
    index := ![2, 8, 15],
    nonzeroWitness := ![9, 19, 1],
    B := 664023711 / 500000000
  }

  let box : Box := {
    interval := AtlasPose.rootInterval ℚ,
    chart := 0, symmetryIndex := 0, root := 0,
    triangle := tri,
    certificate := fun | 0 => ax0 | 1 => ax1 | 2 => ax2 | 3 => ax3,
    c := 9 / 10000, δ := 6 / 10000, r := 1 / 2000
  }

  let mut allNonneg := true
  for j in [0, 1, 2, 3] do
    for i in [0, 1, 2] do
      if hj : j < 4 then
        if hi : i < 3 then
          let wl := box.weightLower ⟨j, hj⟩ ⟨i, hi⟩
          if wl < 0 then
            allNonneg := false
            IO.println s!"axis {j}, contact {i}: NEGATIVE weightLower = {wl}"

  IO.println s!"All weightLower nonneg: {allNonneg}"

  let c_cone_val : ℚ := 5 / 1000
  IO.println s!"barycentricValid with c_cone=5/1000, c+delta=15/10000: {decide (box.decomposedBarycentricValid c_cone_val)}"
