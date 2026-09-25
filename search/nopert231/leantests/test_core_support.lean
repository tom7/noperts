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

  let coreAx : AxisCertificate := {
    edgeStart := ![2, 14, 2],
    edgeFinish := ![1, 15, 1],
    edgeStart₂ := ![1, 15, 1],
    edgeFinish₂ := ![4, 19, 4],
    mix := ![0, 500, 500],
    index := ![1, 15, 1],
    nonzeroWitness := ![15, 1, 15],
    B := 122343351 / 500000000
  }

  let axDummy : AxisCertificate := coreAx
  let box : Box := {
    interval := AtlasPose.rootInterval ℚ,
    chart := 0, symmetryIndex := 0, root := 0,
    triangle := tri,
    certificate := fun _ => axDummy,
    c := 9 / 10000,
    δ := 21 / 10000,
    r := 1 / 2000
  }

  let coreBox := box.withCoreAxis coreAx (7 / 10000) (1 / 1000)

  let mut supp_ok := true
  for i in [0, 1, 2] do
    for k in [0:20] do
      if hi : i < 3 then
        if hk : k < 20 then
          let s := coreBox.supportUpper 0 ⟨i, hi⟩ ⟨k, hk⟩
          if s > 0 then
            supp_ok := false
            IO.println s!"core contact {i}, vertex {k}: POSITIVE support = {s}"
  IO.println s!"core supp_ok = {supp_ok}"

  let var_lhs := coreBox.variationRadiusSum 0 + 3 * variationError
  let var_rhs := coreAx.B * coreBox.δ
  let var_ok := decide (var_lhs ≤ var_rhs)
  IO.println s!"core var_ok = {var_ok}, var_lhs = {var_lhs}, var_rhs = {var_rhs}"
