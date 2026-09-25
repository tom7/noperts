import Noperthedron.Nopert229.AtlasProjectiveLocalViewTree
import Noperthedron.Nopert229.AtlasProjectiveAnnularCertificate

open Noperthedron.Nopert229
open Noperthedron.Nopert229.AtlasProjectiveLocalViewTree
open Noperthedron.Nopert229.AtlasProjectiveLocalCertificate
open Noperthedron.SnubCube.ProjectiveView

def getTriangleForPath (digits : List (Fin 4)) : AtlasProjectiveView.Triangle ℚ :=
  digits.foldl (fun t d => split t d) AtlasProjectiveView.upperWedgeTriangle

def main : IO Unit := do
  let pathDigits : List (Fin 4) := [0, 3, 1, 2, 1, 3, 0, 3, 2, 0, 0]
  let tri := getTriangleForPath pathDigits

  let ax0 : AxisCertificate := {
    edgeStart := ![3, 1, 13],
    edgeFinish := ![2, 4, 14],
    edgeStart₂ := ![2, 4, 14],
    edgeFinish₂ := ![1, 8, 15],
    mix := ![800, 800, 200],
    index := ![2, 4, 14],
    nonzeroWitness := ![9, 15, 1],
    B := 349290553/250000000
  }
  let ax1 : AxisCertificate := {
    edgeStart := ![15, 2, 8],
    edgeFinish := ![19, 1, 9],
    edgeStart₂ := ![19, 1, 9],
    edgeFinish₂ := ![3, 4, 10],
    mix := ![200, 200, 200],
    index := ![19, 1, 9],
    nonzeroWitness := ![8, 15, 2],
    B := 898810711/1000000000
  }
  let ax2 : AxisCertificate := {
    edgeStart := ![2, 10, 10],
    edgeFinish := ![1, 15, 15],
    edgeStart₂ := ![1, 15, 15],
    edgeFinish₂ := ![4, 19, 19],
    mix := ![0, 333, 0],
    index := ![1, 15, 15],
    nonzeroWitness := ![15, 1, 4],
    B := 509162627/1000000000
  }
  let ax3 : AxisCertificate := {
    edgeStart := ![3, 4, 14],
    edgeFinish := ![2, 8, 15],
    edgeStart₂ := ![2, 8, 15],
    edgeFinish₂ := ![1, 9, 19],
    mix := ![800, 800, 800],
    index := ![2, 8, 15],
    nonzeroWitness := ![9, 19, 1],
    B := 1324415559/1000000000
  }
  let coreAxis : AxisCertificate := {
    edgeStart := ![3, 1, 14],
    edgeFinish := ![2, 4, 15],
    edgeStart₂ := ![2, 4, 15],
    edgeFinish₂ := ![1, 8, 19],
    mix := ![800, 800, 400],
    index := ![2, 4, 15],
    nonzeroWitness := ![9, 15, 1],
    B := 638283927/500000000
  }

  let box : Box := {
    interval := AtlasPose.rootInterval ℚ,
    chart := 0, symmetryIndex := 0, root := 0,
    triangle := tri,
    certificate := fun | 0 => ax0 | 1 => ax1 | 2 => ax2 | 3 => ax3,
    c := 22779/500000,
    δ := 50071/200000000,
    r := 1 / 500
  }

  let c_core : ℚ := 5 / 1000
  let r_min : ℚ := 1 / 500
  let cbox := box.withCoreAxis coreAxis c_core r_min

  let u0 : Fin 3 → ℚ := box.approxNormalizedCenter 0
  let u1 : Fin 3 → ℚ := box.approxNormalizedCenter 1
  let u2 : Fin 3 → ℚ := box.approxNormalizedCenter 2
  let u3 : Fin 3 → ℚ := box.approxNormalizedCenter 3
  let uc : Fin 3 → ℚ := cbox.approxNormalizedCenter 0

  IO.println s!"u0 = ![{u0 0}, {u0 1}, {u0 2}]"
  IO.println s!"u1 = ![{u1 0}, {u1 1}, {u1 2}]"
  IO.println s!"u2 = ![{u2 0}, {u2 1}, {u2 2}]"
  IO.println s!"u3 = ![{u3 0}, {u3 1}, {u3 2}]"
  IO.println s!"uc = ![{uc 0}, {uc 1}, {uc 2}]"

  -- Calculate exact lam and w directly from Lean's centers:
  let u0_sq := (u0 0)^2 + (u0 1)^2 + (u0 2)^2
  let dot_u0_uc := (u0 0)*(uc 0) + (u0 1)*(uc 1) + (u0 2)*(uc 2)
  let lam_exact := dot_u0_uc / u0_sq
  let w_exact : Fin 3 → ℚ := fun i => uc i - lam_exact * u0 i
  let w_sq := (w_exact 0)^2 + (w_exact 1)^2 + (w_exact 2)^2

  IO.println s!"lam_exact = {lam_exact}"
  IO.println s!"w_exact = ![{w_exact 0}, {w_exact 1}, {w_exact 2}]"
  IO.println s!"u0_sq = {u0_sq}"
  IO.println s!"w_sq = {w_sq}"

  -- Test hdecomp:
  let decomp_ok := decide (uc = fun i => lam_exact * u0 i + w_exact i)
  IO.println s!"decomp_ok = {decomp_ok}"

  -- Test max supportUpper for ax0:
  for i in [0, 1, 2] do
    let mut max_s : ℚ := -1000
    for k in [0:20] do
      if h3 : i < 3 then
        if h20 : k < 20 then
          let s := box.supportUpper 0 ⟨i, h3⟩ ⟨k, h20⟩
          if s > max_s then max_s := s
    IO.println s!"ax0 contact {i} max supportUpper = {max_s}"

  -- Print centers done.


