import Noperthedron.Nopert229.AtlasProjectiveLocalViewTree
import Noperthedron.Nopert229.AtlasProjectiveAnnularCertificate

open Noperthedron.Nopert229
open Noperthedron.Nopert229.AtlasProjectiveLocalViewTree
open Noperthedron.Nopert229.AtlasProjectiveLocalCertificate
open Noperthedron.SnubCube.ProjectiveView

def getTriangleForPath (digits : List (Fin 4)) : AtlasProjectiveView.Triangle ℚ :=
  digits.foldl (fun t d => split t d) AtlasProjectiveView.upperWedgeTriangle

def pathDigits : List (Fin 4) := [0, 3, 1, 2, 1, 3, 0, 3, 2, 0, 0]
def tri := getTriangleForPath pathDigits

def ax0 : AxisCertificate := {
  edgeStart := ![3, 1, 13],
  edgeFinish := ![2, 4, 14],
  edgeStart₂ := ![2, 4, 14],
  edgeFinish₂ := ![1, 8, 15],
  mix := ![800, 800, 200],
  index := ![2, 4, 14],
  nonzeroWitness := ![9, 15, 1],
  B := 349290553/250000000
}

def ax1 : AxisCertificate := {
  edgeStart := ![2, 10, 2],
  edgeFinish := ![1, 15, 1],
  edgeStart₂ := ![1, 15, 1],
  edgeFinish₂ := ![4, 19, 4],
  mix := ![0, 333, 333],
  index := ![1, 15, 1],
  nonzeroWitness := ![15, 1, 15],
  B := 34623381/200000000
}

def ax2 : AxisCertificate := {
  edgeStart := ![2, 10, 3],
  edgeFinish := ![1, 15, 2],
  edgeStart₂ := ![1, 15, 2],
  edgeFinish₂ := ![4, 19, 1],
  mix := ![0, 666, 0],
  index := ![1, 15, 2],
  nonzeroWitness := ![15, 1, 10],
  B := 38424249/50000000
}

def ax3 : AxisCertificate := {
  edgeStart := ![2, 1, 15],
  edgeFinish := ![1, 4, 19],
  edgeStart₂ := ![1, 4, 19],
  edgeFinish₂ := ![4, 8, 3],
  mix := ![0, 333, 1000],
  index := ![1, 4, 19],
  nonzeroWitness := ![15, 19, 4],
  B := 245064413/500000000
}

def coreAxis2960 : AxisCertificate := {
  edgeStart := ![3, 1, 10],
  edgeFinish := ![2, 4, 15],
  edgeStart₂ := ![2, 4, 15],
  edgeFinish₂ := ![1, 8, 19],
  mix := ![0, 1000, 333],
  index := ![2, 4, 15],
  nonzeroWitness := ![10, 15, 1],
  B := 519773829 / 1000000000
}

def interval : AtlasInterval ℚ :=
  AtlasInterval.mk
    { θ := -1 / 100000, φ := -1 / 100000, x := -1 / 100000, y := -1 / 100000, z := -1 / 100000 }
    { θ := 1 / 100000, φ := 1 / 100000, x := 1 / 100000, y := 1 / 100000, z := 1 / 100000 }
    (by rw [AtlasPose.le_iff]; norm_num)

def box : Box := {
  interval := interval,
  chart := 0, symmetryIndex := 0, root := 0,
  triangle := tri,
  certificate := fun | 0 => ax0 | 1 => ax1 | 2 => ax2 | 3 => ax3,
  c := 1 / 1000,
  δ := 234013 / 1000000000,
  r := 4 / 100000
}

def c_cone : ℚ := 35 / 1000
def c_core : ℚ := 55 / 100000
def r_min : ℚ := 5 / 10000
def D0 : ℚ := 0
def defect0 : Fin 3 → ℚ := fun _ => 0

def main : IO Unit := do
  let u0 := box.approxNormalizedCenter 0
  let coreBox := box.withCoreAxis coreAxis2960 c_core r_min
  let v := coreBox.approxNormalizedCenter 0
  let u_sq := (u0 0)^2 + (u0 1)^2 + (u0 2)^2
  let v_dot_u := (v 0)*(u0 0) + (v 1)*(u0 1) + (v 2)*(u0 2)
  let lam := v_dot_u / u_sq
  let w : Fin 3 → ℚ := fun i => (v i) - lam * (u0 i)
  let w_sq := (w 0)^2 + (w 1)^2 + (w 2)^2

  IO.println s!"lam = {lam}"
  IO.println s!"w = ![{w 0}, {w 1}, {w 2}]"
  IO.println s!"hdecomp = {decide (coreBox.approxNormalizedCenter 0 = lam • box.approxNormalizedCenter 0 + w)}"
  IO.println s!"hortho = {decide ((∑ i, (box.approxNormalizedCenter 0 i) * (w i)) = 0)}"
  IO.println s!"hmargin = {decide (0 ≤ lam * c_cone - c_core)}"

  let lhs_hineq := w_sq * (u_sq - c_cone^2)
  let rhs_hineq := u_sq * (lam * c_cone - c_core)^2
  IO.println s!"hineq = {decide (lhs_hineq ≤ rhs_hineq)}"
  IO.println s!"FULL DecomposedViewValid = {decide (box.DecomposedViewValid coreAxis2960 defect0 D0 r_min c_cone c_core lam w)}"
