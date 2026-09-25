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
  mix := ![150, 1000, 882],
  index := ![2, 4, 14],
  nonzeroWitness := ![9, 15, 1],
  B := 691098263/1000000000
}

def ax1 : AxisCertificate := {
  edgeStart := ![2, 10, 19],
  edgeFinish := ![1, 15, 3],
  edgeStart₂ := ![1, 15, 3],
  edgeFinish₂ := ![4, 19, 2],
  mix := ![50, 800, 950],
  index := ![1, 15, 3],
  nonzeroWitness := ![15, 1, 8],
  B := 2446223/1562500
}

def ax2 : AxisCertificate := {
  edgeStart := ![2, 8, 9],
  edgeFinish := ![1, 9, 10],
  edgeStart₂ := ![1, 9, 10],
  edgeFinish₂ := ![4, 10, 15],
  mix := ![1000, 1000, 343],
  index := ![1, 9, 10],
  nonzeroWitness := ![10, 3, 1],
  B := 41011137/62500000
}

def ax3 : AxisCertificate := {
  edgeStart := ![3, 1, 10],
  edgeFinish := ![2, 4, 15],
  edgeStart₂ := ![2, 4, 15],
  edgeFinish₂ := ![1, 8, 19],
  mix := ![113, 320, 150],
  index := ![2, 4, 15],
  nonzeroWitness := ![9, 19, 4],
  B := 711802171/1000000000
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

def c_cone : ℚ := 15 / 1000

theorem h_bary : box.decomposedBarycentricValid c_cone := by
  native_decide
