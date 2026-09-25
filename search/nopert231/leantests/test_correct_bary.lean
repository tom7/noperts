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
  edgeStart := ![2, 1, 4],
  edgeFinish := ![10, 15, 19],
  edgeStart₂ := ![10, 15, 19],
  edgeFinish₂ := ![2, 1, 4],
  mix := ![0, 333, 333],
  index := ![10, 15, 19],
  nonzeroWitness := ![15, 1, 15],
  B := 34623381/200000000
}

def ax2 : AxisCertificate := {
  edgeStart := ![2, 1, 4],
  edgeFinish := ![10, 15, 19],
  edgeStart₂ := ![10, 15, 19],
  edgeFinish₂ := ![3, 2, 1],
  mix := ![0, 666, 0],
  index := ![10, 15, 19],
  nonzeroWitness := ![15, 1, 10],
  B := 38424249/50000000
}

def ax3 : AxisCertificate := {
  edgeStart := ![2, 1, 4],
  edgeFinish := ![1, 4, 8],
  edgeStart₂ := ![1, 4, 8],
  edgeFinish₂ := ![15, 19, 3],
  mix := ![0, 333, 1000],
  index := ![1, 4, 8],
  nonzeroWitness := ![15, 19, 4],
  B := 245064413/500000000
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

#eval decide (box.decomposedBarycentricValid (35 / 1000))
