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

def box_r : ℚ := 4 / 100000
def box_delta : ℚ := 234013 / 1000000000
def c_cone : ℚ := 20 / 1000
def D0 : ℚ := 0

def main : IO Unit := do
  for r_min_num in [1, 2, 5, 10, 50, 100] do
    let r_min : ℚ := r_min_num / 10000000
    let lhs := ((1 / 2 : ℚ) * box_r ^ 2 * ax0.B + D0) ^ 2
    let rhs := r_min ^ 2 * (1 - (1 / 4 : ℚ) * box_r ^ 2) * ((c_cone - box_delta) ^ 2 * ax0.B ^ 2)
    let ann := decide (lhs ≤ rhs)
    -- Also test c_core = 25 / 100000 = 0.00025:
    let c_core : ℚ := 25 / 100000
    let core_angle := decide (r_min ^ 2 * (1 + (c_core - box_delta) ^ 2) ≤ 4 * (c_core - box_delta) ^ 2)
    IO.println s!"r_min = {r_min_num}/10^7: ann={ann}, core_angle={core_angle}"
