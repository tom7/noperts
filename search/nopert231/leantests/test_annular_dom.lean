import Noperthedron.Nopert229.TestEvalRealCage

open Noperthedron.Nopert229
open Noperthedron.Nopert229.AtlasProjectiveLocalCertificate

def w02 := box.weightUpper 0 2
def defect0 : Fin 3 → ℚ := ![0, 0, 21 / 100000]
def D0 : ℚ := w02 * (21 / 100000)
def c_cone : ℚ := 17 / 1000
def r_min : ℚ := 31 / 100000

#eval w02
#eval D0

def hannular_dominance : Bool :=
  let B := (box.certificate 0).B
  let lhs := ((1 / 2 : ℚ) * box.r ^ 2 * B + D0) ^ 2
  let rhs := r_min ^ 2 * (1 - (1 / 4 : ℚ) * box.r ^ 2) * ((c_cone - box.δ) ^ 2 * B ^ 2)
  lhs ≤ rhs

#eval hannular_dominance
