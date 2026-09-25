import Noperthedron.Nopert229.TestEvalRealCage

open Noperthedron Noperthedron.Nopert229
open AtlasProjectiveLocalCertificate

def defect0 : Fin 3 → ℚ := fun
  | 0 => 0
  | 1 => 0
  | 2 => 205 / 1000000

theorem h_supp : ∀ j i k, box.supportUpper j i k ≤ if j = 0 then defect0 i else 0 := by decide +kernel
