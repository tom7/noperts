import Noperthedron.Nopert229.TestEvalRealCage

open Noperthedron Noperthedron.Nopert229
open AtlasProjectiveLocalCertificate

def defect0 : Fin 3 → ℚ := fun
  | 0 => 0
  | 1 => 0
  | 2 => 205 / 1000000

def D0 : ℚ := 1 / 10000

theorem h_defect_budget0 : (∑ i, box.weightUpper 0 i * defect0 i) ≤ D0 := by
  have hsum : (∑ i, box.weightUpper 0 i * defect0 i) =
      box.weightUpper 0 0 * 0 +
      box.weightUpper 0 1 * 0 +
      box.weightUpper 0 2 * (205 / 1000000) := by
    rw [Fin.sum_univ_three]
    dsimp [defect0]
  rw [hsum]
  have h_le : box.weightUpper 0 2 ≤ 2 / 5 := by decide +kernel
  have h_nonneg : 0 ≤ box.weightUpper 0 2 := by decide +kernel
  dsimp [D0]
  linarith
