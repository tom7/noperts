import Noperthedron.Nopert229.TestEvalRealCage

open Noperthedron Noperthedron.Nopert229

def maxSupp (j : Fin 4) (i : Fin 3) : ℚ :=
  let vals := (List.range 24).map (fun k =>
    if hk : k < 20 then
      box.supportUpper j i ⟨k, hk⟩
    else 0)
  vals.foldl max (-1000)

def defect0 : Fin 3 → ℚ := fun i => max 0 (maxSupp 0 i)

#eval defect0 0
#eval defect0 1
#eval defect0 2

#eval decide (∀ (j : Fin 4) (i : Fin 3) (k : Nopert229.VertexIndex),
  box.supportUpper j i k ≤ if j = 0 then defect0 i else 0)

#eval decide (∀ (j : Fin 4), box.variationRadiusSum j + 3 * variationError ≤ (box.certificate j).B * box.δ)
#eval decide (∀ (j : Fin 4) (i : Fin 3), box.supportUpper j i ((box.certificate j).nonzeroWitness i) < 0)
#eval decide (∀ (j : Fin 4), box.weightBudget j ≤ (box.certificate j).B)
#eval decide (∀ (j : Fin 4) (i : Fin 3), 0 ≤ box.weightLower j i)
#eval decide (∀ (j : Fin 4), ∃ i, 0 < box.weightLower j i)
#eval decide (box.r ^ 2 * (1 + (box.c - box.δ) ^ 2) ≤ 4 * (box.c - box.δ) ^ 2)
