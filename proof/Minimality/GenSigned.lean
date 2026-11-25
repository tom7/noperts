module

public import Mathlib

@[expose] public section

/-!
# Two positive linear forms on a positive-definite 2x2 pencil

`exists_signed_of_pd2`: if `m₁, m₂` make the rows `α i m₁ + β i m₂` positive, and the Gram data
`EA, EB, h` are positive definite (`EA, EB > 0`, `h² < EA EB`), then for any signs `sA, sB` with
`sA (EB m₁ − h m₂) > 0` and `sB (EA m₂ − h m₁) > 0` there are `lA, lB` of signs `sA, sB` such that the
rows stay positive at the image `(lA EA + lB h, lA h + lB EB)` of `(lA, lB)` under the Gram matrix.
(The solution is `lA = EB m₁ − h m₂`, `lB = EA m₂ − h m₁`, i.e. the inverse Gram image of `m`, times
`det = EA EB − h²`.)
-/

set_option autoImplicit false

namespace Minimality

theorem exists_signed_of_pd2 {EA EB h : ℝ} (hEA : 0 < EA) (hEB : 0 < EB) (hD : h ^ 2 < EA * EB)
    {sA sB : ℝ} (α β : Fin 3 → ℝ) (m₁ m₂ : ℝ)
    (hm : ∀ i, 0 < α i * m₁ + β i * m₂)
    (hA : 0 < sA * (EB * m₁ - h * m₂)) (hB : 0 < sB * (EA * m₂ - h * m₁)) :
    ∃ lA lB : ℝ, 0 < sA * lA ∧ 0 < sB * lB ∧
      ∀ i, 0 < α i * (lA * EA + lB * h) + β i * (lA * h + lB * EB) := by
  refine ⟨EB * m₁ - h * m₂, EA * m₂ - h * m₁, hA, hB, fun i => ?_⟩
  have e : α i * ((EB * m₁ - h * m₂) * EA + (EA * m₂ - h * m₁) * h) +
      β i * ((EB * m₁ - h * m₂) * h + (EA * m₂ - h * m₁) * EB) =
      (EA * EB - h ^ 2) * (α i * m₁ + β i * m₂) := by ring
  rw [e]; exact mul_pos (by linarith) (hm i)

end Minimality
