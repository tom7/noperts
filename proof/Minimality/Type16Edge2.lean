module

public import Minimality.Type16Seg35

@[expose] public section

/-!
# Type 16: no horizontal-double-normal exception at `15`, `25`, `03`, `36` (§22)

The certificates of the cover at the views along `15`, `25`, `03`, `36` are edge pairs (Lemma E),
the triangle closings D6 and its image, and the pair certificates `T_c` (Lemma 19.5, four or
five corners) and `B` (Lemma 19.4, five corners) with their images.  The edge pairs are closed
by §22 (`isRupert_ePair_limit`), the others are realized on both face circles (their sides on the
faces are edges of the faces) and closed by Proposition 22.2 (`isRupert_eTri_limit`,
`isRupert_twoFace_limit`), under the codimension-2 conditions `Gen15`, `Gen25`, `Gen03`, `Gen36`.
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

/-! ### Helpers -/

/-- A determinant of three points of a face against its normal is nonzero when the points are
not collinear. -/
theorem det3_face_ne {N p q m : ℝ³} (hq : ⟪N, q - p⟫ = 0) (hm : ⟪N, m - p⟫ = 0)
    (hc : cross (q - p) (m - p) ≠ 0) (hN : N ≠ 0) : det3 (q - p) (m - p) N ≠ 0 := by
  have hpar : cross N (cross (q - p) (m - p)) = 0 := by
    have e1 : ⟪q - p, N⟫ = 0 := by rw [real_inner_comm]; exact hq
    have e2 : ⟪m - p, N⟫ = 0 := by rw [real_inner_comm]; exact hm
    have e : cross (cross (q - p) (m - p)) N = 0 := by
      rw [cross_cross_eq, e1, e2, zero_smul, zero_smul, sub_zero]
    have : cross N (cross (q - p) (m - p)) = -cross (cross (q - p) (m - p)) N := by
      ext j; fin_cases j <;> simp [cross] <;> ring
    rw [this, e, neg_zero]
  obtain ⟨t, ht⟩ : ∃ t : ℝ, cross (q - p) (m - p) = t • N :=
    ⟨_, eq_smul_of_cross_eq_zero hN hpar⟩
  have ht0 : t ≠ 0 := by rintro rfl; rw [zero_smul] at ht; exact hc ht
  rw [det3, ht, real_inner_smul_left]
  exact mul_ne_zero ht0 (real_inner_self_pos.mpr hN).ne'

theorem Face16.N_ne {x : Fin 7 → ℝ³} {S : Finset (Fin 7)} (F : Face16 x S) {i j : Fin 7}
    (hi : i ∈ S) (hj : j ∉ S) : F.N ≠ 0 := by
  intro h0
  have := F.hN (x j) (x i)
  rw [h0, inner_zero_left, F.zero i hi, sub_zero] at this
  exact (F.neg j hj).ne this

theorem rimCertAt_quad {y : Fin 7 → ℝ³} {u : ℝ³} {a b c d : Fin 7}
    (h : RimCertPts (univ.image y) u (quad (y a) (y b) (y c) (y d))) :
    RimCertAt y u (quad a b c d) := by
  have e : ∀ i, y (quad a b c d i) = quad (y a) (y b) (y c) (y d) i := by
    intro i; rcases zmod4_cases i with rfl | rfl | rfl | rfl <;> rfl
  refine ⟨h.three, fun i j hi hj => ?_, fun m i => ?_, ?_⟩
  · rw [e, e, e]; exact h.cyc i j hi hj
  · rw [e, e]; exact h.left _ (mem_image_of_mem y (mem_univ m)) i
  · simp only [e]; exact h.robust

/-! ### The conditions at `15`, `25`, `03`, `36` -/

/-! ### The limit with the alternatives at the six quadrilateral segments -/

/-! ### The facets form -/

end Minimality

end
