module

public import Mathlib
public import MinimalityExtra

/-!
# The HDN equation, single-view Farkas, and circle reduction
-/

@[expose] public section

open Matrix

namespace MinimalityExtra

theorem hdnEquation : HdnEquation := by
  intro G hG a b c u lam _ hl
  have hs : G.transpose = G := hG.isHermitian.eq
  have h10 : G 1 0 = G 0 1 := by simpa using congrFun (congrFun hs 0) 1
  have h20 : G 2 0 = G 0 2 := by simpa using congrFun (congrFun hs 0) 2
  have h21 : G 2 1 = G 1 2 := by simpa using congrFun (congrFun hs 1) 2
  set e := b - a with he
  set w := c - a with hw
  have hy : a + lam • e - c = lam • e - w := by rw [hw]; abel
  constructor
  · rw [hy, sub_dotProduct, smul_dotProduct, smul_eq_mul]
    linear_combination (e ⬝ᵥ G *ᵥ e) * hl
  · simp [Matrix.adjugate_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_three, cross_apply, h10, h20, h21]
    ring

theorem singleViewFarkas : SingleViewFarkas := by
  intro ι P p r hr ⟨c, hc, hsum⟩ ⟨G, hG, hreal⟩
  have hpos : 0 < r ⬝ᵥ G *ᵥ r := hG.dotProduct_mulVec_pos hr
  have h1 : (-r) ⬝ᵥ G *ᵥ r = ∑ q ∈ p, c q * ((P q.1 - P q.2) ⬝ᵥ G *ᵥ r) := by
    conv_lhs => rw [hsum]
    rw [sum_dotProduct]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [smul_dotProduct, smul_eq_mul]
  have h2 : 0 ≤ ∑ q ∈ p, c q * ((P q.1 - P q.2) ⬝ᵥ G *ᵥ r) := by
    refine Finset.sum_nonneg fun q hq => mul_nonneg (hc q hq) ?_
    rw [sub_dotProduct]; linarith [hreal q hq]
  rw [neg_dotProduct] at h1
  linarith

#print axioms hdnEquation
#print axioms singleViewFarkas

theorem circleReduction : CircleReduction := by
  intro G n d m v r _ _ hd _ _ hnr
  have key : r ⬝ᵥ G *ᵥ d = 0 := by
    rw [hd, dotProduct_comm]; exact hnr
  simp only [mulVec_sub, mulVec_smul, dotProduct_sub, dotProduct_smul, smul_eq_mul, key]
  ring

/-- Action of `1 - d nᵀ`. -/
lemma pMat_mulVec (n d x : Fin 3 → ℝ) :
    (1 - vecMulVec d n) *ᵥ x = x - (n ⬝ᵥ x) • d := by
  rw [sub_mulVec, one_mulVec, vecMulVec_mulVec]
  ext i
  simp [Pi.smul_apply]

/-- Bilinear form of `Pᵀ Y P + n nᵀ`. -/
lemma gBil (Y P : Matrix (Fin 3) (Fin 3) ℝ) (n x s : Fin 3 → ℝ) :
    x ⬝ᵥ (Pᵀ * Y * P + vecMulVec n n) *ᵥ s
      = (P *ᵥ x) ⬝ᵥ (Y *ᵥ (P *ᵥ s)) + (n ⬝ᵥ x) * (n ⬝ᵥ s) := by
  rw [add_mulVec, dotProduct_add, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec,
    vecMul_transpose, vecMulVec_mulVec]
  simp [dotProduct_smul, dotProduct_comm]
  ring

theorem circleReductionExists : CircleReductionExists := by
  intro Y n m g hYs hnm hng hY
  have hYt : Yᵀ = Y := hYs
  have hnd : n ⬝ᵥ (m + g) = 1 := by rw [dotProduct_add, hnm, hng, add_zero]
  obtain ⟨d, hd⟩ : ∃ d, d = m + g := ⟨_, rfl⟩
  rw [← hd] at hnd ⊢
  obtain ⟨P, hPdef⟩ : ∃ P : Matrix (Fin 3) (Fin 3) ℝ, P = 1 - vecMulVec d n := ⟨_, rfl⟩
  have hPx : ∀ x, P *ᵥ x = x - (n ⬝ᵥ x) • d := fun x => by
    rw [hPdef]; exact pMat_mulVec n d x
  have hPd : P *ᵥ d = 0 := by rw [hPx, hnd, one_smul, sub_self]
  have hnPx : ∀ x, n ⬝ᵥ (P *ᵥ x) = 0 := by
    intro x
    rw [hPx, dotProduct_sub, dotProduct_smul, hnd, smul_eq_mul, mul_one, sub_self]
  have hvt : (vecMulVec n n)ᵀ = vecMulVec n n := by
    ext i j; simp [vecMulVec, mul_comm]
  have hherm : (Pᵀ * Y * P + vecMulVec n n).IsHermitian := by
    simp [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial, transpose_add,
      transpose_mul, hYt, hvt, mul_assoc]
  have hGv : ∀ s, (Pᵀ * Y * P + vecMulVec n n) *ᵥ s
      = Pᵀ *ᵥ (Y *ᵥ (P *ᵥ s)) + (n ⬝ᵥ s) • n := by
    intro s
    rw [add_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, vecMulVec_mulVec]
    simp
  refine ⟨Pᵀ * Y * P + vecMulVec n n, ?_, ?_, ?_⟩
  · refine Matrix.PosDef.of_dotProduct_mulVec_pos hherm ?_
    intro x hx
    have hstar : star x = x := funext fun i => star_trivial (x i)
    rw [hstar, gBil]
    by_cases hc : n ⬝ᵥ x = 0
    · have hPxe : P *ᵥ x = x := by rw [hPx, hc, zero_smul, sub_zero]
      rw [hPxe, hc]
      simpa using hY x hc hx
    · have hnn : 0 < (n ⬝ᵥ x) * (n ⬝ᵥ x) := mul_self_pos.mpr hc
      have hnonneg : 0 ≤ (P *ᵥ x) ⬝ᵥ (Y *ᵥ (P *ᵥ x)) := by
        by_cases hz : P *ᵥ x = 0
        · rw [hz]; simp
        · exact (hY _ (hnPx x) hz).le
      linarith
  · rw [hGv, hPd, mulVec_zero, mulVec_zero, zero_add, hnd, one_smul]
  · intro r s hr hs
    rw [gBil, hPx, hPx, hr, hs]
    simp

end MinimalityExtra
