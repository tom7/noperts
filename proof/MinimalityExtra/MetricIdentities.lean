module

public import Mathlib
public import MinimalityExtra

/-!
# The HDN equation and single-view Farkas
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

end MinimalityExtra
