module

public import Minimality.Type08S.P2LXhi

@[expose] public section

set_option relaxedAutoImplicit true

/-!
# Lemma LX (ii) for SC2-V (package K): `lemmaSC2V_hi`, frame form, and the combined `lemmaSC2V_all`
-/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

variable {e1 e2 e3 : ℝ³}

/-- **Lemma LX (ii), SC2-V case `h_{x'} > h_f`** (`σ(zf - zp) < 0`), frame form.  Same hypotheses and conclusion
as `lemmaSC2V` except `hσ` (σ = ±1, as in the paper) and `hlo` in place of `0 ≤ σ(zf - zp)`.  No exception. -/
theorem lemmaSC2V_hi (hF : Fr e1 e2 e3) (o : ℝ³) (E : Finset ℝ³)
    {σ L zp zx zf Xr Yr zr Xg Yg zg : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hL : 0 < L) (hzx : 0 < σ * (zx - zp)) (hlo : σ * (zf - zp) < 0)
    (hcr : 0 < (Xg - Xr) * (-Yr) - (Yg - Yr) * (L - Xr)) (hYr : 0 < Yr) (hYg : 0 < Yg)
    (hcg : 0 < Yg * Xr - Xg * Yr) (hc : ClassV2tail L zx zf Xr Yr zr Xg Yg zg)
    (hE : ∀ᶠ s : ℝ in atTop, ∀ y ∈ E, TriCert (rim5 e1 e2 e3 o L zp zx zf Xr Yr zr Xg Yg zg E)
      (pc e1 e2 e3 0 0 1) (pc e1 e2 e3 (σ * s) (-σ) 0) y) :
    IsRupert (rim5 e1 e2 e3 o L zp zx zf Xr Yr zr Xg Yg zg E) := by
  have hσσ : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  -- a large `S`
  have e1' : ∀ᶠ S : ℝ in atTop, 0 < Xg + S * Yg :=
    (tendsto_atTop_add_const_left _ _ (tendsto_id.atTop_mul_const hYg)).eventually_gt_atTop 0
  have e2' : ∀ᶠ S : ℝ in atTop, 0 < Xr + S * Yr :=
    (tendsto_atTop_add_const_left _ _ (tendsto_id.atTop_mul_const hYr)).eventually_gt_atTop 0
  have e3' : ∀ᶠ S : ℝ in atTop, S * Xg - Yg ≠ 0 := by
    by_cases hX : Xg = 0
    · exact Filter.Eventually.of_forall fun S => by rw [hX]; simp; exact hYg.ne'
    · filter_upwards [Filter.eventually_ne_atTop (Yg / Xg)] with S hS h0
      apply hS
      field_simp
      linarith
  obtain ⟨S, hS1, hS2, hS3, hS4⟩ := (e1'.and (e2'.and (e3'.and hE))).exists
  set X := pent L zp zx zf Xr Yr zr Xg Yg zg with hX
  have hprX : ∀ j, pr e1 e2 e3 o (X j) ∈ rim5 e1 e2 e3 o L zp zx zf Xr Yr zr Xg Yg zg E := by
    intro j
    rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
      simp [hX, pent, five_0, five_1, five_2, five_3, five_4, pr, pt, rim5]
  refine rupert_of_rim5 hF o _ X hprX (σ * S) (-σ)
    (lx_cyc hL hzx hcr hYr hYg hcg hS1 hS2) ?_ ?_
  · intro y hy hyx
    simp only [rim5, Finset.mem_union] at hy
    rcases hy with h | h
    · exfalso
      simp only [Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with rfl | rfl | rfl | rfl | rfl
      · exact hyx 0 (by simp [hX, pent, five_0, pr, pt])
      · exact hyx 4 (by simp [hX, pent, five_4, pr, pt])
      · exact hyx 1 (by simp [hX, pent, five_1, pr, pt])
      · exact hyx 2 (by simp [hX, pent, five_2, pr, pt])
      · exact hyx 3 (by simp [hX, pent, five_3, pr, pt])
    · exact hS4 y h
  · have hd := lx_depth (S := S) hσσ hL hzx hlo hYr hS3 hc
    filter_upwards [hd] with s hs
    have key : (fun i => dep (σ * S) (-σ) s (X i)) = fun i => σ *
        (five (σ * zp) (σ * zf) (σ * zr) (σ * zg) (σ * zx) i +
          s * five 0 (S * L) (S * Xr - Yr) (S * Xg - Yg) 0 i) := by
      funext i
      rcases hσ with rfl | rfl <;>
      · rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
          simp only [hX, pent, dep, five_0, five_1, five_2, five_3, five_4] <;> ring
    rw [key]
    rcases hσ with rfl | rfl
    · left; simpa using hs
    · right; simpa using hs

end Type08Sp
end Minimality

#print axioms Minimality.Type08Sp.lemmaSC2V_hi
