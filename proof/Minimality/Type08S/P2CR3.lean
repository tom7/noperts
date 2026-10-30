module

public import Minimality.Type08S.P2CR2

@[expose] public section

set_option relaxedAutoImplicit true

/-!
# P3a core, part 3: the middles over the side `x f` along the slide `u₀ + t e` (`hM`).

Plane `Y = 0` of the frame.  `x = (0,0,κ)`, `f = (L,0,zf)`, `u₀ = κv e3`, `e = c e1`.  A point
`m = (Xm, 0, zm)` is `x + s (f - x) + δ (u₀ + t e)` with
`det = L κv - t c (zf - κ)`, `s = (Xm κv - t c (zm - κ)) / det`, `δ = (L (zm - κ) - Xm (zf - κ)) / det`.
-/

set_option autoImplicit true
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

variable {e1 e2 e3 : ℝ³}

theorem mid_vec (O : ℝ³) {Xm zm κ L zf κv t c s δ : ℝ}
    (hs : s * L + δ * (t * c) = Xm) (hz : s * (zf - κ) + δ * κv = zm - κ) :
    fpt e1 e2 e3 O Xm 0 zm = fpt e1 e2 e3 O 0 0 κ +
      s • (fpt e1 e2 e3 O L 0 zf - fpt e1 e2 e3 O 0 0 κ) + δ • (κv • e3 + t • (c • e1)) := by
  have h : fpt e1 e2 e3 O Xm 0 zm - (fpt e1 e2 e3 O 0 0 κ +
      s • (fpt e1 e2 e3 O L 0 zf - fpt e1 e2 e3 O 0 0 κ) + δ • (κv • e3 + t • (c • e1))) =
      (Xm - (s * L + δ * (t * c))) • e1 + (zm - κ - (s * (zf - κ) + δ * κv)) • e3 := by
    simp only [fpt, pc]; module
  rw [hs, hz] at h
  simp only [sub_self, zero_smul, add_zero] at h
  exact sub_eq_zero.mp h

/-- The solution of the `2 × 2` system. -/
theorem mid_solve {Xm zm κ L zf κv t c : ℝ} (hd : L * κv - t * c * (zf - κ) ≠ 0) :
    ((Xm * κv - t * c * (zm - κ)) / (L * κv - t * c * (zf - κ))) * L +
      ((L * (zm - κ) - Xm * (zf - κ)) / (L * κv - t * c * (zf - κ))) * (t * c) = Xm ∧
    ((Xm * κv - t * c * (zm - κ)) / (L * κv - t * c * (zf - κ))) * (zf - κ) +
      ((L * (zm - κ) - Xm * (zf - κ)) / (L * κv - t * c * (zf - κ))) * κv = zm - κ := by
  constructor
  · rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hd]; ring
  · rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hd]; ring

/-- A middle strictly over the open side `x f` already at `t = 0`. -/
theorem mid_exists_open (O : ℝ³) {Xm zm κ L zf κv c : ℝ} (hL : 0 < L) (hκv : κv ≠ 0)
    (h0 : 0 < Xm) (h1 : Xm < L) (hD : L * (zm - κ) - Xm * (zf - κ) ≠ 0) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
      fpt e1 e2 e3 O Xm 0 zm = fpt e1 e2 e3 O 0 0 κ +
        s • (fpt e1 e2 e3 O L 0 zf - fpt e1 e2 e3 O 0 0 κ) + δ • (κv • e3 + t • (c • e1)) := by
  have hd0 : L * κv - 0 * c * (zf - κ) ≠ 0 := by simpa using mul_ne_zero hL.ne' hκv
  have hcd : ContinuousAt (fun t : ℝ => L * κv - t * c * (zf - κ)) 0 := by fun_prop
  have hS : ContinuousAt (fun t : ℝ => (Xm * κv - t * c * (zm - κ)) / (L * κv - t * c * (zf - κ))) 0 :=
    ContinuousAt.div (by fun_prop) hcd hd0
  have hDl : ContinuousAt (fun t : ℝ => (L * (zm - κ) - Xm * (zf - κ)) / (L * κv - t * c * (zf - κ))) 0 :=
    ContinuousAt.div (by fun_prop) hcd hd0
  have hS0 : (Xm * κv - 0 * c * (zm - κ)) / (L * κv - 0 * c * (zf - κ)) = Xm / L := by
    rw [div_eq_div_iff hd0 hL.ne']; ring
  have e1' : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < (Xm * κv - t * c * (zm - κ)) / (L * κv - t * c * (zf - κ)) := by
    refine hS.eventually (lt_mem_nhds ?_)
    beta_reduce; rw [hS0]; exact div_pos h0 hL
  have e2' : ∀ᶠ t in 𝓝 (0 : ℝ), (Xm * κv - t * c * (zm - κ)) / (L * κv - t * c * (zf - κ)) < 1 := by
    refine hS.eventually (gt_mem_nhds ?_)
    beta_reduce; rw [hS0]; exact (div_lt_one hL).mpr h1
  have e3' : ∀ᶠ t in 𝓝 (0 : ℝ), (L * (zm - κ) - Xm * (zf - κ)) / (L * κv - t * c * (zf - κ)) ≠ 0 := by
    refine hDl.eventually (isOpen_ne.mem_nhds ?_)
    simp only [zero_mul, zero_sub, sub_zero]
    exact div_ne_zero hD (by simpa using mul_ne_zero hL.ne' hκv)
  have e4' : ∀ᶠ t in 𝓝 (0 : ℝ), L * κv - t * c * (zf - κ) ≠ 0 :=
    hcd.eventually (isOpen_ne.mem_nhds hd0)
  filter_upwards [nhdsWithin_le_nhds (e1'.and (e2'.and (e3'.and e4')))] with t ht
  obtain ⟨ht1, ht2, ht3, ht4⟩ := ht
  obtain ⟨hs, hz⟩ := mid_solve (Xm := Xm) (zm := zm) (c := c) ht4
  exact ⟨_, _, ht1, ht2, ht3, mid_vec O hs hz⟩

/-- The origin `x'` becomes a middle over the open side `x f` for `t > 0` when
`c = κ κv` (so that `s ~ t κ² / L > 0`). -/
theorem mid_exists_origin (O : ℝ³) {κ L zf κv : ℝ} (hL : 0 < L) (hκ : κ ≠ 0) (hκv : κv ≠ 0) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
      fpt e1 e2 e3 O 0 0 0 = fpt e1 e2 e3 O 0 0 κ +
        s • (fpt e1 e2 e3 O L 0 zf - fpt e1 e2 e3 O 0 0 κ) + δ • (κv • e3 + t • ((κ * κv) • e1)) := by
  set c := κ * κv with hc
  have hd0 : L * κv - 0 * c * (zf - κ) ≠ 0 := by simpa using mul_ne_zero hL.ne' hκv
  have hcd : ContinuousAt (fun t : ℝ => L * κv - t * c * (zf - κ)) 0 := by fun_prop
  -- `s = t * g t`, `g t = c κ / det`
  have hg : ContinuousAt (fun t : ℝ => (c * κ) / (L * κv - t * c * (zf - κ))) 0 :=
    ContinuousAt.div (by fun_prop) hcd hd0
  have hg0 : 0 < (c * κ) / (L * κv - 0 * c * (zf - κ)) := by
    have : (c * κ) / (L * κv - 0 * c * (zf - κ)) = κ ^ 2 / L := by
      rw [div_eq_div_iff hd0 hL.ne', hc]; ring
    rw [this]; positivity
  have hDl : ContinuousAt (fun t : ℝ => (L * (0 - κ) - 0 * (zf - κ)) / (L * κv - t * c * (zf - κ))) 0 :=
    ContinuousAt.div (by fun_prop) hcd hd0
  have e1' : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < (c * κ) / (L * κv - t * c * (zf - κ)) :=
    hg.eventually (lt_mem_nhds hg0)
  have hts : ContinuousAt (fun t : ℝ => t * ((c * κ) / (L * κv - t * c * (zf - κ)))) 0 :=
    ContinuousAt.mul continuousAt_id hg
  have e2' : ∀ᶠ t in 𝓝 (0 : ℝ), t * ((c * κ) / (L * κv - t * c * (zf - κ))) < 1 :=
    hts.eventually (gt_mem_nhds (by simp))
  have e3' : ∀ᶠ t in 𝓝 (0 : ℝ), (L * (0 - κ) - 0 * (zf - κ)) / (L * κv - t * c * (zf - κ)) ≠ 0 := by
    refine hDl.eventually (isOpen_ne.mem_nhds ?_)
    simp only [zero_mul, zero_sub, sub_zero]
    refine div_ne_zero ?_ (by simpa using mul_ne_zero hL.ne' hκv)
    simpa using mul_ne_zero hL.ne' hκ
  have e4' : ∀ᶠ t in 𝓝 (0 : ℝ), L * κv - t * c * (zf - κ) ≠ 0 :=
    hcd.eventually (isOpen_ne.mem_nhds hd0)
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (e1'.and (e2'.and (e3'.and e4')))] with t ht0 ht
  obtain ⟨ht1, ht2, ht3, ht4⟩ := ht
  have ht0' : 0 < t := ht0
  obtain ⟨hs, hz⟩ := mid_solve (Xm := 0) (zm := 0) (c := c) (κ := κ) (L := L) (zf := zf) (κv := κv) (t := t) ht4
  refine ⟨_, _, ?_, ?_, ht3, mid_vec O hs hz⟩
  · have : (0 * κv - t * c * (0 - κ)) / (L * κv - t * c * (zf - κ)) =
        t * ((c * κ) / (L * κv - t * c * (zf - κ))) := by ring
    rw [this]; exact mul_pos ht0' ht1
  · have : (0 * κv - t * c * (0 - κ)) / (L * κv - t * c * (zf - κ)) =
        t * ((c * κ) / (L * κv - t * c * (zf - κ))) := by ring
    rw [this]; exact ht2

end Type08Sp
end Minimality

#print axioms Minimality.Type08Sp.mid_exists_open
#print axioms Minimality.Type08Sp.mid_exists_origin
