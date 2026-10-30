module

public import Minimality.Type08S.P2I3
public import Minimality.Type08S.P2NP4

@[expose] public section

set_option relaxedAutoImplicit true

/-!
# I4: frame-level closing of the K_2-type slide with the F-middle `p` at the END `f` of the side `x f`
(the case `α1 = 1`, i.e. `T'`: `a` lies directly below `c'`), for the standard cycle `(x, f, r, g)` and `κv > 0`.
-/

set_option autoImplicit true
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

variable {e1 e2 e3 : ℝ³}

/-- A point over the end `f` of the side, slightly displaced toward `x` by the tilt, becomes a middle. -/
theorem mid_exists_end (O : ℝ³) {κ L zf zp κv : ℝ} (hL : 0 < L) (hκv : 0 < κv)
    (hz : 0 < κ * (zp - zf)) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
      fpt e1 e2 e3 O L 0 zp = fpt e1 e2 e3 O 0 0 κ +
        s • (fpt e1 e2 e3 O L 0 zf - fpt e1 e2 e3 O 0 0 κ) + δ • (κv • e3 + t • ((κ * κv) • e1)) := by
  set c := κ * κv with hc
  have hd0 : L * κv - 0 * c * (zf - κ) ≠ 0 := by simpa using (mul_pos hL hκv).ne'
  have hcd : ContinuousAt (fun t : ℝ => L * κv - t * c * (zf - κ)) 0 := by fun_prop
  have hS : ContinuousAt (fun t : ℝ => (L * κv - t * c * (zp - κ)) / (L * κv - t * c * (zf - κ))) 0 :=
    ContinuousAt.div (by fun_prop) hcd hd0
  have hS0 : (L * κv - 0 * c * (zp - κ)) / (L * κv - 0 * c * (zf - κ)) = 1 := by
    simp only [zero_mul, zero_sub, sub_zero]; exact div_self (mul_pos hL hκv).ne'
  have e1' : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < (L * κv - t * c * (zp - κ)) / (L * κv - t * c * (zf - κ)) :=
    hS.eventually (lt_mem_nhds (by beta_reduce; rw [hS0]; norm_num))
  have e4' : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < L * κv - t * c * (zf - κ) :=
    hcd.eventually (lt_mem_nhds (by simpa using mul_pos hL hκv))
  have hDl : ContinuousAt (fun t : ℝ => (L * (zp - κ) - L * (zf - κ)) / (L * κv - t * c * (zf - κ))) 0 :=
    ContinuousAt.div (by fun_prop) hcd hd0
  have e3' : ∀ᶠ t in 𝓝 (0 : ℝ), (L * (zp - κ) - L * (zf - κ)) / (L * κv - t * c * (zf - κ)) ≠ 0 := by
    refine hDl.eventually (isOpen_ne.mem_nhds ?_)
    simp only [zero_mul, zero_sub, sub_zero]
    refine div_ne_zero ?_ (mul_pos hL hκv).ne'
    have : L * (zp - κ) - L * (zf - κ) = L * (zp - zf) := by ring
    rw [this]
    refine mul_ne_zero hL.ne' ?_
    intro h; rw [h, mul_zero] at hz; exact lt_irrefl _ hz
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (e1'.and (e3'.and e4'))] with t ht0 ht
  obtain ⟨ht1, ht3, ht4⟩ := ht
  have ht0' : 0 < t := ht0
  obtain ⟨hs, hz'⟩ := mid_solve (Xm := L) (zm := zp) (c := c) (κ := κ) (L := L) (zf := zf) (κv := κv) (t := t) ht4.ne'
  refine ⟨_, _, ht1, ?_, ?_, mid_vec O hs hz'⟩
  · -- `s < 1`
    have : (L * κv - t * c * (zp - κ)) / (L * κv - t * c * (zf - κ)) =
        1 - t * (c * (zp - zf)) / (L * κv - t * c * (zf - κ)) := by
      field_simp; ring
    rw [this]
    have : 0 < t * (c * (zp - zf)) / (L * κv - t * c * (zf - κ)) := by
      refine div_pos (mul_pos ht0' ?_) ht4
      rw [hc]; nlinarith [mul_pos hκv hz]
    linarith
  · simpa using ht3

/-- `Qg` is counter-clockwise for `κv > 0`. -/
theorem qg_rim_ccw (hF : Fr e1 e2 e3) (O : ℝ³) {κ L zf Xr Yr zr Xg Yg zg κv : ℝ} (hκv : 0 < κv)
    (hL : 0 < L) (hYr : 0 < Yr) (hYg : 0 < Yg)
    (hcr : 0 < (Xg - Xr) * (-Yr) - (Yg - Yr) * (L - Xr)) (hcg : 0 < Yg * Xr - Xg * Yr) :
    (∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 → 0 < det3
      (Qg e1 e2 e3 O κ L zf Xr Yr zr Xg Yg zg (id (i + 1)) - Qg e1 e2 e3 O κ L zf Xr Yr zr Xg Yg zg (id i))
      (Qg e1 e2 e3 O κ L zf Xr Yr zr Xg Yg zg (id j) - Qg e1 e2 e3 O κ L zf Xr Yr zr Xg Yg zg (id i)) (κv • e3)) ∧
    (∀ (i : ZMod 4) (a : ZMod 4), 0 ≤ det3
      (Qg e1 e2 e3 O κ L zf Xr Yr zr Xg Yg zg (id (i + 1)) - Qg e1 e2 e3 O κ L zf Xr Yr zr Xg Yg zg (id i))
      (Qg e1 e2 e3 O κ L zf Xr Yr zr Xg Yg zg a - Qg e1 e2 e3 O κ L zf Xr Yr zr Xg Yg zg (id i)) (κv • e3)) := by
  constructor
  · intro i j hi hj
    rw [det3_Qg hF]
    have : inc i (i + 1) j := by revert i j; decide
    exact mul_pos hκv ((crQ_pos_iff hL hYr hYg hcr hcg _ _ _).mpr this)
  · intro i m
    rw [det3_Qg hF]
    have : ¬ inc i m (i + 1) := by revert i m; decide
    have h2 : ¬ crQ L Xr Yr Xg Yg i (i + 1) m < 0 := fun h => this ((crQ_neg_iff hL hYr hYg hcr hcg _ _ _).mp h)
    exact mul_nonneg hκv.le (not_lt.mp h2)

/-- **K_2-type closing at `T'`** (frame level): the standard screen quadrilateral `(x, f, r, g)`, `x'` at the
origin, the F-middle `p` below `f`, the G-middle `q`. -/
theorem close_end_frame (hF : Fr e1 e2 e3) (O : ℝ³)
    {κ κv L zf Xr Yr zr Xg Yg zg Xq Yq zq zp : ℝ} (hκ : κ ≠ 0) (hκv : 0 < κv)
    (hL : 0 < L) (hYr : 0 < Yr) (hYg : 0 < Yg)
    (hcr : 0 < (Xg - Xr) * (-Yr) - (Yg - Yr) * (L - Xr)) (hcg : 0 < Yg * Xr - Xg * Yr)
    (hYq : 0 < Yq) (hYlt : Yq < Yg) (hcop : Xq * Yg = Yq * Xg)
    (hchord : 0 < κ * ((0 - Yg) * (zq - zg) - (κ - zg) * (Yq - Yg)))
    (hpz : 0 < κ * (zp - zf))
    (hz : IsRobustUnimodal (fun i => ⟪Qg e1 e2 e3 O κ L zf Xr Yr zr Xg Yg zg i, κv • e3⟫))
    (hbad : NoPersistHDN (Qg e1 e2 e3 O κ L zf Xr Yr zr Xg Yg zg) (κv • e3) (L • e1)) :
    IsRupert ({O, fpt e1 e2 e3 O 0 0 κ, fpt e1 e2 e3 O L 0 zf, fpt e1 e2 e3 O Xr Yr zr,
      fpt e1 e2 e3 O Xg Yg zg, fpt e1 e2 e3 O L 0 zp, fpt e1 e2 e3 O Xq Yq zq} : Finset ℝ³) := by
  have hκv0 : κv ≠ 0 := hκv.ne'
  obtain ⟨hc1, hc2⟩ := qg_rim_ccw hF O hκv hL hYr hYg hcr hcg (κ := κ) (zf := zf) (zr := zr) (zg := zg)
  have hw := rows_T4 hF O (κ := κ) (κv := κv) (L := L) (zf := zf) (Xr := Xr) (Yr := Yr) (zr := zr)
    (Xg := Xg) (Yg := Yg) (zg := zg) (Xq := Xq) (Yq := Yq) (zq := zq) hκ hκv0 hL hYr hYg hcr hcg
    hYq hYlt hcop hchord
  have hpx : fpt e1 e2 e3 O L 0 zp ≠ fpt e1 e2 e3 O 0 0 κ := by
    intro h; have := (fpt_inj hF h).1; linarith
  have hpf : fpt e1 e2 e3 O L 0 zp ≠ fpt e1 e2 e3 O L 0 zf := by
    intro h; have := (fpt_inj hF h).2.2; rw [this, sub_self, mul_zero] at hpz; exact lt_irrefl _ hpz
  exact close_np_frame_g hF O _ hκ hκv0 hL hYr hYg hcr hcg hpx hpf (mid_exists_end O hL hκv hpz) hw
    (Qg e1 e2 e3 O κ L zf Xr Yr zr Xg Yg zg) id (fun _ => rfl) (fun _ => rfl) (by norm_num : 3 ≤ 4) id _ _ rfl rfl
    hc1 hc2 hz hbad

end Type08Sp
end Minimality

#print axioms Minimality.Type08Sp.close_end_frame
