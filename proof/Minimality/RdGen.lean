module

public import Minimality.EdgeRd

@[expose] public section

/-!
# Theorem R from a slot certificate, with points hidden at first order (§22.8, §22.10)

A.10's Theorem R (`isRupert_rd_std`, `isRupert_rd`, `isRupert_of_rdRim`) takes (H2) and (H4) and
builds the certificate of the limit system itself (`rd_limit_cert`).  Here:
* the certificate is an input (`isRupert_rdG_std`, `isRupert_rdG`, `RdRimG`), so that Lemma
  22.10's certificate (`rd_limit_cert0`: `σ_g = σ_mf`, (H4) failing) applies too;
* a point may be hidden only at first order along the tilt (`RdSlideHidden`): at a vertex view
  the other middle of the quadrilateral `F_j` lies over the chord at `u₀` and is hidden by the
  tilt along `F_k`'s circle.

* `RdSlideHidden`, `RdSlideHidden.eventually`, `RdSlideHidden.frame`.
* `rd_limit_cert0` (Lemma 22.10).
* `isRupert_rdG_std`, `isRupert_rdG`, `RdRimG`, `RdRim.toG`, `isRupert_of_rdRimG`.
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

/-- `x` is hidden at first order along the tilt `T + κ U` (`κ → 0⁺`): inside a triangle of
points of `V` at every small tilt, from tests that are strict at `T` or vanish there with a
positive derivative along `U` (either orientation `ρ`). -/
def RdSlideHidden (V : Finset ℝ³) (T U x : ℝ³) : Prop :=
  ∃ ρ : ℝ, ρ ≠ 0 ∧ ∃ a ∈ V, ∃ b ∈ V, ∃ c ∈ V, SlideTest ρ (b - a) (c - a) T U ∧
    SlideTest ρ (b - a) (x - a) T U ∧ SlideTest ρ (c - b) (x - b) T U ∧
    SlideTest ρ (a - c) (x - c) T U

theorem RdSlideHidden.eventually {V : Finset ℝ³} {T U x : ℝ³} (h : RdSlideHidden V T U x) :
    ∀ᶠ κ in 𝓝[>] (0 : ℝ), RdHidden V (T + κ • U) x := by
  obtain ⟨ρ, -, a, ha, b, hb, c, hc, h0, h1, h2, h3⟩ := h
  filter_upwards [eventually_det3_slide h0, eventually_det3_slide h1, eventually_det3_slide h2,
    eventually_det3_slide h3] with κ e0 e1 e2 e3
  exact rdHidden_of_sign ha hb hc e0 e1 e2 e3

theorem SlideTest.sub_smul {ρ : ℝ} {X Y T U : ℝ³} (h : SlideTest ρ X Y T U) (t : ℝ) :
    SlideTest ρ X Y T (U - t • T) := by
  rcases h with h | ⟨h0, h1⟩
  · exact Or.inl h
  · refine Or.inr ⟨h0, ?_⟩
    have : det3 X Y (U - t • T) = det3 X Y U - t * det3 X Y T := by
      simp only [det3_expand, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; ring
    rw [this, h0, mul_zero, sub_zero]; exact h1

theorem RdSlideHidden.sub_smul {V : Finset ℝ³} {T U x : ℝ³} (h : RdSlideHidden V T U x)
    (t : ℝ) : RdSlideHidden V T (U - t • T) x := by
  obtain ⟨ρ, hρ, a, ha, b, hb, c, hc, h0, h1, h2, h3⟩ := h
  exact ⟨ρ, hρ, a, ha, b, hb, c, hc, h0.sub_smul t, h1.sub_smul t, h2.sub_smul t, h3.sub_smul t⟩

theorem SlideTest.smul_T {ρ : ℝ} {X Y T U : ℝ³} (h : SlideTest ρ X Y T U) {r : ℝ} (hr : 0 < r) :
    SlideTest ρ X Y (r • T) U := by
  have hs : det3 X Y (r • T) = r * det3 X Y T := by
    simp only [det3_expand, PiLp.smul_apply, smul_eq_mul]; ring
  rcases h with h | ⟨h0, h1⟩
  · left; rw [hs]; nlinarith
  · exact Or.inr ⟨by rw [hs, h0, mul_zero], h1⟩

theorem RdSlideHidden.smul_T {V : Finset ℝ³} {T U x : ℝ³} (h : RdSlideHidden V T U x) {r : ℝ}
    (hr : 0 < r) : RdSlideHidden V (r • T) U x := by
  obtain ⟨ρ, hρ, a, ha, b, hb, c, hc, h0, h1, h2, h3⟩ := h
  exact ⟨ρ, hρ, a, ha, b, hb, c, hc, h0.smul_T hr, h1.smul_T hr, h2.smul_T hr, h3.smul_T hr⟩

/-- Points hidden at first order stay so in frame coordinates (either orientation). -/
theorem RdSlideHidden.frame {V : Finset ℝ³} {v S T N U x : ℝ³} (hF : IsFrame S T N)
    (h : RdSlideHidden V T U x) :
    RdSlideHidden (V.image fun y => (orthoFrameMat S T N).toEuclideanLin (y - v)) (pt 0 1 0)
      (pt ⟪U, S⟫ ⟪U, T⟫ ⟪U, N⟫) ((orthoFrameMat S T N).toEuclideanLin (x - v)) := by
  classical
  obtain ⟨ρ, hρ, a, ha, b, hb, c, hc, h0, h1, h2, h3⟩ := h
  have hsq := hF.det3_sq
  obtain ⟨-, hTT, -, hST, -, hTN⟩ := hF
  set ε := det3 S T N with hε
  have hT : pt 0 1 0 = pt ⟪T, S⟫ ⟪T, T⟫ ⟪T, N⟫ := by
    rw [real_inner_comm, hST, hTT, hTN]
  have key : ∀ W p q r : ℝ³, det3 ((orthoFrameMat S T N).toEuclideanLin (p - v) -
      (orthoFrameMat S T N).toEuclideanLin (r - v)) ((orthoFrameMat S T N).toEuclideanLin (q - v) -
      (orthoFrameMat S T N).toEuclideanLin (r - v)) (pt ⟪W, S⟫ ⟪W, T⟫ ⟪W, N⟫) =
        ε * det3 (p - r) (q - r) W := by
    intro W p q r
    rw [← map_sub, ← map_sub, show p - v - (r - v) = p - r by abel,
      show q - v - (r - v) = q - r by abel, orthoFrameMat_apply, orthoFrameMat_apply,
      det3_frameCoords]
  have tr : ∀ p q r : ℝ³, SlideTest ρ (p - r) (q - r) T U →
      SlideTest (ρ * ε) ((orthoFrameMat S T N).toEuclideanLin (p - v) -
        (orthoFrameMat S T N).toEuclideanLin (r - v))
        ((orthoFrameMat S T N).toEuclideanLin (q - v) -
        (orthoFrameMat S T N).toEuclideanLin (r - v)) (pt 0 1 0) (pt ⟪U, S⟫ ⟪U, T⟫ ⟪U, N⟫) := by
    intro p q r hs
    rw [hT]
    unfold SlideTest
    rw [key, key]
    rcases hs with hs | ⟨hs0, hs1⟩
    · left
      have : ρ * ε * (ε * det3 (p - r) (q - r) T) = (ε * ε) * (ρ * det3 (p - r) (q - r) T) := by
        ring
      rw [this, hsq, one_mul]; exact hs
    · right
      refine ⟨by rw [hs0, mul_zero], ?_⟩
      have : ρ * ε * (ε * det3 (p - r) (q - r) U) = (ε * ε) * (ρ * det3 (p - r) (q - r) U) := by
        ring
      rw [this, hsq, one_mul]; exact hs1
  have hε0 : ε ≠ 0 := by intro h0; rw [h0, mul_zero] at hsq; exact zero_ne_one hsq
  exact ⟨ρ * ε, mul_ne_zero hρ hε0, _, mem_image_of_mem _ ha, _, mem_image_of_mem _ hb, _,
    mem_image_of_mem _ hc, tr b c a h0, tr b x a h1, tr c x b h2, tr a x c h3⟩

/-- **Lemma 22.10's certificate of the limit system** (`σ_g = σ_mf`, so (H4) fails and
`D(f) > 0`): as `rd_limit_cert`, with `K = 0` in place of (H2) and `D(f) > 0` in place of (H4);
`D(v)` may have either sign (the weight `M` is taken large). -/
theorem rd_limit_cert0 {sm tm sf tf s1 t1 s2 t2 ρ s0 : ℝ}
    (hsm : 0 < sm) (hmf : sm < sf) (h12 : s1 < s2)
    (htm : 0 < tm) (ht1 : 0 < t1) (htf : tf < 0) (ht2 : t2 < 0)
    (hK0 : (tf - tm) * (s2 - s1) = (t2 - t1) * (sf - sm))
    (hDf : (t2 - t1) * (sf - s1) < (s2 - s1) * (tf - t1))
    (hρ : ρ * (t2 - t1) = s2 - s1) (hs0 : s0 = s1 - ρ * t1) :
    ∃ θ M : ℝ, 0 < θ ∧ 0 < M ∧
      0 < sm * (-s0 - θ) + M * θ * (sm - ρ * tm) ∧
      0 < sm * ((sm - s0 - ρ * tm) - θ) + M * (tm + θ) * (sm - ρ * tm) ∧
      0 < (sf - sm) * ((sm - s0 - ρ * tm) - θ) +
        M * (tm + θ) * ((sf - sm) - ρ * (tf - tm)) ∧
      0 < (sf - sm) * ((sf - s0 - ρ * tf) - θ) +
        M * (tf + θ) * ((sf - sm) - ρ * (tf - tm)) ∧
      0 < (s2 - s1) * θ ∧
      0 < -ρ * M * (0 + θ) ∧ 0 < -ρ * M * (t1 + θ) ∧
      0 < ρ * M * (tf + θ) ∧ 0 < ρ * M * (t2 + θ) := by
  have ht12 : 0 < t1 - t2 := by linarith
  have hρneg : ρ < 0 := by
    by_contra hc; push Not at hc
    linarith [mul_nonpos_of_nonneg_of_nonpos hc (by linarith : t2 - t1 ≤ 0)]
  -- `K = 0`: `(s_f − s_m) − ρ (t_f − t_m) = 0`
  have hK : (sf - sm) - ρ * (tf - tm) = 0 := by
    have : ((sf - sm) - ρ * (tf - tm)) * (t1 - t2) = 0 := by
      linear_combination (tf - tm) * hρ + hK0
    exact (mul_eq_zero.mp this).resolve_right ht12.ne'
  set DF := sf - s0 - ρ * tf with hDF
  have hDF' : 0 < DF := by
    have : DF * (t1 - t2) = (sf - s1) * (t1 - t2) + (s2 - s1) * (tf - t1) := by
      rw [hDF, hs0]; linear_combination (tf - t1) * hρ
    by_contra hc; push Not at hc
    nlinarith [mul_nonpos_of_nonpos_of_nonneg hc ht12.le]
  have hDM : sm - s0 - ρ * tm = DF := by rw [hDF]; linear_combination -hK
  have hsmρ : 0 < sm - ρ * tm := by nlinarith [mul_pos (neg_pos.mpr hρneg) htm]
  set θ := min (DF / 2) (min (-tf / 2) (-t2 / 2)) with hθdef
  have hθ : 0 < θ := lt_min (by linarith) (lt_min (by linarith) (by linarith))
  have hθF : θ < DF := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hθf : θ < -tf := lt_of_le_of_lt ((min_le_right _ _).trans (min_le_left _ _)) (by linarith)
  have hθ2 : θ < -t2 := lt_of_le_of_lt ((min_le_right _ _).trans (min_le_right _ _)) (by linarith)
  set A := |sm * (s0 + θ)| + 1 with hA
  have hA0 : 0 < A := by positivity
  have hθs : 0 < θ * (sm - ρ * tm) := mul_pos hθ hsmρ
  set M := A / (θ * (sm - ρ * tm)) with hMdef
  have hM : 0 < M := div_pos hA0 hθs
  have hMθ : M * θ * (sm - ρ * tm) = A := by
    rw [hMdef, mul_assoc]; exact div_mul_cancel₀ _ hθs.ne'
  refine ⟨θ, M, hθ, hM, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := le_abs_self (sm * (s0 + θ))
    nlinarith
  · rw [hDM]
    exact add_pos (mul_pos hsm (by linarith)) (mul_pos (mul_pos hM (by linarith)) hsmρ)
  · rw [hDM, hK, mul_zero, add_zero]; exact mul_pos (by linarith) (by linarith)
  · rw [hK, mul_zero, add_zero]; exact mul_pos (by linarith) (by linarith)
  · exact mul_pos (by linarith) hθ
  · have := mul_pos (mul_pos (neg_pos.mpr hρneg) hM) hθ; linarith
  · exact mul_pos (mul_pos (neg_pos.mpr hρneg) hM) (by linarith)
  · exact mul_pos_of_neg_of_neg (mul_neg_of_neg_of_pos hρneg hM) (by linarith)
  · exact mul_pos_of_neg_of_neg (mul_neg_of_neg_of_pos hρneg hM) (by linarith)

set_option maxHeartbeats 1000000 in
/-- **Theorem R of A.10 from a certificate, in coordinates** (as `isRupert_rd_std`, with the
slot weights of the limit system given (`W1`–`W9`, for `rd_limit_cert` or `rd_limit_cert0`) and
with points hidden at first order along the tilt allowed (`RdSlideHidden`)).  As before:  The five-corner rim
`v m f g_f g_v` with `v = 0`, `m = (s_m, t_m, 0)`, `f = (s_f, t_f, 0)`,
`g_f = (s₂, t₂, −h)`, `g_v = (s₁, t₁, −h)` (depth `t`, the face `F_j` in `ν = 0`, the far
edge `g` parallel to it) at the view `u₀ = (0, 1, 0)` along the axle, with (H1)
`t_m, t₁ > 0 > t_f, t₂`, (H2) `σ_mf < σ_g` and (H4) `D(v) > 0 > D(f)` (in the
division-free forms below; `s_m < s_f` since `m` is a middle of `F_j`, `s₁ < s₂` since the
rim of `K_v` is `v f g_f g_v`).  The middles `M` of `F_k` lie in the plane of `F_k`
(through the axle and `g_v`): `x = p g_v + q u₀` with `q ≠ 0` and `0 < p < 1`, or `p = 0`
and `q < 0` (the other end `w` of the axle).  Every other point is strictly hidden at
`u₀`.  Then the point set is Rupert: at the views `u₀ + κ (s₁, 0, −h)` of `F_k`'s circle,
for small `κ > 0`, the motion built from Lemma R2's certificate is strictly inward at all
ten slots of the rim, and `F_k`'s middles lie over its side `[g_v, v]`
(`isRupert_of_chords`). -/
theorem isRupert_rdG_std (V M : Finset ℝ³) {sm tm sf tf s1 t1 s2 t2 h ρ θ M' : ℝ}
    (hv : pt 0 0 0 ∈ V) (hm : pt sm tm 0 ∈ V) (hf : pt sf tf 0 ∈ V)
    (hgf : pt s2 t2 (-h) ∈ V) (hgv : pt s1 t1 (-h) ∈ V)
    (hh : 0 < h) (hsm : 0 < sm) (hmf : sm < sf) (h12 : s1 < s2)
    (htm : 0 < tm) (ht1 : 0 < t1) (htf : tf < 0) (ht2 : t2 < 0)
    (hρ : ρ * (t2 - t1) = s2 - s1) (hθ : 0 < θ) (hM' : 0 < M')
    (W1 : 0 < sm * (-(s1 - ρ * t1) - θ) + M' * θ * (sm - ρ * tm))
    (W2 : 0 < sm * ((sm - (s1 - ρ * t1) - ρ * tm) - θ) + M' * (tm + θ) * (sm - ρ * tm))
    (W3 : 0 < (sf - sm) * ((sm - (s1 - ρ * t1) - ρ * tm) - θ) +
        M' * (tm + θ) * ((sf - sm) - ρ * (tf - tm)))
    (W4 : 0 < (sf - sm) * ((sf - (s1 - ρ * t1) - ρ * tf) - θ) +
        M' * (tf + θ) * ((sf - sm) - ρ * (tf - tm)))
    (W5 : 0 < (s2 - s1) * θ)
    (W6 : 0 < -ρ * M' * (0 + θ)) (W7 : 0 < -ρ * M' * (t1 + θ))
    (W8 : 0 < ρ * M' * (tf + θ)) (W9 : 0 < ρ * M' * (t2 + θ))
    (hM : ∀ x ∈ M, ∃ p q : ℝ, x = pt (p * s1) (p * t1 + q) (-(p * h)) ∧ q ≠ 0 ∧
      ((0 < p ∧ p < 1) ∨ (p = 0 ∧ q < 0)))
    (hrest : ∀ x ∈ V, x ∉ M → x = pt 0 0 0 ∨ x = pt sm tm 0 ∨ x = pt sf tf 0 ∨
      x = pt s2 t2 (-h) ∨ x = pt s1 t1 (-h) ∨ RdHidden V (pt 0 1 0) x ∨
      RdSlideHidden V (pt 0 1 0) (pt s1 t1 (-h)) x) :
    IsRupert V := by
  classical
  have ht12 : 0 < t1 - t2 := by linarith
  -- the view, the motion, the rim
  set u₀ : ℝ³ := pt 0 1 0 with hu₀
  set u₁ : ℝ³ := pt s1 0 (-h) with hu₁
  set ω₀ : ℝ³ := pt 0 0 (ρ * M') with hω₀
  set ω₁ : ℝ³ := pt (h * (ρ - M')) (h * (1 + ρ * M')) 0 with hω₁
  set τ₀ : ℝ³ := pt (-(ρ * M' * θ)) 0 0 with hτ₀
  set τ₁ : ℝ³ := pt 0 0 (h * ((s1 - ρ * t1) + θ - M' * θ)) with hτ₁
  set v : ℝ³ := pt 0 0 0 with hv_def
  set m : ℝ³ := pt sm tm 0 with hm_def
  set f : ℝ³ := pt sf tf 0 with hf_def
  set gf : ℝ³ := pt s2 t2 (-h) with hgf_def
  set gv : ℝ³ := pt s1 t1 (-h) with hgv_def
  -- the ten slots
  have sT1v := eventually_slot (m - v) v ω₀ ω₁ τ₀ τ₁ u₀ u₁ (Or.inr ⟨by rd_unfold; ring,
    (mul_pos hh W1).trans_eq (by rd_unfold; ring)⟩)
  have sT1m := eventually_slot (m - v) m ω₀ ω₁ τ₀ τ₁ u₀ u₁ (Or.inr ⟨by rd_unfold; ring,
    (mul_pos hh W2).trans_eq (by rd_unfold; ring)⟩)
  have sT2m := eventually_slot (f - m) m ω₀ ω₁ τ₀ τ₁ u₀ u₁ (Or.inr ⟨by rd_unfold; ring,
    (mul_pos hh W3).trans_eq (by rd_unfold; ring)⟩)
  have sT2f := eventually_slot (f - m) f ω₀ ω₁ τ₀ τ₁ u₀ u₁ (Or.inr ⟨by rd_unfold; ring,
    (mul_pos hh W4).trans_eq (by rd_unfold; ring)⟩)
  have sBgf := eventually_slot (gv - gf) gf ω₀ ω₁ τ₀ τ₁ u₀ u₁ (Or.inr ⟨by rd_unfold; ring,
    (mul_pos hh W5).trans_eq (by
      rd_unfold; linear_combination (-(h * ((s2 - s1) + M' * (t2 + θ)))) * hρ)⟩)
  have sBgv := eventually_slot (gv - gf) gv ω₀ ω₁ τ₀ τ₁ u₀ u₁ (Or.inr ⟨by rd_unfold; ring,
    (mul_pos hh W5).trans_eq (by rd_unfold; linear_combination (-(h * M' * (t1 + θ))) * hρ)⟩)
  have sLv := eventually_slot (v - gv) v ω₀ ω₁ τ₀ τ₁ u₀ u₁ (Or.inl
    ((mul_pos hh W6).trans_eq (by rd_unfold; ring)))
  have sLgv := eventually_slot (v - gv) gv ω₀ ω₁ τ₀ τ₁ u₀ u₁ (Or.inl
    ((mul_pos hh W7).trans_eq (by rd_unfold; ring)))
  have sRf := eventually_slot (gf - f) f ω₀ ω₁ τ₀ τ₁ u₀ u₁ (Or.inl
    ((mul_pos hh W8).trans_eq (by rd_unfold; ring)))
  have sRgf := eventually_slot (gf - f) gf ω₀ ω₁ τ₀ τ₁ u₀ u₁ (Or.inl
    ((mul_pos hh W9).trans_eq (by rd_unfold; ring)))
  -- convexity of the rim along the tilt (at `m` only to first order)
  have cv := eventually_det3_pos u₁ (show 0 < det3 (m - v) (gv - v) u₀ from
    (mul_pos hh hsm).trans_eq (by rd_unfold; ring))
  have cm := TiltSign.eventually (a := f - m) (b := v - m) (u₀ := u₀) (v := u₁) (Or.inr ⟨by
    rd_unfold; ring, (mul_pos hh (add_pos (mul_pos (by linarith : (0:ℝ) < sf) htm)
      (mul_pos hsm (by linarith : (0:ℝ) < -tf)))).trans_eq (by rd_unfold; ring)⟩)
  have cf := eventually_det3_pos u₁ (show 0 < det3 (gf - f) (m - f) u₀ from
    (mul_pos hh (by linarith : (0:ℝ) < sf - sm)).trans_eq (by rd_unfold; ring))
  have cgf := eventually_det3_pos u₁ (show 0 < det3 (gv - gf) (f - gf) u₀ from
    (mul_pos hh (by linarith : (0:ℝ) < s2 - s1)).trans_eq (by rd_unfold; ring))
  have cgv := eventually_det3_pos u₁ (show 0 < det3 (v - gv) (gf - gv) u₀ from
    (mul_pos hh (by linarith : (0:ℝ) < s2 - s1)).trans_eq (by rd_unfold; ring))
  have cr := eventually_det3_pos u₁ (show 0 < det3 (v - gv) (m - gv) u₀ from
    (mul_pos hh hsm).trans_eq (by rd_unfold; ring))
  -- the rim corners
  set ω := fun κ : ℝ => ω₀ + κ • ω₁
  set τ := fun κ : ℝ => τ₀ + κ • τ₁
  set u := fun κ : ℝ => u₀ + κ • u₁
  have hrim : ∀ x ∈ V, x ∉ M → ∀ᶠ κ in 𝓝[>] (0 : ℝ), TiltCert V (u κ) (ω κ) (τ κ) x := by
    intro x hx hxM
    rcases hrest x hx hxM with rfl | rfl | rfl | rfl | rfl | hid | hsl
    · filter_upwards [cv, sT1v, sLv] with κ e0 e1 e2
      exact Or.inl ⟨gv, hgv, m, hm, e0, e1, e2⟩
    · filter_upwards [cm, sT2m, sT1m] with κ e0 e1 e2
      exact Or.inl ⟨v, hv, f, hf, e0, e1, e2⟩
    · filter_upwards [cf, sRf, sT2f] with κ e0 e1 e2
      exact Or.inl ⟨m, hm, gf, hgf, e0, e1, e2⟩
    · filter_upwards [cgf, sBgf, sRgf] with κ e0 e1 e2
      exact Or.inl ⟨f, hf, gv, hgv, e0, e1, e2⟩
    · filter_upwards [cgv, sLgv, sBgv] with κ e0 e1 e2
      exact Or.inl ⟨gf, hgf, v, hv, e0, e1, e2⟩
    · filter_upwards [hid.eventually_tilt u₁] with κ hk
      exact Or.inr hk
    · have e1 : pt s1 t1 (-h) - t1 • pt 0 1 0 = u₁ := by
        rw [hu₁]; ext i; fin_cases i <;> simp [pt]
      have := (hsl.sub_smul t1).eventually
      rw [e1] at this
      filter_upwards [this] with κ hk
      exact Or.inr hk
  -- the middles of `F_k` over its side `[g_v, v]`
  have hmid : ∀ x ∈ M, ∀ᶠ κ in 𝓝[>] (0 : ℝ), ChordMiddle V (u κ) (ω κ) (τ κ) x := by
    intro x hx
    obtain ⟨p, q, rfl, hq, hp⟩ := hM x hx
    have hp1 : p < 1 := by rcases hp with ⟨-, h1⟩ | ⟨rfl, -⟩ <;> linarith
    have hc : ContinuousAt (fun κ : ℝ => κ * (q / (1 - κ * t1))) 0 :=
      continuousAt_id.mul (continuousAt_const.div
        (continuousAt_const.sub (continuousAt_id.mul continuousAt_const)) (by simp))
    have hlo : ∀ᶠ κ in 𝓝[>] (0 : ℝ), p - 1 < κ * (q / (1 - κ * t1)) :=
      (continuousAt_const.eventually_lt hc (by simp; linarith)).filter_mono nhdsWithin_le_nhds
    have hden := eventually_pos_affine (A := 1) (B := -t1) (Or.inl one_pos)
    have hhi : ∀ᶠ κ in 𝓝[>] (0 : ℝ), κ * (q / (1 - κ * t1)) < p := by
      rcases hp with ⟨hp0, -⟩ | ⟨rfl, hq0⟩
      · exact (hc.eventually_lt continuousAt_const (by simp; linarith)).filter_mono
          nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin, hden] with κ hκ hd
        have hκ' : (0 : ℝ) < κ := hκ
        exact mul_neg_of_pos_of_neg hκ' (div_neg_of_neg_of_pos hq0 (by linarith))
    filter_upwards [hlo, hhi, hden, sLgv, sLv, cr] with κ e1 e2 hd l1 l2 r
    have hd' : 1 - κ * t1 ≠ 0 := by linarith
    refine ⟨gv, hgv, v, hv, m, hm, 1 - p + κ * (q / (1 - κ * t1)), q / (1 - κ * t1),
      by linarith, by linarith, div_ne_zero hq hd', ?_, r, l1, l2⟩
    have hδ : q / (1 - κ * t1) * (1 - κ * t1) = q := div_mul_cancel₀ _ hd'
    ext i; fin_cases i <;>
      simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, u, PiLp.add_apply, PiLp.sub_apply,
        PiLp.smul_apply, smul_eq_mul, pt_zero, pt_one, pt_two, hu₀, hu₁, hgv_def, hv_def]
    · ring
    · linear_combination -hδ
    · ring
  have hne : ∀ κ : ℝ, u κ ≠ 0 := by
    intro κ h0
    have := congrArg (fun y : ℝ³ => y 1) h0
    simp [u, hu₀, hu₁] at this
  have hall : ∀ᶠ κ in 𝓝[>] (0 : ℝ), (∀ x ∈ V, x ∉ M → TiltCert V (u κ) (ω κ) (τ κ) x) ∧
      ∀ x ∈ M, ChordMiddle V (u κ) (ω κ) (τ κ) x := by
    refine ((eventually_all_finset V).mpr fun x hx => ?_).and ((eventually_all_finset M).mpr hmid)
    by_cases hxM : x ∈ M
    · exact Eventually.of_forall fun _ h => absurd hxM h
    · filter_upwards [hrim x hx hxM] with κ hk _ using hk
  obtain ⟨κ, hK, hMk⟩ := hall.exists
  exact isRupert_of_chords V M (u κ) (ω κ) (τ κ) (hne κ) hK hMk

/-- **Theorem R from a certificate, frame-free** (as `isRupert_rd`, with the certificate `W1`–`W9`
and points hidden at first order along the tilt toward `g_v` allowed). -/
theorem isRupert_rdG (V M : Finset ℝ³) {v m f gf gv S T N : ℝ³}
    {sm tm sf tf s1 t1 s2 t2 h ρ θ M' : ℝ} (hF : IsFrame S T N)
    (hv : v ∈ V) (hm : m ∈ V) (hf : f ∈ V) (hgf : gf ∈ V) (hgv : gv ∈ V)
    (cm : ⟪m - v, S⟫ = sm ∧ ⟪m - v, T⟫ = tm ∧ ⟪m - v, N⟫ = 0)
    (cf : ⟪f - v, S⟫ = sf ∧ ⟪f - v, T⟫ = tf ∧ ⟪f - v, N⟫ = 0)
    (cgf : ⟪gf - v, S⟫ = s2 ∧ ⟪gf - v, T⟫ = t2 ∧ ⟪gf - v, N⟫ = -h)
    (cgv : ⟪gv - v, S⟫ = s1 ∧ ⟪gv - v, T⟫ = t1 ∧ ⟪gv - v, N⟫ = -h)
    (hh : 0 < h) (hsm : 0 < sm) (hmf : sm < sf) (h12 : s1 < s2)
    (htm : 0 < tm) (ht1 : 0 < t1) (htf : tf < 0) (ht2 : t2 < 0)
    (hρ : ρ * (t2 - t1) = s2 - s1) (hθ : 0 < θ) (hM' : 0 < M')
    (W1 : 0 < sm * (-(s1 - ρ * t1) - θ) + M' * θ * (sm - ρ * tm))
    (W2 : 0 < sm * ((sm - (s1 - ρ * t1) - ρ * tm) - θ) + M' * (tm + θ) * (sm - ρ * tm))
    (W3 : 0 < (sf - sm) * ((sm - (s1 - ρ * t1) - ρ * tm) - θ) +
        M' * (tm + θ) * ((sf - sm) - ρ * (tf - tm)))
    (W4 : 0 < (sf - sm) * ((sf - (s1 - ρ * t1) - ρ * tf) - θ) +
        M' * (tf + θ) * ((sf - sm) - ρ * (tf - tm)))
    (W5 : 0 < (s2 - s1) * θ)
    (W6 : 0 < -ρ * M' * (0 + θ)) (W7 : 0 < -ρ * M' * (t1 + θ))
    (W8 : 0 < ρ * M' * (tf + θ)) (W9 : 0 < ρ * M' * (t2 + θ))
    (hM : ∀ x ∈ M, ∃ p q : ℝ, x = v + p • (gv - v) + q • T ∧ q ≠ 0 ∧
      ((0 < p ∧ p < 1) ∨ (p = 0 ∧ q < 0)))
    (hrest : ∀ x ∈ V, x ∉ M → x = v ∨ x = m ∨ x = f ∨ x = gf ∨ x = gv ∨ RdHidden V T x ∨
      RdSlideHidden V T (gv - v) x) :
    IsRupert V := by
  classical
  set Φ : ℝ³ → ℝ³ := fun x => (orthoFrameMat S T N).toEuclideanLin (x - v) with hΦ
  have hΦx : ∀ x, Φ x = pt ⟪x - v, S⟫ ⟪x - v, T⟫ ⟪x - v, N⟫ := fun x => orthoFrameMat_apply _ _ _ _
  have hF' := hF
  refine isRupert_of_frame_image V (v := v) hF ?_
  obtain ⟨hSS, hTT, hNN, hST, hSN, hTN⟩ := hF
  have mem : ∀ x ∈ V, Φ x ∈ V.image Φ := fun x hx => mem_image_of_mem _ hx
  have Φv : Φ v = pt 0 0 0 := by rw [hΦx]; simp
  have Φm : Φ m = pt sm tm 0 := by rw [hΦx, cm.1, cm.2.1, cm.2.2]
  have Φf : Φ f = pt sf tf 0 := by rw [hΦx, cf.1, cf.2.1, cf.2.2]
  have Φgf : Φ gf = pt s2 t2 (-h) := by rw [hΦx, cgf.1, cgf.2.1, cgf.2.2]
  have Φgv : Φ gv = pt s1 t1 (-h) := by rw [hΦx, cgv.1, cgv.2.1, cgv.2.2]
  refine isRupert_rdG_std (V.image Φ) (M.image Φ) (Φv ▸ mem v hv) (Φm ▸ mem m hm)
    (Φf ▸ mem f hf) (Φgf ▸ mem gf hgf) (Φgv ▸ mem gv hgv) hh hsm hmf h12 htm ht1 htf ht2 hρ hθ
    hM' W1 W2 W3 W4 W5 W6 W7 W8 W9 ?_ ?_
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hy
    obtain ⟨p, q, rfl, hq, hp⟩ := hM x hx
    refine ⟨p, q, ?_, hq, hp⟩
    rw [hΦx, show v + p • (gv - v) + q • T - v = p • (gv - v) + q • T by abel]
    have hTS : ⟪T, S⟫ = 0 := by rw [real_inner_comm]; exact hST
    simp only [inner_add_left, inner_smul_left, conj_trivial, cgv.1, cgv.2.1, cgv.2.2, hTS, hTT,
      hTN]
    congr 1 <;> ring
  · intro y hy hyM
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hy
    have hxM : x ∉ M := fun h => hyM (mem_image_of_mem _ h)
    rcases hrest x hx hxM with rfl | rfl | rfl | rfl | rfl | hid | hsl
    · exact Or.inl Φv
    · exact Or.inr (Or.inl Φm)
    · exact Or.inr (Or.inr (Or.inl Φf))
    · exact Or.inr (Or.inr (Or.inr (Or.inl Φgf)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl Φgv))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        (hid.frame ⟨hSS, hTT, hNN, hST, hSN, hTN⟩))))))
    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_)))))
      have := hsl.frame (v := v) hF'
      rwa [cgv.1, cgv.2.1, cgv.2.2] at this

/-- **The `R_d` conditions with a certificate** for the five-corner rim `v m f g_f g_v` at the
view along `e`: the frame and coordinates of `RdRim`, (H1), and slot weights `W1`–`W9` of the
limit system (from (H2) and (H4), `RdRim.toG`, or from Lemma 22.10). -/
def RdRimG (v m f gf gv e : ℝ³) : Prop :=
  ∃ (S N : ℝ³) (sm tm sf tf s1 t1 s2 t2 h ρ θ M' : ℝ), IsFrame S (‖e‖⁻¹ • e) N ∧
    (⟪m - v, S⟫ = sm ∧ ⟪m - v, ‖e‖⁻¹ • e⟫ = tm ∧ ⟪m - v, N⟫ = 0) ∧
    (⟪f - v, S⟫ = sf ∧ ⟪f - v, ‖e‖⁻¹ • e⟫ = tf ∧ ⟪f - v, N⟫ = 0) ∧
    (⟪gf - v, S⟫ = s2 ∧ ⟪gf - v, ‖e‖⁻¹ • e⟫ = t2 ∧ ⟪gf - v, N⟫ = -h) ∧
    (⟪gv - v, S⟫ = s1 ∧ ⟪gv - v, ‖e‖⁻¹ • e⟫ = t1 ∧ ⟪gv - v, N⟫ = -h) ∧
    0 < h ∧ 0 < sm ∧ sm < sf ∧ s1 < s2 ∧ 0 < tm ∧ 0 < t1 ∧ tf < 0 ∧ t2 < 0 ∧
    ρ * (t2 - t1) = s2 - s1 ∧ 0 < θ ∧ 0 < M' ∧
    0 < sm * (-(s1 - ρ * t1) - θ) + M' * θ * (sm - ρ * tm) ∧
    0 < sm * ((sm - (s1 - ρ * t1) - ρ * tm) - θ) + M' * (tm + θ) * (sm - ρ * tm) ∧
    0 < (sf - sm) * ((sm - (s1 - ρ * t1) - ρ * tm) - θ) +
        M' * (tm + θ) * ((sf - sm) - ρ * (tf - tm)) ∧
    0 < (sf - sm) * ((sf - (s1 - ρ * t1) - ρ * tf) - θ) +
        M' * (tf + θ) * ((sf - sm) - ρ * (tf - tm)) ∧
    0 < (s2 - s1) * θ ∧
    0 < -ρ * M' * (0 + θ) ∧ 0 < -ρ * M' * (t1 + θ) ∧
    0 < ρ * M' * (tf + θ) ∧ 0 < ρ * M' * (t2 + θ)

/-- (H2) and (H4) give a certificate (`rd_limit_cert`). -/
theorem RdRim.toG {v m f gf gv e : ℝ³} (h : RdRim v m f gf gv e) : RdRimG v m f gf gv e := by
  obtain ⟨S, N, sm, tm, sf, tf, s1, t1, s2, t2, h, hF, cm, cf, cgf, cgv, hh, hsm, hmf, h12, htm,
    ht1, htf, ht2, hH2, hDv, hDf⟩ := h
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ * (t2 - t1) = s2 - s1 :=
    ⟨(s2 - s1) / (t2 - t1), div_mul_cancel₀ _ (by linarith)⟩
  obtain ⟨θ, M', hθ, hM', W1, W2, W3, W4, W5, W6, W7, W8, W9⟩ :=
    rd_limit_cert (s0 := s1 - ρ * t1) hsm hmf h12 htm ht1 htf ht2 hH2 hDv hDf hρ rfl
  exact ⟨S, N, sm, tm, sf, tf, s1, t1, s2, t2, h, ρ, θ, M', hF, cm, cf, cgf, cgv, hh, hsm, hmf,
    h12, htm, ht1, htf, ht2, hρ, hθ, hM', W1, W2, W3, W4, W5, W6, W7, W8, W9⟩

/-- **Theorem R along a view `e` from a certificate** (`RdRimG`), with `F_k`'s middles at
`v + p (g_v − v) + q e` and every other point strictly hidden at `e`, or hidden at first order
along the tilt toward `g_v` (`RdSlideHidden`). -/
theorem isRupert_of_rdRimG (V M : Finset ℝ³) {v m f gf gv e : ℝ³} (hR : RdRimG v m f gf gv e)
    (he : e ≠ 0) (hv : v ∈ V) (hm : m ∈ V) (hf : f ∈ V) (hgf : gf ∈ V) (hgv : gv ∈ V)
    (hM : ∀ x ∈ M, ∃ p q : ℝ, x = v + p • (gv - v) + q • e ∧ q ≠ 0 ∧
      ((0 < p ∧ p < 1) ∨ (p = 0 ∧ q < 0)))
    (hrest : ∀ x ∈ V, x ∉ M → x = v ∨ x = m ∨ x = f ∨ x = gf ∨ x = gv ∨ RdHidden V e x ∨
      RdSlideHidden V e (gv - v) x) :
    IsRupert V := by
  obtain ⟨S, N, sm, tm, sf, tf, s1, t1, s2, t2, h, ρ, θ, M', hF, cm, cf, cgf, cgv, hh, hsm, hmf,
    h12, htm, ht1, htf, ht2, hρ, hθ, hM', W1, W2, W3, W4, W5, W6, W7, W8, W9⟩ := hR
  have hn : 0 < ‖e‖ := norm_pos_iff.mpr he
  have heT : e = ‖e‖ • (‖e‖⁻¹ • e) := by rw [smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
  refine isRupert_rdG V M hF hv hm hf hgf hgv cm cf cgf cgv hh hsm hmf h12 htm ht1 htf ht2 hρ hθ
    hM' W1 W2 W3 W4 W5 W6 W7 W8 W9 ?_ ?_
  · intro x hx
    obtain ⟨p, q, hx, hq, hp⟩ := hM x hx
    refine ⟨p, q * ‖e‖, ?_, mul_ne_zero hq hn.ne', ?_⟩
    · rw [hx, mul_smul, ← heT]
    · rcases hp with hp | ⟨hp, hq'⟩
      · exact Or.inl hp
      · exact Or.inr ⟨hp, mul_neg_of_neg_of_pos hq' hn⟩
  · intro x hx hxM
    rcases hrest x hx hxM with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h.smul (inv_pos.mpr hn)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h.smul_T (inv_pos.mpr hn)))))))

set_option maxHeartbeats 1000000 in
/-- **Lemma 22.10's conditions** (the projection of `g` parallel to `[m, f]`: `m, f, g_f, g_v`
coplanar, so (H4) fails and `D(f) > 0`).  As `rdRim_of_H` with the coplanarity in place of
Lemma E; the certificate is `rd_limit_cert0`.  Statement of `rdRim_of_H` follows.  `m = v + s (f − v) + δ (v − w)`
(`0 < s < 1`, `δ > 0`: the middle of `F_j` above the chord, in the orientation `v − w` with
the kept apex `v` on top), `g_v` off `F_j`'s plane, the rim `v f g_f g_v` oriented, the far edge
`g ∥ F_j`, Lemma E strict (`v`, `w` on opposite sides of the plane `f g_f g_v`), (H1) along
`v − w`, and the foot of the double normal on the open chord `(v, f)`.  Then `RdRim`. -/
theorem rdRimG0_of_H {v m f gf gv w : ℝ³} {s δ : ℝ}
    (hm : m = v + s • (f - v) + δ • (v - w)) (hs0 : 0 < s) (hs1 : s < 1) (hδ : 0 < δ)
    (hoff : det3 (v - w) (f - v) (gv - v) ≠ 0)
    (horient : 0 < det3 (f - v) (gf - v) (v - w) * det3 (gv - gf) (v - gf) (v - w))
    (hpar : det3 (v - w) (f - v) (gf - gv) = 0)
    (hcopl : det3 (f - m) (gf - m) (gv - m) = 0)
    (hH1 : 0 < ⟪m - v, v - w⟫ ∧ 0 < ⟪gv - v, v - w⟫ ∧ ⟪f - v, v - w⟫ < 0 ∧
      ⟪gf - v, v - w⟫ < 0)
    (hfeet : ∃ lam mu : ℝ, 0 < lam ∧ lam < 1 ∧
      ⟪v + lam • (f - v) - (gv + mu • (gf - gv)), v - w⟫ = 0 ∧
      ⟪v + lam • (f - v) - (gv + mu • (gf - gv)), f - v⟫ = 0) :
    RdRimG v m f gf gv (v - w) := by
  obtain ⟨lam, mu, hl0, hl1, hD1, hD2⟩ := hfeet
  obtain ⟨u, rfl⟩ : ∃ u, w = v - u := ⟨v - w, by abel⟩
  simp only [sub_sub_cancel] at *
  have hu : u ≠ 0 := by rintro rfl; apply hoff; simp [det3_expand]
  have huu : 0 < ⟪u, u⟫ := real_inner_self_pos.mpr hu
  obtain ⟨S, N, hF, hfS, huS, r, hr, hNX, hgvN⟩ := exists_rdFrame hoff
  have hL : 0 < ‖u‖ := norm_pos_iff.mpr hu
  set L := ‖u‖ with hL_def
  set T := L⁻¹ • u with hT_def
  have hTX : ∀ X, ⟪X, T⟫ = L⁻¹ * ⟪X, u⟫ := fun X => real_inner_smul_right _ _ _
  have huL : ⟪u, u⟫ = L * L := by rw [real_inner_self_eq_norm_sq]; ring
  have hLT : L • T = u := by rw [hT_def, smul_smul, mul_inv_cancel₀ hL.ne', one_smul]
  have hdetu : ∀ X Y, det3 X Y u = L * det3 X Y T := by
    intro X Y; conv_lhs => rw [← hLT]
    simp only [det3_expand, PiLp.smul_apply, smul_eq_mul]; ring
  set ε := det3 S T N with hε
  have hεε : ε * ε = 1 := hF.det3_sq
  have hmv : m - v = s • (f - v) + δ • u := by rw [hm]; abel
  have νf : ⟪f - v, N⟫ = 0 := by rw [hNX]; simp only [det3_expand]; ring
  have νu : ⟪u, N⟫ = 0 := by rw [hNX]; simp only [det3_expand]; ring
  have νm : ⟪m - v, N⟫ = 0 := by
    rw [hmv, inner_add_left, real_inner_smul_left, real_inner_smul_left, νf, νu]; ring
  have νg : ⟪gf - v, N⟫ = ⟪gv - v, N⟫ := by
    have : det3 u (f - v) (gf - v) - det3 u (f - v) (gv - v) = det3 u (f - v) (gf - gv) := by
      simp only [det3_expand, PiLp.sub_apply]; ring
    rw [hNX, hNX, ← sub_eq_zero, ← mul_sub, this, hpar, mul_zero]
  have hTS : ⟪T, S⟫ = 0 := by rw [real_inner_comm]; exact hF.2.2.2.1
  have hTT : ⟪T, T⟫ = 1 := hF.2.1
  have hTN : ⟪T, N⟫ = 0 := hF.2.2.2.2.2
  have uS : ⟪u, S⟫ = 0 := huS
  have uT : ⟪u, T⟫ = L := by rw [hTX, huL]; field_simp
  have smv : ⟪m - v, S⟫ = s * ⟪f - v, S⟫ := by
    rw [hmv, inner_add_left, real_inner_smul_left, real_inner_smul_left, uS]; ring
  -- (H1)
  have hLi : 0 < L⁻¹ := inv_pos.mpr hL
  obtain ⟨h1m, h1gv, h1f, h1gf⟩ := hH1
  have htm : 0 < ⟪m - v, T⟫ := by rw [hTX]; exact mul_pos hLi h1m
  have ht1 : 0 < ⟪gv - v, T⟫ := by rw [hTX]; exact mul_pos hLi h1gv
  have htf : ⟪f - v, T⟫ < 0 := by rw [hTX]; exact mul_neg_of_pos_of_neg hLi h1f
  have ht2 : ⟪gf - v, T⟫ < 0 := by rw [hTX]; exact mul_neg_of_pos_of_neg hLi h1gf
  -- the orientation of the rim: `s₁ < s₂`
  have h12 : ⟪gv - v, S⟫ < ⟪gf - v, S⟫ := by
    rw [det3_cyc v gf gv u, hdetu, hdetu, hF.det3_T, hF.det3_T, νf, νg] at horient
    have e : L * (ε * (0 * ⟪gf - v, S⟫ - ⟪f - v, S⟫ * ⟪gv - v, N⟫)) *
        (L * (ε * (⟪gv - v, N⟫ * ⟪gv - v, S⟫ - ⟪gf - v, S⟫ * ⟪gv - v, N⟫))) =
        (L * L) * (ε * ε) * (⟪f - v, S⟫ * (⟪gv - v, N⟫ * ⟪gv - v, N⟫)) *
          (⟪gf - v, S⟫ - ⟪gv - v, S⟫) := by ring
    rw [e, hεε, mul_one] at horient
    have hpos : 0 < L * L * (⟪f - v, S⟫ * (⟪gv - v, N⟫ * ⟪gv - v, N⟫)) :=
      mul_pos (mul_pos hL hL) (mul_pos hfS (mul_pos_of_neg_of_neg hgvN hgvN))
    have := pos_of_mul_pos_right horient hpos.le
    linarith
  -- `K = 0` from the coplanarity of `m, f, g_f, g_v`
  have hK0 : (⟪f - v, T⟫ - ⟪m - v, T⟫) * (⟪gf - v, S⟫ - ⟪gv - v, S⟫) =
      (⟪gf - v, T⟫ - ⟪gv - v, T⟫) * (⟪f - v, S⟫ - ⟪m - v, S⟫) := by
    have co : ∀ (P : ℝ³) (Y : ℝ³), ⟪P - m, Y⟫ = ⟪P - v, Y⟫ - ⟪m - v, Y⟫ := by
      intro P Y; rw [← inner_sub_left]; congr 1; abel
    have hpt : ∀ a b c a' b' c' a'' b'' c'' : ℝ, det3 (pt a b c) (pt a' b' c') (pt a'' b'' c'') =
        (b * c' - c * b') * a'' + (c * a' - a * c') * b'' + (a * b' - b * a') * c'' := by
      intro a b c a' b' c' a'' b'' c''; simp only [det3_expand, pt_zero, pt_one, pt_two]
    have hC := hcopl
    rw [hF.det3_eq, ← hε, co f S, co f T, co f N, co gf S, co gf T, co gf N, co gv S, co gv T,
      co gv N, νf, νm, νg, hpt] at hC
    have hn0 : ⟪gv - v, N⟫ ≠ 0 := hgvN.ne
    have hε0 : ε ≠ 0 := by intro h0; rw [h0, mul_zero] at hεε; exact zero_ne_one hεε
    have : ε * (⟪gv - v, N⟫ * ((⟪f - v, T⟫ - ⟪m - v, T⟫) * (⟪gf - v, S⟫ - ⟪gv - v, S⟫) -
        (⟪gf - v, T⟫ - ⟪gv - v, T⟫) * (⟪f - v, S⟫ - ⟪m - v, S⟫))) = 0 := by
      linear_combination -hC
    have h2 := (mul_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hε0)).resolve_left hn0
    linarith
  -- the foot of the double normal
  have hDv : v + lam • (f - v) - (gv + mu • (gf - gv)) =
      lam • (f - v) - (gv - v) - mu • ((gf - v) - (gv - v)) := by module
  have hct : lam * ⟪f - v, T⟫ = ⟪gv - v, T⟫ + mu * (⟪gf - v, T⟫ - ⟪gv - v, T⟫) := by
    have := inner_foot hDv T
    rw [hTX, hD1, mul_zero] at this
    linarith
  have hcs : lam * ⟪f - v, S⟫ = ⟪gv - v, S⟫ + mu * (⟪gf - v, S⟫ - ⟪gv - v, S⟫) := by
    have hpar2 := hF.inner_eq (v + lam • (f - v) - (gv + mu • (gf - gv))) (f - v)
    rw [hD2, νf, mul_zero, add_zero, hTX, hD1, mul_zero, zero_mul, add_zero] at hpar2
    have h0 : ⟪v + lam • (f - v) - (gv + mu • (gf - gv)), S⟫ = 0 :=
      (mul_eq_zero.mp hpar2.symm).resolve_right hfS.ne'
    rw [inner_foot hDv S] at h0
    linarith
  have hsmf : ⟪m - v, S⟫ < ⟪f - v, S⟫ := by
    rw [smv]; have := mul_lt_mul_of_pos_right hs1 hfS; linarith
  have hsm0 : 0 < ⟪m - v, S⟫ := by rw [smv]; exact mul_pos hs0 hfS
  -- `D(f) > 0`: the foot is on the open chord, and (H4) fails
  have hX : ⟪f - v, S⟫ * (⟪gf - v, T⟫ - ⟪gv - v, T⟫) - ⟪f - v, T⟫ * (⟪gf - v, S⟫ - ⟪gv - v, S⟫) < 0 := by
    have e : ⟪f - v, S⟫ * (⟪gf - v, T⟫ - ⟪gv - v, T⟫) - ⟪f - v, T⟫ * (⟪gf - v, S⟫ - ⟪gv - v, S⟫) =
        ⟪m - v, S⟫ * (⟪gf - v, T⟫ - ⟪gv - v, T⟫) - ⟪m - v, T⟫ * (⟪gf - v, S⟫ - ⟪gv - v, S⟫) := by
      linear_combination -hK0
    rw [e]
    nlinarith [mul_pos hsm0 (by linarith : (0:ℝ) < ⟪gv - v, T⟫ - ⟪gf - v, T⟫),
      mul_pos htm (by linarith : (0:ℝ) < ⟪gf - v, S⟫ - ⟪gv - v, S⟫)]
  have hDf : (⟪gf - v, T⟫ - ⟪gv - v, T⟫) * (⟪f - v, S⟫ - ⟪gv - v, S⟫) <
      (⟪gf - v, S⟫ - ⟪gv - v, S⟫) * (⟪f - v, T⟫ - ⟪gv - v, T⟫) := by
    have : (⟪gf - v, T⟫ - ⟪gv - v, T⟫) * (⟪f - v, S⟫ - ⟪gv - v, S⟫) -
        (⟪gf - v, S⟫ - ⟪gv - v, S⟫) * (⟪f - v, T⟫ - ⟪gv - v, T⟫) =
        (1 - lam) * (⟪f - v, S⟫ * (⟪gf - v, T⟫ - ⟪gv - v, T⟫) -
          ⟪f - v, T⟫ * (⟪gf - v, S⟫ - ⟪gv - v, S⟫)) := by
      linear_combination (⟪gf - v, T⟫ - ⟪gv - v, T⟫) * hcs - (⟪gf - v, S⟫ - ⟪gv - v, S⟫) * hct
    nlinarith [mul_neg_of_pos_of_neg (sub_pos.mpr hl1) hX]
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ * (⟪gf - v, T⟫ - ⟪gv - v, T⟫) = ⟪gf - v, S⟫ - ⟪gv - v, S⟫ :=
    ⟨(⟪gf - v, S⟫ - ⟪gv - v, S⟫) / (⟪gf - v, T⟫ - ⟪gv - v, T⟫), div_mul_cancel₀ _ (by linarith)⟩
  obtain ⟨θ, M', hθ, hM', W1, W2, W3, W4, W5, W6, W7, W8, W9⟩ :=
    rd_limit_cert0 (s0 := ⟪gv - v, S⟫ - ρ * ⟪gv - v, T⟫) hsm0 hsmf h12 htm ht1 htf ht2 hK0 hDf
      hρ rfl
  unfold RdRimG
  exact ⟨S, N, ⟪m - v, S⟫, ⟪m - v, T⟫, ⟪f - v, S⟫, ⟪f - v, T⟫, ⟪gv - v, S⟫, ⟪gv - v, T⟫,
    ⟪gf - v, S⟫, ⟪gf - v, T⟫, -⟪gv - v, N⟫, ρ, θ, M', hF, ⟨rfl, rfl, νm⟩, ⟨rfl, rfl, νf⟩,
    ⟨rfl, rfl, by rw [νg, neg_neg]⟩, ⟨rfl, rfl, by rw [neg_neg]⟩, neg_pos.mpr hgvN,
    hsm0, hsmf, h12, htm, ht1, htf, ht2, hρ, hθ, hM', W1, W2, W3, W4, W5, W6, W7, W8, W9⟩

end Minimality

end
