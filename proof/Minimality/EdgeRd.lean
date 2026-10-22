module

public import Minimality.Type08R0

@[expose] public section

/-!
# A.10's conditions for any type (`FEWER-FACES-PROOFS.md` Theorem 22.8)

Lemma R0 (`rdRim_of_R0`) derives A.10's conditions `RdRim` for type 08 from a face `Φ` through
`m, f, g_f` ((H2)) and Lemma 9.3's claim ((H1)).  Theorem 22.8 needs neither: (H1) comes from
the residual (the slide rim and the partner closing two-peaked), (H4) from Lemma E (`v`, `w` on
opposite sides of the plane `f g_f g_v`), and (H2) from (H4) and `m` above the chord (the
referee's remark: `σ_mf < σ_vf < σ_g`).

* `h1_core` (**(H1)**): the depth pattern from the unimodal `K_v`, the two-peaked `K_w`, the
  two-peaked slide rim `v m f g_f g_v` and `m` above the chord.
* `rd_coords'`: (H2) and `D(v) > 0 > D(f)` from (H4), (H1), `s₁ < s₂` and the foot of the
  double normal, in coordinates.
* `rdRim_of_H`: `RdRim` from (H1), Lemma E, `g ∥ F_j` and the double normal's foot.
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

/-- **(H1) from the depth pattern** (Theorem 22.8, the depths in the orientation with the kept
apex `v` on top: `z_w < z_v`).  `K_v = v f g_f g_v` has no weak saddle, `K_w = w f g_f g_v`
has one, `m` lies above the chord `[v, f]`, and the slide rim `v m f g_f g_v` (distinct
depths) has two local maxima.  Then `z_v < z_m`, `z_v < z_{g_v}`, `z_f < z_v`, `z_{g_f} < z_v`. -/
theorem h1_core {zv zm zf zgf zgv zw s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hchord : zv + s * (zf - zv) < zm) (hw : zw < zv)
    (hNv : NWS4 (quad zv zf zgf zgv)) (hNw : ¬ NWS4 (quad zw zf zgf zgv))
    (hinj : Function.Injective (quint zv zm zf zgf zgv))
    (h2 : ∃ i j : ZMod 5, i ≠ j ∧
      (quint zv zm zf zgf zgv (i - 1) < quint zv zm zf zgf zgv i ∧
        quint zv zm zf zgf zgv (i + 1) < quint zv zm zf zgf zgv i) ∧
      (quint zv zm zf zgf zgv (j - 1) < quint zv zm zf zgf zgv j ∧
        quint zv zm zf zgf zgv (j + 1) < quint zv zm zf zgf zgv j)) :
    zv < zm ∧ zv < zgv ∧ zf < zv ∧ zgf < zv := by
  simp only [NWS4, quad_0, quad_1, quad_2, quad_3] at hNv hNw
  -- `K_w` two-peaked: the diagonal `{f, g_v}` lies above `{w, g_f}`
  have hK : zgf < zf ∧ zgf < zgv := by
    rcases not_and_or.mp hNw with hA | hB
    · push Not at hA
      exfalso
      rcases hNv.1 with h | h | h | h <;> linarith [hA.1, hA.2.1, hA.2.2.1, hA.2.2.2]
    · push Not at hB
      have h1 : zf ≠ zgf := fun e => absurd (@hinj 2 3 e) (by decide)
      have h2 : zgv ≠ zgf := fun e => absurd (@hinj 4 3 e) (by decide)
      exact ⟨lt_of_le_of_ne hB.2.2.1 (Ne.symm h1), lt_of_le_of_ne hB.2.2.2 (Ne.symm h2)⟩
  obtain ⟨hK1, hK2⟩ := hK
  -- `m` is not below both `v` and `f`
  have hval : ¬ (zm < zv ∧ zm < zf) := by
    rintro ⟨h1, h2⟩
    nlinarith [mul_pos hs0 (sub_pos.mpr h2), mul_pos (sub_pos.mpr hs1) (sub_pos.mpr h1)]
  obtain ⟨i, j, hij, hi, hj⟩ := h2
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_add_one
  obtain ⟨c0, c1, c2, c3, c4⟩ := zmod5_sub_one
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
  rcases zmod5_cases j with rfl | rfl | rfl | rfl | rfl <;>
  simp only [b0, b1, b2, b3, b4, c0, c1, c2, c3, c4, quint_0, quint_1, quint_2, quint_3,
    quint_4] at hi hj <;>
  first
  | exact absurd rfl hij
  | (exfalso; linarith [hi.1, hi.2, hj.1, hj.2])
  | (exfalso; apply hval; constructor <;> linarith [hi.1, hi.2, hj.1, hj.2])
  | (refine ⟨by linarith [hi.1, hi.2, hj.1, hj.2], by linarith [hi.1, hi.2, hj.1, hj.2], ?_, ?_⟩ <;>
      rcases hNv.2 with h | h | h | h <;> linarith [hi.1, hi.2, hj.1, hj.2])
  | (exfalso
     have hfv : zf < zv := by
       rcases hNv.2 with h | h | h | h <;> linarith [hi.1, hi.2, hj.1, hj.2]
     nlinarith [mul_pos (sub_pos.mpr hs1) (sub_pos.mpr hfv), hi.1, hi.2, hj.1, hj.2])

/-- **(H2) and `D(v) > 0 > D(f)` from (H4)** (Theorem 22.8, in A.10's coordinates; no face
through `m, f, g_f`): `m` above the chord (`t_m > 0 > t_f`, `0 < s_m < s_f`) and (H4)
`σ_vf < σ_g` give (H2) `σ_mf < σ_g`; the foot `λ f = g_v + μ (g_f − g_v)` of the double normal
on the open chord gives `D(v) > 0 > D(f)`. -/
theorem rd_coords' {sm tm sf tf s1 t1 s2 t2 lam mu : ℝ}
    (hsm : 0 < sm) (hmf : sm < sf) (htm : 0 < tm) (htf : tf < 0) (h12 : s1 < s2)
    (hH4 : tf * (s2 - s1) < sf * (t2 - t1))
    (hl0 : 0 < lam) (hl1 : lam < 1) (hcs : lam * sf = s1 + mu * (s2 - s1))
    (hct : lam * tf = t1 + mu * (t2 - t1)) :
    (tf - tm) * (s2 - s1) < (t2 - t1) * (sf - sm) ∧ 0 < s1 * t2 - s2 * t1 ∧
      (s2 - s1) * (tf - t1) < (t2 - t1) * (sf - s1) := by
  have hsf : 0 < sf := by linarith
  refine ⟨?_, ?_, ?_⟩
  · have key : sf * ((tf - tm) * (s2 - s1) - (t2 - t1) * (sf - sm)) =
        (sf - sm) * (tf * (s2 - s1) - sf * (t2 - t1)) + (s2 - s1) * (sm * tf - sf * tm) := by
      ring
    have e1 : (sf - sm) * (tf * (s2 - s1) - sf * (t2 - t1)) < 0 :=
      mul_neg_of_pos_of_neg (by linarith) (by linarith)
    have e3 : sm * tf - sf * tm < 0 := by
      have := mul_pos hsm (neg_pos.mpr htf)
      have := mul_pos hsf htm
      nlinarith
    have e2 : (s2 - s1) * (sm * tf - sf * tm) < 0 := mul_neg_of_pos_of_neg (by linarith) e3
    have : sf * ((tf - tm) * (s2 - s1) - (t2 - t1) * (sf - sm)) < 0 := by rw [key]; linarith
    have := neg_of_mul_neg_right this hsf.le
    linarith
  · have : s1 * t2 - s2 * t1 = lam * (sf * (t2 - t1) - tf * (s2 - s1)) := by
      linear_combination (s2 - s1) * hct - (t2 - t1) * hcs
    rw [this]; exact mul_pos hl0 (by linarith)
  · have : (t2 - t1) * (sf - s1) - (s2 - s1) * (tf - t1) =
        (1 - lam) * (sf * (t2 - t1) - tf * (s2 - s1)) := by
      linear_combination (t2 - t1) * hcs - (s2 - s1) * hct
    nlinarith [mul_pos (sub_pos.mpr hl1) (show 0 < sf * (t2 - t1) - tf * (s2 - s1) by linarith)]

set_option maxHeartbeats 1000000 in
/-- **A.10's conditions from Theorem 22.8's hypotheses.**  `m = v + s (f − v) + δ (v − w)`
(`0 < s < 1`, `δ > 0`: the middle of `F_j` above the chord, in the orientation `v − w` with
the kept apex `v` on top), `g_v` off `F_j`'s plane, the rim `v f g_f g_v` oriented, the far edge
`g ∥ F_j`, Lemma E strict (`v`, `w` on opposite sides of the plane `f g_f g_v`), (H1) along
`v − w`, and the foot of the double normal on the open chord `(v, f)`.  Then `RdRim`. -/
theorem rdRim_of_H {v m f gf gv w : ℝ³} {s δ : ℝ}
    (hm : m = v + s • (f - v) + δ • (v - w)) (hs0 : 0 < s) (hs1 : s < 1) (hδ : 0 < δ)
    (hoff : det3 (v - w) (f - v) (gv - v) ≠ 0)
    (horient : 0 < det3 (f - v) (gf - v) (v - w) * det3 (gv - gf) (v - gf) (v - w))
    (hpar : det3 (v - w) (f - v) (gf - gv) = 0)
    (hE : det3 (gf - f) (gv - f) (v - f) * det3 (gf - f) (gv - f) (w - f) < 0)
    (hH1 : 0 < ⟪m - v, v - w⟫ ∧ 0 < ⟪gv - v, v - w⟫ ∧ ⟪f - v, v - w⟫ < 0 ∧
      ⟪gf - v, v - w⟫ < 0)
    (hfeet : ∃ lam mu : ℝ, 0 < lam ∧ lam < 1 ∧
      ⟪v + lam • (f - v) - (gv + mu • (gf - gv)), v - w⟫ = 0 ∧
      ⟪v + lam • (f - v) - (gv + mu • (gf - gv)), f - v⟫ = 0) :
    RdRim v m f gf gv (v - w) := by
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
  -- (H4) from Lemma E
  have hpt : ∀ a b c a' b' c' a'' b'' c'' : ℝ, det3 (pt a b c) (pt a' b' c') (pt a'' b'' c'') =
      (b * c' - c * b') * a'' + (c * a' - a * c') * b'' + (a * b' - b * a') * c'' := by
    intro a b c a' b' c' a'' b'' c''; simp only [det3_expand, pt_zero, pt_one, pt_two]
  have co : ∀ (P : ℝ³) (Y : ℝ³), ⟪P - f, Y⟫ = ⟪P - v, Y⟫ - ⟪f - v, Y⟫ := by
    intro P Y; rw [← inner_sub_left]; congr 1; abel
  have hvv : ∀ Y : ℝ³, ⟪v - v, Y⟫ = 0 := fun Y => by rw [sub_self, inner_zero_left]
  have hA : det3 (gf - f) (gv - f) (v - f) = ε * (-⟪gv - v, N⟫ *
      (⟪f - v, S⟫ * (⟪gf - v, T⟫ - ⟪gv - v, T⟫) - ⟪f - v, T⟫ * (⟪gf - v, S⟫ - ⟪gv - v, S⟫))) := by
    rw [hF.det3_eq, ← hε, co gf S, co gf T, co gf N, co gv S, co gv T, co gv N, co v S, co v T,
      co v N, hvv, hvv, hvv, νf, νg, hpt]
    ring
  have hB : det3 (gf - f) (gv - f) (v - u - f) = ε * (-⟪gv - v, N⟫ *
      (⟪f - v, S⟫ * (⟪gf - v, T⟫ - ⟪gv - v, T⟫) - ⟪f - v, T⟫ * (⟪gf - v, S⟫ - ⟪gv - v, S⟫) -
        L * (⟪gf - v, S⟫ - ⟪gv - v, S⟫))) := by
    have e1 : ∀ Y : ℝ³, ⟪v - u - f, Y⟫ = -⟪f - v, Y⟫ - ⟪u, Y⟫ := by
      intro Y
      rw [show v - u - f = -(f - v) - u by abel, inner_sub_left, inner_neg_left]
    rw [hF.det3_eq, ← hε, co gf S, co gf T, co gf N, co gv S, co gv T, co gv N, e1, e1, e1, uS,
      uT, νu, νf, νg, hpt]
    ring
  have hH4 : ⟪f - v, T⟫ * (⟪gf - v, S⟫ - ⟪gv - v, S⟫) <
      ⟪f - v, S⟫ * (⟪gf - v, T⟫ - ⟪gv - v, T⟫) := by
    rw [hA, hB] at hE
    set n0 := ⟪gv - v, N⟫ with hn0
    set X := ⟪f - v, S⟫ * (⟪gf - v, T⟫ - ⟪gv - v, T⟫) -
      ⟪f - v, T⟫ * (⟪gf - v, S⟫ - ⟪gv - v, S⟫) with hX
    have e : ε * (-n0 * X) * (ε * (-n0 * (X - L * (⟪gf - v, S⟫ - ⟪gv - v, S⟫)))) =
        (ε * ε) * (n0 * n0) * (X * (X - L * (⟪gf - v, S⟫ - ⟪gv - v, S⟫))) := by ring
    rw [e, hεε, one_mul] at hE
    have hn2 : 0 < n0 * n0 := mul_pos_of_neg_of_neg hgvN hgvN
    have hXX : X * (X - L * (⟪gf - v, S⟫ - ⟪gv - v, S⟫)) < 0 := neg_of_mul_neg_right hE hn2.le
    have hLs : 0 < L * (⟪gf - v, S⟫ - ⟪gv - v, S⟫) := mul_pos hL (by linarith)
    by_contra hcon
    push Not at hcon
    have hX0 : X ≤ 0 := by rw [hX]; linarith
    nlinarith
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
  obtain ⟨H2, Dv, Df⟩ := rd_coords' (sm := ⟪m - v, S⟫) (tm := ⟪m - v, T⟫) (sf := ⟪f - v, S⟫)
    (tf := ⟪f - v, T⟫) (s1 := ⟪gv - v, S⟫) (t1 := ⟪gv - v, T⟫) (s2 := ⟪gf - v, S⟫)
    (t2 := ⟪gf - v, T⟫) hsm0 hsmf htm htf h12 hH4 hl0 hl1 hcs hct
  unfold RdRim
  exact ⟨S, N, ⟪m - v, S⟫, ⟪m - v, T⟫, ⟪f - v, S⟫, ⟪f - v, T⟫, ⟪gv - v, S⟫, ⟪gv - v, T⟫,
    ⟪gf - v, S⟫, ⟪gf - v, T⟫, -⟪gv - v, N⟫, hF, ⟨rfl, rfl, νm⟩, ⟨rfl, rfl, νf⟩,
    ⟨rfl, rfl, by rw [νg, neg_neg]⟩, ⟨rfl, rfl, by rw [neg_neg]⟩, neg_pos.mpr hgvN,
    hsm0, hsmf, h12, htm, ht1, htf, ht2, H2, Dv, Df⟩

end Minimality

end
