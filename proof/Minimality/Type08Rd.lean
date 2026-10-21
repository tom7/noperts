module

public import Minimality.Chords
public import Minimality.OctaTools
public import Minimality.Type08Slide

@[expose] public section

/-!
# Type 08: `R_d` is Rupert (`FEWER-FACES-PROOFS.md` §10 addendum, A.10)

Lemma H of the addendum closes a one-circle closing `K_v` that has a horizontal double
normal perpendicular to its only realizing face `F_j` by sliding along the other face
`F_k`: at the views `u′_η` of `F_k`'s great circle the middle `m` of `F_j` pokes out
and the rim is the five-corner rim `v m f g_f g_v`.  When that rim is two-peaked
(the open piece `R_d` of type (d): the far edge `g = [g_v, g_f]` is parallel to `F_j`)
Theorem 7.3 does not apply, but A.10 shows that the rim is still first-order free for
all small `η > 0`, from one explicit slot-weight certificate of the `η → 0` limit system
(Lemma R2).  Here that certificate becomes a motion `(ω, τ)` that is strictly inward at
every slot (`TiltCert`) at a view exactly in `F_k`'s plane, and `isRupert_of_chords`
(Proposition 8.8 with `F_k`'s middles) concludes.

*Coordinates* (as in A.10): `v` is the origin, the depth `t` is the second coordinate
(the view `u₀` along the axle is `(0, 1, 0)`), `F_j` is the plane `ν = 0` (third
coordinate), `m = (s_m, t_m, 0)`, `f = (s_f, t_f, 0)`, `g_v = (s₁, t₁, −h)`,
`g_f = (s₂, t₂, −h)` with `h > 0`.  The view is `u₀ + κ (s₁, 0, −h)`, in the plane of
`F_k` (through the axle and `g_v`).  With `ρ = (s₂ − s₁) / (t₂ − t₁)` (the inverse slope
of `g`), `s₀ = s₁ − ρ t₁` and `D(P) = s_P − s₀ − ρ t_P`, the hypotheses (H1)–(H4) of
Lemma R0 read: `t_m, t₁ > 0 > t_f, t₂` (H1); `σ_mf < σ_g` (H2); `D(v) > 0 > D(f)` (H4);
(H3) is not needed beyond (H4).

* `rd_limit_cert` (**Lemma R2**): the ten slot weights of the limit system are positive
  for one choice of the certificate's parameters (`t* = −θ`, `δ = θ`, `λ = −ρ M`, with
  `M` balancing the two slots of `[m, f]`).
* `eventually_det3_lin`, `eventually_slot`: a slot test along the tilt,
  `det3 e (V₀ + κ V₁) (u₀ + κ u₁)`, is positive for small `κ > 0` if its value at `0` is
  positive (side slots), or zero with a positive first-order term (top and bottom slots:
  the limit system's weight).  This replaces the paper's rescaled limit (Lemma R1).
* `isRupert_rd_std` (**Theorem R**, in the coordinates above): the point set is Rupert.
  The motion is `ω = (κ h (ρ − M), κ h (1 + ρ M), ρ M)`,
  `τ = (−ρ M θ, 0, κ h (s₀ + θ − M θ))`; the middles of `F_k` (the other end `w` of the
  axle, and `F_k`'s other vertices) are given by their coordinates in `F_k`'s plane;
  every other point is strictly hidden at `u₀` (`RdHidden`).  `η` is not uniform: the
  statement is "for all small `κ > 0`", obtained from `Filter.Eventually`.
* `isRupert_rd`: the same for any orthonormal frame `S, T, N` (`IsFrame`, either
  orientation), by the isometry to the coordinates above (`isRupert_of_frame_image`,
  `RdHidden.frame`); `isRupert_of_rdRim`: with the view along an edge vector `e` and the
  conditions bundled as `RdRim`.
* The two type-08 closings of A.10's table: `isRupert_quad_edge_middle_rd` (N2–`K_c`,
  rim `c 2 b c' b'`, circle `a'b'c`; the hidden `a` lies strictly inside a triangle of the
  rim, `rdHidden_quad_edge`) and `isRupert_t4b_rd` (T4–`K_b`, rim `b a' c b' c'`, circle
  `Q_ab` with the middles `2`, `a`).  `Type08Gen.slideN2c`, `slideT4b` accept `R_d` as a
  third alternative (`RdCond`, via Lemma R0).

(H1)–(H4) are hypotheses here (`RdRim`); Lemma R0, that they hold on `R_d` off `Σ`, is
`Type08R0.lean` (`rdRim_of_R0`).
-/

namespace Minimality

open scoped RealInnerProductSpace Topology Matrix
open Finset Filter

/-- A point of `ℝ³` by its coordinates. -/
noncomputable def pt (a b c : ℝ) : ℝ³ := !₂[a, b, c]

@[simp] theorem pt_zero (a b c : ℝ) : pt a b c 0 = a := rfl
@[simp] theorem pt_one (a b c : ℝ) : pt a b c 1 = b := rfl
@[simp] theorem pt_two (a b c : ℝ) : pt a b c 2 = c := rfl

/-- **Lemma R2 of A.10 (one certificate for the limit system).**  With the inverse slope
`ρ` of the far edge `g` (`ρ (t₂ − t₁) = s₂ − s₁`), `s₀ = s₁ − ρ t₁` and the depth-shifted
distance `D(P) = s_P − s₀ − ρ t_P` from the line of `g`, assume (H1)
`t_m, t₁ > 0 > t_f, t₂`, (H2) `σ_mf < σ_g`, and (H4) `D(v) > 0 > D(f)`.  Then for some
`θ, M > 0` (`t* = −θ`, `δ = θ`, `ℓ(t) = −ρ M (t + θ)`) the slot weights of LP0 are all
positive: the top slots `[v, m]` at `v`, `m` and `[m, f]` at `m`, `f` (in the form
`e₀ (D − δ) + M (t + θ) (e₀ − ρ e₁)` for the edge `e`), the bottom slots
(`(s₂ − s₁) δ`), and the side slots `ℓ(0)`, `ℓ(t₁)` and `−ℓ(t_f)`, `−ℓ(t₂)`. -/
theorem rd_limit_cert {sm tm sf tf s1 t1 s2 t2 ρ s0 : ℝ}
    (hsm : 0 < sm) (hmf : sm < sf) (h12 : s1 < s2)
    (htm : 0 < tm) (ht1 : 0 < t1) (htf : tf < 0) (ht2 : t2 < 0)
    (hH2 : (tf - tm) * (s2 - s1) < (t2 - t1) * (sf - sm))
    (hDv : 0 < s1 * t2 - s2 * t1)
    (hDf : (s2 - s1) * (tf - t1) < (t2 - t1) * (sf - s1))
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
  -- D(v) = −s₀ > 0, D(f) < 0, and K = ρ (t_f − t_m) − (s_f − s_m) > 0 (H2)
  have hDv' : 0 < -s0 := by
    have : -s0 * (t1 - t2) = s1 * t2 - s2 * t1 := by rw [hs0]; linear_combination (-t1) * hρ
    by_contra hc; push Not at hc; linarith [mul_nonpos_of_nonpos_of_nonneg hc ht12.le]
  set DM := sm - s0 - ρ * tm with hDM
  set DF := sf - s0 - ρ * tf with hDF
  have hDF' : DF < 0 := by
    have : DF * (t1 - t2) = (sf - s1) * (t1 - t2) + (s2 - s1) * (tf - t1) := by
      rw [hDF, hs0]; linear_combination (tf - t1) * hρ
    by_contra hc; push Not at hc; linarith [mul_nonneg hc ht12.le]
  have hDM' : -s0 < DM := by rw [hDM]; linarith [mul_pos (neg_pos.mpr hρneg) htm]
  set K := ρ * (tf - tm) - (sf - sm) with hK
  have hK' : 0 < K := by
    have : K * (t1 - t2) = -((tf - tm) * (s2 - s1)) - (sf - sm) * (t1 - t2) := by
      rw [hK]; linear_combination (tm - tf) * hρ
    exact pos_of_mul_pos_left (by rw [this]; linarith [hH2]) ht12.le
  have htmf : 0 < tm - tf := by linarith
  -- the balanced choice of `M`: the two `[m, f]` slots get the same slack
  set M := (sf - sm) * (DM - DF) / (K * (tm - tf)) with hMdef
  have hKt : 0 < K * (tm - tf) := mul_pos hK' htmf
  have hM : 0 < M := div_pos (mul_pos (by linarith) (by linarith)) hKt
  have hMK : M * (K * (tm - tf)) = (sf - sm) * (DM - DF) := div_mul_cancel₀ _ hKt.ne'
  -- `Q = D(N₀) (t_m − t_f) > 0`, `N₀` the point of `MF` at depth `0`
  set Q := DF * tm - DM * tf with hQ
  have hQ' : 0 < Q := by
    have : Q = sf * tm - sm * tf - s0 * (tm - tf) := by rw [hQ, hDM, hDF]; ring
    rw [this]; linarith [mul_pos hsm (neg_pos.mpr htf), mul_pos (by linarith : (0:ℝ) < sf) htm,
      mul_pos hDv' htmf]
  -- `θ` small
  have hev : ∀ᶠ θ in 𝓝[>] (0 : ℝ), 0 < θ ∧ 0 < -tf + θ * (-1) ∧ 0 < -t2 + θ * (-1) ∧
      0 < -s0 + θ * (-1) ∧ 0 < Q + θ * (-(tm - tf) - (DM - DF)) := by
    filter_upwards [self_mem_nhdsWithin, eventually_pos_affine (Or.inl (neg_pos.mpr htf)),
      eventually_pos_affine (Or.inl (neg_pos.mpr ht2)), eventually_pos_affine (Or.inl hDv'),
      eventually_pos_affine (Or.inl hQ')] with θ h0 h1 h2 h3 h4
    exact ⟨h0, h1, h2, h3, h4⟩
  obtain ⟨θ, hθ, hθf, hθ2, hθ0, hθQ⟩ := hev.exists
  have hsmρ : 0 < sm - ρ * tm := by linarith [mul_pos (neg_pos.mpr hρneg) htm]
  refine ⟨θ, M, hθ, hM, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact add_pos (mul_pos hsm (by linarith)) (mul_pos (mul_pos hM hθ) hsmρ)
  · exact add_pos (mul_pos hsm (by linarith)) (mul_pos (mul_pos hM (by linarith)) hsmρ)
  · -- times `t_m − t_f`: `(s_f − s_m) (Q − θ (t_m − t_f) − θ (D(m) − D(f)))`
    have e : ((sf - sm) * (DM - θ) + M * (tm + θ) * ((sf - sm) - ρ * (tf - tm))) * (tm - tf) =
        (sf - sm) * (Q + θ * (-(tm - tf) - (DM - DF))) := by
      rw [hQ]; linear_combination (-(tm + θ)) * hMK
    have : 0 < (sf - sm) * (Q + θ * (-(tm - tf) - (DM - DF))) :=
      mul_pos (by linarith) (by linarith)
    rw [← e] at this; exact pos_of_mul_pos_left this htmf.le
  · have e : ((sf - sm) * (DF - θ) + M * (tf + θ) * ((sf - sm) - ρ * (tf - tm))) * (tm - tf) =
        (sf - sm) * (Q + θ * (-(tm - tf) - (DM - DF))) := by
      rw [hQ]; linear_combination (-(tf + θ)) * hMK
    have : 0 < (sf - sm) * (Q + θ * (-(tm - tf) - (DM - DF))) :=
      mul_pos (by linarith) (by linarith)
    rw [← e] at this; exact pos_of_mul_pos_left this htmf.le
  · exact mul_pos (by linarith) hθ
  · have := mul_pos (mul_pos (neg_pos.mpr hρneg) hM) hθ; linarith
  · exact mul_pos (mul_pos (neg_pos.mpr hρneg) hM) (by linarith)
  · exact mul_pos_of_neg_of_neg (mul_neg_of_neg_of_pos hρneg hM) (by linarith)
  · exact mul_pos_of_neg_of_neg (mul_neg_of_neg_of_pos hρneg hM) (by linarith)

/-- **A slot test along the tilt.**  The test `det3 e (V₀ + κ V₁) (u₀ + κ u₁)` (velocity and
view affine in `κ`) is positive for small `κ > 0` if it is positive at `κ = 0`, or zero
there with a positive first-order term (the slot's weight in the limit system). -/
theorem eventually_det3_lin (e V₀ V₁ u₀ u₁ : ℝ³)
    (h : 0 < det3 e V₀ u₀ ∨ (det3 e V₀ u₀ = 0 ∧ 0 < det3 e V₁ u₀ + det3 e V₀ u₁)) :
    ∀ᶠ κ in 𝓝[>] (0 : ℝ), 0 < det3 e (V₀ + κ • V₁) (u₀ + κ • u₁) := by
  have hexp : ∀ κ : ℝ, det3 e (V₀ + κ • V₁) (u₀ + κ • u₁) =
      det3 e V₀ u₀ + κ * ((det3 e V₁ u₀ + det3 e V₀ u₁) + κ * det3 e V₁ u₁) := by
    intro κ; simp only [det3_expand, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
  rcases h with h | ⟨h0, h1⟩
  · have hc : Continuous fun κ : ℝ =>
        det3 e V₀ u₀ + κ * ((det3 e V₁ u₀ + det3 e V₀ u₁) + κ * det3 e V₁ u₁) := by fun_prop
    have hev := (hc.tendsto 0).eventually (lt_mem_nhds (by simpa using h))
    filter_upwards [hev.filter_mono nhdsWithin_le_nhds] with κ hκ
    rw [hexp]; exact hκ
  · filter_upwards [self_mem_nhdsWithin, eventually_pos_affine
      (A := det3 e V₁ u₀ + det3 e V₀ u₁) (B := det3 e V₁ u₁) (Or.inl h1)] with κ hκ h2
    rw [hexp, h0, zero_add]; exact mul_pos hκ h2

/-- The velocity of a point under a motion affine in `κ` is affine in `κ`. -/
theorem cross_add_smul_vel (ω₀ ω₁ τ₀ τ₁ x : ℝ³) (κ : ℝ) :
    cross (ω₀ + κ • ω₁) x + (τ₀ + κ • τ₁) = (cross ω₀ x + τ₀) + κ • (cross ω₁ x + τ₁) := by
  ext i; fin_cases i <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, cross_apply_zero, cross_apply_one,
      cross_apply_two, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] <;> ring

/-- `eventually_det3_lin` for the velocity `ω × x + τ` of a point under the motion
`(ω₀ + κ ω₁, τ₀ + κ τ₁)`. -/
theorem eventually_slot (e x ω₀ ω₁ τ₀ τ₁ u₀ u₁ : ℝ³)
    (h : 0 < det3 e (cross ω₀ x + τ₀) u₀ ∨ (det3 e (cross ω₀ x + τ₀) u₀ = 0 ∧
      0 < det3 e (cross ω₁ x + τ₁) u₀ + det3 e (cross ω₀ x + τ₀) u₁)) :
    ∀ᶠ κ in 𝓝[>] (0 : ℝ), 0 < det3 e (cross (ω₀ + κ • ω₁) x + (τ₀ + κ • τ₁)) (u₀ + κ • u₁) := by
  simp only [cross_add_smul_vel]; exact eventually_det3_lin _ _ _ _ _ h

/-- `x` lies strictly inside a triangle of points of `V` at the view `w` (the second case
of `TiltCert`). -/
def RdHidden (V : Finset ℝ³) (w x : ℝ³) : Prop :=
  ∃ a ∈ V, ∃ b ∈ V, ∃ c ∈ V, 0 < det3 (b - a) (c - a) w ∧ 0 < det3 (b - a) (x - a) w ∧
    0 < det3 (c - b) (x - b) w ∧ 0 < det3 (a - c) (x - c) w

theorem RdHidden.eventually_tilt {V : Finset ℝ³} {w x : ℝ³} (v : ℝ³) (h : RdHidden V w x) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), RdHidden V (w + ε • v) x := by
  obtain ⟨a, ha, b, hb, c, hc, h0, h1, h2, h3⟩ := h
  filter_upwards [eventually_det3_pos v h0, eventually_det3_pos v h1,
    eventually_det3_pos v h2, eventually_det3_pos v h3] with ε e0 e1 e2 e3
  exact ⟨a, ha, b, hb, c, hc, e0, e1, e2, e3⟩

/-- The determinant expansion used for the slot tests in coordinates. -/
macro "rd_simp" : tactic => `(tactic| simp only [det3_expand, cross_apply_zero, cross_apply_one,
  cross_apply_two, PiLp.add_apply, PiLp.sub_apply, PiLp.neg_apply, PiLp.smul_apply, smul_eq_mul,
  pt_zero, pt_one, pt_two])

-- Unfold the named view, motion and rim of `isRupert_rd_std` and expand the determinants.
set_option hygiene false in
macro "rd_unfold" : tactic =>
  `(tactic| (simp only [hu₀, hu₁, hω₀, hω₁, hτ₀, hτ₁, hv_def, hm_def, hf_def, hgf_def,
    hgv_def] ; rd_simp))

set_option maxHeartbeats 1000000 in
/-- **Theorem R of A.10 (`R_d` is Rupert), in coordinates.**  The five-corner rim
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
theorem isRupert_rd_std (V M : Finset ℝ³) {sm tm sf tf s1 t1 s2 t2 h : ℝ}
    (hv : pt 0 0 0 ∈ V) (hm : pt sm tm 0 ∈ V) (hf : pt sf tf 0 ∈ V)
    (hgf : pt s2 t2 (-h) ∈ V) (hgv : pt s1 t1 (-h) ∈ V)
    (hh : 0 < h) (hsm : 0 < sm) (hmf : sm < sf) (h12 : s1 < s2)
    (htm : 0 < tm) (ht1 : 0 < t1) (htf : tf < 0) (ht2 : t2 < 0)
    (hH2 : (tf - tm) * (s2 - s1) < (t2 - t1) * (sf - sm))
    (hDv : 0 < s1 * t2 - s2 * t1)
    (hDf : (s2 - s1) * (tf - t1) < (t2 - t1) * (sf - s1))
    (hM : ∀ x ∈ M, ∃ p q : ℝ, x = pt (p * s1) (p * t1 + q) (-(p * h)) ∧ q ≠ 0 ∧
      ((0 < p ∧ p < 1) ∨ (p = 0 ∧ q < 0)))
    (hrest : ∀ x ∈ V, x ∉ M → x = pt 0 0 0 ∨ x = pt sm tm 0 ∨ x = pt sf tf 0 ∨
      x = pt s2 t2 (-h) ∨ x = pt s1 t1 (-h) ∨ RdHidden V (pt 0 1 0) x) :
    IsRupert V := by
  classical
  have ht12 : 0 < t1 - t2 := by linarith
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ * (t2 - t1) = s2 - s1 :=
    ⟨(s2 - s1) / (t2 - t1), div_mul_cancel₀ _ (by linarith)⟩
  obtain ⟨θ, M', hθ, hM', W1, W2, W3, W4, W5, W6, W7, W8, W9⟩ :=
    rd_limit_cert (s0 := s1 - ρ * t1) hsm hmf h12 htm ht1 htf ht2 hH2 hDv hDf hρ rfl
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
    rcases hrest x hx hxM with rfl | rfl | rfl | rfl | rfl | hid
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

/-! ### Frame-free form -/

/-- An orthonormal frame `S, T, N` (any orientation). -/
def IsFrame (S T N : ℝ³) : Prop :=
  ⟪S, S⟫ = 1 ∧ ⟪T, T⟫ = 1 ∧ ⟪N, N⟫ = 1 ∧ ⟪S, T⟫ = 0 ∧ ⟪S, N⟫ = 0 ∧ ⟪T, N⟫ = 0

/-- The matrix with rows `S`, `T`, `N`. -/
noncomputable def orthoFrameMat (S T N : ℝ³) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of ![![S 0, S 1, S 2], ![T 0, T 1, T 2], ![N 0, N 1, N 2]]

theorem orthoFrameMat_apply (S T N x : ℝ³) :
    (orthoFrameMat S T N).toEuclideanLin x = pt ⟪x, S⟫ ⟪x, T⟫ ⟪x, N⟫ := by
  ext i; fin_cases i <;>
    simp [orthoFrameMat, pt, Matrix.toLpLin_apply, dotProduct, Fin.sum_univ_three, PiLp.inner_apply]

theorem IsFrame.mul_transpose {S T N : ℝ³} (h : IsFrame S T N) :
    orthoFrameMat S T N * (orthoFrameMat S T N)ᵀ = 1 := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  simp only [PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, conj_trivial] at h1 h2 h3 h4 h5 h6
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [orthoFrameMat, Matrix.mul_apply, Fin.sum_univ_three] <;>
    first | linear_combination h1 | linear_combination h2 | linear_combination h3 |
      linear_combination h4 | linear_combination h5 | linear_combination h6

/-- Rupert-ness transported back from the frame coordinates `x ↦ (⟪x − v, S⟫, ⟪x − v, T⟫,
⟪x − v, N⟫)` (an isometry, possibly orientation-reversing). -/
theorem isRupert_of_frame_image (V : Finset ℝ³) {v S T N : ℝ³} (hF : IsFrame S T N)
    (h : IsRupert (V.image fun x => (orthoFrameMat S T N).toEuclideanLin (x - v))) : IsRupert V := by
  classical
  set A := orthoFrameMat S T N
  have hA : A ∈ Matrix.orthogonalGroup (Fin 3) ℝ :=
    (Matrix.mem_orthogonalGroup_iff (Fin 3) ℝ).mpr hF.mul_transpose
  have hAA : Aᵀ * A = 1 := (Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ).mp hA
  have hAt : Aᵀ ∈ Matrix.orthogonalGroup (Fin 3) ℝ := by
    rw [Matrix.mem_orthogonalGroup_iff, Matrix.transpose_transpose]; exact hAA
  have := Noperts.Pipeline.isRupert_image_similarity v 1 one_pos Aᵀ hAt _ h
  rw [Finset.image_image] at this
  have hcomp : ((fun x => v + (1 : ℝ) • Aᵀ.toEuclideanLin x) ∘
      fun x => A.toEuclideanLin (x - v)) = id := by
    funext x
    simp only [Function.comp_apply, one_smul, id]
    have : Aᵀ.toEuclideanLin (A.toEuclideanLin (x - v)) = x - v := by
      simp [Matrix.toLpLin_apply, Matrix.mulVec_mulVec, hAA]
    rw [this]; abel
  rwa [hcomp, Finset.image_id] at this

/-- The squared orientation of a frame. -/
theorem IsFrame.det3_sq {S T N : ℝ³} (h : IsFrame S T N) : det3 S T N * det3 S T N = 1 := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  have gram : det3 S T N * det3 S T N =
      ⟪S, S⟫ * (⟪T, T⟫ * ⟪N, N⟫ - ⟪T, N⟫ * ⟪T, N⟫) - ⟪S, T⟫ * (⟪S, T⟫ * ⟪N, N⟫ - ⟪T, N⟫ * ⟪S, N⟫) +
        ⟪S, N⟫ * (⟪S, T⟫ * ⟪T, N⟫ - ⟪T, T⟫ * ⟪S, N⟫) := by
    simp only [det3_expand, PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply,
      conj_trivial]; ring
  rw [gram, h1, h2, h3, h4, h5, h6]; norm_num

/-- Determinants in frame coordinates: the orientation times the determinant. -/
theorem det3_frameCoords (S T N a b c : ℝ³) :
    det3 (pt ⟪a, S⟫ ⟪a, T⟫ ⟪a, N⟫) (pt ⟪b, S⟫ ⟪b, T⟫ ⟪b, N⟫) (pt ⟪c, S⟫ ⟪c, T⟫ ⟪c, N⟫) =
      det3 S T N * det3 a b c := by
  simp only [det3_expand, pt_zero, pt_one, pt_two, PiLp.inner_apply, Fin.sum_univ_three,
    RCLike.inner_apply, conj_trivial]; ring

/-- `RdHidden` with the triangle's orientation reversed. -/
theorem rdHidden_of_neg {V : Finset ℝ³} {w x a b c : ℝ³} (ha : a ∈ V) (hb : b ∈ V) (hc : c ∈ V)
    (h0 : det3 (b - a) (c - a) w < 0) (h1 : det3 (b - a) (x - a) w < 0)
    (h2 : det3 (c - b) (x - b) w < 0) (h3 : det3 (a - c) (x - c) w < 0) : RdHidden V w x := by
  refine ⟨a, ha, c, hc, b, hb, ?_, ?_, ?_, ?_⟩
  · have : det3 (c - a) (b - a) w = -det3 (b - a) (c - a) w := by
      simp only [det3_expand, PiLp.sub_apply]; ring
    linarith
  · have : det3 (c - a) (x - a) w = -det3 (a - c) (x - c) w := by
      simp only [det3_expand, PiLp.sub_apply]; ring
    linarith
  · have : det3 (b - c) (x - c) w = -det3 (c - b) (x - b) w := by
      simp only [det3_expand, PiLp.sub_apply]; ring
    linarith
  · have : det3 (a - b) (x - b) w = -det3 (b - a) (x - a) w := by
      simp only [det3_expand, PiLp.sub_apply]; ring
    linarith

/-- Hidden points stay hidden in frame coordinates (either orientation of the frame). -/
theorem RdHidden.frame {V : Finset ℝ³} {v S T N x : ℝ³} (hF : IsFrame S T N)
    (h : RdHidden V T x) :
    RdHidden (V.image fun y => (orthoFrameMat S T N).toEuclideanLin (y - v)) (pt 0 1 0)
      ((orthoFrameMat S T N).toEuclideanLin (x - v)) := by
  classical
  obtain ⟨a, ha, b, hb, c, hc, h0, h1, h2, h3⟩ := h
  have hsq := hF.det3_sq
  obtain ⟨-, hTT, -, hST, -, hTN⟩ := hF
  have hT : pt 0 1 0 = pt ⟪T, S⟫ ⟪T, T⟫ ⟪T, N⟫ := by
    rw [real_inner_comm, hST, hTT, hTN]
  have key : ∀ p q r : ℝ³, det3 ((orthoFrameMat S T N).toEuclideanLin (p - v) -
      (orthoFrameMat S T N).toEuclideanLin (r - v)) ((orthoFrameMat S T N).toEuclideanLin (q - v) -
      (orthoFrameMat S T N).toEuclideanLin (r - v)) (pt 0 1 0) = det3 S T N * det3 (p - r) (q - r) T := by
    intro p q r
    rw [← map_sub, ← map_sub, show p - v - (r - v) = p - r by abel,
      show q - v - (r - v) = q - r by abel, orthoFrameMat_apply, orthoFrameMat_apply, hT, det3_frameCoords]
  have hmem : ∀ y ∈ V, (orthoFrameMat S T N).toEuclideanLin (y - v) ∈
      V.image fun y => (orthoFrameMat S T N).toEuclideanLin (y - v) := fun y hy => mem_image_of_mem _ hy
  rcases mul_self_eq_one_iff.mp hsq with hε | hε
  · refine ⟨_, hmem a ha, _, hmem b hb, _, hmem c hc, ?_, ?_, ?_, ?_⟩ <;>
      rw [key, hε, one_mul] <;> assumption
  · exact rdHidden_of_neg (hmem a ha) (hmem b hb) (hmem c hc) (by rw [key, hε]; linarith)
      (by rw [key, hε]; linarith) (by rw [key, hε]; linarith) (by rw [key, hε]; linarith)

/-- **Theorem R of A.10 (`R_d` is Rupert), frame-free.**  Let `S, T, N` be an orthonormal
frame (either orientation): `T` along the axle (the view `u₀`), `N` normal to the face
`F_j`, and give each point `x` the coordinates `(⟪x − v, S⟫, ⟪x − v, T⟫, ⟪x − v, N⟫)`.  The
five-corner rim `v m f g_f g_v` (`m`, `f` in `F_j`'s plane `ν = 0`, the far edge
`g = [g_v, g_f]` at `ν = −h`, parallel to `F_j`) satisfies (H1), (H2), (H4) as in
`isRupert_rd_std`; the middles `M` of `F_k` lie in the plane through the axle and `g_v`
(`x = v + p (g_v − v) + q T`, `q ≠ 0`, `0 < p < 1` or `p = 0`, `q < 0`), and every other
point is strictly hidden at the view `T`.  Then the point set is Rupert. -/
theorem isRupert_rd (V M : Finset ℝ³) {v m f gf gv S T N : ℝ³}
    {sm tm sf tf s1 t1 s2 t2 h : ℝ} (hF : IsFrame S T N)
    (hv : v ∈ V) (hm : m ∈ V) (hf : f ∈ V) (hgf : gf ∈ V) (hgv : gv ∈ V)
    (cm : ⟪m - v, S⟫ = sm ∧ ⟪m - v, T⟫ = tm ∧ ⟪m - v, N⟫ = 0)
    (cf : ⟪f - v, S⟫ = sf ∧ ⟪f - v, T⟫ = tf ∧ ⟪f - v, N⟫ = 0)
    (cgf : ⟪gf - v, S⟫ = s2 ∧ ⟪gf - v, T⟫ = t2 ∧ ⟪gf - v, N⟫ = -h)
    (cgv : ⟪gv - v, S⟫ = s1 ∧ ⟪gv - v, T⟫ = t1 ∧ ⟪gv - v, N⟫ = -h)
    (hh : 0 < h) (hsm : 0 < sm) (hmf : sm < sf) (h12 : s1 < s2)
    (htm : 0 < tm) (ht1 : 0 < t1) (htf : tf < 0) (ht2 : t2 < 0)
    (hH2 : (tf - tm) * (s2 - s1) < (t2 - t1) * (sf - sm))
    (hDv : 0 < s1 * t2 - s2 * t1)
    (hDf : (s2 - s1) * (tf - t1) < (t2 - t1) * (sf - s1))
    (hM : ∀ x ∈ M, ∃ p q : ℝ, x = v + p • (gv - v) + q • T ∧ q ≠ 0 ∧
      ((0 < p ∧ p < 1) ∨ (p = 0 ∧ q < 0)))
    (hrest : ∀ x ∈ V, x ∉ M → x = v ∨ x = m ∨ x = f ∨ x = gf ∨ x = gv ∨ RdHidden V T x) :
    IsRupert V := by
  classical
  set Φ : ℝ³ → ℝ³ := fun x => (orthoFrameMat S T N).toEuclideanLin (x - v) with hΦ
  have hΦx : ∀ x, Φ x = pt ⟪x - v, S⟫ ⟪x - v, T⟫ ⟪x - v, N⟫ := fun x => orthoFrameMat_apply _ _ _ _
  refine isRupert_of_frame_image V (v := v) hF ?_
  obtain ⟨hSS, hTT, hNN, hST, hSN, hTN⟩ := hF
  have mem : ∀ x ∈ V, Φ x ∈ V.image Φ := fun x hx => mem_image_of_mem _ hx
  have Φv : Φ v = pt 0 0 0 := by rw [hΦx]; simp
  have Φm : Φ m = pt sm tm 0 := by rw [hΦx, cm.1, cm.2.1, cm.2.2]
  have Φf : Φ f = pt sf tf 0 := by rw [hΦx, cf.1, cf.2.1, cf.2.2]
  have Φgf : Φ gf = pt s2 t2 (-h) := by rw [hΦx, cgf.1, cgf.2.1, cgf.2.2]
  have Φgv : Φ gv = pt s1 t1 (-h) := by rw [hΦx, cgv.1, cgv.2.1, cgv.2.2]
  refine isRupert_rd_std (V.image Φ) (M.image Φ) (Φv ▸ mem v hv) (Φm ▸ mem m hm)
    (Φf ▸ mem f hf) (Φgf ▸ mem gf hgf) (Φgv ▸ mem gv hgv) hh hsm hmf h12 htm ht1 htf ht2 hH2 hDv
    hDf ?_ ?_
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
    rcases hrest x hx hxM with rfl | rfl | rfl | rfl | rfl | hid
    · exact Or.inl Φv
    · exact Or.inr (Or.inl Φm)
    · exact Or.inr (Or.inr (Or.inl Φf))
    · exact Or.inr (Or.inr (Or.inr (Or.inl Φgf)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl Φgv))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (hid.frame ⟨hSS, hTT, hNN, hST, hSN, hTN⟩)))))

/-! ### The `R_d` conditions along an edge view, and the two type-08 closings -/

/-- **The `R_d` conditions** of A.10 for the five-corner rim `v m f g_f g_v` at the view
along `e` (the axle direction, depth along `e`): an orthonormal frame `S, T, N` with
`T = e / ‖e‖` and `N` normal to the face `F_j ∋ v, m, f`, in which the far edge
`g = [g_v, g_f]` is parallel to `F_j` (`ν = −h` at both ends) and (H1), (H2), (H4) hold
(as in `isRupert_rd_std`). -/
def RdRim (v m f gf gv e : ℝ³) : Prop :=
  ∃ (S N : ℝ³) (sm tm sf tf s1 t1 s2 t2 h : ℝ), IsFrame S (‖e‖⁻¹ • e) N ∧
    (⟪m - v, S⟫ = sm ∧ ⟪m - v, ‖e‖⁻¹ • e⟫ = tm ∧ ⟪m - v, N⟫ = 0) ∧
    (⟪f - v, S⟫ = sf ∧ ⟪f - v, ‖e‖⁻¹ • e⟫ = tf ∧ ⟪f - v, N⟫ = 0) ∧
    (⟪gf - v, S⟫ = s2 ∧ ⟪gf - v, ‖e‖⁻¹ • e⟫ = t2 ∧ ⟪gf - v, N⟫ = -h) ∧
    (⟪gv - v, S⟫ = s1 ∧ ⟪gv - v, ‖e‖⁻¹ • e⟫ = t1 ∧ ⟪gv - v, N⟫ = -h) ∧
    0 < h ∧ 0 < sm ∧ sm < sf ∧ s1 < s2 ∧ 0 < tm ∧ 0 < t1 ∧ tf < 0 ∧ t2 < 0 ∧
    (tf - tm) * (s2 - s1) < (t2 - t1) * (sf - sm) ∧ 0 < s1 * t2 - s2 * t1 ∧
    (s2 - s1) * (tf - t1) < (t2 - t1) * (sf - s1)

theorem RdHidden.smul {V : Finset ℝ³} {w x : ℝ³} {r : ℝ} (hr : 0 < r) (h : RdHidden V w x) :
    RdHidden V (r • w) x := by
  have hs : ∀ a b : ℝ³, det3 a b (r • w) = r * det3 a b w := by
    intro a b; simp only [det3_expand, PiLp.smul_apply, smul_eq_mul]; ring
  obtain ⟨a, ha, b, hb, c, hc, h0, h1, h2, h3⟩ := h
  exact ⟨a, ha, b, hb, c, hc, by rw [hs]; positivity, by rw [hs]; positivity,
    by rw [hs]; positivity, by rw [hs]; positivity⟩

/-- **Theorem R along an edge view** (`isRupert_rd` with the view `e` unnormalized): under
`RdRim`, with `F_k`'s middles at `v + p (g_v − v) + q e` and every other point strictly
hidden at `e`, the point set is Rupert. -/
theorem isRupert_of_rdRim (V M : Finset ℝ³) {v m f gf gv e : ℝ³} (hR : RdRim v m f gf gv e)
    (he : e ≠ 0) (hv : v ∈ V) (hm : m ∈ V) (hf : f ∈ V) (hgf : gf ∈ V) (hgv : gv ∈ V)
    (hM : ∀ x ∈ M, ∃ p q : ℝ, x = v + p • (gv - v) + q • e ∧ q ≠ 0 ∧
      ((0 < p ∧ p < 1) ∨ (p = 0 ∧ q < 0)))
    (hrest : ∀ x ∈ V, x ∉ M → x = v ∨ x = m ∨ x = f ∨ x = gf ∨ x = gv ∨ RdHidden V e x) :
    IsRupert V := by
  obtain ⟨S, N, sm, tm, sf, tf, s1, t1, s2, t2, h, hF, cm, cf, cgf, cgv, hh, hsm, hmf, h12, htm,
    ht1, htf, ht2, hH2, hDv, hDf⟩ := hR
  have hn : 0 < ‖e‖ := norm_pos_iff.mpr he
  have heT : e = ‖e‖ • (‖e‖⁻¹ • e) := by rw [smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
  refine isRupert_rd V M hF hv hm hf hgf hgv cm cf cgf cgv hh hsm hmf h12 htm ht1 htf ht2 hH2 hDv
    hDf ?_ ?_
  · intro x hx
    obtain ⟨p, q, hx, hq, hp⟩ := hM x hx
    refine ⟨p, q * ‖e‖, ?_, mul_ne_zero hq hn.ne', ?_⟩
    · rw [hx, mul_smul, ← heT]
    · rcases hp with hp | ⟨hp, hq'⟩
      · exact Or.inl hp
      · exact Or.inr ⟨hp, mul_neg_of_neg_of_pos hq' hn⟩
  · intro x hx hxM
    rcases hrest x hx hxM with h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h.smul (inv_pos.mpr hn))))))

/-- A triangle test of either orientation `ρ`: if the four tests all have the sign of `ρ`,
`x` is strictly hidden. -/
theorem rdHidden_of_sign {V : Finset ℝ³} {w x a b c : ℝ³} {ρ : ℝ} (ha : a ∈ V) (hb : b ∈ V)
    (hc : c ∈ V) (h0 : 0 < ρ * det3 (b - a) (c - a) w) (h1 : 0 < ρ * det3 (b - a) (x - a) w)
    (h2 : 0 < ρ * det3 (c - b) (x - b) w) (h3 : 0 < ρ * det3 (a - c) (x - c) w) :
    RdHidden V w x := by
  rcases lt_trichotomy ρ 0 with hρ | rfl | hρ
  · exact rdHidden_of_neg ha hb hc (neg_of_mul_pos_right h0 hρ.le)
      (neg_of_mul_pos_right h1 hρ.le) (neg_of_mul_pos_right h2 hρ.le)
      (neg_of_mul_pos_right h3 hρ.le)
  · simp at h0
  · exact ⟨a, ha, b, hb, c, hc, pos_of_mul_pos_right h0 hρ.le, pos_of_mul_pos_right h1 hρ.le,
      pos_of_mul_pos_right h2 hρ.le, pos_of_mul_pos_right h3 hρ.le⟩

/-- At a quad edge `x → y` of an octahedron (`x'` hidden in the quadrilateral `y p y' p'`
at the view along `y − x`), `x'` lies strictly inside one of the triangles `y p y'`,
`y y' p'` (off the diagonal `y y'`), `p y' p'`, `p p' y` (off the diagonal `p p'`), or, at
the crossing of the diagonals, `m y' p'` for a point `m` over the open side `(y, p)`. -/
theorem rdHidden_quad_edge {x x' y y' p p' m : ℝ³} (F : OctFacets x x' y y' p p')
    (hq₁ : F.a'b'c.f x < F.a'b'c.f y) (hq₂ : F.a'b'c'.f x < F.a'b'c'.f y) {V : Finset ℝ³}
    (hy : y ∈ V) (hy' : y' ∈ V) (hp : p ∈ V) (hp' : p' ∈ V) (hm : m ∈ V)
    (hmid : ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ m = y + s • (p - y) + δ • (y - x)) :
    RdHidden V (y - x) x' := by
  obtain ⟨E1, E2, E3, E4⟩ := quad_edge_tests_or F hq₁ hq₂
  set ρ := det3 (p - y) (p' - y) (y - x)
  have hnd := F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨hxx', hxy, hxy', hxp, hxp'⟩, ⟨hx'y, hx'y', hx'p, hx'p'⟩, ⟨hyy', hyp, hyp'⟩,
    ⟨hy'p, hy'p'⟩, hpp', -⟩ := hnd
  have mx' : x' ∈ ({x, x', y, y', p, p'} : Finset ℝ³) := by simp
  have my : y ∈ ({x, x', y, y', p, p'} : Finset ℝ³) := by simp
  have my' : y' ∈ ({x, x', y, y', p, p'} : Finset ℝ³) := by simp
  have mp : p ∈ ({x, x', y, y', p, p'} : Finset ℝ³) := by simp
  have mp' : p' ∈ ({x, x', y, y', p, p'} : Finset ℝ³) := by simp
  have e1x := E1 x' mx' hx'y hx'p (Ne.symm hxx')
  have e2x := E2 x' mx' hx'p hx'y'
  have e3x := E3 x' mx' hx'y' hx'p'
  have e4x := E4 x' mx' hx'p' hx'y (Ne.symm hxx')
  have e1y' := E1 y' my' (Ne.symm hyy') hy'p (Ne.symm hxy')
  have e2p' := E2 p' mp' (Ne.symm hpp') (Ne.symm hy'p')
  have e3y := E3 y my hyy' hyp'
  have e4p := E4 p mp hpp' (Ne.symm hyp) (Ne.symm hxp)
  have r1 : ∀ a b c : ℝ³, det3 (b - a) (c - a) (y - x) = det3 (c - b) (a - b) (y - x) := by
    intro a b c; simp only [det3_expand, PiLp.sub_apply]; ring
  have r2 : ∀ a b c : ℝ³, det3 (a - b) (c - b) (y - x) = -det3 (b - a) (c - a) (y - x) := by
    intro a b c; simp only [det3_expand, PiLp.sub_apply]; ring
  by_cases hD1 : det3 (y' - y) (x' - y) (y - x) = 0
  · by_cases hD2 : det3 (p' - p) (x' - p) (y - x) = 0
    · -- the crossing of the diagonals: strictly inside `m y' p'`
      obtain ⟨s, δ, hs0, hs1, rfl⟩ := hmid
      have hs1' : 0 < 1 - s := by linarith
      have g0 : det3 (y' - (y + s • (p - y) + δ • (y - x))) (p' - (y + s • (p - y) + δ • (y - x)))
          (y - x) = (1 - s) * det3 (p' - y') (y - y') (y - x) +
            s * det3 (y' - p) (p' - p) (y - x) := by
        simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
        ring
      have g1 : det3 (y' - (y + s • (p - y) + δ • (y - x))) (x' - (y + s • (p - y) + δ • (y - x)))
          (y - x) = (1 - s) * det3 (y' - y) (x' - y) (y - x) +
            s * det3 (y' - p) (x' - p) (y - x) := by
        simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
        ring
      have g3 : det3 (y + s • (p - y) + δ • (y - x) - p') (x' - p') (y - x) =
          (1 - s) * det3 (y - p') (x' - p') (y - x) - s * det3 (p' - p) (x' - p) (y - x) := by
        simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
        ring
      refine rdHidden_of_sign (ρ := ρ) hm hy' hp' ?_ ?_ e3x ?_
      · rw [g0, mul_add, mul_left_comm, mul_left_comm ρ s]
        exact add_pos (mul_pos hs1' e3y) (mul_pos hs0 e2p')
      · rw [g1, hD1, mul_zero, zero_add, mul_left_comm]; exact mul_pos hs0 e2x
      · rw [g3, hD2, mul_zero, sub_zero, mul_left_comm]; exact mul_pos hs1' e4x
    · rcases lt_or_gt_of_ne (mul_ne_zero (quad_orient_ne F) hD2) with hs | hs
      · -- strictly inside `p y' p'`
        refine rdHidden_of_sign hp hy' hp' e2p' e2x e3x ?_
        rw [r2 p p' x']; linarith
      · -- strictly inside `p p' y`
        refine rdHidden_of_sign hp hp' hy ?_ hs e4x e1x
        rw [r1 p p' y]; exact e4p
  · rcases lt_or_gt_of_ne (mul_ne_zero (quad_orient_ne F) hD1) with hs | hs
    · -- strictly inside `y p y'`
      refine rdHidden_of_sign hy hp hy' e1y' e1x e2x ?_
      rw [r2 y y' x']; linarith
    · -- strictly inside `y y' p'`
      refine rdHidden_of_sign hy hy' hp' ?_ hs e3x e4x
      rw [r1 y y' p']; exact e3y

/-- **Theorem R for `K_y` (N2–`K_c`).**  At a quad edge `x → y` of an octahedron (`x'`
hidden) with one more point `m` over the chord from `y` to `p` (case N2 of Theorem 10.1,
with `x, x', y, y', p, p', m = a', a, c, c', b, b', 2`): if the five-corner rim
`y m p y' p'` of Lemma H satisfies the `R_d` conditions at the view along `y − x`
(`RdRim`), the seven points are Rupert (along the circle of the face `x y p'`, whose
middle is `x`). -/
theorem isRupert_quad_edge_middle_rd {x x' y y' p p' m : ℝ³} (F : OctFacets x x' y y' p p')
    (hq₁ : F.a'b'c.f x < F.a'b'c.f y) (hq₂ : F.a'b'c'.f x < F.a'b'c'.f y)
    (hmid : ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ m = y + s • (p - y) + δ • (y - x))
    (hR : RdRim y m p y' p' (y - x)) :
    IsRupert (insert m {x, x', y, y', p, p'}) := by
  classical
  have hnd := F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨-, hxy, -⟩, -⟩ := hnd
  have hV : ∀ z, z ∈ ({x, x', y, y', p, p'} : Finset ℝ³) → z ∈ insert m {x, x', y, y', p, p'} :=
    fun z hz => mem_insert_of_mem hz
  refine isRupert_of_rdRim _ {x} hR (sub_ne_zero.mpr (Ne.symm hxy)) (hV y (by simp))
    (mem_insert_self _ _) (hV p (by simp)) (hV y' (by simp)) (hV p' (by simp)) ?_ ?_
  · intro z hz
    rw [mem_singleton.mp hz]
    exact ⟨0, -1, by module, by norm_num, Or.inr ⟨rfl, by norm_num⟩⟩
  · intro z hz hzM
    simp only [mem_insert, mem_singleton] at hz hzM
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inr (Or.inl rfl)
    · exact absurd rfl hzM
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (rdHidden_quad_edge F hq₁ hq₂ (hV y (by simp)) (hV y' (by simp)) (hV p (by simp))
          (hV p' (by simp)) (mem_insert_self _ _) hmid)))))
    · exact Or.inl rfl
    · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))

/-- **Theorem R for `K_b` (T4).**  In the frame `d; a, c, b` with
`c' = d + α₁ (a − d) + β₁ (b − d)` (`α₁ > 1`: the far end of `Q_ab` along `d b` is `c'`;
`β₁ > 0`): if the five-corner rim `b a' c b' c'` of Lemma H satisfies the `R_d` conditions
at the view along `b − d` (`RdRim`), `K` is Rupert (along the circle of `Q_ab`, whose
middles `d` and `a` lie over its side `[c', b]`). -/
theorem isRupert_t4b_rd {a a' b b' c c' d : ℝ³} {α₁ β₁ : ℝ}
    (hc' : c' = d + α₁ • (a - d) + β₁ • (b - d)) (hα₁ : 1 < α₁) (hβ₁ : 0 < β₁) (hbd : b ≠ d)
    (hR : RdRim b a' c b' c' (b - d)) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  classical
  have hα₁0 : α₁ ≠ 0 := by positivity
  refine isRupert_of_rdRim _ {d, a} hR (sub_ne_zero.mpr hbd) (by simp) (by simp) (by simp)
    (by simp) (by simp) ?_ ?_
  · intro z hz
    simp only [mem_insert, mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact ⟨0, -1, by module, by norm_num, Or.inr ⟨rfl, by norm_num⟩⟩
    · refine ⟨1 / α₁, (1 - β₁ - α₁) / α₁, ?_, ?_, Or.inl ⟨by positivity, ?_⟩⟩
      · rw [hc']
        ext i
        simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
        field_simp
        ring
      · exact div_ne_zero (by linarith) hα₁0
      · rw [div_lt_one (by linarith)]; exact hα₁
  · intro z hz hzM
    simp only [mem_insert, mem_singleton, not_or] at hz hzM
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl hzM.1
    · exact absurd rfl hzM.2
    · exact Or.inr (Or.inl rfl)
    · exact Or.inl rfl
    · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))

end Minimality

end
