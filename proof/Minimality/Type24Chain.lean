module

public import Minimality.Type24Metric

@[expose] public section

/-!
# Type 24 at every metric: the window chain (§20.3–20.5) and a uniform statement (20.9)

`FEWER-FACES-PROOFS.md` §20 (refereed 2026-10-22), at `K`'s own metric (the depth at a view `d`
is `⟪·, d⟫`).  Arc 2 is the arc `d(t) = e_a + t e_b` of the cap face `1 0 2` (`wpView x 2 t`),
WP_2 asks `z6 < z4 < z0 < z2` there (`WPChain x 2 6 4 t`); arc 6 is the mirror (`2 ↔ 6`,
`4 ↔ 5`, `b ↔ c`).  Everything is stated once for a general arc `b` with the other axis `c`
and the WP corner `q` (oblique coordinates `Xa, Xb, Xc` in the frame `x 1; e_a, e_b, e_c`).

* **Lemma 20.3 (WP at the view `t3`)** (`wpChain_after`): if `z0 = z2` at the view `t3 ≥ 0`,
  `g_b > h_ab`, `u_c(t3) ≤ 0`, `a4 + b4 < 1` and (L) (`c4 ≤ 1`, or `z4 > z6` at `t3`), then WP_2's
  depth chain holds at every view `t ∈ (t3, t3 + ε)`.  (At `t3`, `z0 = z2 = w > 0` since
  `(1 + t3) w = ⟪d, d⟫`.)  `t3 = (g_a − h_ab)/(g_b − h_ab)` (`wpView_t3`); Rupert form
  `isRupert_wp2_after` (`t3 ∈ [lo_f, hi_f)`).
* **Theorem 20.4 (the window chain)** (`windowChain`): two circle-2 tests `τ_h`, `τ_l` at the
  views `t_h`, `t_l ∈ [lo, hi]`, with the X-only hypotheses (H_h) (every failure pattern of
  `τ_h` forces `u_b ≥ u_a` on `U(t_h) = {u_c ≤ 0, u_a + t_h u_b > 0}`, `CovFails`) and (H_l);
  under (S) (`u_c ≤ 0` at both views, `g_b > h_ab`) and (L) or (H⁺), either a test does not fail
  or WP_2's chain holds just above `t3 ∈ [lo, hi)`, off the hyperplanes `z0 = z2` at `t_h`,
  `z4 = z6` at `t_l`, `t_h`.  The proof is Cramer-free: `ℓ3 = z2 − z0` is increasing in `t`, so
  `t_l ≤ t3 < t_h`, and `u_c`, `ℓ1` are linear in `t`.
* **Rupert forms** (`WindowChain`: the data of 20.4 on one arc, X-only except for the ties and
  the certificates of the two tests and of WP; `isRupert_windowChain2`, `isRupert_windowChain6`):
  under (S), `K` is Rupert.  **Corollary 20.5** (`isRupert_windowChain_octant`): on the closed
  obtuse octant `c_ab, c_ac, c_bc ≤ 0`, (S) holds at all lengths.
* **Theorem 20.9 (a uniform statement)** (`isRupert_type24_uniform`): two acute-safe cap edges
  (`Type24.TwoSafe`, Theorem 20.8) and the window chain on arc 2 or arc 6 make `K` Rupert at
  `K`'s own metric, whatever its angles and lengths (off the ties and HDNs carried by the data).

Not formalized: Proposition 20.7 (the per-class LP certificates) and the class counts; that `B`'s
rim is `(6, 4, 0, 2, 3)` on `(lo_f, hi_f)` is part of the data (`WPItem` off a finite set of
views), as in `isRupert_m1_corner_wp`.
-/

namespace Minimality

open Finset
open scoped RealInnerProductSpace

/-! ### Linear functions of the arc parameter -/

/-- A linear function positive at `0` stays positive on `[0, ε)`. -/
theorem exists_pos_near {f0 B : ℝ} (h : 0 < f0) :
    ∃ ε > 0, ∀ s, 0 ≤ s → s < ε → 0 < f0 + s * B := by
  have hB : 0 < |B| + 1 := by positivity
  refine ⟨f0 / (|B| + 1), div_pos h hB, fun s hs hsε => ?_⟩
  rw [lt_div_iff₀ hB] at hsε
  have := neg_abs_le B
  nlinarith [mul_le_mul_of_nonneg_left this hs]

/-- Linear interpolation: a linear function `≥ 0` at `t1` and `t2` is `≥ 0` between them. -/
theorem lin_nonneg_between {P Q t1 t2 s : ℝ} (h1 : t1 ≤ s) (h2 : s < t2)
    (hp1 : 0 ≤ P + t1 * Q) (hp2 : 0 ≤ P + t2 * Q) : 0 ≤ P + s * Q := by
  have e : (t2 - t1) * (P + s * Q) = (t2 - s) * (P + t1 * Q) + (s - t1) * (P + t2 * Q) := by ring
  have : 0 ≤ (t2 - t1) * (P + s * Q) := by
    rw [e]; exact add_nonneg (mul_nonneg (by linarith) hp1) (mul_nonneg (by linarith) hp2)
  by_contra hn; push Not at hn
  have := mul_neg_of_pos_of_neg (show 0 < t2 - t1 by linarith) hn
  linarith

/-- Linear interpolation, strict. -/
theorem lin_pos_between {P Q t1 t2 s : ℝ} (h1 : t1 ≤ s) (h2 : s < t2)
    (hp1 : 0 < P + t1 * Q) (hp2 : 0 < P + t2 * Q) : 0 < P + s * Q := by
  have e : (t2 - t1) * (P + s * Q) = (t2 - s) * (P + t1 * Q) + (s - t1) * (P + t2 * Q) := by ring
  have : 0 < (t2 - t1) * (P + s * Q) := by
    rw [e]; exact add_pos_of_pos_of_nonneg (mul_pos (by linarith) hp1)
      (mul_nonneg (by linarith) hp2.le)
  by_contra hn; push Not at hn
  have := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ t2 - t1 by linarith) hn
  linarith

/-! ### Lemma 20.3: WP at the view `t3` -/

/-- The depth along the arc is linear in `t`. -/
theorem inner_wpView (x : Fin 7 → ℝ³) (b : Fin 7) (v : ℝ³) (t : ℝ) :
    ⟪v, wpView x b t⟫ = ⟪v, x 0 - x 1⟫ + t * ⟪v, x b - x 1⟫ := by
  simp only [wpView, inner_add_right, real_inner_smul_right]

theorem inner_wpView_sub (x : Fin 7 → ℝ³) (b : Fin 7) (v : ℝ³) (t s : ℝ) :
    ⟪v, wpView x b t⟫ = ⟪v, wpView x b s⟫ + (t - s) * ⟪v, x b - x 1⟫ := by
  rw [inner_wpView, inner_wpView]; ring

/-- `⟪d, d⟫ = u_a + t u_b` on the arc. -/
theorem wpView_self (x : Fin 7 → ℝ³) (b : Fin 7) (t : ℝ) :
    ⟪wpView x b t, wpView x b t⟫ =
      ⟪x 0 - x 1, wpView x b t⟫ + t * ⟪x b - x 1, wpView x b t⟫ := by
  simp only [wpView, inner_add_left, real_inner_smul_left]

/-- **Lemma 20.3 (WP at the view `t3`), every metric.**  On the arc `e_a + t e_b` of the cap face
`1 0 b`, let `x q = x 1 + a e_a + b' e_b + c e_c` with `a, b', c > 0` and `a + b' < 1` (`r4 > 1`).
If at a view `t3 ≥ 0` the depths of `0` and `b` agree, `h_ab < g_b`, `u_c(t3) = ⟪e_c, d(t3)⟫ ≤ 0`
(`z_c ≤ z_1`), and (L) `c ≤ 1` or `z_c < z_q` at `t3`, then WP's depth chain
`z_c < z_q < z_0 < z_b` holds at every view `t ∈ (t3, t3 + ε)`. -/
theorem wpChain_after {x : Fin 7 → ℝ³} {b c q : Fin 7} (hd : ∀ t, wpView x b t ≠ 0)
    {aq bq cq : ℝ} (hq : x q = x 1 + aq • (x 0 - x 1) + bq • (x b - x 1) + cq • (x c - x 1))
    (haq : 0 < aq) (hbq : 0 < bq) (hcq : 0 < cq) (hr : aq + bq < 1)
    {t3 : ℝ} (ht3 : 0 ≤ t3) (h02 : ⟪x 0, wpView x b t3⟫ = ⟪x b, wpView x b t3⟫)
    (hslope : ⟪x 0 - x 1, x b - x 1⟫ < ⟪x b - x 1, x b - x 1⟫)
    (huc : ⟪x c - x 1, wpView x b t3⟫ ≤ 0)
    (hL : cq ≤ 1 ∨ ⟪x c, wpView x b t3⟫ < ⟪x q, wpView x b t3⟫) :
    ∃ ε > 0, ∀ t, t3 < t → t < t3 + ε → WPChain x b c q t := by
  set d := wpView x b t3 with hd3
  set Ua := ⟪x 0 - x 1, d⟫
  set Ub := ⟪x b - x 1, d⟫
  set Uc := ⟪x c - x 1, d⟫
  have e0 : ⟪x 0, d⟫ = ⟪x 1, d⟫ + Ua := by simp only [Ua, inner_sub_left]; ring
  have eb : ⟪x b, d⟫ = ⟪x 1, d⟫ + Ub := by simp only [Ub, inner_sub_left]; ring
  have ec : ⟪x c, d⟫ = ⟪x 1, d⟫ + Uc := by simp only [Uc, inner_sub_left]; ring
  have eq : ⟪x q, d⟫ = ⟪x 1, d⟫ + aq * Ua + bq * Ub + cq * Uc := by
    rw [hq]; simp only [inner_add_left, real_inner_smul_left]; rfl
  have hab : Ua = Ub := by linarith
  have hdd : 0 < Ua + t3 * Ub := by
    rw [← wpView_self]; exact real_inner_self_pos.mpr (hd t3)
  have hUa : 0 < Ua := by
    rw [← hab] at hdd; nlinarith
  -- `ℓ2(t3) = z0 − zq > 0`, `ℓ1(t3) = zq − zc > 0`
  have l2 : 0 < ⟪x 0, d⟫ - ⟪x q, d⟫ := by
    rw [e0, eq, ← hab]; nlinarith [mul_nonneg hcq.le (neg_nonneg.mpr huc)]
  have l1 : 0 < ⟪x q, d⟫ - ⟪x c, d⟫ := by
    rcases hL with hL | hL
    · rw [eq, ec, ← hab]
      nlinarith [mul_nonneg (sub_nonneg.mpr hL) (neg_nonneg.mpr huc)]
    · linarith
  obtain ⟨ε1, hε1, k1⟩ := exists_pos_near (B := ⟪x q, x b - x 1⟫ - ⟪x c, x b - x 1⟫) l1
  obtain ⟨ε2, hε2, k2⟩ := exists_pos_near (B := ⟪x 0, x b - x 1⟫ - ⟪x q, x b - x 1⟫) l2
  refine ⟨min ε1 ε2, lt_min hε1 hε2, fun t ht1 ht2 => ?_⟩
  have hs : 0 ≤ t - t3 := by linarith
  have hs1 : t - t3 < ε1 := by linarith [min_le_left ε1 ε2]
  have hs2 : t - t3 < ε2 := by linarith [min_le_right ε1 ε2]
  have m1 := k1 (t - t3) hs hs1
  have m2 := k2 (t - t3) hs hs2
  have lin := fun v => inner_wpView_sub x b (x v) t t3
  have hb0 : ⟪x b, x b - x 1⟫ - ⟪x 0, x b - x 1⟫ =
      ⟪x b - x 1, x b - x 1⟫ - ⟪x 0 - x 1, x b - x 1⟫ := by
    simp only [inner_sub_left]; ring
  refine ⟨?_, ?_, ?_⟩
  · rw [lin c, lin q]; nlinarith
  · rw [lin q, lin 0]; nlinarith
  · rw [lin 0, lin b, ← hd3]
    have : 0 < (t - t3) * (⟪x b - x 1, x b - x 1⟫ - ⟪x 0 - x 1, x b - x 1⟫) :=
      mul_pos (by linarith) (by linarith)
    nlinarith

/-- **The view `t3` of circle `b` perpendicular to the edge `0 b`**:
`t3 = (g_a − h_ab)/(g_b − h_ab)` has `z0 = z_b` (at the corner `t3 = g_a / g_b = 1/κ`). -/
theorem wpView_t3 (x : Fin 7 → ℝ³) (b : Fin 7)
    (hslope : ⟪x 0 - x 1, x b - x 1⟫ < ⟪x b - x 1, x b - x 1⟫) :
    ⟪x 0, wpView x b ((⟪x 0 - x 1, x 0 - x 1⟫ - ⟪x 0 - x 1, x b - x 1⟫) /
        (⟪x b - x 1, x b - x 1⟫ - ⟪x 0 - x 1, x b - x 1⟫))⟫ =
      ⟪x b, wpView x b ((⟪x 0 - x 1, x 0 - x 1⟫ - ⟪x 0 - x 1, x b - x 1⟫) /
        (⟪x b - x 1, x b - x 1⟫ - ⟪x 0 - x 1, x b - x 1⟫))⟫ := by
  have hB : ⟪x b - x 1, x b - x 1⟫ - ⟪x 0 - x 1, x b - x 1⟫ ≠ 0 := by linarith
  have hc := real_inner_comm (x 0 - x 1) (x b - x 1)
  have e : ∀ w : ℝ³, ⟪x b, w⟫ - ⟪x 0, w⟫ = ⟪x b - x 1, w⟫ - ⟪x 0 - x 1, w⟫ := by
    intro w; simp only [inner_sub_left]; ring
  rw [← sub_eq_zero, ← neg_sub, e, inner_wpView, inner_wpView, hc]
  field_simp
  ring

/-- **Lemma 20.3 on arc 2, Rupert form.**  If `B`'s rim is WP_2's pentagon on `(lo, hi)` (off
a finite set `S` of views), `z0 = z2` at a view `t3 ∈ [lo, hi)`, `lo ≥ 0`, `h_ab < g_b`,
`u_c(t3) ≤ 0`, `a4 + b4 < 1` and (L), then `K` is Rupert. -/
theorem isRupert_wp2_after {x : Fin 7 → ℝ³} (T : Type24 x) {lo hi t3 : ℝ} (hlo : 0 ≤ lo)
    (hl3 : lo ≤ t3) (h3h : t3 < hi) (S : Finset ℝ)
    (hWP : ∀ t, lo < t → t < hi → t ∉ S → WPItem x 2 6 4 5 t)
    (h02 : ⟪x 0, wpView x 2 t3⟫ = ⟪x 2, wpView x 2 t3⟫)
    (hslope : ⟪x 0 - x 1, x 2 - x 1⟫ < ⟪x 2 - x 1, x 2 - x 1⟫)
    (huc : ⟪x 6 - x 1, wpView x 2 t3⟫ ≤ 0) (hr : oblX0 x 4 + oblX2 x 4 < 1)
    (hL : oblX6 x 4 ≤ 1 ∨ ⟪x 6, wpView x 2 t3⟫ < ⟪x 4, wpView x 2 t3⟫) :
    IsRupert (univ.image x) := by
  have hd : ∀ t, wpView x 2 t ≠ 0 := by
    intro t h
    have e : x 0 - x 1 = -t • (x 2 - x 1) := by
      rw [neg_smul, eq_neg_iff_add_eq_zero]; exact h
    apply T.det_ne
    rw [det24, e]
    simp only [vol3, PiLp.smul_apply, smul_eq_mul]; ring
  obtain ⟨ε, hε, hch⟩ := wpChain_after hd (T.rep 4) (T.X0_pos (by decide)) (T.X2_pos (by decide))
    (T.X6_pos (by decide)) hr (by linarith) h02 hslope huc hL
  have hlt : t3 < min (t3 + ε) hi := lt_min (by linarith) h3h
  obtain ⟨t, ⟨ht1, ht2⟩, htS⟩ := ((Set.Ioo_infinite hlt).sdiff S.finite_toSet).nonempty
  have ht2' := lt_of_lt_of_le ht2 (min_le_left _ _)
  have ht2'' := lt_of_lt_of_le ht2 (min_le_right _ _)
  exact isRupert_wp2 T (by linarith) (hWP t (by linarith) ht2'' htS) (hch t ht1 ht2')

/-! ### Theorem 20.4: the window chain -/

/-- **Theorem 20.4 (the window chain), every metric.**  In the frame `x 1; e_a, e_b, e_c`
(oblique coordinates `Xa, Xb, Xc`), let `x q` have coordinates `a, b', c > 0` with `a + b' < 1`.
Let `τ_h` (rim diagonals `{yh, ch}`, `{ah, bh}`) and `τ_l` be crossing tests at the arc views
`t_h`, `t_l ∈ [lo, hi]`, `lo ≥ 0`, such that, X-only, on `U(t) = {u_c ≤ 0, u_a + t u_b > 0}`
- (H_h) every failure pattern of `τ_h` forces `u_a ≤ u_b` on `U(t_h)`,
- (H_l) every failure pattern of `τ_l` forces `u_b ≤ u_a` on `U(t_l)`.

Suppose (S) `u_c ≤ 0` at both views and `h_ab < g_b`, and (L) `c ≤ 1`, or `z_c < z_q` wherever
`z_0 = z_b` on the arc, or (H⁺) every failure pattern of `τ_h` (of `τ_l`) forces `z_q ≥ z_c` on
`U(t_h)` (on `U(t_l)`).  Then, off the hyperplanes `z0 = z_b` at `t_h` and `z_q = z_c` at
`t_l`, `t_h`: `τ_h` does not fail, or `τ_l` does not fail, or WP's depth chain holds on an
interval `(t3, t3 + ε)` with `lo ≤ t3 < hi`. -/
theorem windowChain {x : Fin 7 → ℝ³} {b c q : Fin 7} (hd : ∀ t, wpView x b t ≠ 0)
    {Xa Xb Xc : Fin 7 → ℝ}
    (hrep : ∀ v, x v = x 1 + Xa v • (x 0 - x 1) + Xb v • (x b - x 1) + Xc v • (x c - x 1))
    (haq : 0 < Xa q) (hbq : 0 < Xb q) (hcq : 0 < Xc q) (hr : Xa q + Xb q < 1)
    {lo hi tl th : ℝ} (hlo : 0 ≤ lo) (hlol : lo ≤ tl) (hhi : th ≤ hi)
    {yh ah ch bh yl al cl bl : Fin 7}
    (Hh : ∀ ua ub uc : ℝ, uc ≤ 0 → 0 < ua + th * ub → CovFails Xa Xb Xc ua ub uc yh ch ah bh →
      ua ≤ ub)
    (Hl : ∀ ua ub uc : ℝ, uc ≤ 0 → 0 < ua + tl * ub → CovFails Xa Xb Xc ua ub uc yl cl al bl →
      ub ≤ ua)
    (hSl : ⟪x c - x 1, wpView x b tl⟫ ≤ 0) (hSh : ⟪x c - x 1, wpView x b th⟫ ≤ 0)
    (hslope : ⟪x 0 - x 1, x b - x 1⟫ < ⟪x b - x 1, x b - x 1⟫)
    (hL : Xc q ≤ 1 ∨
      (∀ t, ⟪x 0, wpView x b t⟫ = ⟪x b, wpView x b t⟫ → ⟪x c, wpView x b t⟫ < ⟪x q, wpView x b t⟫) ∨
      ((∀ ua ub uc : ℝ, uc ≤ 0 → 0 < ua + th * ub → CovFails Xa Xb Xc ua ub uc yh ch ah bh →
          uc ≤ covDepth Xa Xb Xc ua ub uc q) ∧
        (∀ ua ub uc : ℝ, uc ≤ 0 → 0 < ua + tl * ub → CovFails Xa Xb Xc ua ub uc yl cl al bl →
          uc ≤ covDepth Xa Xb Xc ua ub uc q)))
    (n0b : ⟪x 0, wpView x b th⟫ ≠ ⟪x b, wpView x b th⟫)
    (nqh : ⟪x c, wpView x b th⟫ ≠ ⟪x q, wpView x b th⟫)
    (nql : ⟪x c, wpView x b tl⟫ ≠ ⟪x q, wpView x b tl⟫) :
    ¬ Fails4 (x yh) (x ch) (x ah) (x bh) (wpView x b th) ∨
      ¬ Fails4 (x yl) (x cl) (x al) (x bl) (wpView x b tl) ∨
      ∃ t3, lo ≤ t3 ∧ t3 < hi ∧ ∃ ε > 0, ∀ t, t3 < t → t < t3 + ε → WPChain x b c q t := by
  by_cases hFh : Fails4 (x yh) (x ch) (x ah) (x bh) (wpView x b th)
  swap; · exact Or.inl hFh
  by_cases hFl : Fails4 (x yl) (x cl) (x al) (x bl) (wpView x b tl)
  swap; · exact Or.inr (Or.inl hFl)
  right; right
  have covh := (fails4_iff_covFails hrep _ _ _ _ _).mp hFh
  have covl := (fails4_iff_covFails hrep _ _ _ _ _).mp hFl
  have posh : 0 < ⟪x 0 - x 1, wpView x b th⟫ + th * ⟪x b - x 1, wpView x b th⟫ := by
    rw [← wpView_self]; exact real_inner_self_pos.mpr (hd th)
  have posl : 0 < ⟪x 0 - x 1, wpView x b tl⟫ + tl * ⟪x b - x 1, wpView x b tl⟫ := by
    rw [← wpView_self]; exact real_inner_self_pos.mpr (hd tl)
  have l3h := Hh _ _ _ hSh posh covh
  have l3l := Hl _ _ _ hSl posl covl
  -- `ℓ3(t) = u_b − u_a = A + t B` with `B = g_b − h_ab > 0`
  have sub1 : ∀ (v : Fin 7) (t : ℝ), ⟪x v - x 1, wpView x b t⟫ =
      ⟪x v, wpView x b t⟫ - ⟪x 1, wpView x b t⟫ := fun v t => inner_sub_left _ _ _
  set A := ⟪x b - x 1, x 0 - x 1⟫ - ⟪x 0 - x 1, x 0 - x 1⟫ with hA
  set B := ⟪x b - x 1, x b - x 1⟫ - ⟪x 0 - x 1, x b - x 1⟫ with hB
  have hBpos : 0 < B := by simp only [B]; linarith
  have l3 : ∀ t, ⟪x b - x 1, wpView x b t⟫ - ⟪x 0 - x 1, wpView x b t⟫ = A + t * B := by
    intro t
    have hc := real_inner_comm (x 0 - x 1) (x b - x 1)
    rw [inner_wpView, inner_wpView]; simp only [A, B]; rw [hc]; ring
  have l3h' : 0 < A + th * B := by
    rw [← l3]
    have : ⟪x 0 - x 1, wpView x b th⟫ ≠ ⟪x b - x 1, wpView x b th⟫ := by
      rw [sub1, sub1]; intro e; exact n0b (by linarith)
    exact sub_pos.mpr (lt_of_le_of_ne l3h this)
  have l3l' : A + tl * B ≤ 0 := by rw [← l3]; linarith
  set t3 := -A / B with ht3
  have h3 : A + t3 * B = 0 := by rw [ht3, div_mul_cancel₀ _ hBpos.ne']; ring
  have htl3 : tl ≤ t3 := by nlinarith
  have ht3h : t3 < th := by nlinarith
  refine ⟨t3, by linarith, by linarith, ?_⟩
  -- the hypotheses of Lemma 20.3 at `t3`
  have h02 : ⟪x 0, wpView x b t3⟫ = ⟪x b, wpView x b t3⟫ := by
    have := l3 t3; rw [h3, sub1, sub1] at this; linarith
  have huc : ⟪x c - x 1, wpView x b t3⟫ ≤ 0 := by
    have k := lin_nonneg_between (P := -⟪x c - x 1, x 0 - x 1⟫) (Q := -⟪x c - x 1, x b - x 1⟫)
      htl3 ht3h (by rw [inner_wpView] at hSl; linarith) (by rw [inner_wpView] at hSh; linarith)
    rw [inner_wpView]; linarith
  have hq := hrep q
  have hL' : Xc q ≤ 1 ∨ ⟪x c, wpView x b t3⟫ < ⟪x q, wpView x b t3⟫ := by
    rcases hL with hL | hL | ⟨Ph, Pl⟩
    · exact Or.inl hL
    · exact Or.inr (hL t3 h02)
    · right
      have dq : ∀ t, covDepth Xa Xb Xc ⟪x 0 - x 1, wpView x b t⟫ ⟪x b - x 1, wpView x b t⟫
          ⟪x c - x 1, wpView x b t⟫ q = ⟪x q, wpView x b t⟫ - ⟪x 1, wpView x b t⟫ := by
        intro t; rw [inner_covDepth hrep (wpView x b t) q]; ring
      have ph := Ph _ _ _ hSh posh covh
      have pl := Pl _ _ _ hSl posl covl
      rw [dq, sub1] at ph pl
      have ph' : 0 < ⟪x q, wpView x b th⟫ - ⟪x c, wpView x b th⟫ :=
        sub_pos.mpr (lt_of_le_of_ne (by linarith) nqh)
      have pl' : 0 < ⟪x q, wpView x b tl⟫ - ⟪x c, wpView x b tl⟫ :=
        sub_pos.mpr (lt_of_le_of_ne (by linarith) nql)
      rw [inner_wpView, inner_wpView] at ph' pl'
      have k := lin_pos_between (P := ⟪x q, x 0 - x 1⟫ - ⟪x c, x 0 - x 1⟫)
        (Q := ⟪x q, x b - x 1⟫ - ⟪x c, x b - x 1⟫) htl3 ht3h (by linarith) (by linarith)
      rw [inner_wpView, inner_wpView]; linarith
  exact wpChain_after hd hq haq hbq hcq hr (by linarith) h02 hslope huc hL'

/-! ### Rupert forms -/

/-- **The data of the window chain (Theorem 20.4) on one arc**: the face interval `[lo, hi]`
(`lo ≥ 0`) on which `B`'s rim is WP's pentagon (`WPItem`, off a finite set `S` of views), the
tests `τ_h`, `τ_l` at views `t_l, t_h ∈ [lo, hi]` with the rims `(yh, ah, ch, bh)`,
`(yl, al, cl, bl)` certified up to their depth patterns (`QuadTest'`), the X-only hypotheses
(H_h), (H_l), `a + b' < 1` and `c ≤ 1` or (H⁺), and the three ties excluded. -/
structure WindowChain (x : Fin 7 → ℝ³) (b c q i : Fin 7) (Xa Xb Xc : Fin 7 → ℝ) where
  lo : ℝ
  hi : ℝ
  tl : ℝ
  th : ℝ
  yh : Fin 7
  ah : Fin 7
  ch : Fin 7
  bh : Fin 7
  yl : Fin 7
  al : Fin 7
  cl : Fin 7
  bl : Fin 7
  S : Finset ℝ
  hlo : 0 ≤ lo
  hlol : lo ≤ tl
  hloh : lo ≤ th
  hhi : th ≤ hi
  hr : Xa q + Xb q < 1
  Hh : ∀ ua ub uc : ℝ, uc ≤ 0 → 0 < ua + th * ub → CovFails Xa Xb Xc ua ub uc yh ch ah bh →
    ua ≤ ub
  Hl : ∀ ua ub uc : ℝ, uc ≤ 0 → 0 < ua + tl * ub → CovFails Xa Xb Xc ua ub uc yl cl al bl →
    ub ≤ ua
  hL : Xc q ≤ 1 ∨
    ((∀ ua ub uc : ℝ, uc ≤ 0 → 0 < ua + th * ub → CovFails Xa Xb Xc ua ub uc yh ch ah bh →
        uc ≤ covDepth Xa Xb Xc ua ub uc q) ∧
      (∀ ua ub uc : ℝ, uc ≤ 0 → 0 < ua + tl * ub → CovFails Xa Xb Xc ua ub uc yl cl al bl →
        uc ≤ covDepth Xa Xb Xc ua ub uc q))
  testH : QuadTest' (univ.image x) (wpView x b th) (x yh) (x ah) (x ch) (x bh)
  testL : QuadTest' (univ.image x) (wpView x b tl) (x yl) (x al) (x cl) (x bl)
  n0b : ⟪x 0, wpView x b th⟫ ≠ ⟪x b, wpView x b th⟫
  nqh : ⟪x c, wpView x b th⟫ ≠ ⟪x q, wpView x b th⟫
  nql : ⟪x c, wpView x b tl⟫ ≠ ⟪x q, wpView x b tl⟫
  wp : ∀ t, lo < t → t < hi → t ∉ S → WPItem x b c q i t

/-- From the window chain: some test does not fail, or WP's chain holds at a certified view. -/
theorem WindowChain.cases {x : Fin 7 → ℝ³} {b c q i : Fin 7} {Xa Xb Xc : Fin 7 → ℝ}
    (W : WindowChain x b c q i Xa Xb Xc) (hd : ∀ t, wpView x b t ≠ 0)
    (hrep : ∀ v, x v = x 1 + Xa v • (x 0 - x 1) + Xb v • (x b - x 1) + Xc v • (x c - x 1))
    (haq : 0 < Xa q) (hbq : 0 < Xb q) (hcq : 0 < Xc q)
    (hSl : ⟪x c - x 1, wpView x b W.tl⟫ ≤ 0) (hSh : ⟪x c - x 1, wpView x b W.th⟫ ≤ 0)
    (hslope : ⟪x 0 - x 1, x b - x 1⟫ < ⟪x b - x 1, x b - x 1⟫) :
    ¬ Fails4 (x W.yh) (x W.ch) (x W.ah) (x W.bh) (wpView x b W.th) ∨
      ¬ Fails4 (x W.yl) (x W.cl) (x W.al) (x W.bl) (wpView x b W.tl) ∨
      ∃ t, 0 < t ∧ WPItem x b c q i t ∧ WPChain x b c q t := by
  have hL : Xc q ≤ 1 ∨
      (∀ t, ⟪x 0, wpView x b t⟫ = ⟪x b, wpView x b t⟫ →
        ⟪x c, wpView x b t⟫ < ⟪x q, wpView x b t⟫) ∨
      ((∀ ua ub uc : ℝ, uc ≤ 0 → 0 < ua + W.th * ub →
          CovFails Xa Xb Xc ua ub uc W.yh W.ch W.ah W.bh → uc ≤ covDepth Xa Xb Xc ua ub uc q) ∧
        (∀ ua ub uc : ℝ, uc ≤ 0 → 0 < ua + W.tl * ub →
          CovFails Xa Xb Xc ua ub uc W.yl W.cl W.al W.bl → uc ≤ covDepth Xa Xb Xc ua ub uc q)) := by
    rcases W.hL with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  rcases windowChain hd hrep haq hbq hcq W.hr W.hlo W.hlol W.hhi W.Hh W.Hl hSl hSh hslope hL
    W.n0b W.nqh W.nql with h | h | ⟨t3, hl3, h3h, ε, hε, hch⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · right; right
    have hlt : t3 < min (t3 + ε) W.hi := lt_min (by linarith) h3h
    obtain ⟨t, ⟨ht1, ht2⟩, htS⟩ := ((Set.Ioo_infinite hlt).sdiff W.S.finite_toSet).nonempty
    have ht2' := lt_of_lt_of_le ht2 (min_le_left _ _)
    have ht2'' := lt_of_lt_of_le ht2 (min_le_right _ _)
    exact ⟨t, by linarith [W.hlo], W.wp t (by linarith) ht2'' htS, hch t ht1 ht2'⟩

namespace Type24

variable {x : Fin 7 → ℝ³} (T : Type24 x)
include T

/-- The arc views of circle 2 are nonzero (`e_a`, `e_b` independent). -/
theorem wpView2_ne (t : ℝ) : wpView x 2 t ≠ 0 := by
  intro h
  have e : x 0 - x 1 = -t • (x 2 - x 1) := by
    rw [neg_smul, eq_neg_iff_add_eq_zero]; exact h
  apply T.det_ne
  rw [det24, e]
  simp only [vol3, PiLp.smul_apply, smul_eq_mul]; ring

/-- The arc views of circle 6 are nonzero. -/
theorem wpView6_ne (t : ℝ) : wpView x 6 t ≠ 0 := by
  intro h
  have e : x 0 - x 1 = -t • (x 6 - x 1) := by
    rw [neg_smul, eq_neg_iff_add_eq_zero]; exact h
  apply T.det_ne
  rw [det24, e]
  simp only [vol3, PiLp.smul_apply, smul_eq_mul]; ring

end Type24

/-- **Theorem 20.4 on arc 2, Rupert form.**  With the window-chain data on arc 2 (`B`'s rim
`(6, 4, 0, 2, 3)`, `5` inside) and (S), `K` is Rupert. -/
theorem isRupert_windowChain2 {x : Fin 7 → ℝ³} (T : Type24 x)
    (W : WindowChain x 2 6 4 5 (oblX0 x) (oblX2 x) (oblX6 x))
    (hSl : ⟪x 6 - x 1, wpView x 2 W.tl⟫ ≤ 0) (hSh : ⟪x 6 - x 1, wpView x 2 W.th⟫ ≤ 0)
    (hslope : ⟪x 0 - x 1, x 2 - x 1⟫ < ⟪x 2 - x 1, x 2 - x 1⟫) :
    IsRupert (univ.image x) := by
  rcases W.cases T.wpView2_ne T.rep (T.X0_pos (by decide)) (T.X2_pos (by decide))
    (T.X6_pos (by decide)) hSl hSh hslope with h | h | ⟨t, ht, hI, hC⟩
  · exact W.testH.isRupert h
  · exact W.testL.isRupert h
  · exact isRupert_wp2 T ht hI hC

/-- **Theorem 20.4 on arc 6, Rupert form** (the mirror: `B`'s rim `(2, 5, 0, 6, 3)`, `4`
inside; coordinates `(X0, X6, X2)`). -/
theorem isRupert_windowChain6 {x : Fin 7 → ℝ³} (T : Type24 x)
    (W : WindowChain x 6 2 5 4 (oblX0 x) (oblX6 x) (oblX2 x))
    (hSl : ⟪x 2 - x 1, wpView x 6 W.tl⟫ ≤ 0) (hSh : ⟪x 2 - x 1, wpView x 6 W.th⟫ ≤ 0)
    (hslope : ⟪x 0 - x 1, x 6 - x 1⟫ < ⟪x 6 - x 1, x 6 - x 1⟫) :
    IsRupert (univ.image x) := by
  rcases W.cases T.wpView6_ne T.rep062 (T.X0_pos (by decide)) (T.X6_pos (by decide))
    (T.X2_pos (by decide)) hSl hSh hslope with h | h | ⟨t, ht, hI, hC⟩
  · exact W.testH.isRupert h
  · exact W.testL.isRupert h
  · exact isRupert_wp6 T ht hI hC

/-- **Corollary 20.5 (the closed obtuse octant).**  If the window chain holds on arc 2 or on
arc 6, `K` is Rupert at every metric with `c_ab, c_ac, c_bc ≤ 0` (all lengths, no radius). -/
theorem isRupert_windowChain_octant {x : Fin 7 → ℝ³} (T : Type24 x)
    (hW : Nonempty (WindowChain x 2 6 4 5 (oblX0 x) (oblX2 x) (oblX6 x)) ∨
      Nonempty (WindowChain x 6 2 5 4 (oblX0 x) (oblX6 x) (oblX2 x)))
    (hab : ⟪x 0 - x 1, x 2 - x 1⟫ ≤ 0) (hac : ⟪x 0 - x 1, x 6 - x 1⟫ ≤ 0)
    (hbc : ⟪x 2 - x 1, x 6 - x 1⟫ ≤ 0) :
    IsRupert (univ.image x) := by
  have gb := T.gb_pos; have gc := T.gc_pos
  have c1 := real_inner_comm (x 0 - x 1) (x 6 - x 1)
  have c2 := real_inner_comm (x 2 - x 1) (x 6 - x 1)
  have c3 := real_inner_comm (x 0 - x 1) (x 2 - x 1)
  rcases hW with hW | hW
  · obtain ⟨W⟩ := hW
    have hS : ∀ t, 0 ≤ t → ⟪x 6 - x 1, wpView x 2 t⟫ ≤ 0 := by
      intro t ht
      rw [inner_wpView, c1, c2]
      nlinarith [mul_nonpos_of_nonneg_of_nonpos ht hbc]
    exact isRupert_windowChain2 T W (hS _ (by linarith [W.hlo, W.hlol]))
      (hS _ (by linarith [W.hlo, W.hloh])) (by linarith)
  · obtain ⟨W⟩ := hW
    have hS : ∀ t, 0 ≤ t → ⟪x 2 - x 1, wpView x 6 t⟫ ≤ 0 := by
      intro t ht
      rw [inner_wpView, c3]
      nlinarith [mul_nonpos_of_nonneg_of_nonpos ht hbc]
    exact isRupert_windowChain6 T W (hS _ (by linarith [W.hlo, W.hlol]))
      (hS _ (by linarith [W.hlo, W.hloh])) (by linarith)

/-- **Theorem 20.9 (a uniform statement on an explicit region of classes).**  Let `K` be type 24
with two acute-safe cap edges (`Type24.TwoSafe`, e.g. two cap edges with a single far corner,
`Type24.safeE2_of_four`) and the window chain on arc 2 or on arc 6 (`WindowChain`: the affine
hypotheses of 20.4 with `c4 ≤ 1` or (H⁺), resp. the mirror).  Then `K` is Rupert, whatever its
face angles and edge lengths at `1`: if some face angle at `1` is acute, by Theorem 20.8;
otherwise by Corollary 20.5.  The exclusions (ties of the items, horizontal double normals) are
carried by the data. -/
theorem isRupert_type24_uniform {x : Fin 7 → ℝ³} (T : Type24 x) (hsafe : Type24.TwoSafe x)
    (hW : Nonempty (WindowChain x 2 6 4 5 (oblX0 x) (oblX2 x) (oblX6 x)) ∨
      Nonempty (WindowChain x 6 2 5 4 (oblX0 x) (oblX6 x) (oblX2 x))) :
    IsRupert (univ.image x) := by
  by_cases h : 0 < ⟪x 0 - x 1, x 2 - x 1⟫ ∨ 0 < ⟪x 0 - x 1, x 6 - x 1⟫ ∨
      0 < ⟪x 2 - x 1, x 6 - x 1⟫
  · exact isRupert_type24_two_safe T hsafe h
  · simp only [not_or, not_lt] at h
    exact isRupert_windowChain_octant T hW h.1 h.2.1 h.2.2

end Minimality

end
