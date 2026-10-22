module

public import Minimality.Type24Chain
public import Minimality.Type24Side

@[expose] public section

/-!
# Type 24 at every metric: (L) from the high test, the chain without `r4 > 1`, and 20.9′

`FEWER-FACES-PROOFS.md` §20, continued (refereed 2026-10-22, scratch `referee_OO/`), at `K`'s own
metric.  Arc `b` of the cap face `1 0 b` (views `d(t) = e_a + t e_b`, `wpView x b t`), the other
axis `c` and the WP corner `q` (arc 2: `b, c, q = 2, 6, 4`; arc 6: `6, 2, 5`), in oblique
coordinates `x q = x 1 + a e_a + b' e_b + c' e_c`.  With `ℓ1 = z_q − z_c`, `ℓ2 = z_0 − z_q`,
`ℓ3 = z_b − z_0` at the view `d(t)`:

* **Lemma 20.10** (`Lambda.identity`, `Lambda.lemma_20_10`, `Lambda.lemma_20_10_strict`; at
  `K`'s metric `lemma_20_10_wp`): if `a, b' > 0`, `a + b' < 1 < c'`, `t_l < t_h`, `h_bc ≤ 0`,
  `ℓ1(t_h) ≥ 0`, `ℓ2(t_h) ≤ 0`, `ℓ3(t_l) ≤ 0` and
  (Λ) `b'(c' − 1)(t_h − t_l) ≤ (a + b' + c' − 1)(a t_l − b')`, then `ℓ1(t_l) ≥ 0`, and
  `ℓ1(t_l) > 0` if (Λ) is strict.  The proof is OO's linear identity (`cu12_Lambda.lean`,
  denominators cleared), reused verbatim; the strict clause is new.
* **The window chain, general form** (`windowChain_gen`): Theorem 20.4 with `a + b' < 1`
  replaced by "`a + b' < 1` or (L2)" (**Theorem 20.4″**: (L2) is `z0 > z_q` wherever `z0 = z_b`
  on the arc, `WPL2At`; its closed form at `t3` is `wpL2_of_poly`), and (L) supplied by
  `c' ≤ 1`, by (L) itself (`WPLAt`), by (H⁺) (`HPlus`), or by **Corollary 20.11** (`LamCond`:
  `τ_h` with the rim `(0, b, c, q)`, `a + b' < 1 < c'`, (Λ), at a metric with `h_bc ≤ 0`).
  Factored through `windowChain_core` (`t3 ∈ [t_l, t_h)` with `z0 = z_b`, `u_c(t3) ≤ 0`) and
  `wpChain_of_pos` (WP's chain just above `t3` from `ℓ1(t3), ℓ2(t3) > 0`).
* **Rupert forms** (`ChainData`: the window-chain data without `a + b' < 1` and without (L);
  `ChainData.cases`, `isRupert_chainData2`, `isRupert_chainData6`).  20.4″:
  `isRupert_chainData2_L2`, `isRupert_chainData6_L2`.  20.11: `WindowChainΛ` (the data with
  `τ_h = T′` of rim `(0, b, c, q)` and (Λ)), `isRupert_windowChainΛ2`, `isRupert_windowChainΛ6`,
  and on the closed obtuse octant `isRupert_windowChainΛ_octant`.
* **Theorem 20.9′** (`isRupert_type24_uniform_side`): side-covered cosines (20.8′) and the window
  chain on arc 2 or arc 6, with `c4 ≤ 1` or (H⁺) (`WindowChain`) or with (Λ) (`WindowChainΛ`),
  make `K` Rupert at every metric.

Not formalized: the LPs deciding (H_h), (H_l), (H⁺) and side-safety (carried as X-only
∀-statements), the third item `012/0345` of §13 (per-arc certificates), Conjecture B_DS, the
per-class certificates of §16, the counts.
-/

namespace Minimality

open Finset
open scoped RealInnerProductSpace

/-! ### Lemma 20.10: the linear identity -/

namespace Lambda

/-- `ℓ1 t = z4 − z6` at the view `(1, t, 0)`, in the Gram entries `g_a, g_b, h_ab, h_ac, h_bc`. -/
def l1 (a4 b4 c4 ga gb hab hac hbc t : ℝ) : ℝ :=
  a4 * (ga + t * hab) + b4 * (hab + t * gb) + (c4 - 1) * (hac + t * hbc)

/-- `ℓ2 t = z0 − z4` at the view `(1, t, 0)`. -/
def l2 (a4 b4 c4 ga gb hab hac hbc t : ℝ) : ℝ :=
  (1 - a4) * (ga + t * hab) - b4 * (hab + t * gb) - c4 * (hac + t * hbc)

/-- `ℓ3 t = z2 − z0` at the view `(1, t, 0)`. -/
def l3 (ga gb hab t : ℝ) : ℝ := (hab + t * gb) - (ga + t * hab)

/-- **The identity behind Lemma 20.10** (OO, `cu12_Lambda.lean`), with all denominators cleared
(`D = t_h − t_l`, `s = a4 + b4 + c4 − 1`). -/
theorem identity (a4 b4 c4 ga gb hab hac hbc tl th : ℝ) :
    let D := th - tl
    let s := a4 + b4 + c4 - 1
    let L2 := (c4 - 1) * (1 - a4) * D + s
    let L1 := L2 + c4 * a4 * D
    let L3 := (c4 - 1) * a4 * D
    let L4 := (c4 - 1 + a4) * a4 * D
    let L5 := (c4 - 1) * L1 * D
    let L6 := D * (s * (a4 * tl - b4) - b4 * (c4 - 1) * D)
    L1 * l1 a4 b4 c4 ga gb hab hac hbc tl =
      L2 * l1 a4 b4 c4 ga gb hab hac hbc th - L3 * l2 a4 b4 c4 ga gb hab hac hbc th
        - L4 * l3 ga gb hab tl - L5 * hbc + L6 * gb := by
  simp only [l1, l2, l3]
  ring

/-- The bound behind both clauses of Lemma 20.10: `L1 ℓ1(t_l) ≥ L6 g_b` with `L1 > 0`. -/
theorem bound (a4 b4 c4 ga gb hab hac hbc tl th : ℝ)
    (ha4 : 0 < a4) (hb4 : 0 < b4) (hab4 : a4 + b4 < 1) (hc4 : 1 < c4) (ht : tl < th)
    (hhbc : hbc ≤ 0)
    (h1 : 0 ≤ l1 a4 b4 c4 ga gb hab hac hbc th) (h2 : l2 a4 b4 c4 ga gb hab hac hbc th ≤ 0)
    (h3 : l3 ga gb hab tl ≤ 0) :
    0 < (c4 - 1) * (1 - a4) * (th - tl) + (a4 + b4 + c4 - 1) + c4 * a4 * (th - tl) ∧
      (th - tl) * ((a4 + b4 + c4 - 1) * (a4 * tl - b4) - b4 * (c4 - 1) * (th - tl)) * gb ≤
        ((c4 - 1) * (1 - a4) * (th - tl) + (a4 + b4 + c4 - 1) + c4 * a4 * (th - tl)) *
          l1 a4 b4 c4 ga gb hab hac hbc tl := by
  have key := identity a4 b4 c4 ga gb hab hac hbc tl th
  simp only at key
  set D := th - tl with hD
  have hDpos : 0 < D := by rw [hD]; linarith
  have h1a : 0 < 1 - a4 := by linarith
  have hL2 : 0 < (c4 - 1) * (1 - a4) * D + (a4 + b4 + c4 - 1) := by
    have : 0 < (c4 - 1) * (1 - a4) * D := mul_pos (mul_pos (by linarith) h1a) hDpos
    linarith
  have hL1 : 0 < (c4 - 1) * (1 - a4) * D + (a4 + b4 + c4 - 1) + c4 * a4 * D := by
    have : 0 < c4 * a4 * D := mul_pos (mul_pos (by linarith) ha4) hDpos
    linarith
  have hL3 : 0 ≤ (c4 - 1) * a4 * D := (mul_pos (mul_pos (by linarith) ha4) hDpos).le
  have hL4 : 0 ≤ (c4 - 1 + a4) * a4 * D := (mul_pos (mul_pos (by linarith) ha4) hDpos).le
  have hL5 : 0 ≤ (c4 - 1) * ((c4 - 1) * (1 - a4) * D + (a4 + b4 + c4 - 1) + c4 * a4 * D) * D :=
    (mul_pos (mul_pos (by linarith) hL1) hDpos).le
  have t1 := mul_nonneg hL2.le h1
  have t2 := mul_nonneg hL3 (neg_nonneg.mpr h2)
  have t3 := mul_nonneg hL4 (neg_nonneg.mpr h3)
  have t4 := mul_nonneg hL5 (neg_nonneg.mpr hhbc)
  refine ⟨hL1, ?_⟩
  rw [key]
  nlinarith [t1, t2, t3, t4]

/-- **Lemma 20.10** (OO's `Cu12.lemma_20_10`): under (Λ), `ℓ1(t_l) ≥ 0`. -/
theorem lemma_20_10 (a4 b4 c4 ga gb hab hac hbc tl th : ℝ)
    (ha4 : 0 < a4) (hb4 : 0 < b4) (hab4 : a4 + b4 < 1) (hc4 : 1 < c4) (ht : tl < th)
    (hgb : 0 < gb) (hhbc : hbc ≤ 0)
    (h1 : 0 ≤ l1 a4 b4 c4 ga gb hab hac hbc th) (h2 : l2 a4 b4 c4 ga gb hab hac hbc th ≤ 0)
    (h3 : l3 ga gb hab tl ≤ 0)
    (hL : b4 * (c4 - 1) * (th - tl) ≤ (a4 + b4 + c4 - 1) * (a4 * tl - b4)) :
    0 ≤ l1 a4 b4 c4 ga gb hab hac hbc tl := by
  obtain ⟨hL1, hb⟩ := bound a4 b4 c4 ga gb hab hac hbc tl th ha4 hb4 hab4 hc4 ht hhbc h1 h2 h3
  have h6 : 0 ≤ (th - tl) * ((a4 + b4 + c4 - 1) * (a4 * tl - b4) - b4 * (c4 - 1) * (th - tl)) * gb :=
    mul_nonneg (mul_nonneg (by linarith) (by linarith)) hgb.le
  by_contra hneg
  have := mul_neg_of_pos_of_neg hL1 (not_le.mp hneg)
  linarith

/-- **Lemma 20.10, strict clause** (new; the referee noted it was not in Lean): under strict
(Λ), `ℓ1(t_l) > 0`. -/
theorem lemma_20_10_strict (a4 b4 c4 ga gb hab hac hbc tl th : ℝ)
    (ha4 : 0 < a4) (hb4 : 0 < b4) (hab4 : a4 + b4 < 1) (hc4 : 1 < c4) (ht : tl < th)
    (hgb : 0 < gb) (hhbc : hbc ≤ 0)
    (h1 : 0 ≤ l1 a4 b4 c4 ga gb hab hac hbc th) (h2 : l2 a4 b4 c4 ga gb hab hac hbc th ≤ 0)
    (h3 : l3 ga gb hab tl ≤ 0)
    (hL : b4 * (c4 - 1) * (th - tl) < (a4 + b4 + c4 - 1) * (a4 * tl - b4)) :
    0 < l1 a4 b4 c4 ga gb hab hac hbc tl := by
  obtain ⟨hL1, hb⟩ := bound a4 b4 c4 ga gb hab hac hbc tl th ha4 hb4 hab4 hc4 ht hhbc h1 h2 h3
  have h6 : 0 < (th - tl) * ((a4 + b4 + c4 - 1) * (a4 * tl - b4) - b4 * (c4 - 1) * (th - tl)) * gb :=
    mul_pos (mul_pos (by linarith) (by linarith)) hgb
  by_contra hneg
  have := mul_nonpos_of_nonneg_of_nonpos hL1.le (not_lt.mp hneg)
  linarith

end Lambda

/-! ### The forms `ℓ1, ℓ2, ℓ3` at `K`'s metric -/

section Forms

variable {x : Fin 7 → ℝ³} {b c q : Fin 7} {aq bq cq : ℝ}

theorem inner_frame_wp
    (hq : x q = x 1 + aq • (x 0 - x 1) + bq • (x b - x 1) + cq • (x c - x 1)) (t : ℝ) :
    ⟪x q, wpView x b t⟫ = ⟪x 1, wpView x b t⟫ + aq * ⟪x 0 - x 1, wpView x b t⟫ +
      bq * ⟪x b - x 1, wpView x b t⟫ + cq * ⟪x c - x 1, wpView x b t⟫ := by
  rw [hq]; simp only [inner_add_left, real_inner_smul_left]

/-- `ℓ1 = z_q − z_c` at the arc view, in the Gram entries at `1`. -/
theorem wp_l1 (hq : x q = x 1 + aq • (x 0 - x 1) + bq • (x b - x 1) + cq • (x c - x 1)) (t : ℝ) :
    ⟪x q, wpView x b t⟫ - ⟪x c, wpView x b t⟫ =
      Lambda.l1 aq bq cq ⟪x 0 - x 1, x 0 - x 1⟫ ⟪x b - x 1, x b - x 1⟫ ⟪x 0 - x 1, x b - x 1⟫
        ⟪x 0 - x 1, x c - x 1⟫ ⟪x b - x 1, x c - x 1⟫ t := by
  have ec : ⟪x c, wpView x b t⟫ = ⟪x 1, wpView x b t⟫ + ⟪x c - x 1, wpView x b t⟫ := by
    rw [inner_sub_left]; ring
  rw [inner_frame_wp hq, ec]
  simp only [inner_wpView, Lambda.l1]
  rw [real_inner_comm (x 0 - x 1) (x b - x 1), real_inner_comm (x 0 - x 1) (x c - x 1),
    real_inner_comm (x b - x 1) (x c - x 1)]
  ring

/-- `ℓ2 = z_0 − z_q` at the arc view. -/
theorem wp_l2 (hq : x q = x 1 + aq • (x 0 - x 1) + bq • (x b - x 1) + cq • (x c - x 1)) (t : ℝ) :
    ⟪x 0, wpView x b t⟫ - ⟪x q, wpView x b t⟫ =
      Lambda.l2 aq bq cq ⟪x 0 - x 1, x 0 - x 1⟫ ⟪x b - x 1, x b - x 1⟫ ⟪x 0 - x 1, x b - x 1⟫
        ⟪x 0 - x 1, x c - x 1⟫ ⟪x b - x 1, x c - x 1⟫ t := by
  have e0 : ⟪x 0, wpView x b t⟫ = ⟪x 1, wpView x b t⟫ + ⟪x 0 - x 1, wpView x b t⟫ := by
    rw [inner_sub_left]; ring
  rw [inner_frame_wp hq, e0]
  simp only [inner_wpView, Lambda.l2]
  rw [real_inner_comm (x 0 - x 1) (x b - x 1), real_inner_comm (x 0 - x 1) (x c - x 1),
    real_inner_comm (x b - x 1) (x c - x 1)]
  ring

/-- `ℓ3 = z_b − z_0` at the arc view. -/
theorem wp_l3 (x : Fin 7 → ℝ³) (b : Fin 7) (t : ℝ) :
    ⟪x b, wpView x b t⟫ - ⟪x 0, wpView x b t⟫ =
      Lambda.l3 ⟪x 0 - x 1, x 0 - x 1⟫ ⟪x b - x 1, x b - x 1⟫ ⟪x 0 - x 1, x b - x 1⟫ t := by
  have e0 : ⟪x 0, wpView x b t⟫ = ⟪x 1, wpView x b t⟫ + ⟪x 0 - x 1, wpView x b t⟫ := by
    rw [inner_sub_left]; ring
  have eb : ⟪x b, wpView x b t⟫ = ⟪x 1, wpView x b t⟫ + ⟪x b - x 1, wpView x b t⟫ := by
    rw [inner_sub_left]; ring
  rw [e0, eb]
  simp only [inner_wpView, Lambda.l3]
  rw [real_inner_comm (x 0 - x 1) (x b - x 1)]
  ring

/-- **Lemma 20.10 at `K`'s own metric.**  On the arc `e_a + t e_b`, with `x q` at oblique
coordinates `a, b' > 0`, `a + b' < 1 < c'`, `t_l < t_h`, `g_b > 0` and `h_bc ≤ 0`: if
`z_c ≤ z_q` and `z_0 ≤ z_q` at `t_h`, `z_b ≤ z_0` at `t_l`, and (Λ), then `z_c ≤ z_q` at `t_l`,
strictly if (Λ) is strict. -/
theorem lemma_20_10_wp
    (hq : x q = x 1 + aq • (x 0 - x 1) + bq • (x b - x 1) + cq • (x c - x 1))
    (haq : 0 < aq) (hbq : 0 < bq) (hr : aq + bq < 1) (hcq : 1 < cq) {tl th : ℝ} (ht : tl < th)
    (hgb : 0 < ⟪x b - x 1, x b - x 1⟫) (hbc : ⟪x b - x 1, x c - x 1⟫ ≤ 0)
    (h1 : ⟪x c, wpView x b th⟫ ≤ ⟪x q, wpView x b th⟫)
    (h2 : ⟪x 0, wpView x b th⟫ ≤ ⟪x q, wpView x b th⟫)
    (h3 : ⟪x b, wpView x b tl⟫ ≤ ⟪x 0, wpView x b tl⟫)
    (hΛ : bq * (cq - 1) * (th - tl) ≤ (aq + bq + cq - 1) * (aq * tl - bq)) :
    ⟪x c, wpView x b tl⟫ ≤ ⟪x q, wpView x b tl⟫ ∧
      (bq * (cq - 1) * (th - tl) < (aq + bq + cq - 1) * (aq * tl - bq) →
        ⟪x c, wpView x b tl⟫ < ⟪x q, wpView x b tl⟫) := by
  have k1h := wp_l1 hq th
  have k2h := wp_l2 hq th
  have k3l := wp_l3 x b tl
  have k1l := wp_l1 hq tl
  have g1 : 0 ≤ Lambda.l1 aq bq cq ⟪x 0 - x 1, x 0 - x 1⟫ ⟪x b - x 1, x b - x 1⟫
      ⟪x 0 - x 1, x b - x 1⟫ ⟪x 0 - x 1, x c - x 1⟫ ⟪x b - x 1, x c - x 1⟫ th := by
    rw [← k1h]; linarith
  have g2 : Lambda.l2 aq bq cq ⟪x 0 - x 1, x 0 - x 1⟫ ⟪x b - x 1, x b - x 1⟫
      ⟪x 0 - x 1, x b - x 1⟫ ⟪x 0 - x 1, x c - x 1⟫ ⟪x b - x 1, x c - x 1⟫ th ≤ 0 := by
    rw [← k2h]; linarith
  have g3 : Lambda.l3 ⟪x 0 - x 1, x 0 - x 1⟫ ⟪x b - x 1, x b - x 1⟫ ⟪x 0 - x 1, x b - x 1⟫ tl ≤ 0 := by
    rw [← k3l]; linarith
  refine ⟨?_, fun hs => ?_⟩
  · have := Lambda.lemma_20_10 _ _ _ _ _ _ _ _ _ _ haq hbq hr hcq ht hgb hbc g1 g2 g3 hΛ
    rw [← k1l] at this; linarith
  · have := Lambda.lemma_20_10_strict _ _ _ _ _ _ _ _ _ _ haq hbq hr hcq ht hgb hbc g1 g2 g3 hs
    rw [← k1l] at this; linarith

end Forms

/-! ### The window chain, general form -/

/-- Linear interpolation, strict at the left end only. -/
theorem lin_pos_between' {P Q t1 t2 s : ℝ} (h1 : t1 ≤ s) (h2 : s < t2)
    (hp1 : 0 < P + t1 * Q) (hp2 : 0 ≤ P + t2 * Q) : 0 < P + s * Q := by
  have e : (t2 - t1) * (P + s * Q) = (t2 - s) * (P + t1 * Q) + (s - t1) * (P + t2 * Q) := by ring
  have : 0 < (t2 - t1) * (P + s * Q) := by
    rw [e]; exact add_pos_of_pos_of_nonneg (mul_pos (by linarith) hp1)
      (mul_nonneg (by linarith) hp2)
  by_contra hn; push Not at hn
  have := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ t2 - t1 by linarith) hn
  linarith

/-- `ℓ1 > 0` at `t_l` and `ℓ1 ≥ 0` at `t_h` give `ℓ1 > 0` on `[t_l, t_h)`. -/
theorem l1_interp {x : Fin 7 → ℝ³} {b c q : Fin 7} {tl th t3 : ℝ} (h1 : tl ≤ t3) (h2 : t3 < th)
    (hl : ⟪x c, wpView x b tl⟫ < ⟪x q, wpView x b tl⟫)
    (hh : ⟪x c, wpView x b th⟫ ≤ ⟪x q, wpView x b th⟫) :
    ⟪x c, wpView x b t3⟫ < ⟪x q, wpView x b t3⟫ := by
  simp only [inner_wpView] at hl hh ⊢
  have k := lin_pos_between' (P := ⟪x q, x 0 - x 1⟫ - ⟪x c, x 0 - x 1⟫)
    (Q := ⟪x q, x b - x 1⟫ - ⟪x c, x b - x 1⟫) h1 h2 (by linarith) (by linarith)
  linarith

/-- **WP's chain just above `t3`** from `z0 = z_b`, `ℓ1 > 0` and `ℓ2 > 0` at `t3` (the end of the
proof of Lemma 20.3, which uses `r4 > 1` only for `ℓ2(t3) > 0`). -/
theorem wpChain_of_pos {x : Fin 7 → ℝ³} {b c q : Fin 7} {t3 : ℝ}
    (h02 : ⟪x 0, wpView x b t3⟫ = ⟪x b, wpView x b t3⟫)
    (hslope : ⟪x 0 - x 1, x b - x 1⟫ < ⟪x b - x 1, x b - x 1⟫)
    (l1 : ⟪x c, wpView x b t3⟫ < ⟪x q, wpView x b t3⟫)
    (l2 : ⟪x q, wpView x b t3⟫ < ⟪x 0, wpView x b t3⟫) :
    ∃ ε > 0, ∀ t, t3 < t → t < t3 + ε → WPChain x b c q t := by
  obtain ⟨ε1, hε1, k1⟩ := exists_pos_near (B := ⟪x q, x b - x 1⟫ - ⟪x c, x b - x 1⟫)
    (sub_pos.mpr l1)
  obtain ⟨ε2, hε2, k2⟩ := exists_pos_near (B := ⟪x 0, x b - x 1⟫ - ⟪x q, x b - x 1⟫)
    (sub_pos.mpr l2)
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
  · rw [lin 0, lin b]
    have : 0 < (t - t3) * (⟪x b - x 1, x b - x 1⟫ - ⟪x 0 - x 1, x b - x 1⟫) :=
      mul_pos (by linarith) (by linarith)
    nlinarith

/-- **The depths at `t3`.**  Where `z0 = z_b` on the arc (`t3 ≥ 0`), `w = u_a(t3) > 0` and
`ℓ2(t3) = (1 − a − b') w − c' u_c(t3)`, `ℓ1(t3) = (a + b') w + (c' − 1) u_c(t3)`. -/
theorem wp_t3_facts {x : Fin 7 → ℝ³} {b c q : Fin 7} {aq bq cq : ℝ}
    (hq : x q = x 1 + aq • (x 0 - x 1) + bq • (x b - x 1) + cq • (x c - x 1))
    {t3 : ℝ} (ht3 : 0 ≤ t3) (hd : wpView x b t3 ≠ 0)
    (h02 : ⟪x 0, wpView x b t3⟫ = ⟪x b, wpView x b t3⟫) :
    ∃ w > 0, ⟪x 0, wpView x b t3⟫ - ⟪x q, wpView x b t3⟫ =
        (1 - aq - bq) * w - cq * ⟪x c - x 1, wpView x b t3⟫ ∧
      ⟪x q, wpView x b t3⟫ - ⟪x c, wpView x b t3⟫ =
        (aq + bq) * w + (cq - 1) * ⟪x c - x 1, wpView x b t3⟫ := by
  have e0 : ⟪x 0, wpView x b t3⟫ = ⟪x 1, wpView x b t3⟫ + ⟪x 0 - x 1, wpView x b t3⟫ := by
    rw [inner_sub_left]; ring
  have eb : ⟪x b, wpView x b t3⟫ = ⟪x 1, wpView x b t3⟫ + ⟪x b - x 1, wpView x b t3⟫ := by
    rw [inner_sub_left]; ring
  have ec : ⟪x c, wpView x b t3⟫ = ⟪x 1, wpView x b t3⟫ + ⟪x c - x 1, wpView x b t3⟫ := by
    rw [inner_sub_left]; ring
  have eq := inner_frame_wp hq t3
  have hab : ⟪x 0 - x 1, wpView x b t3⟫ = ⟪x b - x 1, wpView x b t3⟫ := by linarith
  have hdd : 0 < ⟪x 0 - x 1, wpView x b t3⟫ + t3 * ⟪x b - x 1, wpView x b t3⟫ := by
    rw [← wpView_self]; exact real_inner_self_pos.mpr hd
  refine ⟨⟪x 0 - x 1, wpView x b t3⟫, by rw [← hab] at hdd; nlinarith, ?_, ?_⟩
  · rw [eq, e0, ← hab]; ring
  · rw [eq, ec, ← hab]; ring

/-- **The core of the window chain** (Theorem 20.4's proof up to (L)): if both tests fail, then
`z_b ≤ z_0` at `t_l`, `z_0 < z_b` at `t_h`, and the unique view `t3` with `z0 = z_b` lies in
`[t_l, t_h)` with `u_c(t3) ≤ 0`. -/
theorem windowChain_core {x : Fin 7 → ℝ³} {b c : Fin 7} (hd : ∀ t, wpView x b t ≠ 0)
    {Xa Xb Xc : Fin 7 → ℝ}
    (hrep : ∀ v, x v = x 1 + Xa v • (x 0 - x 1) + Xb v • (x b - x 1) + Xc v • (x c - x 1))
    {tl th : ℝ} {yh ah ch bh yl al cl bl : Fin 7}
    (Hh : ∀ ua ub uc : ℝ, uc ≤ 0 → 0 < ua + th * ub → CovFails Xa Xb Xc ua ub uc yh ch ah bh →
      ua ≤ ub)
    (Hl : ∀ ua ub uc : ℝ, uc ≤ 0 → 0 < ua + tl * ub → CovFails Xa Xb Xc ua ub uc yl cl al bl →
      ub ≤ ua)
    (hSl : ⟪x c - x 1, wpView x b tl⟫ ≤ 0) (hSh : ⟪x c - x 1, wpView x b th⟫ ≤ 0)
    (hslope : ⟪x 0 - x 1, x b - x 1⟫ < ⟪x b - x 1, x b - x 1⟫)
    (n0b : ⟪x 0, wpView x b th⟫ ≠ ⟪x b, wpView x b th⟫)
    (hFh : Fails4 (x yh) (x ch) (x ah) (x bh) (wpView x b th))
    (hFl : Fails4 (x yl) (x cl) (x al) (x bl) (wpView x b tl)) :
    ⟪x b, wpView x b tl⟫ ≤ ⟪x 0, wpView x b tl⟫ ∧ ⟪x 0, wpView x b th⟫ < ⟪x b, wpView x b th⟫ ∧
      ∃ t3, tl ≤ t3 ∧ t3 < th ∧ ⟪x 0, wpView x b t3⟫ = ⟪x b, wpView x b t3⟫ ∧
        ⟪x c - x 1, wpView x b t3⟫ ≤ 0 ∧
        ∀ t, ⟪x 0, wpView x b t⟫ = ⟪x b, wpView x b t⟫ → t = t3 := by
  have covh := (fails4_iff_covFails hrep _ _ _ _ _).mp hFh
  have covl := (fails4_iff_covFails hrep _ _ _ _ _).mp hFl
  have posh : 0 < ⟪x 0 - x 1, wpView x b th⟫ + th * ⟪x b - x 1, wpView x b th⟫ := by
    rw [← wpView_self]; exact real_inner_self_pos.mpr (hd th)
  have posl : 0 < ⟪x 0 - x 1, wpView x b tl⟫ + tl * ⟪x b - x 1, wpView x b tl⟫ := by
    rw [← wpView_self]; exact real_inner_self_pos.mpr (hd tl)
  have l3h := Hh _ _ _ hSh posh covh
  have l3l := Hl _ _ _ hSl posl covl
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
  have h02 : ⟪x 0, wpView x b t3⟫ = ⟪x b, wpView x b t3⟫ := by
    have := l3 t3; rw [h3, sub1, sub1] at this; linarith
  have huc : ⟪x c - x 1, wpView x b t3⟫ ≤ 0 := by
    have k := lin_nonneg_between (P := -⟪x c - x 1, x 0 - x 1⟫) (Q := -⟪x c - x 1, x b - x 1⟫)
      htl3 ht3h (by rw [inner_wpView] at hSl; linarith) (by rw [inner_wpView] at hSh; linarith)
    rw [inner_wpView]; linarith
  refine ⟨?_, ?_, t3, htl3, ht3h, h02, huc, fun t ht => ?_⟩
  · rw [sub1, sub1] at l3l; linarith
  · have := l3 th; rw [sub1, sub1] at this; linarith
  · have := l3 t; rw [sub1, sub1] at this
    have e : t * B = t3 * B := by linarith
    exact mul_right_cancel₀ hBpos.ne' e

/-- **(L) on the arc**: `z_q > z_c` wherever `z0 = z_b`. -/
def WPLAt (x : Fin 7 → ℝ³) (b c q : Fin 7) : Prop :=
  ∀ t, ⟪x 0, wpView x b t⟫ = ⟪x b, wpView x b t⟫ → ⟪x c, wpView x b t⟫ < ⟪x q, wpView x b t⟫

/-- **(L2) on the arc** (Theorem 20.4″): `z0 > z_q` wherever `z0 = z_b`. -/
def WPL2At (x : Fin 7 → ℝ³) (b q : Fin 7) : Prop :=
  ∀ t, ⟪x 0, wpView x b t⟫ = ⟪x b, wpView x b t⟫ → ⟪x q, wpView x b t⟫ < ⟪x 0, wpView x b t⟫

/-- **(H⁺)** (X-only): every failure pattern of `τ_h` (of `τ_l`) forces `z_q ≥ z_c` on `U(t_h)`
(on `U(t_l)`). -/
def HPlus (Xa Xb Xc : Fin 7 → ℝ) (q yh ah ch bh yl al cl bl : Fin 7) (tl th : ℝ) : Prop :=
  (∀ ua ub uc : ℝ, uc ≤ 0 → 0 < ua + th * ub → CovFails Xa Xb Xc ua ub uc yh ch ah bh →
      uc ≤ covDepth Xa Xb Xc ua ub uc q) ∧
    (∀ ua ub uc : ℝ, uc ≤ 0 → 0 < ua + tl * ub → CovFails Xa Xb Xc ua ub uc yl cl al bl →
      uc ≤ covDepth Xa Xb Xc ua ub uc q)

/-- **The hypothesis of Corollary 20.11** (X-only): `τ_h` has the rim `(0, b, c, q)` (`T′(2,6)`
on arc 2), `a + b' < 1 < c'`, and (Λ) `b'(c' − 1)(t_h − t_l) ≤ (a + b' + c' − 1)(a t_l − b')`. -/
def LamCond (Xa Xb Xc : Fin 7 → ℝ) (b c q yh ah ch bh : Fin 7) (tl th : ℝ) : Prop :=
  (yh = 0 ∧ ah = b ∧ ch = c ∧ bh = q) ∧ Xa q + Xb q < 1 ∧ 1 < Xc q ∧
    Xb q * (Xc q - 1) * (th - tl) ≤ (Xa q + Xb q + Xc q - 1) * (Xa q * tl - Xb q)

/-- **The window chain, general form (Theorems 20.4, 20.4″, Corollary 20.11), every metric.**
As `windowChain`, with `a + b' < 1` replaced by "`a + b' < 1` or (L2)" (20.4″), and (L) supplied
by `c' ≤ 1`, by (L) itself, by (H⁺), or by (Λ) for `τ_h` of rim `(0, b, c, q)` at a metric
with `h_bc ≤ 0` (20.11).  Off the hyperplanes `z0 = z_b` at `t_h` and `z_q = z_c` at `t_l`
(the tie `z_q = z_c` at `t_h` of 20.4 is not needed: `ℓ1` strictly positive at `t_l` and
nonnegative at `t_h` is positive on `[t_l, t_h)`): a test does not fail, or WP's depth chain
holds on an interval `(t3, t3 + ε)` with `lo ≤ t3 < hi`. -/
theorem windowChain_gen {x : Fin 7 → ℝ³} {b c q : Fin 7} (hd : ∀ t, wpView x b t ≠ 0)
    {Xa Xb Xc : Fin 7 → ℝ}
    (hrep : ∀ v, x v = x 1 + Xa v • (x 0 - x 1) + Xb v • (x b - x 1) + Xc v • (x c - x 1))
    (haq : 0 < Xa q) (hbq : 0 < Xb q) (hcq : 0 < Xc q)
    {lo hi tl th : ℝ} (hlo : 0 ≤ lo) (hlol : lo ≤ tl) (hhi : th ≤ hi)
    {yh ah ch bh yl al cl bl : Fin 7}
    (Hh : ∀ ua ub uc : ℝ, uc ≤ 0 → 0 < ua + th * ub → CovFails Xa Xb Xc ua ub uc yh ch ah bh →
      ua ≤ ub)
    (Hl : ∀ ua ub uc : ℝ, uc ≤ 0 → 0 < ua + tl * ub → CovFails Xa Xb Xc ua ub uc yl cl al bl →
      ub ≤ ua)
    (hSl : ⟪x c - x 1, wpView x b tl⟫ ≤ 0) (hSh : ⟪x c - x 1, wpView x b th⟫ ≤ 0)
    (hslope : ⟪x 0 - x 1, x b - x 1⟫ < ⟪x b - x 1, x b - x 1⟫)
    (hR4 : Xa q + Xb q < 1 ∨ WPL2At x b q)
    (hL : Xc q ≤ 1 ∨ WPLAt x b c q ∨ HPlus Xa Xb Xc q yh ah ch bh yl al cl bl tl th ∨
      (LamCond Xa Xb Xc b c q yh ah ch bh tl th ∧ ⟪x b - x 1, x c - x 1⟫ ≤ 0))
    (n0b : ⟪x 0, wpView x b th⟫ ≠ ⟪x b, wpView x b th⟫)
    (nql : ⟪x c, wpView x b tl⟫ ≠ ⟪x q, wpView x b tl⟫) :
    ¬ Fails4 (x yh) (x ch) (x ah) (x bh) (wpView x b th) ∨
      ¬ Fails4 (x yl) (x cl) (x al) (x bl) (wpView x b tl) ∨
      ∃ t3, lo ≤ t3 ∧ t3 < hi ∧ ∃ ε > 0, ∀ t, t3 < t → t < t3 + ε → WPChain x b c q t := by
  by_cases hFh : Fails4 (x yh) (x ch) (x ah) (x bh) (wpView x b th)
  swap; · exact Or.inl hFh
  by_cases hFl : Fails4 (x yl) (x cl) (x al) (x bl) (wpView x b tl)
  swap; · exact Or.inr (Or.inl hFl)
  right; right
  obtain ⟨l3l, l3h, t3, htl3, ht3h, h02, huc, -⟩ :=
    windowChain_core hd hrep Hh Hl hSl hSh hslope n0b hFh hFl
  refine ⟨t3, by linarith, by linarith, ?_⟩
  obtain ⟨w, hw, f2, f1⟩ := wp_t3_facts (hrep q) (by linarith) (hd t3) h02
  have l2 : ⟪x q, wpView x b t3⟫ < ⟪x 0, wpView x b t3⟫ := by
    rcases hR4 with hr | hL2
    · have : 0 < (1 - Xa q - Xb q) * w := mul_pos (by linarith) hw
      nlinarith [mul_nonneg hcq.le (neg_nonneg.mpr huc)]
    · exact hL2 t3 h02
  have l1 : ⟪x c, wpView x b t3⟫ < ⟪x q, wpView x b t3⟫ := by
    rcases hL with hL | hL | ⟨Ph, Pl⟩ | ⟨⟨⟨e1, e2, e3, e4⟩, hr, hc, hΛ⟩, hbc⟩
    · have : 0 < (Xa q + Xb q) * w := mul_pos (by linarith) hw
      nlinarith [mul_nonneg (sub_nonneg.mpr hL) (neg_nonneg.mpr huc)]
    · exact hL t3 h02
    · have covh := (fails4_iff_covFails hrep _ _ _ _ _).mp hFh
      have covl := (fails4_iff_covFails hrep _ _ _ _ _).mp hFl
      have posh : 0 < ⟪x 0 - x 1, wpView x b th⟫ + th * ⟪x b - x 1, wpView x b th⟫ := by
        rw [← wpView_self]; exact real_inner_self_pos.mpr (hd th)
      have posl : 0 < ⟪x 0 - x 1, wpView x b tl⟫ + tl * ⟪x b - x 1, wpView x b tl⟫ := by
        rw [← wpView_self]; exact real_inner_self_pos.mpr (hd tl)
      have dq : ∀ t, covDepth Xa Xb Xc ⟪x 0 - x 1, wpView x b t⟫ ⟪x b - x 1, wpView x b t⟫
          ⟪x c - x 1, wpView x b t⟫ q = ⟪x q, wpView x b t⟫ - ⟪x 1, wpView x b t⟫ := by
        intro t; rw [inner_covDepth hrep (wpView x b t) q]; ring
      have ph := Ph _ _ _ hSh posh covh
      have pl := Pl _ _ _ hSl posl covl
      rw [dq, inner_sub_left] at ph pl
      exact l1_interp htl3 ht3h (lt_of_le_of_ne (by linarith) nql) (by linarith)
    · -- Corollary 20.11: Lemma 20.10 from the pattern of `τ_h`
      rw [e1, e2, e3, e4] at hFh
      have hpat : ⟪x c, wpView x b th⟫ ≤ ⟪x q, wpView x b th⟫ ∧
          ⟪x 0, wpView x b th⟫ ≤ ⟪x q, wpView x b th⟫ := by
        rcases hFh with h | h <;> simp only [max_le_iff, le_min_iff] at h
        · exact ⟨h.2.2, h.2.1⟩
        · exact absurd h.1.1 (not_le.mpr l3h)
      have hgb : 0 < ⟪x b - x 1, x b - x 1⟫ := by
        refine real_inner_self_pos.mpr fun h0 => ?_
        simp [h0] at hslope
      have hlam := lemma_20_10_wp (hrep q) haq hbq hr hc (by linarith) hgb hbc hpat.1 hpat.2 l3l hΛ
      exact l1_interp htl3 ht3h (lt_of_le_of_ne hlam.1 nql) hpat.1
  exact wpChain_of_pos h02 hslope l1 l2

/-- **(L2) from its closed form** (Theorem 20.4″): with `h_ab < g_b`,
`(g_a g_b − h_ab²)(1 − a − b') − c' [h_ac (g_b − h_ab) + h_bc (g_a − h_ab)] > 0` is
`(g_b − h_ab) ℓ2(t3) > 0`, so `z0 > z_q` at the view `t3` where `z0 = z_b`. -/
theorem wpL2_of_poly {x : Fin 7 → ℝ³} {b c q : Fin 7} {aq bq cq : ℝ}
    (hq : x q = x 1 + aq • (x 0 - x 1) + bq • (x b - x 1) + cq • (x c - x 1))
    (hslope : ⟪x 0 - x 1, x b - x 1⟫ < ⟪x b - x 1, x b - x 1⟫)
    (hP : 0 < (⟪x 0 - x 1, x 0 - x 1⟫ * ⟪x b - x 1, x b - x 1⟫ - ⟪x 0 - x 1, x b - x 1⟫ ^ 2) *
        (1 - aq - bq) - cq * (⟪x 0 - x 1, x c - x 1⟫ *
          (⟪x b - x 1, x b - x 1⟫ - ⟪x 0 - x 1, x b - x 1⟫) +
        ⟪x b - x 1, x c - x 1⟫ * (⟪x 0 - x 1, x 0 - x 1⟫ - ⟪x 0 - x 1, x b - x 1⟫))) :
    WPL2At x b q := by
  intro t ht
  have k2 := wp_l2 hq t
  have k3 := wp_l3 x b t
  rw [ht, sub_self] at k3
  simp only [Lambda.l2] at k2
  simp only [Lambda.l3] at k3
  set ga := ⟪x 0 - x 1, x 0 - x 1⟫
  set gb := ⟪x b - x 1, x b - x 1⟫
  set hab := ⟪x 0 - x 1, x b - x 1⟫
  set hac := ⟪x 0 - x 1, x c - x 1⟫
  set hbc := ⟪x b - x 1, x c - x 1⟫
  have key : (gb - hab) * ((1 - aq) * (ga + t * hab) - bq * (hab + t * gb) - cq * (hac + t * hbc)) =
      (ga * gb - hab ^ 2) * (1 - aq - bq) - cq * (hac * (gb - hab) + hbc * (ga - hab)) := by
    linear_combination ((1 - aq) * hab - bq * gb - cq * hbc) * k3.symm
  have hpos : 0 < (1 - aq) * (ga + t * hab) - bq * (hab + t * gb) - cq * (hac + t * hbc) := by
    by_contra hn; push Not at hn
    nlinarith [mul_nonpos_of_nonneg_of_nonpos (sub_pos.mpr hslope).le hn]
  linarith

/-! ### Rupert forms -/

/-- **The data of the window chain on one arc, without `a + b' < 1` and without (L)**: the face
interval `[lo, hi]` (`lo ≥ 0`) on which `B`'s rim is WP's pentagon (`WPItem`, off a finite set
`S` of views), the tests `τ_h`, `τ_l` at views `t_l, t_h ∈ [lo, hi]` with the rims
`(yh, ah, ch, bh)`, `(yl, al, cl, bl)` certified up to their depth patterns (`QuadTest'`), the
X-only hypotheses (H_h), (H_l), and the ties `z0 = z_b` at `t_h` and `z_q = z_c` at `t_l`
excluded. -/
structure ChainData (x : Fin 7 → ℝ³) (b c q i : Fin 7) (Xa Xb Xc : Fin 7 → ℝ) where
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
  Hh : ∀ ua ub uc : ℝ, uc ≤ 0 → 0 < ua + th * ub → CovFails Xa Xb Xc ua ub uc yh ch ah bh →
    ua ≤ ub
  Hl : ∀ ua ub uc : ℝ, uc ≤ 0 → 0 < ua + tl * ub → CovFails Xa Xb Xc ua ub uc yl cl al bl →
    ub ≤ ua
  testH : QuadTest' (univ.image x) (wpView x b th) (x yh) (x ah) (x ch) (x bh)
  testL : QuadTest' (univ.image x) (wpView x b tl) (x yl) (x al) (x cl) (x bl)
  n0b : ⟪x 0, wpView x b th⟫ ≠ ⟪x b, wpView x b th⟫
  nql : ⟪x c, wpView x b tl⟫ ≠ ⟪x q, wpView x b tl⟫
  wp : ∀ t, lo < t → t < hi → t ∉ S → WPItem x b c q i t

/-- (H⁺) for the chain data. -/
def ChainData.HPlus {x : Fin 7 → ℝ³} {b c q i : Fin 7} {Xa Xb Xc : Fin 7 → ℝ}
    (D : ChainData x b c q i Xa Xb Xc) : Prop :=
  Minimality.HPlus Xa Xb Xc q D.yh D.ah D.ch D.bh D.yl D.al D.cl D.bl D.tl D.th

/-- The hypothesis of Corollary 20.11 for the chain data. -/
def ChainData.Lam {x : Fin 7 → ℝ³} {b c q i : Fin 7} {Xa Xb Xc : Fin 7 → ℝ}
    (D : ChainData x b c q i Xa Xb Xc) : Prop :=
  LamCond Xa Xb Xc b c q D.yh D.ah D.ch D.bh D.tl D.th

/-- From the chain data: some test does not fail, or WP's chain holds at a certified view. -/
theorem ChainData.cases {x : Fin 7 → ℝ³} {b c q i : Fin 7} {Xa Xb Xc : Fin 7 → ℝ}
    (D : ChainData x b c q i Xa Xb Xc) (hd : ∀ t, wpView x b t ≠ 0)
    (hrep : ∀ v, x v = x 1 + Xa v • (x 0 - x 1) + Xb v • (x b - x 1) + Xc v • (x c - x 1))
    (haq : 0 < Xa q) (hbq : 0 < Xb q) (hcq : 0 < Xc q)
    (hSl : ⟪x c - x 1, wpView x b D.tl⟫ ≤ 0) (hSh : ⟪x c - x 1, wpView x b D.th⟫ ≤ 0)
    (hslope : ⟪x 0 - x 1, x b - x 1⟫ < ⟪x b - x 1, x b - x 1⟫)
    (hR4 : Xa q + Xb q < 1 ∨ WPL2At x b q)
    (hL : Xc q ≤ 1 ∨ WPLAt x b c q ∨ D.HPlus ∨ (D.Lam ∧ ⟪x b - x 1, x c - x 1⟫ ≤ 0)) :
    ¬ Fails4 (x D.yh) (x D.ch) (x D.ah) (x D.bh) (wpView x b D.th) ∨
      ¬ Fails4 (x D.yl) (x D.cl) (x D.al) (x D.bl) (wpView x b D.tl) ∨
      ∃ t, 0 < t ∧ WPItem x b c q i t ∧ WPChain x b c q t := by
  rcases windowChain_gen hd hrep haq hbq hcq D.hlo D.hlol D.hhi D.Hh D.Hl hSl hSh hslope hR4 hL
    D.n0b D.nql with h | h | ⟨t3, hl3, h3h, ε, hε, hch⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · right; right
    have hlt : t3 < min (t3 + ε) D.hi := lt_min (by linarith) h3h
    obtain ⟨t, ⟨ht1, ht2⟩, htS⟩ := ((Set.Ioo_infinite hlt).sdiff D.S.finite_toSet).nonempty
    have ht2' := lt_of_lt_of_le ht2 (min_le_left _ _)
    have ht2'' := lt_of_lt_of_le ht2 (min_le_right _ _)
    exact ⟨t, by linarith [D.hlo], D.wp t (by linarith) ht2'' htS, hch t ht1 ht2'⟩

/-- **The general window chain on arc 2, Rupert form** (`B`'s rim `(6, 4, 0, 2, 3)`, `5`
inside). -/
theorem isRupert_chainData2 {x : Fin 7 → ℝ³} (T : Type24 x)
    (D : ChainData x 2 6 4 5 (oblX0 x) (oblX2 x) (oblX6 x))
    (hSl : ⟪x 6 - x 1, wpView x 2 D.tl⟫ ≤ 0) (hSh : ⟪x 6 - x 1, wpView x 2 D.th⟫ ≤ 0)
    (hslope : ⟪x 0 - x 1, x 2 - x 1⟫ < ⟪x 2 - x 1, x 2 - x 1⟫)
    (hR4 : oblX0 x 4 + oblX2 x 4 < 1 ∨ WPL2At x 2 4)
    (hL : oblX6 x 4 ≤ 1 ∨ WPLAt x 2 6 4 ∨ D.HPlus ∨ (D.Lam ∧ ⟪x 2 - x 1, x 6 - x 1⟫ ≤ 0)) :
    IsRupert (univ.image x) := by
  rcases D.cases T.wpView2_ne T.rep (T.X0_pos (by decide)) (T.X2_pos (by decide))
    (T.X6_pos (by decide)) hSl hSh hslope hR4 hL with h | h | ⟨t, ht, hI, hC⟩
  · exact D.testH.isRupert h
  · exact D.testL.isRupert h
  · exact isRupert_wp2 T ht hI hC

/-- **The general window chain on arc 6, Rupert form** (the mirror: `B`'s rim `(2, 5, 0, 6, 3)`,
`4` inside; coordinates `(X0, X6, X2)`). -/
theorem isRupert_chainData6 {x : Fin 7 → ℝ³} (T : Type24 x)
    (D : ChainData x 6 2 5 4 (oblX0 x) (oblX6 x) (oblX2 x))
    (hSl : ⟪x 2 - x 1, wpView x 6 D.tl⟫ ≤ 0) (hSh : ⟪x 2 - x 1, wpView x 6 D.th⟫ ≤ 0)
    (hslope : ⟪x 0 - x 1, x 6 - x 1⟫ < ⟪x 6 - x 1, x 6 - x 1⟫)
    (hR4 : oblX0 x 5 + oblX6 x 5 < 1 ∨ WPL2At x 6 5)
    (hL : oblX2 x 5 ≤ 1 ∨ WPLAt x 6 2 5 ∨ D.HPlus ∨ (D.Lam ∧ ⟪x 6 - x 1, x 2 - x 1⟫ ≤ 0)) :
    IsRupert (univ.image x) := by
  rcases D.cases T.wpView6_ne T.rep062 (T.X0_pos (by decide)) (T.X6_pos (by decide))
    (T.X2_pos (by decide)) hSl hSh hslope hR4 hL with h | h | ⟨t, ht, hI, hC⟩
  · exact D.testH.isRupert h
  · exact D.testL.isRupert h
  · exact isRupert_wp6 T ht hI hC

/-- **Theorem 20.4″ on arc 2 (the chain without `r4 > 1`), Rupert form.**  With the chain data,
`c4 ≤ 1` or (H⁺), (S), and (L2) in closed form
`(g_a g_b − h_ab²)(1 − a4 − b4) − c4 [h_ac (g_b − h_ab) + h_bc (g_a − h_ab)] > 0`, `K` is Rupert;
`a4 + b4 < 1` is not needed. -/
theorem isRupert_chainData2_L2 {x : Fin 7 → ℝ³} (T : Type24 x)
    (D : ChainData x 2 6 4 5 (oblX0 x) (oblX2 x) (oblX6 x)) (hL : oblX6 x 4 ≤ 1 ∨ D.HPlus)
    (hSl : ⟪x 6 - x 1, wpView x 2 D.tl⟫ ≤ 0) (hSh : ⟪x 6 - x 1, wpView x 2 D.th⟫ ≤ 0)
    (hslope : ⟪x 0 - x 1, x 2 - x 1⟫ < ⟪x 2 - x 1, x 2 - x 1⟫)
    (hL2 : 0 < (⟪x 0 - x 1, x 0 - x 1⟫ * ⟪x 2 - x 1, x 2 - x 1⟫ - ⟪x 0 - x 1, x 2 - x 1⟫ ^ 2) *
        (1 - oblX0 x 4 - oblX2 x 4) - oblX6 x 4 * (⟪x 0 - x 1, x 6 - x 1⟫ *
          (⟪x 2 - x 1, x 2 - x 1⟫ - ⟪x 0 - x 1, x 2 - x 1⟫) +
        ⟪x 2 - x 1, x 6 - x 1⟫ * (⟪x 0 - x 1, x 0 - x 1⟫ - ⟪x 0 - x 1, x 2 - x 1⟫))) :
    IsRupert (univ.image x) := by
  refine isRupert_chainData2 T D hSl hSh hslope (Or.inr (wpL2_of_poly (T.rep 4) hslope hL2)) ?_
  rcases hL with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inr (Or.inl h))

/-- **Theorem 20.4″ on arc 6, Rupert form** (the mirror: (L2) with `a5, c5, b5` and `b ↔ c`). -/
theorem isRupert_chainData6_L2 {x : Fin 7 → ℝ³} (T : Type24 x)
    (D : ChainData x 6 2 5 4 (oblX0 x) (oblX6 x) (oblX2 x)) (hL : oblX2 x 5 ≤ 1 ∨ D.HPlus)
    (hSl : ⟪x 2 - x 1, wpView x 6 D.tl⟫ ≤ 0) (hSh : ⟪x 2 - x 1, wpView x 6 D.th⟫ ≤ 0)
    (hslope : ⟪x 0 - x 1, x 6 - x 1⟫ < ⟪x 6 - x 1, x 6 - x 1⟫)
    (hL2 : 0 < (⟪x 0 - x 1, x 0 - x 1⟫ * ⟪x 6 - x 1, x 6 - x 1⟫ - ⟪x 0 - x 1, x 6 - x 1⟫ ^ 2) *
        (1 - oblX0 x 5 - oblX6 x 5) - oblX2 x 5 * (⟪x 0 - x 1, x 2 - x 1⟫ *
          (⟪x 6 - x 1, x 6 - x 1⟫ - ⟪x 0 - x 1, x 6 - x 1⟫) +
        ⟪x 6 - x 1, x 2 - x 1⟫ * (⟪x 0 - x 1, x 0 - x 1⟫ - ⟪x 0 - x 1, x 6 - x 1⟫))) :
    IsRupert (univ.image x) := by
  refine isRupert_chainData6 T D hSl hSh hslope (Or.inr (wpL2_of_poly (T.rep062 5) hslope hL2)) ?_
  rcases hL with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inr (Or.inl h))

/-- **The window chain with (Λ) (Corollary 20.11)**: the chain data with `τ_h = T′` of rim
`(0, b, c, q)` (`T′(2,6) = 012/236` with rim `(0, 2, 6, 4)` on arc 2), `a + b' < 1 < c'`, and
(Λ) `b'(c' − 1)(t_h − t_l) ≤ (a + b' + c' − 1)(a t_l − b')`.  All X-only. -/
structure WindowChainΛ (x : Fin 7 → ℝ³) (b c q i : Fin 7) (Xa Xb Xc : Fin 7 → ℝ) extends
    ChainData x b c q i Xa Xb Xc where
  lam : LamCond Xa Xb Xc b c q yh ah ch bh tl th

/-- **Corollary 20.11 on arc 2, Rupert form**: with (Λ) in place of (L) and (H⁺), (S) and
`h_bc ≤ 0`, `K` is Rupert. -/
theorem isRupert_windowChainΛ2 {x : Fin 7 → ℝ³} (T : Type24 x)
    (W : WindowChainΛ x 2 6 4 5 (oblX0 x) (oblX2 x) (oblX6 x))
    (hSl : ⟪x 6 - x 1, wpView x 2 W.tl⟫ ≤ 0) (hSh : ⟪x 6 - x 1, wpView x 2 W.th⟫ ≤ 0)
    (hslope : ⟪x 0 - x 1, x 2 - x 1⟫ < ⟪x 2 - x 1, x 2 - x 1⟫)
    (hbc : ⟪x 2 - x 1, x 6 - x 1⟫ ≤ 0) : IsRupert (univ.image x) :=
  isRupert_chainData2 T W.toChainData hSl hSh hslope (Or.inl W.lam.2.1)
    (Or.inr (Or.inr (Or.inr ⟨W.lam, hbc⟩)))

/-- **Corollary 20.11 on arc 6, Rupert form** (the mirror: `τ_h = 016/236` with rim
`(0, 6, 2, 5)`, (Λ₆) `c5(b5 − 1)(t_h − t_l) ≤ (a5 + b5 + c5 − 1)(a5 t_l − c5)`). -/
theorem isRupert_windowChainΛ6 {x : Fin 7 → ℝ³} (T : Type24 x)
    (W : WindowChainΛ x 6 2 5 4 (oblX0 x) (oblX6 x) (oblX2 x))
    (hSl : ⟪x 2 - x 1, wpView x 6 W.tl⟫ ≤ 0) (hSh : ⟪x 2 - x 1, wpView x 6 W.th⟫ ≤ 0)
    (hslope : ⟪x 0 - x 1, x 6 - x 1⟫ < ⟪x 6 - x 1, x 6 - x 1⟫)
    (hbc : ⟪x 6 - x 1, x 2 - x 1⟫ ≤ 0) : IsRupert (univ.image x) :=
  isRupert_chainData6 T W.toChainData hSl hSh hslope (Or.inl W.lam.2.1)
    (Or.inr (Or.inr (Or.inr ⟨W.lam, hbc⟩)))

/-- **Corollary 20.11 on the closed obtuse octant.**  If the window chain with (Λ) holds on arc 2
or on arc 6, `K` is Rupert at every metric with `c_ab, c_ac, c_bc ≤ 0` (all lengths, no
radius). -/
theorem isRupert_windowChainΛ_octant {x : Fin 7 → ℝ³} (T : Type24 x)
    (hW : Nonempty (WindowChainΛ x 2 6 4 5 (oblX0 x) (oblX2 x) (oblX6 x)) ∨
      Nonempty (WindowChainΛ x 6 2 5 4 (oblX0 x) (oblX6 x) (oblX2 x)))
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
    exact isRupert_windowChainΛ2 T W (hS _ (by linarith [W.hlo, W.hlol]))
      (hS _ (by linarith [W.hlo, W.hloh])) (by linarith) hbc
  · obtain ⟨W⟩ := hW
    have hS : ∀ t, 0 ≤ t → ⟪x 2 - x 1, wpView x 6 t⟫ ≤ 0 := by
      intro t ht
      rw [inner_wpView, c3]
      nlinarith [mul_nonpos_of_nonneg_of_nonpos ht hbc]
    exact isRupert_windowChainΛ6 T W (hS _ (by linarith [W.hlo, W.hlol]))
      (hS _ (by linarith [W.hlo, W.hloh])) (by linarith) (by rw [c2]; exact hbc)

/-- **Theorem 20.9′ (a uniform statement from side-safety).**  Let `K` be type 24 with each
cosine at `1` seen on a safe side by a cap edge (`Type24.SideCovered`, Theorem 20.8′) and the
window chain on arc 2 or on arc 6, with `c4 ≤ 1` or (H⁺) (`WindowChain`) or with (Λ)
(`WindowChainΛ`, Corollary 20.11).  Then `K` is Rupert, whatever its face angles and edge
lengths at `1`: if some face angle at `1` is acute, by Theorem 20.8′; otherwise on the closed
obtuse octant by Corollaries 20.5 and 20.11.  The exclusions (ties of the items, horizontal
double normals) are carried by the data. -/
theorem isRupert_type24_uniform_side {x : Fin 7 → ℝ³} (T : Type24 x)
    (hside : Type24.SideCovered x)
    (hW : Nonempty (WindowChain x 2 6 4 5 (oblX0 x) (oblX2 x) (oblX6 x)) ∨
      Nonempty (WindowChain x 6 2 5 4 (oblX0 x) (oblX6 x) (oblX2 x)) ∨
      Nonempty (WindowChainΛ x 2 6 4 5 (oblX0 x) (oblX2 x) (oblX6 x)) ∨
      Nonempty (WindowChainΛ x 6 2 5 4 (oblX0 x) (oblX6 x) (oblX2 x))) :
    IsRupert (univ.image x) := by
  by_cases h : 0 < ⟪x 0 - x 1, x 2 - x 1⟫ ∨ 0 < ⟪x 0 - x 1, x 6 - x 1⟫ ∨
      0 < ⟪x 2 - x 1, x 6 - x 1⟫
  · exact isRupert_type24_side_safe T hside h
  · simp only [not_or, not_lt] at h
    rcases hW with hW | hW | hW | hW
    · exact isRupert_windowChain_octant T (Or.inl hW) h.1 h.2.1 h.2.2
    · exact isRupert_windowChain_octant T (Or.inr hW) h.1 h.2.1 h.2.2
    · exact isRupert_windowChainΛ_octant T (Or.inl hW) h.1 h.2.1 h.2.2
    · exact isRupert_windowChainΛ_octant T (Or.inr hW) h.1 h.2.1 h.2.2

end Minimality

end
