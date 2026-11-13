module

public import Minimality.Type16M
public import Minimality.OctAxis

@[expose] public section

/-!
# Edge pairs: Lemma E (§14)

Lemma E, in Euclidean form (as the angle lemma in `OctAxis.lean`): the usual "at
every metric" becomes a statement about the inner product of `ℝ³`, which is one metric, so
the depth along the view `u = w − v` is `⟪·, u⟫`.

The setting: an edge crossing (Theorem 8.9) along the edge `v w`, view `u = w − v`.  The two
closings `K_v` (keep `v`, drop `w`) and `K_w` have the 4-corner rims `(v, a, c, b)` and
`(w, a, c, b)` (counterclockwise at `u`: the four triple tests `q₁`–`q₄`), with one far path
`a, c, b`.  A 4-corner rim with distinct depths is unimodal unless its diagonals are
depth-separated (`DepthSep`, `overlap4_of_not_depthSep`).

* **Lemma E** (`edgePair_not_both`, `edgePair_unimodal`): if `v` and `w` lie weakly on
  opposite sides of the plane `abc`, i.e. `[a b c v] [a b c w] ≤ 0` (the paper's (iii) is the
  strict case; equality is the planar closing), the two rims are not both depth-separated,
  so `K_v` or `K_w` is unimodal (with distinct depths).  The parameter form
  (`edgePair_param`, the remark on `l_v ≥ 0 ≥ l_w`): over the crossing `m` of the diagonals,
  `e − d_v = λ u` with `0 ≤ λ ≤ 1 − s`.
* **(ii) ⟺ (iii)** (`edgePair_tri_iff`): the segment `[a, b]` meets the closed triangle
  `(v, w, c)` (`SegMeetsTri`) iff `[a b c v] [a b c w] ≤ 0`.
* **The converse at the level of depth functionals** (`edgePair_converse`): if
  `[a b c v] [a b c w] > 0`, some linear functional `φ` with `φ(u) > 0` depth-separates both
  rims.  (The paper adds distinct depths, an open set of such `φ`, and the metric with
  `G u = φ` of §13.0; those are not formalized.)
* **Corollary 14.1 (Rupert)** (`isRupert_edgePair`): with the shadow `(q, a, c, b)` strictly
  convex, every other point a middle over a side at `q` (`EdgeMid`) or strictly inside
  (`EdgeHidden`), distinct depths on both rims and no horizontal double normal at `u` for
  either closing, `K` is Rupert (Theorem 8.9 with Theorem 7.3, through
  `isRupert_quad_rim_int`).  The closing used is `isRupert_edgePair_closing`.
* **The wedge argument** (`wedge_sep`) and **Proposition 14.3 (E06)**: for every type-16
  point set, `0` and `6` lie strictly on opposite sides of the plane `345`
  (`type16_sep06`); so at the view along `06`, if `1` and `2` are strictly inside the
  4-corner shadow `(0, 4, 5, 3)` (or `(0, 3, 5, 4)`), the pair `K − 6`, `K − 0` certifies `K`
  (`isRupert_type16_06`).
* **Triangle closings** (Corollary 14.1, `isRupert_edgeTri`; Proposition 14.3 with `5`
  hidden, `isRupert_type16_06_tri`): a triangle rim with distinct depths is unimodal.

Not formalized: Lemma E′ and Proposition 14.2 (statements about all metrics), the metric
part of the converse (distinct depths and `G u = φ`), Lemma V, Corollary V1 and
Observation 14.4.
-/

namespace Minimality

open scoped RealInnerProductSpace
open Finset

/-! ### Lemma E: the depth core -/

/-- **Lemma E, (iii) ⇒ (ii) in parameter form.**  Over the crossing of the diagonals,
`e − d_v = μ u` with `e ∈ [a, b]`, `d_v = v + s (c − v)` and `u = w − v`; if `v`, `w` lie
weakly on opposite sides of the plane `abc` (and `u` is not parallel to it), then
`0 ≤ μ ≤ 1 − s`: the two closings can fail only in opposite directions. -/
theorem edgePair_param {v w a b c : ℝ³} {s t μ : ℝ} (hs1 : s ≤ 1)
    (hm : a + t • (b - a) - (v + s • (c - v)) = μ • (w - v))
    (hL : det3 (b - a) (c - a) (w - v) ≠ 0)
    (hE : det3 (b - a) (c - a) (v - a) * det3 (b - a) (c - a) (w - a) ≤ 0) :
    0 ≤ μ ∧ μ ≤ 1 - s := by
  have key : μ * det3 (b - a) (c - a) (w - a) =
      (μ - (1 - s)) * det3 (b - a) (c - a) (v - a) := by
    have e := congrArg (fun x => det3 (b - a) (c - a) x) hm
    simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul] at e ⊢
    linear_combination -e
  have hLe : det3 (b - a) (c - a) (w - v) =
      det3 (b - a) (c - a) (w - a) - det3 (b - a) (c - a) (v - a) := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  rw [hLe] at hL
  set Fv := det3 (b - a) (c - a) (v - a)
  set Fw := det3 (b - a) (c - a) (w - a)
  constructor
  · by_contra hμ
    push Not at hμ
    have h1 : (μ - (1 - s)) * (Fv * Fv) = μ * (Fv * Fw) := by linear_combination (-Fv) * key
    have p1 : 0 ≤ μ * (Fv * Fw) := mul_nonneg_of_nonpos_of_nonpos hμ.le hE
    have p3 : Fv * Fv ≤ 0 := by
      by_contra hc
      push Not at hc
      have := mul_neg_of_neg_of_pos (show μ - (1 - s) < 0 by linarith) hc
      linarith
    have hFv : Fv = 0 := mul_self_eq_zero.mp (le_antisymm p3 (mul_self_nonneg _))
    rw [hFv, mul_zero] at key
    have hFw : Fw = 0 := (mul_eq_zero.mp key).resolve_left hμ.ne
    exact hL (by rw [hFv, hFw]; ring)
  · by_contra hμ
    push Not at hμ
    have hμ0 : 0 < μ := by linarith
    have h1 : μ * (Fw * Fw) = (μ - (1 - s)) * (Fv * Fw) := by linear_combination Fw * key
    have p1 : (μ - (1 - s)) * (Fv * Fw) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) hE
    have p3 : Fw * Fw ≤ 0 := by
      by_contra hc
      push Not at hc
      have := mul_pos hμ0 hc
      linarith
    have hFw : Fw = 0 := mul_self_eq_zero.mp (le_antisymm p3 (mul_self_nonneg _))
    rw [hFw, mul_zero] at key
    have hFv : Fv = 0 :=
      (mul_eq_zero.mp key.symm).resolve_left (by linarith)
    exact hL (by rw [hFv, hFw]; ring)

/-! ### (ii) ⟺ (iii) -/

/-- The segment `[a, b]` meets the closed triangle `(v, w, c)`. -/
def SegMeetsTri (a b v w c : ℝ³) : Prop :=
  ∃ t α β γ : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ 0 ≤ α ∧ 0 ≤ β ∧ 0 ≤ γ ∧ α + β + γ = 1 ∧
    a + t • (b - a) = α • v + β • w + γ • c

/-- **Lemma E, (ii) ⟺ (iii)** (weak form): if the projections of `[v, c]` and `[a, b]` meet
along `u = w − v` and `u` is not parallel to the plane `abc`, the segment `[a, b]` meets the
closed triangle `(v, w, c)` iff `[a b c v] [a b c w] ≤ 0`. -/
theorem edgePair_tri_iff {v w a b c : ℝ³} (hm : SegMeet v c a b (w - v))
    (hL : det3 (b - a) (c - a) (w - v) ≠ 0) :
    SegMeetsTri a b v w c ↔
      det3 (b - a) (c - a) (v - a) * det3 (b - a) (c - a) (w - a) ≤ 0 := by
  constructor
  · rintro ⟨t, α, β, γ, ht0, ht1, hα, hβ, hγ, hsum, he⟩
    by_contra hpos
    push Not at hpos
    set Fv := det3 (b - a) (c - a) (v - a)
    set Fw := det3 (b - a) (c - a) (w - a)
    have key : α * Fv + β * Fw = 0 := by
      have e := congrArg (fun x => det3 (b - a) (c - a) (x - a)) he
      have hγ' : γ = 1 - α - β := by linarith
      subst hγ'
      simp only [Fv, Fw, det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
        smul_eq_mul] at e ⊢
      linear_combination -e
    -- `α = β = 0`, so `e = c` lies on `[a, b]` and `c − a ∥ b − a`
    have hab : α = 0 ∧ β = 0 := by
      have hFv0 : Fv ≠ 0 := by
        rintro h0; rw [h0, zero_mul] at hpos; exact lt_irrefl _ hpos
      rcases lt_or_gt_of_ne hFv0 with hv | hv
      · have hw : Fw < 0 := by nlinarith
        constructor <;> nlinarith [mul_nonneg hα (neg_nonneg.mpr hv.le),
          mul_nonneg hβ (neg_nonneg.mpr hw.le)]
      · have hw : 0 < Fw := by nlinarith
        constructor <;> nlinarith [mul_nonneg hα hv.le, mul_nonneg hβ hw.le]
    obtain ⟨rfl, rfl⟩ := hab
    have hγ1 : γ = 1 := by linarith
    subst hγ1
    apply hL
    have hc : c - a = t • (b - a) := by
      rw [zero_smul, zero_smul, zero_add, zero_add, one_smul] at he
      rw [← he]; abel
    rw [hc]
    simp only [det3_expand, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]; ring
  · intro hE
    obtain ⟨s, t, μ, hs0, hs1, ht0, ht1, h⟩ := hm
    obtain ⟨hμ0, hμ1⟩ := edgePair_param hs1 h hL hE
    refine ⟨t, 1 - s - μ, μ, s, ht0, ht1, by linarith, hμ0, hs0, by ring, ?_⟩
    rw [sub_eq_iff_eq_add] at h
    rw [h]; module

/-! ### The converse, at the level of depth functionals -/

/-! ### Corollary 14.1: the Rupert form -/

/-- A point strictly inside the 4-corner shadow `(v, a, c, b)` at the view `u` (strictly left
of its four sides). -/
def EdgeHidden (u v a c b z : ℝ³) : Prop :=
  0 < det3 (a - v) (z - v) u ∧ 0 < det3 (c - a) (z - a) u ∧ 0 < det3 (b - c) (z - c) u ∧
    0 < det3 (v - b) (z - b) u

/-- A *middle* of the edge crossing along `v w` (Theorem 8.9), on a face at `v w` with far end
`a` or `b`: over the side `q a` (or `b q`) of the shadow, on the chain from `v` (below the
chord from `v`, along `u = w − v`) or from `w` (above the chord from `w`). -/
def EdgeMid (v w a b m : ℝ³) : Prop :=
  ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ 0 < δ ∧
    (m = v + s • (a - v) - δ • (w - v) ∨ m = b + s • (v - b) - δ • (w - v) ∨
      m = w + s • (a - w) + δ • (w - v) ∨ m = b + s • (w - b) + δ • (w - v))

/-- A middle is a middle of the closing `K_v` (`w = v − (−1) u`). -/
theorem EdgeMid.edgeMiddle_v {v w a b m : ℝ³} (h : EdgeMid v w a b m) :
    EdgeMiddle (w - v) v w a b (-1) m := by
  obtain ⟨s, δ, hs0, hs1, hδ, h | h | h | h⟩ := h
  · exact ⟨v, s, -δ, Or.inl rfl, hs0, hs1, neg_ne_zero.mpr hδ.ne', Or.inl (by rw [h]; module)⟩
  · exact ⟨v, s, -δ, Or.inl rfl, hs0, hs1, neg_ne_zero.mpr hδ.ne', Or.inr (by rw [h]; module)⟩
  · exact ⟨w, s, δ, Or.inr ⟨rfl, by linarith⟩, hs0, hs1, hδ.ne', Or.inl h⟩
  · exact ⟨w, s, δ, Or.inr ⟨rfl, by linarith⟩, hs0, hs1, hδ.ne', Or.inr h⟩

/-- A middle is a middle of the closing `K_w` (`v = w − 1 u`). -/
theorem EdgeMid.edgeMiddle_w {v w a b m : ℝ³} (h : EdgeMid v w a b m) :
    EdgeMiddle (w - v) w v a b 1 m := by
  obtain ⟨s, δ, hs0, hs1, hδ, h | h | h | h⟩ := h
  · exact ⟨v, s, -δ, Or.inr ⟨rfl, by linarith⟩, hs0, hs1, neg_ne_zero.mpr hδ.ne',
      Or.inl (by rw [h]; module)⟩
  · exact ⟨v, s, -δ, Or.inr ⟨rfl, by linarith⟩, hs0, hs1, neg_ne_zero.mpr hδ.ne',
      Or.inr (by rw [h]; module)⟩
  · exact ⟨w, s, δ, Or.inl rfl, hs0, hs1, hδ.ne', Or.inl h⟩
  · exact ⟨w, s, δ, Or.inl rfl, hs0, hs1, hδ.ne', Or.inr h⟩

/-- Screen tests at `u = w − v` do not see the difference between `v` and `w`. -/
theorem det3_vw_both (x y v w : ℝ³) :
    det3 (x - w) (y - w) (w - v) = det3 (x - v) (y - v) (w - v) := by
  simp only [det3_expand, PiLp.sub_apply]; ring

theorem det3_vw_right (x y v w : ℝ³) :
    det3 x (w - y) (w - v) = det3 x (v - y) (w - v) := by
  simp only [det3_expand, PiLp.sub_apply]; ring

theorem det3_vw_left (x y v w : ℝ³) :
    det3 (w - y) x (w - v) = det3 (v - y) x (w - v) := by
  simp only [det3_expand, PiLp.sub_apply]; ring

theorem EdgeHidden.shift {v w a c b z : ℝ³} (h : EdgeHidden (w - v) v a c b z) :
    EdgeHidden (w - v) w a c b z := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨by rw [det3_vw_both]; exact h1, h2, h3, by rw [det3_vw_left]; exact h4⟩

/-! ### The wedge argument and Proposition 14.3 (type 16, the edge `06`) -/

/-! ### Triangle closings (Corollary 14.1, Proposition 14.3 with `5` hidden) -/

/-- A point strictly inside the triangular shadow `(v, a, b)` at the view `u`. -/
def TriHidden (u v a b z : ℝ³) : Prop :=
  0 < det3 (a - v) (z - v) u ∧ 0 < det3 (b - a) (z - a) u ∧ 0 < det3 (v - b) (z - b) u

end Minimality

end
