module

public import Minimality.Type16M
public import Minimality.OctAxis

@[expose] public section

/-!
# Edge pairs: Lemma E (§14)

`FEWER-FACES-PROOFS.md` §14, in Euclidean form (as §13 in `OctAxis.lean`): the paper's "at
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

/-- **Lemma E, (iii) ⇒ (i), Euclidean form.**  The projections of the diagonals `[v, c]` and
`[a, b]` meet along `u = w − v`, `u` is not parallel to the plane `abc`, and `v`, `w` lie
weakly on opposite sides of that plane.  Then the rims `(v, a, c, b)` and `(w, a, c, b)` are
not both depth-separated at `u`: `K_v` can fail only with `{a, b}` above `{v, c}`, `K_w` only
with `{w, c}` above `{a, b}`, and the two orders of `c` against `a`, `b` exclude each other. -/
theorem edgePair_not_both {v w a b c : ℝ³} (hm : SegMeet v c a b (w - v))
    (hL : det3 (b - a) (c - a) (w - v) ≠ 0)
    (hE : det3 (b - a) (c - a) (v - a) * det3 (b - a) (c - a) (w - a) ≤ 0) :
    ¬ (DepthSep v c a b (w - v) ∧ DepthSep w c a b (w - v)) := by
  rintro ⟨h1, h2⟩
  obtain ⟨s, t, μ, hs0, hs1, ht0, ht1, h⟩ := hm
  obtain ⟨hμ0, hμ1⟩ := edgePair_param hs1 h hL hE
  set u := w - v with hu
  have hu0 : u ≠ 0 := by
    intro h0; apply hL; rw [h0]; simp only [det3, inner_zero_right]
  have huu : 0 < ⟪u, u⟫ := real_inner_self_pos.mpr hu0
  have hw : ⟪u, u⟫ = ⟪w, u⟫ - ⟪v, u⟫ := by
    conv_lhs => rw [hu]
    rw [inner_sub_left]
  have i1 := congrArg (fun x => ⟪x, u⟫) h
  simp only [inner_sub_left, inner_seg, real_inner_smul_left] at i1
  obtain ⟨e1, e2⟩ := seg_bounds (x := ⟪a, u⟫) (y := ⟪b, u⟫) ht0 ht1
  obtain ⟨d1, d2⟩ := seg_bounds (x := ⟪v, u⟫) (y := ⟪c, u⟫) hs0 hs1
  obtain ⟨f1, f2⟩ := seg_bounds (x := ⟪w, u⟫) (y := ⟪c, u⟫) hs0 hs1
  have p1 : 0 ≤ μ * ⟪u, u⟫ := mul_nonneg hμ0 huu.le
  have p2 : 0 ≤ (1 - s - μ) * ⟪u, u⟫ := mul_nonneg (by linarith) huu.le
  have m1 := min_le_left ⟪a, u⟫ ⟪b, u⟫
  have m2 := le_max_left ⟪a, u⟫ ⟪b, u⟫
  have m3 := le_max_right ⟪v, u⟫ ⟪c, u⟫
  have m4 := min_le_right ⟪w, u⟫ ⟪c, u⟫
  simp only [DepthSep] at h1 h2
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · nlinarith
  · linarith
  · nlinarith
  · nlinarith

/-- **Lemma E (i), Euclidean form**: under the hypotheses of `edgePair_not_both`, with
distinct depths on both rims, one of the two closings `(v, a, c, b)`, `(w, a, c, b)` has
cyclically unimodal depths at `u = w − v`. -/
theorem edgePair_unimodal {v w a b c : ℝ³} (hm : SegMeet v c a b (w - v))
    (hL : det3 (b - a) (c - a) (w - v) ≠ 0)
    (hE : det3 (b - a) (c - a) (v - a) * det3 (b - a) (c - a) (w - a) ≤ 0)
    (hz₁ : [⟪v, w - v⟫, ⟪a, w - v⟫, ⟪c, w - v⟫, ⟪b, w - v⟫].Nodup)
    (hz₂ : [⟪w, w - v⟫, ⟪a, w - v⟫, ⟪c, w - v⟫, ⟪b, w - v⟫].Nodup) :
    IsCyclicUnimodal (quad ⟪v, w - v⟫ ⟪a, w - v⟫ ⟪c, w - v⟫ ⟪b, w - v⟫) ∨
      IsCyclicUnimodal (quad ⟪w, w - v⟫ ⟪a, w - v⟫ ⟪c, w - v⟫ ⟪b, w - v⟫) := by
  have nb := edgePair_not_both hm hL hE
  have key : ∀ y : ℝ³, [⟪y, w - v⟫, ⟪a, w - v⟫, ⟪c, w - v⟫, ⟪b, w - v⟫].Nodup →
      ¬ DepthSep y c a b (w - v) →
      IsCyclicUnimodal (quad ⟪y, w - v⟫ ⟪a, w - v⟫ ⟪c, w - v⟫ ⟪b, w - v⟫) := by
    intro y hz hsep
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, and_true] at hz
    obtain ⟨⟨z1, z2, z3⟩, ⟨z4, z5⟩, z6, -⟩ := hz
    have hov := overlap4_of_not_depthSep hsep z1 z2 z3 z4 z5 z6
    exact isCyclicUnimodal_four (quad_injective z1 z2 z3 z4 z5 z6) hov
  by_cases h1 : DepthSep v c a b (w - v)
  · exact Or.inr (key w hz₂ fun h2 => nb ⟨h1, h2⟩)
  · exact Or.inl (key v hz₁ h1)

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

/-- **Lemma E, not (iii) ⇒ not (i), for depth functionals.**  If `v` and `w` lie strictly on
the same side of the plane `abc` (and the projections of the diagonals meet along
`u = w − v`), some linear functional `φ = ⟪·, g⟫` with `φ(u) > 0` depth-separates both rims:
`{v, c}` above `{a, b}` (if `[a, b]` passes below `[v, c]`) or `{a, b}` above `{w, c}`.  The
functional is the normal of the two diagonal directions, so the depths of the diagonals'
ends tie in pairs; the paper perturbs it to distinct depths, and realises it as `G u` for a
metric `G` (§13.0); that part is not formalized. -/
theorem edgePair_converse {v w a b c : ℝ³} (hm : SegMeet v c a b (w - v))
    (hE : 0 < det3 (b - a) (c - a) (v - a) * det3 (b - a) (c - a) (w - a)) :
    ∃ g : ℝ³, 0 < ⟪w - v, g⟫ ∧ DepthSep v c a b g ∧ DepthSep w c a b g := by
  obtain ⟨s, t, μ, hs0, hs1, ht0, ht1, h⟩ := hm
  set Fv := det3 (b - a) (c - a) (v - a)
  set Fw := det3 (b - a) (c - a) (w - a)
  have key : μ * Fw = (μ - (1 - s)) * Fv := by
    have e := congrArg (fun x => det3 (b - a) (c - a) x) h
    simp only [Fv, Fw, det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
      smul_eq_mul] at e ⊢
    linear_combination -e
  have hFv : Fv ≠ 0 := by rintro h0; rw [h0, zero_mul] at hE; exact lt_irrefl _ hE
  have hFw : Fw ≠ 0 := by rintro h0; rw [h0, mul_zero] at hE; exact lt_irrefl _ hE
  -- `μ` and `μ − (1 − s)` have one sign
  have hμ : 0 < μ * (μ - (1 - s)) := by
    have h1 : μ * (μ - (1 - s)) * (Fv * Fw) = (μ - (1 - s)) * (μ - (1 - s)) * (Fv * Fv) := by
      linear_combination (μ - (1 - s)) * Fv * key
    have hμ0 : μ ≠ 0 := by
      intro hμ0
      rw [hμ0] at key h
      have h1s : (1 - s) * Fv = 0 := by linear_combination key
      have hs : s = 1 := by linarith [(mul_eq_zero.mp h1s).resolve_right hFv]
      rw [hs] at h
      apply hFv
      have e := congrArg (fun x => det3 (b - a) x (v - a)) h
      simp only [Fv, det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
        smul_eq_mul] at e ⊢
      linear_combination -e
    have hμ1 : μ - (1 - s) ≠ 0 := by
      intro h0; rw [h0, zero_mul] at key
      exact hFw ((mul_eq_zero.mp key).resolve_left hμ0)
    have := mul_pos (mul_self_pos.mpr hμ1) (mul_self_pos.mpr hFv)
    rw [← h1] at this
    exact pos_of_mul_pos_left this hE.le
  set u := w - v with hu
  have hwg : ∀ g : ℝ³, ⟪w, g⟫ = ⟪v, g⟫ + ⟪u, g⟫ := by
    intro g; rw [hu, inner_sub_left]; ring
  rcases lt_or_gt_of_ne (show μ ≠ 0 by rintro rfl; simp at hμ) with hneg | hpos
  · -- `μ < 0`: `[a, b]` passes below `[v, c]`; `n = (c − v) × (b − a)`
    set n := cross (c - v) (b - a)
    have hnc : ⟪c, n⟫ = ⟪v, n⟫ := by
      have : ⟪c - v, n⟫ = 0 := by
        rw [real_inner_comm]; show det3 (c - v) (b - a) (c - v) = 0
        simp only [det3_expand, PiLp.sub_apply]; ring
      rw [inner_sub_left] at this; linarith
    have hnb : ⟪b, n⟫ = ⟪a, n⟫ := by
      have : ⟪b - a, n⟫ = 0 := by
        rw [real_inner_comm]; show det3 _ (b - a) (b - a) = 0
        simp only [det3_expand, PiLp.sub_apply]; ring
      rw [inner_sub_left] at this; linarith
    have hK : ⟪v, n⟫ - ⟪a, n⟫ = -Fv := by
      rw [← inner_sub_left, real_inner_comm]
      show det3 (c - v) (b - a) (v - a) = -Fv
      simp only [Fv, det3_expand, PiLp.sub_apply]; ring
    have hun : μ * ⟪u, n⟫ = Fv := by
      have e := congrArg (fun x => ⟪x, n⟫) h
      simp only [inner_sub_left, inner_seg, real_inner_smul_left, hnc, hnb] at e
      linarith
    -- `σ = −sign Fv`
    rcases lt_or_gt_of_ne hFv with hv | hv
    · refine ⟨n, ?_, ?_, ?_⟩
      · nlinarith
      · right; simp only [hnc, hnb, max_self, min_self]; linarith
      · right
        have : 0 < ⟪u, n⟫ := by nlinarith
        simp only [hnc, hnb, max_self, lt_min_iff, hwg n]; constructor <;> linarith
    · refine ⟨-n, ?_, ?_, ?_⟩
      · rw [inner_neg_right]; nlinarith
      · right; simp only [inner_neg_right, hnc, hnb, max_self, min_self]; linarith
      · right
        have : ⟪u, n⟫ < 0 := by nlinarith
        simp only [inner_neg_right, hnc, hnb, max_self, lt_min_iff, hwg n]
        constructor <;> linarith
  · -- `μ > 1 − s`: `[a, b]` passes above `[w, c]`; `n = (c − w) × (b − a)`
    have hμ' : 0 < μ - (1 - s) := by
      by_contra hc; push Not at hc; nlinarith
    set n := cross (c - w) (b - a)
    have hnc : ⟪c, n⟫ = ⟪w, n⟫ := by
      have : ⟪c - w, n⟫ = 0 := by
        rw [real_inner_comm]; show det3 (c - w) (b - a) (c - w) = 0
        simp only [det3_expand, PiLp.sub_apply]; ring
      rw [inner_sub_left] at this; linarith
    have hnb : ⟪b, n⟫ = ⟪a, n⟫ := by
      have : ⟪b - a, n⟫ = 0 := by
        rw [real_inner_comm]; show det3 _ (b - a) (b - a) = 0
        simp only [det3_expand, PiLp.sub_apply]; ring
      rw [inner_sub_left] at this; linarith
    have hK : ⟪w, n⟫ - ⟪a, n⟫ = -Fw := by
      rw [← inner_sub_left, real_inner_comm]
      show det3 (c - w) (b - a) (w - a) = -Fw
      simp only [Fw, det3_expand, PiLp.sub_apply]; ring
    have hun : (μ - (1 - s)) * ⟪u, n⟫ = Fw := by
      have h' : a + t • (b - a) - (w + s • (c - w)) = (μ - (1 - s)) • u := by
        rw [sub_smul, ← h, hu]; module
      have e := congrArg (fun x => ⟪x, n⟫) h'
      simp only [inner_sub_left, inner_seg, real_inner_smul_left, hnc, hnb] at e
      linarith
    rcases lt_or_gt_of_ne hFw with hv | hv
    · refine ⟨-n, ?_, ?_, ?_⟩
      · rw [inner_neg_right]; nlinarith
      · left
        have : ⟪u, n⟫ < 0 := by nlinarith
        simp only [inner_neg_right, hnc, hnb, min_self, max_lt_iff]
        constructor <;> linarith [hwg n]
      · left; simp only [inner_neg_right, hnc, hnb, max_self, min_self]; linarith
    · refine ⟨n, ?_, ?_, ?_⟩
      · nlinarith
      · left
        have : 0 < ⟪u, n⟫ := by nlinarith
        simp only [hnc, hnb, min_self, max_lt_iff]
        constructor <;> linarith [hwg n]
      · left; simp only [hnc, hnb, max_self, min_self]; linarith

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

/-- **One closing, certified** (Theorem 8.9 with Theorem 7.3): the rim `(y, a, c, b)` is a
strictly convex counterclockwise quadrilateral at `u`, the other axle end is `o = y − h u`,
every other point not in `M` is strictly inside, the middles `M` are those of Theorem 8.9,
the depths are distinct and the diagonals `[y, c]`, `[a, b]` are not depth-separated.  Then
`V` is Rupert (no horizontal double normal of `V − o` at `u` assumed). -/
theorem isRupert_edgePair_closing (V M : Finset ℝ³) {u y o a b c : ℝ³} {h : ℝ} (hh : h ≠ 0)
    (ho : o = y - h • u) (hu : u ≠ 0) (hoV : o ∈ V) (hyV : y ∈ V) (haV : a ∈ V) (hbV : b ∈ V)
    (hcV : c ∈ V) (hyM : y ∉ M) (haM : a ∉ M) (hbM : b ∉ M) (hcM : c ∉ M)
    (q₁ : 0 < det3 (a - y) (c - y) u) (q₂ : 0 < det3 (c - a) (b - a) u)
    (q₃ : 0 < det3 (b - c) (y - c) u) (q₄ : 0 < det3 (y - b) (a - b) u)
    (hrest : ∀ z ∈ V, z ∉ M → z ≠ o → z ≠ y → z ≠ a → z ≠ c → z ≠ b → EdgeHidden u y a c b z)
    (hz : [⟪y, u⟫, ⟪a, u⟫, ⟪c, u⟫, ⟪b, u⟫].Nodup) (hsep : ¬ DepthSep y c a b u)
    (hM : ∀ m ∈ M, EdgeMiddle u y o a b h m) (hnd : NoHDNAt (V.erase o) u) : IsRupert V := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hz
  obtain ⟨⟨z1, z2, z3⟩, ⟨z4, z5⟩, z6, -⟩ := hz
  have hov := overlap4_of_not_depthSep hsep z1 z2 z3 z4 z5 z6
  have i2 : det3 (a - y) (b - y) u = det3 (y - b) (a - b) u := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have i4 : det3 (c - a) (y - a) u = det3 (a - y) (c - y) u := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have i6 : det3 (b - c) (a - c) u = det3 (c - a) (b - a) u := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have i8 : det3 (y - b) (c - b) u = det3 (b - c) (y - c) u := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  refine isRupert_quad_rim_int V M u hu h hh ho hoV hyV hcV haV hbV hyM haM hcM hbM q₁
    (by rw [i2]; exact q₄) q₂ (by rw [i4]; exact q₁) q₃ (by rw [i6]; exact q₂) q₄
    (by rw [i8]; exact q₃) hrest (quad_injective z1 z2 z3 z4 z5 z6) ?_ hM hnd
  simp only [NWS4, quad_0, quad_1, quad_2, quad_3]
  exact ⟨hov.1, hov.2.1⟩

/-- **Corollary 14.1 (Rupert), Euclidean form.**  An edge crossing along `v w` at the view
`u = w − v`: the shadow is the strictly convex counterclockwise quadrilateral
`(q, P a, P c, P b)` (`q = P v = P w`; the triple tests `q₁`–`q₄`), and every point of `V`
is `v`, `w`, `a`, `b`, `c`, a middle of Theorem 8.9 (`EdgeMid`) or strictly inside the shadow
(`EdgeHidden`) — this is (G1) with the far path `a, c, b`.  If `v` and `w` lie weakly on
opposite sides of the plane `abc` (`[a b c v] [a b c w] ≤ 0`: Lemma E (iii), or a planar
closing), both rims have distinct depths (G2), and neither closing has a horizontal double
normal at `u`, then `V` is Rupert: `K_v` or `K_w` is unimodal (Lemma E), and Theorem 8.9 with
Theorem 7.3 applies. -/
theorem isRupert_edgePair {v w a b c : ℝ³} (V : Finset ℝ³)
    (hvV : v ∈ V) (hwV : w ∈ V) (haV : a ∈ V) (hbV : b ∈ V) (hcV : c ∈ V)
    (q₁ : 0 < det3 (a - v) (c - v) (w - v)) (q₂ : 0 < det3 (c - a) (b - a) (w - v))
    (q₃ : 0 < det3 (b - c) (v - c) (w - v)) (q₄ : 0 < det3 (v - b) (a - b) (w - v))
    (hE : det3 (b - a) (c - a) (v - a) * det3 (b - a) (c - a) (w - a) ≤ 0)
    (hz₁ : [⟪v, w - v⟫, ⟪a, w - v⟫, ⟪c, w - v⟫, ⟪b, w - v⟫].Nodup)
    (hz₂ : [⟪w, w - v⟫, ⟪a, w - v⟫, ⟪c, w - v⟫, ⟪b, w - v⟫].Nodup)
    (hV : ∀ z ∈ V, z = v ∨ z = w ∨ z = a ∨ z = b ∨ z = c ∨ EdgeMid v w a b z ∨
      EdgeHidden (w - v) v a c b z)
    (hnd₁ : NoHDNAt (V.erase w) (w - v)) (hnd₂ : NoHDNAt (V.erase v) (w - v)) :
    IsRupert V := by
  classical
  set M := V.filter (fun z => EdgeMid v w a b z ∧ z ≠ v ∧ z ≠ w ∧ z ≠ a ∧ z ≠ b ∧ z ≠ c)
    with hM
  have hu : w - v ≠ 0 := by
    intro h0; rw [h0] at q₁; simp only [det3, inner_zero_right, lt_irrefl] at q₁
  have nM : ∀ z, z = v ∨ z = w ∨ z = a ∨ z = b ∨ z = c → z ∉ M := by
    intro z hz hzM
    obtain ⟨-, -, h1, h2, h3, h4, h5⟩ := mem_filter.mp hzM
    rcases hz with rfl | rfl | rfl | rfl | rfl <;> simp_all
  have hsm : SegMeet v c a b (w - v) := by
    refine segMeet_of_sides ?_ ?_
    · have e1 : det3 (c - v) (a - v) (w - v) = -det3 (a - v) (c - v) (w - v) := by
        simp only [det3_expand, PiLp.sub_apply]; ring
      have e2 : det3 (c - v) (b - v) (w - v) = det3 (b - c) (v - c) (w - v) := by
        simp only [det3_expand, PiLp.sub_apply]; ring
      rw [e1, e2]; nlinarith
    · have e1 : det3 (b - a) (v - a) (w - v) = det3 (v - b) (a - b) (w - v) := by
        simp only [det3_expand, PiLp.sub_apply]; ring
      have e2 : det3 (b - a) (c - a) (w - v) = -det3 (c - a) (b - a) (w - v) := by
        simp only [det3_expand, PiLp.sub_apply]; ring
      rw [e1, e2]; nlinarith
  have hL : det3 (b - a) (c - a) (w - v) ≠ 0 := by
    have e2 : det3 (b - a) (c - a) (w - v) = -det3 (c - a) (b - a) (w - v) := by
      simp only [det3_expand, PiLp.sub_apply]; ring
    rw [e2]; linarith
  have nb := edgePair_not_both hsm hL hE
  -- the points that are not corners, middles or the other axle end are hidden
  have rest : ∀ z ∈ V, z ∉ M → z ≠ v → z ≠ w → z ≠ a → z ≠ c → z ≠ b →
      EdgeHidden (w - v) v a c b z := by
    intro z hz hzM h1 h2 h3 h4 h5
    rcases hV z hz with e | e | e | e | e | hmid | hid
    · exact absurd e h1
    · exact absurd e h2
    · exact absurd e h3
    · exact absurd e h5
    · exact absurd e h4
    · exact absurd (mem_filter.mpr ⟨hz, hmid, h1, h2, h3, h5, h4⟩) hzM
    · exact hid
  by_cases h1 : DepthSep v c a b (w - v)
  · -- `K_w` is unimodal
    have h2 : ¬ DepthSep w c a b (w - v) := fun h2 => nb ⟨h1, h2⟩
    refine isRupert_edgePair_closing V M (y := w) (o := v) (h := 1) one_ne_zero
      (by rw [one_smul]; abel) hu hvV hwV haV hbV hcV (nM w (by tauto)) (nM a (by tauto))
      (nM b (by tauto)) (nM c (by tauto)) (by rw [det3_vw_both]; exact q₁) q₂
      (by rw [det3_vw_right]; exact q₃) (by rw [det3_vw_left]; exact q₄) ?_ hz₂ h2 ?_
      hnd₂
    · intro z hz hzM h1 h2 h3 h4 h5
      exact (rest z hz hzM h1 h2 h3 h4 h5).shift
    · intro m hm
      exact (mem_filter.mp hm).2.1.edgeMiddle_w
  · -- `K_v` is unimodal
    refine isRupert_edgePair_closing V M (y := v) (o := w) (h := -1) (by norm_num)
      (by rw [neg_one_smul, sub_neg_eq_add]; abel) hu hwV hvV haV hbV hcV (nM v (by tauto))
      (nM a (by tauto)) (nM b (by tauto)) (nM c (by tauto)) q₁ q₂ q₃ q₄ ?_ hz₁ h1 ?_ hnd₁
    · intro z hz hzM h1 h2 h3 h4 h5
      exact rest z hz hzM h2 h1 h3 h4 h5
    · intro m hm
      exact (mem_filter.mp hm).2.1.edgeMiddle_v

/-! ### The wedge argument and Proposition 14.3 (type 16, the edge `06`) -/

/-- **The wedge argument** (§14.3).  Two face planes `f_A`, `f_B` of a convex body meet in the
edge line `p q`; `r` lies strictly beneath both, `v` on the first and strictly beneath the
second, `w` on the second and strictly beneath the first.  Then `v` and `w` lie strictly on
opposite sides of the plane `pqr`: the affine functions vanishing on the line `p q` form a
plane, `[p q r ·] = α f_A + β f_B` with `α β < 0` (it vanishes at `r`). -/
theorem wedge_sep {fA fB : ℝ³ → ℝ} {NA NB : ℝ³} (hA : ∀ y z, fA y - fA z = ⟪NA, y - z⟫)
    (hB : ∀ y z, fB y - fB z = ⟪NB, y - z⟫) {p q r v w : ℝ³} (hpq : p ≠ q)
    (hAp : fA p = 0) (hAq : fA q = 0) (hBp : fB p = 0) (hBq : fB q = 0)
    (hAr : fA r < 0) (hBr : fB r < 0) (hAv : fA v = 0) (hBv : fB v < 0)
    (hBw : fB w = 0) (hAw : fA w < 0) :
    det3 (r - p) (q - p) (v - p) * det3 (r - p) (q - p) (w - p) < 0 := by
  set gv := det3 (r - p) (q - p) (v - p)
  set gw := det3 (r - p) (q - p) (w - p)
  have cyc : ∀ x : ℝ³, det3 (r - p) (q - p) (x - p) = det3 (q - p) (x - p) (r - p) := by
    intro x; simp only [det3_expand, PiLp.sub_apply]; ring
  have hgv : gv ≠ 0 := by
    intro h0
    have hc := cross_ne_zero_of_affine hB hpq hBp hBq hBv
    have := affine_zero_of_coplanar hA hAp hAq hAv hc (by rw [← cyc]; exact h0)
    linarith
  have hgw : gw ≠ 0 := by
    intro h0
    have hc := cross_ne_zero_of_affine hA hpq hAp hAq hAw
    have := affine_zero_of_coplanar hB hBp hBq hBw hc (by rw [← cyc]; exact h0)
    linarith
  have hcr := cramer (r - p) (q - p) (v - p) (w - p)
  have lin : ∀ (f : ℝ³ → ℝ) (N : ℝ³), (∀ y z, f y - f z = ⟪N, y - z⟫) → f p = 0 →
      ∀ x, ⟪N, x - p⟫ = f x := by
    intro f N hf hp x; rw [← hf, hp, sub_zero]
  have eA := congrArg (fun x => ⟪NA, x⟫) hcr
  have eB := congrArg (fun x => ⟪NB, x⟫) hcr
  simp only [inner_add_right, real_inner_smul_right, lin fA NA hA hAp, lin fB NB hB hBp] at eA eB
  rw [hAq, hAv] at eA
  rw [hBq, hBw] at eB
  set c1 := det3 (w - p) (q - p) (v - p)
  -- `gv fA(w) = c1 fA(r)` and `0 = c1 fB(r) + gw fB(v)`
  have k : gv * gw * (fA w * fB r) = -(gw * gw) * (fB v * fA r) := by
    have e1 : gv * fA w = c1 * fA r := by linarith
    have e2 : c1 * fB r = -(gw * fB v) := by linarith
    linear_combination (gw * fB r) * e1 + (gw * fA r) * e2
  have hpos : 0 < fA w * fB r := mul_pos_of_neg_of_neg hAw hBr
  have hneg : -(gw * gw) * (fB v * fA r) < 0 := by
    have := mul_pos (mul_self_pos.mpr hgw) (mul_pos_of_neg_of_neg hBv hAr)
    linarith
  rw [← k] at hneg
  by_contra hc
  push Not at hc
  nlinarith

/-- **Proposition 14.3, the sign (E06)**: for every type-16 point set, `0` and `6` lie
strictly on opposite sides of the plane `345` (the wedge of `K` at the edge `35`, between
the quadrilaterals `0235` and `1356`, with `4` strictly beneath both). -/
theorem type16_sep06 {x : Fin 7 → ℝ³} (T : Type16 x) :
    det3 (x 4 - x 3) (x 5 - x 3) (x 0 - x 3) * det3 (x 4 - x 3) (x 5 - x 3) (x 6 - x 3) < 0 :=
  wedge_sep T.q0235.hN T.q1356.hN (T.inj.ne (by decide))
    (T.q0235.zero 3 (by decide)) (T.q0235.zero 5 (by decide))
    (T.q1356.zero 3 (by decide)) (T.q1356.zero 5 (by decide))
    (T.q0235.neg 4 (by decide)) (T.q1356.neg 4 (by decide))
    (T.q0235.zero 0 (by decide)) (T.q1356.neg 0 (by decide))
    (T.q1356.zero 6 (by decide)) (T.q0235.neg 6 (by decide))

/-- **Proposition 14.3 (E06), Rupert form.**  Type 16 at the view `u = x 6 − x 0` along the
edge `06` (faces `036`, `046`, no middles; `K_0 = K − 6`, `K_6 = K − 0`).  Suppose the shadow
is the strictly convex counterclockwise quadrilateral `(q, P a, P 5, P b)` with
`{a, b} = {x 4, x 3}` (the far path `4, 5, 3`, so `5` is a corner) and `1`, `2` strictly
inside it (not corners, and (G1)).  With distinct depths on both rims and no horizontal
double normal at `u` for either closing, `K` is Rupert: by `type16_sep06` and Lemma E one of
`K − 6`, `K − 0` is unimodal. -/
theorem isRupert_type16_06 {x : Fin 7 → ℝ³} (T : Type16 x) {a b : ℝ³}
    (hab : (a = x 4 ∧ b = x 3) ∨ (a = x 3 ∧ b = x 4))
    (q₁ : 0 < det3 (a - x 0) (x 5 - x 0) (x 6 - x 0))
    (q₂ : 0 < det3 (x 5 - a) (b - a) (x 6 - x 0))
    (q₃ : 0 < det3 (b - x 5) (x 0 - x 5) (x 6 - x 0))
    (q₄ : 0 < det3 (x 0 - b) (a - b) (x 6 - x 0))
    (h₁ : EdgeHidden (x 6 - x 0) (x 0) a (x 5) b (x 1))
    (h₂ : EdgeHidden (x 6 - x 0) (x 0) a (x 5) b (x 2))
    (hz₁ : [⟪x 0, x 6 - x 0⟫, ⟪a, x 6 - x 0⟫, ⟪x 5, x 6 - x 0⟫, ⟪b, x 6 - x 0⟫].Nodup)
    (hz₂ : [⟪x 6, x 6 - x 0⟫, ⟪a, x 6 - x 0⟫, ⟪x 5, x 6 - x 0⟫, ⟪b, x 6 - x 0⟫].Nodup)
    (hnd₁ : NoHDNAt ((univ.image x).erase (x 6)) (x 6 - x 0))
    (hnd₂ : NoHDNAt ((univ.image x).erase (x 0)) (x 6 - x 0)) :
    IsRupert (univ.image x) := by
  have hs := type16_sep06 T
  have hmem : ∀ i, x i ∈ univ.image x := fun i => mem_image_of_mem x (mem_univ i)
  have haV : a ∈ univ.image x := by rcases hab with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> exact hmem _
  have hbV : b ∈ univ.image x := by rcases hab with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> exact hmem _
  refine isRupert_edgePair (univ.image x) (hmem 0) (hmem 6) haV hbV (hmem 5) q₁ q₂ q₃ q₄ ?_
    hz₁ hz₂ ?_ hnd₁ hnd₂
  · have e : ∀ y : ℝ³, det3 (x 3 - x 4) (x 5 - x 4) (y - x 4) =
        -det3 (x 4 - x 3) (x 5 - x 3) (y - x 3) := by
      intro y; simp only [det3_expand, PiLp.sub_apply]; ring
    rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [e, e]; nlinarith
    · nlinarith
  · intro z hz
    obtain ⟨i, -, rfl⟩ := mem_image.mp hz
    rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> fin_cases i <;>
      first
        | exact Or.inl rfl
        | exact Or.inr (Or.inl rfl)
        | exact Or.inr (Or.inr (Or.inl rfl))
        | exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
        | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
        | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h₁)))))
        | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h₂)))))

/-! ### Triangle closings (Corollary 14.1, Proposition 14.3 with `5` hidden) -/

/-- A point strictly inside the triangular shadow `(v, a, b)` at the view `u`. -/
def TriHidden (u v a b z : ℝ³) : Prop :=
  0 < det3 (a - v) (z - v) u ∧ 0 < det3 (b - a) (z - a) u ∧ 0 < det3 (v - b) (z - b) u

/-- **A triangle closing (Corollary 14.1)**: at the edge crossing along `v w` (view
`u = w − v`), the shadow is the counterclockwise triangle `(q, P a, P b)` and every other
point of `V` is a middle (`EdgeMid`) or strictly inside.  A triangle rim with distinct depths
is unimodal, so without a horizontal double normal of `K_v` at `u`, `V` is Rupert (Theorem 8.9
with Theorem 7.3). -/
theorem isRupert_edgeTri {v w a b : ℝ³} (V : Finset ℝ³)
    (hvV : v ∈ V) (hwV : w ∈ V) (haV : a ∈ V) (hbV : b ∈ V)
    (hT : 0 < det3 (a - v) (b - v) (w - v))
    (hz : [⟪v, w - v⟫, ⟪a, w - v⟫, ⟪b, w - v⟫].Nodup)
    (hV : ∀ z ∈ V, z = v ∨ z = w ∨ z = a ∨ z = b ∨ EdgeMid v w a b z ∨
      TriHidden (w - v) v a b z)
    (hnd : NoHDNAt (V.erase w) (w - v)) : IsRupert V := by
  classical
  set M := V.filter (fun z => EdgeMid v w a b z ∧ z ≠ v ∧ z ≠ w ∧ z ≠ a ∧ z ≠ b) with hM
  have hu : w - v ≠ 0 := by
    intro h0; rw [h0] at hT; simp only [det3, inner_zero_right, lt_irrefl] at hT
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hz
  obtain ⟨⟨z1, z2⟩, z3, -⟩ := hz
  obtain ⟨b0, b1, b2⟩ := zmod3_add_one
  have i1 : det3 (b - a) (v - a) (w - v) = det3 (a - v) (b - v) (w - v) := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have i2 : det3 (v - b) (a - b) (w - v) = det3 (a - v) (b - v) (w - v) := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  refine isRupert_of_edgeView V M (w - v) hu (k := 3) le_rfl (tri v a b) 0 w (-1) hwV
    (by rw [tri_0, neg_one_smul, sub_neg_eq_add]; abel) (by norm_num) ?_ ?_ ?_ ?_ ?_ hnd ?_
  · intro i; rcases zmod3_cases i with rfl | rfl | rfl
    exacts [hvV, haV, hbV]
  · intro i hi
    obtain ⟨-, -, h1, -, h3, h4⟩ := mem_filter.mp hi
    rcases zmod3_cases i with rfl | rfl | rfl
    exacts [h1 rfl, h3 rfl, h4 rfl]
  · intro i j hi hj
    rcases zmod3_pairs i j hi hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp only [b0, b1, b2, tri_0, tri_1, tri_2, i1, i2]
    exacts [hT, hT, hT]
  · intro z hz hzM hzw hzx i
    have h0 := hzx 0; have h1 := hzx 1; have h2 := hzx 2
    simp only [tri_0, tri_1, tri_2] at h0 h1 h2
    rcases hV z hz with e | e | e | e | hmid | ⟨r1, r2, r3⟩
    · exact absurd e h0
    · exact absurd e hzw
    · exact absurd e h1
    · exact absurd e h2
    · exact absurd (mem_filter.mpr ⟨hz, hmid, h0, hzw, h1, h2⟩) hzM
    · rcases zmod3_cases i with rfl | rfl | rfl <;> simp only [b0, b1, b2, tri_0, tri_1, tri_2]
      exacts [r1, r2, r3]
  · rw [tri_inner]
    exact isCyclicUnimodal_three (tri_injective z1 z2 z3)
  · intro m hm
    rw [zmod3_zero_add_one, zmod3_zero_sub_one, tri_0, tri_1, tri_2]
    exact (mem_filter.mp hm).2.1.edgeMiddle_v

/-- **Proposition 14.3 with `5` hidden.**  Type 16 at the view `u = x 6 − x 0`: if the shadow
is the counterclockwise triangle `(q, P a, P b)` with `{a, b} = {x 4, x 3}` and `1`, `2`, `5`
are strictly inside it, the rims are triangles, and with distinct depths on the rim
`(0, a, b)` and no horizontal double normal of `K − 6` at `u`, `K` is Rupert. -/
theorem isRupert_type16_06_tri {x : Fin 7 → ℝ³} {a b : ℝ³}
    (hab : (a = x 4 ∧ b = x 3) ∨ (a = x 3 ∧ b = x 4))
    (hT : 0 < det3 (a - x 0) (b - x 0) (x 6 - x 0))
    (h₁ : TriHidden (x 6 - x 0) (x 0) a b (x 1)) (h₂ : TriHidden (x 6 - x 0) (x 0) a b (x 2))
    (h₅ : TriHidden (x 6 - x 0) (x 0) a b (x 5))
    (hz : [⟪x 0, x 6 - x 0⟫, ⟪a, x 6 - x 0⟫, ⟪b, x 6 - x 0⟫].Nodup)
    (hnd : NoHDNAt ((univ.image x).erase (x 6)) (x 6 - x 0)) :
    IsRupert (univ.image x) := by
  have hmem : ∀ i, x i ∈ univ.image x := fun i => mem_image_of_mem x (mem_univ i)
  have haV : a ∈ univ.image x := by rcases hab with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> exact hmem _
  have hbV : b ∈ univ.image x := by rcases hab with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> exact hmem _
  refine isRupert_edgeTri (univ.image x) (hmem 0) (hmem 6) haV hbV hT hz ?_ hnd
  intro z hz
  obtain ⟨i, -, rfl⟩ := mem_image.mp hz
  rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> fin_cases i <;>
    first
      | exact Or.inl rfl
      | exact Or.inr (Or.inl rfl)
      | exact Or.inr (Or.inr (Or.inl rfl))
      | exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h₁))))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h₂))))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h₅))))

end Minimality

end
