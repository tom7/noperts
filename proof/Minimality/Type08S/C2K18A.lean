module

public import Minimality.Type08S.C2K17F2A

@[expose] public section


/-!
# K18 / A: the general tie-break lemmas (cone cells with a ray witness)

A frame lex cell (`k8_cell_gen` pattern) whose first-order tests and lex unimodality hold on an **open polyhedral
cone** of tilts `(v1, v2)` (a finite list `L` of strict linear inequalities `0 < l.1 v1 + l.2 v2`).  A depth tie
`z p = z q` at the view is broken by the tilt through the linear functional
`m = (⟪p-q, P⟫, ⟪p-q, Q⟫)` (`k8_wdiff`): requiring `w p < w q` is one more entry of `L`.

* `k18_cone_of_ray`: if every functional of `L` is lex positive at a ray `ρ` in the direction `δ`
  (`0 < l·ρ`, or `l·ρ = 0 ∧ 0 < l·δ`), then `ρ + ε δ` lies in the open cone for all small `ε > 0`.
* `k18_cone_cell`: cone hypotheses + a lex-positive ray witness ⇒ `HasLexCellAt V r` (no segment bookkeeping).
* `k18_tie_two`: **the two-cell tie lemma**.  Two cells at the same view and frame whose cones touch along a common
  ray `ρ` (each cone's own functionals are lex positive at `ρ` in its own direction `δᵢ`), where cell 1 needs the
  tie functional `m > 0` and cell 2 needs `m < 0`: if `m·ρ ≠ 0` one of them is a lex cell.  The leftover is
  `m·ρ = 0` (one more literal), or second order: `k18_tie_two'` decides `m·ρ = 0` by the signs of `m·δᵢ`.
* `k18_tie_one`: one cell whose cone has a ray where the tie functional is lex positive.

When the hypotheses fail: the two cones lie on opposite sides of the tie line `m = 0` with the wrong signs
(`C₁ ⊆ {m ≤ 0}`, `C₂ ⊆ {m ≥ 0}`; K14's H2 tie: pentagon cone `W`, quad cone `-W`).  Then no tilt helps and the
split must use another literal (K14: a second depth difference) or another view.
-/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

/-- Lex positivity of `(value at the ray, derivative along the direction)`. -/
def k18LexPos (x y : ℝ) : Prop := 0 < x ∨ (x = 0 ∧ 0 < y)

/-- The open cone of a finite list of linear functionals on `ℝ²`. -/
def k18Cone (L : List (ℝ × ℝ)) (v1 v2 : ℝ) : Prop := ∀ l ∈ L, 0 < l.1 * v1 + l.2 * v2

theorem k18Cone_cons {l : ℝ × ℝ} {L : List (ℝ × ℝ)} {v1 v2 : ℝ} :
    k18Cone (l :: L) v1 v2 ↔ 0 < l.1 * v1 + l.2 * v2 ∧ k18Cone L v1 v2 := by
  simp [k18Cone]

/-- One functional, lex positive at `(ρ, δ)`: positive on `ρ + ε δ` for `0 < ε < e`. -/
theorem k18_one_ray {a b x y : ℝ} (h : k18LexPos x y) :
    ∃ e : ℝ, 0 < e ∧ ∀ ε : ℝ, 0 < ε → ε < e → 0 < x + ε * y := by
  rcases h with hx | ⟨hx, hy⟩
  · refine ⟨x / (|y| + 1), by positivity, fun ε h0 h1 => ?_⟩
    have hpos : 0 < |y| + 1 := by positivity
    have h2 : ε * (|y| + 1) < x := by rwa [lt_div_iff₀ hpos] at h1
    have h3 : -(ε * y) ≤ ε * |y| := by
      have := neg_abs_le y
      nlinarith
    nlinarith
  · exact ⟨1, one_pos, fun ε h0 _ => by rw [hx]; positivity⟩

/-- **Ray witness**: every functional lex positive at `(ρ, δ)` ⇒ `ρ + ε δ` in the open cone for `0 < ε < e`. -/
theorem k18_cone_of_ray (L : List (ℝ × ℝ)) {ρ1 ρ2 δ1 δ2 : ℝ}
    (h : ∀ l ∈ L, k18LexPos (l.1 * ρ1 + l.2 * ρ2) (l.1 * δ1 + l.2 * δ2)) :
    ∃ e : ℝ, 0 < e ∧ ∀ ε : ℝ, 0 < ε → ε < e → k18Cone L (ρ1 + ε * δ1) (ρ2 + ε * δ2) := by
  induction L with
  | nil => exact ⟨1, one_pos, fun ε _ _ l hl => by simp at hl⟩
  | cons l L ih =>
    obtain ⟨e1, he1, h1⟩ := ih (fun l' hl' => h l' (List.mem_cons_of_mem _ hl'))
    obtain ⟨e2, he2, h2⟩ := k18_one_ray (a := 0) (b := 0) (h l List.mem_cons_self)
    refine ⟨min e1 e2, lt_min he1 he2, fun ε h0 hε => ?_⟩
    rw [k18Cone_cons]
    refine ⟨?_, h1 ε h0 (lt_of_lt_of_le hε (min_le_left _ _))⟩
    have := h2 ε h0 (lt_of_lt_of_le hε (min_le_right _ _))
    linarith [show l.1 * (ρ1 + ε * δ1) + l.2 * (ρ2 + ε * δ2) =
      (l.1 * ρ1 + l.2 * ρ2) + ε * (l.1 * δ1 + l.2 * δ2) by ring]

/-- A point of a nonempty open cone gives a whole tilt segment inside the cone. -/
theorem k18_seg_of_cone {L : List (ℝ × ℝ)} (hL : L ≠ []) {v1 v2 : ℝ} (hv : k18Cone L v1 v2) :
    ∃ t1 t2 : ℝ, v1 * t2 - v2 * t1 ≠ 0 ∧
      ∀ lam : ℝ, 0 < lam → lam < 1 → k18Cone L (v1 + lam * t1) (v2 + lam * t2) := by
  obtain ⟨l0, hl0⟩ := List.exists_mem_of_ne_nil L hL
  have hne : v1 ≠ 0 ∨ v2 ≠ 0 := by
    by_contra hh; push Not at hh
    have := hv l0 hl0; rw [hh.1, hh.2] at this; simp at this
  obtain ⟨e, he, hcone⟩ := k18_cone_of_ray L (ρ1 := v1) (ρ2 := v2) (δ1 := -v2) (δ2 := v1)
    (fun l hl => Or.inl (hv l hl))
  refine ⟨e / 2 * (-v2), e / 2 * v1, ?_, fun lam h0 h1 => ?_⟩
  · have hs : 0 < v1 ^ 2 + v2 ^ 2 := by
      rcases hne with h | h
      · have := pow_pos (abs_pos.2 h) 2; rw [sq_abs] at this; nlinarith [sq_nonneg v2]
      · have := pow_pos (abs_pos.2 h) 2; rw [sq_abs] at this; nlinarith [sq_nonneg v1]
    have : v1 * (e / 2 * v1) - v2 * (e / 2 * (-v2)) = e / 2 * (v1 ^ 2 + v2 ^ 2) := by ring
    rw [this]; positivity
  · have := hcone (lam * (e / 2)) (by positivity) (by nlinarith)
    convert this using 2 <;> ring

/-- **Cone cell**: a frame cycle whose tests and lex unimodality hold on the open cone of `L` (nonempty), and a
lex-positive ray witness `(ρ, δ)` for `L`, give `HasLexCellAt V r`. -/
theorem k18_cone_cell (V : Finset ℝ³) (p q r d : ℝ³) (hΔ : det3 p q r ≠ 0) {k : ℕ} [NeZero k] (hk : 3 ≤ k)
    (Y : ZMod k → ℝ × ℝ × ℝ) (hYinj : ∀ i j, Y i = Y j → i = j) (hmem : ∀ i, fpoint p q r d (Y i) ∈ V)
    (L : List (ℝ × ℝ)) (hL : L ≠ [])
    (hcyc : ∀ v1 v2 : ℝ, k18Cone L v1 v2 → ∀ D : ℝ, 0 < D → ∀ i j : ZMod k, j ≠ i → j ≠ i + 1 →
      TSc D (Y (i + 1) - Y i) (Y j - Y i) (v1, v2, 0))
    (hrest : ∀ y ∈ V, (∀ j, y ≠ fpoint p q r d (Y j)) → ∃ t, y = fpoint p q r d t ∧
      ∀ v1 v2 : ℝ, k18Cone L v1 v2 → ∀ D : ℝ, 0 < D → ∀ i, TSc D (Y (i + 1) - Y i) (t - Y i) (v1, v2, 0))
    (hlex : ∀ v1 v2 : ℝ, k18Cone L v1 v2 →
      (∀ i j, ⟪fpoint p q r d (Y i), r⟫ = ⟪fpoint p q r d (Y j), r⟫ →
        ⟪fpoint p q r d (Y i), fcomb p q r v1 v2 0⟫ = ⟪fpoint p q r d (Y j), fcomb p q r v1 v2 0⟫ → i = j) →
      LexUni (fun i => ⟪fpoint p q r d (Y i), r⟫) (fun i => ⟪fpoint p q r d (Y i), fcomb p q r v1 v2 0⟫))
    {ρ1 ρ2 δ1 δ2 : ℝ} (hray : ∀ l ∈ L, k18LexPos (l.1 * ρ1 + l.2 * ρ2) (l.1 * δ1 + l.2 * δ2)) :
    HasLexCellAt V r := by
  obtain ⟨e, he, hcone⟩ := k18_cone_of_ray L hray
  have hv := hcone (e / 2) (by positivity) (by linarith)
  obtain ⟨t1, t2, hut, hseg⟩ := k18_seg_of_cone hL hv
  refine k8_cell_gen V p q r d hΔ hk Y hYinj hut hmem (fun lam h0 h1 => hcyc _ _ (hseg lam h0 h1)) ?_ ?_
  · intro y hy hyx
    obtain ⟨t, rfl, ht⟩ := hrest y hy hyx
    exact ⟨t, rfl, fun lam h0 h1 => ht _ _ (hseg lam h0 h1)⟩
  · intro lam h0 h1 w hw hinj
    have e : w = fun i => ⟪fpoint p q r d (Y i),
        fcomb p q r ((ρ1 + e / 2 * δ1) + lam * t1) ((ρ2 + e / 2 * δ2) + lam * t2) 0⟫ := funext hw
    subst e
    exact hlex _ _ (hseg lam h0 h1) hinj

/-- **One cell at a tie**: the cone list is `m :: L` (`m` the tie functional, cell needs `m·v > 0`); the ray witness
only has to make `m` lex positive at the ray, the rest of `L` as usual. -/
theorem k18_tie_one (V : Finset ℝ³) (p q r d : ℝ³) (hΔ : det3 p q r ≠ 0) {k : ℕ} [NeZero k] (hk : 3 ≤ k)
    (Y : ZMod k → ℝ × ℝ × ℝ) (hYinj : ∀ i j, Y i = Y j → i = j) (hmem : ∀ i, fpoint p q r d (Y i) ∈ V)
    (m : ℝ × ℝ) (L : List (ℝ × ℝ))
    (hcyc : ∀ v1 v2 : ℝ, k18Cone (m :: L) v1 v2 → ∀ D : ℝ, 0 < D → ∀ i j : ZMod k, j ≠ i → j ≠ i + 1 →
      TSc D (Y (i + 1) - Y i) (Y j - Y i) (v1, v2, 0))
    (hrest : ∀ y ∈ V, (∀ j, y ≠ fpoint p q r d (Y j)) → ∃ t, y = fpoint p q r d t ∧
      ∀ v1 v2 : ℝ, k18Cone (m :: L) v1 v2 → ∀ D : ℝ, 0 < D → ∀ i, TSc D (Y (i + 1) - Y i) (t - Y i) (v1, v2, 0))
    (hlex : ∀ v1 v2 : ℝ, k18Cone (m :: L) v1 v2 →
      (∀ i j, ⟪fpoint p q r d (Y i), r⟫ = ⟪fpoint p q r d (Y j), r⟫ →
        ⟪fpoint p q r d (Y i), fcomb p q r v1 v2 0⟫ = ⟪fpoint p q r d (Y j), fcomb p q r v1 v2 0⟫ → i = j) →
      LexUni (fun i => ⟪fpoint p q r d (Y i), r⟫) (fun i => ⟪fpoint p q r d (Y i), fcomb p q r v1 v2 0⟫))
    {ρ1 ρ2 δ1 δ2 : ℝ} (hm : k18LexPos (m.1 * ρ1 + m.2 * ρ2) (m.1 * δ1 + m.2 * δ2))
    (hray : ∀ l ∈ L, k18LexPos (l.1 * ρ1 + l.2 * ρ2) (l.1 * δ1 + l.2 * δ2)) :
    HasLexCellAt V r :=
  k18_cone_cell V p q r d hΔ hk Y hYinj hmem (m :: L) (List.cons_ne_nil _ _) hcyc hrest hlex
    (by
      intro l hl
      rcases List.mem_cons.1 hl with rfl | hl
      · exact hm
      · exact hray l hl)

/-- Data of one frame cone cell at the view `r` (for the two-cell lemmas). -/
structure K18Cell (V : Finset ℝ³) (p q r d : ℝ³) (C : ℝ → ℝ → Prop) : Prop where
  cell : ∀ {ρ1 ρ2 δ1 δ2 : ℝ} (L : List (ℝ × ℝ)), (∀ v1 v2, k18Cone L v1 v2 → C v1 v2) → L ≠ [] →
    (∀ l ∈ L, k18LexPos (l.1 * ρ1 + l.2 * ρ2) (l.1 * δ1 + l.2 * δ2)) → HasLexCellAt V r

/-- Packaging: the hypotheses of `k18_cone_cell` on a predicate `C` (cone ⊆ C) give a `K18Cell`. -/
theorem k18Cell_of (V : Finset ℝ³) (p q r d : ℝ³) (hΔ : det3 p q r ≠ 0) {k : ℕ} [NeZero k] (hk : 3 ≤ k)
    (Y : ZMod k → ℝ × ℝ × ℝ) (hYinj : ∀ i j, Y i = Y j → i = j) (hmem : ∀ i, fpoint p q r d (Y i) ∈ V)
    (C : ℝ → ℝ → Prop)
    (hcyc : ∀ v1 v2 : ℝ, C v1 v2 → ∀ D : ℝ, 0 < D → ∀ i j : ZMod k, j ≠ i → j ≠ i + 1 →
      TSc D (Y (i + 1) - Y i) (Y j - Y i) (v1, v2, 0))
    (hrest : ∀ y ∈ V, (∀ j, y ≠ fpoint p q r d (Y j)) → ∃ t, y = fpoint p q r d t ∧
      ∀ v1 v2 : ℝ, C v1 v2 → ∀ D : ℝ, 0 < D → ∀ i, TSc D (Y (i + 1) - Y i) (t - Y i) (v1, v2, 0))
    (hlex : ∀ v1 v2 : ℝ, C v1 v2 →
      (∀ i j, ⟪fpoint p q r d (Y i), r⟫ = ⟪fpoint p q r d (Y j), r⟫ →
        ⟪fpoint p q r d (Y i), fcomb p q r v1 v2 0⟫ = ⟪fpoint p q r d (Y j), fcomb p q r v1 v2 0⟫ → i = j) →
      LexUni (fun i => ⟪fpoint p q r d (Y i), r⟫) (fun i => ⟪fpoint p q r d (Y i), fcomb p q r v1 v2 0⟫)) :
    K18Cell V p q r d C :=
  ⟨fun L hC hL hray => k18_cone_cell V p q r d hΔ hk Y hYinj hmem L hL
    (fun v1 v2 h => hcyc v1 v2 (hC v1 v2 h))
    (fun y hy hyx => by
      obtain ⟨t, ht, h⟩ := hrest y hy hyx
      exact ⟨t, ht, fun v1 v2 hv => h v1 v2 (hC v1 v2 hv)⟩)
    (fun v1 v2 hv => hlex v1 v2 (hC v1 v2 hv)) hray⟩

/-- **The two-cell tie lemma.**  Cell 1 works on `{m > 0} ∩ cone(L1)`, cell 2 on `{m < 0} ∩ cone(L2)` (same view and
frame).  The cones touch along the ray `ρ`: `L1` is lex positive at `ρ` towards `δ1`, `L2` towards `δ2`.  If the tie
functional does not vanish at the shared ray, one of the cells is a lex cell. -/
theorem k18_tie_two {V : Finset ℝ³} {p q r d : ℝ³} {m : ℝ × ℝ} {L1 L2 : List (ℝ × ℝ)}
    (h1 : K18Cell V p q r d (k18Cone (m :: L1))) (h2 : K18Cell V p q r d (k18Cone ((-m.1, -m.2) :: L2)))
    {ρ1 ρ2 δ1 δ2 ε1 ε2 : ℝ}
    (hr1 : ∀ l ∈ L1, k18LexPos (l.1 * ρ1 + l.2 * ρ2) (l.1 * δ1 + l.2 * δ2))
    (hr2 : ∀ l ∈ L2, k18LexPos (l.1 * ρ1 + l.2 * ρ2) (l.1 * ε1 + l.2 * ε2))
    (hm : m.1 * ρ1 + m.2 * ρ2 ≠ 0) : HasLexCellAt V r := by
  rcases hm.lt_or_gt with hneg | hpos
  · refine h2.cell (ρ1 := ρ1) (ρ2 := ρ2) (δ1 := ε1) (δ2 := ε2) ((-m.1, -m.2) :: L2) (fun _ _ h => h) (List.cons_ne_nil _ _) ?_
    intro l hl
    rcases List.mem_cons.1 hl with rfl | hl
    · left; simp only; linarith
    · exact hr2 l hl
  · refine h1.cell (ρ1 := ρ1) (ρ2 := ρ2) (δ1 := δ1) (δ2 := δ2) (m :: L1) (fun _ _ h => h) (List.cons_ne_nil _ _) ?_
    intro l hl
    rcases List.mem_cons.1 hl with rfl | hl
    · exact Or.inl hpos
    · exact hr1 l hl

/-- **Second order at the shared ray**: if `m·ρ = 0`, the two directions decide (`m·δ1 > 0` gives cell 1,
`m·ε2 < 0` gives cell 2).  With `δ1 = -ε2` (cones on the two sides of `ρ`), `m·δ1 ≠ 0` suffices. -/
theorem k18_tie_two' {V : Finset ℝ³} {p q r d : ℝ³} {m : ℝ × ℝ} {L1 L2 : List (ℝ × ℝ)}
    (h1 : K18Cell V p q r d (k18Cone (m :: L1))) (h2 : K18Cell V p q r d (k18Cone ((-m.1, -m.2) :: L2)))
    {ρ1 ρ2 δ1 δ2 ε1 ε2 : ℝ}
    (hr1 : ∀ l ∈ L1, k18LexPos (l.1 * ρ1 + l.2 * ρ2) (l.1 * δ1 + l.2 * δ2))
    (hr2 : ∀ l ∈ L2, k18LexPos (l.1 * ρ1 + l.2 * ρ2) (l.1 * ε1 + l.2 * ε2))
    (hm : k18LexPos (m.1 * ρ1 + m.2 * ρ2) (m.1 * δ1 + m.2 * δ2) ∨
      k18LexPos (-(m.1 * ρ1 + m.2 * ρ2)) (-(m.1 * ε1 + m.2 * ε2))) : HasLexCellAt V r := by
  rcases hm with hm | hm
  · refine h1.cell (ρ1 := ρ1) (ρ2 := ρ2) (δ1 := δ1) (δ2 := δ2) (m :: L1) (fun _ _ h => h) (List.cons_ne_nil _ _) ?_
    intro l hl
    rcases List.mem_cons.1 hl with rfl | hl
    · exact hm
    · exact hr1 l hl
  · refine h2.cell (ρ1 := ρ1) (ρ2 := ρ2) (δ1 := ε1) (δ2 := ε2) ((-m.1, -m.2) :: L2) (fun _ _ h => h) (List.cons_ne_nil _ _) ?_
    intro l hl
    rcases List.mem_cons.1 hl with rfl | hl
    · simp only; convert hm using 2 <;> ring
    · exact hr2 l hl

/-- Lex order from a depth tie and the tilt weights. -/
theorem k18_lexLt_tie {z1 z2 w1 w2 : ℝ} (hz : z1 = z2) (hw : w1 < w2) : LexLt (z1, w1) (z2, w2) :=
  Or.inr ⟨hz, hw⟩

/-- The tie functional of a frame-point pair: `w(s) - w(t) = m · v` with `m = (⟪s-t, p⟫, ⟪s-t, q⟫)`. -/
theorem k18_wdiff (p q r d : ℝ³) (s t : ℝ × ℝ × ℝ) (v1 v2 : ℝ) :
    ⟪fpoint p q r d s, fcomb p q r v1 v2 0⟫ - ⟪fpoint p q r d t, fcomb p q r v1 v2 0⟫ =
      ⟪fpoint p q r d s - fpoint p q r d t, p⟫ * v1 + ⟪fpoint p q r d s - fpoint p q r d t, q⟫ * v2 := by
  rw [k8_wdiff]; ring

end C2
end Type08Sp
end Minimality
