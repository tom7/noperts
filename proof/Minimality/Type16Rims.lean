module

public import Minimality.Type16NF

@[expose] public section

/-!
# Single tests with explicit rims (type 16, §19.3–19.5)

The two-test and three-test certificates of §19.3–19.5 combine single tests whose rims are
quadrilaterals or pentagons, at an edge view (Theorem 8.9) or at the view along the line of
two faces through a vertex (Proposition 8.8).  These are `isRupert_of_edgeViewσ` and
`isRupert_of_vertexViewσ` with the cycle written out: every determinant test is a separate
hypothesis, and the depths are assumed cyclically unimodal (the pair and triple lemmas decide
which test is unimodal).

* `isRupert_vquadσ`, `isRupert_vquintσ`: vertex views, middles over any side;
* `isRupert_equadσ`, `isRupert_equintσ`: edge views (`w = y₀ − h u`), middles over the sides
  at the apex (`EdgeMiddle`);
* `quad_unimodal`: a 4-cycle with distinct depths is unimodal unless its diagonals are
  depth-separated.
-/

namespace Minimality

open scoped RealInnerProductSpace
open Finset

theorem quad_unimodal {y₀ y₁ y₂ y₃ u : ℝ³} (h : ¬ DepthSep y₀ y₂ y₁ y₃ u)
    (hz : [⟪y₀, u⟫, ⟪y₁, u⟫, ⟪y₂, u⟫, ⟪y₃, u⟫].Nodup) :
    IsCyclicUnimodal (quad ⟪y₀, u⟫ ⟪y₁, u⟫ ⟪y₂, u⟫ ⟪y₃, u⟫) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hz
  obtain ⟨⟨z1, z2, z3⟩, ⟨z4, z5⟩, z6, -⟩ := hz
  exact isCyclicUnimodal_four (quad_injective z1 z2 z3 z4 z5 z6)
    (overlap4_of_not_depthSep h z1 z2 z3 z4 z5 z6)

/-- A vertex-view quadrilateral rim `y₀ y₁ y₂ y₃` (orientation `σ`). -/
theorem isRupert_vquadσ (V M : Finset ℝ³) {u : ℝ³} (hu : u ≠ 0) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    {y₀ y₁ y₂ y₃ : ℝ³} (h₀ : y₀ ∈ V) (h₁ : y₁ ∈ V) (h₂ : y₂ ∈ V) (h₃ : y₃ ∈ V)
    (n₀ : y₀ ∉ M) (n₁ : y₁ ∉ M) (n₂ : y₂ ∉ M) (n₃ : y₃ ∉ M)
    (c₁ : 0 < σ * det3 (y₁ - y₀) (y₂ - y₀) u) (c₂ : 0 < σ * det3 (y₁ - y₀) (y₃ - y₀) u)
    (c₃ : 0 < σ * det3 (y₂ - y₁) (y₃ - y₁) u) (c₄ : 0 < σ * det3 (y₂ - y₁) (y₀ - y₁) u)
    (c₅ : 0 < σ * det3 (y₃ - y₂) (y₀ - y₂) u) (c₆ : 0 < σ * det3 (y₃ - y₂) (y₁ - y₂) u)
    (c₇ : 0 < σ * det3 (y₀ - y₃) (y₁ - y₃) u) (c₈ : 0 < σ * det3 (y₀ - y₃) (y₂ - y₃) u)
    (hrest : ∀ z ∈ V, z ∉ M → z ≠ y₀ → z ≠ y₁ → z ≠ y₂ → z ≠ y₃ →
      0 < σ * det3 (y₁ - y₀) (z - y₀) u ∧ 0 < σ * det3 (y₂ - y₁) (z - y₁) u ∧
        0 < σ * det3 (y₃ - y₂) (z - y₂) u ∧ 0 < σ * det3 (y₀ - y₃) (z - y₃) u)
    (hz : IsCyclicUnimodal (quad ⟪y₀, u⟫ ⟪y₁, u⟫ ⟪y₂, u⟫ ⟪y₃, u⟫)) (hnd : NoHDNAt V u)
    (hM : ∀ m ∈ M, ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
      (m = y₀ + s • (y₁ - y₀) + δ • u ∨ m = y₁ + s • (y₂ - y₁) + δ • u ∨
        m = y₂ + s • (y₃ - y₂) + δ • u ∨ m = y₃ + s • (y₀ - y₃) + δ • u)) : IsRupert V := by
  obtain ⟨a0, a1, a2, a3⟩ := zmod4_add_one
  refine isRupert_of_vertexViewσ V M u hu hσ (k := 4) (by norm_num) (quad y₀ y₁ y₂ y₃) ?_ ?_ ?_
    ?_ (by rw [quad_inner]; exact hz) hnd ?_
  · intro i; rcases zmod4_cases i with rfl | rfl | rfl | rfl
    exacts [h₀, h₁, h₂, h₃]
  · intro i; rcases zmod4_cases i with rfl | rfl | rfl | rfl
    exacts [n₀, n₁, n₂, n₃]
  · intro i j hi hj
    rcases zmod4_pairs i j hi hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3]
    exacts [c₁, c₂, c₃, c₄, c₅, c₆, c₇, c₈]
  · intro y hy hyM hyx i
    obtain ⟨r0, r1, r2, r3⟩ := hrest y hy hyM (hyx 0) (hyx 1) (hyx 2) (hyx 3)
    rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
      simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3]
    exacts [r0, r1, r2, r3]
  · intro m hm
    obtain ⟨s, δ, hs0, hs1, hδ, h | h | h | h⟩ := hM m hm
    · exact ⟨0, s, δ, hs0, hs1, hδ, by simp only [a0, quad_0, quad_1]; exact h⟩
    · exact ⟨1, s, δ, hs0, hs1, hδ, by simp only [a1, quad_1, quad_2]; exact h⟩
    · exact ⟨2, s, δ, hs0, hs1, hδ, by simp only [a2, quad_2, quad_3]; exact h⟩
    · exact ⟨3, s, δ, hs0, hs1, hδ, by simp only [a3, quad_3, quad_0]; exact h⟩

theorem quint_inner (p₀ p₁ p₂ p₃ p₄ u : ℝ³) :
    (fun i => ⟪quint p₀ p₁ p₂ p₃ p₄ i, u⟫) = quint ⟪p₀, u⟫ ⟪p₁, u⟫ ⟪p₂, u⟫ ⟪p₃, u⟫ ⟪p₄, u⟫ := by
  funext i; rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;> rfl

/-- The fifteen tests of a strictly convex pentagon `y₀ … y₄` (orientation `σ`) at `u`. -/
def Pent15 (σ : ℝ) (y₀ y₁ y₂ y₃ y₄ u : ℝ³) : Prop :=
  0 < σ * det3 (y₁ - y₀) (y₂ - y₀) u ∧ 0 < σ * det3 (y₁ - y₀) (y₃ - y₀) u ∧
  0 < σ * det3 (y₁ - y₀) (y₄ - y₀) u ∧ 0 < σ * det3 (y₂ - y₁) (y₃ - y₁) u ∧
  0 < σ * det3 (y₂ - y₁) (y₄ - y₁) u ∧ 0 < σ * det3 (y₂ - y₁) (y₀ - y₁) u ∧
  0 < σ * det3 (y₃ - y₂) (y₄ - y₂) u ∧ 0 < σ * det3 (y₃ - y₂) (y₀ - y₂) u ∧
  0 < σ * det3 (y₃ - y₂) (y₁ - y₂) u ∧ 0 < σ * det3 (y₄ - y₃) (y₀ - y₃) u ∧
  0 < σ * det3 (y₄ - y₃) (y₁ - y₃) u ∧ 0 < σ * det3 (y₄ - y₃) (y₂ - y₃) u ∧
  0 < σ * det3 (y₀ - y₄) (y₁ - y₄) u ∧ 0 < σ * det3 (y₀ - y₄) (y₂ - y₄) u ∧
  0 < σ * det3 (y₀ - y₄) (y₃ - y₄) u

/-- `z` strictly inside the pentagon `y₀ … y₄` (orientation `σ`) at `u`. -/
def PentIn (σ : ℝ) (y₀ y₁ y₂ y₃ y₄ u z : ℝ³) : Prop :=
  0 < σ * det3 (y₁ - y₀) (z - y₀) u ∧ 0 < σ * det3 (y₂ - y₁) (z - y₁) u ∧
  0 < σ * det3 (y₃ - y₂) (z - y₂) u ∧ 0 < σ * det3 (y₄ - y₃) (z - y₃) u ∧
  0 < σ * det3 (y₀ - y₄) (z - y₄) u

theorem pent15_cyc {σ : ℝ} {y₀ y₁ y₂ y₃ y₄ u : ℝ³} (h : Pent15 σ y₀ y₁ y₂ y₃ y₄ u) :
    ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 → 0 < σ * det3
      (quint y₀ y₁ y₂ y₃ y₄ (i + 1) - quint y₀ y₁ y₂ y₃ y₄ i)
      (quint y₀ y₁ y₂ y₃ y₄ j - quint y₀ y₁ y₂ y₃ y₄ i) u := by
  obtain ⟨a0, a1, a2, a3, a4⟩ := zmod5_add_one
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15⟩ := h
  intro i j hi hj
  rcases zmod5_pairs i j hi hj with ⟨rfl, rfl | rfl | rfl⟩ | ⟨rfl, rfl | rfl | rfl⟩ |
    ⟨rfl, rfl | rfl | rfl⟩ | ⟨rfl, rfl | rfl | rfl⟩ | ⟨rfl, rfl | rfl | rfl⟩ <;>
  simp only [a0, a1, a2, a3, a4, quint_0, quint_1, quint_2, quint_3, quint_4]
  exacts [c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15]

theorem pentIn_rest {σ : ℝ} {y₀ y₁ y₂ y₃ y₄ u z : ℝ³} (h : PentIn σ y₀ y₁ y₂ y₃ y₄ u z) :
    ∀ i : ZMod 5, 0 < σ * det3
      (quint y₀ y₁ y₂ y₃ y₄ (i + 1) - quint y₀ y₁ y₂ y₃ y₄ i) (z - quint y₀ y₁ y₂ y₃ y₄ i) u := by
  obtain ⟨a0, a1, a2, a3, a4⟩ := zmod5_add_one
  obtain ⟨r0, r1, r2, r3, r4⟩ := h
  intro i
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    simp only [a0, a1, a2, a3, a4, quint_0, quint_1, quint_2, quint_3, quint_4]
  exacts [r0, r1, r2, r3, r4]

/-- A vertex-view pentagonal rim `y₀ … y₄` (orientation `σ`). -/
theorem isRupert_vquintσ (V M : Finset ℝ³) {u : ℝ³} (hu : u ≠ 0) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    {y₀ y₁ y₂ y₃ y₄ : ℝ³} (h₀ : y₀ ∈ V) (h₁ : y₁ ∈ V) (h₂ : y₂ ∈ V) (h₃ : y₃ ∈ V) (h₄ : y₄ ∈ V)
    (n₀ : y₀ ∉ M) (n₁ : y₁ ∉ M) (n₂ : y₂ ∉ M) (n₃ : y₃ ∉ M) (n₄ : y₄ ∉ M)
    (hc : Pent15 σ y₀ y₁ y₂ y₃ y₄ u)
    (hrest : ∀ z ∈ V, z ∉ M → z ≠ y₀ → z ≠ y₁ → z ≠ y₂ → z ≠ y₃ → z ≠ y₄ →
      PentIn σ y₀ y₁ y₂ y₃ y₄ u z)
    (hz : IsCyclicUnimodal (quint ⟪y₀, u⟫ ⟪y₁, u⟫ ⟪y₂, u⟫ ⟪y₃, u⟫ ⟪y₄, u⟫)) (hnd : NoHDNAt V u)
    (hM : ∀ m ∈ M, ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
      (m = y₀ + s • (y₁ - y₀) + δ • u ∨ m = y₁ + s • (y₂ - y₁) + δ • u ∨
        m = y₂ + s • (y₃ - y₂) + δ • u ∨ m = y₃ + s • (y₄ - y₃) + δ • u ∨
        m = y₄ + s • (y₀ - y₄) + δ • u)) : IsRupert V := by
  obtain ⟨a0, a1, a2, a3, a4⟩ := zmod5_add_one
  refine isRupert_of_vertexViewσ V M u hu hσ (k := 5) (by norm_num) (quint y₀ y₁ y₂ y₃ y₄) ?_ ?_
    (pent15_cyc hc) ?_ (by rw [quint_inner]; exact hz) hnd ?_
  · intro i; rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl
    exacts [h₀, h₁, h₂, h₃, h₄]
  · intro i; rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl
    exacts [n₀, n₁, n₂, n₃, n₄]
  · intro y hy hyM hyx
    exact pentIn_rest (hrest y hy hyM (hyx 0) (hyx 1) (hyx 2) (hyx 3) (hyx 4))
  · intro m hm
    obtain ⟨s, δ, hs0, hs1, hδ, h | h | h | h | h⟩ := hM m hm
    · exact ⟨0, s, δ, hs0, hs1, hδ, by simp only [a0, quint_0, quint_1]; exact h⟩
    · exact ⟨1, s, δ, hs0, hs1, hδ, by simp only [a1, quint_1, quint_2]; exact h⟩
    · exact ⟨2, s, δ, hs0, hs1, hδ, by simp only [a2, quint_2, quint_3]; exact h⟩
    · exact ⟨3, s, δ, hs0, hs1, hδ, by simp only [a3, quint_3, quint_4]; exact h⟩
    · exact ⟨4, s, δ, hs0, hs1, hδ, by simp only [a4, quint_4, quint_0]; exact h⟩

/-- An edge-view quadrilateral rim `y₀ y₁ y₂ y₃` at the apex `y₀` (other axle end
`w = y₀ − h u`, orientation `σ`). -/
theorem isRupert_equadσ (V M : Finset ℝ³) {u : ℝ³} (hu : u ≠ 0) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    {y₀ y₁ y₂ y₃ w : ℝ³} {h : ℝ} (hh : h ≠ 0) (hw : w = y₀ - h • u) (hwV : w ∈ V)
    (h₀ : y₀ ∈ V) (h₁ : y₁ ∈ V) (h₂ : y₂ ∈ V) (h₃ : y₃ ∈ V)
    (n₀ : y₀ ∉ M) (n₁ : y₁ ∉ M) (n₂ : y₂ ∉ M) (n₃ : y₃ ∉ M)
    (c₁ : 0 < σ * det3 (y₁ - y₀) (y₂ - y₀) u) (c₂ : 0 < σ * det3 (y₁ - y₀) (y₃ - y₀) u)
    (c₃ : 0 < σ * det3 (y₂ - y₁) (y₃ - y₁) u) (c₄ : 0 < σ * det3 (y₂ - y₁) (y₀ - y₁) u)
    (c₅ : 0 < σ * det3 (y₃ - y₂) (y₀ - y₂) u) (c₆ : 0 < σ * det3 (y₃ - y₂) (y₁ - y₂) u)
    (c₇ : 0 < σ * det3 (y₀ - y₃) (y₁ - y₃) u) (c₈ : 0 < σ * det3 (y₀ - y₃) (y₂ - y₃) u)
    (hrest : ∀ z ∈ V, z ∉ M → z ≠ w → z ≠ y₀ → z ≠ y₁ → z ≠ y₂ → z ≠ y₃ →
      0 < σ * det3 (y₁ - y₀) (z - y₀) u ∧ 0 < σ * det3 (y₂ - y₁) (z - y₁) u ∧
        0 < σ * det3 (y₃ - y₂) (z - y₂) u ∧ 0 < σ * det3 (y₀ - y₃) (z - y₃) u)
    (hz : IsCyclicUnimodal (quad ⟪y₀, u⟫ ⟪y₁, u⟫ ⟪y₂, u⟫ ⟪y₃, u⟫)) (hnd : NoHDNAt (V.erase w) u)
    (hM : ∀ m ∈ M, EdgeMiddle u y₀ w y₁ y₃ h m) : IsRupert V := by
  obtain ⟨a0, a1, a2, a3⟩ := zmod4_add_one
  refine isRupert_of_edgeViewσ V M u hu hσ (k := 4) (by norm_num) (quad y₀ y₁ y₂ y₃) 0 w h hwV
    hw hh ?_ ?_ ?_ ?_ (by rw [quad_inner]; exact hz) hnd ?_
  · intro i; rcases zmod4_cases i with rfl | rfl | rfl | rfl
    exacts [h₀, h₁, h₂, h₃]
  · intro i; rcases zmod4_cases i with rfl | rfl | rfl | rfl
    exacts [n₀, n₁, n₂, n₃]
  · intro i j hi hj
    rcases zmod4_pairs i j hi hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3]
    exacts [c₁, c₂, c₃, c₄, c₅, c₆, c₇, c₈]
  · intro y hy hyM hyw hyx i
    obtain ⟨r0, r1, r2, r3⟩ := hrest y hy hyM hyw (hyx 0) (hyx 1) (hyx 2) (hyx 3)
    rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
      simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3]
    exacts [r0, r1, r2, r3]
  · intro m hm
    rw [zmod4_zero_sub_one, zero_add]
    simpa only [quad_0, quad_1, quad_3] using hM m hm

/-- An edge-view pentagonal rim `y₀ … y₄` at the apex `y₀` (other axle end `w = y₀ − h u`,
orientation `σ`). -/
theorem isRupert_equintσ (V M : Finset ℝ³) {u : ℝ³} (hu : u ≠ 0) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    {y₀ y₁ y₂ y₃ y₄ w : ℝ³} {h : ℝ} (hh : h ≠ 0) (hw : w = y₀ - h • u) (hwV : w ∈ V)
    (h₀ : y₀ ∈ V) (h₁ : y₁ ∈ V) (h₂ : y₂ ∈ V) (h₃ : y₃ ∈ V) (h₄ : y₄ ∈ V)
    (n₀ : y₀ ∉ M) (n₁ : y₁ ∉ M) (n₂ : y₂ ∉ M) (n₃ : y₃ ∉ M) (n₄ : y₄ ∉ M)
    (hc : Pent15 σ y₀ y₁ y₂ y₃ y₄ u)
    (hrest : ∀ z ∈ V, z ∉ M → z ≠ w → z ≠ y₀ → z ≠ y₁ → z ≠ y₂ → z ≠ y₃ → z ≠ y₄ →
      PentIn σ y₀ y₁ y₂ y₃ y₄ u z)
    (hz : IsCyclicUnimodal (quint ⟪y₀, u⟫ ⟪y₁, u⟫ ⟪y₂, u⟫ ⟪y₃, u⟫ ⟪y₄, u⟫))
    (hnd : NoHDNAt (V.erase w) u) (hM : ∀ m ∈ M, EdgeMiddle u y₀ w y₁ y₄ h m) : IsRupert V := by
  obtain ⟨a0, a1, a2, a3, a4⟩ := zmod5_add_one
  refine isRupert_of_edgeViewσ V M u hu hσ (k := 5) (by norm_num) (quint y₀ y₁ y₂ y₃ y₄) 0 w h
    hwV hw hh ?_ ?_ (pent15_cyc hc) ?_ (by rw [quint_inner]; exact hz) hnd ?_
  · intro i; rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl
    exacts [h₀, h₁, h₂, h₃, h₄]
  · intro i; rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl
    exacts [n₀, n₁, n₂, n₃, n₄]
  · intro y hy hyM hyw hyx
    exact pentIn_rest (hrest y hy hyM hyw (hyx 0) (hyx 1) (hyx 2) (hyx 3) (hyx 4))
  · intro m hm
    rw [(zmod5_sub_one).1, zero_add]
    simpa only [quint_0, quint_1, quint_4] using hM m hm

end Minimality

end
