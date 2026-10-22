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
    (hz : IsRobustUnimodal (quad ⟪y₀, u⟫ ⟪y₁, u⟫ ⟪y₂, u⟫ ⟪y₃, u⟫)) (hnd : NoHDNAt V u)
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
    (hz : IsRobustUnimodal (quint ⟪y₀, u⟫ ⟪y₁, u⟫ ⟪y₂, u⟫ ⟪y₃, u⟫ ⟪y₄, u⟫)) (hnd : NoHDNAt V u)
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
    (hz : IsRobustUnimodal (quad ⟪y₀, u⟫ ⟪y₁, u⟫ ⟪y₂, u⟫ ⟪y₃, u⟫)) (hnd : NoHDNAt (V.erase w) u)
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
    (hz : IsRobustUnimodal (quint ⟪y₀, u⟫ ⟪y₁, u⟫ ⟪y₂, u⟫ ⟪y₃, u⟫ ⟪y₄, u⟫))
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

/-! ### Certificate forms (§18.2): the same rims without the horizontal double normal -/

theorem sigma_sq {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) : σ * σ = 1 := by
  rcases hσ with rfl | rfl <;> norm_num

theorem quad_inner_sigma (y₀ y₁ y₂ y₃ u : ℝ³) (σ : ℝ) :
    quad ⟪y₀, σ • u⟫ ⟪y₁, σ • u⟫ ⟪y₂, σ • u⟫ ⟪y₃, σ • u⟫ =
      fun i => σ * quad ⟪y₀, u⟫ ⟪y₁, u⟫ ⟪y₂, u⟫ ⟪y₃, u⟫ i := by
  funext i; rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
    simp only [quad_0, quad_1, quad_2, quad_3, real_inner_smul_right]

theorem quint_inner_sigma (y₀ y₁ y₂ y₃ y₄ u : ℝ³) (σ : ℝ) :
    quint ⟪y₀, σ • u⟫ ⟪y₁, σ • u⟫ ⟪y₂, σ • u⟫ ⟪y₃, σ • u⟫ ⟪y₄, σ • u⟫ =
      fun i => σ * quint ⟪y₀, u⟫ ⟪y₁, u⟫ ⟪y₂, u⟫ ⟪y₃, u⟫ ⟪y₄, u⟫ i := by
  funext i; rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    simp only [quint_0, quint_1, quint_2, quint_3, quint_4, real_inner_smul_right]

/-- **A quadrilateral rim at the view `σ u`** from the tests of `isRupert_vquadσ`, with every
point over a closed side or strictly inside. -/
theorem rimCertPts_quadσ (V : Finset ℝ³) {u : ℝ³} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    {y₀ y₁ y₂ y₃ : ℝ³} (h₀ : y₀ ∈ V) (h₁ : y₁ ∈ V) (h₂ : y₂ ∈ V) (h₃ : y₃ ∈ V)
    (c₁ : 0 < σ * det3 (y₁ - y₀) (y₂ - y₀) u) (c₂ : 0 < σ * det3 (y₁ - y₀) (y₃ - y₀) u)
    (c₃ : 0 < σ * det3 (y₂ - y₁) (y₃ - y₁) u) (c₄ : 0 < σ * det3 (y₂ - y₁) (y₀ - y₁) u)
    (c₅ : 0 < σ * det3 (y₃ - y₂) (y₀ - y₂) u) (c₆ : 0 < σ * det3 (y₃ - y₂) (y₁ - y₂) u)
    (c₇ : 0 < σ * det3 (y₀ - y₃) (y₁ - y₃) u) (c₈ : 0 < σ * det3 (y₀ - y₃) (y₂ - y₃) u)
    (hclass : ∀ z ∈ V, (∃ j₁ j₂ : ZMod 4, ∃ s δ : ℝ, 0 ≤ s ∧ s ≤ 1 ∧
      z = quad y₀ y₁ y₂ y₃ j₁ + s • (quad y₀ y₁ y₂ y₃ j₂ - quad y₀ y₁ y₂ y₃ j₁) + δ • u) ∨
      (0 < σ * det3 (y₁ - y₀) (z - y₀) u ∧ 0 < σ * det3 (y₂ - y₁) (z - y₁) u ∧
        0 < σ * det3 (y₃ - y₂) (z - y₂) u ∧ 0 < σ * det3 (y₀ - y₃) (z - y₃) u))
    (hz : IsRobustUnimodal (quad ⟪y₀, u⟫ ⟪y₁, u⟫ ⟪y₂, u⟫ ⟪y₃, u⟫)) :
    RimCertPts V (σ • u) (quad y₀ y₁ y₂ y₃) := by
  simp only [det3_sigma] at c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ hclass
  refine rimCertPts_quad V h₀ h₁ h₂ h₃ c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ (fun z hz => ?_) ?_
  · rcases hclass z hz with h | h
    · exact Or.inl (class_sigma (sigma_sq hσ) h)
    · exact Or.inr h
  · rw [quad_inner_sigma]; exact hz.sigma hσ

/-- A middle over a side of a quadrilateral rim (vertex views). -/
theorem quad_class_mid {y₀ y₁ y₂ y₃ u m : ℝ³}
    (h : ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
      (m = y₀ + s • (y₁ - y₀) + δ • u ∨ m = y₁ + s • (y₂ - y₁) + δ • u ∨
        m = y₂ + s • (y₃ - y₂) + δ • u ∨ m = y₃ + s • (y₀ - y₃) + δ • u)) :
    ∃ j₁ j₂ : ZMod 4, ∃ s δ : ℝ, 0 ≤ s ∧ s ≤ 1 ∧
      m = quad y₀ y₁ y₂ y₃ j₁ + s • (quad y₀ y₁ y₂ y₃ j₂ - quad y₀ y₁ y₂ y₃ j₁) + δ • u := by
  obtain ⟨s, δ, hs0, hs1, -, h | h | h | h⟩ := h
  · exact ⟨0, 1, s, δ, hs0.le, hs1.le, h⟩
  · exact ⟨1, 2, s, δ, hs0.le, hs1.le, h⟩
  · exact ⟨2, 3, s, δ, hs0.le, hs1.le, h⟩
  · exact ⟨3, 0, s, δ, hs0.le, hs1.le, h⟩

/-- **`isRupert_vquadσ`, certificate form.** -/
theorem rimCertPts_vquadσ (V M : Finset ℝ³) {u : ℝ³} (_hu : u ≠ 0) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    {y₀ y₁ y₂ y₃ : ℝ³} (h₀ : y₀ ∈ V) (h₁ : y₁ ∈ V) (h₂ : y₂ ∈ V) (h₃ : y₃ ∈ V)
    (_n₀ : y₀ ∉ M) (_n₁ : y₁ ∉ M) (_n₂ : y₂ ∉ M) (_n₃ : y₃ ∉ M)
    (c₁ : 0 < σ * det3 (y₁ - y₀) (y₂ - y₀) u) (c₂ : 0 < σ * det3 (y₁ - y₀) (y₃ - y₀) u)
    (c₃ : 0 < σ * det3 (y₂ - y₁) (y₃ - y₁) u) (c₄ : 0 < σ * det3 (y₂ - y₁) (y₀ - y₁) u)
    (c₅ : 0 < σ * det3 (y₃ - y₂) (y₀ - y₂) u) (c₆ : 0 < σ * det3 (y₃ - y₂) (y₁ - y₂) u)
    (c₇ : 0 < σ * det3 (y₀ - y₃) (y₁ - y₃) u) (c₈ : 0 < σ * det3 (y₀ - y₃) (y₂ - y₃) u)
    (hrest : ∀ z ∈ V, z ∉ M → z ≠ y₀ → z ≠ y₁ → z ≠ y₂ → z ≠ y₃ →
      0 < σ * det3 (y₁ - y₀) (z - y₀) u ∧ 0 < σ * det3 (y₂ - y₁) (z - y₁) u ∧
        0 < σ * det3 (y₃ - y₂) (z - y₂) u ∧ 0 < σ * det3 (y₀ - y₃) (z - y₃) u)
    (hz : IsRobustUnimodal (quad ⟪y₀, u⟫ ⟪y₁, u⟫ ⟪y₂, u⟫ ⟪y₃, u⟫))
    (hM : ∀ m ∈ M, ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
      (m = y₀ + s • (y₁ - y₀) + δ • u ∨ m = y₁ + s • (y₂ - y₁) + δ • u ∨
        m = y₂ + s • (y₃ - y₂) + δ • u ∨ m = y₃ + s • (y₀ - y₃) + δ • u)) :
    RimCertPts V (σ • u) (quad y₀ y₁ y₂ y₃) := by
  classical
  refine rimCertPts_quadσ V hσ h₀ h₁ h₂ h₃ c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ (fun z hz => ?_) hz
  by_cases hzM : z ∈ M
  · exact Or.inl (quad_class_mid (hM z hzM))
  by_cases e0 : z = y₀
  · exact Or.inl ⟨0, 0, 0, 0, le_rfl, zero_le_one, by rw [e0]; simp [quad_0]⟩
  by_cases e1 : z = y₁
  · exact Or.inl ⟨1, 1, 0, 0, le_rfl, zero_le_one, by rw [e1]; simp [quad_1]⟩
  by_cases e2 : z = y₂
  · exact Or.inl ⟨2, 2, 0, 0, le_rfl, zero_le_one, by rw [e2]; simp [quad_2]⟩
  by_cases e3 : z = y₃
  · exact Or.inl ⟨3, 3, 0, 0, le_rfl, zero_le_one, by rw [e3]; simp [quad_3]⟩
  exact Or.inr (hrest z hz hzM e0 e1 e2 e3)

/-- A middle of an edge view over a side at the apex `y₀` (`EdgeMiddle`). -/
theorem quad_class_edgeMid {y₀ y₁ y₂ y₃ u w m : ℝ³} {h : ℝ} (hw : w = y₀ - h • u)
    (hm : EdgeMiddle u y₀ w y₁ y₃ h m) :
    ∃ j₁ j₂ : ZMod 4, ∃ s δ : ℝ, 0 ≤ s ∧ s ≤ 1 ∧
      m = quad y₀ y₁ y₂ y₃ j₁ + s • (quad y₀ y₁ y₂ y₃ j₂ - quad y₀ y₁ y₂ y₃ j₁) + δ • u := by
  obtain ⟨c, s, δ, hc, hs0, hs1, -, hm⟩ := hm
  obtain ⟨t, hct⟩ : ∃ t : ℝ, c = y₀ + t • u := by
    rcases hc with rfl | ⟨rfl, -⟩
    · exact ⟨0, by simp⟩
    · exact ⟨-h, by rw [hw]; module⟩
  rcases hm with rfl | rfl
  · exact class_middle (y := quad y₀ y₁ y₂ y₃) 0 1 t 0 s δ hs0.le hs1.le
      (by simp only [quad_0, quad_1, zero_smul, add_zero]; rw [hct])
  · exact class_middle (y := quad y₀ y₁ y₂ y₃) 3 0 0 t s δ hs0.le hs1.le
      (by simp only [quad_0, quad_3, zero_smul, add_zero]; rw [hct])

/-- **`isRupert_equadσ`, certificate form.** -/
theorem rimCertPts_equadσ (V M : Finset ℝ³) {u : ℝ³} (_hu : u ≠ 0) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    {y₀ y₁ y₂ y₃ w : ℝ³} {h : ℝ} (_hh : h ≠ 0) (hw : w = y₀ - h • u) (_hwV : w ∈ V)
    (h₀ : y₀ ∈ V) (h₁ : y₁ ∈ V) (h₂ : y₂ ∈ V) (h₃ : y₃ ∈ V)
    (_n₀ : y₀ ∉ M) (_n₁ : y₁ ∉ M) (_n₂ : y₂ ∉ M) (_n₃ : y₃ ∉ M)
    (c₁ : 0 < σ * det3 (y₁ - y₀) (y₂ - y₀) u) (c₂ : 0 < σ * det3 (y₁ - y₀) (y₃ - y₀) u)
    (c₃ : 0 < σ * det3 (y₂ - y₁) (y₃ - y₁) u) (c₄ : 0 < σ * det3 (y₂ - y₁) (y₀ - y₁) u)
    (c₅ : 0 < σ * det3 (y₃ - y₂) (y₀ - y₂) u) (c₆ : 0 < σ * det3 (y₃ - y₂) (y₁ - y₂) u)
    (c₇ : 0 < σ * det3 (y₀ - y₃) (y₁ - y₃) u) (c₈ : 0 < σ * det3 (y₀ - y₃) (y₂ - y₃) u)
    (hrest : ∀ z ∈ V, z ∉ M → z ≠ w → z ≠ y₀ → z ≠ y₁ → z ≠ y₂ → z ≠ y₃ →
      0 < σ * det3 (y₁ - y₀) (z - y₀) u ∧ 0 < σ * det3 (y₂ - y₁) (z - y₁) u ∧
        0 < σ * det3 (y₃ - y₂) (z - y₂) u ∧ 0 < σ * det3 (y₀ - y₃) (z - y₃) u)
    (hz : IsRobustUnimodal (quad ⟪y₀, u⟫ ⟪y₁, u⟫ ⟪y₂, u⟫ ⟪y₃, u⟫))
    (hM : ∀ m ∈ M, EdgeMiddle u y₀ w y₁ y₃ h m) : RimCertPts V (σ • u) (quad y₀ y₁ y₂ y₃) := by
  classical
  refine rimCertPts_quadσ V hσ h₀ h₁ h₂ h₃ c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ (fun z hz => ?_) hz
  by_cases hzM : z ∈ M
  · exact Or.inl (quad_class_edgeMid hw (hM z hzM))
  by_cases ew : z = w
  · exact Or.inl (class_double (y := quad y₀ y₁ y₂ y₃) 0 (-h) (by rw [ew, hw, quad_0]; module))
  by_cases e0 : z = y₀
  · exact Or.inl ⟨0, 0, 0, 0, le_rfl, zero_le_one, by rw [e0]; simp [quad_0]⟩
  by_cases e1 : z = y₁
  · exact Or.inl ⟨1, 1, 0, 0, le_rfl, zero_le_one, by rw [e1]; simp [quad_1]⟩
  by_cases e2 : z = y₂
  · exact Or.inl ⟨2, 2, 0, 0, le_rfl, zero_le_one, by rw [e2]; simp [quad_2]⟩
  by_cases e3 : z = y₃
  · exact Or.inl ⟨3, 3, 0, 0, le_rfl, zero_le_one, by rw [e3]; simp [quad_3]⟩
  exact Or.inr (hrest z hz hzM ew e0 e1 e2 e3)

/-- **A pentagonal rim at the view `σ u`** from `Pent15`, with every point over a closed side
or strictly inside. -/
theorem rimCertPts_quintσ (V : Finset ℝ³) {u : ℝ³} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    {y₀ y₁ y₂ y₃ y₄ : ℝ³} (h₀ : y₀ ∈ V) (h₁ : y₁ ∈ V) (h₂ : y₂ ∈ V) (h₃ : y₃ ∈ V) (h₄ : y₄ ∈ V)
    (hc : Pent15 σ y₀ y₁ y₂ y₃ y₄ u)
    (hclass : ∀ z ∈ V, (∃ j₁ j₂ : ZMod 5, ∃ s δ : ℝ, 0 ≤ s ∧ s ≤ 1 ∧
      z = quint y₀ y₁ y₂ y₃ y₄ j₁ + s • (quint y₀ y₁ y₂ y₃ y₄ j₂ - quint y₀ y₁ y₂ y₃ y₄ j₁) +
        δ • u) ∨ PentIn σ y₀ y₁ y₂ y₃ y₄ u z)
    (hz : IsRobustUnimodal (quint ⟪y₀, u⟫ ⟪y₁, u⟫ ⟪y₂, u⟫ ⟪y₃, u⟫ ⟪y₄, u⟫)) :
    RimCertPts V (σ • u) (quint y₀ y₁ y₂ y₃ y₄) := by
  refine rimCertPts_of_class V (σ • u) (by norm_num) _ ?_ ?_ (fun z hz => ?_) ?_
  · intro i; rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl
    exacts [h₀, h₁, h₂, h₃, h₄]
  · intro i j hi hj
    rw [← det3_sigma]; exact pent15_cyc hc i j hi hj
  · rcases hclass z hz with h | h
    · exact Or.inl (class_sigma (sigma_sq hσ) h)
    · exact Or.inr fun i => by rw [← det3_sigma]; exact pentIn_rest h i
  · rw [quint_inner, quint_inner_sigma]; exact hz.sigma hσ

/-- A middle over a side of a pentagonal rim (vertex views). -/
theorem quint_class_mid {y₀ y₁ y₂ y₃ y₄ u m : ℝ³}
    (h : ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
      (m = y₀ + s • (y₁ - y₀) + δ • u ∨ m = y₁ + s • (y₂ - y₁) + δ • u ∨
        m = y₂ + s • (y₃ - y₂) + δ • u ∨ m = y₃ + s • (y₄ - y₃) + δ • u ∨
        m = y₄ + s • (y₀ - y₄) + δ • u)) :
    ∃ j₁ j₂ : ZMod 5, ∃ s δ : ℝ, 0 ≤ s ∧ s ≤ 1 ∧
      m = quint y₀ y₁ y₂ y₃ y₄ j₁ + s • (quint y₀ y₁ y₂ y₃ y₄ j₂ - quint y₀ y₁ y₂ y₃ y₄ j₁) +
        δ • u := by
  obtain ⟨s, δ, hs0, hs1, -, h | h | h | h | h⟩ := h
  · exact ⟨0, 1, s, δ, hs0.le, hs1.le, h⟩
  · exact ⟨1, 2, s, δ, hs0.le, hs1.le, h⟩
  · exact ⟨2, 3, s, δ, hs0.le, hs1.le, h⟩
  · exact ⟨3, 4, s, δ, hs0.le, hs1.le, h⟩
  · exact ⟨4, 0, s, δ, hs0.le, hs1.le, h⟩

/-- **`isRupert_vquintσ`, certificate form.** -/
theorem rimCertPts_vquintσ (V M : Finset ℝ³) {u : ℝ³} (_hu : u ≠ 0) {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1)
    {y₀ y₁ y₂ y₃ y₄ : ℝ³} (h₀ : y₀ ∈ V) (h₁ : y₁ ∈ V) (h₂ : y₂ ∈ V) (h₃ : y₃ ∈ V) (h₄ : y₄ ∈ V)
    (_n₀ : y₀ ∉ M) (_n₁ : y₁ ∉ M) (_n₂ : y₂ ∉ M) (_n₃ : y₃ ∉ M) (_n₄ : y₄ ∉ M)
    (hc : Pent15 σ y₀ y₁ y₂ y₃ y₄ u)
    (hrest : ∀ z ∈ V, z ∉ M → z ≠ y₀ → z ≠ y₁ → z ≠ y₂ → z ≠ y₃ → z ≠ y₄ →
      PentIn σ y₀ y₁ y₂ y₃ y₄ u z)
    (hz : IsRobustUnimodal (quint ⟪y₀, u⟫ ⟪y₁, u⟫ ⟪y₂, u⟫ ⟪y₃, u⟫ ⟪y₄, u⟫))
    (hM : ∀ m ∈ M, ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
      (m = y₀ + s • (y₁ - y₀) + δ • u ∨ m = y₁ + s • (y₂ - y₁) + δ • u ∨
        m = y₂ + s • (y₃ - y₂) + δ • u ∨ m = y₃ + s • (y₄ - y₃) + δ • u ∨
        m = y₄ + s • (y₀ - y₄) + δ • u)) : RimCertPts V (σ • u) (quint y₀ y₁ y₂ y₃ y₄) := by
  classical
  refine rimCertPts_quintσ V hσ h₀ h₁ h₂ h₃ h₄ hc (fun z hz => ?_) hz
  by_cases hzM : z ∈ M
  · exact Or.inl (quint_class_mid (hM z hzM))
  by_cases e0 : z = y₀
  · exact Or.inl ⟨0, 0, 0, 0, le_rfl, zero_le_one, by rw [e0]; simp [quint_0]⟩
  by_cases e1 : z = y₁
  · exact Or.inl ⟨1, 1, 0, 0, le_rfl, zero_le_one, by rw [e1]; simp [quint_1]⟩
  by_cases e2 : z = y₂
  · exact Or.inl ⟨2, 2, 0, 0, le_rfl, zero_le_one, by rw [e2]; simp [quint_2]⟩
  by_cases e3 : z = y₃
  · exact Or.inl ⟨3, 3, 0, 0, le_rfl, zero_le_one, by rw [e3]; simp [quint_3]⟩
  by_cases e4 : z = y₄
  · exact Or.inl ⟨4, 4, 0, 0, le_rfl, zero_le_one, by rw [e4]; simp [quint_4]⟩
  exact Or.inr (hrest z hz hzM e0 e1 e2 e3 e4)

/-- A middle of an edge view over a side at the apex `y₀` of a pentagonal rim. -/
theorem quint_class_edgeMid {y₀ y₁ y₂ y₃ y₄ u w m : ℝ³} {h : ℝ} (hw : w = y₀ - h • u)
    (hm : EdgeMiddle u y₀ w y₁ y₄ h m) :
    ∃ j₁ j₂ : ZMod 5, ∃ s δ : ℝ, 0 ≤ s ∧ s ≤ 1 ∧
      m = quint y₀ y₁ y₂ y₃ y₄ j₁ + s • (quint y₀ y₁ y₂ y₃ y₄ j₂ - quint y₀ y₁ y₂ y₃ y₄ j₁) +
        δ • u := by
  obtain ⟨c, s, δ, hc, hs0, hs1, -, hm⟩ := hm
  obtain ⟨t, hct⟩ : ∃ t : ℝ, c = y₀ + t • u := by
    rcases hc with rfl | ⟨rfl, -⟩
    · exact ⟨0, by simp⟩
    · exact ⟨-h, by rw [hw]; module⟩
  rcases hm with rfl | rfl
  · exact class_middle (y := quint y₀ y₁ y₂ y₃ y₄) 0 1 t 0 s δ hs0.le hs1.le
      (by simp only [quint_0, quint_1, zero_smul, add_zero]; rw [hct])
  · exact class_middle (y := quint y₀ y₁ y₂ y₃ y₄) 4 0 0 t s δ hs0.le hs1.le
      (by simp only [quint_0, quint_4, zero_smul, add_zero]; rw [hct])

/-- **`isRupert_equintσ`, certificate form.** -/
theorem rimCertPts_equintσ (V M : Finset ℝ³) {u : ℝ³} (_hu : u ≠ 0) {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1)
    {y₀ y₁ y₂ y₃ y₄ w : ℝ³} {h : ℝ} (_hh : h ≠ 0) (hw : w = y₀ - h • u) (_hwV : w ∈ V)
    (h₀ : y₀ ∈ V) (h₁ : y₁ ∈ V) (h₂ : y₂ ∈ V) (h₃ : y₃ ∈ V) (h₄ : y₄ ∈ V)
    (_n₀ : y₀ ∉ M) (_n₁ : y₁ ∉ M) (_n₂ : y₂ ∉ M) (_n₃ : y₃ ∉ M) (_n₄ : y₄ ∉ M)
    (hc : Pent15 σ y₀ y₁ y₂ y₃ y₄ u)
    (hrest : ∀ z ∈ V, z ∉ M → z ≠ w → z ≠ y₀ → z ≠ y₁ → z ≠ y₂ → z ≠ y₃ → z ≠ y₄ →
      PentIn σ y₀ y₁ y₂ y₃ y₄ u z)
    (hz : IsRobustUnimodal (quint ⟪y₀, u⟫ ⟪y₁, u⟫ ⟪y₂, u⟫ ⟪y₃, u⟫ ⟪y₄, u⟫))
    (hM : ∀ m ∈ M, EdgeMiddle u y₀ w y₁ y₄ h m) :
    RimCertPts V (σ • u) (quint y₀ y₁ y₂ y₃ y₄) := by
  classical
  refine rimCertPts_quintσ V hσ h₀ h₁ h₂ h₃ h₄ hc (fun z hz => ?_) hz
  by_cases hzM : z ∈ M
  · exact Or.inl (quint_class_edgeMid hw (hM z hzM))
  by_cases ew : z = w
  · exact Or.inl (class_double (y := quint y₀ y₁ y₂ y₃ y₄) 0 (-h)
      (by rw [ew, hw, quint_0]; module))
  by_cases e0 : z = y₀
  · exact Or.inl ⟨0, 0, 0, 0, le_rfl, zero_le_one, by rw [e0]; simp [quint_0]⟩
  by_cases e1 : z = y₁
  · exact Or.inl ⟨1, 1, 0, 0, le_rfl, zero_le_one, by rw [e1]; simp [quint_1]⟩
  by_cases e2 : z = y₂
  · exact Or.inl ⟨2, 2, 0, 0, le_rfl, zero_le_one, by rw [e2]; simp [quint_2]⟩
  by_cases e3 : z = y₃
  · exact Or.inl ⟨3, 3, 0, 0, le_rfl, zero_le_one, by rw [e3]; simp [quint_3]⟩
  by_cases e4 : z = y₄
  · exact Or.inl ⟨4, 4, 0, 0, le_rfl, zero_le_one, by rw [e4]; simp [quint_4]⟩
  exact Or.inr (hrest z hz hzM ew e0 e1 e2 e3 e4)


end Minimality

end
