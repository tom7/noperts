module

public import Minimality.Tilt
public import Minimality.Generic.PV.SK
public import Minimality.L8T3

@[expose] public section

/-!
# Lemma TA (tie merge): an adjacent depth tie on the rim, broken by a tilt along the tied edge

At a view `u₀` where the rim corners `x a`, `x (a+1)` are adjacent and have equal depth, if the
cycle with the two entries merged into one (`skipAt z a`: entry `a` deleted, `a+1` carrying the tied
value) is strictly unimodal, then one of the two strict orderings of the pair gives a strictly
unimodal cycle, and the tilt `v = ±(x (a+1) - x a)` realizes it.

* `isCyclicUnimodal_of_tieMerge` (combinatorial core): a strict refinement `z'` of `z` in which
  `z' a` lies strictly between its neighbours, in the direction of the step `z (a-1) → z a`,
  is cyclically unimodal when `skipAt z a` is.  No tie is needed here.
* `isRupert_of_tieMerge'`: geometric wrapper with any tilt `v` (rim rows as `TiltSign`), the tie
  `⟪x a, u₀⟫ = ⟪x (a+1), u₀⟫`, merged unimodality, and the sign of `⟪x (a+1) - x a, v⟫`
  continuing the step from `a-1` to `a`.
* `isRupert_of_tieMerge`: rim rows strict at `u₀`; the tilt is `±(x (a+1) - x a)`.
* `isRupert_of_tieMerge_four`: 4-corner rim; merged unimodality is just distinctness.
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

/-- Strict comparisons kept, both sides injective: cyclic unimodality transfers. -/
theorem isCyclicUnimodal_of_refine {k : ℕ} [NeZero k] {z w : ZMod k → ℝ}
    (hz : IsCyclicUnimodal z) (hw : Function.Injective w) (hord : ∀ p q, z p < z q → w p < w q) :
    IsCyclicUnimodal w := by
  have hiff : ∀ p q, z p < z q ↔ w p < w q := by
    intro p q
    refine ⟨hord p q, fun h => ?_⟩
    rcases lt_trichotomy (z p) (z q) with h' | h' | h'
    · exact h'
    · exact absurd (congrArg w (hz.1 h')) h.ne
    · exact absurd (hord q p h') (lt_asymm h)
  refine ⟨hw, ?_⟩
  rw [← hz.2]
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, hiff]

/-- **Lemma TA, combinatorial core.**  If the cycle `z` with entry `i` deleted is cyclically
unimodal (`skipAt z i`), and `z'` is injective, keeps every strict comparison of `z`, and puts
`z' i` strictly between `z' (i-1)` and `z' (i+1)` in the direction of the step from `i-1` to `i`,
then `z'` is cyclically unimodal.  Used at an adjacent tie `z i = z (i+1)`, where the order of
`z' i, z' (i+1)` is free. -/
theorem isCyclicUnimodal_of_tieMerge {m : ℕ} [NeZero m] (hm : 2 ≤ m) {z z' : ZMod (m + 1) → ℝ}
    {i : ZMod (m + 1)} (hU : IsCyclicUnimodal (skipAt z i)) (hinj : Function.Injective z')
    (hord : ∀ p q, z p < z q → z' p < z' q)
    (hb : (z (i - 1) < z i ∧ z' i < z' (i + 1)) ∨ (z i < z (i - 1) ∧ z' (i + 1) < z' i)) :
    IsCyclicUnimodal z' := by
  have hb' : (z' (i - 1) < z' i ∧ z' i < z' (i + 1)) ∨ (z' (i + 1) < z' i ∧ z' i < z' (i - 1)) := by
    rcases hb with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨hord _ _ h1, h2⟩
    · exact Or.inr ⟨h2, hord _ _ h1⟩
  rw [skipAt_unimodal_iff hm z' i hinj hb']
  exact isCyclicUnimodal_of_refine hU (hinj.comp (phi_inj i)) fun p q h => hord _ _ h

/-- The depth predicate of Lemma TA: every strict comparison of `z₀` kept, and the pair
`(a, a+1)` ordered so that `a` lies between its neighbours. -/
def TieMergeQ {k : ℕ} (z₀ : ZMod k → ℝ) (a : ZMod k) (z : ZMod k → ℝ) : Prop :=
  (∀ p q, z₀ p < z₀ q → z p < z q) ∧
    ((z₀ (a - 1) < z₀ a ∧ z a < z (a + 1)) ∨ (z₀ a < z₀ (a - 1) ∧ z (a + 1) < z a))

theorem isOpen_tieMergeQ {k : ℕ} [NeZero k] (z₀ : ZMod k → ℝ) (a : ZMod k) :
    IsOpen {z | TieMergeQ z₀ a z} := by
  have hlt : ∀ p q : ZMod k, IsOpen {z : ZMod k → ℝ | z p < z q} := fun p q =>
    isOpen_lt (continuous_apply p) (continuous_apply q)
  have hc : ∀ (P : Prop) (S : Set (ZMod k → ℝ)), IsOpen S → IsOpen {z | P → z ∈ S} := by
    intro P S hS
    by_cases hP : P
    · simpa [hP] using hS
    · simp [hP]
  have hc' : ∀ (P : Prop) (S : Set (ZMod k → ℝ)), IsOpen S → IsOpen {z | P ∧ z ∈ S} := by
    intro P S hS
    by_cases hP : P
    · simpa [hP] using hS
    · simp [hP]
  have h1 : IsOpen {z : ZMod k → ℝ | ∀ p q, z₀ p < z₀ q → z p < z q} := by
    have : {z : ZMod k → ℝ | ∀ p q, z₀ p < z₀ q → z p < z q} =
        ⋂ p, ⋂ q, {z | z₀ p < z₀ q → z ∈ {z : ZMod k → ℝ | z p < z q}} := by
      ext z; simp
    rw [this]
    exact isOpen_iInter_of_finite fun p => isOpen_iInter_of_finite fun q => hc _ _ (hlt p q)
  exact h1.inter ((hc' _ _ (hlt a (a + 1))).union (hc' _ _ (hlt (a + 1) a)))

/-- **Lemma TA, tilt form.**  Rim `x` (a cycle of `m + 1 ≥ 3` points of `V`) with the tests of
Lemma 8.0 at `(u₀, v)`, an adjacent depth tie `⟪x a, u₀⟫ = ⟪x (a+1), u₀⟫`, the merged cycle
`skipAt z₀ a` cyclically unimodal (all other depths distinct, also from the tied value), and the
tilt ordering the pair so that `a` continues the step from `a-1`: `V` is Rupert. -/
theorem isRupert_of_tieMerge' (V : Finset ℝ³) (u₀ v : ℝ³) (hu₀ : u₀ ≠ 0) {m : ℕ} [NeZero m]
    (hm : 2 ≤ m) (x : ZMod (m + 1) → ℝ³) (hxV : ∀ i, x i ∈ V)
    (hcyc : ∀ i j, j ≠ i → j ≠ i + 1 → TiltSign (x (i + 1) - x i) (x j - x i) u₀ v)
    (hrest : ∀ y ∈ V, (∀ j, y ≠ x j) → ∀ i, TiltSign (x (i + 1) - x i) (y - x i) u₀ v)
    (a : ZMod (m + 1)) (htie : ⟪x a, u₀⟫ = ⟪x (a + 1), u₀⟫)
    (hU : IsCyclicUnimodal (skipAt (fun i => ⟪x i, u₀⟫) a))
    (hv : (⟪x (a - 1), u₀⟫ < ⟪x a, u₀⟫ ∧ 0 < ⟪x (a + 1) - x a, v⟫) ∨
      (⟪x a, u₀⟫ < ⟪x (a - 1), u₀⟫ ∧ ⟪x (a + 1) - x a, v⟫ < 0)) : IsRupert V := by
  set z₀ : ZMod (m + 1) → ℝ := fun i => ⟪x i, u₀⟫ with hz₀
  have e1 : ∀ (ε : ℝ) (p : ℝ³), ⟪p, u₀ + ε • v⟫ = ⟪p, u₀⟫ + ε * ⟪p, v⟫ := by
    intro ε p; rw [inner_add_right, inner_smul_right]
  refine isRupert_of_tilted_unimodal' V u₀ v hu₀ (by omega) x hxV hcyc hrest (TieMergeQ z₀ a)
    (isOpen_tieMergeQ z₀ a) ?_ ?_ ?_
  · rintro z c hc ⟨h1, h2⟩
    refine ⟨fun p q h => mul_lt_mul_of_pos_left (h1 p q h) hc, ?_⟩
    rcases h2 with ⟨h3, h4⟩ | ⟨h3, h4⟩
    · exact Or.inl ⟨h3, mul_lt_mul_of_pos_left h4 hc⟩
    · exact Or.inr ⟨h3, mul_lt_mul_of_pos_left h4 hc⟩
  · have hpair : ∀ p q : ZMod (m + 1), ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        z₀ p < z₀ q → ⟪x p, u₀ + ε • v⟫ < ⟪x q, u₀ + ε • v⟫ := by
      intro p q
      by_cases h : z₀ p < z₀ q
      · have := eventually_pos_affine (A := z₀ q - z₀ p) (B := ⟪x q, v⟫ - ⟪x p, v⟫)
          (Or.inl (sub_pos.2 h))
        filter_upwards [this] with ε hε _
        rw [e1, e1]; simp only [hz₀] at hε; nlinarith
      · exact Eventually.of_forall fun _ h' => absurd h' h
    have hall := eventually_all.2 fun p => eventually_all.2 fun q => hpair p q
    have hd : ∀ ε : ℝ, ⟪x (a + 1), u₀ + ε • v⟫ - ⟪x a, u₀ + ε • v⟫ =
        ε * ⟪x (a + 1) - x a, v⟫ := by
      intro ε; rw [e1, e1, ← htie, inner_sub_left]; ring
    rcases hv with ⟨h3, h4⟩ | ⟨h3, h4⟩
    · filter_upwards [hall, self_mem_nhdsWithin] with ε hε hε0
      refine ⟨hε, Or.inl ⟨h3, ?_⟩⟩
      have := hd ε
      have : 0 < ε * ⟪x (a + 1) - x a, v⟫ := mul_pos hε0 h4
      linarith
    · filter_upwards [hall, self_mem_nhdsWithin] with ε hε hε0
      refine ⟨hε, Or.inr ⟨h3, ?_⟩⟩
      have := hd ε
      have : ε * ⟪x (a + 1) - x a, v⟫ < 0 := mul_neg_of_pos_of_neg hε0 h4
      linarith
  · rintro z hz ⟨h1, h2⟩
    exact isCyclicUnimodal_of_tieMerge hm hU hz h1 h2

/-- In the merged cycle `skipAt z a` (`m ≥ 2`), the entries at `a-1` and `a+1` differ. -/
theorem skipAt_ne_ends {m : ℕ} [NeZero m] (hm : 2 ≤ m) {z : ZMod (m + 1) → ℝ} {a : ZMod (m + 1)}
    (hU : Function.Injective (skipAt z a)) : z (a + 1) ≠ z (a - 1) := by
  have : Fact (1 < m) := ⟨by omega⟩
  intro h
  have h0 : skipAt z a 0 = skipAt z a (-1) := by
    have e0 : skipAt z a 0 = z (a + 1) := by simp [skipAt]
    have e1 : skipAt z a (-1) = z (a - 1) := by
      show z (phi a (-1)) = _; rw [phi_neg_one]
    rw [e0, e1, h]
  have := hU h0
  apply one_ne_zero (α := ZMod m)
  simpa using (neg_eq_zero.mp this.symm)

/-- **Lemma TA.**  Rim `x` with all tests of Lemma 8.0 strict at `u₀` (the rim is the same on a
neighbourhood of `u₀`), an adjacent depth tie `⟪x a, u₀⟫ = ⟪x (a+1), u₀⟫`, and the merged cycle
strictly unimodal: `V` is Rupert (tilt `±(x (a+1) - x a)`). -/
theorem isRupert_of_tieMerge (V : Finset ℝ³) (u₀ : ℝ³) (hu₀ : u₀ ≠ 0) {m : ℕ} [NeZero m]
    (hm : 2 ≤ m) (x : ZMod (m + 1) → ℝ³) (hxV : ∀ i, x i ∈ V)
    (hcyc : ∀ i j, j ≠ i → j ≠ i + 1 → 0 < det3 (x (i + 1) - x i) (x j - x i) u₀)
    (hrest : ∀ y ∈ V, (∀ j, y ≠ x j) → ∀ i, 0 < det3 (x (i + 1) - x i) (y - x i) u₀)
    (a : ZMod (m + 1)) (htie : ⟪x a, u₀⟫ = ⟪x (a + 1), u₀⟫)
    (hU : IsCyclicUnimodal (skipAt (fun i => ⟪x i, u₀⟫) a)) : IsRupert V := by
  have hd : x (a + 1) - x a ≠ 0 := by
    intro h
    have hne1 : a + 1 + 1 ≠ a := by
      intro e
      have h2 : ((2 : ℕ) : ZMod (m + 1)) = 0 := by
        have : a + 1 + 1 = a + ((2 : ℕ) : ZMod (m + 1)) := by push_cast; ring
        rw [this] at e; simpa using e
      rw [ZMod.natCast_eq_zero_iff] at h2
      have := Nat.le_of_dvd (by norm_num) h2; omega
    have hne2 : a + 1 + 1 ≠ a + 1 := by
      intro e
      have : Fact (1 < m + 1) := ⟨by omega⟩
      simp at e
    have := hcyc a (a + 1 + 1) hne1 hne2
    have z0 : ∀ p q : ℝ³, det3 0 p q = 0 := fun p q => by
      simp [det3, cross, PiLp.inner_apply, Fin.sum_univ_three]
    rw [h, z0] at this
    exact lt_irrefl _ this
  have hpos : 0 < ⟪x (a + 1) - x a, x (a + 1) - x a⟫ := real_inner_self_pos.2 hd
  have hne : ⟪x (a - 1), u₀⟫ ≠ ⟪x a, u₀⟫ := by
    rw [htie]
    exact (skipAt_ne_ends hm (z := fun i => ⟪x i, u₀⟫) hU.1).symm
  rcases lt_or_gt_of_ne hne with h | h
  · refine isRupert_of_tieMerge' V u₀ (x (a + 1) - x a) hu₀ hm x hxV
      (fun i j hi hj => Or.inl (hcyc i j hi hj)) (fun y hy hyx i => Or.inl (hrest y hy hyx i))
      a htie hU (Or.inl ⟨h, hpos⟩)
  · refine isRupert_of_tieMerge' V u₀ (-(x (a + 1) - x a)) hu₀ hm x hxV
      (fun i j hi hj => Or.inl (hcyc i j hi hj)) (fun y hy hyx i => Or.inl (hrest y hy hyx i))
      a htie hU (Or.inr ⟨h, by rw [inner_neg_right]; linarith⟩)

/-- **Lemma TA, four corners.**  A 4-corner rim with an adjacent tie and the three merged values
distinct satisfies the merged hypothesis. -/
theorem isRupert_of_tieMerge_four (V : Finset ℝ³) (u₀ : ℝ³) (hu₀ : u₀ ≠ 0)
    (x : ZMod 4 → ℝ³) (hxV : ∀ i, x i ∈ V)
    (hcyc : ∀ i j, j ≠ i → j ≠ i + 1 → 0 < det3 (x (i + 1) - x i) (x j - x i) u₀)
    (hrest : ∀ y ∈ V, (∀ j, y ≠ x j) → ∀ i, 0 < det3 (x (i + 1) - x i) (y - x i) u₀)
    (a : ZMod 4) (htie : ⟪x a, u₀⟫ = ⟪x (a + 1), u₀⟫)
    (hdist : Function.Injective (skipAt (m := 3) (fun i => ⟪x i, u₀⟫) a)) : IsRupert V :=
  isRupert_of_tieMerge V u₀ hu₀ (m := 3) (by norm_num) x hxV hcyc hrest a htie
    (isCyclicUnimodal_three hdist)

end Minimality

end
