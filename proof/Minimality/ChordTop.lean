module

public import Minimality.DepthSeparated

@[expose] public section

/-!
# Lemma CT (the chord on top) and the triangle-rim lemma

On a strictly convex counterclockwise polygon `p` (the rim of `K′` at a view) take an edge
`a → a + 1` (the chord), its predecessor `a − 1` and the successor `a + 2`.

* `IsAntipodalChord p a`: the turn from the edge `(a − 1, a)` to the edge `(a + 1, a + 2)` is at
  least `π`: `cross2 (p a − p (a − 1)) (p (a + 2) − p (a + 1)) ≤ 0` (the A* sign of
  k1c/COVER145.md §2.1, item (v)).
* `IsCcwPolygon.antipodalChord_iff_left` / `_iff_right` (§2.1, (i) ⇔ (v) ⇔ (ii)): it holds iff
  `a + 1` is antipodal to the edge `(a − 1, a)` (`−n ∈ N_{a+1}`), iff `a` is antipodal to the edge
  `(a + 1, a + 2)`.  Helper: `IsCcwPolygon.mem_normalConeAt_of_local` (a local extremum of a
  nonzero linear functional on the corners is global).
* `isDepthSeparatedPair_chordTop` (Lemma CT, §2.3): if the chord ends are strictly the two
  deepest (or the two shallowest) corners, with distinct depths, and the chord is antipodal, then
  `(edge a − 1, corner a + 1)` (when `z (a + 1)` is between `z a` and the rest) or
  `(edge a + 1, corner a)` is a depth-separated pair (`IsDepthSeparatedPair`, Theorem 8.10).
  One-sided forms `isDepthSeparatedPair_chordTop_left`, `_right` (only the lower end needs to lie
  above the rest).
* `isDepthSeparatedPair_triangle`, `exists_isDepthSeparatedPair_triangle` (triangle-rim lemma,
  §2.3): on a triangle the middle-depth corner and the opposite edge are a depth-separated pair.
* `isRupert_of_chords_chordTop`, `isRupert_of_chords_triangle`: Proposition 8.8
  (`isRupert_of_chords_depthSeparated`) with these pairs.
* `isAntipodalChord_proj_iff` (screen form) and `isAntipodalChord_edgeView_iff` (§2.2): at a view
  `u` the sign is `det3 (x a − x (a − 1)) (x (a + 2) − x (a + 1)) u ≤ 0`; at the edge view
  `u = x a − m` it says that `x (a + 1)` is a farthest rim corner from the plane through
  `x (a − 1), x a, m` (on the side of the rim).

Not here: the no-HDN hypothesis (generic views of an arc) and the A* set in a sector (§2.4).
-/

namespace Minimality

open scoped RealInnerProductSpace
open Finset

/-- **The A* sign** of the chord `a → a + 1`: the edges `(a − 1, a)` and `(a + 1, a + 2)` turn
by at least `π`. -/
def IsAntipodalChord {k : ℕ} (p : ZMod k → ℝ²) (a : ZMod k) : Prop :=
  cross2 (p a - p (a - 1)) (p (a + 2) - p (a + 1)) ≤ 0

theorem inner_neg_outNormal (a b w : ℝ²) : ⟪-outNormal a b, w⟫ = cross2 (b - a) w := by
  rw [inner_neg_left, inner_outNormal, neg_neg]

namespace IsCcwPolygon

variable {k : ℕ} {p : ZMod k → ℝ²}

/-- A local maximum of a nonzero linear functional at a corner is a global one: the functional
is in the normal cone there. -/
theorem mem_normalConeAt_of_local (hp : IsCcwPolygon p) {ν : ℝ²} (hν : ν ≠ 0) {s : ZMod k}
    (h1 : 0 ≤ ⟪ν, p s - p (s - 1)⟫) (h2 : ⟪ν, p (s + 1) - p s⟫ ≤ 0) :
    ν ∈ normalConeAt (convexHull ℝ (Set.range p)) (p s) := by
  have hall : ∀ j, ⟪ν, p j⟫ ≤ ⟪ν, p s⟫ := by
    intro j
    by_cases hj1 : j = s - 1
    · subst hj1; rw [inner_sub_right] at h1; linarith
    by_cases hj2 : j = s
    · subst hj2; exact le_rfl
    by_cases hj3 : j = s + 1
    · subst hj3; rw [inner_sub_right] at h2; linarith
    exact (hp.lt_of_localMax hν h1 h2 hj1 hj2 hj3).le
  intro q hq
  have hsub : convexHull ℝ (Set.range p) ⊆ {w : ℝ² | ⟪ν, w⟫ ≤ ⟪ν, p s⟫} := by
    refine convexHull_min ?_ (convex_halfSpace_le (f := fun w : ℝ² => ⟪ν, w⟫) ?_ _)
    · rintro _ ⟨j, rfl⟩
      exact hall j
    · exact ⟨fun x y => inner_add_right _ _ _, fun c x => by simp [real_inner_smul_right]⟩
  have := hsub hq
  simp only [Set.mem_ofPred_eq] at this
  rw [inner_sub_right]
  linarith

theorem add_two_eq (a : ZMod k) : a + 2 = a + 1 + 1 := by ring

/-- **§2.1, (v) ⇔ (i).**  The chord is antipodal iff `a + 1` is antipodal to the edge
`(a − 1, a)`. -/
theorem antipodalChord_iff_left (hp : IsCcwPolygon p) (a : ZMod k) :
    IsAntipodalChord p a ↔
      -outNormal (p (a - 1)) (p a) ∈ normalConeAt (convexHull ℝ (Set.range p)) (p (a + 1)) := by
  have he := hp.cross2_edge_pos a
  constructor
  · intro hA
    have h1 : 0 ≤ ⟪-outNormal (p (a - 1)) (p a), p (a + 1) - p (a + 1 - 1)⟫ := by
      rw [inner_neg_outNormal, add_sub_cancel_right]; exact he.le
    have hν : -outNormal (p (a - 1)) (p a) ≠ 0 := by
      intro h0
      rw [inner_neg_outNormal, add_sub_cancel_right] at h1
      have : ⟪-outNormal (p (a - 1)) (p a), p (a + 1) - p a⟫ = 0 := by rw [h0, inner_zero_left]
      rw [inner_neg_outNormal] at this
      linarith
    refine hp.mem_normalConeAt_of_local hν h1 ?_
    rw [inner_neg_outNormal, ← add_two_eq]; exact hA
  · intro h
    have := h (p (a + 2)) (subset_convexHull ℝ _ ⟨_, rfl⟩)
    rwa [inner_neg_outNormal] at this

/-- **§2.1, (v) ⇔ (ii).**  The chord is antipodal iff `a` is antipodal to the edge
`(a + 1, a + 2)`. -/
theorem antipodalChord_iff_right (hp : IsCcwPolygon p) (a : ZMod k) :
    IsAntipodalChord p a ↔
      -outNormal (p (a + 1)) (p (a + 2)) ∈ normalConeAt (convexHull ℝ (Set.range p)) (p a) := by
  have he := hp.cross2_edge_pos (a + 1)
  rw [add_sub_cancel_right, ← add_two_eq] at he
  constructor
  · intro hA
    have h2 : ⟪-outNormal (p (a + 1)) (p (a + 2)), p (a + 1) - p a⟫ ≤ 0 := by
      rw [inner_neg_outNormal, cross2_comm]; linarith
    have hν : -outNormal (p (a + 1)) (p (a + 2)) ≠ 0 := by
      intro h0
      have : ⟪-outNormal (p (a + 1)) (p (a + 2)), p (a + 1) - p a⟫ = 0 := by
        rw [h0, inner_zero_left]
      rw [inner_neg_outNormal, cross2_comm] at this
      linarith
    refine hp.mem_normalConeAt_of_local hν ?_ h2
    rw [inner_neg_outNormal, cross2_comm]
    unfold IsAntipodalChord at hA
    linarith
  · intro h
    have := h (p (a - 1)) (subset_convexHull ℝ _ ⟨_, rfl⟩)
    rw [inner_neg_outNormal] at this
    have e : cross2 (p (a + 2) - p (a + 1)) (p (a - 1) - p a) =
        cross2 (p a - p (a - 1)) (p (a + 2) - p (a + 1)) := by
      simp only [cross2, PiLp.sub_apply]; ring
    unfold IsAntipodalChord
    linarith

end IsCcwPolygon

/-- Negating the depths keeps a depth-separated pair. -/
theorem IsDepthSeparatedPair.neg {k : ℕ} {p : ZMod k → ℝ²} {z : ZMod k → ℝ} {a c : ZMod k}
    (h : IsDepthSeparatedPair p z a c) : IsDepthSeparatedPair p (fun i => -z i) a c := by
  obtain ⟨hn, hz⟩ := h
  refine ⟨hn, ?_⟩
  simp only [neg_lt_neg_iff]
  rcases hz with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inr ⟨h1, h2⟩
  · exact Or.inl ⟨h1, h2⟩

theorem zmod_val_sub_two {k : ℕ} [NeZero k] (hk : 3 ≤ k) (a : ZMod k) :
    (a - 1 - (a + 1)).val = k - 2 := by
  have e : a - 1 - (a + 1) = ((k - 2 : ℕ) : ZMod k) := by
    rw [Nat.cast_sub (by omega), ZMod.natCast_self]; push_cast; ring
  rw [e, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]

theorem zmod_val_add_one_sub {k : ℕ} [NeZero k] (hk : 2 ≤ k) (a : ZMod k) :
    (a + 1 - a).val = 1 := by
  have e : a + 1 - a = ((1 : ℕ) : ZMod k) := by push_cast; ring
  rw [e, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]

/-- **Lemma CT, the lower end `a + 1`.**  If the chord `a → a + 1` is antipodal, every other
corner lies strictly below `z (a + 1)` and `z (a + 1) < z a`, then `(edge a − 1, corner a + 1)` is
a depth-separated pair: the two chains are `{a}` (above) and the rest (below). -/
theorem isDepthSeparatedPair_chordTop_left {k : ℕ} {p : ZMod k → ℝ²}
    (hp : IsCcwPolygon p) {z : ZMod k → ℝ} {a : ZMod k} (hA : IsAntipodalChord p a)
    (hz : ∀ j, j ≠ a → j ≠ a + 1 → z j < z (a + 1)) (hab : z (a + 1) < z a) :
    IsDepthSeparatedPair p z (a - 1) (a + 1) := by
  have hk := hp.1
  have : NeZero k := ⟨by omega⟩
  refine ⟨?_, Or.inr ⟨fun s hs0 hs => ?_, fun s hs1 hs2 => ?_⟩⟩
  · rw [sub_add_cancel]; exact (hp.antipodalChord_iff_left a).mp hA
  · rw [zmod_val_sub_two hk] at hs
    apply hz
    · intro h
      have hne := zmod_add_ne (k := k) (a := s) (b := k - 1) (by omega) (by omega) (by omega)
        (a + 1)
      rw [zmod_natCast_pred (by omega), add_neg_cancel_right] at hne
      exact hne h
    · exact (IsCcwPolygon.ne_add_natCast hs0 (by omega) (a + 1)).symm
  · rw [zmod_val_sub_two hk] at hs1
    obtain rfl : s = k - 1 := by omega
    rw [zmod_natCast_pred (by omega), add_neg_cancel_right]
    exact hab

/-- **Lemma CT, the lower end `a`.**  If the chord `a → a + 1` is antipodal, every other corner
lies strictly below `z a` and `z a < z (a + 1)`, then `(edge a + 1, corner a)` is a
depth-separated pair: the chains are `{a + 1}` (above) and the rest (below). -/
theorem isDepthSeparatedPair_chordTop_right {k : ℕ} {p : ZMod k → ℝ²}
    (hp : IsCcwPolygon p) {z : ZMod k → ℝ} {a : ZMod k} (hA : IsAntipodalChord p a)
    (hz : ∀ j, j ≠ a → j ≠ a + 1 → z j < z a) (hab : z a < z (a + 1)) :
    IsDepthSeparatedPair p z (a + 1) a := by
  have hk := hp.1
  have : NeZero k := ⟨by omega⟩
  refine ⟨?_, Or.inl ⟨fun s hs0 hs => ?_, fun s hs1 hs2 => ?_⟩⟩
  · rw [← IsCcwPolygon.add_two_eq]; exact (hp.antipodalChord_iff_right a).mp hA
  · rw [zmod_val_add_one_sub (by omega)] at hs
    obtain rfl : s = 1 := by omega
    simpa using hab
  · rw [zmod_val_add_one_sub (by omega)] at hs1
    apply hz
    · exact (IsCcwPolygon.ne_add_natCast (by omega) hs2 a).symm
    · have hne := zmod_add_ne (k := k) (a := s) (b := 1) hs2 (by omega) (by omega) a
      simpa using hne

/-- **Lemma CT** (k1c/COVER145.md §2.3).  If the chord ends `a, a + 1` of an antipodal chord
(`IsAntipodalChord`) have distinct depths and are strictly the two deepest, or strictly the two
shallowest, corners, then `(edge a − 1, corner a + 1)` or `(edge a + 1, corner a)` is a
depth-separated pair. -/
theorem isDepthSeparatedPair_chordTop {k : ℕ} {p : ZMod k → ℝ²}
    (hp : IsCcwPolygon p) {z : ZMod k → ℝ} {a : ZMod k} (hA : IsAntipodalChord p a)
    (hz : (∀ j, j ≠ a → j ≠ a + 1 → z j < min (z a) (z (a + 1))) ∨
      (∀ j, j ≠ a → j ≠ a + 1 → max (z a) (z (a + 1)) < z j))
    (hne : z a ≠ z (a + 1)) :
    IsDepthSeparatedPair p z (a - 1) (a + 1) ∨ IsDepthSeparatedPair p z (a + 1) a := by
  rcases hz with hz | hz
  · rcases lt_or_gt_of_ne hne with h | h
    · exact Or.inr (isDepthSeparatedPair_chordTop_right hp hA
        (fun j h1 h2 => (lt_min_iff.mp (hz j h1 h2)).1) h)
    · exact Or.inl (isDepthSeparatedPair_chordTop_left hp hA
        (fun j h1 h2 => (lt_min_iff.mp (hz j h1 h2)).2) h)
  · have hz' : ∀ j, j ≠ a → j ≠ a + 1 → -z j < min (-z a) (-z (a + 1)) := fun j h1 h2 => by
      have := max_lt_iff.mp (hz j h1 h2)
      exact lt_min (by linarith [this.1]) (by linarith [this.2])
    rcases lt_or_gt_of_ne hne with h | h
    · have := (isDepthSeparatedPair_chordTop_left (z := fun i => -z i) hp hA
        (fun j h1 h2 => (lt_min_iff.mp (hz' j h1 h2)).2) (by simpa using h)).neg
      exact Or.inl (by simpa using this)
    · have := (isDepthSeparatedPair_chordTop_right (z := fun i => -z i) hp hA
        (fun j h1 h2 => (lt_min_iff.mp (hz' j h1 h2)).1) (by simpa using h)).neg
      exact Or.inr (by simpa using this)

/-- Every chord of a triangle is antipodal. -/
theorem isAntipodalChord_triangle {p : ZMod 3 → ℝ²} (hp : IsCcwPolygon p) (c : ZMod 3) :
    IsAntipodalChord p c := by
  have h1 : ∀ c : ZMod 3, c + 2 ≠ c := by decide
  have h2 : ∀ c : ZMod 3, c + 2 ≠ c + 1 := by decide
  have h := hp.2 c (c + 2) (h1 c) (h2 c)
  have e : c - 1 = c + 2 := (show ∀ c : ZMod 3, c - 1 = c + 2 by decide) c
  unfold IsAntipodalChord
  rw [e]
  have : cross2 (p c - p (c + 2)) (p (c + 2) - p (c + 1)) =
      -cross2 (p (c + 1) - p c) (p (c + 2) - p c) := by
    simp only [cross2, PiLp.sub_apply]; ring
  linarith

/-- **Triangle-rim lemma** (k1c/COVER145.md §2.3).  On a triangle, a corner `c` whose depth lies
strictly between the other two and the opposite edge `(c + 1, c + 2)` are a depth-separated
pair. -/
theorem isDepthSeparatedPair_triangle {p : ZMod 3 → ℝ²} (hp : IsCcwPolygon p) {z : ZMod 3 → ℝ}
    {c : ZMod 3} (hc : (z (c + 1) - z c) * (z (c + 2) - z c) < 0) :
    IsDepthSeparatedPair p z (c + 1) c := by
  have hval : (c + 1 - c).val = 1 := zmod_val_add_one_sub (by norm_num) c
  have hn : -outNormal (p (c + 1)) (p (c + 1 + 1)) ∈
      normalConeAt (convexHull ℝ (Set.range p)) (p c) := by
    rw [← IsCcwPolygon.add_two_eq]
    exact (hp.antipodalChord_iff_right c).mp (isAntipodalChord_triangle hp c)
  refine ⟨hn, ?_⟩
  rw [hval]
  have hs : ∀ s : ℕ, 1 < s → s < 3 → c + (s : ZMod 3) = c + 2 := fun s h1 h2 => by
    obtain rfl : s = 2 := by omega
    rfl
  have h0 : z (c + 1) - z c ≠ 0 := by
    intro h
    rw [h, zero_mul] at hc
    exact lt_irrefl _ hc
  rcases lt_or_gt_of_ne h0 with h | h
  · have h' : 0 < z (c + 2) - z c := by nlinarith
    refine Or.inr ⟨fun s h1 h2 => ?_, fun s h1 h2 => ?_⟩
    · obtain rfl : s = 1 := by omega
      simp only [Nat.cast_one]; linarith
    · rw [hs s h1 h2]; linarith
  · have h' : z (c + 2) - z c < 0 := by nlinarith
    refine Or.inl ⟨fun s h1 h2 => ?_, fun s h1 h2 => ?_⟩
    · obtain rfl : s = 1 := by omega
      simp only [Nat.cast_one]; linarith
    · rw [hs s h1 h2]; linarith

/-- **Triangle-rim lemma, existence form.**  A triangle with distinct corner depths has a
depth-separated pair (the middle-depth corner and the opposite edge). -/
theorem exists_isDepthSeparatedPair_triangle {p : ZMod 3 → ℝ²} (hp : IsCcwPolygon p)
    {z : ZMod 3 → ℝ} (hz : Function.Injective z) : ∃ c, IsDepthSeparatedPair p z (c + 1) c := by
  have h01 : z 0 ≠ z 1 := fun h => absurd (hz h) (by decide)
  have h02 : z 0 ≠ z 2 := fun h => absurd (hz h) (by decide)
  have h12 : z 1 ≠ z 2 := fun h => absurd (hz h) (by decide)
  have e0 : ((0 : ZMod 3) + 1 = 1) ∧ ((0 : ZMod 3) + 2 = 2) := by decide
  have e1 : ((1 : ZMod 3) + 1 = 2) ∧ ((1 : ZMod 3) + 2 = 0) := by decide
  have e2 : ((2 : ZMod 3) + 1 = 0) ∧ ((2 : ZMod 3) + 2 = 1) := by decide
  rcases lt_or_gt_of_ne h01 with a | a <;> rcases lt_or_gt_of_ne h02 with b | b <;>
    rcases lt_or_gt_of_ne h12 with c | c
  all_goals first
    | exact ⟨0, isDepthSeparatedPair_triangle hp (by rw [e0.1, e0.2]; nlinarith)⟩
    | exact ⟨1, isDepthSeparatedPair_triangle hp (by rw [e1.1, e1.2]; nlinarith)⟩
    | exact ⟨2, isDepthSeparatedPair_triangle hp (by rw [e2.1, e2.2]; nlinarith)⟩

/-- **Lemma CT, Rupert form** (Proposition 8.8 with the chord-top pair).  The setting of
`isRupert_of_chords_depthSeparated` (middles `M` over silhouette edges of `K′` at `u₀`, the
silhouette of `K′` the strictly convex polygon `x`, no horizontal double normal); if the rim
edge `x a → x (a + 1)` is an antipodal chord whose ends are, with distinct depths, strictly the
two deepest or the two shallowest rim corners, then `V` is Rupert. -/
theorem isRupert_of_chords_chordTop (V M : Finset ℝ³) (R : Matrix (Fin 3) (Fin 3) ℝ)
    (hR : R ∈ SO3) {u₀ : ℝ³} {r : ℝ} (hr : 0 < r) (hRu : R.toEuclideanLin u₀ = r • ez)
    {k : ℕ} [NeZero k] (x : ZMod k → ℝ³) (hxV : ∀ i, x i ∈ V) (hxM : ∀ i, x i ∉ M)
    (hp : IsCcwPolygon (fun i => proj_xy (R.toEuclideanLin (x i))))
    (hin : ∀ v ∈ V, v ∉ M → (∀ i, v ≠ x i) → proj_xy (R.toEuclideanLin v) ∈
      interior (convexHull ℝ (Set.range fun i => proj_xy (R.toEuclideanLin (x i)))))
    {a : ZMod k} (hA : IsAntipodalChord (fun i => proj_xy (R.toEuclideanLin (x i))) a)
    (hz : (∀ j, j ≠ a → j ≠ a + 1 → (R.toEuclideanLin (x j)) 2 <
        min ((R.toEuclideanLin (x a)) 2) ((R.toEuclideanLin (x (a + 1))) 2)) ∨
      (∀ j, j ≠ a → j ≠ a + 1 → max ((R.toEuclideanLin (x a)) 2)
        ((R.toEuclideanLin (x (a + 1))) 2) < (R.toEuclideanLin (x j)) 2))
    (hne : (R.toEuclideanLin (x a)) 2 ≠ (R.toEuclideanLin (x (a + 1))) 2)
    (hnd : ¬ HasHorizontalDoubleNormal (fun i => proj_xy (R.toEuclideanLin (x i)))
      (fun i => (R.toEuclideanLin (x i)) 2))
    (hM : ∀ m ∈ M, ∃ i : ZMod k, ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
      m = x i + s • (x (i + 1) - x i) + δ • u₀) : IsRupert V := by
  rcases isDepthSeparatedPair_chordTop hp hA hz hne with hds | hds
  · exact isRupert_of_chords_depthSeparated V M R hR hr hRu x hxV hxM hp hin hds hnd hM
  · exact isRupert_of_chords_depthSeparated V M R hR hr hRu x hxV hxM hp hin hds hnd hM

/-- **Triangle-rim lemma, Rupert form.**  In the setting of `isRupert_of_chords_depthSeparated`,
a triangle rim of `K′` with distinct depths and no horizontal double normal gives Rupert. -/
theorem isRupert_of_chords_triangle (V M : Finset ℝ³) (R : Matrix (Fin 3) (Fin 3) ℝ)
    (hR : R ∈ SO3) {u₀ : ℝ³} {r : ℝ} (hr : 0 < r) (hRu : R.toEuclideanLin u₀ = r • ez)
    (x : ZMod 3 → ℝ³) (hxV : ∀ i, x i ∈ V) (hxM : ∀ i, x i ∉ M)
    (hp : IsCcwPolygon (fun i => proj_xy (R.toEuclideanLin (x i))))
    (hin : ∀ v ∈ V, v ∉ M → (∀ i, v ≠ x i) → proj_xy (R.toEuclideanLin v) ∈
      interior (convexHull ℝ (Set.range fun i => proj_xy (R.toEuclideanLin (x i)))))
    (hz : Function.Injective fun i => (R.toEuclideanLin (x i)) 2)
    (hnd : ¬ HasHorizontalDoubleNormal (fun i => proj_xy (R.toEuclideanLin (x i)))
      (fun i => (R.toEuclideanLin (x i)) 2))
    (hM : ∀ m ∈ M, ∃ i : ZMod 3, ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
      m = x i + s • (x (i + 1) - x i) + δ • u₀) : IsRupert V := by
  obtain ⟨c, hds⟩ := exists_isDepthSeparatedPair_triangle hp hz
  exact isRupert_of_chords_depthSeparated V M R hR hr hRu x hxV hxM hp hin hds hnd hM

/-- **The A* sign in 3D.**  At a rotation `R` with `R u = r e_z` (`r > 0`), the chord of the
projected rim is antipodal iff `det3 (x a − x (a − 1)) (x (a + 2) − x (a + 1)) u ≤ 0`. -/
theorem isAntipodalChord_proj_iff {R : Matrix (Fin 3) (Fin 3) ℝ} (hR : R ∈ SO3) {u : ℝ³} {r : ℝ}
    (hr : 0 < r) (hRu : R.toEuclideanLin u = r • ez) {k : ℕ} (x : ZMod k → ℝ³) (a : ZMod k) :
    IsAntipodalChord (fun i => proj_xy (R.toEuclideanLin (x i))) a ↔
      det3 (x a - x (a - 1)) (x (a + 2) - x (a + 1)) u ≤ 0 := by
  have e := cross2_proj_rot hR hRu (x a - x (a - 1)) (x (a + 2) - x (a + 1))
  rw [← proj_rot_sub, ← proj_rot_sub] at e
  unfold IsAntipodalChord
  rw [← e]
  constructor
  · intro h; exact mul_nonpos_of_nonneg_of_nonpos hr.le h
  · intro h; exact nonpos_of_mul_nonpos_right h hr

/-- **§2.2, antipodality at an edge view.**  At the view `u = x a − m` along a hidden edge
`m → x a` of the facet through `x (a − 1), x a, m` (`R u = r e_z`, `r > 0`, the projected rim a
strictly convex ccw polygon), the chord `a → a + 1` is antipodal iff `x (a + 1)` is a farthest
rim corner from that plane, on the side of the rim: with `N = (x a − m) × (x a − x (a − 1))`,
`⟪N, x j⟫ ≤ ⟪N, x (a + 1)⟫` for every `j`. -/
theorem isAntipodalChord_edgeView_iff {R : Matrix (Fin 3) (Fin 3) ℝ} (hR : R ∈ SO3) {r : ℝ}
    (hr : 0 < r) {k : ℕ} (x : ZMod k → ℝ³) (m : ℝ³) (a : ZMod k)
    (hRu : R.toEuclideanLin (x a - m) = r • ez)
    (hp : IsCcwPolygon (fun i => proj_xy (R.toEuclideanLin (x i)))) :
    IsAntipodalChord (fun i => proj_xy (R.toEuclideanLin (x i))) a ↔
      ∀ j, ⟪cross (x a - m) (x a - x (a - 1)), x j⟫ ≤
        ⟪cross (x a - m) (x a - x (a - 1)), x (a + 1)⟫ := by
  set p : ZMod k → ℝ² := fun i => proj_xy (R.toEuclideanLin (x i)) with hpdef
  have key : ∀ j, ⟪-outNormal (p (a - 1)) (p a), p j - p (a + 1)⟫ * r =
      ⟪cross (x a - m) (x a - x (a - 1)), x j⟫ - ⟪cross (x a - m) (x a - x (a - 1)), x (a + 1)⟫ := by
    intro j
    rw [inner_neg_outNormal]
    have e := cross2_proj_rot hR hRu (x a - x (a - 1)) (x j - x (a + 1))
    rw [← proj_rot_sub, ← proj_rot_sub] at e
    rw [← inner_sub_right, mul_comm]
    simp only [hpdef]
    rw [e]
    show det3 _ _ _ = det3 _ _ _
    simp only [det3, cross, PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, conj_trivial]
    simp
    ring
  rw [hp.antipodalChord_iff_left a]
  constructor
  · intro h j
    have := h (p j) (subset_convexHull ℝ _ ⟨_, rfl⟩)
    have := key j
    nlinarith
  · intro h
    have hall : ∀ j, ⟪-outNormal (p (a - 1)) (p a), p j - p (a + 1)⟫ ≤ 0 := fun j => by
      have := key j
      have := h j
      have : ⟪-outNormal (p (a - 1)) (p a), p j - p (a + 1)⟫ * r ≤ 0 := by linarith
      exact nonpos_of_mul_nonpos_left this hr
    intro q hq
    have hconv : Convex ℝ {w : ℝ² | ⟪-outNormal (p (a - 1)) (p a), w⟫ ≤
        ⟪-outNormal (p (a - 1)) (p a), p (a + 1)⟫} :=
      convex_halfSpace_le (f := fun w : ℝ² => ⟪-outNormal (p (a - 1)) (p a), w⟫)
        ⟨fun v w => inner_add_right _ _ _, fun s v => real_inner_smul_right _ _ _⟩ _
    have hsub : Set.range p ⊆ {w : ℝ² | ⟪-outNormal (p (a - 1)) (p a), w⟫ ≤
        ⟪-outNormal (p (a - 1)) (p a), p (a + 1)⟫} := by
      rintro _ ⟨j, rfl⟩
      have := hall j
      rw [inner_sub_right] at this
      show _ ≤ _
      linarith
    have := convexHull_min hsub hconv hq
    simp only [Set.mem_ofPred_eq] at this
    rw [inner_sub_right]; linarith

end Minimality

end
