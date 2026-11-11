module

public import Mathlib
public import Minimality.Tilt
public import Minimality.Polygon
public import Minimality.RobustUnimodal
public import Minimality.L8T3

@[expose] public section

/-!
# Lemma WV (the wall view)

Look along a direction `n`.  Let `x : ZMod k → ℝ³` list the rim, the vertices of `V` over the
corners of the shadow, counterclockwise.  Call `⟪x i, n⟫` the *level* of the corner `i`.

* **(W1)**, `hcyc` and `hrest`: the shadow corners are strictly convex and counterclockwise
  (`det3 (x (i+1) - x i) (x j - x i) n > 0` for `j ≠ i, i + 1`, the area of the shadow triangle),
  and every other point of `V` projects strictly to the left of every edge.  This excludes
  *doubles* (two points of `V` over one shadow point) and *middles* (a point over the relative
  interior of an edge of the shadow).
* **(W2), (W3)**, `WallShape`: the levels have the shape of a mountain with two flat ends.  After
  starting the list at the first corner of the lowest run, the levels are constant on `0 … s` (the
  *floor run*), strictly increasing on `s … r`, constant on `r … r'` (the *ceiling run*) and
  strictly decreasing on `r' … k` (position `k` is position `0`).  Equal levels of consecutive
  corners occur only at the bottom and at the top.

Then `V` is Rupert (`isRupert_of_wallView`): at the tilted view `n + ε w`, for a suitable direction
`w` and all small `ε > 0`, the corner depths `level + ε ⟪x i, w⟫` are cyclically unimodal, and
Theorem 7.3 applies (`isRupert_of_tilted_unimodal'`, which tolerates ties at the view itself).

The wall facets of the usual setting (two parallel facets of `conv V` with normal `n`) are not used:
the lemma speaks only about the rim levels along `n`.  With facets at levels `0` and `h`, every
vertex has a level in `[0, h]`, so the rim corners over the two facets are the corners at levels
`0` and `h`, and the condition on ties says that two consecutive rim corners share a level only if it
is the lowest or the highest rim level (in particular if it is `0` or `h`).

How `w` is chosen (`exists_wallTilt`).  A *separating* direction: if the floor run has two or more
corners, `w` is the normal of the chord from its first to its last corner, pointing to the side of
the rest of the shadow; if the floor run is a single corner and the ceiling run has two or more, `w`
is the normal of the chord of the ceiling run, pointing away from the rest.  Then `w` gives every
floor corner a smaller `w`-value than every ceiling corner.  Along a strictly convex polygon a
linear function has no local maximum that is not a global one, so a floor run cannot contain an
interior local maximum of `w`, nor a ceiling run an interior local minimum
(`Polygon.lean`, `IsCcwPolygon.lt_of_localMax`).  That is exactly what unimodality of
`level + ε w` needs (`isCyclicUnimodal_of_wallShape`).  If both runs are single corners, no tilt is
needed.
-/

set_option autoImplicit false

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

/-- The level sequence `l` of a cyclic list of rim corners has the *wall shape* with parameters
`s < r ≤ r' < k`: constant on `0 … s` (the floor run), strictly increasing on `s … r`, constant
on `r … r'` (the ceiling run), strictly decreasing on `r' … k` (position `k` is position `0`).
This is "cyclically unimodal, with ties only at the bottom and the top", for a list that starts at
the bottom run. -/
structure WallShape {k : ℕ} (l : ZMod k → ℝ) (s r r' : ℕ) : Prop where
  lt_sr : s < r
  le_rr : r ≤ r'
  lt_rk : r' < k
  floor : ∀ t : ℕ, t < s → l t = l (t + 1)
  rise : ∀ t : ℕ, s ≤ t → t < r → l t < l (t + 1)
  ceil : ∀ t : ℕ, r ≤ t → t < r' → l t = l (t + 1)
  fall : ∀ t : ℕ, r' ≤ t → t < k → l (t + 1) < l t

theorem cast_ne_of_lt {k : ℕ} {a b : ℕ} (ha : a < k) (hb : b < k) (h : a ≠ b) :
    (a : ZMod k) ≠ (b : ZMod k) := by
  intro e
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at e
  exact h e

theorem natCast_sub_one_zmod {k : ℕ} {t : ℕ} (ht : 1 ≤ t) :
    ((t - 1 : ℕ) : ZMod k) = (t : ZMod k) - 1 := by
  rw [Nat.cast_sub ht, Nat.cast_one]

/-- **A wall-shaped level sequence, broken lexicographically by a tilt, is unimodal.**
Let `z` have distinct entries and respect the order "by `l`, then by `f`".  If `f` has no
local maximum (weak) at an interior corner of the floor run and no local minimum (weak) at an
interior corner of the ceiling run, then `z` is cyclically unimodal.  Pairs tied in both `l` and
`f` are left free. -/
theorem isCyclicUnimodal_of_wallShape {k : ℕ} [NeZero k] {l f z : ZMod k → ℝ} {s r r' : ℕ}
    (hS : WallShape l s r r')
    (hF2 : ∀ t : ℕ, 0 < t → t < s →
      ¬ (f ((t : ZMod k) - 1) ≤ f t ∧ f ((t : ZMod k) + 1) ≤ f t))
    (hF3 : ∀ t : ℕ, r < t → t < r' →
      ¬ (f t ≤ f ((t : ZMod k) - 1) ∧ f t ≤ f ((t : ZMod k) + 1)))
    (hinj : Function.Injective z)
    (hQ : ∀ i j, (l i < l j ∨ (l i = l j ∧ f i < f j)) → z i < z j) :
    IsCyclicUnimodal z := by
  have hsr := hS.lt_sr
  have hrr := hS.le_rr
  have hrk := hS.lt_rk
  have hk : 2 ≤ k := by omega
  -- facts at a local maximum
  have key : ∀ i : ZMod k, z (i - 1) < z i ∧ z (i + 1) < z i →
      (l (i - 1) ≤ l i ∧ (l i = l (i - 1) → f (i - 1) ≤ f i)) ∧
      (l (i + 1) ≤ l i ∧ (l i = l (i + 1) → f (i + 1) ≤ f i)) := by
    rintro i ⟨h1, h2⟩
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · by_contra h; push Not at h; have := hQ i (i - 1) (Or.inl h); linarith
    · intro he; by_contra h; push Not at h; have := hQ i (i - 1) (Or.inr ⟨he, h⟩); linarith
    · by_contra h; push Not at h; have := hQ i (i + 1) (Or.inl h); linarith
    · intro he; by_contra h; push Not at h; have := hQ i (i + 1) (Or.inr ⟨he, h⟩); linarith
  have hsucc : ∀ t : ℕ, ((t + 1 : ℕ) : ZMod k) = (t : ZMod k) + 1 := fun t => by push_cast; rfl
  -- local maxima lie in the ceiling run
  have hrange : ∀ t : ℕ, t < k → (z ((t : ZMod k) - 1) < z t ∧ z ((t : ZMod k) + 1) < z t) →
      r ≤ t ∧ t ≤ r' := by
    intro t htk hloc
    obtain ⟨⟨hl1, hf1⟩, ⟨hl2, hf2⟩⟩ := key _ hloc
    by_cases ht0 : t = 0
    · exfalso
      subst ht0
      have h := hS.fall (k - 1) (by omega) (by omega)
      have e1 : (((k - 1 : ℕ) : ZMod k) + 1) = 0 := by
        rw [natCast_sub_one_zmod (by omega)]; simp
      have e2 : ((0 : ℕ) : ZMod k) - 1 = ((k - 1 : ℕ) : ZMod k) := by
        rw [natCast_sub_one_zmod (by omega)]; simp
      rw [e1] at h
      rw [e2] at hl1
      simp only [Nat.cast_zero] at hl1
      linarith
    · have ht1 : 1 ≤ t := by omega
      have hp1 : ((t - 1 : ℕ) : ZMod k) = (t : ZMod k) - 1 := natCast_sub_one_zmod ht1
      have e1' : ((t - 1 : ℕ) : ZMod k) + 1 = (t : ZMod k) := by rw [hp1]; ring
      by_cases hts : t < s
      · exfalso
        have e1 := hS.floor (t - 1) (by omega)
        rw [e1', hp1] at e1
        have e2 := hS.floor t hts
        exact hF2 t (by omega) hts ⟨hf1 e1.symm, hf2 e2⟩
      · by_cases htr : t < r
        · exfalso
          have := hS.rise t (by omega) htr
          linarith
        · by_cases htr' : t ≤ r'
          · exact ⟨by omega, htr'⟩
          · exfalso
            have h := hS.fall (t - 1) (by omega) (by omega)
            rw [e1', hp1] at h
            linarith
  -- two local maxima in the ceiling run coincide
  have haux : ∀ t t' : ℕ, t < t' → r ≤ t → t' ≤ r' →
      (z ((t : ZMod k) - 1) < z t ∧ z ((t : ZMod k) + 1) < z t) →
      (z ((t' : ZMod k) - 1) < z t' ∧ z ((t' : ZMod k) + 1) < z t') → False := by
    intro t t' htt hrt hrt' hloc hloc'
    obtain ⟨⟨hl1, hf1⟩, ⟨hl2, hf2⟩⟩ := key _ hloc
    obtain ⟨⟨hl1', hf1'⟩, ⟨hl2', hf2'⟩⟩ := key _ hloc'
    by_cases hadj : t' = t + 1
    · subst hadj
      have e : ((t + 1 : ℕ) : ZMod k) - 1 = (t : ZMod k) := by rw [hsucc]; ring
      have := hloc'.1
      rw [e] at this
      have := hloc.2
      rw [← hsucc] at this
      linarith [hloc'.1, hloc.2]
    · have hne : (Finset.Ioo t t').Nonempty := ⟨t + 1, by simp only [Finset.mem_Ioo]; omega⟩
      obtain ⟨u, hu, hmin⟩ :=
        Finset.exists_min_image (Finset.Ioo t t') (fun u : ℕ => f (u : ZMod k)) hne
      simp only [Finset.mem_Ioo] at hu
      have hu1 : ((u - 1 : ℕ) : ZMod k) = (u : ZMod k) - 1 := natCast_sub_one_zmod (by omega)
      have hu1' : ((u - 1 : ℕ) : ZMod k) + 1 = (u : ZMod k) := by rw [hu1]; ring
      refine hF3 u (by omega) (by omega) ⟨?_, ?_⟩
      · rw [← hu1]
        by_cases hut : u - 1 = t
        · obtain rfl : u = t + 1 := by omega
          have := hf2 (hS.ceil t hrt (by omega))
          simpa using this
        · exact hmin (u - 1) (by simp only [Finset.mem_Ioo]; omega)
      · rw [← hsucc]
        by_cases hut : u + 1 = t'
        · obtain rfl : t' = u + 1 := hut.symm
          have e := hS.ceil u (by omega) (by omega)
          simpa using hf1' (by simpa using e.symm)
        · exact hmin (u + 1) (by simp only [Finset.mem_Ioo]; omega)
  refine isCyclicUnimodal_of_atMostOne hk hinj fun i j hi hj => ?_
  obtain ⟨t, htk, rfl⟩ : ∃ t : ℕ, t < k ∧ i = (t : ZMod k) :=
    ⟨i.val, ZMod.val_lt i, (ZMod.natCast_zmod_val i).symm⟩
  obtain ⟨t', htk', rfl⟩ : ∃ t' : ℕ, t' < k ∧ j = (t' : ZMod k) :=
    ⟨j.val, ZMod.val_lt j, (ZMod.natCast_zmod_val j).symm⟩
  obtain ⟨h1, h2⟩ := hrange t htk hi
  obtain ⟨h1', h2'⟩ := hrange t' htk' hj
  rcases lt_trichotomy t t' with h | h | h
  · exact (haux t t' h h1 h2' hi hj).elim
  · rw [h]
  · exact (haux t' t h h1' h2 hj hi).elim

/-! ### Part B: a tilt direction -/

theorem inner_perp (d q : ℝ²) : ⟪!₂[-(d 1), d 0], q⟫ = cross2 d q := by
  simp only [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, conj_trivial, cross2]
  simp; ring

theorem wall_F23 {k : ℕ} [NeZero k] {p : ZMod k → ℝ²} (hp : IsCcwPolygon p) {ν : ℝ²} (hν : ν ≠ 0)
    {s r r' : ℕ} (hsr : s < r) (hrr : r ≤ r') (hrk : r' < k)
    (hS : ∀ u b : ℕ, u ≤ s → r ≤ b → b ≤ r' → ⟪ν, p u⟫ < ⟪ν, p b⟫) :
    (∀ t : ℕ, 0 < t → t < s →
      ¬ (⟪ν, p ((t : ZMod k) - 1)⟫ ≤ ⟪ν, p t⟫ ∧ ⟪ν, p ((t : ZMod k) + 1)⟫ ≤ ⟪ν, p t⟫)) ∧
    (∀ t : ℕ, r < t → t < r' →
      ¬ (⟪ν, p t⟫ ≤ ⟪ν, p ((t : ZMod k) - 1)⟫ ∧ ⟪ν, p t⟫ ≤ ⟪ν, p ((t : ZMod k) + 1)⟫)) := by
  have hsucc : ∀ t : ℕ, ((t + 1 : ℕ) : ZMod k) = (t : ZMod k) + 1 := fun t => by push_cast; rfl
  constructor
  · rintro t ht0 hts ⟨h1, h2⟩
    have hp1 := natCast_sub_one_zmod (k := k) (t := t) (by omega)
    have := hp.lt_of_localMax hν (s := (t : ZMod k))
      (by rw [inner_sub_right]; linarith) (by rw [inner_sub_right]; linarith)
      (j := (r : ZMod k))
      (by rw [← hp1]; exact cast_ne_of_lt (by omega) (by omega) (by omega))
      (cast_ne_of_lt (by omega) (by omega) (by omega))
      (by rw [← hsucc]; exact cast_ne_of_lt (by omega) (by omega) (by omega))
    have h3 := hS t r (by omega) le_rfl hrr
    linarith
  · rintro t htr htr' ⟨h1, h2⟩
    have hp1 := natCast_sub_one_zmod (k := k) (t := t) (by omega)
    have := hp.lt_of_localMax (neg_ne_zero.mpr hν) (s := (t : ZMod k))
      (by rw [inner_sub_right, inner_neg_left, inner_neg_left]; linarith)
      (by rw [inner_sub_right, inner_neg_left, inner_neg_left]; linarith)
      (j := ((0 : ℕ) : ZMod k))
      (by rw [← hp1]; exact cast_ne_of_lt (by omega) (by omega) (by omega))
      (cast_ne_of_lt (by omega) (by omega) (by omega))
      (by rw [← hsucc]; exact cast_ne_of_lt (by omega) (by omega) (by omega))
    have h3 := hS 0 t (by omega) (by omega) (by omega)
    rw [inner_neg_left, inner_neg_left] at this
    linarith

theorem ccw3 {k : ℕ} [NeZero k] {p : ZMod k → ℝ²} (hp : IsCcwPolygon p) {a b c : ℕ} (hab : a < b)
    (hbc : b < c) (hck : c < k) :
    0 < cross2 (p b - p a) (p c - p a) := by
  have := hp.cross2_pos_of_cycBetween (cycBetween_of_lt (0 : ZMod k) hab hbc hck)
  simpa only [zero_add] using this

theorem exists_wallTilt {k : ℕ} [NeZero k] {p : ZMod k → ℝ²} (hp : IsCcwPolygon p) {s r r' : ℕ}
    (hsr : s < r) (hrr : r ≤ r') (hrk : r' < k) :
    ∃ ν : ℝ²,
      (∀ t : ℕ, 0 < t → t < s →
        ¬ (⟪ν, p ((t : ZMod k) - 1)⟫ ≤ ⟪ν, p t⟫ ∧ ⟪ν, p ((t : ZMod k) + 1)⟫ ≤ ⟪ν, p t⟫)) ∧
      (∀ t : ℕ, r < t → t < r' →
        ¬ (⟪ν, p t⟫ ≤ ⟪ν, p ((t : ZMod k) - 1)⟫ ∧ ⟪ν, p t⟫ ≤ ⟪ν, p ((t : ZMod k) + 1)⟫)) := by
  have hne : ∀ {a b : ℕ}, a < k → b < k → a ≠ b → p a - p b ≠ 0 := fun ha hb hab h =>
    cast_ne_of_lt ha hb hab (hp.injective (sub_eq_zero.mp h))
  have hperp : ∀ d : ℝ², d ≠ 0 → (!₂[-(d 1), d 0] : ℝ²) ≠ 0 := by
    intro d hd h
    apply hd
    have h0 := congrArg (fun v : ℝ² => v 0) h
    have h1 := congrArg (fun v : ℝ² => v 1) h
    simp at h0 h1
    ext i; fin_cases i <;> simp [h0, h1]
  by_cases hs0 : 0 < s
  · -- chord of the floor run
    set d : ℝ² := p s - p ((0 : ℕ) : ZMod k) with hd
    have hd0 : d ≠ 0 := hne (by omega) (by omega) (by omega)
    refine ⟨!₂[-(d 1), d 0], wall_F23 hp (hperp d hd0) hsr hrr hrk ?_⟩
    intro u b hu hrb hbr'
    rw [inner_perp, inner_perp]
    have hb : 0 < cross2 d (p b - p ((0 : ℕ) : ZMod k)) := by
      have := ccw3 hp (a := 0) (b := s) (c := b) (by omega) (by omega) (by omega)
      simpa only [hd] using this
    have hu' : cross2 d (p u - p ((0 : ℕ) : ZMod k)) ≤ 0 := by
      rcases Nat.eq_zero_or_pos u with rfl | hu0
      · simp [cross2]
      · rcases hu.lt_or_eq with hus | rfl
        · have := ccw3 hp (a := 0) (b := u) (c := s) hu0 hus (by omega)
          rw [hd, cross2_comm]
          linarith
        · rw [hd, cross2_self]
    rw [cross2_sub_right] at hb hu'
    linarith
  · by_cases hrr' : r < r'
    · -- chord of the ceiling run
      have hs : s = 0 := by omega
      set d : ℝ² := p r - p r' with hd
      have hd0 : d ≠ 0 := hne (by omega) (by omega) (by omega)
      refine ⟨!₂[-(d 1), d 0], wall_F23 hp (hperp d hd0) hsr hrr hrk ?_⟩
      intro u b hu hrb hbr'
      have hu0 : u = 0 := by omega
      subst hu0
      rw [inner_perp, inner_perp]
      have h0 : cross2 d (p ((0 : ℕ) : ZMod k) - p r') < 0 := by
        have := ccw3 hp (a := 0) (b := r) (c := r') (by omega) hrr' hrk
        have e : cross2 d (p ((0 : ℕ) : ZMod k) - p r') =
            -cross2 (p r - p ((0 : ℕ) : ZMod k)) (p r' - p ((0 : ℕ) : ZMod k)) := by
          simp only [hd, cross2, PiLp.sub_apply]; ring
        rw [e]; linarith
      have hb : 0 ≤ cross2 d (p b - p r') := by
        rcases hrb.lt_or_eq with hrb' | rfl
        · rcases hbr'.lt_or_eq with hbr'' | rfl
          · have := ccw3 hp (a := r) (b := b) (c := r') hrb' hbr'' hrk
            have e : cross2 d (p b - p r') = cross2 (p b - p r) (p r' - p r) := by
              simp only [hd, cross2, PiLp.sub_apply]; ring
            rw [e]; exact this.le
          · simp [cross2]
        · rw [hd]; simp only [cross2, PiLp.sub_apply]; exact le_of_eq (by ring)
      rw [cross2_sub_right] at h0 hb
      linarith
    · have hrr'' : r = r' := by omega
      subst hrr''
      refine ⟨0, ?_, ?_⟩
      · intro t _ hts; omega
      · intro t htr htr'; omega

/-! ### Part C: the wall view -/

/-- The vector with `⟪x, wDir R ν⟫ = ⟪ν, π (R x)⟫`, the depth gain of a planar direction `ν`
at the view `R`. -/
noncomputable def wDir (R : Matrix (Fin 3) (Fin 3) ℝ) (ν : ℝ²) : ℝ³ :=
  !₂[ν 0 * R 0 0 + ν 1 * R 1 0, ν 0 * R 0 1 + ν 1 * R 1 1, ν 0 * R 0 2 + ν 1 * R 1 2]

theorem inner_wDir (R : Matrix (Fin 3) (Fin 3) ℝ) (ν : ℝ²) (x : ℝ³) :
    ⟪x, wDir R ν⟫ = ⟪ν, proj_xy (R.toEuclideanLin x)⟫ := by
  simp only [wDir, proj_xy, PiLp.inner_apply, Fin.sum_univ_two, Fin.sum_univ_three,
    RCLike.inner_apply, conj_trivial, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct]
  simp
  ring

/-- **Lemma WV (the wall view).**  `V` is a finite set of points, `n ≠ 0` a direction, and
`x : ZMod k → ℝ³` a counterclockwise list of its rim along `n` (`hcyc`, `hrest`: see the module
documentation), whose levels `⟪x i, n⟫` have the wall shape `s, r, r'`.  Then `V` is Rupert.

`det3 a b n = ⟪a × b, n⟫` is the signed area of the shadows of `a` and `b`. -/
theorem isRupert_of_wallView (V : Finset ℝ³) (n : ℝ³) (hn : n ≠ 0) {k : ℕ} [NeZero k]
    (hk : 3 ≤ k) (x : ZMod k → ℝ³) (hxV : ∀ i, x i ∈ V)
    (hcyc : ∀ i j, j ≠ i → j ≠ i + 1 → 0 < det3 (x (i + 1) - x i) (x j - x i) n)
    (hrest : ∀ y ∈ V, (∀ j, y ≠ x j) → ∀ i, 0 < det3 (x (i + 1) - x i) (y - x i) n)
    {s r r' : ℕ} (hS : WallShape (fun i => ⟪x i, n⟫) s r r') : IsRupert V := by
  classical
  obtain ⟨R, hR, ρ, hρ, hRn⟩ := exists_rotation_to_ez_pos n hn
  set p : ZMod k → ℝ² := fun i => proj_xy (R.toEuclideanLin (x i)) with hpdef
  have hp : IsCcwPolygon p := by
    refine ⟨hk, fun i j hi hj => ?_⟩
    simp only [hpdef, proj_rot_sub]
    exact cross2_proj_rot_pos hR hρ hRn (hcyc i j hi hj)
  obtain ⟨ν, hF2, hF3⟩ := exists_wallTilt hp hS.lt_sr hS.le_rr hS.lt_rk
  set w : ℝ³ := wDir R ν with hw
  have hfw : ∀ i, ⟪x i, w⟫ = ⟪ν, p i⟫ := fun i => inner_wDir R ν (x i)
  have hexp : ∀ (ε : ℝ) (i : ZMod k), ⟪x i, n + ε • w⟫ = ⟪x i, n⟫ + ε * ⟪x i, w⟫ := by
    intro ε i; rw [inner_add_right, real_inner_smul_right]
  let P : (ZMod k → ℝ) → Prop := fun z => ∀ i j : ZMod k,
    (⟪x i, n⟫ < ⟪x j, n⟫ ∨ (⟪x i, n⟫ = ⟪x j, n⟫ ∧ ⟪x i, w⟫ < ⟪x j, w⟫)) → z i < z j
  refine isRupert_of_tilted_unimodal' V n w hn hk x hxV
    (fun i j hj hj' => Or.inl (hcyc i j hj hj'))
    (fun y hy hyx i => Or.inl (hrest y hy hyx i)) P ?_ ?_ ?_ ?_
  · have : {z : ZMod k → ℝ | P z} = ⋂ i, ⋂ j, ⋂ (_ : (⟪x i, n⟫ < ⟪x j, n⟫ ∨
        (⟪x i, n⟫ = ⟪x j, n⟫ ∧ ⟪x i, w⟫ < ⟪x j, w⟫))), {z | z i < z j} := by
      ext z; simp [P]
    rw [this]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      isOpen_iInter_of_finite fun _ => isOpen_lt (continuous_apply i) (continuous_apply j)
  · intro z c hc hz i j hij
    exact mul_lt_mul_of_pos_left (hz i j hij) hc
  · have h1 : ∀ i j : ZMod k, ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        (⟪x i, n⟫ < ⟪x j, n⟫ ∨ (⟪x i, n⟫ = ⟪x j, n⟫ ∧ ⟪x i, w⟫ < ⟪x j, w⟫)) →
          ⟪x i, n + ε • w⟫ < ⟪x j, n + ε • w⟫ := by
      intro i j
      by_cases hlt : ⟪x i, n⟫ < ⟪x j, n⟫
      · have hc : Continuous fun ε : ℝ => ⟪x j, n + ε • w⟫ - ⟪x i, n + ε • w⟫ := by fun_prop
        have h0 : (0 : ℝ) < (fun ε : ℝ => ⟪x j, n + ε • w⟫ - ⟪x i, n + ε • w⟫) 0 := by
          simp only [zero_smul, add_zero]; linarith
        have h2 : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < ⟪x j, n + ε • w⟫ - ⟪x i, n + ε • w⟫ :=
          hc.continuousAt.eventually (lt_mem_nhds h0)
        filter_upwards [nhdsWithin_le_nhds h2] with ε hε _
        linarith
      · filter_upwards [self_mem_nhdsWithin] with ε hε h
        rcases h with h | ⟨he, hf⟩
        · exact absurd h hlt
        · rw [hexp, hexp, he]
          have : (0 : ℝ) < ε := hε
          nlinarith
    filter_upwards [Filter.eventually_all.2 fun i => Filter.eventually_all.2 (h1 i)] with ε h
    exact fun i j => h i j
  · intro z hz hQ
    refine isCyclicUnimodal_of_wallShape (l := fun i => ⟪x i, n⟫) (f := fun i => ⟪x i, w⟫) hS
      ?_ ?_ hz hQ
    · intro t ht0 hts
      simpa only [hfw] using hF2 t ht0 hts
    · intro t htr htr'
      simpa only [hfw] using hF3 t htr htr'

end Minimality
