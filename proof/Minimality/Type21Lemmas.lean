module

public import Minimality.Type29

@[expose] public section

/-!
# Type 21: the setting of §9 (`FEWER-FACES-PROOFS.md` §9)

Labels of §9 with `a, a', b, b', c, c', d = 0, 3, 4, 5, 1, 6, 2`: the octahedron
`O6 = K − 2` has the opposite pairs `(0, 3)`, `(4, 5)`, `(1, 6)`
(`F : OctFacets a a' b b' c c'`; its faces `014, 046, 015, 056, 134, 346, 135, 356` are
`abc, abc', ab'c, ab'c', a'bc, a'bc', a'b'c, a'b'c'`), and the cap `2` lies on the
planes `056` and `346` (so on their line `ℓ` through `6`), strictly beyond `356` and
strictly beneath the other five faces (`IsCap21`).  Then `K = conv (O6 ∪ {2})` has the
faces `014, 015, 0256, 046, 134, 135, 2346, 235`, and conversely (§9.0).

* The quadrilaterals: `IsCap21.coords` (`0256`: `2 = 0 + α (5 − 0) + β (6 − 0)` with
  `α, β > 0`, `α + β > 1`); `2346` is the same statement for the symmetry
  `σ1 = (04)(35)` (`IsCap21.sigma1`, the relabelling `F.perm₁₂`).
* The second octahedron: `O2 = K − 6` with opposite pairs `(0, 3)`, `(4, 5)`, `(1, 2)` and
  the cap `6` over its face `024`.  `IsCap21.O2` builds its facet functions (the new
  faces `235` and `024` are pencils through `35` and `04`; `024` needs both
  quadrilaterals), labelled by `σ2 = (26)(05)(34)` as `OctFacets 5 4 3 0 1 2`, and
  `IsCap21.sigma2` shows that `6` is a type-21 cap over it.  So every statement for
  `O6` transfers to `O2`.
* A label-free hiddenness (`HiddenAt`: the image of a point lies strictly inside every
  supporting line of the shadow through two vertices) and its consequence at a quad
  edge (`quadHidden_of_hiddenAt`), for Lemma 2 (a).
* **Lemma 1 (a) of §9** — `IsCap21.not_hidden_04`: at the view along `04` the cap is never
  hidden (it lies strictly beyond the silhouette edge `56` or `36`;
  `not_hiddenAt_of_combo`).  The general rim statement of Lemma 1 and its part (b) are not
  formalized; Lemma 3 uses the facet inequalities of the quad edge instead.
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

/-! ### The cap -/

/-- The cap `d` (`2`) of a type-21 point set over the octahedron `O6` with opposite pairs
`(a, a') = (0, 3)`, `(b, b') = (4, 5)`, `(c, c') = (1, 6)`: on the planes of `ab'c'`
(`056`) and `a'bc'` (`346`), which become the quadrilaterals `0256` and `2346`, strictly
beyond `a'b'c'` (`356`), strictly beneath the other five faces. -/
structure IsCap21 {a a' b b' c c' : ℝ³} (F : OctFacets a a' b b' c c') (d : ℝ³) : Prop where
  ab'c' : F.ab'c'.f d = 0
  a'bc' : F.a'bc'.f d = 0
  a'b'c' : 0 < F.a'b'c'.f d
  abc : F.abc.f d < 0
  abc' : F.abc'.f d < 0
  ab'c : F.ab'c.f d < 0
  a'bc : F.a'bc.f d < 0
  a'b'c : F.a'b'c.f d < 0

section Cap

variable {a a' b b' c c' d : ℝ³} {F : OctFacets a a' b b' c c'}

/-- The symmetry `σ1 = (04)(35)` of type 21 (it fixes `1, 2, 6`). -/
theorem IsCap21.sigma1 (h : IsCap21 F d) : IsCap21 F.perm₁₂ d :=
  ⟨h.a'bc', h.ab'c', h.a'b'c', h.abc, h.abc', h.a'bc, h.ab'c, h.a'b'c⟩

theorem IsCap21.ne (h : IsCap21 F d) : d ≠ a ∧ d ≠ a' ∧ d ≠ b ∧ d ≠ b' ∧ d ≠ c ∧ d ≠ c' := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rintro rfl
  · have := h.abc; rw [F.abc.hP] at this; exact lt_irrefl _ this
  · have := h.a'b'c'; rw [F.a'b'c'.hP] at this; exact lt_irrefl _ this
  · have := h.abc; rw [F.abc.hQ] at this; exact lt_irrefl _ this
  · have := h.a'b'c'; rw [F.a'b'c'.hQ] at this; exact lt_irrefl _ this
  · have := h.abc; rw [F.abc.hR] at this; exact lt_irrefl _ this
  · have := h.a'b'c'; rw [F.a'b'c'.hR] at this; exact lt_irrefl _ this

/-- **The quadrilateral `0256` is convex**, with `2` opposite `0`: in the frame
`0; 5 − 0, 6 − 0`, `2` has coordinates `α, β > 0` (beneath `046` and `015`) with
`α + β > 1` (beyond `356`). -/
theorem IsCap21.coords (h : IsCap21 F d) :
    0 < F.abc'.f d / F.abc'.f b' ∧ 0 < F.ab'c.f d / F.ab'c.f c' ∧
      1 < F.abc'.f d / F.abc'.f b' + F.ab'c.f d / F.ab'c.f c' ∧
      d = a + (F.abc'.f d / F.abc'.f b') • (b' - a) + (F.ab'c.f d / F.ab'c.f c') • (c' - a) := by
  have hnd := F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨haa', hab, hab', hac, hac'⟩, ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩,
    ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd
  have n0 := F.ab'c'.neg b (by simp) (Ne.symm hab) hbb' hbc'
  have n1 := F.abc'.neg b' (by simp) (Ne.symm hab') (Ne.symm hbb') hb'c'
  have n2 := F.ab'c.neg c' (by simp) (Ne.symm hac') (Ne.symm hb'c') (Ne.symm hcc')
  have hco := coords_of_affine3 F.ab'c'.hN F.abc'.hN F.ab'c.hN F.ab'c'.hP F.ab'c'.hQ
    F.ab'c'.hR h.ab'c' n0.ne F.abc'.hP F.abc'.hR n1.ne F.ab'c.hP F.ab'c.hQ n2.ne
  set α := F.abc'.f d / F.abc'.f b'
  set β := F.ab'c.f d / F.ab'c.f c'
  refine ⟨div_pos_of_neg_of_neg h.abc' n1, div_pos_of_neg_of_neg h.ab'c n2, ?_, hco⟩
  have hf := affine_frame F.a'b'c'.hN a b' c' α β
  rw [← hco, F.a'b'c'.hQ, F.a'b'c'.hR] at hf
  have := F.a'b'c'.neg a (by simp) haa' hab' hac'
  nlinarith [h.a'b'c']

/-- The coordinates of `IsCap21.coords` as an existential. -/
theorem IsCap21.coords' (h : IsCap21 F d) :
    ∃ α β : ℝ, 0 < α ∧ 0 < β ∧ 1 < α + β ∧ d = a + α • (b' - a) + β • (c' - a) :=
  ⟨_, _, h.coords⟩

/-! ### The faces `235` and `024`, and the octahedron `O2 = K − 6` -/

/-- An element of a six-point set. -/
theorem mem_six {w x₁ x₂ x₃ x₄ x₅ x₆ : ℝ³} (hw : w ∈ ({x₁, x₂, x₃, x₄, x₅, x₆} : Finset ℝ³)) :
    w = x₁ ∨ w = x₂ ∨ w = x₃ ∨ w = x₄ ∨ w = x₅ ∨ w = x₆ := by
  simpa only [mem_insert, mem_singleton] using hw

/-- A combination of two affine functions (a plane of their pencil) is affine. -/
theorem pencil_hN {f₁ f₂ : ℝ³ → ℝ} {N₁ N₂ : ℝ³} (h₁ : ∀ y z, f₁ y - f₁ z = ⟪N₁, y - z⟫)
    (h₂ : ∀ y z, f₂ y - f₂ z = ⟪N₂, y - z⟫) (s₁ s₂ : ℝ) :
    ∀ y z, (s₁ * f₁ y - s₂ * f₂ y) - (s₁ * f₁ z - s₂ * f₂ z) = ⟪s₁ • N₁ - s₂ • N₂, y - z⟫ := by
  intro y z
  rw [inner_sub_left, real_inner_smul_left, real_inner_smul_left, ← h₁, ← h₂]; ring

/-- A facet function of `V` restricted to `W`, given the sign at the points of `W` outside
`V`. -/
def FacetFn.restrict {V W : Finset ℝ³} {P Q R : ℝ³} (G : FacetFn V P Q R)
    (h : ∀ w ∈ W, w ∉ V → w ≠ P → w ≠ Q → w ≠ R → G.f w < 0) : FacetFn W P Q R where
  f := G.f
  N := G.N
  hN := G.hN
  hP := G.hP
  hQ := G.hQ
  hR := G.hR
  neg := fun w hw h1 h2 h3 => by
    by_cases hV : w ∈ V
    · exact G.neg w hV h1 h2 h3
    · exact h w hw hV h1 h2 h3

/-- **The face `235` of `K`**: the plane through `35` and `2` in the pencil of `135` and
`356`, as a facet of `O2 = {5, 4, 3, 0, 1, 2}`. -/
noncomputable def IsCap21.f235 (h : IsCap21 F d) :
    FacetFn ({b', b, a', a, c, d} : Finset ℝ³) b' a' d where
  f := fun z => F.a'b'c'.f d * F.a'b'c.f z - F.a'b'c.f d * F.a'b'c'.f z
  N := F.a'b'c'.f d • F.a'b'c.N - F.a'b'c.f d • F.a'b'c'.N
  hN := pencil_hN F.a'b'c.hN F.a'b'c'.hN _ _
  hP := by simp only [F.a'b'c.hQ, F.a'b'c'.hQ]; ring
  hQ := by simp only [F.a'b'c.hP, F.a'b'c'.hP]; ring
  hR := by ring
  neg := fun w hw h1 h2 h3 => by
    have hnd := F.nodup
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
      not_or, List.nodup_nil, and_true] at hnd
    obtain ⟨⟨haa', hab, hab', hac, hac'⟩, ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩,
      ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd
    have hp := h.a'b'c'
    have hn := h.a'b'c
    show F.a'b'c'.f d * F.a'b'c.f w - F.a'b'c.f d * F.a'b'c'.f w < 0
    rcases mem_six hw with e | e | e | e | e | e
    · exact absurd e h1
    · rw [e]
      have := F.a'b'c.neg b (by simp) (Ne.symm ha'b) hbb' hbc
      have := F.a'b'c'.neg b (by simp) (Ne.symm ha'b) hbb' hbc'
      nlinarith
    · exact absurd e h2
    · rw [e]
      have := F.a'b'c.neg a (by simp) haa' hab' hac
      have := F.a'b'c'.neg a (by simp) haa' hab' hac'
      nlinarith
    · rw [e]
      have := F.a'b'c'.neg c (by simp) (Ne.symm ha'c) (Ne.symm hb'c) hcc'
      rw [F.a'b'c.hR]
      nlinarith
    · exact absurd e h3

/-- **The face `024` of `O2`**: the plane through `04` and `2` in the pencil of `014` and
`046`.  It is negative at `5` and `3` by the convexity of `0256` and `2346`, positive at
`6`. -/
noncomputable def IsCap21.f024 (h : IsCap21 F d) :
    FacetFn ({b', b, a', a, c, d} : Finset ℝ³) b a d where
  f := fun z => F.abc'.f d * F.abc.f z - F.abc.f d * F.abc'.f z
  N := F.abc'.f d • F.abc.N - F.abc.f d • F.abc'.N
  hN := pencil_hN F.abc.hN F.abc'.hN _ _
  hP := by simp only [F.abc.hQ, F.abc'.hQ]; ring
  hQ := by simp only [F.abc.hP, F.abc'.hP]; ring
  hR := by ring
  neg := fun w hw h1 h2 h3 => by
    have hnd := F.nodup
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
      not_or, List.nodup_nil, and_true] at hnd
    obtain ⟨⟨haa', hab, hab', hac, hac'⟩, ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩,
      ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd
    obtain ⟨g, hgd⟩ : ∃ g : ℝ³ → ℝ,
        g = fun z => F.abc'.f d * F.abc.f z - F.abc.f d * F.abc'.f z := ⟨_, rfl⟩
    have hg' : ∀ y z, g y - g z = ⟪F.abc'.f d • F.abc.N - F.abc.f d • F.abc'.N, y - z⟫ := by
      rw [hgd]; exact pencil_hN F.abc.hN F.abc'.hN _ _
    have gw : ∀ z, g z = F.abc'.f d * F.abc.f z - F.abc.f d * F.abc'.f z := fun z => by
      rw [hgd]
    have g0 : g a = 0 := by rw [gw, F.abc.hP, F.abc'.hP]; ring
    have g4 : g b = 0 := by rw [gw, F.abc.hQ, F.abc'.hQ]; ring
    have g2 : g d = 0 := by rw [gw]; ring
    have g6 : 0 < g c' := by
      rw [gw, F.abc'.hR]
      have := F.abc.neg c' (by simp) (Ne.symm hac') (Ne.symm hbc') (Ne.symm hcc')
      nlinarith [h.abc']
    show F.abc'.f d * F.abc.f w - F.abc.f d * F.abc'.f w < 0
    rw [← gw]
    rcases mem_six hw with e | e | e | e | e | e
    · -- `5`, by the quadrilateral `0256`
      rw [e]
      obtain ⟨α, β, hα, hβ, -, hco⟩ := h.coords'
      have hf := affine_frame hg' a b' c' α β
      rw [← hco, g0, g2] at hf
      nlinarith
    · exact absurd e h1
    · -- `3`, by the quadrilateral `2346`
      rw [e]
      obtain ⟨α, β, hα, hβ, -, hco⟩ := h.sigma1.coords'
      have hf := affine_frame hg' b a' c' α β
      rw [← hco, g4, g2] at hf
      nlinarith
    · exact absurd e h2
    · rw [e, gw, F.abc.hR]
      have := F.abc'.neg c (by simp) (Ne.symm hac) (Ne.symm hbc) hcc'
      nlinarith [h.abc]
    · exact absurd e h3

/-- **The octahedron `O2 = K − 6`**, labelled by `σ2 = (26)(05)(34)`: opposite pairs
`(5, 4)`, `(3, 0)`, `(1, 2)`; its faces `135, 235, 015, 025, 134, 234, 014, 024`. -/
noncomputable def IsCap21.O2 (h : IsCap21 F d) : OctFacets b' b a' a c d where
  nodup := by
    have hnd := F.nodup
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
      not_or, List.nodup_nil, and_true] at hnd ⊢
    obtain ⟨⟨haa', hab, hab', hac, hac'⟩, ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩,
      ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd
    obtain ⟨hda, hda', hdb, hdb', hdc, hdc'⟩ := h.ne
    exact ⟨⟨Ne.symm hbb', Ne.symm ha'b', Ne.symm hab', hb'c, Ne.symm hdb'⟩,
      ⟨Ne.symm ha'b, Ne.symm hab, hbc, Ne.symm hdb⟩, ⟨Ne.symm haa', ha'c, Ne.symm hda'⟩,
      ⟨hac, Ne.symm hda⟩, Ne.symm hdc, not_false⟩
  abc := F.a'b'c.p12.restrict fun w hw hwV _ _ _ => by
    rcases mem_six hw with rfl | rfl | rfl | rfl | rfl | rfl <;> first
      | exact h.a'b'c | exact absurd (by simp) hwV
  abc' := h.f235
  ab'c := F.ab'c.p12.restrict fun w hw hwV _ _ _ => by
    rcases mem_six hw with rfl | rfl | rfl | rfl | rfl | rfl <;> first
      | exact h.ab'c | exact absurd (by simp) hwV
  ab'c' :=
    { f := F.ab'c'.f, N := F.ab'c'.N, hN := F.ab'c'.hN, hP := F.ab'c'.hQ, hQ := F.ab'c'.hP,
      hR := h.ab'c'
      neg := fun w hw h1 h2 h3 => by
        have hnd := F.nodup
        simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
          not_or, List.nodup_nil, and_true] at hnd
        obtain ⟨⟨haa', hab, hab', hac, hac'⟩, ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩,
          ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd
        rcases mem_six hw with rfl | rfl | rfl | rfl | rfl | rfl
        · exact absurd rfl h1
        · exact F.ab'c'.neg w (by simp) (Ne.symm hab) hbb' hbc'
        · exact F.ab'c'.neg w (by simp) (Ne.symm haa') ha'b' ha'c'
        · exact absurd rfl h2
        · exact F.ab'c'.neg w (by simp) (Ne.symm hac) (Ne.symm hb'c) hcc'
        · exact absurd rfl h3 }
  a'bc := F.a'bc.p12.restrict fun w hw hwV _ _ _ => by
    rcases mem_six hw with rfl | rfl | rfl | rfl | rfl | rfl <;> first
      | exact h.a'bc | exact absurd (by simp) hwV
  a'bc' :=
    { f := F.a'bc'.f, N := F.a'bc'.N, hN := F.a'bc'.hN, hP := F.a'bc'.hQ, hQ := F.a'bc'.hP,
      hR := h.a'bc'
      neg := fun w hw h1 h2 h3 => by
        have hnd := F.nodup
        simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
          not_or, List.nodup_nil, and_true] at hnd
        obtain ⟨⟨haa', hab, hab', hac, hac'⟩, ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩,
          ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd
        rcases mem_six hw with rfl | rfl | rfl | rfl | rfl | rfl
        · exact F.a'bc'.neg w (by simp) (Ne.symm ha'b') (Ne.symm hbb') hb'c'
        · exact absurd rfl h1
        · exact absurd rfl h2
        · exact F.a'bc'.neg w (by simp) haa' hab hac'
        · exact F.a'bc'.neg w (by simp) (Ne.symm ha'c) (Ne.symm hbc) hcc'
        · exact absurd rfl h3 }
  a'b'c := F.abc.p12.restrict fun w hw hwV _ _ _ => by
    rcases mem_six hw with rfl | rfl | rfl | rfl | rfl | rfl <;> first
      | exact h.abc | exact absurd (by simp) hwV
  a'b'c' := h.f024

/-- **The symmetry `σ2`**: `6` is a type-21 cap over `O2 = K − 6` (on `025` and `234`,
beyond `024`, beneath the other faces). -/
theorem IsCap21.sigma2 (h : IsCap21 F d) : IsCap21 h.O2 c' := by
  have hnd := F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨haa', hab, hab', hac, hac'⟩, ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩,
    ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd
  have n1 := F.abc.neg c' (by simp) (Ne.symm hac') (Ne.symm hbc') (Ne.symm hcc')
  have n2 := F.a'b'c.neg c' (by simp) (Ne.symm ha'c') (Ne.symm hb'c') (Ne.symm hcc')
  refine ⟨F.ab'c'.hR, F.a'bc'.hR, ?_, n2, ?_, F.ab'c.neg c' (by simp) (Ne.symm hac')
    (Ne.symm hb'c') (Ne.symm hcc'), F.a'bc.neg c' (by simp) (Ne.symm ha'c') (Ne.symm hbc')
    (Ne.symm hcc'), n1⟩
  · show 0 < F.abc'.f d * F.abc.f c' - F.abc.f d * F.abc'.f c'
    rw [F.abc'.hR]; nlinarith [h.abc']
  · show F.a'b'c'.f d * F.a'b'c.f c' - F.a'b'c.f d * F.a'b'c'.f c' < 0
    rw [F.a'b'c'.hR]; nlinarith [h.a'b'c']

/-- The point set of `O2 ∪ {6}` is that of `K`. -/
theorem type21_set_O2 (a a' b b' c c' d : ℝ³) :
    insert c' ({b', b, a', a, c, d} : Finset ℝ³) = insert d {a, a', b, b', c, c'} := by
  ext z; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto

end Cap

/-! ### Hidden points -/

/-- **A point hidden at a view.**  The image of `m` along `u` lies strictly inside every
line through the images of two points of `O` that supports the shadow of `O` (all of `O`
weakly on one side, some point strictly): when the shadow is a polygon, `m` projects into
its interior. -/
def HiddenAt (O : Finset ℝ³) (u m : ℝ³) : Prop :=
  ∀ A ∈ O, ∀ B ∈ O, (∀ z ∈ O, 0 ≤ det3 (B - A) (z - A) u) →
    (∃ z ∈ O, 0 < det3 (B - A) (z - A) u) → 0 < det3 (B - A) (m - A) u

theorem det3_rev_neg (A B z u : ℝ³) : det3 (B - A) (z - A) (-u) = det3 (A - B) (z - B) u := by
  simp only [det3_expand, PiLp.sub_apply, PiLp.neg_apply]; ring

/-- Hiddenness does not depend on the orientation of the view. -/
theorem HiddenAt.neg {O : Finset ℝ³} {u m : ℝ³} (h : HiddenAt O u m) : HiddenAt O (-u) m := by
  intro A hA B hB h1 h2
  simp only [det3_rev_neg] at h1 h2 ⊢
  exact h B hB A hA h1 h2

/-- `HiddenAt` for a supporting line in either orientation `σ`. -/
theorem HiddenAt.sigma {O : Finset ℝ³} {u m : ℝ³} (h : HiddenAt O u m) {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) {A B : ℝ³} (hA : A ∈ O) (hB : B ∈ O)
    (h1 : ∀ z ∈ O, 0 ≤ σ * det3 (B - A) (z - A) u)
    (h2 : ∃ z ∈ O, 0 < σ * det3 (B - A) (z - A) u) : 0 < σ * det3 (B - A) (m - A) u := by
  have e : ∀ z, -det3 (B - A) (z - A) u = det3 (A - B) (z - B) u := fun z => by
    simp only [det3_expand, PiLp.sub_apply]; ring
  rcases hσ with rfl | rfl
  · simp only [one_mul] at h1 h2 ⊢; exact h A hA B hB h1 h2
  · simp only [neg_mul, one_mul, e] at h1 h2 ⊢
    exact h B hB A hA h1 h2

/-- **A hidden point at a quad edge.**  If `m` is hidden (`HiddenAt`) at the view along a
quad edge `x → y` of an octahedron, it passes the four edge tests of the shadow
`y, p, y', p'` (`QuadHidden`). -/
theorem quadHidden_of_hiddenAt {x x' y y' p p' m : ℝ³} (F : OctFacets x x' y y' p p')
    (hq₁ : F.a'b'c.f x < F.a'b'c.f y) (hq₂ : F.a'b'c'.f x < F.a'b'c'.f y)
    (hH : HiddenAt {x, x', y, y', p, p'} (y - x) m) : QuadHidden x y y' p p' m := by
  obtain ⟨σ, hσ, hor, E1, E2, E3, E4⟩ := quad_edge_testsσ F hq₁ hq₂
  have hnd := F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨hxx', hxy, hxy', hxp, hxp'⟩, ⟨hx'y, hx'y', hx'p, hx'p'⟩, ⟨hyy', hyp, hyp'⟩,
    ⟨hy'p, hy'p'⟩, hpp', -⟩ := hnd
  have hσ2 : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have z0 : ∀ A B : ℝ³, det3 (B - A) (A - A) (y - x) = 0 := fun A B => by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have z1 : ∀ A B : ℝ³, det3 (B - A) (B - A) (y - x) = 0 := fun A B => by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have key : ∀ T : ℝ, 0 < σ * T → 0 < T * det3 (p - y) (p' - y) (y - x) := fun T hT => by
    have : 0 < (σ * T) * (σ * det3 (p - y) (p' - y) (y - x)) := mul_pos hT hor
    nlinarith
  refine ⟨key _ (hH.sigma hσ (by simp) (by simp) (fun z hz => ?_) ⟨p', by simp, E1 p' (by simp)
      (Ne.symm hyp') (Ne.symm hpp') (Ne.symm hxp')⟩), key _ (hH.sigma hσ (by simp) (by simp)
      (fun z hz => ?_) ⟨y, by simp, E2 y (by simp) hyp hyy'⟩), key _ (hH.sigma hσ (by simp)
      (by simp) (fun z hz => ?_) ⟨p, by simp, E3 p (by simp) (Ne.symm hy'p) hpp'⟩),
    key _ (hH.sigma hσ (by simp) (by simp) (fun z hz => ?_) ⟨y', by simp, E4 y' (by simp)
      hy'p' (Ne.symm hyy') (Ne.symm hxy')⟩)⟩
  · by_cases h1 : z = y
    · rw [h1, z0]; simp
    by_cases h2 : z = p
    · rw [h2, z1]; simp
    by_cases h3 : z = x
    · rw [h3, det3_xy_zero]; simp
    exact (E1 z hz h1 h2 h3).le
  · by_cases h1 : z = p
    · rw [h1, z0]; simp
    by_cases h2 : z = y'
    · rw [h2, z1]; simp
    exact (E2 z hz h1 h2).le
  · by_cases h1 : z = y'
    · rw [h1, z0]; simp
    by_cases h2 : z = p'
    · rw [h2, z1]; simp
    exact (E3 z hz h1 h2).le
  · by_cases h1 : z = p'
    · rw [h1, z0]; simp
    by_cases h2 : z = y
    · rw [h2, z1]; simp
    by_cases h3 : z = x
    · rw [h3, det3_xy_zero']; simp
    exact (E4 z hz h1 h2 h3).le

/-- A facet function is nonpositive on its point set. -/
theorem FacetFn.nonpos {V : Finset ℝ³} {P Q R : ℝ³} (G : FacetFn V P Q R) {w : ℝ³} (hw : w ∈ V) :
    G.f w ≤ 0 := by
  by_cases h1 : w = P
  · rw [h1, G.hP]
  by_cases h2 : w = Q
  · rw [h2, G.hQ]
  by_cases h3 : w = R
  · rw [h3, G.hR]
  exact (G.neg w hw h1 h2 h3).le

/-- **A point beyond a supporting plane is not hidden.**  An affine `g` (constant along `u`)
vanishing at `P, Q ∈ O`, nonpositive on `O`, negative at `r ∈ O` off the vertical plane
through `P Q`, and positive at `m`: the line of `P Q` supports the shadow of `O` and `m` is
strictly outside. -/
theorem not_hiddenAt_of_combo {O : Finset ℝ³} {u m P Q r : ℝ³} {g : ℝ³ → ℝ} {N : ℝ³}
    (hg : ∀ y z, g y - g z = ⟪N, y - z⟫) (hP : g P = 0) (hQ : g Q = 0) (hNu : ⟪N, u⟫ = 0)
    (hPO : P ∈ O) (hQO : Q ∈ O) (hr : r ∈ O) (hgr : g r < 0)
    (hdr : det3 (Q - P) (r - P) u ≠ 0) (hO : ∀ z ∈ O, g z ≤ 0) (hm : 0 < g m) :
    ¬ HiddenAt O u m := by
  intro hH
  have hNe : ⟪N, Q - P⟫ = 0 := by rw [← hg, hP, hQ, sub_zero]
  have key : ∀ z, det3 (Q - P) (z - P) u * g r = det3 (Q - P) (r - P) u * g z := by
    intro z
    have := det3_mul_inner_eq (w := z - P) (w' := r - P) hNe hNu
    rwa [← hg, ← hg, hP, sub_zero, sub_zero] at this
  have e : ∀ z, det3 (P - Q) (z - Q) u = -det3 (Q - P) (z - P) u := fun z => by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have km := key m
  rcases lt_or_gt_of_ne hdr with hn | hp
  · have h := hH Q hQO P hPO (fun z hz => by
        rw [e]; have := key z; have := hO z hz; nlinarith) ⟨r, hr, by rw [e]; linarith⟩
    rw [e] at h
    nlinarith
  · have h := hH P hPO Q hQO (fun z hz => by
        have := key z; have := hO z hz; nlinarith) ⟨r, hr, hp⟩
    nlinarith

/-- **Lemma 1 (a) of §9: at `04` the cap is on the rim.**  At the view along `04` the cap `2`
is never hidden in the shadow of `O6`: it is strictly beyond the silhouette edge at `6`
(`56`, between `056` and `356`, or `36`, between `346` and `356`, by the sign of the face
`356` along the view; on the plane `056` or `346` and beyond `356`). -/
theorem IsCap21.not_hidden_04 {a a' b b' c c' d : ℝ³} {F : OctFacets a a' b b' c c'}
    (hd : IsCap21 F d) : ¬ HiddenAt {a, a', b, b', c, c'} (b - a) d := by
  have hnd := F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨haa', hab, hab', hac, hac'⟩, ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩,
    ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd
  have h356a := F.a'b'c'.neg a (by simp) haa' hab' hac'
  -- the vertical plane through `5 6` misses `0`
  have hdet56 : det3 (c' - b') (a - b') (b - a) ≠ 0 := by
    intro h0
    have hc := cross_ne_zero_of_affine F.ab'c.hN hab' F.ab'c.hP F.ab'c.hQ
      (F.ab'c.neg c' (by simp) (Ne.symm hac') (Ne.symm hb'c') (Ne.symm hcc'))
    have hw : det3 (b' - a) (c' - a) (b - a) = 0 := by
      rw [← h0]; simp only [det3_expand, PiLp.sub_apply]; ring
    have := affine_zero_of_coplanar F.ab'c'.hN F.ab'c'.hP F.ab'c'.hQ F.ab'c'.hR hc hw
    linarith [F.ab'c'.neg b (by simp) (Ne.symm hab) hbb' hbc']
  have hN056 : ⟪F.ab'c'.N, b - a⟫ < 0 := by
    rw [← F.ab'c'.hN, F.ab'c'.hP, sub_zero]; exact F.ab'c'.neg b (by simp) (Ne.symm hab) hbb' hbc'
  have hN346 : 0 < ⟪F.a'bc'.N, b - a⟫ := by
    rw [← F.a'bc'.hN, F.a'bc'.hQ, zero_sub, neg_pos]; exact F.a'bc'.neg a (by simp) haa' hab hac'
  set s := ⟪F.a'b'c'.N, b - a⟫ with hs
  rcases lt_trichotomy s 0 with hs0 | hs0 | hs0
  · -- the silhouette edge `36` (faces `346`, `356`)
    have hdet36 : det3 (c' - a') (a - a') (b - a) ≠ 0 := by
      intro h0
      have hc := cross_ne_zero_of_affine F.a'bc.hN ha'b F.a'bc.hP F.a'bc.hQ
        (F.a'bc.neg c' (by simp) (Ne.symm ha'c') (Ne.symm hbc') (Ne.symm hcc'))
      have hw : det3 (b - a') (c' - a') (a - a') = 0 := by
        rw [← h0]; simp only [det3_expand, PiLp.sub_apply]; ring
      have := affine_zero_of_coplanar F.a'bc'.hN F.a'bc'.hP F.a'bc'.hQ F.a'bc'.hR hc hw
      linarith [F.a'bc'.neg a (by simp) haa' hab hac']
    refine not_hiddenAt_of_combo (pencil_hN F.a'bc'.hN F.a'b'c'.hN (-s) (-⟪F.a'bc'.N, b - a⟫))
      (P := a') (Q := c') (r := a) (u := b - a) ?_ ?_ ?_ (by simp) (by simp) (by simp) ?_ hdet36
      ?_ ?_
    · rw [F.a'bc'.hP, F.a'b'c'.hP]; ring
    · rw [F.a'bc'.hR, F.a'b'c'.hR]; ring
    · rw [inner_sub_left, real_inner_smul_left, real_inner_smul_left, ← hs]; ring
    · have := F.a'bc'.neg a (by simp) haa' hab hac'
      nlinarith
    · intro z hz
      have := F.a'bc'.nonpos hz; have := F.a'b'c'.nonpos hz
      nlinarith
    · rw [hd.a'bc']; nlinarith [hd.a'b'c']
  · -- the face `356` is vertical
    refine not_hiddenAt_of_combo F.a'b'c'.hN (P := b') (Q := c') (r := a) (u := b - a)
      F.a'b'c'.hQ F.a'b'c'.hR (by rw [← hs, hs0]) (by simp) (by simp) (by simp) h356a hdet56
      (fun z hz => F.a'b'c'.nonpos hz) hd.a'b'c'
  · -- the silhouette edge `56` (faces `056`, `356`)
    refine not_hiddenAt_of_combo (pencil_hN F.ab'c'.hN F.a'b'c'.hN s ⟪F.ab'c'.N, b - a⟫)
      (P := b') (Q := c') (r := a) (u := b - a) ?_ ?_ ?_ (by simp) (by simp) (by simp) ?_ hdet56
      ?_ ?_
    · rw [F.ab'c'.hQ, F.a'b'c'.hQ]; ring
    · rw [F.ab'c'.hR, F.a'b'c'.hR]; ring
    · rw [inner_sub_left, real_inner_smul_left, real_inner_smul_left, ← hs]; ring
    · rw [F.ab'c'.hP]; nlinarith
    · intro z hz
      have := F.ab'c'.nonpos hz; have := F.a'b'c'.nonpos hz
      nlinarith
    · rw [hd.ab'c']; nlinarith [hd.a'b'c']

end Minimality

end
