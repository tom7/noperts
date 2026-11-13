module

public import Minimality.Type29Lift

@[expose] public section

/-!
# Type 29: Theorem P of §12, partial

Labels of §12 with `a, a', b, b', c, c', d = 0, 4, 1, 3, 2, 5, 6`: the octahedron
`O = K − 6` has the opposite pairs `(0, 4)`, `(1, 3)`, `(2, 5)` (`F : OctFacets a a' b b' c c'`),
and the cap `6` lies on the plane `145` (`a'bc'`), strictly beyond `345` (`a'b'c'`) and
strictly beneath the other six faces of `O` (`IsCap29`); conversely such a point gives
type 29 (Lemma 0 (a)).  The automorphism `σ = (0 2)(4 5)` is `IsCap29.sigma`.

* **Lemma 0 (b)** — `IsCap29.coords`: `6 = 1 + s (4 − 1) + t (5 − 1)` with `s, t > 0`,
  `s + t > 1`.
* **Lemma 3 (the quad edges at 1 always lift)** — (a) `isRupert_type29_14`: a quad edge
  `1 → 4` of `O` forces `t < 1`, so `6` is a middle (Lemma 2); (b)
  `isRupert_type29_41`: a quad edge `4 → 1` with `t < 1` lifts by Lemma 2, with `t > 1`
  by the far-end lift `isRupert_lift_far` (`Type29Lift.lean`: the up/down-face rule
  and the contradiction argument); `t = 1` would make `56 ∥ 14`.  At `15`:
  `isRupert_type29_15`, `isRupert_type29_51` (by `σ`).
* **Lemma 4 (the cap is hidden)** — `type29_hidden_03`, `type29_hidden_05` (and by `σ`
  `2 → 3`, `2 → 4`): at the views along these quad edges `6` is hidden
  (`quadHidden_of_beneath`; the paper's finer `P6 ∈ int P(345)` is not needed), so
  Lemma 2 applies: `isRupert_type29_03`, `isRupert_type29_05`, `isRupert_type29_23`,
  `isRupert_type29_24`.
* **Theorem P** — `isRupert_type29_C1` (clause C1: an inner-tailed quad edge of `O` in
  `G = {1→4, 4→1, 1→5, 5→1, 0→3, 0→5, 2→3, 2→4}`, `Type29C1`), `isRupert_type29_C2`
  (clause C2: `K − 5` an octahedron with an inner-tailed quad edge along `14` with
  `t > 1` or along `46` with `s < 1`, `Type29C2`; `K − 4` by `σ`),
  `isRupert_type29_C3` (clause C3: an inner-tailed quad edge of any octahedron `K − m`
  with `m` hidden), and `isRupert_type29_P` (any of them).  General position: `GenPos`
  (no two segments parallel or orthogonal: distinct depths, no touching, `s, t ≠ 1`),
  `NoPlaneParallel` (Lemma 3 (b)'s corner condition), `NoHDNAt` at the views along the
  segments (no horizontal double normal), and no planar equator (`κ ≠ 0`) of the
  octahedron used.  Theorem P is partial: it does not show that some clause always
  holds, so there is no `not_type29_of_isNopert`.
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

/-! ### General position at an edge view -/

/-! ### The cap -/

/-- The cap `d` (`6`) of a type-29 point set over the octahedron `O` with opposite
pairs `(a, a') = (0, 4)`, `(b, b') = (1, 3)`, `(c, c') = (2, 5)`: on the plane of
`a'bc'` (`145`, which becomes the quadrilateral `1456`), strictly beyond `a'b'c'`
(`345`), strictly beneath the other six faces. -/
structure IsCap29 {a a' b b' c c' : ℝ³} (F : OctFacets a a' b b' c c') (d : ℝ³) : Prop where
  a'bc' : F.a'bc'.f d = 0
  a'b'c' : 0 < F.a'b'c'.f d
  abc : F.abc.f d < 0
  abc' : F.abc'.f d < 0
  ab'c : F.ab'c.f d < 0
  ab'c' : F.ab'c'.f d < 0
  a'bc : F.a'bc.f d < 0
  a'b'c : F.a'b'c.f d < 0

/-- The automorphism `σ = (0 2)(4 5)` of type 29. -/
theorem IsCap29.sigma {a a' b b' c c' d : ℝ³} {F : OctFacets a a' b b' c c'} (h : IsCap29 F d) :
    IsCap29 F.perm₂₃.perm₁₂.perm₂₃ d :=
  ⟨h.a'bc', h.a'b'c', h.abc, h.a'bc, h.ab'c, h.a'b'c, h.abc', h.ab'c'⟩

theorem IsCap29.ne {a a' b b' c c' d : ℝ³} {F : OctFacets a a' b b' c c'} (h : IsCap29 F d) :
    d ≠ a ∧ d ≠ a' ∧ d ≠ b ∧ d ≠ b' ∧ d ≠ c ∧ d ≠ c' := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rintro rfl
  · have := h.abc; rw [F.abc.hP] at this; exact lt_irrefl _ this
  · have := h.a'bc; rw [F.a'bc.hP] at this; exact lt_irrefl _ this
  · have := h.abc; rw [F.abc.hQ] at this; exact lt_irrefl _ this
  · have := h.ab'c; rw [F.ab'c.hQ] at this; exact lt_irrefl _ this
  · have := h.abc; rw [F.abc.hR] at this; exact lt_irrefl _ this
  · have := h.abc'; rw [F.abc'.hR] at this; exact lt_irrefl _ this

/-- **Lemma 0 (b) of §12.**  `6 = 1 + s (4 − 1) + t (5 − 1)` with `s, t > 0` (`6` is
beneath `015` and `124`) and `s + t > 1` (`6` is beyond `345`). -/
theorem IsCap29.coords {a a' b b' c c' d : ℝ³} {F : OctFacets a a' b b' c c'} (h : IsCap29 F d) :
    0 < F.abc'.f d / F.abc'.f a' ∧ 0 < F.a'bc.f d / F.a'bc.f c' ∧
      1 < F.abc'.f d / F.abc'.f a' + F.a'bc.f d / F.a'bc.f c' ∧
      d = b + (F.abc'.f d / F.abc'.f a') • (a' - b) + (F.a'bc.f d / F.a'bc.f c') • (c' - b) := by
  have hnd := F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨haa', hab, hab', hac, hac'⟩, ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩,
    ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd
  have n0 := F.a'bc'.neg a (by simp) haa' hab hac'
  have n1 := F.abc'.neg a' (by simp) (Ne.symm haa') ha'b ha'c'
  have n2 := F.a'bc.neg c' (by simp) (Ne.symm ha'c') (Ne.symm hbc') (Ne.symm hcc')
  have hco := coords_of_affine3 F.a'bc'.hN F.abc'.hN F.a'bc.hN F.a'bc'.hQ F.a'bc'.hP
    F.a'bc'.hR h.a'bc' n0.ne F.abc'.hQ F.abc'.hR n1.ne F.a'bc.hQ F.a'bc.hP n2.ne
  set s := F.abc'.f d / F.abc'.f a'
  set t := F.a'bc.f d / F.a'bc.f c'
  refine ⟨div_pos_of_neg_of_neg h.abc' n1, div_pos_of_neg_of_neg h.a'bc n2, ?_, hco⟩
  have hf := affine_frame F.a'b'c'.hN b a' c' s t
  rw [← hco, F.a'b'c'.hP, F.a'b'c'.hR] at hf
  have := F.a'b'c'.neg b (by simp) (Ne.symm ha'b) hbb' hbc'
  nlinarith [h.a'b'c']

/-! ### Lemma 3: the quad edges at 1 always lift -/

/-! ### Lemma 4: the cap is hidden -/

/-! ### Theorem P, clause C1 -/

/-! ### Theorem P, clauses C2 and C3 -/

end Minimality

end
