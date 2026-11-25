module

public import Mathlib
public import Minimality.HiddenCapFree

/-!
# Fixed base, moving apex: Lemma UP and Lemma APEX (Fable HOLE3 reply, section 1.2-1.3)

For three points `a, b, c` of a finite set `O` (for type 24: `x 0, x 2, x 6`, the base triangle `026`
of the cap over vertex `1`) and an apex `x`, the open cone of the apex is
`C(x) = {ca (a - x) + cb (b - x) + cc (c - x) | ca, cb, cc > 0}`.

* `cone_mono` (Lemma UP (a)): if `x' = x + t (p - x)` with `p` in the triangle `conv {a, b, c}` and
  `0 <= t < 1`, then `C(x) ⊆ C(x')`, with explicit coefficients, and
  `det3 (a - x') (b - x') (c - x') = (1 - t) Split.det3 (a - x) (b - x) (c - x)` (`det3_apex`).
* `freeAt_insert_of_cone_mono` (Lemma UP (b), Rupert level): a first-order free view `u` of `O`
  in `C(x)` is a free view of `insert x' O` for every such `x'` (`FreeAt` is the common currency of
  all leaves: Lex, Split, face-chord of `O` give `FreeAt O u` at `u` in the interior of the screen
  rim).  The converse is `freeAt_of_insert_of_cone`, so freedom at a cone view depends on `O` only.
* `freeAt_insert_apex`, `isRupert_insert_apex` (Lemma APEX): if `A` is a point with independent
  edges to `a, b, c` and `O` is free at a view `u` in `C(A)`, then `insert x O` is free (hence
  Rupert) for EVERY `x` in the tetrahedron `conv {A, a, b, c}` minus the base triangle.  No
  obtuseness, no metric condition, no type-24 structure.

TODO (not done): the type-24 instance, `CbarIn` with `Delta > 0` iff the three planes of the
facets `236, 046, 025` meet at a point `A*` with all frame coordinates negative (referee: exact on
168807 points; Fable proved it only in the symmetric case).
-/

@[expose] public section

set_option autoImplicit false

namespace Minimality.T24.Apex
open Minimality Minimality.Split

/-- Determinant of the edges from an apex moved towards the base triangle. -/
theorem det3_apex (a b c x p : ℝ³) (l1 l2 l3 t : ℝ) (hsum : l1 + l2 + l3 = 1)
    (hp : p = l1 • a + l2 • b + l3 • c) :
    Split.det3 (a - (x + t • (p - x))) (b - (x + t • (p - x))) (c - (x + t • (p - x))) =
      (1 - t) * Split.det3 (a - x) (b - x) (c - x) := by
  have h3 : l3 = 1 - l1 - l2 := by linarith
  subst hp h3
  simp only [Split.det3, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  ring

/-- Lemma UP (a): the cone of `x` lies in the cone of `x' = x + t (p - x)`. -/
theorem cone_mono (a b c x p : ℝ³) (l1 l2 l3 t : ℝ) (hl1 : 0 ≤ l1) (hl2 : 0 ≤ l2) (hl3 : 0 ≤ l3)
    (hsum : l1 + l2 + l3 = 1) (hp : p = l1 • a + l2 • b + l3 • c) (ht0 : 0 ≤ t) (ht1 : t < 1)
    (ca cb cc : ℝ) (hca : 0 < ca) (hcb : 0 < cb) (hcc : 0 < cc) :
    ∃ ca' cb' cc' : ℝ, 0 < ca' ∧ 0 < cb' ∧ 0 < cc' ∧
      ca • (a - x) + cb • (b - x) + cc • (c - x) =
        ca' • (a - (x + t • (p - x))) + cb' • (b - (x + t • (p - x))) +
          cc' • (c - (x + t • (p - x))) := by
  have h1 : 0 < 1 - t := by linarith
  have h3 : l3 = 1 - l1 - l2 := by linarith
  set s : ℝ := t / (1 - t) * (ca + cb + cc) with hs
  have hs0 : 0 ≤ s := by
    have : 0 ≤ t / (1 - t) := div_nonneg ht0 h1.le
    rw [hs]; positivity
  refine ⟨ca + s * l1, cb + s * l2, cc + s * l3, by nlinarith, by nlinarith, by nlinarith, ?_⟩
  subst hp h3
  ext i
  simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  rw [hs]
  field_simp
  ring

/-- Lemma UP (b), Rupert level: freedom of `O` at a view of the cone of `x` gives freedom of
`insert x'` at the same view, for every `x'` between `x` and the base triangle. -/
theorem freeAt_insert_of_cone_mono (O : Finset ℝ³) (a b c x p : ℝ³) (ha : a ∈ O) (hb : b ∈ O)
    (hc : c ∈ O) (hD : Split.det3 (a - x) (b - x) (c - x) ≠ 0) (l1 l2 l3 t : ℝ) (hl1 : 0 ≤ l1)
    (hl2 : 0 ≤ l2) (hl3 : 0 ≤ l3) (hsum : l1 + l2 + l3 = 1) (hp : p = l1 • a + l2 • b + l3 • c)
    (ht0 : 0 ≤ t) (ht1 : t < 1) (ca cb cc : ℝ) (hca : 0 < ca) (hcb : 0 < cb) (hcc : 0 < cc)
    (hfree : FreeAt O (ca • (a - x) + cb • (b - x) + cc • (c - x))) :
    FreeAt (insert (x + t • (p - x)) O) (ca • (a - x) + cb • (b - x) + cc • (c - x)) := by
  obtain ⟨ca', cb', cc', h1, h2, h3, he⟩ :=
    cone_mono a b c x p l1 l2 l3 t hl1 hl2 hl3 hsum hp ht0 ht1 ca cb cc hca hcb hcc
  rw [he] at hfree ⊢
  refine freeAt_insert_of_cone O _ a b c ha hb hc ?_ ca' cb' cc' (Or.inl ⟨h1, h2, h3⟩) hfree
  rw [det3_apex a b c x p l1 l2 l3 t hsum hp]
  exact mul_ne_zero (by linarith) hD

/-- Lemma APEX, free form: `A` with independent edges to `a, b, c ∈ O`, `O` free at a view in the
open cone of `A`; then `insert x O` is free for `x = A + t (p - A)`, `p` in the triangle, `t < 1`. -/
theorem freeAt_insert_apex (O : Finset ℝ³) (a b c A p x : ℝ³) (ha : a ∈ O) (hb : b ∈ O)
    (hc : c ∈ O) (hD : Split.det3 (a - A) (b - A) (c - A) ≠ 0) (l1 l2 l3 t : ℝ) (hl1 : 0 ≤ l1)
    (hl2 : 0 ≤ l2) (hl3 : 0 ≤ l3) (hsum : l1 + l2 + l3 = 1) (hp : p = l1 • a + l2 • b + l3 • c)
    (ht0 : 0 ≤ t) (ht1 : t < 1) (hx : x = A + t • (p - A)) (ca cb cc : ℝ) (hca : 0 < ca)
    (hcb : 0 < cb) (hcc : 0 < cc) (hfree : FreeAt O (ca • (a - A) + cb • (b - A) + cc • (c - A))) :
    FreeAt (insert x O) (ca • (a - A) + cb • (b - A) + cc • (c - A)) := by
  subst hx
  exact freeAt_insert_of_cone_mono O a b c A p ha hb hc hD l1 l2 l3 t hl1 hl2 hl3 hsum hp ht0 ht1
    ca cb cc hca hcb hcc hfree

/-- Lemma APEX, Rupert form: `isRupert (insert x O)` for every apex `x` in `conv {A, a, b, c}`
off the base triangle, when `O` is free at one view of the open cone of `A`. -/
theorem isRupert_insert_apex (O : Finset ℝ³) (a b c A p x : ℝ³) (ha : a ∈ O) (hb : b ∈ O)
    (hc : c ∈ O) (hD : Split.det3 (a - A) (b - A) (c - A) ≠ 0) (l1 l2 l3 t : ℝ) (hl1 : 0 ≤ l1)
    (hl2 : 0 ≤ l2) (hl3 : 0 ≤ l3) (hsum : l1 + l2 + l3 = 1) (hp : p = l1 • a + l2 • b + l3 • c)
    (ht0 : 0 ≤ t) (ht1 : t < 1) (hx : x = A + t • (p - A)) (ca cb cc : ℝ) (hca : 0 < ca)
    (hcb : 0 < cb) (hcc : 0 < cc) (hfree : FreeAt O (ca • (a - A) + cb • (b - A) + cc • (c - A))) :
    IsRupert (insert x O) := by
  refine FreeAt.isRupert ?_ (freeAt_insert_apex O a b c A p x ha hb hc hD l1 l2 l3 t hl1 hl2 hl3
    hsum hp ht0 ht1 hx ca cb cc hca hcb hcc hfree)
  intro h0
  have h1 : Split.det3 (ca • (a - A) + cb • (b - A) + cc • (c - A)) (b - A) (c - A) =
      ca * Split.det3 (a - A) (b - A) (c - A) := by
    simp only [Split.det3, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  rw [h0] at h1
  have h2 : Split.det3 (0 : ℝ³) (b - A) (c - A) = 0 := by simp [Split.det3]
  rw [h2] at h1
  exact hD ((mul_eq_zero.1 h1.symm).resolve_left hca.ne')

end Minimality.T24.Apex
