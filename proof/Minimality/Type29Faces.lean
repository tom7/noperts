module

public import Minimality.Type29Sec
public import Minimality.Type21Limit

@[expose] public section

/-!
# Type 29: the nine facets of the normal form (`FEWER-FACES-PROOFS.md` §21.0, §22, §28)

The faces of a type-29 point set are `012, 015, 023, 035, 124, 1456, 234, 346, 356`
(`sevenTypeFaces 28`).  For a normal form `N : NF29 x` each facet function is the orientation
determinant of three of its points (`Face16.ofPoly`), whose value at every vertex is a
polynomial in the eight parameters times the frame determinant; the signs are the inequalities
of `NF29` (`nlinarith`).  `Facets29`: the nine facets, with convex position (`Facets29.noSeg`),
as `Facets21` for type 21.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

variable {x : Fin 7 → ℝ³}

/-- **A facet from the orientation determinant of three of its points**: the function
`−σ D · det3 (Q − P, R − P, · − P)`, with `det3 (…, x i − P) = p i · D` and `σ p i > 0` off `S`. -/
noncomputable def Face16.ofPoly {S : Finset (Fin 7)} (N : NF29 x) (P Q R : Fin 7) (σ : ℝ)
    (p : Fin 7 → ℝ)
    (hp : ∀ i, det3 (x Q - x P) (x R - x P) (x i - x P) = p i * N.D)
    (h0 : ∀ i ∈ S, p i = 0) (h1 : ∀ i ∉ S, 0 < σ * p i) : Face16 x S where
  f y := (-σ * N.D) * det3 (x Q - x P) (x R - x P) (y - x P)
  N := (-σ * N.D) • cross (x Q - x P) (x R - x P)
  hN y z := by
    rw [real_inner_smul_left, ← mul_sub, det3, det3, ← inner_sub_right]
    congr 2; abel
  zero i hi := by rw [hp, h0 i hi]; ring
  neg i hi := by
    rw [hp]
    have h := h1 i hi
    have hD0 : N.D ≠ 0 := N.hD
    have hD : 0 < N.D ^ 2 := by positivity
    nlinarith

/-- The value of `Face16.ofPoly` at a vertex. -/
theorem Face16.ofPoly_f {S : Finset (Fin 7)} (N : NF29 x) (P Q R : Fin 7) (σ : ℝ)
    (p : Fin 7 → ℝ) (hp : ∀ i, det3 (x Q - x P) (x R - x P) (x i - x P) = p i * N.D)
    (h0 : ∀ i ∈ S, p i = 0) (h1 : ∀ i ∉ S, 0 < σ * p i) (i : Fin 7) :
    (Face16.ofPoly N P Q R σ p hp h0 h1).f (x i) = (-σ * N.D) * (p i * N.D) := by
  show (-σ * N.D) * det3 (x Q - x P) (x R - x P) (x i - x P) = _
  rw [hp]

/-- The determinant of a facet's three points with a point of the shape. -/
macro "face29_det " N:term:max : tactic =>
  `(tactic| (
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Fin.isValue,
      Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
    nf29_simp $N
    simp only [det3c, NF29.D]
    ring))

macro "face29_zero " hi:term:max : tactic =>
  `(tactic| first
    | (exfalso; revert $hi; decide)
    | simp)

macro "face29_pos " N:term:max hi:term:max : tactic =>
  `(tactic| first
    | exact absurd (by decide) $hi
    | (
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Fin.isValue,
        Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
      nlinarith [NF29.hh0 $N, NF29.hh2 $N, NF29.ha0 $N, NF29.hb2 $N, NF29.t345_0 $N,
        NF29.t345_2 $N, NF29.hF4 $N, NF29.hF5 $N, NF29.hDD $N, NF29.hDG4 $N, NF29.hDG5 $N,
        NF29.hE35 $N, NF29.hE24 $N, NF29.hs $N, NF29.ht $N, NF29.hst $N, NF29.d023 $N,
        NF29.d035 $N, NF29.d234 $N]))

/-- The facet `{0, 1, 2}` of a type-29 shape from the normal form. -/
noncomputable def NF29.f012 (N : NF29 x) : Face16 x {0, 1, 2} :=
  Face16.ofPoly N 0 1 2 1
    ![0, 0, 0, N.a0 * N.b2 + -(N.a2 * N.b0), N.b0 * N.h2 + -(N.b2 * N.h0),
     -(N.a0 * N.h2) + N.a2 * N.h0,
     -(N.a0 * N.h2 * N.t) + N.a2 * N.h0 * N.t + N.b0 * N.h2 * N.s + -(N.b2 * N.h0 * N.s)]
    (by intro i; fin_cases i <;> face29_det N)
    (by intro i hi; fin_cases i <;> face29_zero hi)
    (by intro i hi; fin_cases i <;> face29_pos N hi)

/-- The facet `{0, 1, 5}` of a type-29 shape from the normal form. -/
noncomputable def NF29.f015 (N : NF29 x) : Face16 x {0, 1, 5} :=
  Face16.ofPoly N 0 1 5 (-1)
    ![0, 0, N.a0 * N.h2 + -(N.a2 * N.h0), N.a0, -(N.h0), 0, -(N.h0 * N.s)]
    (by intro i; fin_cases i <;> face29_det N)
    (by intro i hi; fin_cases i <;> face29_zero hi)
    (by intro i hi; fin_cases i <;> face29_pos N hi)

/-- The facet `{0, 2, 3}` of a type-29 shape from the normal form. -/
noncomputable def NF29.f023 (N : NF29 x) : Face16 x {0, 2, 3} :=
  Face16.ofPoly N 0 2 3 1
    ![0, N.a0 * N.b2 + -(N.a2 * N.b0), 0, 0,
     N.a0 * N.b2 + -(N.a2 * N.b0) + N.b0 + -(N.b0 * N.h2) + -(N.b2) + N.b2 * N.h0,
     -(N.a0) + N.a0 * N.b2 + N.a0 * N.h2 + N.a2 + -(N.a2 * N.b0) + -(N.a2 * N.h0),
     N.a0 * N.b2 + N.a0 * N.h2 * N.t + -(N.a0 * N.t) + -(N.a2 * N.b0) + -(N.a2 * N.h0 * N.t)
       + N.a2 * N.t + -(N.b0 * N.h2 * N.s) + N.b0 * N.s + N.b2 * N.h0 * N.s + -(N.b2 * N.s)]
    (by intro i; fin_cases i <;> face29_det N)
    (by intro i hi; fin_cases i <;> face29_zero hi)
    (by intro i hi; fin_cases i <;> face29_pos N hi)

/-- The facet `{0, 3, 5}` of a type-29 shape from the normal form. -/
noncomputable def NF29.f035 (N : NF29 x) : Face16 x {0, 3, 5} :=
  Face16.ofPoly N 0 3 5 1
    ![0, -(N.a0), -(N.a0) + N.a0 * N.b2 + N.a0 * N.h2 + N.a2 + -(N.a2 * N.b0) + -(N.a2 * N.h0),
     0, (1) + -(N.a0) + -(N.b0) + -(N.h0), 0,
     -(N.a0) + N.a0 * N.t + -(N.b0 * N.s) + -(N.h0 * N.s) + N.s]
    (by intro i; fin_cases i <;> face29_det N)
    (by intro i hi; fin_cases i <;> face29_zero hi)
    (by intro i hi; fin_cases i <;> face29_pos N hi)

/-- The facet `{1, 2, 4}` of a type-29 shape from the normal form. -/
noncomputable def NF29.f124 (N : NF29 x) : Face16 x {1, 2, 4} :=
  Face16.ofPoly N 1 2 4 (-1)
    ![-(N.b0 * N.h2) + N.b2 * N.h0, 0, 0, N.b2, 0, -(N.h2), -(N.h2 * N.t)]
    (by intro i; fin_cases i <;> face29_det N)
    (by intro i hi; fin_cases i <;> face29_zero hi)
    (by intro i hi; fin_cases i <;> face29_pos N hi)

/-- The facet `{1, 4, 5, 6}` of a type-29 shape from the normal form. -/
noncomputable def NF29.f1456 (N : NF29 x) : Face16 x {1, 4, 5, 6} :=
  Face16.ofPoly N 1 4 5 (-1)
    ![-(N.h0), 0, -(N.h2), (-1), 0, 0, 0]
    (by intro i; fin_cases i <;> face29_det N)
    (by intro i hi; fin_cases i <;> face29_zero hi)
    (by intro i hi; fin_cases i <;> face29_pos N hi)

/-- The facet `{2, 3, 4}` of a type-29 shape from the normal form. -/
noncomputable def NF29.f234 (N : NF29 x) : Face16 x {2, 3, 4} :=
  Face16.ofPoly N 2 3 4 (-1)
    ![-(N.a0 * N.b2) + N.a2 * N.b0 + -(N.b0) + N.b0 * N.h2 + N.b2 + -(N.b2 * N.h0), N.b2, 0, 0,
     0, (-1) + N.a2 + N.b2 + N.h2, N.a2 * N.t + N.b2 + -(N.b2 * N.s) + N.h2 * N.t + -(N.t)]
    (by intro i; fin_cases i <;> face29_det N)
    (by intro i hi; fin_cases i <;> face29_zero hi)
    (by intro i hi; fin_cases i <;> face29_pos N hi)

/-- The facet `{3, 4, 6}` of a type-29 shape from the normal form. -/
noncomputable def NF29.f346 (N : NF29 x) : Face16 x {3, 4, 6} :=
  Face16.ofPoly N 3 4 6 1
    ![-(N.a0 * N.t) + -(N.b0) + N.b0 * N.s + -(N.h0 * N.t) + N.t, N.t,
     -(N.a2 * N.t) + -(N.b2) + N.b2 * N.s + -(N.h2 * N.t) + N.t, 0, 0, (-1) + N.s + N.t, 0]
    (by intro i; fin_cases i <;> face29_det N)
    (by intro i hi; fin_cases i <;> face29_zero hi)
    (by intro i hi; fin_cases i <;> face29_pos N hi)

/-- The facet `{3, 5, 6}` of a type-29 shape from the normal form. -/
noncomputable def NF29.f356 (N : NF29 x) : Face16 x {3, 5, 6} :=
  Face16.ofPoly N 3 5 6 (-1)
    ![N.a0 + -(N.a0 * N.t) + N.b0 * N.s + N.h0 * N.s + -(N.s), -(N.s),
     N.a2 + -(N.a2 * N.t) + N.b2 * N.s + N.h2 * N.s + -(N.s), 0, (1) + -(N.s) + -(N.t), 0, 0]
    (by intro i; fin_cases i <;> face29_det N)
    (by intro i hi; fin_cases i <;> face29_zero hi)
    (by intro i hi; fin_cases i <;> face29_pos N hi)

/-- Two vertices at the same height over the quadrilateral `1456` have equal frame heights. -/
theorem NF29.f1456_eq (N : NF29 x) {i j : Fin 7}
    (h : ⟪N.f1456.N, x i⟫ = ⟪N.f1456.N, x j⟫) :
    ![-N.h0, 0, -N.h2, -1, 0, 0, 0] i = ![-N.h0, 0, -N.h2, -1, 0, 0, 0] j := by
  have k := N.f1456.hN (x i) (x j)
  rw [inner_sub_right, h, sub_self] at k
  have fi : N.f1456.f (x i) = (-(-1 : ℝ) * N.D) * (![-N.h0, 0, -N.h2, -1, 0, 0, 0] i * N.D) :=
    Face16.ofPoly_f N 1 4 5 (-1) _ _ _ _ i
  have fj : N.f1456.f (x j) = (-(-1 : ℝ) * N.D) * (![-N.h0, 0, -N.h2, -1, 0, 0, 0] j * N.D) :=
    Face16.ofPoly_f N 1 4 5 (-1) _ _ _ _ j
  rw [fi, fj] at k
  have hD : N.D ^ 2 ≠ 0 := pow_ne_zero 2 N.hD
  have : N.D ^ 2 * (![-N.h0, 0, -N.h2, -1, 0, 0, 0] i - ![-N.h0, 0, -N.h2, -1, 0, 0, 0] j) = 0 := by
    linear_combination k
  have := (mul_eq_zero.mp this).resolve_left hD
  linarith

/-- **The facets of a type-29 shape**: seven distinct points with the nine facets of type 29. -/
structure Facets29 (x : Fin 7 → ℝ³) where
  inj : Function.Injective x
  f012 : Face16 x {0, 1, 2}
  f015 : Face16 x {0, 1, 5}
  f023 : Face16 x {0, 2, 3}
  f035 : Face16 x {0, 3, 5}
  f124 : Face16 x {1, 2, 4}
  f1456 : Face16 x {1, 4, 5, 6}
  f234 : Face16 x {2, 3, 4}
  f346 : Face16 x {3, 4, 6}
  f356 : Face16 x {3, 5, 6}

/-- The facets of a normal form. -/
noncomputable def NF29.facets (N : NF29 x) : Facets29 x :=
  ⟨N.inj, N.f012, N.f015, N.f023, N.f035, N.f124, N.f1456, N.f234, N.f346, N.f356⟩

/-- **Type 29 is in convex position**: each vertex is cut off by its facets. -/
theorem Facets29.noSeg (T : Facets29 x) :
    ∀ i j m : Fin 7, x m ≠ x i → x m ≠ x j → ∀ s : ℝ, 0 < s → s < 1 →
      x m ≠ x i + s • (x j - x i) := by
  intro i j m hmi hmj s hs0 hs1
  have hmi' : m ≠ i := fun h => hmi (by rw [h])
  have hmj' : m ≠ j := fun h => hmj (by rw [h])
  fin_cases m <;> fin_cases i <;> fin_cases j <;>
    first
    | exact absurd rfl hmi'
    | exact absurd rfl hmj'
    | exact T.f012.ne_seg (by decide) (by decide) s hs0 hs1
    | exact T.f015.ne_seg (by decide) (by decide) s hs0 hs1
    | exact T.f023.ne_seg (by decide) (by decide) s hs0 hs1
    | exact T.f035.ne_seg (by decide) (by decide) s hs0 hs1
    | exact T.f124.ne_seg (by decide) (by decide) s hs0 hs1
    | exact T.f1456.ne_seg (by decide) (by decide) s hs0 hs1
    | exact T.f234.ne_seg (by decide) (by decide) s hs0 hs1
    | exact T.f346.ne_seg (by decide) (by decide) s hs0 hs1
    | exact T.f356.ne_seg (by decide) (by decide) s hs0 hs1

theorem NF29.noSeg (N : NF29 x) :
    ∀ i j m : Fin 7, x m ≠ x i → x m ≠ x j → ∀ s : ℝ, 0 < s → s < 1 →
      x m ≠ x i + s • (x j - x i) :=
  N.facets.noSeg

end Minimality

end
