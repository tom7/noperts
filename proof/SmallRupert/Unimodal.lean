module

public import SmallRupert.SixVertices

@[expose] public section

/-!
# L7: unimodal silhouettes

LEMMAS.md L7, in the standard view (`proj_xy`, depth = coordinate 2).

* `exists_forces_of_not_firstOrderInward` (Lemma 7.1, the direction used):
  if no first-order motion is strictly inward, there are horizontal *corner
  forces* `f v` in the normal cones of the shadow at the points of `V`, not all
  zero, with zero sum (E1), zero depth moment (E2) and zero torque (E3).  It is
  stated with normal cones (`normalConeAt`), so it needs neither (G1) nor
  edge normals.
* `hasHorizontalDoubleNormal_of_forces` (Theorem 7.3 (⇒), pure polygon form):
  forces in the normal cones of a strictly convex counterclockwise polygon,
  balanced as in (E1)–(E3), with cyclically unimodal distinct depths, force a
  horizontal double normal of the silhouette cycle.
* `exists_firstOrderInward_of_unimodal`, `isRupert_of_unimodalView` (Theorem
  7.3 at an explicit view): a generic unimodal silhouette without horizontal
  double normal gives a passage.
* `exists_badPlanes` (Lemma 7.4) and `isRupert_of_genericUnimodalView`
  (Theorem 7.5): a generic unimodal view suffices.
* `isRupert_translationPrism` (Theorem 7.7) and
  `isRupert_octahedron_conditionA` (Corollary 7.8).

The silhouette at an explicit view is given by a cyclic list of points
`x : ZMod k → ℝ³` of `V`: (G1) is `IsCcwPolygon (proj_xy ∘ x)` (strictly convex,
counterclockwise) together with "every other point of `V` projects into the
interior", and (G2) is injectivity of the depths, part of `IsCyclicUnimodal`.
-/

namespace SmallRupert

open scoped RealInnerProductSpace

/-- The normal cone of `S` at `p`. -/
def normalConeAt (S : Set ℝ²) (p : ℝ²) : Set ℝ² := {n | ∀ q ∈ S, ⟪n, q - p⟫ ≤ 0}

/-- The 2D cross product `a × b = a₀ b₁ - a₁ b₀`. -/
def cross2 (a b : ℝ²) : ℝ := a 0 * b 1 - a 1 * b 0

/-- **Lemma 7.1 (corner forces), the direction used.**  If no first-order
motion is strictly inward, there are forces `f v ∈ N_S(P v)` (`v ∈ V`), not all
zero, with `Σ f = 0`, `Σ z f = 0`, `Σ P v × f = 0`.  (Points projecting into
the interior of the shadow get `f v = 0`, their normal cone being `{0}`.) -/
theorem exists_forces_of_not_firstOrderInward (V : Finset ℝ³)
    (hint : (interior (proj_xy '' convexHull ℝ (V : Set ℝ³))).Nonempty)
    (h : ∀ ω τ : ℝ³, ¬ FirstOrderInward V ω τ) :
    ∃ f : ℝ³ → ℝ², (∀ v ∈ V, f v ∈ normalConeAt (proj_xy '' convexHull ℝ (V : Set ℝ³))
        (proj_xy v)) ∧ (∃ v ∈ V, f v ≠ 0) ∧ ∑ v ∈ V, f v = 0 ∧ ∑ v ∈ V, v 2 • f v = 0 ∧
      ∑ v ∈ V, cross2 (proj_xy v) (f v) = 0 := by
  sorry

/-- `p` lists the corners of a strictly convex polygon counterclockwise: every
corner lies strictly to the left of every directed edge not containing it. -/
def IsCcwPolygon {k : ℕ} (p : ZMod k → ℝ²) : Prop :=
  3 ≤ k ∧ ∀ i j : ZMod k, j ≠ i → j ≠ i + 1 → 0 < cross2 (p (i + 1) - p i) (p j - p i)

/-- A cyclic sequence of distinct reals with exactly one local maximum (hence
exactly one local minimum). -/
def IsCyclicUnimodal {k : ℕ} [NeZero k] (z : ZMod k → ℝ) : Prop :=
  Function.Injective z ∧
    (Finset.univ.filter (fun i : ZMod k => z (i - 1) < z i ∧ z (i + 1) < z i)).card = 1

/-- The corner `(p i, z i)` of the silhouette cycle in `ℝ³`. -/
noncomputable def liftPt (q : ℝ²) (t : ℝ) : ℝ³ := !₂[q 0, q 1, t]

/-- The silhouette cycle `C = x₀x₁⋯x_{k-1}x₀` has a *horizontal double normal*:
two points of `C` at the same depth whose projections span a double normal of
the shadow `conv p`. -/
def HasHorizontalDoubleNormal {k : ℕ} (p : ZMod k → ℝ²) (z : ZMod k → ℝ) : Prop :=
  ∃ y y' : ℝ³, (∃ i, y ∈ segment ℝ (liftPt (p i) (z i)) (liftPt (p (i + 1)) (z (i + 1)))) ∧
    (∃ j, y' ∈ segment ℝ (liftPt (p j) (z j)) (liftPt (p (j + 1)) (z (j + 1)))) ∧
    y 2 = y' 2 ∧ proj_xy y ≠ proj_xy y' ∧
    proj_xy y' - proj_xy y ∈ normalConeAt (convexHull ℝ (Set.range p)) (proj_xy y') ∧
    proj_xy y - proj_xy y' ∈ normalConeAt (convexHull ℝ (Set.range p)) (proj_xy y)

/-- **Theorem 7.3 (⇒), polygon form.**  Forces in the normal cones of a
strictly convex counterclockwise polygon, not all zero, with zero sum, zero
depth moment and zero torque, at cyclically unimodal distinct depths, force a
horizontal double normal. -/
theorem hasHorizontalDoubleNormal_of_forces {k : ℕ} [NeZero k] (p : ZMod k → ℝ²)
    (z : ZMod k → ℝ) (hp : IsCcwPolygon p) (hz : IsCyclicUnimodal z) (f : ZMod k → ℝ²)
    (hf : ∀ i, f i ∈ normalConeAt (convexHull ℝ (Set.range p)) (p i)) (hne : ∃ i, f i ≠ 0)
    (h1 : ∑ i, f i = 0) (h2 : ∑ i, z i • f i = 0) (h3 : ∑ i, cross2 (p i) (f i) = 0) :
    HasHorizontalDoubleNormal p z := by
  sorry

/-- **Theorem 7.3 at an explicit standard view.**  The silhouette is the cycle
`x`, every other point of `V` projects into the interior of the shadow, the
corner depths are cyclically unimodal and distinct, and there is no horizontal
double normal.  Then some first-order motion is strictly inward. -/
theorem exists_firstOrderInward_of_unimodal (V : Finset ℝ³) {k : ℕ} [NeZero k]
    (x : ZMod k → ℝ³) (hxV : ∀ i, x i ∈ V) (hp : IsCcwPolygon (fun i => proj_xy (x i)))
    (hin : ∀ v ∈ V, (∀ i, v ≠ x i) →
      proj_xy v ∈ interior (convexHull ℝ (Set.range fun i => proj_xy (x i))))
    (hz : IsCyclicUnimodal (fun i => x i 2))
    (hnd : ¬ HasHorizontalDoubleNormal (fun i => proj_xy (x i)) (fun i => x i 2)) :
    ∃ ω τ : ℝ³, FirstOrderInward V ω τ := by
  sorry

/-- **Theorem 7.3, Rupert form, at the view of a rotation `R`.** -/
theorem isRupert_of_unimodalView (V : Finset ℝ³) (R : Matrix (Fin 3) (Fin 3) ℝ) (hR : R ∈ SO3)
    {k : ℕ} [NeZero k] (x : ZMod k → ℝ³) (hxV : ∀ i, x i ∈ V)
    (hp : IsCcwPolygon (fun i => proj_xy (R.toEuclideanLin (x i))))
    (hin : ∀ v ∈ V, (∀ i, v ≠ x i) → proj_xy (R.toEuclideanLin v) ∈
      interior (convexHull ℝ (Set.range fun i => proj_xy (R.toEuclideanLin (x i)))))
    (hz : IsCyclicUnimodal (fun i => (R.toEuclideanLin (x i)) 2))
    (hnd : ¬ HasHorizontalDoubleNormal (fun i => proj_xy (R.toEuclideanLin (x i)))
      (fun i => (R.toEuclideanLin (x i)) 2)) :
    IsRupert V := by
  sorry

/-- **Lemma 7.4 (exceptional views).**  Horizontal double normals at generic
views occur only for views `u = Rᵀ e_z` on finitely many great circles
`l ⟂ u`, determined by `V` alone (cases (a)–(e) of LEMMAS.md). -/
theorem exists_badPlanes (V : Finset ℝ³) :
    ∃ Λ : Finset ℝ³, (∀ l ∈ Λ, l ≠ 0) ∧
      ∀ R ∈ SO3, ∀ (k : ℕ) [NeZero k] (x : ZMod k → ℝ³), (∀ i, x i ∈ V) →
        IsCcwPolygon (fun i => proj_xy (R.toEuclideanLin (x i))) →
        IsCyclicUnimodal (fun i => (R.toEuclideanLin (x i)) 2) →
        HasHorizontalDoubleNormal (fun i => proj_xy (R.toEuclideanLin (x i)))
          (fun i => (R.toEuclideanLin (x i)) 2) →
        ∃ l ∈ Λ, (R.toEuclideanLin l) 2 = 0 := by
  sorry

/-- **Theorem 7.5 (unimodal view criterion).**  A generic view (strictly
convex silhouette `x`, all other points inside, distinct corner depths) with a
unimodal silhouette makes `V` Rupert. -/
theorem isRupert_of_genericUnimodalView (V : Finset ℝ³) (R : Matrix (Fin 3) (Fin 3) ℝ)
    (hR : R ∈ SO3) {k : ℕ} [NeZero k] (x : ZMod k → ℝ³) (hxV : ∀ i, x i ∈ V)
    (hp : IsCcwPolygon (fun i => proj_xy (R.toEuclideanLin (x i))))
    (hin : ∀ v ∈ V, (∀ i, v ≠ x i) → proj_xy (R.toEuclideanLin v) ∈
      interior (convexHull ℝ (Set.range fun i => proj_xy (R.toEuclideanLin (x i)))))
    (hz : IsCyclicUnimodal (fun i => (R.toEuclideanLin (x i)) 2)) :
    IsRupert V := by
  sorry

/-- **Theorem 7.7 (translation prisms).**  `K = T + [0, w]` for a triangle
`T = ABC` and `w` not parallel to its plane.  If `w` is not perpendicular to
the plane of `T`, or `T` has an obtuse angle, `K` is Rupert.  (Right prisms over
non-obtuse triangles remain open.) -/
theorem isRupert_translationPrism (A B C w : ℝ³) (hind : AffineIndependent ℝ ![A, B, C, A + w])
    (h : ⟪w, B - A⟫ ≠ 0 ∨ ⟪w, C - A⟫ ≠ 0 ∨ ⟪B - A, C - A⟫ < 0 ∨ ⟪A - B, C - B⟫ < 0 ∨
      ⟪A - C, B - C⟫ < 0) :
    IsRupert {A, B, C, A + w, B + w, C + w} := by
  sorry

/-- An octahedron with opposite vertex pairs `(a, a')`, `(b, b')`, `(c, c')`:
the eight triangles with one vertex from each pair are facets. -/
structure IsOctahedron (a a' b b' c c' : ℝ³) : Prop where
  nodup : [a, a', b, b', c, c'].Nodup
  facet_abc : IsFacetTriangle {a, a', b, b', c, c'} a b c
  facet_abc' : IsFacetTriangle {a, a', b, b', c, c'} a b c'
  facet_ab'c : IsFacetTriangle {a, a', b, b', c, c'} a b' c
  facet_ab'c' : IsFacetTriangle {a, a', b, b', c, c'} a b' c'
  facet_a'bc : IsFacetTriangle {a, a', b, b', c, c'} a' b c
  facet_a'bc' : IsFacetTriangle {a, a', b, b', c, c'} a' b c'
  facet_a'b'c : IsFacetTriangle {a, a', b, b', c, c'} a' b' c
  facet_a'b'c' : IsFacetTriangle {a, a', b, b', c, c'} a' b' c'

/-- **Corollary 7.8 (Condition A).**  With `d = a - a'`, if the projections of
the diagonals `bb'` and `cc'` onto the axis `aa'` overlap in more than a point,
the octahedron is Rupert. -/
theorem isRupert_octahedron_conditionA {a a' b b' c c' : ℝ³} (h : IsOctahedron a a' b b' c c')
    (hA : max (min ⟪a - a', b⟫ ⟪a - a', b'⟫) (min ⟪a - a', c⟫ ⟪a - a', c'⟫) <
      min (max ⟪a - a', b⟫ ⟪a - a', b'⟫) (max ⟪a - a', c⟫ ⟪a - a', c'⟫)) :
    IsRupert {a, a', b, b', c, c'} := by
  sorry

end SmallRupert

end
