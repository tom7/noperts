module

public import SmallRupert.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic

@[expose] public section

/-!
# L1: a strictly inward first-order motion gives a passage

LEMMAS.md Lemma 1, in the standard view.  `K = convexHull ℝ V`,
`S = proj_xy '' K` is the shadow.  A first-order motion `(ω, τ)` is
*strictly inward* (`FirstOrderInward`) if its screen velocity at every point
`v ∈ V` points strictly into `S` at `proj_xy v`.  For points projecting into
`interior S` this is automatic (`isInwardAt_of_mem_interior`), so the
condition only concerns LEMMAS.md's boundary vertices `V_∂`
(`firstOrderInward_iff_frontier`); `V` need not consist of vertices only.

The rotation curve `R_s` is arbitrary as long as `R 0 = 1` and `R' 0 = [ω]×`
entrywise (`eventually_innerShadow_subset`).  LEMMAS.md uses
`R_s = exp(s[ω]×)`; for the `IsRupert` corollary we use the Cayley curve
`rotCurve ω s`, the rational rotation with Cayley vector `(s/2)ω`, which is in
`SO(3)` for every `s` (same formula as `Noperthedron.cayleyMatrix`).
-/

namespace SmallRupert

open scoped RealInnerProductSpace Matrix Topology
open Filter

/-- The first-order motion `(ω, τ)` moves every point of `V` strictly into
the standard-view shadow `proj_xy '' conv V` (LEMMAS.md L1 hypothesis
`ν(v) ∈ int T_S(Pv)`). -/
def FirstOrderInward (V : Finset ℝ³) (ω τ : ℝ³) : Prop :=
  ∀ v ∈ V, IsInwardAt (proj_xy '' convexHull ℝ (V : Set ℝ³)) (proj_xy v) (screenVel ω τ v)

/-- Only the boundary points `V_∂ = {v ∈ V : Pv ∈ ∂S}` matter. -/
theorem firstOrderInward_iff_frontier (V : Finset ℝ³) (ω τ : ℝ³) :
    FirstOrderInward V ω τ ↔
      ∀ v ∈ V, proj_xy v ∈ frontier (proj_xy '' convexHull ℝ (V : Set ℝ³)) →
        IsInwardAt (proj_xy '' convexHull ℝ (V : Set ℝ³)) (proj_xy v) (screenVel ω τ v) := by
  sorry

/-- **Lemma 1 (analytic core).** Points of a convex set moving with a
one-sided first derivative that is strictly inward at time `0` are eventually
in the interior, uniformly over a finite family. -/
theorem eventually_forall_mem_interior {ι : Type*} (s : Finset ι) {S : Set ℝ²}
    (hS : Convex ℝ S) (φ : ι → ℝ → ℝ²) (d : ι → ℝ²)
    (h0 : ∀ i ∈ s, φ i 0 ∈ closure S)
    (hderiv : ∀ i ∈ s, HasDerivWithinAt (φ i) (d i) (Set.Ici 0) 0)
    (hin : ∀ i ∈ s, IsInwardAt S (φ i 0) (d i)) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ i ∈ s, φ i t ∈ interior S := by
  sorry

/-- **Lemma 1.** If `(ω, τ)` is strictly inward, then for every curve of
matrices `R` with `R 0 = 1` and `R' 0 = [ω]×` (entrywise), and all small
`s > 0`, the shadow of `R_s K + sτ` lies in the interior of the shadow of `K`:
`P(R_s K + sτ) ⊆ int P(K)`. -/
theorem eventually_innerShadow_subset (V : Finset ℝ³) (ω τ : ℝ³)
    (h : FirstOrderInward V ω τ) (R : ℝ → Matrix (Fin 3) (Fin 3) ℝ) (hR0 : R 0 = 1)
    (hR : ∀ i j, HasDerivAt (fun s => R s i j) (crossMatrix ω i j) 0) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ),
      innerShadow (R s) (s • proj_xy τ) (convexHull ℝ (V : Set ℝ³)) ⊆
        interior (outerShadow 1 (convexHull ℝ (V : Set ℝ³))) := by
  sorry

/-- The Cayley rotation with Cayley vector `v` (the unit quaternion
proportional to `(1, v)`); the same matrix as `Noperthedron.cayleyMatrix`. -/
noncomputable def cayley (v : ℝ³) : Matrix (Fin 3) (Fin 3) ℝ :=
  let x := v 0
  let y := v 1
  let z := v 2
  let d := 1 + x ^ 2 + y ^ 2 + z ^ 2
  !![(1 + x ^ 2 - y ^ 2 - z ^ 2) / d, 2 * (x * y - z) / d, 2 * (x * z + y) / d;
     2 * (x * y + z) / d, (1 - x ^ 2 + y ^ 2 - z ^ 2) / d, 2 * (y * z - x) / d;
     2 * (x * z - y) / d, 2 * (y * z + x) / d, (1 - x ^ 2 - y ^ 2 + z ^ 2) / d]

/-- A rotation curve through the identity with angular velocity `ω`. -/
noncomputable def rotCurve (ω : ℝ³) (s : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  cayley ((s / 2) • ω)

theorem cayley_mem_SO3 (v : ℝ³) : cayley v ∈ SO3 := by
  sorry

theorem rotCurve_zero (ω : ℝ³) : rotCurve ω 0 = 1 := by
  sorry

theorem hasDerivAt_rotCurve (ω : ℝ³) (i j : Fin 3) :
    HasDerivAt (fun s => rotCurve ω s i j) (crossMatrix ω i j) 0 := by
  sorry

/-- **Lemma 1, Rupert form** (standard view): a strictly inward first-order
motion makes `V` Rupert, with `R₁ = rotCurve ω s`, offset `s • Pτ`, `R₂ = 1`
for small `s > 0`. -/
theorem isRupert_of_firstOrderInward (V : Finset ℝ³) (ω τ : ℝ³)
    (h : FirstOrderInward V ω τ) : IsRupert V := by
  sorry

/-- **Lemma 1, Rupert form** at the view of a rotation `Q`, i.e. view
direction `Qᵀ ez`. -/
theorem isRupert_of_firstOrderInward_image (V : Finset ℝ³) (Q : Matrix (Fin 3) (Fin 3) ℝ)
    (hQ : Q ∈ SO3) (ω τ : ℝ³) (h : FirstOrderInward (V.image Q.toEuclideanLin) ω τ) :
    IsRupert V :=
  isRupert_of_isRupert_image_rotation Q hQ V (isRupert_of_firstOrderInward _ ω τ h)

end SmallRupert

end
