module

public import SnubCube.Statement
public import Pipeline.OctaIsNotRupert
public import Nopert

@[expose] public section

/-!
# The snub cube is not Rupert

The **snub cube** is the Archimedean solid with 38 faces (6 squares and 32
triangles) and 24 vertices. Its symmetry group is the octahedral rotation
group O (order 24), without reflections, so it is chiral: it comes in two
mirror-image forms. This file is the entry point for its result: it states
exactly what Lean has checked about it.

## The solid

`snubCube` (in `SnubCube/Statement.lean`) is Wikipedia's definition, with
exact (irrational) coordinates: with t the tribonacci constant (the real root
of t³ = t² + t + 1, `tribonacci`), the even permutations of (±1, ±1/t, ±t)
with an even number of plus signs, together with the odd permutations with an
odd number of plus signs. `IsSnubCube V` says that the finite set `V` is the
image of these points under a similarity: an orthogonal map (possibly a
reflection), a positive scaling and a translation. So the headline covers
both chiralities, in any position, size and orientation.

## What `IsRupert` means

`IsRupert` (in `MainTheorem.lean`) says that two copies of the solid, each
rotated arbitrarily, can be placed so that the shadow of one (projected
straight down onto the plane, and slid sideways by any amount) lies strictly
inside the shadow of the other: a straight hole through one copy that the
other can pass through.

## The proof

The certificates are checked against fixed rational vertices
(`SnubCube/ModelData.lean`), not the irrational solid: the solution tables
exclude every *`OModel`* (every polyhedron whose 24 vertices are an orbit of
O within 6·10⁻¹⁶ of the rational model) whose hull satisfies the cap claims
(`OctaCaps.CapsHold`). The exact snub cube is an `OModel` (`snubOModel`,
kernel checked), and the cap claims hold for it (`capsHold_snubOModel`): the
snub cube has a view u* where the first-order margin vanishes, with an exact
tie (a family of poses with clearance exactly 0) running from it; the cap and
tie-tube certificate (`search/sc/sccapcert.cc`, checked by `KCert.check` over
the exact field ℚ(t)) proves that no pose near them is Rupert.

## What Lean proved, and what it verified

1. **A Lean proof** (`isNopert_of_certificatesValid` below): *if* the
   certificate data is valid (`CertificatesValid`: the four chart tables,
   the view cover and the cap certificate), *then* every snub cube is a
   nopert: a genuine solid (not coplanar, proved outright) that is not
   Rupert. It depends only on the standard axioms.

2. **A Lean verification** that the data is valid: `constructSnubCube`
   reads the data, runs Lean's own checks as compiled code, and only if all
   pass uses part 1 to build a value of type `∀ V, IsSnubCube V → IsNopert V`.
   Trusting this part means trusting Lean's compiler and runtime (the trust
   `native_decide` asks for; no `native_decide` is used).

The programs that *found* the data (`search/sc`) need not be trusted: a
mistake there can only produce data that fails the checks. See
`snub-cube.md` at the top of the repository.
-/

namespace SnubCube

open Noperts Noperts.Pipeline Noperts.Pipeline.KCap
open scoped Matrix

/-- The certificate data is valid: four solution tables, one per chart, each
passing Lean's validity check (with the shared tube tables), the code
triangles cover the view domain, and a cap certificate with the template's
data passes `KCert.check`. This is what `constructSnubCube` establishes by
computation. -/
def CertificatesValid : Prop :=
  (∃ table : CayleyAtlas.ChartIndex → OctaSolutionTree.Table,
    (∀ chart, (table chart).chart = chart) ∧ (∀ chart, (table chart).Valid)) ∧
  octaCoverValid = true ∧
  ∃ c : KCert TribQ, c.check = true ∧ certMatches c = true

/-- If the certificate data is valid, the exact model is not Rupert. -/
theorem not_isRupert_snubOModel_of_certificatesValid (h : CertificatesValid) :
    ¬ IsRupert snubOModel.toC4.verts := by
  obtain ⟨⟨table, hchart, hvalid⟩, hcover, c, hc, hm⟩ := h
  exact OctaSolutionTree.not_rupert_of_valid_tables snubOModel table hchart hvalid hcover
    (capsHold_snubOModel c hc hm)

/-- If the certificate data is valid, no snub cube is Rupert. -/
theorem not_isRupert_of_certificatesValid (h : CertificatesValid) :
    ∀ V : Finset ℝ³, IsSnubCube V → ¬ IsRupert V :=
  snubCube_not_rupert (not_isRupert_snubOModel_of_certificatesValid h)

/-! ### Not coplanar -/

theorem coplanar_image {X : Set ℝ³} (g : ℝ³ →ᵃ[ℝ] ℝ³) (h : Coplanar ℝ X) :
    Coplanar ℝ (g '' X) := by
  rw [coplanar_iff_finrank_le_two] at h ⊢
  rw [← AffineMap.map_vectorSpan]
  exact (Submodule.finrank_map_le _ _).trans h

theorem wikiPoint_mem {ps : Equiv.Perm (Fin 3) × (Fin 3 → Bool)} (h : ps ∈ wikiIndex) :
    wikiPoint ps ∈ (snubCube : Set ℝ³) := by
  simp only [snubCube, Finset.coe_image]
  exact ⟨ps, h, rfl⟩

/-- Wikipedia's points are not all in one plane: (−1, −1/t, −t), (1, 1/t, −t),
(1, −1/t, t) and (−1, 1/t, t) span a tetrahedron (determinant −16 · (1/t) · t). -/
theorem not_coplanar_snubCube : ¬ Coplanar ℝ (snubCube : Set ℝ³) := by
  have ht := tribonacci_pos
  let p : (Fin 3 → Bool) → Equiv.Perm (Fin 3) × (Fin 3 → Bool) := fun s => (1, s)
  have h1 : p ![false, false, false] ∈ wikiIndex := by decide
  have h2 : p ![true, true, false] ∈ wikiIndex := by decide
  have h3 : p ![true, false, true] ∈ wikiIndex := by decide
  have h4 : p ![false, true, true] ∈ wikiIndex := by decide
  refine not_coplanar_set_of_det3_ne_zero (wikiPoint_mem h1) (wikiPoint_mem h2) (wikiPoint_mem h3)
    (wikiPoint_mem h4) ?_
  simp only [det3, Matrix.det_fin_three, wikiPoint, wikiBase, p]
  simp [Matrix.of_apply]
  field_simp
  ring_nf
  positivity

theorem not_coplanar_of_isSnubCube {V : Finset ℝ³} (hV : IsSnubCube V) : ¬ Coplanar ℝ (V : Set ℝ³) := by
  obtain ⟨c, s, M, hs, hM, hVeq⟩ := hV
  have hMM : Mᵀ * M = 1 := (Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ).mp hM
  let g : ℝ³ →ᵃ[ℝ] ℝ³ :=
    (s⁻¹ • (Mᵀ.toEuclideanLin : ℝ³ →ₗ[ℝ] ℝ³)).toAffineMap +
      AffineMap.const ℝ ℝ³ (-(s⁻¹ • Mᵀ.toEuclideanLin c))
  have hg : ∀ x, g (c + s • M.toEuclideanLin x) = x := by
    intro x
    have hx : Mᵀ.toEuclideanLin (M.toEuclideanLin x) = x := by
      rw [← IModel.toEuclideanLin_mul, hMM]
      simp
    have hgy : ∀ y, g y = s⁻¹ • Mᵀ.toEuclideanLin y + -(s⁻¹ • Mᵀ.toEuclideanLin c) :=
      fun y => rfl
    rw [hgy, map_add, map_smul, hx, smul_add, smul_smul, inv_mul_cancel₀ hs.ne', one_smul]
    abel
  intro hcop
  rw [hVeq, Finset.coe_image] at hcop
  have himg := coplanar_image g hcop
  rw [Set.image_image, show (fun x => g (c + s • M.toEuclideanLin x)) = id from funext hg,
    Set.image_id] at himg
  exact not_coplanar_snubCube himg

/-! ### The headline -/

/-- **Every snub cube is a nopert**, given valid certificate data: it is a
genuine solid (`not_coplanar_of_isSnubCube`) and it is not Rupert
(`not_isRupert_of_certificatesValid`). `IsSnubCube` covers both mirror
images. -/
theorem isNopert_of_certificatesValid (h : CertificatesValid) :
    ∀ V : Finset ℝ³, IsSnubCube V → IsNopert V :=
  fun V hV => ⟨not_coplanar_of_isSnubCube hV, not_isRupert_of_certificatesValid h V hV⟩

/-- Wikipedia's snub cube is a nopert, given valid certificate data. -/
theorem isNopert_snubCube_of_certificatesValid (h : CertificatesValid) : IsNopert snubCube :=
  isNopert_of_certificatesValid h snubCube isSnubCube_snubCube

end SnubCube

end
