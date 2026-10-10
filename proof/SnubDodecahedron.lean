module

public import SnubDodecahedron.Statement
public import SnubDodecahedron.IsNotRupert
public import Nopert

@[expose] public section

/-!
# The snub dodecahedron is not Rupert

The **snub dodecahedron** is the Archimedean solid with 92 faces (12
pentagons and 80 triangles) and 60 vertices. Its symmetry group is the
icosahedral rotation group I (order 60), without reflections, so it is
chiral: it comes in two mirror-image forms. This file is the entry point for
its result: it states exactly what Lean has checked about it.

## The solid

`snubDodecahedron` (in `SnubDodecahedron/Statement.lean`) is Wikipedia's
definition, with exact (irrational) coordinates. With φ the golden ratio and
ξ ≈ 0.94315 the real zero of x³ + 2x² − φ² (`snubXiW`, unique by
`snubXiW_unique`), the 60 vertices are the images of

    p = (φ² − φ²ξ, −φ³ + φξ + 2φξ², ξ)

under repeated multiplication by M₁ (the rotation by 2π/5 about (0, 1, φ))
and M₂ (the cyclic shift of coordinates). `SnubOrbit` is that set, literally,
and `mem_snubDodecahedron_iff` shows that the `Finset` `snubDodecahedron` is
the same set. `IsSnubDodecahedron V` says that the finite set `V` is the
image of these points under a similarity: an orthogonal map, a positive
scaling and a translation. The orthogonal map may be a reflection, so both
mirror images (chiralities) are included (`isSnubDodecahedron_mirror`). The
headline below is about every such `V`, so about the exact solid, of either
handedness, in any position, size and orientation.

## What `IsRupert` means

`IsRupert` (in `MainTheorem.lean`) says that two copies of the solid, each
rotated arbitrarily, can be placed so that the shadow of one (projected
straight down onto the plane, and slid sideways by any amount) lies strictly
inside the shadow of the other. That is the same as cutting a straight hole
through one copy that the other copy can pass through.

## A neighborhood of a rational model

The certificates are checked against fixed rational vertices
(`SnubDodecahedron/Vertices.lean`), not against the irrational solid. The
solution tables exclude every *`IModel`*: every polyhedron whose 60 vertices
are an orbit of the icosahedral rotation group I (in a frame where z is a
5-fold axis) within 6·10⁻¹⁶ of that rational model
(`SnubDodecahedron/IcoModel.lean`). The exact solid is one of them: the
kernel decides, by exact arithmetic in K = ℚ(√5, sin 72°) and a rational
enclosure of ξ, that a rotation and scaling of `snubDodecahedron` is an
`IModel` (`snubIModel`, `snubIModel_verts`). Similarities, reflections
included, preserve being Rupert (`isRupert_image_similarity`), which carries
the result to every snub dodecahedron.

## What Lean proved, and what it verified

The result has two parts, and they are trusted differently.

1. **A Lean proof** (`isNopert_of_certificatesValid` below): *if* the
   certificate data is valid, *then* every snub dodecahedron is a nopert: a
   genuine solid (its points are not all in one plane, which is proved
   outright) that is not Rupert. The data is a large table that splits up
   every way the solid could be rotated and records, for each piece, why no
   passage exists there. This part is checked by Lean's kernel in the usual
   way. It depends only on the standard axioms (`propext`,
   `Classical.choice`, `Quot.sound`) and on nothing about how the data was
   produced.

2. **A Lean verification** that the data is valid. The data is far too
   large for the kernel to check directly. Instead, the program
   `constructSnubDodecahedron` (in `constructSnubDodecahedron.lean`) reads
   the data, runs Lean's own validity checks on every row as compiled code,
   and, only if every check passes, uses part 1 to build a value of type
   `∀ V, IsSnubDodecahedron V → IsNopert V` and prints

       instantiated: IsNopert V for every snub dodecahedron V (none is Rupert)

   Trusting this part means trusting that Lean's compiler and runtime
   evaluate the check functions correctly. That is the same trust that
   `native_decide` asks for, although no `native_decide` is used. The check
   functions themselves are ordinary Lean definitions, and the kernel proves
   (part 1) that if they return true, the conclusion follows.

The program that *found* the data (the C++ search, on the `snubdodecahedron`
branch of nopert229) does not need to be trusted: a mistake there can only
produce data that fails the checks.

See `snub-dodecahedron.md` at the top of the repository for the data, how to
rerun the verification, and the times it takes.
-/

namespace SnubDodecahedron

open Noperts Noperts.Pipeline IcoZ
open scoped Matrix

/-- The certificate data is valid: there are four solution tables, one for
each of the four charts that together cover every rotation, each passing
Lean's validity check (which includes the shared tube tables), and the code
triangles cover the view domain (`WedgeCover.coverValid`, a fixed computation
too large for the kernel). This is the statement that
`constructSnubDodecahedron` establishes by computation. -/
def CertificatesValid : Prop :=
  (∃ table : CayleyAtlas.ChartIndex → AtlasProjectiveSolutionTree.Table,
    (∀ chart, (table chart).chart = chart) ∧ (∀ chart, (table chart).Valid)) ∧
  WedgeCover.coverValid = true

/-- If the certificate data is valid, no `IModel` is Rupert: no polyhedron
whose vertices are an I-orbit within 6·10⁻¹⁶ of the rational model. -/
theorem not_isRupert_iModel_of_certificatesValid (h : CertificatesValid) :
    ∀ P : IModel, ¬ IsRupert P.toC5.verts := by
  obtain ⟨⟨table, hchart, hvalid⟩, hcover⟩ := h
  exact fun P => not_rupert_of_valid_tables P table hchart hvalid hcover

/-- If the certificate data is valid, no snub dodecahedron is Rupert. -/
theorem not_isRupert_of_certificatesValid (h : CertificatesValid) :
    ∀ V : Finset ℝ³, IsSnubDodecahedron V → ¬ IsRupert V :=
  snubDodecahedron_not_rupert (not_isRupert_iModel_of_certificatesValid h)

/-! ### Not coplanar -/

/-- An affine image of a coplanar set is coplanar. -/
theorem coplanar_image {X : Set ℝ³} (g : ℝ³ →ᵃ[ℝ] ℝ³) (h : Coplanar ℝ X) :
    Coplanar ℝ (g '' X) := by
  rw [coplanar_iff_finrank_le_two] at h ⊢
  rw [← AffineMap.map_vectorSpan]
  exact (Submodule.finrank_map_le _ _).trans h

/-- The coordinates of Wikipedia's p are positive: p₀ = φ²(1 − ξ),
p₁ = φξ(1 − ξ²) (using ξ³ + 2ξ² = φ²) and p₂ = ξ, with 0 < ξ < 1. -/
theorem snubP_pos : 0 < snubP 0 ∧ 0 < snubP 1 ∧ 0 < snubP 2 := by
  have hxi := snubXiW_pos
  have hxi1 : snubXiW < 1 :=
    lt_of_le_of_lt snubXiW_bounds.2 (by norm_num [xiWHi, xiWLoNum])
  have hphi : 0 < goldenPhi := by
    unfold goldenPhi
    have := sqrt5_nonneg
    positivity
  have hcubic := snubXiW_cubic
  have h1 : snubP 1 = goldenPhi * snubXiW * (1 - snubXiW ^ 2) := by
    simp only [snubP]
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
    linear_combination goldenPhi * hcubic
  refine ⟨?_, ?_, ?_⟩
  · simp only [snubP, PiLp.toLp_apply, Matrix.cons_val_zero]
    nlinarith [mul_pos (pow_pos hphi 2) (sub_pos.mpr hxi1)]
  · rw [h1]
    have : 0 < 1 - snubXiW ^ 2 := by nlinarith
    positivity
  · simpa [snubP] using hxi

/-- A diagonal element of the group (times 20). -/
def diagM3 (a b c : Int) : M3 :=
  let z : IcoZ := ⟨0, 0, 0, 0⟩
  ⟨⟨a, 0, 0, 0⟩, z, z, z, ⟨b, 0, 0, 0⟩, z, z, z, ⟨c, 0, 0, 0⟩⟩

theorem wikiEntry_55 : wikiEntry 55 = diagM3 20 (-20) (-20) := by decide +kernel
theorem wikiEntry_35 : wikiEntry 35 = diagM3 (-20) 20 (-20) := by decide +kernel
theorem wikiEntry_31 : wikiEntry 31 = diagM3 (-20) (-20) 20 := by decide +kernel

theorem wiki_apply_diag {n : Nat} {a b c : Int} (h : wikiEntry n = diagM3 a b c) (v : ℝ³) (i : Fin 3) :
    (wiki n).toEuclideanLin v i = ![(a : ℝ) / 20 * v 0, (b : ℝ) / 20 * v 1, (c : ℝ) / 20 * v 2] i := by
  fin_cases i <;>
    simp [wiki, h, diagM3, M3.toMatrix, M3.entry, IcoZ.val, Matrix.toLpLin_apply, Matrix.mulVec,
      dotProduct, Fin.sum_univ_three] <;>
    left <;> ring

/-- Wikipedia's points are not all in one plane: p and its images under the
three half-turns about the coordinate axes (elements 55, 35 and 31 of the
group) span a tetrahedron of volume 16 p₀ p₁ p₂ / 6 ≠ 0. -/
theorem not_coplanar_snubDodecahedron : ¬ Coplanar ℝ (snubDodecahedron : Set ℝ³) := by
  obtain ⟨h0, h1, h2⟩ := snubP_pos
  have hmem : ∀ n, n < 60 → (wiki n).toEuclideanLin snubP ∈ (snubDodecahedron : Set ℝ³) :=
    fun n hn => by
      simp only [snubDodecahedron, Finset.coe_image, Finset.coe_range]
      exact ⟨n, hn, rfl⟩
  have hp : snubP ∈ (snubDodecahedron : Set ℝ³) := (mem_snubDodecahedron_iff _).mpr SnubOrbit.base
  refine not_coplanar_set_of_det3_ne_zero hp (hmem 55 (by norm_num)) (hmem 35 (by norm_num))
    (hmem 31 (by norm_num)) ?_
  have e55 := wiki_apply_diag wikiEntry_55 snubP
  have e35 := wiki_apply_diag wikiEntry_35 snubP
  have e31 := wiki_apply_diag wikiEntry_31 snubP
  simp only [det3, Matrix.det_fin_three, PiLp.sub_apply, e55, e35, e31]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons,
    Matrix.tail_cons, Matrix.head_fin_const]
  have : 0 < snubP 0 * snubP 1 * snubP 2 := by positivity
  push_cast
  nlinarith

/-- Every snub dodecahedron is a genuine solid: its points are not all in one
plane. (A similarity is invertible, and an affine image of a coplanar set is
coplanar.) -/
theorem not_coplanar_of_isSnubDodecahedron {V : Finset ℝ³}
    (hV : IsSnubDodecahedron V) : ¬ Coplanar ℝ (V : Set ℝ³) := by
  obtain ⟨c, s, M, hs, hM, hVeq⟩ := hV
  have hMM : Mᵀ * M = 1 := (Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ).mp hM
  -- The inverse similarity x ↦ s⁻¹ Mᵀ (x − c).
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
  exact not_coplanar_snubDodecahedron himg

/-! ### The headline -/

/-- **Every snub dodecahedron is a nopert**, given valid certificate data:
it is a genuine solid (`not_coplanar_of_isSnubDodecahedron`, a Lean proof)
and it is not Rupert (`not_isRupert_of_certificatesValid`; the data's
validity is what `constructSnubDodecahedron` verifies). `IsSnubDodecahedron`
covers both mirror images. `IsNopert` is defined in `Nopert.lean`. -/
theorem isNopert_of_certificatesValid (h : CertificatesValid) :
    ∀ V : Finset ℝ³, IsSnubDodecahedron V → IsNopert V :=
  fun V hV => ⟨not_coplanar_of_isSnubDodecahedron hV,
    not_isRupert_of_certificatesValid h V hV⟩

/-- Wikipedia's snub dodecahedron is a nopert, given valid certificate
data. -/
theorem isNopert_snubDodecahedron_of_certificatesValid (h : CertificatesValid) :
    IsNopert snubDodecahedron :=
  isNopert_of_certificatesValid h snubDodecahedron isSnubDodecahedron_snubDodecahedron

/-- The other chirality: the mirror image of Wikipedia's snub dodecahedron
(through the origin) is a snub dodecahedron too, so the headline covers it. -/
theorem isSnubDodecahedron_mirror :
    IsSnubDodecahedron (snubDodecahedron.image fun x => -x) := by
  refine ⟨0, 1, -1, one_pos, ?_, ?_⟩
  · rw [Matrix.mem_orthogonalGroup_iff']
    simp
  · congr 1
    funext x
    simp

end SnubDodecahedron

end
