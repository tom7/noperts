module

public import DeltoidalHexecontahedron.Ties
public import DeltoidalHexecontahedron.IsNotRupert
public import Nopert

@[expose] public section

/-!
# The deltoidal hexecontahedron is not Rupert

The **deltoidal hexecontahedron** is the Catalan solid with 60 kite-shaped
faces and 62 vertices (the dual of the rhombicosidodecahedron). This file is
the entry point for its result: it states exactly what Lean has checked about
it.

## The solid

`DH.deltoidalHexecontahedron` (in `DeltoidalHexecontahedron/Statement.lean`)
is David McCooey's vertex set, with exact (irrational) coordinates: the cyclic
permutations, with all sign changes, of the five points

    (0, 0, √5), (0, C₁, C₇), (C₃, 0, C₆), (C₀, C₂, C₅), (C₄, C₄, C₄),

where C₀ = (5 − √5)/4, C₁ = (15 + √5)/22, C₂ = √5/2, C₃ = (5 + √5)/6,
C₄ = (5 + 4√5)/11, C₅ = (5 + √5)/4, C₆ = (5 + 3√5)/6 and
C₇ = (25 + 9√5)/22. `DH.IsDeltoidalHexecontahedron V` says that the finite set
`V` is the image of these points under a similarity: an orthogonal map
(possibly a reflection), a positive scaling and a translation. The headline
below is about every such `V`, so about the exact solid in any position, size
and orientation. (`mcCooey` is McCooey's set itself, as a `Finset`.)

## What `IsRupert` means

`IsRupert` (in `MainTheorem.lean`) says that two copies of the solid,
each rotated arbitrarily, can be placed so that the shadow of one
(projected straight down onto the plane, and slid sideways by any
amount) lies strictly inside the shadow of the other. That is the same
as cutting a proper straight hole through one copy that the other copy
can pass through.

## Why the proof needs the exact solid

The deltoidal hexecontahedron is only just not Rupert: it has poses whose
clearance is exactly 0 (*ties*), and moving its twelve 5-fold vertices outward
by 0.1% gives a Rupert solid (a passage checked numerically to 50 digits by
`dh-boundary.py` in the search's repository, not by Lean). So, unlike for the
Septopert, no statement about all solids near a rational model can be true.
The proof therefore splits in two:

- the solution tables exclude every centrally symmetric solid with
  icosahedral symmetry whose vertices are within 6·10⁻¹⁶ of a rational model,
  *provided* certain exact claims hold for it near the ties (the *caps* and
  *ties* claims, `AtlasProjectiveSolutionTree.ExactClaims`);
- for the exact solid, the kernel checks by exact computation over
  K = ℚ(√5, sin 72°) that it is such a solid (`DH.dhIModel`: the frame, the 70
  vertex slots, the orbits, the central symmetry and the closeness to the
  rational model are all decided by `decide +kernel`), and the cap and tie
  certificates prove the exact claims (`DH.capsHold_of_certs`,
  `DH.tiesHold_of_certs`).

## What Lean proved, and what it verified

The result has two parts, and they are trusted differently.

1. **A Lean proof** (`isNopert_of_certificatesValid` below): *if* the
   certificate data is valid, *then* every deltoidal hexecontahedron is a
   nopert: a genuine solid (its points are not all in one plane, which is
   proved outright) that is not Rupert. The data is a large table that splits
   up every way the solid could be rotated and records, for each piece, why no
   passage exists there, plus the cap and tie certificates near the ties.
   This part is checked by Lean's kernel in the usual way. It depends only on
   the standard axioms (`propext`, `Classical.choice`, `Quot.sound`) and on
   nothing about how the data was produced.

2. **A Lean verification** that the data is valid. The data is about 20 GB
   (chart 0's table alone has 36.2 million rows), far too much for the kernel
   to check directly. Instead, the program `constructDeltoidalHexecontahedron`
   (in `constructDeltoidalHexecontahedron.lean`) reads the data, runs Lean's
   own validity checks on every row and certificate as compiled code, and,
   only if every check passes, uses part 1 to build a value of type
   `∀ V, DH.IsDeltoidalHexecontahedron V → IsNopert V` and prints

       instantiated: IsNopert V for every deltoidal hexecontahedron V (none is Rupert)

   Trusting this part means trusting that Lean's compiler and runtime evaluate
   the check functions correctly. That is the same trust that `native_decide`
   asks for, although no `native_decide` is used. The check functions
   themselves are ordinary Lean definitions, and the kernel proves (part 1)
   that if they return true, the conclusion follows.

The program that *found* the data (the C++ search, in `search/dh`) does
not need to be trusted: a mistake there can only produce data that
fails the checks.

See `deltoidal-hexecontahedron.md` at the top of the repository for the data,
how to rerun the verification, and the times it takes.
-/

namespace DeltoidalHexecontahedron

open Noperts Noperts.Pipeline
open scoped Matrix

/-- The certificate data is valid: there are four solution tables, one for
each of the four charts that together cover every rotation, each passing
Lean's validity check (which includes the shared tube tables); the code
triangles cover the view domain (`WedgeCover.coverValid`, a fixed computation
too large for the kernel); and there are cap and tie certificates that pass
their checks. This is the statement that `constructDeltoidalHexecontahedron`
establishes by computation. -/
def CertificatesValid : Prop :=
  (∃ table : CayleyAtlas.ChartIndex → AtlasProjectiveSolutionTree.Table,
    (∀ chart, (table chart).chart = chart) ∧ (∀ chart, (table chart).Valid)) ∧
  WedgeCover.coverValid = true ∧
  (∃ caps : Array Cap.CapCert, DH.capsCheck caps = true) ∧
  (∃ ties : DH.TieCerts, DH.tiesCheck ties = true)

/-- If the certificate data is valid, no deltoidal hexecontahedron is Rupert. -/
theorem not_isRupert_of_certificatesValid (h : CertificatesValid) :
    ∀ V : Finset ℝ³, DH.IsDeltoidalHexecontahedron V → ¬ IsRupert V := by
  obtain ⟨⟨table, hchart, hvalid⟩, hcover, ⟨caps, hcaps⟩, ⟨ties, hties⟩⟩ := h
  exact DH.deltoidalHexecontahedron_not_rupert_of_checks
    (fun P hsym hclaims => not_rupert_of_valid_tables P hsym table hchart hvalid hcover hclaims)
    caps hcaps ties hties

/-! ### Not coplanar -/

/-- An affine image of a coplanar set is coplanar. -/
theorem coplanar_image {X : Set ℝ³} (g : ℝ³ →ᵃ[ℝ] ℝ³) (h : Coplanar ℝ X) :
    Coplanar ℝ (g '' X) := by
  rw [coplanar_iff_finrank_le_two] at h ⊢
  rw [← AffineMap.map_vectorSpan]
  exact (Submodule.finrank_map_le _ _).trans h

/-- McCooey's points are not all in one plane: (0, 0, √5), (0, √5, 0),
(√5, 0, 0) and (0, 0, −√5) span a tetrahedron. -/
theorem not_coplanar_deltoidalHexecontahedron :
    ¬ Coplanar ℝ DH.deltoidalHexecontahedron := by
  have h5 : (0 : ℝ) < √5 := by positivity
  have h55 : √5 * √5 = 5 := Real.mul_self_sqrt (by norm_num)
  have h42 : Nat.testBit 4 2 = true := by decide
  refine not_coplanar_set_of_det3_ne_zero
    (a := DH.mcPoint 0 0 0) (b := DH.mcPoint 0 0 1) (c := DH.mcPoint 0 0 2)
    (d := DH.mcPoint 0 4 0) ⟨0, 0, 0, rfl⟩ ⟨0, 0, 1, rfl⟩ ⟨0, 0, 2, rfl⟩ ⟨0, 4, 0, rfl⟩ ?_
  simp [det3, Matrix.det_fin_three, DH.mcPoint, DH.mcGen, DH.signOf, DH.C8, h42]
  nlinarith

/-- Every deltoidal hexecontahedron is a genuine solid: its points are not all
in one plane. (A similarity is invertible, and an affine image of a coplanar
set is coplanar.) -/
theorem not_coplanar_of_isDeltoidalHexecontahedron {V : Finset ℝ³}
    (hV : DH.IsDeltoidalHexecontahedron V) : ¬ Coplanar ℝ (V : Set ℝ³) := by
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
  rw [hVeq] at hcop
  have himg := coplanar_image g hcop
  rw [Set.image_image, show (fun x => g (c + s • M.toEuclideanLin x)) = id from funext hg,
    Set.image_id] at himg
  exact not_coplanar_deltoidalHexecontahedron himg

/-! ### The headline -/

/-- **Every deltoidal hexecontahedron is a nopert**, given valid certificate
data: it is a genuine solid (`not_coplanar_of_isDeltoidalHexecontahedron`, a
Lean proof) and it is not Rupert (`not_isRupert_of_certificatesValid`; the
data's validity is what `constructDeltoidalHexecontahedron` verifies).
`IsNopert` is defined in `Nopert.lean`. -/
theorem isNopert_of_certificatesValid (h : CertificatesValid) :
    ∀ V : Finset ℝ³, DH.IsDeltoidalHexecontahedron V → IsNopert V :=
  fun V hV => ⟨not_coplanar_of_isDeltoidalHexecontahedron hV,
    not_isRupert_of_certificatesValid h V hV⟩

/-- McCooey's 62 points (`DH.deltoidalHexecontahedron`) as a `Finset`. -/
noncomputable def mcCooey : Finset ℝ³ :=
  Finset.univ.image fun t : Fin 5 × Fin 8 × Fin 3 => DH.mcPoint t.1 t.2.1 t.2.2

theorem isDeltoidalHexecontahedron_mcCooey : DH.IsDeltoidalHexecontahedron mcCooey := by
  refine ⟨0, 1, 1, one_pos, one_mem _, ?_⟩
  ext v
  simp [mcCooey, DH.deltoidalHexecontahedron, eq_comm]

/-- McCooey's deltoidal hexecontahedron is a nopert, given valid certificate
data. -/
theorem isNopert_mcCooey_of_certificatesValid (h : CertificatesValid) : IsNopert mcCooey :=
  isNopert_of_certificatesValid h mcCooey isDeltoidalHexecontahedron_mcCooey

end DeltoidalHexecontahedron

end
