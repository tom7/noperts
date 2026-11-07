module

public import SeptopertM18.IsNotRupert
public import Nopert

@[expose] public section

/-!
# The SeptopertM18 is not Rupert

The **SeptopertM18** is the convex polyhedron whose vertices are the seven points
`septopert` below. This file is the entry point for its result: it states
exactly what Lean has checked about it.

## What `IsRupert` means

`IsRupert` (in `MainTheorem.lean`) says that two copies of the solid, each
rotated arbitrarily, can be placed so that the shadow of one (projected
straight down onto the plane, and slid sideways by any amount) lies strictly
inside the shadow of the other. That is the same as cutting a straight hole
through one copy that the other copy can pass through.

## What Lean proved, and what it verified

The result has two parts, and they are trusted differently.

1. **A Lean proof** (`isNopert_of_certificatesValid` below): *if* the
   certificate data is valid, *then* the SeptopertM18 is a nopert: a genuine
   solid (its points are not all in one plane, which is proved outright)
   that is not Rupert. The data is a large table that splits up every way
   the solid could be rotated and records, for each piece, why no passage
   exists there. This part is checked by Lean's kernel in the usual way.
   It depends only on the standard axioms (`propext`, `Classical.choice`,
   `Quot.sound`) and on nothing about how the data was produced.

2. **A Lean verification** that the data is valid. The data is about 850
   thousand table rows (45 MB) and two cap certificates (1.1 MB), too much for
   the kernel to check directly.
   Instead, the program `constructSeptopertM18` (in `constructSeptopertM18.lean`)
   reads the data, runs Lean's own validity checks on every row as compiled
   code, and, only if every check passes, uses part 1 to build a value of type
   `IsNopert septopert` and prints

       instantiated: IsNopert septopert (the SeptopertM18 is a Nopert: not Rupert)

   Trusting this part means trusting that Lean's compiler and runtime evaluate
   the check functions correctly. That is the same trust that `native_decide`
   asks for, although no `native_decide` is used. The check functions
   themselves are ordinary Lean definitions, and the kernel proves (part 1)
   that if they return true, the conclusion follows.

The program that *found* the data (the C++ in `search/septopert/`) does not
need to be trusted at all: a mistake there can only produce data that fails
the checks.
That said, it does its own checking, and might be considered its own independent
verification of the result.

See `septopert.md` at the top of the repository for how to obtain the data,
rerun the verification, and the times it takes.
-/

namespace SeptopertM18

open Noperts Noperts.Pipeline

/-- The seven vertices of the SeptopertM18. They are exact rational numbers; written
over the common denominator 32 they are integers (see `septopert.md`). -/
noncomputable def septopert : Finset ℝ³ :=
  {!₂[-9/16, 9/32, 9/32],
   !₂[9/32, -9/16, 9/32],
   !₂[9/32, 9/32, -9/16],
   !₂[17/32, 3/32, 3/32],
   !₂[3/32, 17/32, 3/32],
   !₂[3/32, 3/32, 17/32],
   !₂[-9/32, -9/32, -9/32]}

/-- The certificate data is valid: there are four solution tables, one for each
of the four charts that together cover every rotation, each passing Lean's
validity check, the cap certificate (which covers the small region the
tables leave out, around the solid's mirror directions) passes its check, and
the arc cap certificate (which covers the other region the tables leave out,
small rotations at views near the arc from (2, 2, -1) towards a mirror direction)
passes its check. This is the statement that `constructSeptopertM18` establishes by computation. -/
def CertificatesValid : Prop :=
  ∃ table : CayleyAtlas.ChartIndex → SolutionTree.Table,
    (∀ chart, (table chart).chart = chart) ∧
    (∀ chart, (table chart).Valid) ∧
    SolutionTree.CapOk ∧
    SolutionTree.ArcOk

/-- `septopert` is the vertex set the proof works with (`SeptopertM18.verts`). -/
theorem septopert_eq_verts : septopert = verts := by
  have h0 : toR3 (vertexQ 0) = !₂[-9/16, 9/32, 9/32] := by
    ext j; fin_cases j <;> simp [toR3, vertexQ]
  have h1 : toR3 (vertexQ 1) = !₂[9/32, -9/16, 9/32] := by
    ext j; fin_cases j <;> simp [toR3, vertexQ]
  have h2 : toR3 (vertexQ 2) = !₂[9/32, 9/32, -9/16] := by
    ext j; fin_cases j <;> simp [toR3, vertexQ]
  have h3 : toR3 (vertexQ 3) = !₂[17/32, 3/32, 3/32] := by
    ext j; fin_cases j <;> simp [toR3, vertexQ]
  have h4 : toR3 (vertexQ 4) = !₂[3/32, 17/32, 3/32] := by
    ext j; fin_cases j <;> simp [toR3, vertexQ]
  have h5 : toR3 (vertexQ 5) = !₂[3/32, 3/32, 17/32] := by
    ext j; fin_cases j <;> simp [toR3, vertexQ]
  have h6 : toR3 (vertexQ 6) =
      !₂[-9/32, -9/32, -9/32] := by
    ext j; fin_cases j <;> simp [toR3, vertexQ]
  have huniv : (Finset.univ : Finset (Fin 7)) = {0, 1, 2, 3, 4, 5, 6} := by decide
  unfold septopert verts
  rw [huniv]
  simp only [Finset.image_insert, Finset.image_singleton, h0, h1, h2, h3, h4, h5, h6]

/-- If the certificate data is valid, the SeptopertM18 is not Rupert. -/
theorem not_isRupert_of_certificatesValid (h : CertificatesValid) :
    ¬ IsRupert septopert := by
  obtain ⟨table, hchart, hvalid, hcap, harc⟩ := h
  rw [septopert_eq_verts]
  exact not_rupert_of_valid_tables table hchart hvalid hcap harc

/-- The SeptopertM18 is a genuine solid: its points are not all in one plane.
(Proved outright: vertices 0, 1, 2 and 6 span a tetrahedron.) -/
theorem not_coplanar_septopert : ¬ Coplanar ℝ (septopert : Set ℝ³) := by
  refine not_coplanar_of_det3_ne_zero
    (a := !₂[-9/16, 9/32, 9/32])
    (b := !₂[9/32, -9/16, 9/32])
    (c := !₂[9/32, 9/32, -9/16])
    (d := !₂[-9/32, -9/32, -9/32])
    (by simp [septopert]) (by simp [septopert]) (by simp [septopert]) (by simp [septopert]) ?_
  simp [det3, Matrix.det_fin_three]
  norm_num

/-- **The SeptopertM18 is a nopert**, given valid certificate data: it is a
genuine solid (`not_coplanar_septopert`, a Lean proof) and it is not Rupert
(`not_isRupert_of_certificatesValid`; the data's validity is what
`constructSeptopertM18` verifies). `IsNopert` is defined in `Nopert.lean`. -/
theorem isNopert_of_certificatesValid (h : CertificatesValid) : IsNopert septopert :=
  ⟨not_coplanar_septopert, not_isRupert_of_certificatesValid h⟩

end SeptopertM18

end
