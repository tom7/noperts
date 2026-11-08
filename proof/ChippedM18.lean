module

public import ChippedM18.IsNotRupert
public import Nopert

@[expose] public section

/-!
# The Chipped M18 is not Rupert

The **Chipped M18** is the SeptopertM18 with its three vertices (-18,9,9)/32 (and C3
images) cut off by the planes (-1,5,5).x = 209/64 (and C3 images): the convex
polyhedron whose vertices are the 19 points `chippedM18` below. It has C3v
symmetry and six acute dihedral edges of 81.95 degrees. This file is the entry point for its result: it states
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
   certificate data is valid, *then* the ChippedM18 is a nopert: a genuine
   solid (its points are not all in one plane, which is proved outright)
   that is not Rupert. The data is a large table that splits up every way
   the solid could be rotated and records, for each piece, why no passage
   exists there. This part is checked by Lean's kernel in the usual way.
   It depends only on the standard axioms (`propext`, `Classical.choice`,
   `Quot.sound`) and on nothing about how the data was produced.

2. **A Lean verification** that the data is valid. The data is about 850
   thousand table rows (45 MB) and two cap certificates (1.1 MB), too much for
   the kernel to check directly.
   Instead, the program `constructChippedM18` (in `constructChippedM18.lean`)
   reads the data, runs Lean's own validity checks on every row as compiled
   code, and, only if every check passes, uses part 1 to build a value of type
   `IsNopert chippedM18` and prints

       instantiated: IsNopert chippedM18 (the Chipped M18 is a Nopert: not Rupert)

   Trusting this part means trusting that Lean's compiler and runtime evaluate
   the check functions correctly. That is the same trust that `native_decide`
   asks for, although no `native_decide` is used. The check functions
   themselves are ordinary Lean definitions, and the kernel proves (part 1)
   that if they return true, the conclusion follows.

The program that *found* the data (the C++ in `search/chipped-m18/`) does not
need to be trusted at all: a mistake there can only produce data that fails
the checks.
That said, it does its own checking, and might be considered its own independent
verification of the result.

See `chipped-m18.md` at the top of the repository for how to obtain the data,
rerun the verification, and the times it takes.
-/

namespace ChippedM18

open Noperts Noperts.Pipeline

/-- The 19 vertices of the ChippedM18. They are exact rational numbers; written
over a common denominator they are integers (see `chipped-m18.md`). -/
noncomputable def chippedM18 : Finset ℝ³ :=
  {!₂[-107/192, 13/48, 13/48],
   !₂[-209/384, 101/384, 9/32],
   !₂[-209/384, 9/32, 101/384],
   !₂[-249/704, 39/176, 127/352],
   !₂[-249/704, 127/352, 39/176],
   !₂[-9/32, -9/32, -9/32],
   !₂[3/32, 3/32, 17/32],
   !₂[3/32, 17/32, 3/32],
   !₂[39/176, -249/704, 127/352],
   !₂[39/176, 127/352, -249/704],
   !₂[101/384, -209/384, 9/32],
   !₂[101/384, 9/32, -209/384],
   !₂[13/48, -107/192, 13/48],
   !₂[13/48, 13/48, -107/192],
   !₂[9/32, -209/384, 101/384],
   !₂[9/32, 101/384, -209/384],
   !₂[127/352, -249/704, 39/176],
   !₂[127/352, 39/176, -249/704],
   !₂[17/32, 3/32, 3/32]}

/-- The certificate data is valid: there are four solution tables, one for each
of the four charts that together cover every rotation, each passing Lean's
validity check, the cap certificate (which covers the small region the
tables leave out, around the solid's mirror directions) passes its check, and
the arc cap certificate (which covers the other region the tables leave out,
small rotations at views near the arc from (2, 2, -1) towards a mirror direction)
passes its check. This is the statement that `constructChippedM18` establishes by computation. -/
def CertificatesValid : Prop :=
  ∃ table : CayleyAtlas.ChartIndex → SolutionTree.Table,
    (∀ chart, (table chart).chart = chart) ∧
    (∀ chart, (table chart).Valid) ∧
    SolutionTree.CapOk ∧
    SolutionTree.ArcOk

/-- `chippedM18` is the vertex set the proof works with (`ChippedM18.verts`). -/
theorem chippedM18_eq_verts : chippedM18 = verts := by
  have h0 : toR3 (vertexQ 0) = !₂[-107/192, 13/48, 13/48] := by
    ext j; fin_cases j <;> simp [toR3, vertexQ]
  have h1 : toR3 (vertexQ 1) = !₂[-209/384, 101/384, 9/32] := by
    ext j; fin_cases j <;> simp [toR3, vertexQ]
  have h2 : toR3 (vertexQ 2) = !₂[-209/384, 9/32, 101/384] := by
    ext j; fin_cases j <;> simp [toR3, vertexQ]
  have h3 : toR3 (vertexQ 3) = !₂[-249/704, 39/176, 127/352] := by
    ext j; fin_cases j <;> simp [toR3, vertexQ]
  have h4 : toR3 (vertexQ 4) = !₂[-249/704, 127/352, 39/176] := by
    ext j; fin_cases j <;> simp [toR3, vertexQ]
  have h5 : toR3 (vertexQ 5) = !₂[-9/32, -9/32, -9/32] := by
    ext j; fin_cases j <;> simp [toR3, vertexQ]
  have h6 : toR3 (vertexQ 6) = !₂[3/32, 3/32, 17/32] := by
    ext j; fin_cases j <;> simp [toR3, vertexQ]
  have h7 : toR3 (vertexQ 7) = !₂[3/32, 17/32, 3/32] := by
    ext j; fin_cases j <;> simp [toR3, vertexQ]
  have h8 : toR3 (vertexQ 8) = !₂[39/176, -249/704, 127/352] := by
    ext j; fin_cases j <;> simp [toR3, vertexQ]
  have h9 : toR3 (vertexQ 9) = !₂[39/176, 127/352, -249/704] := by
    ext j; fin_cases j <;> simp [toR3, vertexQ]
  have h10 : toR3 (vertexQ 10) = !₂[101/384, -209/384, 9/32] := by
    ext j; fin_cases j <;> simp [toR3, vertexQ]
  have h11 : toR3 (vertexQ 11) = !₂[101/384, 9/32, -209/384] := by
    ext j; fin_cases j <;> simp [toR3, vertexQ]
  have h12 : toR3 (vertexQ 12) = !₂[13/48, -107/192, 13/48] := by
    ext j; fin_cases j <;> simp [toR3, vertexQ]
  have h13 : toR3 (vertexQ 13) = !₂[13/48, 13/48, -107/192] := by
    ext j; fin_cases j <;> simp [toR3, vertexQ]
  have h14 : toR3 (vertexQ 14) = !₂[9/32, -209/384, 101/384] := by
    ext j; fin_cases j <;> simp [toR3, vertexQ]
  have h15 : toR3 (vertexQ 15) = !₂[9/32, 101/384, -209/384] := by
    ext j; fin_cases j <;> simp [toR3, vertexQ]
  have h16 : toR3 (vertexQ 16) = !₂[127/352, -249/704, 39/176] := by
    ext j; fin_cases j <;> simp [toR3, vertexQ]
  have h17 : toR3 (vertexQ 17) = !₂[127/352, 39/176, -249/704] := by
    ext j; fin_cases j <;> simp [toR3, vertexQ]
  have h18 : toR3 (vertexQ 18) = !₂[17/32, 3/32, 3/32] := by
    ext j; fin_cases j <;> simp [toR3, vertexQ]
  have huniv : (Finset.univ : Finset (Fin 19)) = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18} := by decide
  unfold chippedM18 verts
  rw [huniv]
  simp only [Finset.image_insert, Finset.image_singleton, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18]

/-- If the certificate data is valid, the ChippedM18 is not Rupert. -/
theorem not_isRupert_of_certificatesValid (h : CertificatesValid) :
    ¬ IsRupert chippedM18 := by
  obtain ⟨table, hchart, hvalid, hcap, harc⟩ := h
  rw [chippedM18_eq_verts]
  exact not_rupert_of_valid_tables table hchart hvalid hcap harc

/-- The ChippedM18 is a genuine solid: its points are not all in one plane.
(Proved outright: vertices 0, 1, 2 and 5 span a tetrahedron.) -/
theorem not_coplanar_chippedM18 : ¬ Coplanar ℝ (chippedM18 : Set ℝ³) := by
  refine not_coplanar_of_det3_ne_zero
    (a := !₂[-107/192, 13/48, 13/48])
    (b := !₂[-209/384, 101/384, 9/32])
    (c := !₂[-209/384, 9/32, 101/384])
    (d := !₂[-9/32, -9/32, -9/32])
    (by simp [chippedM18]) (by simp [chippedM18]) (by simp [chippedM18]) (by simp [chippedM18]) ?_
  simp [det3, Matrix.det_fin_three]
  norm_num

/-- **The ChippedM18 is a nopert**, given valid certificate data: it is a
genuine solid (`not_coplanar_chippedM18`, a Lean proof) and it is not Rupert
(`not_isRupert_of_certificatesValid`; the data's validity is what
`constructChippedM18` verifies). `IsNopert` is defined in `Nopert.lean`. -/
theorem isNopert_of_certificatesValid (h : CertificatesValid) : IsNopert chippedM18 :=
  ⟨not_coplanar_chippedM18, not_isRupert_of_certificatesValid h⟩

end ChippedM18

end
