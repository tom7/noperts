module

public import SeptopertM12.ArcCap
public import SeptopertM12.AxisCap
public import SeptopertM12.IsNopert

@[expose] public section

/-!
# SeptopertM12 is not Rupert

**SeptopertM12** is the convex polyhedron whose vertices are the seven points

    (−11, 7, 7), (7, −11, 7), (7, 7, −11), (12, 3, 3), (3, 12, 3), (3, 3, 12), (−5, −5, −5)

divided by 16 (`SeptopertM12.verts`; the exact rationals are `SeptopertM12.vertexQ` in `SeptopertM12/Model.lean`).
It is a member of the Septopert family in the same doubly special position as the Septopert (`Septopert.lean`): the
apex, vertex 6, is an exact cube corner, and the Triforce is exact. This file is the entry point for its result. It
contains no definitions of its own: it imports the modules of the proof (in `SeptopertM12/`), and this comment says
what Lean has checked and where.

## The statement

In `SeptopertM12/IsNopert.lean`:

    theorem SeptopertM12.isNopert_of_certificatesValid (h : SeptopertM12.CertificatesValid) :
        IsNopert SeptopertM12.verts

`IsNopert` (in `Nopert.lean`) says that the solid is genuine (its points are not all in one plane) and that it is not
Rupert. `IsRupert` (in `MainTheorem.lean`) says that two copies of the solid, each rotated arbitrarily, can be placed
so that the shadow of one (projected straight down onto the plane, and slid sideways by any amount) lies strictly
inside the shadow of the other. That is the same as cutting a straight hole through one copy that the other copy can
pass through.

## What Lean proved, and what it verified

The result has two parts, and they are trusted differently.

1. **A Lean proof** (`SeptopertM12.isNopert_of_certificatesValid`): *if* the certificate data is valid, *then*
   SeptopertM12 is a Nopert. That it is genuine is proved outright (vertices 0, 1, 2 and 6 span a tetrahedron). This
   part is checked by Lean's kernel in the usual way. It depends only on the standard axioms (`propext`,
   `Classical.choice`, `Quot.sound`) and on nothing about how the data was produced.

   `SeptopertM12.CertificatesValid` (in `SeptopertM12/IsNopert.lean`) says what valid means. There are four solution
   tables, one for each of the four charts that together cover every rotation, and each passes Lean's validity check.
   The tables record, for each piece of the space of rotations, why no passage exists there. Four certificates
   cover the small regions of views that the tables leave out, where the first-order margin vanishes, and each passes
   its check:
   - the mirror cap, around the solid's mirror directions (`SolutionTree.CapOk`);
   - the arc cap, along the arc of views ending at the view down an apex edge, a consequence of the cube corner at
     vertex 6 (`SolutionTree.ArcOk`, `SeptopertM12/ArcCap.lean`);
   - the axis cap, around the view along the 3-fold axis, where the exact Triforce puts the inner triangle's shadow
     on the base's medial triangle (`SolutionTree.AxisOk`, `SeptopertM12/AxisCap.lean`);
   - the P cap, along the strip of views where face 0–2–4 is edge-on (`PCapOk`, `SeptopertM12/PCap.lean`).

2. **A Lean verification** that the data is valid. The data (about 768,000 table rows and the four cap
   certificates) is too much for the kernel to check directly. Instead, the program `constructSeptopertM12` (in
   `constructSeptopertM12.lean`) reads the data, runs Lean's own validity checks on all of it as compiled code, and,
   only if every check passes, uses part 1 to build a value of type `IsNopert SeptopertM12.verts` and prints

       instantiated: IsNopert SeptopertM12.verts (...)

   Trusting this part means trusting that Lean's compiler and runtime evaluate the check functions correctly. That
   is the same trust that `native_decide` asks for, although no `native_decide` is used. The check functions
   themselves are ordinary Lean definitions, and the kernel proves (part 1) that if they return true, the conclusion
   follows.

The programs that *found* the data (the C++ in `search/septopert-m12/`) do not need to be trusted at all: a mistake
there can only produce data that fails the checks.

See `septopert-m12.md` at the top of the repository for the solid's geometry, how to obtain the data and rerun the
verification, and the times it takes.
-/
