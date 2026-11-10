module

public import Septopert.ArcCap
public import Septopert.AxisCap
public import Septopert.IsNopert
public import Septopert.Integer

@[expose] public section

/-!
# The Septopert is not Rupert

The **Septopert** is the convex polyhedron whose vertices are the seven integer points

    (−7, 7, 7), (7, −7, 7), (7, 7, −7), (3, −4, −4), (−4, 3, −4), (−4, −4, 3), (7, 7, 7)

(`Septopert.intVerts`, also called `Septopert.septopert`). It is the 7-vertex Nopert of the main theorem
(`ProofOfMainTheorem.lean`). This file is the entry point for its result. It contains no definitions of its own: it
imports the modules of the proof (in `Septopert/`), and this comment says what Lean has checked and where.

## The statement

In `Septopert/Integer.lean`:

    theorem Septopert.isNopert_intVerts (h : Septopert.CertificatesValid) : IsNopert Septopert.intVerts

`IsNopert` (in `Nopert.lean`) says that the solid is genuine (its points are not all in one plane) and that it is not
Rupert. `IsRupert` (in `MainTheorem.lean`) says that two copies of the solid, each rotated arbitrarily, can be placed
so that the shadow of one (projected straight down onto the plane, and slid sideways by any amount) lies strictly
inside the shadow of the other. That is the same as cutting a straight hole through one copy that the other copy can
pass through.

The certificates are built in a congruent copy of the solid, `Septopert.verts`, with the coordinates
(−27, 15, 15), (27, 6, 6), (−13, −13, −13) and their permutations, over 64. `Septopert/Integer.lean` maps it to the
integer coordinates by an exact similarity (`Septopert.intVerts_image_eq`: scale 3/64, an orthogonal map and a
translation), and similarities preserve Rupertness.

## What Lean proved, and what it verified

The result has two parts, and they are trusted differently.

1. **A Lean proof** (`Septopert.isNopert_intVerts`): *if* the certificate data is valid, *then* the Septopert is a
   Nopert. That it is genuine is proved outright (vertices 0, 1, 2 and 6 span a tetrahedron). This part is checked by
   Lean's kernel in the usual way. It depends only on the standard axioms (`propext`, `Classical.choice`,
   `Quot.sound`) and on nothing about how the data was produced.

   `Septopert.CertificatesValid` (in `Septopert/IsNopert.lean`) says what valid means. There are four solution
   tables, one for each of the four charts that together cover every rotation, and each passes Lean's validity check.
   The tables record, for each piece of the space of rotations, why no passage exists there. Four certificates
   cover the small regions of views that the tables leave out, where the first-order margin vanishes, and each passes
   its check:
   - the mirror cap, around the solid's mirror directions (`SolutionTree.CapOk`);
   - the arc cap, along the arc of views ending at the view down an apex edge, a consequence of the cube corner at
     vertex 6 (`SolutionTree.ArcOk`, `Septopert/ArcCap.lean`);
   - the axis cap, around the view along the 3-fold axis, where the exact Triforce puts the inner triangle's shadow
     on the base's medial triangle (`SolutionTree.AxisOk`, `Septopert/AxisCap.lean`);
   - the P cap, along the strip of views where face 0–2–4 is edge-on (`PCapOk`, `Septopert/PCap.lean`).

2. **A Lean verification** that the data is valid. The data (about 732,000 table rows and the four cap
   certificates) is too much for the kernel to check directly. Instead, the program `constructSeptopert` (in
   `constructSeptopert.lean`) reads the data, runs Lean's own validity checks on all of it as compiled code, and,
   only if every check passes, uses part 1 to build a value of type `IsNopert Septopert.intVerts` and prints

       instantiated: IsNopert Septopert.intVerts (...)

   Trusting this part means trusting that Lean's compiler and runtime evaluate the check functions correctly. That
   is the same trust that `native_decide` asks for, although no `native_decide` is used. The check functions
   themselves are ordinary Lean definitions, and the kernel proves (part 1) that if they return true, the conclusion
   follows.

The programs that *found* the data (the C++ in `search/septopert/`) do not need to be trusted at all: a mistake there can only
produce data that fails the checks.

See `septopert.md` at the top of the repository for the solid's geometry, how the proof works, how to obtain the
data and rerun the verification, and the times it takes.
-/
