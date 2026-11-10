import SeptopertShell

/-!
# The Septopert island is surrounded by Rupert shapes

This file is the entry point for the result about the shapes *near* Septopert Classic. It states exactly what Lean
has checked.

## The family and the island

Septopert Classic (`SeptopertClassic.lean`) belongs to the *Septopert family*: the 7-vertex solids with vertices
`(−a, b, b)`, `(c, e, e)`, `(−f, −f, −f)` and the coordinate permutations of the first two. Up to similarity, such
a solid is fixed by three numbers `(s, y, z)` = `(P/A, C/A, E/A)`, where `A = a + b`, `P = a − f`, `C = c − b`,
`E = e − b`. `SeptopertShell.shellVerts p` is the solid with parameters `p = (s, y, z)`. Its vertices are
`(0, 1, 1)`, `(1 + y, 1 + z, 1 + z)` and `(s, s, s)`, plus the coordinate permutations of the first two.
Septopert Classic is the point `SeptopertShell.classicParams` = `(426431, 376317, −279863) / 1268289`.

Computer search says that Septopert Classic is not alone: the shapes around it form a small region in which none of
them has a passage, the *Septopert island*. Numerically, it is a curved tetrahedron with one corner cut off. The
island has five faces: the plane `s = 1/3` (where the solid's apex is an exact cube corner), the plane `y − z = 1/2`,
two curved faces and a small facet. It is tiny: `s` runs from 1/3 to about 0.3504, `y` from about 0.27 to 0.32,
and `z` from about −0.227 to −0.211. Just outside every face, the shapes have passages.

## What `IslandEnclosed` says

`SeptopertShell.IslandEnclosed` says: There is a set `W` of parameter points such that every shape in `W` is Rupert,
and every continuous path in parameter space from Septopert Classic to the far-away point
`SeptopertShell.outsideParams` = `(1, 0, 0)` passes through `W`. In other words, there is no way to deform Septopert
Classic continuously within the family into a distant shape without passing through a shape that is Rupert: the
island is walled off by a watertight shell of shapes, each with a certified passage.

It does not say that every shape inside the shell is a Nopert (only Septopert Classic itself is proved to be one,
in `SeptopertClassic.lean`), nor that the island is exactly the region described above.

## How the shell is built

For each face of the island there is a *slab*: a thin curved box just outside the face, given by a polynomial chart
`(x₀, x₁, δ) ↦ (s, y, z)` in which `δ` measures how far outside the face the shape is, for `δ` from 1/1000 to 2/1000.
Each slab comes with one witness for all of its shapes at once. The view direction, the rotation of the inner copy and
its offset are all polynomial in the chart coordinates. For every shape in the slab, every vertex of the rotated inner
copy must project strictly inside a triangle of the outer copy's projected vertices. That is 21 polynomial
inequalities, plus one more that makes the view direction usable. They are proved on the whole box by exact rational
lower bounds, with subdivision. Each piece of the subdivision uses one of two bounds: a centred form
(`SeptopertShell.Poly.centredBound`) or a Bernstein-basis bound (`SeptopertShell.Bern`). So every shape in a slab is
Rupert (`SeptopertShell.SlabData.isRupert_of_check`). There are six slabs: one per face, with the slanted face in two
halves.

The slabs alone do not obviously close up into a shell, so the certificate also has a *closure* part. It defines a
region `D` around the island: a bounding box, cut down by one polynomial inequality per face that ends in the middle
of that face's slab (`δ = 3/2000`). It then checks three things: that the boundary of `D` lies inside the union of the
slabs; that Septopert Classic is in `D`; and that `(1, 0, 0)` is not. A path that starts in `D` and ends outside it
must cross the boundary of `D`, hence a slab (`SeptopertShell.separates_of_frontier_subset`).

## What Lean proved, and what it verified

1. **A Lean proof** (`SeptopertShell.islandEnclosed_of_closureData`, in `SeptopertShell.lean`): *if* the check
   functions return `true` on the certificate data, *then* `IslandEnclosed` holds. This is checked by Lean's kernel in
   the usual way, uses only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`), and depends on
   nothing about how the data was produced.

2. **A Lean verification** that the check functions return `true` on the certificate. The certificate is 43 KB of
   text, `SeptopertShell/data/shell.txt`, compiled into the library. Here `native_decide` runs the check while this
   file is compiled, which takes about 75 seconds and 7 GB of memory. That makes `SeptopertShell.islandEnclosed` an
   ordinary theorem that other files can import. Trusting it means trusting that Lean's compiler and runtime evaluate
   the check functions correctly. Lean records this trust as auxiliary axioms that `native_decide` adds. The
   assertion at the end of this file fails unless those, and the standard axioms, are the only ones used. The
   repository's headline theorems use only the standard axioms (`Tests/Axioms.lean`) and do not import this file.
   The program `checkSeptopertShell` performs the same check in about 8 seconds, without `native_decide`, and
   instantiates `IslandEnclosed` at run time.

The programs that *found* the certificate (polynomial fits of the witnesses and exact certifiers, in C++ and Python)
do not need to be trusted: a mistake there can only produce data that fails the checks.
-/

namespace SeptopertShell

/-- The inlined certificate, parsed (`none` if it does not parse). -/
def shellData? : Option ClosureData :=
  match parseShell shellText with
  | .ok C => some C
  | .error _ => none

theorem shellData?_isSome : shellData?.isSome = true := by native_decide

/-- The inlined certificate. -/
def shellData : ClosureData := shellData?.get shellData?_isSome

theorem shellData_classicOk : shellData.classicOk = true := by native_decide

theorem shellData_checkPar : shellData.checkPar 32 = true := by native_decide

/-- **The Septopert island is enclosed by Rupert shapes**: every continuous path in the Septopert family from
Septopert Classic to `(P/A, C/A, E/A) = (1, 0, 0)` passes through a set of Rupert shapes (`native_decide` on the
inlined certificate). -/
theorem islandEnclosed : IslandEnclosed :=
  islandEnclosed_of_closureData shellData (shellData.check_of_checkPar shellData_checkPar) shellData_classicOk

end SeptopertShell

open Lean Elab Command in
/-- Fails unless the theorem depends only on the standard axioms and `native_decide`'s auxiliary axioms. -/
elab "#assert_native_axioms " id:ident : command => do
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let axioms ← liftCoreM <| collectAxioms name
  let standard := #[``propext, ``Classical.choice, ``Quot.sound]
  for a in axioms do
    unless standard.contains a || (a.toString.splitOn "._native.native_decide.").length > 1 do
      throwError "{name} depends on {a}"

#assert_native_axioms SeptopertShell.islandEnclosed
