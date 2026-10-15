# How the Nopert proofs work

The solids' proofs share one strategy and most of their machinery. This
page names the techniques; each solid's page says which it uses and what is
special about it. The table at the end summarizes.

## The statement and what is trusted

`IsRupert` ([proof/MainTheorem.lean](proof/MainTheorem.lean), from the
Noperthedron project) says that some rotation and offset of one copy of the
solid has a shadow strictly inside the shadow of another rotated copy.
`IsNopert` ([proof/Nopert.lean](proof/Nopert.lean)) adds that the points are
not all in one plane, so they span a genuine solid.

Each proof has two parts:
- a **Lean theorem**, checked by the kernel with the standard axioms only:
  if the certificate data is valid (`CertificatesValid`), the solid is a
  Nopert;
- a **native check** of the data: the program `constructX` runs the same
  Lean validity checks as compiled code on every row, and only if all pass
  does it construct the proof value (the same trust as `native_decide`,
  which is not used). See [Packs and the native check](#packs-and-the-native-check).

The C++ searches that produce the data need not be trusted: a mistake there
can only produce data that fails the checks.

## Poses and symmetry reductions

A pose is an outer **view** direction u and a **relative rotation** R
between the two copies (the inner copy's offset is eliminated by the
certificates). Both are reduced modulo the solid's symmetries before any
search, since at a symmetry R the two shadows coincide and nothing can be
certified there:
- the view into a fundamental domain (a triangle or a few) of the solid's
  symmetry group with the antipode;
- the relative rotation into the cell of the identity (a Dirichlet,
  max-trace cell); boxes outside it are rejected by **prunes** (icosahedral,
  octahedral, fivefold, C3), checked with exact or bounded-error quadratic
  bounds;
- for solids with central symmetry or a mirror, the **half-turn** or
  **mirror-tie reduction**: R may be replaced by H_u R g (H_u the half-turn
  about the view), which halves the cell again and handles poses that tie.

## Rational models and neighborhoods

The certificates are checked against fixed rational vertices. Unless the
solid is itself rational (the Septopert), the theorem covers every solid
with the right symmetry within 6·10⁻¹⁶ of a rational model (`IModel`,
`OModel`, `C5Model`), and Lean's kernel decides, by exact algebraic
arithmetic and interval enclosures, that the exact solid is one of them.
This works when the solid is not *on the edge*: when its neighborhood
contains no Rupert solids. For solids with exact **ties** (poses of
clearance exactly 0: the snub cube, the deltoidal hexecontahedron), the
theorem is about the exact solid near the ties; see [Caps](#caps) and
[Ties and tie tubes](#ties-and-tie-tubes).

## Codes and the view cover

`codebdd` splits the view domain into cells where the silhouette's
combinatorics (the *face-visibility code*) is constant, and triangulates
them into **code triangles**. That the code triangles cover the view domain
is a separate check (`WedgeCover`, `ViewCover`): decided by the kernel for
the Septopert, checked natively with the tables for the others.

## Balanced witnesses

Every certificate that rules out a box of poses is a **balanced witness**:
directions perpendicular to the view (contacts between the two
silhouettes), weights that balance them so the inner copy's offset cancels,
and an inequality between the outer shadow's support and the rotated inner
points, bounded over the box (Bernstein or ball bounds, with exact or
rigorously bounded arithmetic). Weighted *mixtures* of several witnesses
certify boxes no single one does.

The inner point of a direction need not be a vertex: a **blended inner
point** (1 − t)·v_a + t·v_c on the segment between two vertices is still in
the solid, and its inequality is the same blend of theirs, so it can stay
positive where the best vertex switches. (`KCap.Leaf.blends` in
`Pipeline/KCapCheck.lean`; the `innerOther` / `innerT` fields and pack tags
17 / 18 of the 5D rows. Soundness rests only on `innerPt_mem`.) The searches
try blends only where plain vertices fail, since blended rows are larger.

## The identity tube

At R = identity the two shadows coincide, so near it every witness's slack
is only proportional to the rotation, and boxes would have to shrink
without end. Near the identity the proof instead uses **first-order
rigidity**: for each code triangle, a tree of view triangles (`tubecode`,
`tuberefine`), each with a certificate that rules out every rotation within
a certified radius. These are the identity-tube tables
(`Pipeline/AtlasProjectiveLocalViewTree.lean`).

## Identity blow-up certificates

Instead of a radius from first-order rigidity, the rotations near the
identity can be **blown up**: write the Cayley vector of R as w = μσ̂ (μ ≥ 0,
σ̂ on a face of the cube [−1, 1]³). With denominators cleared, the witness
inequality is a polynomial whose μ⁰ term vanishes; divided by μ it is the
first-order term plus the exact higher-order terms, which no longer shrink
with the rotation. An **identity blow-up row** holds, for a view triangle,
per cube face a subdivision of (μ, view, direction) whose leaves are
balanced witnesses, checked exactly over ℚ, and rules out every rotation
within radius 1/64 of the identity over the triangle (`Pipeline/IdCap.lean`;
`Pipeline/CayleyNear.lean`: a rotation within ρ ≤ 1 of the identity has a
Cayley vector of length at most ρ; `Pipeline/IdCapBridge.lean`, `Row.idcap`; found by `search/common/idcap.cc`).
This needs an exact (rational) model.

## The 5D search

Away from the identity, `search5d` covers the reduced poses: (view triangle)
× (box of Cayley coordinates of R) in each of four **Cayley charts** that
together cover all rotations. Each leaf of its trees is a balanced witness
(single or mixture), a **tube leaf** (inside the identity tube's radius), a
**cap leaf** (inside a cap, below) or a prune. `pack5d` writes the trees as
the **solution tables**, one per chart (`Pipeline/AtlasProjectiveSolutionTree.lean`).

## Caps

At a few special views the margin vanishes or a tie meets the identity, and
the 5D search cannot close. There a **cap** blows up the view and the
rotation together (view u = x + μ·e(…), rotation w = μ·(…), charts on the
faces of a cube and cones at the identity and around the ties), with each
box certified by a balanced witness divided by the blow-up variables and
bounded exactly (over ℚ, ℚ(t) or ℚ(√5, sin 72°)). The 5D search's cap leaves
cite the cap's claim (`Pipeline/KCapTree.lean`, `Pipeline/KCapCheck.lean`;
the solids' `Caps` modules).

## Ties and tie tubes

A **tie** is a family of poses of clearance exactly 0. No box around it can
be certified by bounds, so along each tie a **tie tube** proves, exactly,
that no rotation close to the tie is a passage. Ties come from symmetry
(H_u R g, the half-turn or mirror-tie reduction above).

## Packs and the native check

`pack5d` and `export-codetrees-pack` write the tables as compact binary
**packs** (per code triangle). The executable `constructX` decodes them
(decoding is untrusted: the decoded table is what gets checked), checks
every row in parallel native code, and applies the kernel-proved soundness
theorems that turn valid tables into `¬ IsRupert`.

## Which solid uses what

| | rational model / neighborhood | identity tube | blow-up rows | caps | ties | reductions |
|---|---|---|---|---|---|---|
| [Septopert](septopert.md) | exact (rational) | yes | yes | at the mirror normal | mirror ties | C3, mirror-tie |
| [Snub cube](snub-cube.md) | `OModel` | yes | | at the zero-margin view | one tie, in the cap | octahedral |
| [Snub dodecahedron](snub-dodecahedron.md) | `IModel` | yes | | | | icosahedral, fivefold |
| [Pentagonal hexecontahedron](pentagonal-hexecontahedron.md) | `IModel` | yes | | | | icosahedral, fivefold |
| [Deltoidal hexecontahedron](deltoidal-hexecontahedron.md) | exact near the ties | yes | | 3 caps | tie tubes | icosahedral, half-turn |
| [Candidate #231](nopert231.md) | `C5Model` | yes | | | | fivefold |

All use codes, the view cover, balanced witnesses, the 5D search and the
native check. Blended inner points are in the data of every solid except
the snub cube (whose search has not been rerun with them).
