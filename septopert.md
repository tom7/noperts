# The Septopert

*Draft: this page is a placeholder and will be rewritten.*

The Septopert is a convex polyhedron with 7 vertices that is not Rupert (a
"nopert"). Its vertices are

- (-7, 7, 7), (3, -4, -4), (7, 7, 7) and their coordinate permutations
  (3 + 3 + 1 = 7 distinct points).

The Lean entry point is [`proof/Septopert.lean`](proof/Septopert.lean), with
the headline theorem in [`proof/Septopert/IsNopert.lean`](proof/Septopert/IsNopert.lean)
(`Septopert.isNopert_of_certificatesValid`). The certificate data is checked by
the executables `constructSeptopert` (everything), `checkSeptopertArc`,
`checkSeptopertAxis` and `checkSeptopertPCap` (the cap certificates alone). The search is in
[`search/septopert/`](search/septopert/).

Other 7-vertex noperts found along the way: [SeptopertM18](septopert-m18.md)
(`proof/SeptopertM18/`) and SeptopertM12 (`proof/SeptopertM12/`).

TODO: write this page (description, pictures, STL, how it was found, verification log).
