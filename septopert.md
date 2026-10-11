# The Septopert

The Septopert is a convex polyhedron with 7 vertices that is not Rupert.
This page gives the exact statement, what Lean checked and how, and how to
reproduce the result.

Lean entry point: [`proof/Septopert.lean`](proof/Septopert.lean).

## The solid

The convex hull of these 7 points. Each coordinate is an integer divided by
1048576 (2^20):

```
-940638   327651   327651
 327651  -940638   327651
 327651   327651  -940638
 703968    47788    47788
  47788   703968    47788
  47788    47788   703968
-514207  -514207  -514207
```

In lowest terms (the form used in Lean, `septopert` in
`proof/Septopert.lean`):

| vertex | x | y | z |
|---|---|---|---|
| 0 | −470319/524288 | 327651/1048576 | 327651/1048576 |
| 1 | 327651/1048576 | −470319/524288 | 327651/1048576 |
| 2 | 327651/1048576 | 327651/1048576 | −470319/524288 |
| 3 | 21999/32768 | 11947/262144 | 11947/262144 |
| 4 | 11947/262144 | 21999/32768 | 11947/262144 |
| 5 | 11947/262144 | 11947/262144 | 21999/32768 |
| 6 | −514207/1048576 | −514207/1048576 | −514207/1048576 |

- The statement is about these points unscaled (largest |v| ≈ 0.99999935).
  The integer form is the same solid scaled by 2^20.
- Symmetry C3v: a 3-fold axis along (1,1,1) and three mirror planes (each
  swapping two coordinates). Vertices 0–2 are the permutations of (a, b, b),
  vertices 3–5 those of (c, d, d), and vertex 6 is e·(1,1,1).
- 10 triangular faces; vertex degrees 5,5,5 (vertices 0–2), 4,4,4 (3–5)
  and 3 (vertex 6). Combinatorially a gyroelongated triangular pyramid: a
  triangular antiprism (vertices 0–5) with a pyramid (apex 6) on its larger
  face.
- `search/septopert_model.txt` is the exact (rational) model the search
  uses; `proof/Septopert/ModelData.lean` has the same vertices.

## The statement

In [`proof/Septopert.lean`](proof/Septopert.lean):

```lean
theorem isNopert_of_certificatesValid (h : CertificatesValid) : IsNopert septopert
```

`IsNopert V` (in `proof/Nopert.lean`) says that the points of `V` are not all
in one plane, so their convex hull is a genuine solid, and that this solid is
not Rupert. `IsRupert` (in `proof/MainTheorem.lean`) is the Rupert property:
two copies of the solid, each rotated, can be placed so that the shadow of
one lies strictly inside the shadow of the other. `CertificatesValid` says
that the certificate data (four solution tables and a cap certificate) passes
Lean's validity checks. The same `IsNopert` is used by the
[minimality](minimality.md) result, so the two together say that 7 is the
smallest number of vertices of a nopert.

## What is proved and what is verified

This is a **Lean verification**, not a direct kernel-only Lean proof:

1. **Lean proof.** `isNopert_of_certificatesValid` is checked by Lean's
   kernel and depends only on the standard axioms (`propext`,
   `Classical.choice`, `Quot.sound`). Its "genuine solid" half needs no data
   at all.
2. **Verification of the data.** The data is about 85 million table rows
   (6.7 GB), too much for the kernel. The program `constructSeptopert` runs
   the same Lean validity checks as compiled code on every row, and only if
   all pass does it construct `¬ IsRupert` (via part 1) and print
   `instantiated: ¬ IsRupert Septopert.verts (the Septopert is not Rupert)`.
   This step trusts Lean's compiler and runtime to evaluate the checks
   correctly — the same trust as `native_decide`, though `native_decide` is
   not used.

The C++ search in `search/` that produced the data does not need to be
trusted: a mistake there can only produce data that fails the checks.

## Reproducing

See [BUILDING.md](BUILDING.md) for requirements. From a fresh clone:

```sh
./get-cc-lib.sh
(cd proof && lake exe cache get)                       # Mathlib build cache
search/septopert_rebuild.sh --from model --threads 64 --mem_gb 100
```

This builds everything, runs `codebdd` on the exact model
`search/septopert_model.txt`, runs the search, packs the tables into `work/`, and
finally runs `constructSeptopert` on them. Stages: `model`, `tube`,
`tubepack`, `cap`, `search`, `pack`, `verify`; `--from STAGE` restarts at a
stage, `--only STAGE` runs one, `--work DIR` moves the output. Each stage
appends its wall time and peak memory to `work/stages.log`.

Measured times (the 64-core column is a from-scratch run in a fresh clone,
4 h 22 min in total):

| Stage | 16 cores, 12 threads | 64 cores, 64 threads |
|---|---|---|
| model | | 7 s |
| tube + tubepack | 11 min | 3.6 min |
| cap | 2 min | 33 s |
| search | about 2 h | 28 min |
| pack | 2 h 20 min | 49 min |
| verify | 8 h 22 min, 15.7 GB peak | 3 h 1 min, 15.2 GB peak |

An independent reproduction (2026-10-10) followed these steps from a fresh
clone, in a container on the 64-core machine without network access or
systemd: it copied in a checkout of cc-lib r7488 and the Mathlib build
cache, and the rebuild ran its stages without memory caps. Its stages took
about 4 h in all: model 8 s, tube 3.3 min, tubepack 17 s, cap 33 s, search
28 min (64,840,591 nodes), pack 48 min and verify 2 h 40 min. Its tube
tables and cap certificate were byte-identical to the archive, its chart
tables had exactly the row counts below, and `constructSeptopert` ended with
`instantiated: ¬ IsRupert Septopert.verts`. (Its reported peak memory,
42.9 GB, was read from the container's cgroup, so it counts the page cache
too; it is not comparable with the column above.)

## Verifying existing data

Given the data (`tube_packs/`, `packs/`, `cap-1_16.cert`), only the last
stage is needed:

```sh
(cd proof && lake build constructSeptopert)
cd work && LEAN_NUM_THREADS=64 ../proof/.lake/build/bin/constructSeptopert \
  tube_packs/manifest.txt packs cap-1_16.cert
```

It checks the cap certificate, the 22 tube tables, then the four chart
tables one at a time (chart 0 is 83,340,081 rows; charts 1–3 have 144,165,
124,872 and 104,577).

## The data

The certificate data is machine output, intended to be CC0:

- `cap-1_16.cert`: 540 KB, the cap certificate around the mirror directions;
- `tube_packs/`: 382 MB, 22 identity-tube tables and `manifest.txt`;
- `packs/`: 6.3 GB, 88 per-code solution packs (`packs/c<chart>/t<code>.pack`).

Two independent runs (a 16-core machine with restarts, and a from-scratch
64-core run) produced byte-identical files, and three native verifications
(two machines) passed; a third from-scratch rebuild (above) and its
verification passed too. An archive with SHA-256 sums of all files is kept at
`/mnt/nopertdata/archive/septopert/` on the 64-core VM (and
`septopert.7z`, 575 MB). `packs/c0/t3.pack` alone is 5.2 GB, above GitHub's
2 GB release-asset limit, so the data is not attached to the repository;
rebuilding reproduces it.
