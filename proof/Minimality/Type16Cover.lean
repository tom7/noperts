module

public import Minimality.Type16NF

@[expose] public section

/-!
# Type 16: the Lemma E cover

In the normal form `NF16` (§19.0), each step of Theorem 19.2 names an edge crossing whose
two closings satisfy Lemma E (`rimCert_edgePairσ_robust`: Lemma E with ties), or a triangle
closing (`rimCert_edgeTriσ_robust`); each step ends in a certificate `Cert16` (a rim
certificate at a named view, §18.2), with no horizontal double normal assumed.  Depth ties are
allowed: only three far corners (or the
three triangle corners) at one depth are excluded, which `TieSeg` (at most one tie at each
edge view) rules out (`depth_far3`, `depth_tri3`).  Every orientation test is a polynomial in `(a, b, g, d, p, q, r)`
times the frame determinant `D` (`nf_test`); the sign of each polynomial on its region is
a type inequality, a defining inequality of the region, or a short identity (given in the
proofs, found with an exact LP over products of the hypotheses).

* `NF16.cert_E06`: off `R1 ∪ R2`, the pair at `06` (Proposition 14.3; `5` is always a
  corner, `1` hidden iff not `R1`, `2` hidden iff not `R2`).
* Theorem 19.2 in `R1`: step 1 (A, the planar closing `1356` at `14`, `cert_stepA`), step 2
  (U, `d > 1`: E35, `cert_stepU1a`, `_U1b`), step 3 (U, `d < 1`: E35, E02, E25, E03,
  `cert_stepU2`–`_U5`), step 4 (D, `c36 < 0`: E36, `cert_stepD1`), step 5 (D2–D4:
  E35, E25, E03; D5, D6: triangle closings at `16`, `15`; D7: `4` hidden at `35`;
  `cert_stepD2`–`_D7`).
* Lemma 19.1 (b), (c) (`g_gt_one`, `q_gt_b`), the special positions of the route (`Gen`), the
  residual `Omega` and the dispatch `cert_R1_or_omega`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Minimality

open scoped RealInnerProductSpace
open Finset

namespace NF16

variable {x : Fin 7 → ℝ³}

theorem mem_image (i : Fin 7) : x i ∈ univ.image x := Finset.mem_image_of_mem x (mem_univ i)

/-! ### Lemma 19.1 and the dispatch of Theorem 19.2 -/

/-- The nondegeneracy conditions of the cover (§19.7.1, "equality in a sign condition of the
route" and the far-end ties), as polynomials of the normal form. -/
structure Gen (N : NF16 x) : Prop where
  qg : N.q ≠ N.g
  rd : N.r ≠ N.d
  p013 : N.r * N.g ≠ N.q * N.d
  a1 : N.a ≠ 1
  b1 : N.b ≠ 1
  g1 : N.g ≠ 1
  d1 : N.d ≠ 1
  Z2 : N.a * N.q ≠ N.b * N.p
  c36 : N.q * (N.a - 1) ≠ N.b * (N.p - 1)
  f15 : (N.g - 1) * (N.p + N.r - 1) ≠ N.d * N.q
  f03 : N.q * (1 - N.d) + N.g * (N.r - 1) ≠ 0
  pr : N.p + N.r ≠ 1
  HA : (N.b - 1) * N.g * N.p * N.r + (N.q * (1 - N.d) + N.g * (N.r - 1)) *
    (N.a * (N.q - 1) - (N.b - 1) * N.p) ≠ 0
  T5 : N.d * (N.q * (N.a - 1) - N.b * (N.p - 1)) - (N.g - 1) * (N.a - 1) * N.r ≠ 0

end NF16

end Minimality

end
