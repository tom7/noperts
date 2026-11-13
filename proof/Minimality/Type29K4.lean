module

public import Minimality.Type29NF

@[expose] public section

/-!
# Type 29, class K4 (`FEWER-FACES-PROOFS.md` §21.1)

In the normal coordinates of `NF29` (`Type29NF.lean`) class K4a is `a2 > 0`, `b0 > 0`, `V < 0`
(K4b is its `σ`-image).  On `R_G` (none of the class's E-good `G` edges is a quad edge of `O`,
Lemma 21.3) every shape has a metric-free certificate (Theorem 21.11):

* Lemmas 21.7, 21.8 (`NF29.k4_facts`): `e0, e2 > 0`, `s, t < 1`, `b2 + h2 > 0`, `G5 ≥ 0`.
* Tier (A), `h0 < 1`, Lemma 21.9 (F35): the vertex crossing `V = 035/1456`
  (`NF29.isRupert_k4_V`, view `NF29.vV`) or the edge crossing `Y = 035/356-3`
  (`NF29.isRupert_k4_Y`) is unimodal (`NF29.isRupert_k4_A`; the pentagon argument in reals,
  `k4_Y_core`, with `quint_unimodal_of`).
* Tier (B1), `h0 > 1 > h0 + a0`: tier (A) for `x ∘ σ` (`NF29.sigma`).
* Tier (B2), `h0 + a0 < 0`, Lemma 21.10 (F35′): the edge crossing `W = 023/035-0` and the vertex
  crossing `Z = 035/234` (`NF29.isRupert_k4_W`, `NF29.isRupert_k4_Z`, view `NF29.vZ`) are not
  both depth-separated (Corollary 13.3 with the shared diagonal `[1, 3]`,
  `NF29.isRupert_k4_B2`).
* Theorem 21.11: `NF29.isRupert_K4a` (special positions and genericity in `K4Gen`) and
  `NF29.isRupert_K4b`.

Every rim test is a polynomial in the eight coordinates times the frame determinant, proved
positive from the class, region and type inequalities by explicit products (`linarith` with
product hints); middles are explicit combinations (`mid_comb`).
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Minimality

open scoped RealInnerProductSpace
open Finset

theorem img29 {x : Fin 7 → ℝ³} (i : Fin 7) : x i ∈ univ.image x :=
  Finset.mem_image_of_mem x (mem_univ i)

variable {x : Fin 7 → ℝ³}

/-- The view of `Z = 035/234`: `u_Z = (A0 (B2 − e2), B2 (A0 − e0), A0 B2 − e0 e2)`, along
`aff 035 ∩ aff 234`. -/
noncomputable def NF29.vZ (N : NF29 x) : ℝ³ :=
  nfV N.E₁ N.E₂ N.E₃ (-N.a0 * (-N.b2 - (N.a2 + N.h2 - 1)))
    (-N.b2 * (-N.a0 - (N.b0 + N.h0 - 1))) (N.a0 * N.b2 - (N.b0 + N.h0 - 1) * (N.a2 + N.h2 - 1))

end Minimality

end
