module

public import Minimality.Type16Cover
public import Minimality.Type16Rims

@[expose] public section

/-!
# Type 16: the pairs and the triple on `Ω`

On the residual `Ω` of Theorem 19.2 no edge certificate of the named edges applies; each part of
`Ω` is certified by two or three tests whose failures force opposite signs of an inner product
of their views (Lemma V, in the form of the angle lemma 13.2: a failing quadrilateral rim has
its diagonals depth-separated, and the direction of the separation is fixed by the crossing of
the diagonals, `depthSep_of_meet`).

* **Lemma 19.3** (`cert_F3`): `Ω ∩ {d > 1}`: the closing `K_3` at `35` (rim `(3, x, 4, 1)`)
  and the vertex crossing `046/145` at `4` (view `vT2`, rim `(4, 5, 3, 6)`).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace NF16

variable {x : Fin 7 → ℝ³}

/-! ### Lemma 19.3 -/

/-- `f15 = f046(1) − f046(5)`: `046` faces toward `5` at the view along `15` iff `f15 > 0`. -/
def f15 (N : NF16 x) : ℝ := (N.g - 1) * (N.p + N.r - 1) - N.d * N.q

/-- `[0146] = f046(1)`. -/
def t0146v (N : NF16 x) : ℝ := N.g * (N.p + N.r - 1) - N.q * (N.d - 1)

/-- **The view of `T2`** (§19.3 (ii)): `v = (−f15)(4 − 1) + f046(1)(5 − 1)`, parallel to the
planes of `046` and `145`. -/
noncomputable def vT2 (N : NF16 x) : ℝ³ :=
  nfV N.E₁ N.E₂ N.E₃ (-N.f15 * N.p) (-N.f15 * (N.q - N.g) + N.t0146v * (1 - N.g))
    (-N.f15 * (N.r - N.d) + N.t0146v * (-N.d))

/-- `vT2` is the named view along the vertex crossing `046/145` (`vtxView16 x 0 = −D vT2`). -/
theorem vtxView16_vT2 (N : NF16 x) : vtxView16 x 0 = (-N.D) • N.vT2 := by
  show planeLine (x 0) (x 4) (x 6) (x 1) (x 4) (x 5) = _
  simp only [planeLine, vT2, f15, t0146v, D]
  nf_simp N
  ext k
  simp only [nfV, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, PiLp.neg_apply, smul_eq_mul,
    det3c]
  ring

-- order: [3, 1, 4, 2]

-- order: [3, 1, 4, 0]

-- order: [4, 6, 3, 5]

/-! ### Lemma 19.4 and Lemma 19.5: the views -/

/-- `f03`: `146` faces toward `3` at the view along `03` iff `f03 > 0`. -/
def f03 (N : NF16 x) : ℝ := N.q * (1 - N.d) + N.g * (N.r - 1)

/-- **The view of `A`** (§19.4 (i)): `v_A = (g p, 0, f03) = g p (0 − 6) + [0146] (6 − 3)`, along the
line of the planes `036` and `146`. -/
noncomputable def vA (N : NF16 x) : ℝ³ := nfV N.E₁ N.E₂ N.E₃ (N.g * N.p) 0 N.f03

/-- **The view of `T_a`** (§19.5): `u_a = (p + r − 1, q, 0) = (4 − 0) + r (0 − 6)`, along the
line of the planes `0235` and `046`. -/
noncomputable def uA (N : NF16 x) : ℝ³ := nfV N.E₁ N.E₂ N.E₃ (N.p + N.r - 1) N.q 0

/-- `vA` is the named view along the vertex crossing `036/146` (`vtxView16 x 1 = −D vA`). -/
theorem vtxView16_vA (N : NF16 x) : vtxView16 x 1 = (-N.D) • N.vA := by
  show planeLine (x 0) (x 3) (x 6) (x 1) (x 4) (x 6) = _
  simp only [planeLine, vA, f03, D]
  nf_simp N
  ext k
  simp only [nfV, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, PiLp.neg_apply, smul_eq_mul,
    det3c]
  ring

/-- `uA` is the named view along the vertex crossing `0235/046` (`vtxView16 x 2 = −D uA`). -/
theorem vtxView16_uA (N : NF16 x) : vtxView16 x 2 = (-N.D) • N.uA := by
  show planeLine (x 0) (x 3) (x 5) (x 0) (x 4) (x 6) = _
  simp only [planeLine, uA, D]
  nf_simp N
  ext k
  simp only [nfV, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, PiLp.neg_apply, smul_eq_mul,
    det3c]
  ring

-- order: [6, 3, 5, 4]

-- order: [1, 4, 0, 6]

-- order: [6, 0, 2, 4, 1]

-- order: [0, 5, 1, 6]

-- order: [6, 3, 5, 2, 4]

-- order: [1, 4, 2, 0, 6]

/-! ### Lemma 19.5: the triple `T6` on `Ω_open` -/

end NF16

end Minimality

end
