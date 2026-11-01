module

public import Minimality.Type16V2Tri
public import Minimality.Type16NF

@[expose] public section


/-!
# U1 bridge: type 16 in its normal form, with the facet functions and view depths in the parameters

`Par T`: the normal form `N = T.toNF` (`x3 = 0`, `x0 = e1`, `x5 = e2`, `x6 = e3`, `x2 = (a,b,0)`, `x1 = (0,g,d)`,
`x4 = (p,q,r)`) with
* `E` (`046`): `fE(j) = e3 * (1 - α - γ + s β)` at `(α,β,γ)`, `s = (p+r-1)/q`;
* `B` (`1356`): `fB(0) = b0`, `fB(4) = p b0`, `fB(2) = a b0`;
* `F` (`145`), `H` (`245`): `φF * (p d) = t3 * R1`, `φH * (a r) = -h3 * R2`;
* depths along `u = x6 - x0`: `⟪x j, u⟫ = z3 + α m1 + β m2 + γ m3` with `m3 - m1 > 0`, `m2 = ζ`.
-/

set_option autoImplicit true
set_option linter.unusedVariables false
open scoped RealInnerProductSpace
open Finset Filter

namespace Minimality
namespace H16U
open V2

variable {x : Fin 7 → ℝ³}

theorem ff_nf (T : Type16 x) (i : Fin 8) {v : ℝ³} {α β γ : ℝ}
    (h : v = nfP (x 3) (x 0 - x 3) (x 5 - x 3) (x 6 - x 3) α β γ) :
    T.ff i v = T.ff i (x 3) + α * (T.ff i (x 0) - T.ff i (x 3)) + β * (T.ff i (x 5) - T.ff i (x 3)) +
      γ * (T.ff i (x 6) - T.ff i (x 3)) := by
  fin_cases i
  · exact face_nf T.q0235 h
  · exact face_nf T.q1356 h
  · exact face_nf T.t024 h
  · exact face_nf T.t036 h
  · exact face_nf T.t046 h
  · exact face_nf T.t145 h
  · exact face_nf T.t146 h
  · exact face_nf T.t245 h

/-- The type-16 data in the normal form frame. -/
structure Par (T : Type16 x) where
  N : NF16 x
  e3 : ℝ
  he3 : e3 < 0
  eE3 : T.ff 4 (x 3) = e3
  eE5 : T.ff 4 (x 5) = e3 * (1 + (N.p + N.r - 1) / N.q)
  eE1 : T.ff 4 (x 1) = e3 * (1 - N.d + (N.p + N.r - 1) / N.q * N.g)
  eE2 : T.ff 4 (x 2) = e3 * (1 - N.a + (N.p + N.r - 1) / N.q * N.b)
  b0 : ℝ
  hb0 : b0 < 0
  eB0 : T.ff 1 (x 0) = b0
  eB4 : T.ff 1 (x 4) = N.p * b0
  eB2 : T.ff 1 (x 2) = N.a * b0
  t3 : ℝ
  ht3 : t3 < 0
  eF : (T.ff 5 (x 6) - T.ff 5 (x 0)) * (N.p * N.d) = t3 * ((N.g - 1) * (N.p + N.r) - N.d * (N.q - 1))
  h3 : ℝ
  hh3 : h3 < 0
  eH : (T.ff 7 (x 6) - T.ff 7 (x 0)) * (N.a * N.r) = -h3 * ((N.b - 1) * (N.p + N.r) - N.a * (N.q - 1))

theorem exists_par (T : Type16 x) : Nonempty (Par T) := by
  let N := T.toNF
  have hq : 0 < N.q := N.hq
  have h0 : T.ff 4 (x 0) = 0 := ff_zero T 4 0 (by decide)
  have h6 : T.ff 4 (x 6) = 0 := ff_zero T 4 6 (by decide)
  have h4 : T.ff 4 (x 4) = 0 := ff_zero T 4 4 (by decide)
  have n3 : T.ff 4 (x 3) < 0 := ff_neg T 4 3 (by decide)
  have f4 := ff_nf T 4 N.x4
  have f1 := ff_nf T 4 N.x1
  have f2 := ff_nf T 4 N.x2
  rw [h4, h0, h6] at f4
  rw [h0, h6] at f1 f2
  have e5 : T.ff 4 (x 5) = T.ff 4 (x 3) * (1 + (N.p + N.r - 1) / N.q) := by
    field_simp
    linear_combination (-1 : ℝ) * f4
  refine ⟨⟨N, T.ff 4 (x 3), n3, rfl, e5, ?_, ?_, T.ff 1 (x 0), ff_neg T 1 0 (by decide), rfl, ?_, ?_,
    T.ff 5 (x 3), ff_neg T 5 3 (by decide), ?_, T.ff 7 (x 3), ff_neg T 7 3 (by decide), ?_⟩⟩
  · rw [f1, e5]; field_simp; ring
  · rw [f2, e5]; field_simp; ring
  · have := ff_nf T 1 N.x4
    rw [ff_zero T 1 3 (by decide), ff_zero T 1 5 (by decide), ff_zero T 1 6 (by decide)] at this
    rw [this]; ring
  · have := ff_nf T 1 N.x2
    rw [ff_zero T 1 3 (by decide), ff_zero T 1 5 (by decide), ff_zero T 1 6 (by decide)] at this
    rw [this]; ring
  · have g1 := ff_nf T 5 N.x1
    have g4 := ff_nf T 5 N.x4
    rw [ff_zero T 5 1 (by decide), ff_zero T 5 5 (by decide)] at g1
    rw [ff_zero T 5 4 (by decide), ff_zero T 5 5 (by decide)] at g4
    linear_combination (-(N.p + N.r)) * g1 + N.d * g4
  · have g2 := ff_nf T 7 N.x2
    have g4 := ff_nf T 7 N.x4
    rw [ff_zero T 7 2 (by decide), ff_zero T 7 5 (by decide)] at g2
    rw [ff_zero T 7 4 (by decide), ff_zero T 7 5 (by decide)] at g4
    linear_combination (-N.a) * g4 + (N.p + N.r) * g2

end H16U
end Minimality
