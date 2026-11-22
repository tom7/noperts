module

public import Minimality.Type29T1Pair

@[expose] public section

/-!
# Type 29, `t = 1` close: `V46` failure gives `A_46`, then `W14` closes

`u46` (Type29T1Pair) is definitionally the view `u2346` of the existing exact `F023xF346` leaf
(`lexAny29_U2346`), so `u46_eq_u2346` is `rfl`. The leaf is a `LexAny29` leaf outside
`M_{23,46} = {z0, z4 <= z1, z3 ...}`; its region contains `z4 <= z1` as one conjunct, hence
`v46_fail`: if the leaf's other hypotheses hold and `LexAny29` fails, then `A_46 : z4(u46) <= z1(u46)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.Gen Minimality.LexCell Minimality.H21

namespace Minimality.NF29

variable {x : Fin 7 → ℝ³}

theorem u46_eq_u2346 (N : NF29 x) : N.u46 x = N.u2346 x := rfl

/-- If the `V46 = F023xF346` leaf's non-region hypotheses hold and `LexAny29` fails, then
`A_46`: `z4(u46) <= z1(u46)`. -/
theorem v46_fail (N : NF29 x) (hdG4 : 0 < N.dG4)
    (h012 : 0 < N.f012.f (x 3 + N.u2346 x) - N.f012.f (x 3))
    (h015 : N.f015.f (x 3 + N.u2346 x) - N.f015.f (x 3) < 0)
    (h035 : N.f035.f (x 3 + N.u2346 x) - N.f035.f (x 3) < 0)
    (h124 : 0 < N.f124.f (x 3 + N.u2346 x) - N.f124.f (x 3))
    (h1456 : N.f1456.f (x 3 + N.u2346 x) - N.f1456.f (x 3) < 0)
    (h234 : 0 < N.f234.f (x 3 + N.u2346 x) - N.f234.f (x 3))
    (h356 : N.f356.f (x 3 + N.u2346 x) - N.f356.f (x 3) < 0)
    (lam mu eta : ℝ) (hlam0 : 0 < lam) (hlam1 : lam < 1) (hmu0 : 0 < mu) (hmu1 : mu < 1)
    (heta : 0 < eta)
    (hfront : lam • x 1 + (1 - lam) • x 3 = mu • x 0 + (1 - mu) • x 4 + eta • N.u2346 x)
    (hnf : ¬ Minimality.H29.LexAny29 (s0x_fac29 N.facets)) :
    ⟪x 4 - x 6, N.u46 x⟫ ≤ ⟪x 1 - x 6, N.u46 x⟫ := by
  by_contra h
  push Not at h
  apply hnf
  refine lexAny29_U2346 N hdG4 h012 h015 h035 h124 h1456 h234 h356 lam mu eta hlam0 hlam1 hmu0 hmu1
    heta hfront ?_
  rintro ⟨-, h41, -, -⟩
  rw [inner_sub_left, inner_sub_left] at h
  have h41' : ⟪x 4, N.u46 x⟫ ≤ ⟪x 1, N.u46 x⟫ := h41
  have h' : ⟪x 1, N.u46 x⟫ - ⟪x 6, N.u46 x⟫ < ⟪x 4, N.u46 x⟫ - ⟪x 6, N.u46 x⟫ := h
  linarith

/-- **`t = 1` closed** on the K1a cell (`hdG4`, `hA`, `hU5`), weak `OB6` at vertex 6 (`hg35`, `hg45`),
`hsD` (named sample fact, FALSE as a region fact: see report), and the `V46` leaf hypotheses. -/
theorem t1_closed (N : NF29 x) (ht : N.t = 1)
    (hdG4 : 0 < N.dG4) (hA : 0 < 1 - N.b0 - N.h0) (hU5 : 0 < N.DG4 - N.D023)
    (hsD : N.s < 1 ∨ N.D234 < 1)
    (hg35 : ⟪x 3 - x 6, x 5 - x 6⟫ ≤ 0) (hg45 : ⟪x 4 - x 6, x 5 - x 6⟫ ≤ 0)
    (h012 : 0 < N.f012.f (x 3 + N.u2346 x) - N.f012.f (x 3))
    (h015 : N.f015.f (x 3 + N.u2346 x) - N.f015.f (x 3) < 0)
    (h035 : N.f035.f (x 3 + N.u2346 x) - N.f035.f (x 3) < 0)
    (h124 : 0 < N.f124.f (x 3 + N.u2346 x) - N.f124.f (x 3))
    (h1456 : N.f1456.f (x 3 + N.u2346 x) - N.f1456.f (x 3) < 0)
    (h234 : 0 < N.f234.f (x 3 + N.u2346 x) - N.f234.f (x 3))
    (h356 : N.f356.f (x 3 + N.u2346 x) - N.f356.f (x 3) < 0)
    (lam mu eta : ℝ) (hlam0 : 0 < lam) (hlam1 : lam < 1) (hmu0 : 0 < mu) (hmu1 : mu < 1)
    (heta : 0 < eta)
    (hfront : lam • x 1 + (1 - lam) • x 3 = mu • x 0 + (1 - mu) • x 4 + eta • N.u2346 x)
    (hnf : ¬ Minimality.H29.LexAny29 (s0x_fac29 N.facets)) : False :=
  hnf (lexAny29_W14_of_V46 N ht hdG4 hA hU5 hsD hg35 hg45
    (v46_fail N hdG4 h012 h015 h035 h124 h1456 h234 h356 lam mu eta hlam0 hlam1 hmu0 hmu1 heta hfront hnf))

end Minimality.NF29
