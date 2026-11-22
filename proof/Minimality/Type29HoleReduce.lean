module

public import Minimality.Type29Hole
public import Minimality.Type29T1Close

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.Gen Minimality.H21 Minimality.H29K1 Minimality.H29S Minimality.NF29

namespace Minimality.H29

/-!
# Type 29: Reduction of `Hole29` to `Hole29'`

Excludes the `t = 1` K1a cell closed by `NF29.t1_closed` (`T1Hyp`) from `Hole29`, yielding
`Hole29' x N := Hole29 x N ∧ ¬ T1Hyp x N`.
-/

/-- Hypothesis bundle for `NF29.t1_closed` (excluding `OB6`'s `hg35, hg45` and `¬ LexAny29`,
which are already supplied by `Hole29`). -/
def T1Hyp (x : Fin 7 → ℝ³) (N : NF29 x) : Prop :=
  N.t = 1 ∧ 0 < N.dG4 ∧ 0 < 1 - N.b0 - N.h0 ∧ 0 < N.DG4 - N.D023 ∧
    (N.s < 1 ∨ N.D234 < 1) ∧
    0 < N.f012.f (x 3 + N.u2346 x) - N.f012.f (x 3) ∧
    N.f015.f (x 3 + N.u2346 x) - N.f015.f (x 3) < 0 ∧
    N.f035.f (x 3 + N.u2346 x) - N.f035.f (x 3) < 0 ∧
    0 < N.f124.f (x 3 + N.u2346 x) - N.f124.f (x 3) ∧
    N.f1456.f (x 3 + N.u2346 x) - N.f1456.f (x 3) < 0 ∧
    0 < N.f234.f (x 3 + N.u2346 x) - N.f234.f (x 3) ∧
    N.f356.f (x 3 + N.u2346 x) - N.f356.f (x 3) < 0 ∧
    ∃ lam mu eta : ℝ, 0 < lam ∧ lam < 1 ∧ 0 < mu ∧ mu < 1 ∧ 0 < eta ∧
      lam • x 1 + (1 - lam) • x 3 = mu • x 0 + (1 - mu) • x 4 + eta • N.u2346 x

/-- Shrunken Type-29 open hole proposition, excluding `T1Hyp`. -/
def Hole29' (x : Fin 7 → ℝ³) (N : NF29 x) : Prop :=
  Hole29 x N ∧ ¬ T1Hyp x N

/-- Every point of `Hole29'` lies in `Hole29`. -/
theorem hole29_of_hole29' {x : Fin 7 → ℝ³} {N : NF29 x} (h : Hole29' x N) : Hole29 x N :=
  h.1

/-- **Reduction of `Hole29` to `Hole29'`**: `NF29.t1_closed` rules out `T1Hyp` inside `Hole29`. -/
theorem hole29_reduce {x : Fin 7 → ℝ³} {N : NF29 x} (h : Hole29 x N) : Hole29' x N := by
  refine ⟨h, fun hT => ?_⟩
  rcases hT with ⟨ht, hdG4, hA, hU5, hsD, h012, h015, h035, h124, h1456, h234, h356,
    lam, mu, eta, hlam0, hlam1, hmu0, hmu1, heta, hfront⟩
  exact t1_closed N ht hdG4 hA hU5 hsD h.2.2.1.2.1 h.2.2.1.2.2
    h012 h015 h035 h124 h1456 h234 h356 lam mu eta hlam0 hlam1 hmu0 hmu1 heta hfront
    h.2.2.2.2.2.1

/-- Main Type-29 reduction leaving `Hole29'`. -/
theorem type29_rupert_or_hole' {x : Fin 7 → ℝ³} (N : NF29 x)
    (hK1 : K1_29 N) (hZ : ¬ Z29 x) (hOB : OB6 x) :
    IsRupert (univ.image x) ∨ Hole29' x N :=
  (type29_rupert_or_hole N hK1 hZ hOB).elim Or.inl (fun h => Or.inr (hole29_reduce h))

end Minimality.H29
