module

public import Minimality.Type08S.P2FinalH

@[expose] public section

set_option relaxedAutoImplicit true
/-!
# pkQ / PQDefs: definitions for package P5 (planar equators, `κ = 0`).  No sorry.
Compile with `leanchk PQDefs.lean -o`.

The weak labelling is the tree's `Norm08w` (`P2Defs`: `κ_a, κ_b ≥ 0`, `[b c] ≤ 0`, no condition on `κ_c`).
`[b c] ≤ 0` is the same as `< 0` (`[b c] = μ·gWU` with `gWU < 0` and `μ ≠ 0`; package Q0 proves
`Norm08w.hU_lt`).

**Leftovers (map.md §4).**  Codimensions in the convention of plan2/map.md (`T`, `T'`, a planar equator,
a tie, an HDN at a fixed view: 1 each).
* `LeftTT` — planar, at `T` or `T'`: the T4 weak far triple (`TouchT`), or the robust `K_b` / `K_2` corner rim
  of the refined limit theorem carries its own HDN.  Codim 3 (planar + T + HDN; `T ∩ T'` is codim 2 and
  planar automatically, + HDN = 3); `TouchT` is ≥ 4.
* `ParEnd` with `κ_a = 0` — off `T`, `T'`: a persistent HDN of a robust closing whose top side is parallel to the
  closing's face (`Yr = Yg`) and either lies over the chord's line (`Par5`) or passes over `f̄` (`CEf5`).
  `κ_a = 0` + `Yr = Yg` + (one more) = codim 3.  These are exactly the two places where `P3` uses strict
  Lemma E (`P2H13.lemE_strict`, via `SC2*_of_CEf` and `P2CE2.cef_*`).
-/

set_option autoImplicit true
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

/-! ## Normal form on the closure -/

/-- The culJ region of `Norm08w`: entries 0–8, 12–23 of `ineq08` strict, `gWa, gWb ≥ 0` (entries 9–11 dropped). -/
def Ineq08w (θ : Fin 6 → ℝ) : Prop :=
  (∀ k : Fin 24, k ≠ 9 → k ≠ 10 → k ≠ 11 → 0 < ineq08 θ k) ∧ 0 ≤ gWa θ ∧ 0 ≤ gWb θ

/-- Closure of the T4 region (`γ6 ≤ 1 ≤ α1` in culJ). -/
def T4cl {a a' b b' c c' : ℝ³} (F : OctFacets a a' b b' c c') : Prop :=
  F.abc'.f c ≤ F.abc'.f a' ∧ F.a'bc.f c' ≤ F.a'bc.f a

/-- A planar equator (some Gale `κ` vanishes), in point form: one of the three equators is planar. -/
def PlanarEq (a a' b b' c c' : ℝ³) : Prop :=
  det3 (c - b) (b' - b) (c' - b) = 0 ∨ det3 (c - a) (a' - a) (c' - a) = 0 ∨ det3 (b - a) (a' - a) (b' - a) = 0

/-! ## Leftover at `T ∨ T'` (refined limit theorem on the T4 closure) -/

/-- **`LeftTT`**: at `T` or `T'`, the T4 weak far triple, or the robust `K_b` (resp. `K_2`, `K_b` not robust)
corner rim of the limit theorem has its own HDN. -/
def LeftTT (a a' b b' c c' d : ℝ³) : Prop :=
  (IsT a' b c d ∨ IsT' a b c' d) ∧
    (TouchT b b' c c' d ∨
      (RobKb a a' b b' c c' d ∧ ∃ s, RobHDN a a' b b' c c' d (1, s, true)) ∨
      (¬ RobKb a a' b b' c c' d ∧ ∃ s, RobHDN a a' b b' c c' d (1, s, false)))

/-! ## Leftover off `T`, `T'` (P3 where strict Lemma E was used) -/

/-- Frame numbers of a persistent HDN with a top side parallel to the face (`Yr = Yg`) over the chord's line
(`Par5`) or over `f̄` (`CEf5`). -/
def ParEnd5 (L zx zf Xr Yr zr Xg Yg zg : ℝ) : Prop :=
  Yr = Yg ∧ (CEf5 L zx zf Xr Yr zr Xg Yg zg ∨ Par5 L zx zf Xr Yr zr Xg Yg zg)

/-- `ParEnd5` for N2's `K_c` in the canonical frame of `SC2N2` (`x' = a'`, `x = c`, `f = b`, `r = c'`, `g = b'`). -/
def ParEndN2 (a a' b b' c c' : ℝ³) : Prop :=
  ∃ (e1 e2 e3 : ℝ³) (κ : ℝ), Fr e1 e2 e3 ∧ κ ≠ 0 ∧ c - a' = κ • e3 ∧ ⟪b - a', e2⟫ = 0 ∧
    0 < ⟪b - a', e1⟫ ∧ 0 < ⟪c' - a', e2⟫ ∧ Rob4 κ ⟪b - a', e3⟫ ⟪c' - a', e3⟫ ⟪b' - a', e3⟫ ∧
    ParEnd5 ⟪b - a', e1⟫ κ ⟪b - a', e3⟫ ⟪c' - a', e1⟫ ⟪c' - a', e2⟫ ⟪c' - a', e3⟫ ⟪b' - a', e1⟫ ⟪b' - a', e2⟫
      ⟪b' - a', e3⟫

/-- `ParEnd5` for T4's `K_b` in the canonical frame of `SC2Kb` (`x' = d`, `x = b`, `f = c`, `r = b'`, `g = c'`). -/
def ParEndKb (b b' c c' d : ℝ³) : Prop :=
  ∃ (e1 e2 e3 : ℝ³) (κ : ℝ), Fr e1 e2 e3 ∧ κ ≠ 0 ∧ b - d = κ • e3 ∧ ⟪c - d, e2⟫ = 0 ∧
    0 < ⟪c - d, e1⟫ ∧ 0 < ⟪b' - d, e2⟫ ∧ Rob4 κ ⟪c - d, e3⟫ ⟪b' - d, e3⟫ ⟪c' - d, e3⟫ ∧
    ParEnd5 ⟪c - d, e1⟫ κ ⟪c - d, e3⟫ ⟪b' - d, e1⟫ ⟪b' - d, e2⟫ ⟪b' - d, e3⟫ ⟪c' - d, e1⟫ ⟪c' - d, e2⟫
      ⟪c' - d, e3⟫

/-- `ParEnd5` for T4's `K_2` in the canonical frame of `SC2K2` (`x' = b`, `x = d`, `f = c'`, `r = b'`, `g = c`). -/
def ParEndK2 (b b' c c' d : ℝ³) : Prop :=
  ∃ (e1 e2 e3 : ℝ³) (κ : ℝ), Fr e1 e2 e3 ∧ κ ≠ 0 ∧ d - b = κ • e3 ∧ ⟪c' - b, e2⟫ = 0 ∧
    0 < ⟪c' - b, e1⟫ ∧ 0 < ⟪b' - b, e2⟫ ∧ Rob4 κ ⟪c' - b, e3⟫ ⟪b' - b, e3⟫ ⟪c - b, e3⟫ ∧
    ParEnd5 ⟪c' - b, e1⟫ κ ⟪c' - b, e3⟫ ⟪b' - b, e1⟫ ⟪b' - b, e2⟫ ⟪b' - b, e3⟫ ⟪c - b, e1⟫ ⟪c - b, e2⟫
      ⟪c - b, e3⟫

/-- **`ParEnd`** (one of the three closings).  Used with `κ_a = 0` (`det3 (c - b) (b' - b) (c' - b) = 0`). -/
def ParEnd (a a' b b' c c' d : ℝ³) : Prop :=
  ParEndN2 a a' b b' c c' ∨ ParEndKb b b' c c' d ∨ ParEndK2 b b' c c' d

/-! ## The planar residual and the new top-level residual -/

/-- **The planar leftover in one labelling** (codim ≥ 3, see the header). -/
def ResP (a a' b b' c c' d : ℝ³) : Prop :=
  LeftTT a a' b b' c c' d ∨ (det3 (c - b) (b' - b) (c' - b) = 0 ∧ ParEnd a a' b b' c c' d)

/-- `ResP` in a labelling that carries a `Norm08w` structure. -/
def ResidP (a a' b b' c c' d : ℝ³) : Prop := ∃ _ : Norm08w a a' b b' c c' d, ResP a a' b b' c c' d

/-- The planar residual in one of the six labellings. -/
def ResidP6 (a a' b b' c c' d : ℝ³) : Prop :=
  ResidP a a' b b' c c' d ∨ ResidP b b' a a' c c' d ∨ ResidP a a' c c' b b' d ∨
  ResidP c c' a a' b b' d ∨ ResidP b b' c c' a a' d ∨ ResidP c c' b b' a a' d

/-- **`Resid08FinalI`**: `Resid08FinalH` with the planar items `PlanarTwo ∨ PlanarGen` cut down by the weak
pipeline to `ResidP6` (the old-route failure is kept as a conjunct, so `I ⊆ H`). -/
def Resid08FinalI (a a' b b' c c' d : ℝ³) : Prop :=
  ((PlanarTwo a a' b b' c c' ∨ PlanarGen a a' b b' c c' d) ∧ ResidP6 a a' b b' c c' d) ∨
  ResidNH a a' b b' c c' d ∨ ResidNH b b' a a' c c' d ∨ ResidNH a a' c c' b b' d ∨
  ResidNH c c' a a' b b' d ∨ ResidNH b b' c c' a a' d ∨ ResidNH c c' b b' a a' d

/-- `I ⊆ H`. -/
theorem resid08FinalI_imp_H {a a' b b' c c' d : ℝ³} (h : Resid08FinalI a a' b b' c c' d) :
    Resid08FinalH a a' b b' c c' d := by
  rcases h with ⟨hp | hp, -⟩ | h | h | h | h | h | h
  · exact Or.inl hp
  · exact Or.inr (Or.inl hp)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))

end Type08Sp
end Minimality
