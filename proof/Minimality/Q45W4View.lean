module

public import Minimality.Q45B2View

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21 Minimality.LexCell Minimality.T24.SAT

/-!
# The wall view `(-e4, e26, -e5)` for the corner sub-branch on the wall `a4 = 1` (job OSPEC7)

nopert229 notes/OPENSPECIAL-STRATEGY.md.  On the wall `a4 = oblX0 x 4 = 1` the facet `126` is parallel to `e4 =
x 4 - x 0` (`⟪N5, e4⟫ = 0`), so the corner cell `C1` (view `-e4 + ε e5`) loses its `126` sign.  The 3-level lex view
`(x 0 - x 4, x 2 - x 6, x 0 - x 5)` keeps the corner base `-e4` and breaks the tie of `126` inside its own plane
(`x 2 - x 6` lies in `126`), so `126` is decided at the third level by `⟪N5, x 0 - x 5⟫ = f5(x 0) - f5(x 5)`, positive
off the double wall (`a5 > 1`).  Rim `0 5 2 6`; facets `012 016 025 126` up, `0345 046 235 236 346` down.
Automatic for every type-24 solid (`w4_up_of_mem`, `w4_dn4`, `w4_dn8`): `012 016 025` up and `346` down at level 1
(`0` in the facet, `4` not, resp. the reverse), `046` down at level 2 (`6` in it, `2` not).  `W4ViewOK` asks for the
other four facet signs and `RobUniLex` of the rim; `lexAny_of_w4View` makes it a lex cell.  The mirror `π = (2 6)(4 5)`
(`Sym24Transport.lean`) gives the view `(-e5, -e26, -e4)` on the wall `a5 = 1` (`lexAny_of_w4View_sym`).
-/

namespace Minimality.T24.Q45

variable {x : Fin 7 → ℝ³}

/-- Rim `0 5 2 6` (facets `0 1 2 5` up, `3 4 6 7 8` down). -/
def rimW4 : ZMod 4 → Fin 7 := ![0, 5, 2, 6]
def UW4 : Finset (Fin 9) := {0, 1, 2, 5}
def DnW4 : Finset (Fin 9) := {3, 4, 6, 7, 8}

theorem rimW4_cyc : S0xCycUD s0x_S24 rimW4 UW4 DnW4 := by decide
theorem rimW4_inj : Function.Injective rimW4 := by decide

/-- Facet `t` is up in the lex view `(x 0 - x 4, x 2 - x 6, x 0 - x 5)`. -/
def W4Up {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (t : Fin 9) : Prop :=
  LexPos3 ⟪F.N t, x 0 - x 4⟫ ⟪F.N t, x 2 - x 6⟫ ⟪F.N t, x 0 - x 5⟫
/-- Facet `t` is down in the lex view `(x 0 - x 4, x 2 - x 6, x 0 - x 5)`. -/
def W4Dn {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (t : Fin 9) : Prop :=
  LexPos3 (-⟪F.N t, x 0 - x 4⟫) (-⟪F.N t, x 2 - x 6⟫) (-⟪F.N t, x 0 - x 5⟫)

/-- Lex depth triples of a rim in the view `(x 0 - x 4, x 2 - x 6, x 0 - x 5)`. -/
noncomputable def w4Z {x : Fin 7 → ℝ³} (_F : S0xFac 9 s0x_S24 x) (c : ZMod 4 → Fin 7) : ZMod 4 → ℝ × ℝ × ℝ :=
  fun i => (⟪x (c i), x 0 - x 4⟫, ⟪x (c i), x 2 - x 6⟫, ⟪x (c i), x 0 - x 5⟫)

/-- **The wall view condition**: `0345 235 236` down, `126` up, and the rim `0 5 2 6` `RobUniLex` in the lex order
`(x 0 - x 4, x 2 - x 6, x 0 - x 5)` (the other five facet signs are automatic). -/
def W4ViewOK {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  W4Dn F 3 ∧ W4Up F 5 ∧ W4Dn F 6 ∧ W4Dn F 7 ∧ RobUniLex (w4Z F rimW4)

/-- A facet through `0` but not `4` is up (level 1). -/
theorem w4_up_of_mem (F : S0xFac 9 s0x_S24 x) (t : Fin 9) (h0 : (0 : Fin 7) ∈ s0x_S24 t)
    (h4 : (4 : Fin 7) ∉ s0x_S24 t) : W4Up F t := by
  left
  rw [F.inner_sub t 0 4, F.zero t 0 h0]
  linarith [F.neg t 4 h4]

/-- The facet `346` is down (level 1: `4` in it, `0` not). -/
theorem w4_dn8 (F : S0xFac 9 s0x_S24 x) : W4Dn F 8 := by
  left
  rw [F.inner_sub 8 0 4, F.zero 8 4 (by decide)]
  linarith [F.neg 8 0 (by decide)]

/-- The facet `046` is down (level 1 zero: `0`, `4` in it; level 2: `6` in it, `2` not). -/
theorem w4_dn4 (F : S0xFac 9 s0x_S24 x) : W4Dn F 4 := by
  right
  refine ⟨?_, Or.inl ?_⟩
  · rw [F.inner_sub 4 0 4, F.zero 4 0 (by decide), F.zero 4 4 (by decide)]; ring
  · rw [F.inner_sub 4 2 6, F.zero 4 6 (by decide)]
    linarith [F.neg 4 2 (by decide)]

/-- **The wall view is a lex cell.** -/
theorem lexAny_of_w4View (F : S0xFac 9 s0x_S24 x) (h : W4ViewOK F) : Gen.LexAny F := by
  obtain ⟨h3, h5, h6, h7, hR⟩ := h
  refine ⟨4, inferInstance, rimW4, UW4, DnW4, x 0 - x 4, x 2 - x 6, x 0 - x 5, le_refl _, rimW4_inj,
    rimW4_cyc, ?_, ?_, hR⟩
  · intro t ht
    simp only [UW4, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl
    exacts [w4_up_of_mem F 0 (by decide) (by decide), w4_up_of_mem F 1 (by decide) (by decide),
      w4_up_of_mem F 2 (by decide) (by decide), h5]
  · intro t ht
    simp only [DnW4, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    exacts [h3, w4_dn4 F, h6, h7, w4_dn8 F]

/-- **The `a5 = 1` form** (mirror `π = (2 6)(4 5)`): the wall view of the mirrored solid, i.e. the view
`(x 0 - x 5, x 6 - x 2, x 0 - x 4)` of `x`, is a lex cell of `x`. -/
theorem lexAny_of_w4View_sym (F : S0xFac 9 s0x_S24 x) (h : W4ViewOK (Sym.sym24 F)) : Gen.LexAny F :=
  Sym.lexAny_sym F (lexAny_of_w4View (Sym.sym24 F) h)

end Minimality.T24.Q45
