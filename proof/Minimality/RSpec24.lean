module

public import Minimality.RimCellClosed
public import Minimality.EdgeViewLink
public import Minimality.EdgeTiltBD
public import Minimality.Sym24

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace Topology
open Filter Finset
open Minimality Minimality.H21 Minimality.T24.SAT Minimality.RimCell Minimality.EdgeViewLink
open Minimality.EdgeTilt Minimality.T24.Sym

namespace Minimality.T24.RSpec

private lemma rspec_ev_pos (v b d : ℝ³)
    (h : 0 < ⟪v, b⟫ ∨ (⟪v, b⟫ = 0 ∧ 0 < ⟪v, d⟫)) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ⟪v, b + ε • d⟫ := by
  have := Minimality.eventually_pos_affine (A := ⟪v, b⟫) (B := ⟪v, d⟫) h
  filter_upwards [this] with ε hε
  rw [inner_add_right, inner_smul_right]; exact hε

private lemma rspec_ev_neg (v b d : ℝ³)
    (h : ⟪v, b⟫ < 0 ∨ (⟪v, b⟫ = 0 ∧ ⟪v, d⟫ < 0)) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ⟪v, b + ε • d⟫ < 0 := by
  have := rspec_ev_pos (-v) b d (by
    simp only [inner_neg_left]
    rcases h with h | ⟨h1, h2⟩
    · exact Or.inl (by linarith)
    · exact Or.inr ⟨by linarith, by linarith⟩)
  filter_upwards [this] with ε hε
  simp only [inner_neg_left] at hε; linarith

private lemma rspec_inj_quad {a b c d : Fin 7}
    (h : a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d) :
    Function.Injective (quad a b c d) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> first | rfl | exact absurd hij (by simp [quad]; tauto)

/-- **Lexicographic closed-cell leaf for a 4-rim** (view `u₀`, tilt `d`). The rim facings are
lex-signed at `(u₀, d)` (strict, or zero with the tilt strict), and a negative and a positive
diagonal form of the rim exist at `(u₀, d)` in the same lex sense: Rupert. No genericity, no
injectivity of depths, no unique farthest vertex, no horizontal double normal. -/
theorem rspec_lex_q4 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) {c : ZMod 4 → Fin 7}
    (hc : Function.Injective c) {U Dn : Finset (Fin 9)} (hcyc : S0xCycUD s0x_S24 c U Dn)
    (u₀ d : ℝ³)
    (hU : ∀ t ∈ U, 0 < ⟪F.N t, u₀⟫ ∨ (⟪F.N t, u₀⟫ = 0 ∧ 0 < ⟪F.N t, d⟫))
    (hD : ∀ t ∈ Dn, ⟪F.N t, u₀⟫ < 0 ∨ (⟪F.N t, u₀⟫ = 0 ∧ ⟪F.N t, d⟫ < 0))
    (hn : ∃ p ∈ diagPairs, ⟪x (c p.1) - x (c p.2), u₀⟫ < 0 ∨
      (⟪x (c p.1) - x (c p.2), u₀⟫ = 0 ∧ ⟪x (c p.1) - x (c p.2), d⟫ < 0))
    (hp : ∃ p ∈ diagPairs, 0 < ⟪x (c p.1) - x (c p.2), u₀⟫ ∨
      (⟪x (c p.1) - x (c p.2), u₀⟫ = 0 ∧ 0 < ⟪x (c p.1) - x (c p.2), d⟫)) :
    IsRupert (univ.image x) := by
  obtain ⟨p, hpm, hpn⟩ := hn
  obtain ⟨q, hqm, hqp⟩ := hp
  obtain ⟨ε, ha, hg, hg'⟩ := ((ev_cellAt_tilt F hU hD).and
    ((rspec_ev_neg _ _ _ hpn).and (rspec_ev_pos _ _ _ hqp))).exists
  exact isRupert_of_closedCell_q4 F (inj_of_fac24 F) hc hcyc ha ha.cellLe ha.cellLe
    ⟨p, hpm, hg⟩ ⟨q, hqm, hg'⟩

/-! Cell A: rim `0 2 3 4`, facets `{2,3,6}` up, `{0,4,7,8}` down; view `2 x₅ - x₀ - x₁`, tilt `x₀ - x₁`. -/
def UA : Finset (Fin 9) := {2, 3, 6}
def DA : Finset (Fin 9) := {0, 4, 7, 8}
theorem cycA : S0xCycUD s0x_S24 (quad 0 2 3 4) UA DA := by decide

/-- Special-locus closed-cell leaf A on rim `0 2 3 4` (`u₀ = 2 x₅ - x₀ - x₁`, `d = x₀ - x₁`). -/
theorem rspec_A {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hU : ∀ t ∈ UA, 0 < ⟪F.N t, (x 5 - x 0) + (x 5 - x 1)⟫ ∨
      (⟪F.N t, (x 5 - x 0) + (x 5 - x 1)⟫ = 0 ∧ 0 < ⟪F.N t, x 0 - x 1⟫))
    (hD : ∀ t ∈ DA, ⟪F.N t, (x 5 - x 0) + (x 5 - x 1)⟫ < 0 ∨
      (⟪F.N t, (x 5 - x 0) + (x 5 - x 1)⟫ = 0 ∧ ⟪F.N t, x 0 - x 1⟫ < 0))
    (hn : ∃ p ∈ diagPairs, ⟪x (quad 0 2 3 4 p.1) - x (quad 0 2 3 4 p.2), (x 5 - x 0) + (x 5 - x 1)⟫ < 0 ∨
      (⟪x (quad 0 2 3 4 p.1) - x (quad 0 2 3 4 p.2), (x 5 - x 0) + (x 5 - x 1)⟫ = 0 ∧
        ⟪x (quad 0 2 3 4 p.1) - x (quad 0 2 3 4 p.2), x 0 - x 1⟫ < 0))
    (hp : ∃ p ∈ diagPairs, 0 < ⟪x (quad 0 2 3 4 p.1) - x (quad 0 2 3 4 p.2), (x 5 - x 0) + (x 5 - x 1)⟫ ∨
      (⟪x (quad 0 2 3 4 p.1) - x (quad 0 2 3 4 p.2), (x 5 - x 0) + (x 5 - x 1)⟫ = 0 ∧
        0 < ⟪x (quad 0 2 3 4 p.1) - x (quad 0 2 3 4 p.2), x 0 - x 1⟫)) :
    IsRupert (univ.image x) :=
  rspec_lex_q4 F (rspec_inj_quad (by decide)) cycA _ _ hU hD hn hp

/-! Cell B: rim `0 1 6 4`, facets `{1,4}` up, `{0,3,5,8}` down; view `x₄ - x₃`, tilt `x₁ - x₂`. -/
def UB : Finset (Fin 9) := {1, 4}
def DB : Finset (Fin 9) := {0, 3, 5, 8}
theorem cycB : S0xCycUD s0x_S24 (quad 0 1 6 4) UB DB := by decide

/-- Special-locus closed-cell leaf B on rim `0 1 6 4` (`u₀ = x₄ - x₃`, `d = x₁ - x₂`). -/
theorem rspec_B {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hU : ∀ t ∈ UB, 0 < ⟪F.N t, x 4 - x 3⟫ ∨ (⟪F.N t, x 4 - x 3⟫ = 0 ∧ 0 < ⟪F.N t, x 1 - x 2⟫))
    (hD : ∀ t ∈ DB, ⟪F.N t, x 4 - x 3⟫ < 0 ∨ (⟪F.N t, x 4 - x 3⟫ = 0 ∧ ⟪F.N t, x 1 - x 2⟫ < 0))
    (hn : ∃ p ∈ diagPairs, ⟪x (quad 0 1 6 4 p.1) - x (quad 0 1 6 4 p.2), x 4 - x 3⟫ < 0 ∨
      (⟪x (quad 0 1 6 4 p.1) - x (quad 0 1 6 4 p.2), x 4 - x 3⟫ = 0 ∧
        ⟪x (quad 0 1 6 4 p.1) - x (quad 0 1 6 4 p.2), x 1 - x 2⟫ < 0))
    (hp : ∃ p ∈ diagPairs, 0 < ⟪x (quad 0 1 6 4 p.1) - x (quad 0 1 6 4 p.2), x 4 - x 3⟫ ∨
      (⟪x (quad 0 1 6 4 p.1) - x (quad 0 1 6 4 p.2), x 4 - x 3⟫ = 0 ∧
        0 < ⟪x (quad 0 1 6 4 p.1) - x (quad 0 1 6 4 p.2), x 1 - x 2⟫)) :
    IsRupert (univ.image x) :=
  rspec_lex_q4 F (rspec_inj_quad (by decide)) cycB _ _ hU hD hn hp

/-- Mirror of `rspec_A`: the same statement for `x ∘ pi24` (facets through `sig24`). -/
theorem rspec_A_sym {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hU : ∀ t ∈ UA, 0 < ⟪F.N (sig24 t), (x (pi24 5) - x 0) + (x (pi24 5) - x 1)⟫ ∨
      (⟪F.N (sig24 t), (x (pi24 5) - x 0) + (x (pi24 5) - x 1)⟫ = 0 ∧ 0 < ⟪F.N (sig24 t), x 0 - x 1⟫))
    (hD : ∀ t ∈ DA, ⟪F.N (sig24 t), (x (pi24 5) - x 0) + (x (pi24 5) - x 1)⟫ < 0 ∨
      (⟪F.N (sig24 t), (x (pi24 5) - x 0) + (x (pi24 5) - x 1)⟫ = 0 ∧ ⟪F.N (sig24 t), x 0 - x 1⟫ < 0))
    (hn : ∃ p ∈ diagPairs, ⟪x (pi24 (quad 0 2 3 4 p.1)) - x (pi24 (quad 0 2 3 4 p.2)),
        (x (pi24 5) - x 0) + (x (pi24 5) - x 1)⟫ < 0 ∨
      (⟪x (pi24 (quad 0 2 3 4 p.1)) - x (pi24 (quad 0 2 3 4 p.2)),
        (x (pi24 5) - x 0) + (x (pi24 5) - x 1)⟫ = 0 ∧
        ⟪x (pi24 (quad 0 2 3 4 p.1)) - x (pi24 (quad 0 2 3 4 p.2)), x 0 - x 1⟫ < 0))
    (hp : ∃ p ∈ diagPairs, 0 < ⟪x (pi24 (quad 0 2 3 4 p.1)) - x (pi24 (quad 0 2 3 4 p.2)),
        (x (pi24 5) - x 0) + (x (pi24 5) - x 1)⟫ ∨
      (⟪x (pi24 (quad 0 2 3 4 p.1)) - x (pi24 (quad 0 2 3 4 p.2)),
        (x (pi24 5) - x 0) + (x (pi24 5) - x 1)⟫ = 0 ∧
        0 < ⟪x (pi24 (quad 0 2 3 4 p.1)) - x (pi24 (quad 0 2 3 4 p.2)), x 0 - x 1⟫)) :
    IsRupert (univ.image x) :=
  isRupert_of_comp_pi24 (rspec_A (sym24 F) hU hD hn hp)

/-- Mirror of `rspec_B`: the same statement for `x ∘ pi24` (facets through `sig24`). -/
theorem rspec_B_sym {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hU : ∀ t ∈ UB, 0 < ⟪F.N (sig24 t), x (pi24 4) - x (pi24 3)⟫ ∨
      (⟪F.N (sig24 t), x (pi24 4) - x (pi24 3)⟫ = 0 ∧ 0 < ⟪F.N (sig24 t), x (pi24 1) - x (pi24 2)⟫))
    (hD : ∀ t ∈ DB, ⟪F.N (sig24 t), x (pi24 4) - x (pi24 3)⟫ < 0 ∨
      (⟪F.N (sig24 t), x (pi24 4) - x (pi24 3)⟫ = 0 ∧ ⟪F.N (sig24 t), x (pi24 1) - x (pi24 2)⟫ < 0))
    (hn : ∃ p ∈ diagPairs, ⟪x (pi24 (quad 0 1 6 4 p.1)) - x (pi24 (quad 0 1 6 4 p.2)),
        x (pi24 4) - x (pi24 3)⟫ < 0 ∨
      (⟪x (pi24 (quad 0 1 6 4 p.1)) - x (pi24 (quad 0 1 6 4 p.2)), x (pi24 4) - x (pi24 3)⟫ = 0 ∧
        ⟪x (pi24 (quad 0 1 6 4 p.1)) - x (pi24 (quad 0 1 6 4 p.2)), x (pi24 1) - x (pi24 2)⟫ < 0))
    (hp : ∃ p ∈ diagPairs, 0 < ⟪x (pi24 (quad 0 1 6 4 p.1)) - x (pi24 (quad 0 1 6 4 p.2)),
        x (pi24 4) - x (pi24 3)⟫ ∨
      (⟪x (pi24 (quad 0 1 6 4 p.1)) - x (pi24 (quad 0 1 6 4 p.2)), x (pi24 4) - x (pi24 3)⟫ = 0 ∧
        0 < ⟪x (pi24 (quad 0 1 6 4 p.1)) - x (pi24 (quad 0 1 6 4 p.2)), x (pi24 1) - x (pi24 2)⟫)) :
    IsRupert (univ.image x) :=
  isRupert_of_comp_pi24 (rspec_B (sym24 F) hU hD hn hp)

/-! ## Case bundles for `Type24Hole` -/

/-- Case bundle for `rspec_A`. -/
def H_specA {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  (∀ t ∈ UA, 0 < ⟪F.N t, (x 5 - x 0) + (x 5 - x 1)⟫ ∨
    (⟪F.N t, (x 5 - x 0) + (x 5 - x 1)⟫ = 0 ∧ 0 < ⟪F.N t, x 0 - x 1⟫)) ∧
  (∀ t ∈ DA, ⟪F.N t, (x 5 - x 0) + (x 5 - x 1)⟫ < 0 ∨
    (⟪F.N t, (x 5 - x 0) + (x 5 - x 1)⟫ = 0 ∧ ⟪F.N t, x 0 - x 1⟫ < 0)) ∧
  (∃ p ∈ diagPairs, ⟪x (quad 0 2 3 4 p.1) - x (quad 0 2 3 4 p.2), (x 5 - x 0) + (x 5 - x 1)⟫ < 0 ∨
    (⟪x (quad 0 2 3 4 p.1) - x (quad 0 2 3 4 p.2), (x 5 - x 0) + (x 5 - x 1)⟫ = 0 ∧
      ⟪x (quad 0 2 3 4 p.1) - x (quad 0 2 3 4 p.2), x 0 - x 1⟫ < 0)) ∧
  (∃ p ∈ diagPairs, 0 < ⟪x (quad 0 2 3 4 p.1) - x (quad 0 2 3 4 p.2), (x 5 - x 0) + (x 5 - x 1)⟫ ∨
    (⟪x (quad 0 2 3 4 p.1) - x (quad 0 2 3 4 p.2), (x 5 - x 0) + (x 5 - x 1)⟫ = 0 ∧
      0 < ⟪x (quad 0 2 3 4 p.1) - x (quad 0 2 3 4 p.2), x 0 - x 1⟫))

/-- Case bundle for `rspec_A_sym`. -/
def H_specA_sym {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  H_specA (sym24 F)

/-- Case bundle for `rspec_B`. -/
def H_specB {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  (∀ t ∈ UB, 0 < ⟪F.N t, x 4 - x 3⟫ ∨ (⟪F.N t, x 4 - x 3⟫ = 0 ∧ 0 < ⟪F.N t, x 1 - x 2⟫)) ∧
  (∀ t ∈ DB, ⟪F.N t, x 4 - x 3⟫ < 0 ∨ (⟪F.N t, x 4 - x 3⟫ = 0 ∧ ⟪F.N t, x 1 - x 2⟫ < 0)) ∧
  (∃ p ∈ diagPairs, ⟪x (quad 0 1 6 4 p.1) - x (quad 0 1 6 4 p.2), x 4 - x 3⟫ < 0 ∨
    (⟪x (quad 0 1 6 4 p.1) - x (quad 0 1 6 4 p.2), x 4 - x 3⟫ = 0 ∧
      ⟪x (quad 0 1 6 4 p.1) - x (quad 0 1 6 4 p.2), x 1 - x 2⟫ < 0)) ∧
  (∃ p ∈ diagPairs, 0 < ⟪x (quad 0 1 6 4 p.1) - x (quad 0 1 6 4 p.2), x 4 - x 3⟫ ∨
    (⟪x (quad 0 1 6 4 p.1) - x (quad 0 1 6 4 p.2), x 4 - x 3⟫ = 0 ∧
      0 < ⟪x (quad 0 1 6 4 p.1) - x (quad 0 1 6 4 p.2), x 1 - x 2⟫))

/-- Case bundle for `rspec_B_sym`. -/
def H_specB_sym {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  H_specB (sym24 F)

/-- Disjunction of the four special-locus closed-cell bundles. -/
def HSpecAny {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  H_specA F ∨ H_specA_sym F ∨ H_specB F ∨ H_specB_sym F

/-- Any of the four `RSpec` bundles closes the solid as Rupert. -/
theorem rspec_closes {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (h : HSpecAny F) :
    IsRupert (univ.image x) := by
  rcases h with hA | hAs | hB | hBs
  · exact rspec_A F hA.1 hA.2.1 hA.2.2.1 hA.2.2.2
  · exact isRupert_of_comp_pi24 (rspec_A (sym24 F) hAs.1 hAs.2.1 hAs.2.2.1 hAs.2.2.2)
  · exact rspec_B F hB.1 hB.2.1 hB.2.2.1 hB.2.2.2
  · exact isRupert_of_comp_pi24 (rspec_B (sym24 F) hBs.1 hBs.2.1 hBs.2.2.1 hBs.2.2.2)

end Minimality.T24.RSpec
