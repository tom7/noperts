module

public import Minimality.Type16ArcB
public import Minimality.SilS0XB

@[expose] public section


set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace H16A
open Minimality.H21 Minimality.H16U Minimality.V2

variable {x : Fin 7 → ℝ³}

/-- Robust version of `H16ALeaf`: `Uni` weakened to `RobUni` (no weak alternating quadruple). -/
def H16A2Leaf (T : Type16 x) {k : ℕ} [NeZero k] (c : ZMod k → Fin 7) (ea eb : ZMod k → Fin 8)
    (u : ℝ³) : Prop :=
  ((∀ i, 0 < ⟪T.fN (ea i), u⟫) ∧ (∀ i, ⟪T.fN (eb i), u⟫ < 0) ∨
    (∀ i, 0 < ⟪T.fN (eb i), u⟫) ∧ (∀ i, ⟪T.fN (ea i), u⟫ < 0)) ∧ RobUni (fun i => ⟪x (c i), u⟫)

theorem h16a2_leaf_of {k : ℕ} [NeZero k] (T : Type16 x) (c : ZMod k → Fin 7) (ea eb : ZMod k → Fin 8)
    (u : ℝ³) (h : H16ALeaf T c ea eb u) : H16A2Leaf T c ea eb u :=
  ⟨h.1, s0x_robUni_of_uni h.2⟩

/-- **The robust arc leaf shape**. -/
theorem h16a2_leaf_gen {k : ℕ} [NeZero k] (T : Type16 x) (hk : 3 ≤ k) (c : ZMod k → Fin 7)
    (hc : Function.Injective c) (ea eb : ZMod k → Fin 8) (u : ℝ³)
    (h0 : ∀ i, c i ∈ fIdx (ea i) ∧ c i ∈ fIdx (eb i))
    (h1 : ∀ i, c (i + 1) ∈ fIdx (ea i) ∧ c (i + 1) ∈ fIdx (eb i))
    (hs : ∀ i m, m ≠ c i → m ≠ c (i + 1) → m ∉ fIdx (ea i) ∨ m ∉ fIdx (eb i))
    (h : H16A2Leaf T c ea eb u) : IsRupert (univ.image x) := by
  rcases h with ⟨⟨hu, hd⟩ | ⟨hu, hd⟩, hU⟩
  · exact s0x_sil_isRupert_rob hk T.inj hc (h16a_sil T c ea eb u h0 h1 hs hu hd) hU
  · exact s0x_sil_isRupert_rob hk T.inj hc
      (h16a_sil T c eb ea u (fun i => (h0 i).symm) (fun i => (h1 i).symm)
        (fun i m a b => (hs i m a b).symm) hu hd) hU

end H16A
end Minimality
