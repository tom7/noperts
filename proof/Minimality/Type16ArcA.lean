module

public import Minimality.Type16VW
public import Minimality.Type21SilE

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

/-- Silhouette data of type 16 along a cycle `c` at any view `u`: edge `i` lies in the facets
`ea i` (facing up) and `eb i` (facing down). -/
noncomputable def h16a_sil {k : ℕ} (T : Type16 x) (c : ZMod k → Fin 7) (ea eb : ZMod k → Fin 8)
    (u : ℝ³)
    (h0 : ∀ i, c i ∈ fIdx (ea i) ∧ c i ∈ fIdx (eb i))
    (h1 : ∀ i, c (i + 1) ∈ fIdx (ea i) ∧ c (i + 1) ∈ fIdx (eb i))
    (hs : ∀ i m, m ≠ c i → m ≠ c (i + 1) → m ∉ fIdx (ea i) ∨ m ∉ fIdx (eb i))
    (hup : ∀ i, 0 < ⟪T.fN (ea i), u⟫) (hdn : ∀ i, ⟪T.fN (eb i), u⟫ < 0) :
    SilData k x c u where
  A i := T.fN (ea i)
  B i := T.fN (eb i)
  fA i := T.ff (ea i)
  fB i := T.ff (eb i)
  hA i := ff_hN T (ea i)
  hB i := ff_hN T (eb i)
  zA0 i := ff_zero T _ _ (h0 i).1
  zA1 i := ff_zero T _ _ (h1 i).1
  zB0 i := ff_zero T _ _ (h0 i).2
  zB1 i := ff_zero T _ _ (h1 i).2
  nA i m := by
    by_cases h : m ∈ fIdx (ea i)
    · rw [ff_zero T _ m h]
    · exact (ff_neg T _ m h).le
  nB i m := by
    by_cases h : m ∈ fIdx (eb i)
    · rw [ff_zero T _ m h]
    · exact (ff_neg T _ m h).le
  strict i m a b := by
    rcases hs i m a b with h | h
    · exact Or.inl (ff_neg T _ m h)
    · exact Or.inr (ff_neg T _ m h)
  up := hup
  dn := hdn

/-- The leaf condition at the view `u`: per cycle edge the facet `ea i` faces up and `eb i` down (or, the
mirror pattern, `eb i` up and `ea i` down), and the depths along the cycle are strictly unimodal. -/
def H16ALeaf (T : Type16 x) {k : ℕ} [NeZero k] (c : ZMod k → Fin 7) (ea eb : ZMod k → Fin 8)
    (u : ℝ³) : Prop :=
  ((∀ i, 0 < ⟪T.fN (ea i), u⟫) ∧ (∀ i, ⟪T.fN (eb i), u⟫ < 0) ∨
    (∀ i, 0 < ⟪T.fN (eb i), u⟫) ∧ (∀ i, ⟪T.fN (ea i), u⟫ < 0)) ∧ Uni (fun i => ⟪x (c i), u⟫)

/-- **The arc leaf shape**: a silhouette cycle `c` on `ZMod k` at an arbitrary view `u`. -/
theorem h16a_leaf_gen {k : ℕ} [NeZero k] (T : Type16 x) (hk : 3 ≤ k) (c : ZMod k → Fin 7)
    (hc : Function.Injective c) (ea eb : ZMod k → Fin 8) (u : ℝ³)
    (h0 : ∀ i, c i ∈ fIdx (ea i) ∧ c i ∈ fIdx (eb i))
    (h1 : ∀ i, c (i + 1) ∈ fIdx (ea i) ∧ c (i + 1) ∈ fIdx (eb i))
    (hs : ∀ i m, m ≠ c i → m ≠ c (i + 1) → m ∉ fIdx (ea i) ∨ m ∉ fIdx (eb i))
    (h : H16ALeaf T c ea eb u) : IsRupert (univ.image x) := by
  rcases h with ⟨⟨hu, hd⟩ | ⟨hu, hd⟩, hU⟩
  · exact h21_sil_isRupert hk T.inj hc (h16a_sil T c ea eb u h0 h1 hs hu hd) hU
  · exact h21_sil_isRupert hk T.inj hc
      (h16a_sil T c eb ea u (fun i => (h0 i).symm) (fun i => (h1 i).symm)
        (fun i m a b => (hs i m a b).symm) hu hd) hU

/-- The point of the plane `span (v1, v2)` where the two constraints `n1, n2` take the same positive
value: `u = w_a v1 + w_b v2`, `w = sign(D) (β₂ - β₁, α₁ - α₂)` (`α_m = n_m · v1`, `β_m = n_m · v2`). -/
noncomputable def h16a_u (v1 v2 n1 n2 : ℝ³) : ℝ³ :=
  (if 0 < ⟪n1, v1⟫ * ⟪n2, v2⟫ - ⟪n2, v1⟫ * ⟪n1, v2⟫ then (1 : ℝ) else -1) •
    ((⟪n2, v2⟫ - ⟪n1, v2⟫) • v1 + (⟪n1, v1⟫ - ⟪n2, v1⟫) • v2)

/-- Relabelling by `σ`: a leaf for `x ∘ σ` gives a Rupert passage for `x`. -/
theorem h16a_sigma (h : IsRupert (univ.image (x ∘ sigma16))) : IsRupert (univ.image x) := by
  rwa [image_sigma16] at h

end H16A
end Minimality
