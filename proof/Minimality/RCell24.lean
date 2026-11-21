module

public import Minimality.FaceCircleClosed
public import Minimality.Type24SAT.K24.ParR2
public import Minimality.FaceChordFac
public import Minimality.LexCell

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace
open Finset

namespace Minimality.T24.RCell

open Minimality Minimality.H21 Minimality.H24.SAT Minimality.T24.SAT Minimality.FaceChord Minimality.LexCell

/-- Generic closed-cell tope leaf on Type 24 (`k ≥ 4`).
Note: `k = 3` has no closed-cell version in the toolbox because `RobUni` is vacuously true
for `k ≤ 3` (every 3-cycle). -/
def ToCC {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  ∃ (k : ℕ) (_ : NeZero k) (c : ZMod k → Fin 7) (U Dn : Finset (Fin 9)) (a u₀ : ℝ³),
    4 ≤ k ∧ Function.Injective c ∧ S0xCycUD s0x_S24 c U Dn ∧
    CellAt F U Dn a ∧ CellLe F U Dn u₀ ∧ RobUni (fun i => ⟪x (c i), u₀⟫)

/-- Generic closed-cell view on any of the nine facet circles (`k ≥ 4`).
Note: `k = 3` has no closed-cell version in the toolbox because `RobUni` is vacuously true
for `k ≤ 3` (every 3-cycle). -/
def CircCC {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  ∃ (f : Fin 9) (k : ℕ) (_ : NeZero k) (c : ZMod k → Fin 7) (U Dn : Finset (Fin 9)) (u₀ : ℝ³),
    4 ≤ k ∧ Function.Injective c ∧ S0xCycUD s0x_S24 c U Dn ∧
    ((f ∈ U ∧ f ∉ Dn) ∨ (f ∈ Dn ∧ f ∉ U)) ∧ F.N f ≠ 0 ∧
    ⟪F.N f, u₀⟫ = 0 ∧ (∀ t ∈ U, t ≠ f → 0 < ⟪F.N t, u₀⟫) ∧
    (∀ t ∈ Dn, t ≠ f → ⟪F.N t, u₀⟫ < 0) ∧ RobUni (fun i => ⟪x (c i), u₀⟫)

/-- Every generic closed-cell tope leaf on Type 24 (`k ≥ 4`) yields `IsRupert`. -/
theorem toCC_isRupert {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (h : ToCC F) :
    IsRupert (univ.image x) := by
  rcases h with ⟨k, _, c, U, Dn, a, u₀, hk, hc, hcyc, ha, hu₀, hR⟩
  exact isRupert_of_closedCell hk F (inj_of_fac F) hc hcyc ha hu₀ hR

/-- Every generic closed-cell facet-circle view on Type 24 (`k ≥ 4`) yields `IsRupert`. -/
theorem circCC_isRupert {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (h : CircCC F) :
    IsRupert (univ.image x) := by
  rcases h with ⟨f, k, _, c, U, Dn, u₀, hk, hc, hcyc, hf, hNf, hf0, hU, hD, hR⟩
  exact isRupert_faceCircleClosed hk F (inj_of_fac F) hc hcyc hf hNf hf0 hU hD hR

/-- Existence of a `FaceChordView` on any of the nine facets of Type 24. -/
def AnyFaceChord {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  ∃ t : Fin 9, FaceChordView F t

/-- Any `FaceChordView` on any of the nine facets of Type 24 yields `IsRupert`. -/
theorem anyFaceChord_isRupert {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (h : AnyFaceChord F) :
    IsRupert (univ.image x) := by
  rcases h with ⟨t, ht⟩
  exact isRupert_of_faceChordView F ht

/-- Generic lexicographic closed-cell leaf on Type 24 (`k ≥ 4`). -/
def LexAny {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  ∃ (k : ℕ) (_ : NeZero k) (c : ZMod k → Fin 7) (U Dn : Finset (Fin 9)) (b d1 d2 : ℝ³),
    4 ≤ k ∧ Function.Injective c ∧ S0xCycUD s0x_S24 c U Dn ∧
    (∀ t ∈ U, LexPos3 ⟪F.N t, b⟫ ⟪F.N t, d1⟫ ⟪F.N t, d2⟫) ∧
    (∀ t ∈ Dn, LexPos3 (-⟪F.N t, b⟫) (-⟪F.N t, d1⟫) (-⟪F.N t, d2⟫)) ∧
    RobUniLex (fun i => (⟪x (c i), b⟫, ⟪x (c i), d1⟫, ⟪x (c i), d2⟫))

/-- Every generic lexicographic closed-cell leaf on Type 24 (`k ≥ 4`) yields `IsRupert`. -/
theorem lexAny_isRupert {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (h : LexAny F) :
    IsRupert (univ.image x) := by
  rcases h with ⟨k, _, c, U, Dn, b, d1, d2, hk, hc, hcyc, hU, hD, hR⟩
  exact Minimality.LexCell.isRupert_of_lexCell hk F (inj_of_fac F) hc hcyc b d1 d2 hU hD hR

/-- Every `ToCC` closed-cell leaf is a `d2 = 0` instance of `LexAny`. -/
theorem toCC_imp_lexAny {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (h : ToCC F) :
    LexAny F := by
  rcases h with ⟨k, hk0, c, U, Dn, a, u₀, hk, hc, hcyc, ha, hu, hR⟩
  refine ⟨k, hk0, c, U, Dn, u₀, a - u₀, 0, hk, hc, hcyc, ?_, ?_, ?_⟩
  · intro t ht
    rcases (hu.1 t ht).lt_or_eq with hlt | heq
    · exact Or.inl hlt
    · refine Or.inr ⟨heq.symm, Or.inl ?_⟩
      rw [inner_sub_right, ← heq]; simpa using ha.1 t ht
  · intro t ht
    rcases (hu.2 t ht).lt_or_eq with hlt | heq
    · exact Or.inl (by linarith)
    · refine Or.inr ⟨by rw [heq]; simp, Or.inl ?_⟩
      rw [inner_sub_right, heq]; have := ha.2 t ht; simp; linarith
  · intro B b' c' d' h1 h2 h3 h4
    have := hR B b' c' d' h1 h2 h3 h4
    by_contra hn
    push Not at hn
    have key : ∀ p q : ℝ³, ¬ LexLt3 (⟪p, u₀⟫, ⟪p, a - u₀⟫, ⟪p, (0 : ℝ³)⟫)
        (⟪q, u₀⟫, ⟪q, a - u₀⟫, ⟪q, (0 : ℝ³)⟫) → ⟪q, u₀⟫ ≤ ⟪p, u₀⟫ := by
      intro p q h'
      by_contra hlt
      exact h' (Or.inl (by simp only; linarith [not_le.1 hlt]))
    exact this ⟨key _ _ hn.1, key _ _ hn.2.1, key _ _ hn.2.2.1, key _ _ hn.2.2.2⟩

/-- Every `CircCC` facet-circle closed-cell view is an instance of `LexAny`. -/
theorem circCC_imp_lexAny {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (h : CircCC F) :
    LexAny F := by
  rcases h with ⟨f, k, hk0, c, U, Dn, u₀, hk, hc, hcyc, hf, hNf, hf0, hU, hD, hR⟩
  have hff : 0 < ⟪F.N f, F.N f⟫ := real_inner_self_pos.mpr hNf
  obtain ⟨σ, hfU, hfD⟩ : ∃ σ : ℝ, (f ∈ U → 0 < σ) ∧ (f ∈ Dn → σ < 0) := by
    rcases hf with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨1, fun _ => one_pos, fun h => absurd h h2⟩
    · exact ⟨-1, fun h => absurd h h2, fun _ => by norm_num⟩
  refine ⟨k, hk0, c, U, Dn, u₀, σ • F.N f, 0, hk, hc, hcyc, ?_, ?_, ?_⟩
  · intro t ht
    by_cases htf : t = f
    · subst htf
      refine Or.inr ⟨hf0, Or.inl ?_⟩
      rw [real_inner_smul_right]
      exact mul_pos (hfU ht) hff
    · exact Or.inl (hU t ht htf)
  · intro t ht
    by_cases htf : t = f
    · subst htf
      refine Or.inr ⟨by rw [hf0]; simp, Or.inl ?_⟩
      rw [real_inner_smul_right]
      have : σ * ⟪F.N t, F.N t⟫ < 0 := mul_neg_of_neg_of_pos (hfD ht) hff
      linarith
    · exact Or.inl (by linarith [hD t ht htf])
  · intro B b' c' d' h1 h2 h3 h4
    have := hR B b' c' d' h1 h2 h3 h4
    by_contra hn
    push Not at hn
    have key : ∀ p q : ℝ³, ¬ LexLt3 (⟪p, u₀⟫, ⟪p, σ • F.N f⟫, ⟪p, (0 : ℝ³)⟫)
        (⟪q, u₀⟫, ⟪q, σ • F.N f⟫, ⟪q, (0 : ℝ³)⟫) → ⟪q, u₀⟫ ≤ ⟪p, u₀⟫ := by
      intro p q h'
      by_contra hlt
      exact h' (Or.inl (by simp only; linarith [not_le.1 hlt]))
    exact this ⟨key _ _ hn.1, key _ _ hn.2.1, key _ _ hn.2.2.1, key _ _ hn.2.2.2⟩

end Minimality.T24.RCell
