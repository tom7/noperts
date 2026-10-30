module

public import Minimality.Type08S.P2RDefs

@[expose] public section

set_option relaxedAutoImplicit true
set_option autoImplicit true
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality

/-- The lex-order open condition. -/
def LexQ {k : ℕ} (z w : ZMod k → ℝ) (z' : ZMod k → ℝ) : Prop :=
  ∀ i j, LexLt (z i, w i) (z j, w j) → z' i < z' j

theorem LexQ_open {k : ℕ} [NeZero k] (z w : ZMod k → ℝ) : IsOpen {z' | LexQ z w z'} := by
  classical
  haveI : Fintype (ZMod k) := ZMod.fintype k
  have : {z' : ZMod k → ℝ | LexQ z w z'} =
      ⋂ i, ⋂ j, {z' | LexLt (z i, w i) (z j, w j) → z' i < z' j} := by
    ext z'; simp [LexQ]
  rw [this]
  refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
  by_cases h : LexLt (z i, w i) (z j, w j)
  · simp only [h, true_implies]
    exact isOpen_lt (continuous_apply i) (continuous_apply j)
  · simp [h]

theorem LexQ_scale {k : ℕ} (z w : ZMod k → ℝ) (z' : ZMod k → ℝ) (c : ℝ) (hc : 0 < c)
    (h : LexQ z w z') : LexQ z w (fun i => c * z' i) :=
  fun i j hij => mul_lt_mul_of_pos_left (h i j hij) hc

theorem LexQ_unimodal {k : ℕ} [NeZero k] (z w : ZMod k → ℝ) (hU : LexUni z w)
    (z' : ZMod k → ℝ) (hinj : Function.Injective z') (hQ : LexQ z w z') : IsCyclicUnimodal z' := by
  classical
  obtain ⟨hd, hcard⟩ := hU
  refine ⟨hinj, ?_⟩
  have key : ∀ i j, z' i < z' j ↔ LexLt (z i, w i) (z j, w j) := by
    intro i j
    refine ⟨fun h => ?_, hQ i j⟩
    by_contra hn
    have hne : i ≠ j := by rintro rfl; exact lt_irrefl _ h
    have hne' : ¬ (z i = z j ∧ w i = w j) := fun ⟨a, b⟩ => hne (hd i j a b)
    have : LexLt (z j, w j) (z i, w i) := by
      unfold LexLt at hn ⊢
      simp only at hn ⊢
      rcases lt_trichotomy (z j) (z i) with h1 | h1 | h1
      · exact Or.inl h1
      · rcases lt_trichotomy (w j) (w i) with h2 | h2 | h2
        · exact Or.inr ⟨h1, h2⟩
        · exact absurd (hd i j h1.symm h2.symm) hne
        · exact absurd (Or.inr ⟨h1.symm, h2⟩) hn
      · exact absurd (Or.inl h1) hn
    exact absurd (hQ j i this) (not_lt.2 h.le)
  convert hcard using 2
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, key]

theorem isRupert_of_lexCell (V : Finset ℝ³) (u₀ v : ℝ³) (hu₀ : u₀ ≠ 0) {k : ℕ} [NeZero k]
    (x : ZMod k → ℝ³) (h : LexCell V u₀ v x) : IsRupert V := by
  obtain ⟨hk, hxV, hcyc, hrest, hU⟩ := h
  refine isRupert_of_tilted_unimodal' V u₀ v hu₀ hk x hxV hcyc hrest
    (LexQ (fun i => ⟪x i, u₀⟫) (fun i => ⟪x i, v⟫)) (LexQ_open _ _)
    (fun z' c hc hz => LexQ_scale _ _ z' c hc hz) ?_
    (fun z' hinj hQ => LexQ_unimodal _ _ hU z' hinj hQ)
  have : ∀ i j : ZMod k, LexLt (⟪x i, u₀⟫, ⟪x i, v⟫) (⟪x j, u₀⟫, ⟪x j, v⟫) →
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ⟪x i, u₀ + ε • v⟫ < ⟪x j, u₀ + ε • v⟫ := by
    intro i j hij
    have hp : 0 < (⟪x j, u₀⟫ - ⟪x i, u₀⟫) ∨
        ((⟪x j, u₀⟫ - ⟪x i, u₀⟫) = 0 ∧ 0 < (⟪x j, v⟫ - ⟪x i, v⟫)) := by
      rcases hij with h | ⟨h1, h2⟩
      · exact Or.inl (by simp only at h; linarith)
      · exact Or.inr ⟨by simp only at h1; linarith, by simp only at h2; linarith⟩
    refine (eventually_pos_affine hp).mono fun ε h => ?_
    simp only [inner_add_right, real_inner_smul_right]
    linarith
  exact eventually_all.2 fun i => eventually_all.2 fun j => by
    by_cases hij : LexLt (⟪x i, u₀⟫, ⟪x i, v⟫) (⟪x j, u₀⟫, ⟪x j, v⟫)
    · exact (this i j hij).mono fun _ h _ => h
    · exact Eventually.of_forall fun _ h => absurd h hij

end Minimality

