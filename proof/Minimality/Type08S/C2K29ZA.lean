module

public import Minimality.Type08S.C2K28ZA
public import Minimality.Type08S.C2K28B4a3
public import Minimality.Type08S.C2K28L2b2
public import Minimality.Type08S.C2K28L2b3
public import Minimality.Type08S.C2K28L2c4
public import Minimality.Type08S.C2K28H5d3
public import Minimality.Type08S.C2K28H5r2

/-!
# K29 / Z: M stratum (N2 side), cells at arrangement vertices (specpos/C2/K28B4S, K28L2S, K28L2T, K28H5S).
- β6 = 1 boundary, `⟪c'-a', b'-c⟫ < 0`: leaf A `k28b4_A`.
- L2 tail (`K6mH1Left ∧ K17b2L2Left`): H1 tie → `k28_h1tie`; else, with `U` the vertex view `k28l2aU0`,
  `z(c) < z(a')` → B′ `k28l2_Bp`; `L = ⟪a-a',U⟫ < 0` → B `k28l2_B`; `L ≥ 0`, `X3 < 0` → A `k28l2_A0`
  (at `L = 0` it needs `z(a') < z(c)`). Left: the corners `K29L2Corner` (empty on samples except the tie
  `L = 0 ∧ z(a') = z(c)`, untested).
- H5 residue, `S = ⟪c'-a,b'-a⟫ > 0`, `T = ⟪a-d,a-c'⟫ < 0`: cell A `k28h5_A'` with `hrb` from `k28h5rb_hrb`.
  Left: `T = 0` (three-way tie) and the side `S ≤ 0` (cell B needs four more facts).
-/
@[expose] public section

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
open C2

/-- K27's boundary with the β6 = 1 leaf A (`⟪c'-a', b'-c⟫ < 0`) removed. -/
def K29mBoundary (a a' b b' c c' d : ℝ³) (α1 β1 β6 γ6 : ℝ) : Prop :=
  (1 < β1 ∧ β6 + γ6 = β1) ∨
    (1 < β1 ∧ β1 < β6 + γ6 ∧ 1 < α1 ∧ ((β6 = 1 ∧ 0 ≤ ⟪c' - a', b' - c⟫) ∨ γ6 = 1))

/-- The corners of the L2 tail left by the cells A, B, B′ (`U = k28l2aU0`, `L = ⟪a-a',U⟫`). -/
def K29L2Corner (a a' b b' c c' d : ℝ³) (α1 β1 : ℝ) : Prop :=
  (⟪c' - a, b' - c⟫ = 0 ∧ (⟪a - a', k28l2aU0 a b c d α1 β1⟫ < 0 ∨ ⟪a - c', a - b'⟫ = 0 ∨
      (⟪a - a', k28l2aU0 a b c d α1 β1⟫ = 0 ∧
        ⟪c, k28l2aU0 a b c d α1 β1⟫ ≤ ⟪a', k28l2aU0 a b c d α1 β1⟫))) ∨
  (⟪a - c', a - b'⟫ = 0 ∧ 0 ≤ ⟪a - a', k28l2aU0 a b c d α1 β1⟫ ∧
      ⟪a', k28l2aU0 a b c d α1 β1⟫ ≤ ⟪c, k28l2aU0 a b c d α1 β1⟫) ∨
  (⟪a - a', k28l2aU0 a b c d α1 β1⟫ = 0 ∧
      ⟪a', k28l2aU0 a b c d α1 β1⟫ = ⟪c, k28l2aU0 a b c d α1 β1⟫)

theorem k29_l2 {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ}
    (hC : K6mCoords a a' b b' c c' d α1 β1 β6 γ6) (hM : K6sM a a' b b' c c' d)
    (hrel : K16Rel a b c d α1 β1) (hH1 : K6mH1Left a a' b b' c c' d α1 β1 β6 γ6)
    (hL2 : K17b2L2Left a a' b b' c c' d α1 β1 β6 γ6) (hne : ⟪c - a', a - b'⟫ ≠ 0) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K29L2Corner a a' b b' c c' d α1 β1 := by
  have hD0 : ⟪c - a', a - b'⟫ = 0 → ⟪a - c', a - b'⟫ ≤ 0 := fun h => (hne h).elim
  have hD : ⟪a - c', a - b'⟫ ≤ 0 := by
    rcases hH1.2.2 with h | h
    · exact (hne h).elim
    · exact h.2
  have hX4 : 0 ≤ ⟪c' - a, b' - c⟫ := hL2.1.2.1
  by_cases hB0 : ⟪c' - a, b' - c⟫ = 0
  · by_cases hA : ⟪a - c', a - b'⟫ < 0 ∧ 0 ≤ ⟪a - a', k28l2aU0 a b c d α1 β1⟫ ∧
        (⟪a - a', k28l2aU0 a b c d α1 β1⟫ = 0 →
          ⟪a', k28l2aU0 a b c d α1 β1⟫ < ⟪c, k28l2aU0 a b c d α1 β1⟫)
    · exact Or.inl (k28l2_A0 hC hM hrel hH1 hL2 hA.1 hX4 hA.2.2 hA.2.1)
    · refine Or.inr (Or.inl ⟨hB0, ?_⟩)
      rcases lt_or_eq_of_le hD with h3 | h3
      · rcases lt_or_ge ⟪a - a', k28l2aU0 a b c d α1 β1⟫ 0 with hL | hL
        · exact Or.inl hL
        · right; right
          by_contra hn
          apply hA
          refine ⟨h3, hL, fun h0 => ?_⟩
          exact lt_of_not_ge (fun hle => hn ⟨h0, hle⟩)
      · exact Or.inr (Or.inl h3)
  · by_cases hz : ⟪c, k28l2aU0 a b c d α1 β1⟫ < ⟪a', k28l2aU0 a b c d α1 β1⟫
    · exact Or.inl (k28l2_Bp hC hM hrel hH1 hL2 hD0 hB0 hz)
    have hz' := le_of_not_gt hz
    rcases lt_or_ge ⟪a - a', k28l2aU0 a b c d α1 β1⟫ 0 with hL | hL
    · exact Or.inl (k28l2_B hC hM hrel hH1 hL2 hD0 hB0 hL)
    rcases lt_or_eq_of_le hD with h3 | h3
    · by_cases hL0 : ⟪a - a', k28l2aU0 a b c d α1 β1⟫ = 0
      · rcases lt_or_eq_of_le hz' with hlt | heq
        · exact Or.inl (k28l2_A0 hC hM hrel hH1 hL2 h3 hX4 (fun _ => hlt) hL)
        · exact Or.inr (Or.inr (Or.inr ⟨hL0, heq⟩))
      · exact Or.inl (k28l2_A0 hC hM hrel hH1 hL2 h3 hX4 (fun h => (hL0 h).elim) hL)
    · exact Or.inr (Or.inr (Or.inl ⟨h3, hL, hz'⟩))

/-- The H5 residue left by cell A: the three-way tie `T = 0` on `S > 0`, and the side `S ≤ 0`. -/
def K29H5Rest (a b' c' d : ℝ³) : Prop :=
  (0 < ⟪c' - a, b' - a⟫ ∧ ⟪a - d, a - c'⟫ = 0) ∨ ⟪c' - a, b' - a⟫ ≤ 0

theorem k29_h5 {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ}
    (hC : K6mCoords a a' b b' c c' d α1 β1 β6 γ6) (hM : K6sM a a' b b' c c' d)
    (hrel : K16Rel a b c d α1 β1) (h5 : K20mH5c a a' b b' c c' d α1 β1 β6 γ6) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K29H5Rest a b' c' d := by
  have hT : ⟪a - d, a - c'⟫ ≤ 0 := by
    obtain ⟨⟨⟨⟨⟨-, -, -, -, -⟩, hT⟩, -, -⟩, -, -⟩, -, -⟩ := h5
    exact hT
  rcases lt_or_ge 0 ⟪c' - a, b' - a⟫ with hS | hS
  · rcases lt_or_eq_of_le hT with hT | hT
    · exact Or.inl (k28h5_A' hC hM hrel h5 hS hT (k28h5rb_hrb hC hM hrel h5))
    · exact Or.inr (Or.inl ⟨hS, hT⟩)
  · exact Or.inr (Or.inr hS)

def K29LeftMN2 {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) : Prop :=
  K6sMN2 a a' b b' c c' d ∧ ∃ α1 β1 β6 γ6 : ℝ, K6mCoords a a' b b' c c' d α1 β1 β6 γ6 ∧
    (RegN2 W.F → 1 < γ6) ∧
    (K29mBoundary a a' b b' c c' d α1 β1 β6 γ6 ∨
      (K6mH1Left a a' b b' c c' d α1 β1 β6 γ6 ∧ K17b2L2Left a a' b b' c c' d α1 β1 β6 γ6 ∧
        K29L2Corner a a' b b' c c' d α1 β1) ∨
      (K20mH5c a a' b b' c c' d α1 β1 β6 γ6 ∧ K29H5Rest a b' c' d))

theorem k29z_MN2 {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (h : K28LeftMN2 W) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K29LeftMN2 W := by
  obtain ⟨hs, α1, β1, β6, γ6, hC, hreg, h0 | ⟨hH1, hL⟩ | h0⟩ := h
  · -- boundary
    rcases h0 with h0 | ⟨hβ1, hσ, hα1, hb | hg⟩
    · exact Or.inr ⟨hs, α1, β1, β6, γ6, hC, hreg, Or.inl (Or.inl h0)⟩
    · rcases lt_or_ge ⟪c' - a', b' - c⟫ 0 with hLp | hLp
      · have hrel : K16Rel a b c d α1 β1 := by
          obtain ⟨hdet, hc', hb', ha', hα1', -, -, -, hγ6', h3⟩ := hC
          exact k16_n2_rel W hs.1 hs.2.1 hs.2.2.1 hdet hc' ha' hα1' hβ1 hγ6' h3
        subst hb
        exact Or.inl (k28b4_A hC hs.2.2 hrel hα1 hβ1 hσ hLp)
      · exact Or.inr ⟨hs, α1, β1, β6, γ6, hC, hreg,
          Or.inl (Or.inr ⟨hβ1, hσ, hα1, Or.inl ⟨hb, hLp⟩⟩)⟩
    · exact Or.inr ⟨hs, α1, β1, β6, γ6, hC, hreg, Or.inl (Or.inr ⟨hβ1, hσ, hα1, Or.inr hg⟩)⟩
  · -- L2 tail
    have hrel : K16Rel a b c d α1 β1 := by
      obtain ⟨hdet, hc', hb', ha', hα1', -, -, -, hγ6', h3⟩ := hC
      exact k16_n2_rel W hs.1 hs.2.1 hs.2.2.1 hdet hc' ha' hα1' hH1.1.2.1 hγ6' h3
    by_cases ht : ⟪c - a', a - b'⟫ = 0
    · exact Or.inl (k28_h1tie W hs hC hH1 ht)
    rcases k29_l2 hC hs.2.2 hrel hH1 hL ht with h1 | h1
    · exact Or.inl h1
    · exact Or.inr ⟨hs, α1, β1, β6, γ6, hC, hreg, Or.inr (Or.inl ⟨hH1, hL, h1⟩)⟩
  · -- H5 residue
    have hrel : K16Rel a b c d α1 β1 := by
      obtain ⟨hdet, hc', hb', ha', hα1', -, -, -, hγ6', h3⟩ := hC
      have hβ1 : 1 < β1 := by
        obtain ⟨⟨⟨⟨⟨-, hβ, -, -, -⟩, -⟩, -, -⟩, -, -⟩, -, -⟩ := h0
        exact hβ
      exact k16_n2_rel W hs.1 hs.2.1 hs.2.2.1 hdet hc' ha' hα1' hβ1 hγ6' h3
    rcases k29_h5 hC hs.2.2 hrel h0 with h1 | h1
    · exact Or.inl h1
    · exact Or.inr ⟨hs, α1, β1, β6, γ6, hC, hreg, Or.inr (Or.inr ⟨h0, h1⟩)⟩

def K29Slice {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) : Prop :=
  K29LeftMN2 W ∨ K27LeftMKb W

theorem k29_slice_step {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d)
    (hNR : ¬ IsRupert (V8 a a' b b' c c' d)) (h : K28Slice W) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K29Slice W := by
  rcases h with h | h
  · rcases k29z_MN2 W h with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr h)

def K29ResidP (a a' b b' c c' d : ℝ³) : Prop :=
  ∃ W : Norm08w a a' b b' c c' d, ResP W.F d ∧ K29Slice W

def K29ResidP6 (a a' b b' c c' d : ℝ³) : Prop :=
  K29ResidP a a' b b' c c' d ∨ K29ResidP b b' a a' c c' d ∨ K29ResidP a a' c c' b b' d ∨
  K29ResidP c c' a a' b b' d ∨ K29ResidP b b' c c' a a' d ∨ K29ResidP c c' b b' a a' d

/-- **`Resid08FinalK29`**: as K28 with the β6 = 1 leaf A, the L2 tail (up to corners) and H5 cell A closed. -/
def Resid08FinalK29 (a a' b b' c c' d : ℝ³) : Prop :=
  (PlanarTwo a a' b b' c c' ∨ PlanarGen a a' b b' c c' d) ∧ K29ResidP6 a a' b b' c c' d ∧
    ¬ HasLexCell (V8 a a' b b' c c' d)

theorem k29_residP_step {p p' q q' r r' d : ℝ³}
    (hNR : ¬ IsRupert (V8 p p' q q' r r' d)) (h : K28ResidP p p' q q' r r' d) :
    HasLexCell (V8 p p' q q' r r' d) ∨ K29ResidP p p' q q' r r' d := by
  obtain ⟨W, hR, hs⟩ := h
  rcases k29_slice_step W hNR hs with h | h
  · exact Or.inl h
  · exact Or.inr ⟨W, hR, h⟩

theorem resid08FinalK28_imp_K29 {a a' b b' c c' d : ℝ³}
    (hNR : ¬ IsRupert (V8 a a' b b' c c' d)) (h : Resid08FinalK28 a a' b b' c c' d) :
    Resid08FinalK29 a a' b b' c c' d := by
  obtain ⟨hpl, h6, hno⟩ := h
  have e := type08_set_perm a a' b b' c c' d
  refine ⟨hpl, ?_, hno⟩
  rcases h6 with h | h | h | h | h | h
  · rcases k29_residP_step hNR h with h | h
    · exact (hno h).elim
    · exact Or.inl h
  · rcases k29_residP_step (fun hR => hNR (by rw [V8, ← e.2.1]; exact hR)) h with h | h
    · exact (hno (by rw [V8, ← e.2.1]; exact h)).elim
    · exact Or.inr (Or.inl h)
  · rcases k29_residP_step (fun hR => hNR (by rw [V8, ← e.2.2.1]; exact hR)) h with h | h
    · exact (hno (by rw [V8, ← e.2.2.1]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inl h))
  · rcases k29_residP_step (fun hR => hNR (by rw [V8, ← e.2.2.2.1]; exact hR)) h with h | h
    · exact (hno (by rw [V8, ← e.2.2.2.1]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · rcases k29_residP_step (fun hR => hNR (by rw [V8, ← e.2.2.2.2.1]; exact hR)) h with h | h
    · exact (hno (by rw [V8, ← e.2.2.2.2.1]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · rcases k29_residP_step (fun hR => hNR (by rw [V8, ← e.2.2.2.2.2]; exact hR)) h with h | h
    · exact (hno (by rw [V8, ← e.2.2.2.2.2]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))

end Type08Sp
end Minimality
