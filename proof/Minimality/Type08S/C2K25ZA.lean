module

public import Minimality.Type08S.C2K24ZA

/-!
# K25 / Z: TT closed.  The whole slice `K6t3LeftTT` (ties included) is a truncated right prism over (d, a, c) along
b - d with b' beyond ac, so `k20_prism3` makes it Rupert (spec: specpos/C2/K20TL).  The lex cells of C2K20T* are
now redundant for the chain.
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

/-- The TT slice is a truncated right prism over `(d, a, c)` along `b - d`, with `b'` beyond `ac`: Rupert (`k20_prism3`). -/
theorem k24_TT_prism {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (h : K6t3LeftTT a a' b b' c c' d) :
    IsRupert (V8 a a' b b' c c' d) := by
  obtain ⟨⟨hT, hT', -⟩, hL1, hL2⟩ := h
  obtain ⟨α4, β1, γ4, β6, γ6, hdet, hΔ, hβ1, hα4p, hγ4, hαγ, hβ6, hγ6, hβγ, hfar', hc', hb', ha', -, -⟩ :=
    k5d_setup W hT'
  have hg6 : γ6 = 1 := isT_gamma6 hdet ha' hT
  subst hg6
  have h1 : ⟪b - d, a - d⟫ = 0 := by
    have : ⟪a - d, d - b⟫ = -⟪a - d, b - d⟫ := by
      rw [show d - b = -(b - d) by abel, inner_neg_right]
    rw [real_inner_comm]; linarith
  have h2 : ⟪b - d, c - d⟫ = 0 := by
    have : ⟪c - d, d - b⟫ = -⟪c - d, b - d⟫ := by
      rw [show d - b = -(b - d) by abel, inner_neg_right]
    rw [real_inner_comm]; linarith
  have hD : det3 (a - d) (c - d) (b - d) ≠ 0 := by
    intro h0; apply hdet
    have e : det3 (a - d) (b - d) (c - d) = -det3 (a - d) (c - d) (b - d) := by
      simp only [det3_expand, PiLp.sub_apply]; ring
    rw [e, h0, neg_zero]
  have key := k20_prism3 d (b - d) (a - d) (c - d) (β := α4) (γ := γ4) (z0 := 1) (z1 := β1) (z2 := β6)
    h1 h2 hD one_pos hβ1 hβ6 hαγ
  -- key : IsRupert {d, d + (a-d), d + (c-d), d + (α4•(a-d) + γ4•(c-d)), d + 1•(b-d), d + (a-d) + β1•(b-d), d + (c-d) + β6•(b-d)}
  have q5 : d + (a - d) + β1 • (b - d) = c' := by rw [hc']; module
  have q6 : d + (c - d) + β6 • (b - d) = a' := by rw [ha']; module
  have q3 : d + (α4 • (a - d) + γ4 • (c - d)) = b' := by rw [hb', add_assoc]
  have q4 : d + (1 : ℝ) • (b - d) = b := by module
  have q1 : d + (a - d) = a := by abel
  have q2 : d + (c - d) = c := by abel
  rw [q5, q6, q3, q4, q1, q2] at key   -- q5, q6 before q1, q2 (q1/q2 would break their patterns)
  convert key using 1
  ext x; simp only [V8, Finset.mem_insert, Finset.mem_singleton]; tauto

def K25Slice {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) : Prop :=
  K17hTcZ1 a a' b b' c c' d ∨ K22LeftMN2 W ∨ K22LeftMKb W

theorem k25_slice_step {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d)
    (hNR : ¬ IsRupert (V8 a a' b b' c c' d)) (h : K24Slice W) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K25Slice W := by
  rcases h with h | h
  · exact (hNR (k24_TT_prism W h.1)).elim
  · exact Or.inr h

def K25ResidP (a a' b b' c c' d : ℝ³) : Prop :=
  ∃ W : Norm08w a a' b b' c c' d, ResP W.F d ∧ K25Slice W

def K25ResidP6 (a a' b b' c c' d : ℝ³) : Prop :=
  K25ResidP a a' b b' c c' d ∨ K25ResidP b b' a a' c c' d ∨ K25ResidP a a' c c' b b' d ∨
  K25ResidP c c' a a' b b' d ∨ K25ResidP b b' c c' a a' d ∨ K25ResidP c c' b b' a a' d

/-- **`Resid08FinalK25`**: as K24 with TT closed (right prism, `k24_TT_prism`). -/
def Resid08FinalK25 (a a' b b' c c' d : ℝ³) : Prop :=
  (PlanarTwo a a' b b' c c' ∨ PlanarGen a a' b b' c c' d) ∧ K25ResidP6 a a' b b' c c' d ∧
    ¬ HasLexCell (V8 a a' b b' c c' d)

theorem k25_residP_step {p p' q q' r r' d : ℝ³}
    (hNR : ¬ IsRupert (V8 p p' q q' r r' d)) (h : K24ResidP p p' q q' r r' d) :
    HasLexCell (V8 p p' q q' r r' d) ∨ K25ResidP p p' q q' r r' d := by
  obtain ⟨W, hR, hs⟩ := h
  rcases k25_slice_step W hNR hs with h | h
  · exact Or.inl h
  · exact Or.inr ⟨W, hR, h⟩

theorem resid08FinalK24_imp_K25 {a a' b b' c c' d : ℝ³}
    (hNR : ¬ IsRupert (V8 a a' b b' c c' d)) (h : Resid08FinalK24 a a' b b' c c' d) :
    Resid08FinalK25 a a' b b' c c' d := by
  obtain ⟨hpl, h6, hno⟩ := h
  have e := type08_set_perm a a' b b' c c' d
  refine ⟨hpl, ?_, hno⟩
  rcases h6 with h | h | h | h | h | h
  · rcases k25_residP_step hNR h with h | h
    · exact (hno h).elim
    · exact Or.inl h
  · rcases k25_residP_step (fun hR => hNR (by rw [V8, ← e.2.1]; exact hR)) h with h | h
    · exact (hno (by rw [V8, ← e.2.1]; exact h)).elim
    · exact Or.inr (Or.inl h)
  · rcases k25_residP_step (fun hR => hNR (by rw [V8, ← e.2.2.1]; exact hR)) h with h | h
    · exact (hno (by rw [V8, ← e.2.2.1]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inl h))
  · rcases k25_residP_step (fun hR => hNR (by rw [V8, ← e.2.2.2.1]; exact hR)) h with h | h
    · exact (hno (by rw [V8, ← e.2.2.2.1]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · rcases k25_residP_step (fun hR => hNR (by rw [V8, ← e.2.2.2.2.1]; exact hR)) h with h | h
    · exact (hno (by rw [V8, ← e.2.2.2.2.1]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · rcases k25_residP_step (fun hR => hNR (by rw [V8, ← e.2.2.2.2.2]; exact hR)) h with h | h
    · exact (hno (by rw [V8, ← e.2.2.2.2.2]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))

end Type08Sp
end Minimality
