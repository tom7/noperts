module

public import Minimality.Type08S.C2K45ZA
public import Minimality.Type08S.C2K46TRB

/-!
# K46 / Z: M stratum, the A2 tie (σ = β1, R1, M = 0, ori < 0, dep = 0, lit1 > 0, β1 = α1 + 1) is Rupert

The tie has no lex cell on most of its 2-parameter family; it is closed by four motion cells
(`a2mc_L`, `a2mc_C`, `a2mc_Cp`, `a2mc_U`: `TiltCert` at a fixed rational view with a Cramer motion, in the
orthonormal frame p, c′ − a, b′ − a), transferred by `k46_tie_rupert` (C2K46TRB). Design: specpos/C2/K47MAP,
K50MC, K51SYM, K53COVER. This closes `K45mBoundary` (the σ = β1 tie) on both sides: the Kb side is empty and the
N2 side is left with the L2 tail corners `K33L2Corner` only.
-/
@[expose] public section

set_option maxHeartbeats 1000000

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
open C2

/-- N2 side after K46: only the L2 tail corners. -/
def K46LeftMN2 {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) : Prop :=
  K6sMN2 a a' b b' c c' d ∧ ∃ α1 β1 β6 γ6 : ℝ, K6mCoords a a' b b' c c' d α1 β1 β6 γ6 ∧
    (RegN2 W.F → 1 < γ6) ∧
    K6mH1Left a a' b b' c c' d α1 β1 β6 γ6 ∧ K17b2L2Left a a' b b' c c' d α1 β1 β6 γ6 ∧
      K33L2Corner a a' b b' c c' d α1 β1

theorem k46_boundary_rupert {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ}
    (hC : K6mCoords a a' b b' c c' d α1 β1 β6 γ6) (hM : K6sM a a' b b' c c' d)
    (hrel : 1 < β1 → K16Rel a b c d α1 β1) (h : K45mBoundary a a' b b' c c' d α1 β1 β6 γ6) :
    IsRupert (V8 a a' b b' c c' d) := by
  obtain ⟨hβ1, hσ, hL, hr⟩ := h
  exact k46_tie_rupert hC hM (hrel hβ1) hβ1 hσ hL hr

theorem k46z_MN2 {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d)
    (hNR : ¬ IsRupert (V8 a a' b b' c c' d)) (h : K45LeftMN2 W) : K46LeftMN2 W := by
  obtain ⟨hs, α1, β1, β6, γ6, hC, hreg, h0 | hL⟩ := h
  · have hrel : 1 < β1 → K16Rel a b c d α1 β1 := fun hβ1 => by
      obtain ⟨hdet, hc', hb', ha', hα1', -, -, -, hγ6', h3⟩ := hC
      exact k16_n2_rel W hs.1 hs.2.1 hs.2.2.1 hdet hc' ha' hα1' hβ1 hγ6' h3
    exact (hNR (k46_boundary_rupert hC hs.2.2 hrel h0)).elim
  · exact ⟨hs, α1, β1, β6, γ6, hC, hreg, hL⟩

theorem k46z_MKb {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d)
    (hNR : ¬ IsRupert (V8 a a' b b' c c' d)) (h : K45LeftMKb W) : False := by
  obtain ⟨hs, α1, β1, β6, γ6, hC, hreg, h0⟩ := h
  have hrel : 1 < β1 → K16Rel a b c d α1 β1 := fun hβ1 => by
    obtain ⟨hdet, hc', hb', ha', hα1', -⟩ := hC
    exact k16_kb_rel W hs.1 hs.2.1 hs.2.2.1 hdet hb' hα1' hβ1
  exact hNR (k46_boundary_rupert hC hs.2.2 hrel h0)

/-- After K46 only the N2 side is left. -/
def K46Slice {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) : Prop := K46LeftMN2 W

theorem k46_slice_step {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d)
    (hNR : ¬ IsRupert (V8 a a' b b' c c' d)) (h : K45Slice W) : K46Slice W := by
  rcases h with h | h
  · exact k46z_MN2 W hNR h
  · exact (k46z_MKb W hNR h).elim

def K46ResidP (a a' b b' c c' d : ℝ³) : Prop :=
  ∃ W : Norm08w a a' b b' c c' d, ResP W.F d ∧ K46Slice W

def K46ResidP6 (a a' b b' c c' d : ℝ³) : Prop :=
  K46ResidP a a' b b' c c' d ∨ K46ResidP b b' a a' c c' d ∨ K46ResidP a a' c c' b b' d ∨
  K46ResidP c c' a a' b b' d ∨ K46ResidP b b' c c' a a' d ∨ K46ResidP c c' b b' a a' d

/-- **`Resid08FinalK46`**: as K45 with the A2 tie closed; only the L2 tail corners (`K33L2Corner`, N2) are left. -/
def Resid08FinalK46 (a a' b b' c c' d : ℝ³) : Prop :=
  (PlanarTwo a a' b b' c c' ∨ PlanarGen a a' b b' c c' d) ∧ K46ResidP6 a a' b b' c c' d ∧
    ¬ HasLexCell (V8 a a' b b' c c' d)

theorem k46_residP_step {p p' q q' r r' d : ℝ³}
    (hNR : ¬ IsRupert (V8 p p' q q' r r' d)) (h : K45ResidP p p' q q' r r' d) :
    K46ResidP p p' q q' r r' d := by
  obtain ⟨W, hR, hs⟩ := h
  exact ⟨W, hR, k46_slice_step W hNR hs⟩

theorem resid08FinalK45_imp_K46 {a a' b b' c c' d : ℝ³}
    (hNR : ¬ IsRupert (V8 a a' b b' c c' d)) (h : Resid08FinalK45 a a' b b' c c' d) :
    Resid08FinalK46 a a' b b' c c' d := by
  obtain ⟨hpl, h6, hno⟩ := h
  have e := type08_set_perm a a' b b' c c' d
  refine ⟨hpl, ?_, hno⟩
  rcases h6 with h | h | h | h | h | h
  · exact Or.inl (k46_residP_step hNR h)
  · exact Or.inr (Or.inl (k46_residP_step (fun hR => hNR (by rw [V8, ← e.2.1]; exact hR)) h))
  · exact Or.inr (Or.inr (Or.inl
      (k46_residP_step (fun hR => hNR (by rw [V8, ← e.2.2.1]; exact hR)) h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl
      (k46_residP_step (fun hR => hNR (by rw [V8, ← e.2.2.2.1]; exact hR)) h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (k46_residP_step (fun hR => hNR (by rw [V8, ← e.2.2.2.2.1]; exact hR)) h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (k46_residP_step (fun hR => hNR (by rw [V8, ← e.2.2.2.2.2]; exact hR)) h)))))

end Type08Sp
end Minimality
