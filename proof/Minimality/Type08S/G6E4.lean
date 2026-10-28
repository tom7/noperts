module

public import Minimality.Type08S.G6E3

@[expose] public section

set_option autoImplicit true

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

/-- The frame data of `T ∩ H1` (copied from `closeT_H1_caseA`): all seven points in the frame
with `e3 ∥ b - d`. -/
theorem h1_setup {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d)
    (hT : IsT a' b c d) (hH : H1 b b' c c' d) :
    ∃ (e1 e2 e3 o : ℝ³) (ν v1 C0 w1 ha w3 α β1 γ4 β6 : ℝ), Fr e1 e2 e3 ∧ 0 < ν ∧ v1 ≠ 0 ∧
      0 < ha ∧ 1 < α ∧ 0 < β1 ∧ β1 < γ4 ∧ 0 < β6 ∧ b - d = ν • e3 ∧
      d = pt e1 e2 e3 o (-v1) 0 0 ∧ b = pt e1 e2 e3 o (-v1) 0 ν ∧ c = pt e1 e2 e3 o 0 0 C0 ∧
      a = pt e1 e2 e3 o (-v1 + w1) ha w3 ∧ a' = pt e1 e2 e3 o 0 0 (β6 * ν + C0) ∧
      b' = pt e1 e2 e3 o (-v1 * (1 - γ4) + α * w1) (α * ha) (α * w3 + γ4 * C0) ∧
      c' = pt e1 e2 e3 o (-v1 + α * w1) (α * ha) (α * w3 + β1 * ν) ∧
      c - d = v1 • e1 + C0 • e3 ∧ ∀ p : ℝ³, ⟪p, b - d⟫ = ν * (⟪p, e3⟫) := by
  obtain ⟨α, β1, γ4, β6, hdet, hc', hb', ha', hα, hβ1, hγ, hβ6⟩ := norm08_coords N hT hH
  obtain ⟨e1, e2, e3, hF, hu1, hu2, hu3, hv2, hv1, hw2⟩ := frame_exists hdet
  have hu : b - d = ⟪b - d, e3⟫ • e3 := by
    have := hF.expand (b - d); rw [hu1, hu2] at this; simpa using this
  have hv : c - d = ⟪c - d, e1⟫ • e1 + ⟪c - d, e3⟫ • e3 := by
    have := hF.expand (c - d); rw [hv2] at this; simpa using this
  have hw := hF.expand (a - d)
  generalize hν : ⟪b - d, e3⟫ = ν at *
  generalize hV1 : ⟪c - d, e1⟫ = v1 at *
  generalize hC0 : ⟪c - d, e3⟫ = C0 at *
  generalize hW1 : ⟪a - d, e1⟫ = w1 at *
  generalize hHA : ⟪a - d, e2⟫ = ha at *
  generalize hW3 : ⟪a - d, e3⟫ = w3 at *
  obtain ⟨o, ho⟩ : ∃ o : ℝ³, o = d + v1 • e1 := ⟨_, rfl⟩
  have hd_pt : d = pt e1 e2 e3 o (-v1) 0 0 := by simp only [pt, pc, ho]; module
  have hb_pt : b = pt e1 e2 e3 o (-v1) 0 ν := by
    have : b = d + ν • e3 := by rw [← hu]; abel
    rw [this]; simp only [pt, pc, ho]; module
  have hc_pt : c = pt e1 e2 e3 o 0 0 C0 := by
    have : c = d + (v1 • e1 + C0 • e3) := by rw [← hv]; abel
    rw [this]; simp only [pt, pc, ho]; module
  have ha_pt : a = pt e1 e2 e3 o (-v1 + w1) ha w3 := by
    have : a = d + (w1 • e1 + ha • e2 + w3 • e3) := by rw [← hw]; abel
    rw [this]; simp only [pt, pc, ho]; module
  have ha'_pt : a' = pt e1 e2 e3 o 0 0 (β6 * ν + C0) := by
    rw [ha', hu, hv]; simp only [pt, pc, ho]; module
  have hb'_pt : b' = pt e1 e2 e3 o (-v1 * (1 - γ4) + α * w1) (α * ha) (α * w3 + γ4 * C0) := by
    rw [hb', hw, hv]; simp only [pt, pc, ho]; module
  have hc'_pt : c' = pt e1 e2 e3 o (-v1 + α * w1) (α * ha) (α * w3 + β1 * ν) := by
    rw [hc', hw, hu]; simp only [pt, pc, ho]; module
  refine ⟨e1, e2, e3, o, ν, v1, C0, w1, ha, w3, α, β1, γ4, β6, hF, hu3, hv1, hw2, hα, hβ1, hγ,
    hβ6, hu, hd_pt, hb_pt, hc_pt, ha_pt, ha'_pt, hb'_pt, hc'_pt, hv, ?_⟩
  intro p; rw [hu, real_inner_smul_right]

end Type08Sp
end Minimality
