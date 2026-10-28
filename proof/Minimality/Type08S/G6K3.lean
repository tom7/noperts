module

public import Minimality.Type08S.G6K2
public import Minimality.Type08S.G6p

@[expose] public section

set_option autoImplicit true

/-!
# G6' : `close_T'2'` (29.13: Theorem 18.1 on the planar corner polygon `X_2a = (d, a, b', c)` at `T'`)
-/

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

/-- The depth function is affine on the planar quadrilateral `(d, a, b', c)`: its two diagonals
cannot be weakly separated unless the face is level. -/
theorem planar_notSep {α4 γ4 w3 C0 : ℝ} (hα4 : 0 < α4) (hγ4 : 0 < γ4) (hE : 1 < α4 + γ4)
    (hl : ¬ (w3 = 0 ∧ C0 = 0)) : ¬ Sep 0 (α4 * w3 + γ4 * C0) w3 C0 := by
  intro h
  apply hl
  unfold Sep at h
  simp only [max_le_iff, le_min_iff] at h
  have hs : 0 < α4 + γ4 - 1 := by linarith
  rcases h with ⟨⟨a1, a2⟩, ⟨a3, a4⟩⟩ | ⟨⟨a1, a2⟩, ⟨a3, a4⟩⟩
  · rcases le_total w3 C0 with h | h
    · have h0 : C0 = 0 := by
        nlinarith [mul_nonneg hα4.le (sub_nonneg.2 h), mul_nonneg hs.le (neg_nonneg.2 a2)]
      subst h0
      refine ⟨by nlinarith [mul_pos hα4 hα4], rfl⟩
    · have h0 : w3 = 0 := by
        nlinarith [mul_nonneg hγ4.le (sub_nonneg.2 h), mul_nonneg hs.le (neg_nonneg.2 a1)]
      subst h0
      exact ⟨rfl, by nlinarith [mul_pos hγ4 hγ4]⟩
  · rcases le_total w3 C0 with h | h
    · have h0 : w3 = 0 := by
        nlinarith [mul_nonneg hγ4.le (sub_nonneg.2 h), mul_nonneg hs.le a1]
      subst h0
      exact ⟨rfl, by nlinarith [mul_pos hγ4 hγ4]⟩
    · have h0 : C0 = 0 := by
        nlinarith [mul_nonneg hα4.le (sub_nonneg.2 h), mul_nonneg hs.le a3]
      subst h0
      exact ⟨by nlinarith [mul_pos hα4 hα4], rfl⟩


/-- The frame data of `T'`. -/
theorem hTp_setup {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d)
    (hT' : IsT' a b c' d) :
    ∃ (e1 e2 e3 o : ℝ³) (ν v1 C0 w1 ha w3 α4 β1 γ4 β6 γ6 : ℝ), Fr e1 e2 e3 ∧ 0 < ν ∧ v1 ≠ 0 ∧
      0 < ha ∧ 0 < α4 ∧ 0 < γ4 ∧ 1 < α4 + γ4 ∧ 0 < β1 ∧ 0 < β6 ∧ 0 < γ6 ∧ γ6 < 1 ∧
      b - d = ν • e3 ∧
      d = pt e1 e2 e3 o (-v1) 0 0 ∧ b = pt e1 e2 e3 o (-v1) 0 ν ∧ c = pt e1 e2 e3 o 0 0 C0 ∧
      a = pt e1 e2 e3 o (-v1 + w1) ha w3 ∧
      a' = pt e1 e2 e3 o (-v1 * (1 - γ6)) 0 (γ6 * C0 + β6 * ν) ∧
      b' = pt e1 e2 e3 o (-v1 * (1 - γ4) + α4 * w1) (α4 * ha) (α4 * w3 + γ4 * C0) ∧
      c' = pt e1 e2 e3 o (-v1 + w1) ha (w3 + β1 * ν) ∧
      ⟪a - d, b - d⟫ = ν * w3 ∧ ⟪c - d, b - d⟫ = ν * C0 := by
  obtain ⟨α4, β1, γ4, β6, γ6, hdet, hc', hb', ha', hα4, hγ4, hαγ, hβ1, hβ6, hγ6, hγ61⟩ :=
    norm08_coordsTp N hT'
  obtain ⟨e1, e2, e3, hF, hu1, hu2, hu3, hv2, hv1, hw2⟩ := frame_exists hdet
  have hu : b - d = ⟪b - d, e3⟫ • e3 := by
    have := hF.expand (b - d); rw [hu1, hu2] at this; simpa using this
  have hv : c - d = ⟪c - d, e1⟫ • e1 + ⟪c - d, e3⟫ • e3 := by
    have := hF.expand (c - d); rw [hv2] at this; simpa using this
  have hw := hF.expand (a - d)
  have hin : ∀ x : ℝ³, ⟪x, b - d⟫ = ⟪b - d, e3⟫ * ⟪x, e3⟫ := by
    intro x; conv_lhs => rw [hu]
    rw [real_inner_smul_right, real_inner_comm]
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
  have ha'_pt : a' = pt e1 e2 e3 o (-v1 * (1 - γ6)) 0 (γ6 * C0 + β6 * ν) := by
    rw [ha', hu, hv]; simp only [pt, pc, ho]; module
  have hb'_pt : b' = pt e1 e2 e3 o (-v1 * (1 - γ4) + α4 * w1) (α4 * ha) (α4 * w3 + γ4 * C0) := by
    rw [hb', hw, hv]; simp only [pt, pc, ho]; module
  have hc'_pt : c' = pt e1 e2 e3 o (-v1 + w1) ha (w3 + β1 * ν) := by
    rw [hc', hw, hu]; simp only [pt, pc, ho]; module
  refine ⟨e1, e2, e3, o, ν, v1, C0, w1, ha, w3, α4, β1, γ4, β6, γ6, hF, hu3, hv1, hw2, hα4, hγ4,
    hαγ, hβ1, hβ6, hγ6, hγ61, hu, hd_pt, hb_pt, hc_pt, ha_pt, ha'_pt, hb'_pt, hc'_pt, ?_, ?_⟩
  · rw [hin, hW3]
  · rw [hin, hC0]


/-- **T' closing** (29.13): Theorem 18.1 on the planar robust corner polygon `X_2a`. -/
theorem close_T'2' {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d)
    (hT' : IsT' a b c' d) (hco : ¬ CoT'2 a a' b b' c c' d) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  unfold CoT'2 at hco
  simp only [not_or, not_not] at hco
  obtain ⟨hno, hlev⟩ := hco
  obtain ⟨e1, e2, e3, o, ν, v1, C0, w1, ha, w3, α4, β1, γ4, β6, γ6, hF, hν, hv1, hha, hα4, hγ4,
    hαγ, hβ1, hβ6, hγ6, hγ61, hu, hd, hb, hc, haa, ha', hb', hc', hiw, hiC⟩ := hTp_setup N hT'
  have hl : ¬ (w3 = 0 ∧ C0 = 0) := by
    rintro ⟨h1, h2⟩
    apply hlev
    rw [hiw, hiC, h1, h2]; simp
  rw [hu] at hno
  have hmem : ∀ p : ℝ³, (p = d ∨ p = a ∨ p = a' ∨ p = b ∨ p = b' ∨ p = c ∨ p = c') →
      p ∈ insert d ({a, a', b, b', c, c'} : Finset ℝ³) := by
    intro p hp; simp only [mem_insert, mem_singleton]; tauto
  refine poly_coreTp hF o (w1 := w1) hν hv1 hha hβ1 hβ6 hα4 hγ4 (by linarith) hγ6 hγ61
    (planar_notSep hα4 hγ4 hαγ hl) (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) ?_ ?_ ?_ ?_ ?_
    ({d, a, b', c} : Finset ℝ³) ?_ ?_ ?_ ?_ hno
  · intro v hv'
    simp only [mem_insert, mem_singleton] at hv'
    rcases hv' with h | h | h | h | h | h | h <;>
      simp only [h, haa, hb', hc', ha', hd, hb, hc, true_or, or_true]
  · rw [← hd]; apply hmem; simp
  · rw [← haa]; apply hmem; simp
  · rw [← hb']; apply hmem; simp
  · rw [← hc]; apply hmem; simp
  · rw [← hd]; simp
  · rw [← haa]; simp
  · rw [← hb']; simp
  · rw [← hc]; simp

end Type08Sp
end Minimality

#print axioms Minimality.Type08Sp.close_T'2'
