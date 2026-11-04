module

public import Minimality.Type08S.L2.K89CB

@[expose] public section

set_option maxHeartbeats 1000000

set_option autoImplicit true
set_option relaxedAutoImplicit true
open scoped RealInnerProductSpace
open Minimality Minimality.Type08Sp

namespace Minimality.Type08Sp.C2
noncomputable section

set_option maxHeartbeats 16000000 in
theorem k89_curve {a a' b b' c c' d : ℝ³} {t μ : ℝ} (ht1 : 1 < t) (ht2 : t ≤ 5/3) (hμ : 0 < μ)
    (hdet : det3 (a - d) (b - d) (c - d) ≠ 0)
    (hpp : ⟪a - d, a - d⟫ = μ) (hqq : ⟪b - d, b - d⟫ = μ) (hrr : ⟪c - d, c - d⟫ = μ)
    (hpq : ⟪a - d, b - d⟫ = -μ * ((t-1)/(2*t))) (hpr : ⟪a - d, c - d⟫ = -μ * ((t-1)/(2*t)))
    (hqr : ⟪b - d, c - d⟫ = -μ * ((t-1)/(2*t)))
    (hc' : c' = d + ((t+1)/(3-t)) • (a - d) + ((t+1)/(3-t)) • (b - d))
    (hb' : b' = d + ((t+1)/(3-t)) • (a - d) + ((t+1)/(3-t)) • (c - d))
    (ha' : a' = d + ((t+1)/(3-t)) • (b - d) + ((t+1)/(3-t)) • (c - d)) :
    IsRupert (V8 a a' b b' c c' d) := by
  obtain ⟨σ, hσD⟩ : ∃ σ : ℝ, 0 < σ * det3 (a - d) (b - d) (c - d) := by
    rcases lt_or_gt_of_ne hdet with h | h
    · exact ⟨-1, by linarith⟩
    · exact ⟨1, by linarith⟩
  have hP0 : d = d + k89c_cb (a - d) (b - d) (c - d) (k89c_P t 0) := by
    simp [k89c_cb, k89c_P]
  have hP1 : a = d + k89c_cb (a - d) (b - d) (c - d) (k89c_P t 1) := by
    simp [k89c_cb, k89c_P]
  have hP2 : b = d + k89c_cb (a - d) (b - d) (c - d) (k89c_P t 2) := by
    simp [k89c_cb, k89c_P]
  have hP3 : c = d + k89c_cb (a - d) (b - d) (c - d) (k89c_P t 3) := by
    simp [k89c_cb, k89c_P]
  have hP4 : a' = d + k89c_cb (a - d) (b - d) (c - d) (k89c_P t 4) := by
    rw [ha']; simp [k89c_cb, k89c_P, k89c_e, add_assoc]
  have hP5 : b' = d + k89c_cb (a - d) (b - d) (c - d) (k89c_P t 5) := by
    rw [hb']; simp [k89c_cb, k89c_P, k89c_e, add_assoc]
  have hP6 : c' = d + k89c_cb (a - d) (b - d) (c - d) (k89c_P t 6) := by
    rw [hc']; simp [k89c_cb, k89c_P, k89c_e, add_assoc]
  have mem0 : d ∈ V8 a a' b b' c c' d := by simp [V8]
  have mem1 : a ∈ V8 a a' b b' c c' d := by simp [V8]
  have mem2 : b ∈ V8 a a' b b' c c' d := by simp [V8]
  have mem3 : c ∈ V8 a a' b b' c c' d := by simp [V8]
  have mem4 : a' ∈ V8 a a' b b' c c' d := by simp [V8]
  have mem5 : b' ∈ V8 a a' b b' c c' d := by simp [V8]
  have mem6 : c' ∈ V8 a a' b b' c c' d := by simp [V8]
  have hcert : ∀ x ∈ V8 a a' b b' c c' d,
      TiltCert (V8 a a' b b' c c' d) (k89c_w (a - d) (b - d) (c - d) σ)
        (k89c_omv (a - d) (b - d) (c - d) μ t) (k89c_tau (a - d) (b - d) (c - d) d μ t) x := by
    intro x hx
    simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with hx | hx | hx | hx | hx | hx | hx
    · exact k89c_rim (u := k89c_u t) hμ rfl hpp hqq hrr hpq hpr hqr hσD (hx.trans hP0) hP3 hP1 mem3 mem1
        (k89c_conv0 t ht1 ht2) (k89c_rA0 t ht1 ht2) (k89c_rB0 t ht1 ht2)
    · exact k89c_rim (u := k89c_u t) hμ rfl hpp hqq hrr hpq hpr hqr hσD (hx.trans hP1) hP0 hP6 mem0 mem6
        (k89c_conv1 t ht1 ht2) (k89c_rA1 t ht1 ht2) (k89c_rB1 t ht1 ht2)
    · exact k89c_rim (u := k89c_u t) hμ rfl hpp hqq hrr hpq hpr hqr hσD (hx.trans hP4) hP6 hP3 mem6 mem3
        (k89c_conv3 t ht1 ht2) (k89c_rA3 t ht1 ht2) (k89c_rB3 t ht1 ht2)
    · exact k89c_tri hσD (hx.trans hP2) hP0 hP1 hP4 mem0 mem1 mem4
        (k89c_ia1 t ht1 ht2) (k89c_ia2 t ht1 ht2) (k89c_ia3 t ht1 ht2) (k89c_ia4 t ht1 ht2)
    · exact k89c_tri hσD (hx.trans hP5) hP0 hP6 hP4 mem0 mem6 mem4
        (k89c_ib1 t ht1 ht2) (k89c_ib2 t ht1 ht2) (k89c_ib3 t ht1 ht2) (k89c_ib4 t ht1 ht2)
    · exact k89c_rim (u := k89c_u t) hμ rfl hpp hqq hrr hpq hpr hqr hσD (hx.trans hP3) hP4 hP0 mem4 mem0
        (k89c_conv4 t ht1 ht2) (k89c_rA4 t ht1 ht2) (k89c_rB4 t ht1 ht2)
    · exact k89c_rim (u := k89c_u t) hμ rfl hpp hqq hrr hpq hpr hqr hσD (hx.trans hP6) hP1 hP4 mem1 mem4
        (k89c_conv2 t ht1 ht2) (k89c_rA2 t ht1 ht2) (k89c_rB2 t ht1 ht2)
  refine isRupert_of_tiltCert _ (k89c_w (a - d) (b - d) (c - d) σ) ?_ _ _ hcert
  intro hw
  have h1 := k89c_det_w (a - d) (b - d) (c - d) σ hσD _ _ (k89c_conv0 t ht1 ht2)
  rw [hw] at h1
  simp [det3] at h1

end
end Minimality.Type08Sp.C2
