module

public import Minimality.Type08S.C2K33EC

@[expose] public section

set_option maxHeartbeats 1000000
set_option autoImplicit true
set_option relaxedAutoImplicit true
open scoped RealInnerProductSpace

namespace Minimality
namespace Type08Sp
open C2

theorem k32e_facts {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ}
    (hC : K6mCoords a a' b b' c c' d α1 β1 β6 γ6) (hM : K6sM a a' b b' c c' d) :
    ⟪a - d, c - d⟫ = ⟪a - d, b - d⟫ ∧ 0 < ⟪a - d, a - d⟫ ∧ ⟪b - d, c - d⟫ < ⟪b - d, b - d⟫ ∧
      ⟪b - d, c - d⟫ < ⟪c - d, c - d⟫ := by
  obtain ⟨hdet, hc', hb', ha', -, hβ1, -, -, hγ6, -⟩ := hC
  obtain ⟨hm0, hm1, hm2⟩ := hM
  have hPR : ⟪a - d, c - d⟫ = ⟪a - d, b - d⟫ := by
    have e : b - c = (b - d) - (c - d) := by abel
    rw [e, inner_sub_right] at hm0; linarith
  refine ⟨hPR, real_inner_self_pos.2 (by
    intro h0; apply hdet; rw [h0]; simp [det3_expand]), ?_, ?_⟩
  · have e1 : c' - d = α1 • (a - d) + β1 • (b - d) + (0:ℝ) • (c - d) := by rw [hc']; module
    have e2 : b - c = (0:ℝ) • (a - d) + (1:ℝ) • (b - d) + (-1:ℝ) • (c - d) := by module
    rw [e1, e2, k32e_ip _ _ _ hPR] at hm1; simp only [k32e_G] at hm1
    nlinarith
  · have e1 : b' - d = α1 • (a - d) + (0:ℝ) • (b - d) + β1 • (c - d) := by rw [hb']; module
    have e2 : b - c = (0:ℝ) • (a - d) + (1:ℝ) • (b - d) + (-1:ℝ) • (c - d) := by module
    rw [e1, e2, k32e_ip _ _ _ hPR] at hm2; simp only [k32e_G] at hm2
    nlinarith

theorem k32e_b4q {a a' b b' c c' d : ℝ³} {α1 β1 γ6 : ℝ}
    (hC : K6mCoords a a' b b' c c' d α1 β1 1 γ6) (hM : K6sM a a' b b' c c' d)
    (hrel : K16Rel a b c d α1 β1) (hα : 1 < α1) (hβ : 1 < β1) (hσ : β1 < 1 + γ6)
    (hLp : ⟪c' - a', b' - c⟫ = 0) : ⟪c' - a', b' - a⟫ < 0 := by
  obtain ⟨hPR, hpp, hqq, hrr⟩ := k32e_facts hC hM
  obtain ⟨hdet, hc', hb', ha', -, -, -, -, hγ6, -⟩ := hC
  have e1 : c' - a' = α1 • (a - d) + (β1 - 1) • (b - d) + (-γ6) • (c - d) := by
    rw [hc', ha']; module
  have e2 : b' - c = α1 • (a - d) + (0:ℝ) • (b - d) + (β1 - 1) • (c - d) := by rw [hb']; module
  have e3 : b' - a = (α1 - 1) • (a - d) + (0:ℝ) • (b - d) + β1 • (c - d) := by rw [hb']; module
  rw [e1, e2] at hLp; rw [e1, e3]
  exact (k32e_b4_vec _ _ _ α1 β1 γ6 hPR hpp hqq hrr hrel.1 hrel.2 hα hβ hσ hγ6 hLp).1

theorem k32e_b4E {a a' b b' c c' d : ℝ³} {α1 β1 γ6 : ℝ}
    (hC : K6mCoords a a' b b' c c' d α1 β1 1 γ6) (hM : K6sM a a' b b' c c' d)
    (hrel : K16Rel a b c d α1 β1) (hα : 1 < α1) (hβ : 1 < β1) (hσ : β1 < 1 + γ6)
    (hLp : ⟪c' - a', b' - c⟫ = 0) (hz : ⟪c' - c, k28b4c_u0 a a' c c' d⟫ < 0) :
    0 < -⟪c' - a', b - d⟫ + (1 - γ6) * ⟪c' - a', c - d⟫ := by
  obtain ⟨hPR, hpp, hqq, hrr⟩ := k32e_facts hC hM
  obtain ⟨hdet, hc', hb', ha', -, -, -, -, hγ6, -⟩ := hC
  have e1 : c' - a' = α1 • (a - d) + (β1 - 1) • (b - d) + (-γ6) • (c - d) := by
    rw [hc', ha']; module
  have e2 : b' - c = α1 • (a - d) + (0:ℝ) • (b - d) + (β1 - 1) • (c - d) := by rw [hb']; module
  have e4 : c' - c = α1 • (a - d) + β1 • (b - d) + (-1:ℝ) • (c - d) := by rw [hc']; module
  rw [e1, e2] at hLp
  unfold k28b4c_u0 at hz
  rw [e4, e1] at hz; rw [e1]
  exact (k32e_b4_vec _ _ _ α1 β1 γ6 hPR hpp hqq hrr hrel.1 hrel.2 hα hβ hσ hγ6 hLp).2 hz

end Type08Sp
end Minimality
