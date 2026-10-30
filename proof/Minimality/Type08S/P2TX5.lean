module

public import Minimality.Type08S.P2TX4

@[expose] public section

set_option relaxedAutoImplicit true
/-!
# pkP / X5: `cellXba_rupert` (sp08f §6, cell `(−,−,−)` at `T`; Remark 24.1-R, Theorem 24.1).
-/

set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unreachableTactic false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

theorem sepSwapX {x y u v : ℝ} (h : ¬ Sep x y u v) : ¬ Sep x y v u := by
  simpa only [Sep, max_comm, min_comm] using h

set_option maxHeartbeats 1600000 in
/-- The frame statement: all data of `h3_setup`, `1 < γ4`, robust `X_ba'`. -/
theorem cell_frame {a a' b b' c c' d o : ℝ³} {e1 e2 e3 : ℝ³} (hF : Fr e1 e2 e3)
    {ν v1 C0 w1 ha w3 α1 α4 β1 γ4 β6 : ℝ} (hν : 0 < ν) (hv1 : v1 ≠ 0) (hha : 0 < ha) (hα : 1 < α1)
    (hα4 : 0 < α4) (hγ4 : 1 < γ4) (hβ1 : 0 < β1) (hβ6 : 0 < β6)
    (hE : 0 < α4 - α4 * β1 - α1 * (1 - γ4))
    (hd : d = pt e1 e2 e3 o (-v1) 0 0) (hb : b = pt e1 e2 e3 o (-v1) 0 ν)
    (hc : c = pt e1 e2 e3 o 0 0 C0) (haa : a = pt e1 e2 e3 o (-v1 + w1) ha w3)
    (ha' : a' = pt e1 e2 e3 o 0 0 (β6 * ν + C0))
    (hb' : b' = pt e1 e2 e3 o (-v1 * (1 - γ4) + α4 * w1) (α4 * ha) (α4 * w3 + γ4 * C0))
    (hc' : c' = pt e1 e2 e3 o (-v1 + α1 * w1) (α1 * ha) (α1 * w3 + β1 * ν))
    (hrob : ¬ Sep ν (α4 * w3 + γ4 * C0) (α1 * w3 + β1 * ν) (β6 * ν + C0)) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  -- the orientation sign
  obtain ⟨σ, hσ, hvσ⟩ : ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ σ * v1 < 0 := by
    rcases lt_or_gt_of_ne hv1 with h | h
    · exact ⟨1, Or.inl rfl, by linarith⟩
    · exact ⟨-1, Or.inr rfl, by linarith⟩
  have hσσ : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hr : 0 < -(σ * v1) := by linarith
  have hha' : ha ≠ 0 := hha.ne'
  -- distinct screen points
  have p01 : -v1 ≠ -v1 + α1 * w1 ∨ (0 : ℝ) ≠ α1 * ha :=
    Or.inr (by have := mul_pos (by linarith : (0:ℝ) < α1) hha; linarith)
  have p02 : -v1 ≠ -v1 * (1 - γ4) + α4 * w1 ∨ (0 : ℝ) ≠ α4 * ha :=
    Or.inr (by have := mul_pos hα4 hha; linarith)
  have p03 : -v1 ≠ (0 : ℝ) ∨ (0 : ℝ) ≠ 0 := Or.inl (by intro h; exact hv1 (by linarith))
  have p12 : -v1 + α1 * w1 ≠ -v1 * (1 - γ4) + α4 * w1 ∨ α1 * ha ≠ α4 * ha := by
    by_cases h : α1 * ha = α4 * ha
    · left
      intro hx
      have h1 : α1 = α4 := mul_right_cancel₀ hha' h
      subst h1
      apply hv1
      have : v1 * γ4 = 0 := by linarith
      rcases mul_eq_zero.1 this with h | h
      · exact h
      · linarith
    · exact Or.inr h
  have p13 : -v1 + α1 * w1 ≠ (0 : ℝ) ∨ α1 * ha ≠ 0 :=
    Or.inr (by have := mul_pos (by linarith : (0:ℝ) < α1) hha; linarith)
  have p23 : -v1 * (1 - γ4) + α4 * w1 ≠ (0 : ℝ) ∨ α4 * ha ≠ 0 :=
    Or.inr (by have := mul_pos hα4 hha; linarith)
  obtain ⟨n01, i01⟩ := tilt_pair (w1 := w1) (σ := σ) hha' hσσ p01
  obtain ⟨n02, i02⟩ := tilt_pair (w1 := w1) (σ := σ) hha' hσσ p02
  obtain ⟨n03, i03⟩ := tilt_pair (w1 := w1) (σ := σ) hha' hσσ p03
  obtain ⟨n12, i12⟩ := tilt_pair (w1 := w1) (σ := σ) hha' hσσ p12
  obtain ⟨n13, i13⟩ := tilt_pair (w1 := w1) (σ := σ) hha' hσσ p13
  obtain ⟨n23, i23⟩ := tilt_pair (w1 := w1) (σ := σ) hha' hσσ p23
  obtain ⟨u, hu0, huM, huL⟩ := exists_avoid (-(σ * v1) * (γ4 - 1) / α4)
    (by have := mul_pos hr (by linarith : (0:ℝ) < γ4 - 1); positivity)
    [(w1 * (-v1 - (-v1 + α1 * w1)) / ha + (0 - α1 * ha), -σ * (-v1 - (-v1 + α1 * w1)) / ha),
     (w1 * (-v1 - (-v1 * (1 - γ4) + α4 * w1)) / ha + (0 - α4 * ha),
       -σ * (-v1 - (-v1 * (1 - γ4) + α4 * w1)) / ha),
     (w1 * (-v1 - 0) / ha + (0 - 0), -σ * (-v1 - 0) / ha),
     (w1 * (-v1 + α1 * w1 - (-v1 * (1 - γ4) + α4 * w1)) / ha + (α1 * ha - α4 * ha),
       -σ * (-v1 + α1 * w1 - (-v1 * (1 - γ4) + α4 * w1)) / ha),
     (w1 * (-v1 + α1 * w1 - 0) / ha + (α1 * ha - 0), -σ * (-v1 + α1 * w1 - 0) / ha),
     (w1 * (-v1 * (1 - γ4) + α4 * w1 - 0) / ha + (α4 * ha - 0), -σ * (-v1 * (1 - γ4) + α4 * w1 - 0) / ha)]
    (by
      intro P hP
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hP
      rcases hP with rfl | rfl | rfl | rfl | rfl | rfl
      exacts [n01, n02, n03, n12, n13, n23])
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at huL
  obtain ⟨u01, u02, u03, u12, u13, u23⟩ := huL
  have hu1 : σ * (w1 - ha * ((w1 - σ * u) / ha)) = u := by
    have : ha * ((w1 - σ * u) / ha) = w1 - σ * u := by field_simp
    rw [this]
    have : σ * (σ * u) = u := by rw [← mul_assoc, hσσ, one_mul]
    linarith
  have hu2 : σ * (w1 - ha * ((w1 - σ * u) / ha)) * α4 < -(σ * v1) * (γ4 - 1) := by
    rw [hu1]
    rwa [lt_div_iff₀ hα4] at huM
  have hmem : ∀ p : ℝ³, (p = d ∨ p = a ∨ p = a' ∨ p = b ∨ p = b' ∨ p = c ∨ p = c') →
      p ∈ insert d ({a, a', b, b', c, c'} : Finset ℝ³) := by
    intro p hp; simp only [mem_insert, mem_singleton]; tauto
  refine cell_core hF o (t1 := (w1 - σ * u) / ha) hσ hν hha hα hα4 hγ4 hβ1 hβ6 hE hvσ
    (by rw [hu1]; exact hu0) hu2 hrob (i01 u u01) (i02 u u02) (i03 u u03) (i12 u u12) (i13 u u13)
    (i23 u u23) _ ?_ ?_ ?_ ?_ ?_
  · intro y hy
    simp only [mem_insert, mem_singleton] at hy
    rcases hy with h | h | h | h | h | h | h <;> rw [h]
    · exact Or.inl hd
    · exact Or.inr (Or.inl haa)
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ha')))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hb)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hb')))))
    · exact Or.inr (Or.inr (Or.inl hc))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hc'))))
  · rw [← hb]; exact hmem _ (by simp)
  · rw [← hc']; exact hmem _ (by simp)
  · rw [← hb']; exact hmem _ (by simp)
  · rw [← ha']; exact hmem _ (by simp)

/-- sp08f §6, cell `(−,−,−)`: when `∠q + ∠q' > π`, a robust `X_ba'` is Rupert by Theorem 24.1 with any HDN. -/
theorem cellXba_rupert {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) (hT : IsT a' b c d)
    (hang : AngBig a b b' c d) (hrob : ¬ Sep ⟪b, b - d⟫ ⟪b', b - d⟫ ⟪a', b - d⟫ ⟪c', b - d⟫) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  obtain ⟨e1, e2, e3, o, ν, v1, C0, w1, ha, w3, α1, α4, β1, γ4, β6, hF, hν, hv1, hha, hα, hα4, hγ4,
    hβ1, hβ6, hE, hu, hd, hb, hc, haa, ha', hb', hc', hv, hdep⟩ := h3_setup N hT
  have hγ : 1 < γ4 := (angBig_iff_gamma4 hF hν.ne' hv1 hha.ne' hd hb hc haa hb').1 hang
  have ez : ∀ (p : ℝ³) (X Y z : ℝ), p = pt e1 e2 e3 o X Y z → ⟪p, b - d⟫ = ν * (z + ⟪o, e3⟫) := by
    intro p X Y z hp; rw [hdep, hp, inner_pt_3 hF, add_comm]
  have hrob' : ¬ Sep ν (α4 * w3 + γ4 * C0) (α1 * w3 + β1 * ν) (β6 * ν + C0) := by
    have e0 := ez b _ _ _ hb
    have e1' := ez b' _ _ _ hb'
    have e2' := ez a' _ _ _ ha'
    have e3' := ez c' _ _ _ hc'
    rw [e0, e1', e2', e3', sep_aff hν] at hrob
    exact sepSwapX hrob
  exact cell_frame hF hν hv1 hha hα hα4 hγ hβ1 hβ6 hE hd hb hc haa ha' hb' hc' hrob'

end Type08Sp
end Minimality
