module

public import Minimality.Type08S.P2TY3

@[expose] public section

set_option relaxedAutoImplicit true
/-!
# pkP / X2 / Y4: `cellXba2_rupert` (sp08f §6, cell `(+,−,−)` at `T`; Lemma 8.0, Theorem 24.1).
-/

set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unreachableTactic false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

/-- Avoiding finitely many affine zeros, with a lower bound only. -/
theorem exists_avoid_gt (M : ℝ) (L : List (ℝ × ℝ)) (hL : ∀ P ∈ L, P.1 ≠ 0 ∨ P.2 ≠ 0) :
    ∃ u : ℝ, M < u ∧ ∀ P ∈ L, P.1 + P.2 * u ≠ 0 := by
  obtain ⟨u, hu, huS⟩ := (Set.Ioi_infinite M).exists_notMem_finset (L.map (fun P => -P.1 / P.2)).toFinset
  refine ⟨u, hu, fun P hP e => huS ?_⟩
  simp only [List.mem_toFinset, List.mem_map]
  refine ⟨P, hP, ?_⟩
  rcases hL P hP with h | h
  · by_cases hB : P.2 = 0
    · rw [hB] at e; simp at e; exact absurd e h
    · field_simp; linarith
  · field_simp; linarith

set_option maxHeartbeats 1600000 in
/-- The frame statement: all data of `h3_setup`, `¬RobKb`, robust `X_ba'`, `R ≠ P`. -/
theorem cell2_frame {a a' b b' c c' d o : ℝ³} {e1 e2 e3 : ℝ³} (hF : Fr e1 e2 e3)
    {ν v1 C0 w1 ha w3 α1 α4 β1 γ4 β6 : ℝ} (hν : 0 < ν) (hv1 : v1 ≠ 0) (hha : 0 < ha) (hα : 1 < α1)
    (hα4 : 0 < α4) (hγ4 : 0 < γ4) (hβ1 : 0 < β1) (hβ6 : 0 < β6)
    (hE : 0 < α4 - α4 * β1 - α1 * (1 - γ4))
    (hd : d = pt e1 e2 e3 o (-v1) 0 0) (hb : b = pt e1 e2 e3 o (-v1) 0 ν)
    (hc : c = pt e1 e2 e3 o 0 0 C0) (haa : a = pt e1 e2 e3 o (-v1 + w1) ha w3)
    (ha' : a' = pt e1 e2 e3 o 0 0 (β6 * ν + C0))
    (hb' : b' = pt e1 e2 e3 o (-v1 * (1 - γ4) + α4 * w1) (α4 * ha) (α4 * w3 + γ4 * C0))
    (hc' : c' = pt e1 e2 e3 o (-v1 + α1 * w1) (α1 * ha) (α1 * w3 + β1 * ν))
    (hrob : ¬ Sep ν (α4 * w3 + γ4 * C0) (β6 * ν + C0) (α1 * w3 + β1 * ν))
    (hK : Sep ν (α4 * w3 + γ4 * C0) (α1 * w3 + β1 * ν) C0)
    (hRP : α1 * w3 + β1 * ν ≠ α4 * w3 + γ4 * C0) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  obtain ⟨σ, hσ, hvσ⟩ : ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ σ * v1 < 0 := by
    rcases lt_or_gt_of_ne hv1 with h | h
    · exact ⟨1, Or.inl rfl, by linarith⟩
    · exact ⟨-1, Or.inr rfl, by linarith⟩
  have hσσ : (-σ) * (-σ) = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hr : 0 < -(σ * v1) := by linarith
  have hha' : ha ≠ 0 := hha.ne'
  have p01 : (0 : ℝ) ≠ -v1 ∨ (0 : ℝ) ≠ 0 := Or.inl (by intro h; exact hv1 (by linarith))
  have p02 : (0 : ℝ) ≠ -v1 * (1 - γ4) + α4 * w1 ∨ (0 : ℝ) ≠ α4 * ha :=
    Or.inr (by have := mul_pos hα4 hha; linarith)
  obtain ⟨n01, i01⟩ := tilt_pair (w1 := w1) (σ := -σ) (x1 := 0) (y1 := 0) (x2 := -v1) (y2 := 0) hha' hσσ p01
  obtain ⟨n02, i02⟩ := tilt_pair (w1 := w1) (σ := -σ) (x1 := 0) (y1 := 0) (x2 := -v1 * (1 - γ4) + α4 * w1)
    (y2 := α4 * ha) hha' hσσ p02
  obtain ⟨u, huM, huL⟩ := exists_avoid_gt |(-(σ * v1)) * (1 - γ4) / α4|
    [(w1 * (0 - -v1) / ha + (0 - 0), - -σ * (0 - -v1) / ha),
     (w1 * (0 - (-v1 * (1 - γ4) + α4 * w1)) / ha + (0 - α4 * ha),
       - -σ * (0 - (-v1 * (1 - γ4) + α4 * w1)) / ha)]
    (by
      intro P hP
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hP
      rcases hP with rfl | rfl
      exacts [n01, n02])
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at huL
  obtain ⟨u01, u02⟩ := huL
  have hu1 : σ * (ha * ((w1 - -σ * u) / ha) - w1) = u := by
    have : ha * ((w1 - -σ * u) / ha) = w1 - -σ * u := by field_simp
    rw [this]
    have : σ * (w1 - -σ * u - w1) = (σ * σ) * u := by ring
    rw [this]
    have h2 : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
    rw [h2, one_mul]
  have hM : 0 ≤ |(-(σ * v1)) * (1 - γ4) / α4| := abs_nonneg _
  have hu0 : 0 < u := by linarith
  have hu2 : -(σ * v1) * (1 - γ4) < α4 * u := by
    have h1 : (-(σ * v1)) * (1 - γ4) / α4 < u := lt_of_le_of_lt (le_abs_self _) huM
    have h2 := (div_lt_iff₀ hα4).1 h1
    linarith
  have hmem : ∀ p : ℝ³, (p = d ∨ p = a ∨ p = a' ∨ p = b ∨ p = b' ∨ p = c ∨ p = c') →
      p ∈ insert d ({a, a', b, b', c, c'} : Finset ℝ³) := by
    intro p hp; simp only [mem_insert, mem_singleton]; tauto
  refine cell2_core hF o (t1 := (w1 - -σ * u) / ha) hσ hν hha hα hα4 hγ4 hβ1 hβ6 hE hvσ
    (by rw [hu1]; exact hu0) (by rw [hu1]; exact hu2) hrob hK hRP (i01 u u01) (i02 u u02) _ ?_ ?_ ?_ ?_ ?_ ?_ ?_
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
  · rw [← ha']; exact hmem _ (by simp)
  · rw [← hb]; exact hmem _ (by simp)
  · rw [← hd]; exact hmem _ (by simp)
  · rw [← haa]; exact hmem _ (by simp)
  · rw [← hc']; exact hmem _ (by simp)
  · rw [← hb']; exact hmem _ (by simp)

/-- sp08f §6, cell `(+,−,−)`: robust `X_ba'`, `¬RobKb` (so `min(B,P) ≥ max(R,C)`) and `z_c' ≠ z_b'`:
Rupert by Theorem 24.1 with any HDN (the hypothesis `¬ AngBig` is not needed). -/
theorem cellXba2_rupert {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) (hT : IsT a' b c d)
    (hB : ¬ RobKb a a' b b' c c' d) (hang : ¬ AngBig a b b' c d) (hrob : RobXba a' b b' c' d)
    (hRP : ⟪c', b - d⟫ ≠ ⟪b', b - d⟫) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  obtain ⟨e1, e2, e3, o, ν, v1, C0, w1, ha, w3, α1, α4, β1, γ4, β6, hF, hν, hv1, hha, hα, hα4, hγ4,
    hβ1, hβ6, hE, hu, hd, hb, hc, haa, ha', hb', hc', hv, hdep⟩ := h3_setup N hT
  have ez : ∀ (p : ℝ³) (X Y z : ℝ), p = pt e1 e2 e3 o X Y z → ⟪p, b - d⟫ = ν * (z + ⟪o, e3⟫) := by
    intro p X Y z hp; rw [hdep, hp, inner_pt_3 hF, add_comm]
  have e0 := ez b _ _ _ hb
  have e1' := ez b' _ _ _ hb'
  have e2' := ez a' _ _ _ ha'
  have e3' := ez c' _ _ _ hc'
  have e4' := ez c _ _ _ hc
  have hrob' : ¬ Sep ν (α4 * w3 + γ4 * C0) (β6 * ν + C0) (α1 * w3 + β1 * ν) := by
    have h := hrob
    unfold RobXba at h
    rw [e0, e1', e2', e3', sep_aff hν] at h
    exact h
  have hK : Sep ν (α4 * w3 + γ4 * C0) (α1 * w3 + β1 * ν) C0 := by
    by_contra hns
    apply hB
    unfold RobKb
    have hq2 : (test08 1 true true).depth (pts08 a a' b b' c c' d) =
        quad ⟪b, b - d⟫ ⟪c', b - d⟫ ⟪b', b - d⟫ ⟪c, b - d⟫ := by
      funext i
      rcases z4_cases i with rfl | rfl | rfl | rfl <;> rfl
    rw [hq2]
    apply robust4
    rw [e0, e1', e3', e4', sep_aff hν]
    exact hns
  have hRP' : α1 * w3 + β1 * ν ≠ α4 * w3 + γ4 * C0 := by
    intro h
    apply hRP
    rw [e3', e1', h]
  exact cell2_frame hF hν hv1 hha hα hα4 hγ4 hβ1 hβ6 hE hd hb hc haa ha' hb' hc' hrob' hK hRP'

end Type08Sp
end Minimality
