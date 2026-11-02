import Minimality.Type08S.C2K28B4a2
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped RealInnerProductSpace Topology
open Finset Filter
namespace Minimality
namespace Type08Sp
namespace C2

set_option maxHeartbeats 6400000 in
/-- Leaf A of the type 08 M-stratum boundary piece `β6 = 1` (`K27mBoundary`, 4th disjunct): view
`u0 = m3 (a-d) - m1 (c-d)`, cycle `(a, c', a', b')`, tilt cone `{l1 > 0, l2 > 0}`, side `Lp < 0`. -/
theorem k28b4_A {a a' b b' c c' d : ℝ³} {α1 β1 γ6 : ℝ}
    (hC : K6mCoords a a' b b' c c' d α1 β1 1 γ6) (hM : K6sM a a' b b' c c' d)
    (hrel : K16Rel a b c d α1 β1) (hα : 1 < α1) (hβ : 1 < β1) (hσ : β1 < 1 + γ6)
    (hLp : ⟪c' - a', b' - c⟫ < 0) : HasLexCell (V8 a a' b b' c c' d) := by
  obtain ⟨k1, k3, k4, k5⟩ := k28b4a_keys hC hM hrel hα hβ hσ hLp
  obtain ⟨hdet, hc', hb', ha', -, -, -, -, hγ6, -⟩ := hC
  obtain ⟨m1, hm1⟩ : ∃ m1, m1 = ⟪c' - a', a - d⟫ := ⟨_, rfl⟩
  obtain ⟨m2, hm2⟩ : ∃ m2, m2 = ⟪c' - a', b - d⟫ := ⟨_, rfl⟩
  obtain ⟨m3, hm3⟩ : ∃ m3, m3 = ⟪c' - a', c - d⟫ := ⟨_, rfl⟩
  rw [← hm1] at k1 k4 k5
  rw [← hm3] at k3 k4 k5
  obtain ⟨μ, hμ⟩ : ∃ μ, μ = m3 / m1 := ⟨_, rfl⟩
  rw [← hμ] at k5
  have hμ0 : μ < 0 := by rw [hμ]; exact div_neg_of_neg_of_pos k3 k1
  have hm3μ : m3 = μ * m1 := by rw [hμ]; field_simp
  have hLp' : α1 + (β1 - 1) * μ < 0 := by
    rw [hm3μ] at k4
    by_contra hn; push_neg at hn
    nlinarith [mul_nonneg hn k1.le]
  obtain ⟨R, hR⟩ : ∃ R : ℝ³, R = μ • (a - d) - (c - d) := ⟨_, rfl⟩
  rw [← hR] at k5
  have hΔ : det3 (a - d) (b - d) R ≠ 0 := by
    have e : det3 (a - d) (b - d) R = -det3 (a - d) (b - d) (c - d) := by
      rw [hR]; simp only [det3_expand, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; ring
    rw [e]; exact neg_ne_zero.2 hdet
  have hR0 : R ≠ 0 := k17f_r0 hΔ
  have Ea : fpoint (a - d) (b - d) R d (1, 0, 0) = a := by rw [k17f_fp]; module
  have Ed : fpoint (a - d) (b - d) R d (0, 0, 0) = d := by rw [k17f_fp]; module
  have Eb : fpoint (a - d) (b - d) R d (0, 1, 0) = b := by rw [k17f_fp]; module
  have Ec : fpoint (a - d) (b - d) R d (μ, 0, -1) = c := by rw [k17f_fp, hR]; module
  have Ec' : fpoint (a - d) (b - d) R d (α1, β1, 0) = c' := by rw [k17f_fp, hc']; module
  have Ea' : fpoint (a - d) (b - d) R d (γ6 * μ, 1, -γ6) = a' := by rw [k17f_fp, ha', hR]; module
  have Eb' : fpoint (a - d) (b - d) R d (α1 + β1 * μ, 0, -β1) = b' := by rw [k17f_fp, hb', hR]; module
  -- depth facts
  have F2 : ⟪a', R⟫ = ⟪c', R⟫ := by
    have : ⟪c' - a', R⟫ = 0 := by
      rw [hR, inner_sub_right, inner_smul_right, ← hm1, ← hm3, hm3μ]; ring
    rw [inner_sub_left] at this; linarith
  have F1 : ⟪b', R⟫ < ⟪a', R⟫ := by
    rw [← sub_pos, ← inner_sub_left]; exact k5
  refine ⟨R, hR0, ?_⟩
  set Y := k28b4aY α1 β1 γ6 μ with hY
  have hY0 : fpoint (a - d) (b - d) R d (Y 0) = a := Ea
  have hY1 : fpoint (a - d) (b - d) R d (Y 1) = c' := Ec'
  have hY2 : fpoint (a - d) (b - d) R d (Y 2) = a' := Ea'
  have hY3 : fpoint (a - d) (b - d) R d (Y 3) = b' := Eb'
  have hcone : ∀ v1 v2 : ℝ, k18Cone [(0, -1), (m1, m2)] v1 v2 → v2 < 0 ∧ 0 < m1 * v1 + m2 * v2 := by
    intro v1 v2 hv
    have h1 := hv (0, -1) (by simp)
    have h2 := hv (m1, m2) (by simp)
    simp only at h1 h2
    exact ⟨by linarith, h2⟩
  have hcyc : ∀ v1 v2 : ℝ, k18Cone [(0, -1), (m1, m2)] v1 v2 → ∀ D : ℝ, 0 < D → ∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
      TSc D (Y (i + 1) - Y i) (Y j - Y i) (v1, v2, 0) := fun v1 v2 hv D hD =>
    (k28b4a_tsc hD hα hβ hγ6 hσ hμ0 hLp' (hcone v1 v2 hv).1).1
  have hrest : ∀ y ∈ V8 a a' b b' c c' d, (∀ j, y ≠ fpoint (a - d) (b - d) R d (Y j)) →
      ∃ t, y = fpoint (a - d) (b - d) R d t ∧
      ∀ v1 v2 : ℝ, k18Cone [(0, -1), (m1, m2)] v1 v2 → ∀ D : ℝ, 0 < D → ∀ i,
        TSc D (Y (i + 1) - Y i) (t - Y i) (v1, v2, 0) := by
    intro y hy hyx
    have hT : ∀ t ∈ [((0 : ℝ), (0 : ℝ), (0 : ℝ)), (0, 1, 0), (μ, 0, -1)],
        ∀ v1 v2 : ℝ, k18Cone [(0, -1), (m1, m2)] v1 v2 → ∀ D : ℝ, 0 < D → ∀ i,
          TSc D (Y (i + 1) - Y i) (t - Y i) (v1, v2, 0) := fun t ht v1 v2 hv D hD i =>
      (k28b4a_tsc hD hα hβ hγ6 hσ hμ0 hLp' (hcone v1 v2 hv).1).2 t ht i
    have hV : y = fpoint (a - d) (b - d) R d (γ6 * μ, 1, -γ6) ∨ y = fpoint (a - d) (b - d) R d (α1, β1, 0) ∨
        y = fpoint (a - d) (b - d) R d (α1 + β1 * μ, 0, -β1) ∨ y = fpoint (a - d) (b - d) R d (1, 0, 0) ∨
        y = fpoint (a - d) (b - d) R d (0, 0, 0) ∨ y = fpoint (a - d) (b - d) R d (0, 1, 0) ∨
        y = fpoint (a - d) (b - d) R d (μ, 0, -1) := by
      rw [Ea', Ec', Eb', Ea, Ed, Eb, Ec]
      simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
      tauto
    rcases hV with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hyx 2 (by rw [hY2, Ea'])).elim
    · exact (hyx 1 (by rw [hY1, Ec'])).elim
    · exact (hyx 3 (by rw [hY3, Eb'])).elim
    · exact (hyx 0 (by rw [hY0, Ea])).elim
    · exact ⟨_, rfl, fun v1 v2 hv D hD i => hT _ (by simp) v1 v2 hv D hD i⟩
    · exact ⟨_, rfl, fun v1 v2 hv D hD i => hT _ (by simp) v1 v2 hv D hD i⟩
    · exact ⟨_, rfl, fun v1 v2 hv D hD i => hT _ (by simp) v1 v2 hv D hD i⟩
  have hmem : ∀ i, fpoint (a - d) (b - d) R d (Y i) ∈ V8 a a' b b' c c' d := by
    intro i
    rcases k19_z4_cases i with rfl | rfl | rfl | rfl
    · rw [hY0]; simp [V8]
    · rw [hY1]; simp [V8]
    · rw [hY2]; simp [V8]
    · rw [hY3]; simp [V8]
  have hinj := k28b4aY_inj hα hβ hγ6 hμ0
  have hL : ([(0, -1), (m1, m2)] : List (ℝ × ℝ)) ≠ [] := by simp
  have hray : ∀ l ∈ ([(0, -1), (m1, m2)] : List (ℝ × ℝ)),
      k18LexPos (l.1 * (1 + m2) + l.2 * (-m1)) (l.1 * 0 + l.2 * 0) := by
    intro l hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl
    · left; simp only; linarith
    · left; simp only; nlinarith
  have stepLt : ∀ s t, ⟪fpoint (a - d) (b - d) R d s, R⟫ < ⟪fpoint (a - d) (b - d) R d t, R⟫ →
      K25Step (a - d) (b - d) R d [(0, -1), (m1, m2)] s t := fun s t h => ⟨h.le, fun e => absurd e h.ne⟩
  have htie : ∀ v1 v2 : ℝ, k18Cone [(0, -1), (m1, m2)] v1 v2 →
      0 < ⟪fpoint (a - d) (b - d) R d (Y 1) - fpoint (a - d) (b - d) R d (Y 2), a - d⟫ * v1 +
        ⟪fpoint (a - d) (b - d) R d (Y 1) - fpoint (a - d) (b - d) R d (Y 2), b - d⟫ * v2 := by
    intro v1 v2 hv
    rw [hY1, hY2, ← hm1, ← hm2]; exact (hcone v1 v2 hv).2
  have stepTie : K25Step (a - d) (b - d) R d [(0, -1), (m1, m2)] (Y 2) (Y 1) := by
    refine ⟨by rw [hY1, hY2]; exact F2.le, fun _ => htie⟩
  obtain ⟨e0, e1, e2, e3, f0, f1, f2, f3⟩ := k19_z4
  rcases lt_trichotomy ⟪a, R⟫ ⟪c', R⟫ with h | h | h
  · refine k25_tie_cell _ _ _ _ _ hΔ (by norm_num) Y hinj hmem _ hL hcyc hrest 1 ?_ ?_ ?_ hray
    · rw [f1]; exact stepLt _ _ (by rw [hY0, hY1]; exact h)
    · exact stepTie
    · intro i hi
      rcases k19_z4_cases i with rfl | rfl | rfl | rfl
      · right; rw [e0]; exact stepLt _ _ (by rw [hY0, hY1]; exact h)
      · exact absurd rfl hi
      · left; rw [f2]; exact stepTie
      · left; rw [f3]; exact stepLt _ _ (by rw [hY3, hY2]; exact F1)
  · refine k25_tie_cell2 _ _ _ _ _ hΔ (by norm_num) Y hinj hmem _ hL hcyc hrest 0 (by decide) ?_ ?_ ?_ hray
    · rw [f0]; exact stepLt _ _ (by rw [hY3, hY0, h, ← F2]; exact F1)
    · rw [e0, e1]; exact stepTie
    · intro i hi hi'
      rw [e0] at hi'
      rcases k19_z4_cases i with rfl | rfl | rfl | rfl
      · exact absurd rfl hi
      · exact absurd rfl hi'
      · left; rw [f2]; exact stepTie
      · left; rw [f3]; exact stepLt _ _ (by rw [hY3, hY2]; exact F1)
  · refine k25_tie_cell _ _ _ _ _ hΔ (by norm_num) Y hinj hmem _ hL hcyc hrest 0 ?_ ?_ ?_ hray
    · rw [f0]; exact stepLt _ _ (by rw [hY3, hY0]; rw [← F2] at h; exact lt_trans F1 h)
    · rw [e0]; exact stepLt _ _ (by rw [hY1, hY0]; exact h)
    · intro i hi
      rcases k19_z4_cases i with rfl | rfl | rfl | rfl
      · exact absurd rfl hi
      · left; rw [f1]; exact stepLt _ _ (by rw [hY1, hY0]; exact h)
      · left; rw [f2]; exact stepTie
      · left; rw [f3]; exact stepLt _ _ (by rw [hY3, hY2]; exact F1)

end C2
end Type08Sp
end Minimality
