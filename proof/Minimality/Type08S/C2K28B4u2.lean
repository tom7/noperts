module

public import Minimality.Type08S.C2K28B4u1
public import Minimality.Type08S.C2K28B4t0
public import Minimality.Type08S.C2K28B4c3

@[expose] public section

set_option maxHeartbeats 1000000
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
/-- Leaf C of the type 08 M-stratum boundary piece `β6 = 1`: view `u0`, cycle `(a, c', a', c, d)`,
tilt cone `-C1 = {l1 < 0, l2 < 0}`, side `Lp > 0, Lq < 0, Lz < 0`. -/
theorem k28b4_Cq0 {a a' b b' c c' d : ℝ³} {α1 β1 γ6 : ℝ}
    (hC : K6mCoords a a' b b' c c' d α1 β1 1 γ6) (hM : K6sM a a' b b' c c' d)
    (hrel : K16Rel a b c d α1 β1) (hα : 1 < α1) (hβ : 1 < β1) (hσ : β1 < 1 + γ6)
    (hLq : ⟪c' - a', b' - a⟫ = 0)
    (hLz : ⟪c' - c, k28b4c_u0 a a' c c' d⟫ < 0) : HasLexCell (V8 a a' b b' c c' d) := by
  obtain ⟨k1, k3, kc, ka, kp, kq⟩ := k28b4t_keysq hC hM hrel hα hβ hσ hLq
  obtain ⟨hdet, hc', hb', ha', -, -, -, -, hγ6, -⟩ := hC
  obtain ⟨m1, hm1⟩ : ∃ m1, m1 = ⟪c' - a', a - d⟫ := ⟨_, rfl⟩
  obtain ⟨m2, hm2⟩ : ∃ m2, m2 = ⟪c' - a', b - d⟫ := ⟨_, rfl⟩
  obtain ⟨m3, hm3⟩ : ∃ m3, m3 = ⟪c' - a', c - d⟫ := ⟨_, rfl⟩
  have hu0 : k28b4c_u0 a a' c c' d = m3 • (a - d) - m1 • (c - d) := by
    unfold k28b4c_u0; rw [hm1, hm3]
  rw [hu0] at hLz
  rw [← hm1] at k1 kc ka kp kq
  rw [← hm3] at k3 kc ka kp kq
  obtain ⟨μ, hμ⟩ : ∃ μ, μ = m3 / m1 := ⟨_, rfl⟩
  rw [← hμ] at kc ka
  have hμ0 : μ < 0 := by rw [hμ]; exact div_neg_of_neg_of_pos k3 k1
  have hm3μ : m3 = μ * m1 := by rw [hμ]; field_simp
  have hLp' : 0 < α1 + (β1 - 1) * μ := by
    rw [hm3μ] at kp
    by_contra hn; push Not at hn
    nlinarith [mul_nonneg (by linarith : 0 ≤ -(α1 + (β1 - 1) * μ)) k1.le]
  have hLq' : α1 - 1 + β1 * μ = 0 := by
    rw [hm3μ] at kq
    have : m1 * (α1 - 1 + β1 * μ) = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h k1.ne'
    · exact h
  obtain ⟨R, hR⟩ : ∃ R : ℝ³, R = μ • (a - d) - (c - d) := ⟨_, rfl⟩
  rw [← hR] at kc ka
  have hu0R : m3 • (a - d) - m1 • (c - d) = m1 • R := by rw [hR, hm3μ]; module
  rw [hu0R, inner_smul_right] at hLz
  have kz : ⟪c' - c, R⟫ < 0 := by
    by_contra hn; push Not at hn; nlinarith [mul_nonneg k1.le hn]
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
  have Fc : ⟪c, R⟫ < ⟪d, R⟫ := by rw [← sub_neg, ← inner_sub_left]; exact kc
  have Fa : ⟪a, R⟫ < ⟪d, R⟫ := by rw [← sub_neg, ← inner_sub_left]; exact ka
  have Fz : ⟪c', R⟫ < ⟪c, R⟫ := by rw [← sub_neg, ← inner_sub_left]; exact kz
  refine ⟨R, hR0, ?_⟩
  set Y := k28b4uY α1 β1 γ6 μ with hY
  have hY0 : fpoint (a - d) (b - d) R d (Y 0) = a := Ea
  have hY1 : fpoint (a - d) (b - d) R d (Y 1) = c' := Ec'
  have hY2 : fpoint (a - d) (b - d) R d (Y 2) = a' := Ea'
  have hY3 : fpoint (a - d) (b - d) R d (Y 3) = c := Ec
  have hY4 : fpoint (a - d) (b - d) R d (Y 4) = d := Ed
  have hcone : ∀ v1 v2 : ℝ, k18Cone [(0, 1), (-m1, -m2), (-1, 0)] v1 v2 → 0 < v2 ∧ v1 < 0 ∧ 0 < -m1 * v1 + -m2 * v2 := by
    intro v1 v2 hv
    have h1 := hv (0, 1) (by simp)
    have h2 := hv (-m1, -m2) (by simp)
    have h3 := hv (-1, 0) (by simp)
    simp only at h1 h2 h3
    exact ⟨by linarith, by linarith, h2⟩
  have hcyc : ∀ v1 v2 : ℝ, k18Cone [(0, 1), (-m1, -m2), (-1, 0)] v1 v2 → ∀ D : ℝ, 0 < D → ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      TSc D (Y (i + 1) - Y i) (Y j - Y i) (v1, v2, 0) := fun v1 v2 hv D hD =>
    (k28b4u_tsc hD hα hβ hγ6 hσ hμ0 hLp' hLq' (hcone v1 v2 hv).1 (hcone v1 v2 hv).2.1).1
  have hrest : ∀ y ∈ V8 a a' b b' c c' d, (∀ j, y ≠ fpoint (a - d) (b - d) R d (Y j)) →
      ∃ t, y = fpoint (a - d) (b - d) R d t ∧
      ∀ v1 v2 : ℝ, k18Cone [(0, 1), (-m1, -m2), (-1, 0)] v1 v2 → ∀ D : ℝ, 0 < D → ∀ i,
        TSc D (Y (i + 1) - Y i) (t - Y i) (v1, v2, 0) := by
    intro y hy hyx
    have hT : ∀ t ∈ [((0 : ℝ), (1 : ℝ), (0 : ℝ)), (α1 + β1 * μ, 0, -β1)],
        ∀ v1 v2 : ℝ, k18Cone [(0, 1), (-m1, -m2), (-1, 0)] v1 v2 → ∀ D : ℝ, 0 < D → ∀ i,
          TSc D (Y (i + 1) - Y i) (t - Y i) (v1, v2, 0) := fun t ht v1 v2 hv D hD i =>
      (k28b4u_tsc hD hα hβ hγ6 hσ hμ0 hLp' hLq' (hcone v1 v2 hv).1 (hcone v1 v2 hv).2.1).2 t ht i
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
    · exact ⟨_, rfl, fun v1 v2 hv D hD i => hT _ (by simp) v1 v2 hv D hD i⟩
    · exact (hyx 0 (by rw [hY0, Ea])).elim
    · exact (hyx 4 (by rw [hY4, Ed])).elim
    · exact ⟨_, rfl, fun v1 v2 hv D hD i => hT _ (by simp) v1 v2 hv D hD i⟩
    · exact (hyx 3 (by rw [hY3, Ec])).elim
  have hmem : ∀ i, fpoint (a - d) (b - d) R d (Y i) ∈ V8 a a' b b' c c' d := by
    intro i
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
    · rw [hY0]; simp [V8]
    · rw [hY1]; simp [V8]
    · rw [hY2]; simp [V8]
    · rw [hY3]; simp [V8]
    · rw [hY4]; simp [V8]
  have hinj := k28b4uY_inj hα hβ hγ6 hμ0
  have hL : ([(0, 1), (-m1, -m2), (-1, 0)] : List (ℝ × ℝ)) ≠ [] := by simp
  have hray : ∀ l ∈ ([(0, 1), (-m1, -m2), (-1, 0)] : List (ℝ × ℝ)),
      k18LexPos (l.1 * (-((|m2| + 1) / m1)) + l.2 * 1) (l.1 * 0 + l.2 * 0) := by
    intro l hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl
    · left; simp only; linarith
    · left; simp only; nlinarith [abs_nonneg m2, le_abs_self m2, neg_abs_le m2, div_mul_cancel₀ (|m2| + 1) k1.ne']
    · left; simp only; have : 0 < (|m2| + 1) / m1 := by positivity
      linarith
  have stepLt : ∀ s t, ⟪fpoint (a - d) (b - d) R d s, R⟫ < ⟪fpoint (a - d) (b - d) R d t, R⟫ →
      K25Step (a - d) (b - d) R d [(0, 1), (-m1, -m2), (-1, 0)] s t := fun s t h => ⟨h.le, fun e => absurd e h.ne⟩
  have htie : ∀ v1 v2 : ℝ, k18Cone [(0, 1), (-m1, -m2), (-1, 0)] v1 v2 →
      0 < ⟪fpoint (a - d) (b - d) R d (Y 2) - fpoint (a - d) (b - d) R d (Y 1), a - d⟫ * v1 +
        ⟪fpoint (a - d) (b - d) R d (Y 2) - fpoint (a - d) (b - d) R d (Y 1), b - d⟫ * v2 := by
    intro v1 v2 hv
    rw [hY1, hY2]
    have e1 : a' - c' = -(c' - a') := by abel
    rw [e1, inner_neg_left, inner_neg_left, ← hm1, ← hm2]
    have := (hcone v1 v2 hv).2.2
    linarith
  have stepTie : K25Step (a - d) (b - d) R d [(0, 1), (-m1, -m2), (-1, 0)] (Y 1) (Y 2) := by
    refine ⟨by rw [hY1, hY2]; exact F2.ge, fun _ => htie⟩
  obtain ⟨e0, e1, e2, e3, e4, f0, f1, f2, f3, f4⟩ := k19_z5
  refine k25_tie_cell _ _ _ _ _ hΔ (by norm_num) Y hinj hmem _ hL hcyc hrest 4 ?_ ?_ ?_ hray
  · rw [e4]; exact stepLt _ _ (by rw [hY3, hY4]; exact Fc)
  · rw [f4]; exact stepLt _ _ (by rw [hY0, hY4]; exact Fa)
  · intro i hi
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
    · left; rw [e0]; exact stepLt _ _ (by rw [hY0, hY4]; exact Fa)
    · right; rw [f1]; exact stepTie
    · right; rw [f2]; exact stepLt _ _ (by rw [hY2, hY3, F2]; exact Fz)
    · right; rw [f3]; exact stepLt _ _ (by rw [hY3, hY4]; exact Fc)
    · exact absurd rfl hi

end C2
end Type08Sp
end Minimality
