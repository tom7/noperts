module

public import Minimality.Type08S.C2K35BA

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

set_option maxHeartbeats 12800000 in
theorem k28h5_B {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ}
    (hC : K6mCoords a a' b b' c c' d α1 β1 β6 γ6) (hM : K6sM a a' b b' c c' d)
    (hrel : K16Rel a b c d α1 β1) (h5 : K20mH5c a a' b b' c c' d α1 β1 β6 γ6)
    (hS : ⟪c' - a, b' - a⟫ < 0)
    (hd1 : ⟪b' - c, ⟪c' - a, b' - a⟫ • (c' - a) - ⟪c' - a, c' - a⟫ • (b' - a)⟫ < 0)
    (hd2 : ⟪c - a', ⟪c' - a, b' - a⟫ • (c' - a) - ⟪c' - a, c' - a⟫ • (b' - a)⟫ < 0)
    (H1 : 0 < γ6 * (α1 + β1 - 1) * ⟪c' - a, b' - a⟫ +
      (α1 * β1 * (γ6 + β6 - 1) - γ6 * (α1 + β1 - 1)) * ⟪c' - a, c' - a⟫)
    (H2 : 0 < γ6 * ⟪c' - a, b' - a⟫ + ⟪c' - a, c' - a⟫ * (γ6 * (α1 - 1) + α1 * β6))
    (H3 : 0 < ⟪c' - a, c' - a⟫ * β6 * (β1 + α1 - 1) + ⟪c' - a, b' - a⟫ *
      (β6 * (1 - β1 - α1) + α1 * β1 * (β6 + γ6 - 1))) :
    HasLexCell (V8 a a' b b' c c' d) := by
  obtain ⟨hdet, hc', hb', ha', hα1', hβ1', h1, hβ6', hγ6', h3⟩ := hC
  obtain ⟨⟨⟨⟨⟨hα1, hβ1, hσ, hβ6, hγ6⟩, hW⟩, -, -⟩, -, -⟩, -, -, -, -⟩ := h5
  -- vectors
  set P0 := a - d with hP0
  set Q0 := b - d with hQ0
  set R0 := c - d with hR0
  have ee : c' - a = (α1 - 1) • P0 + β1 • Q0 := by rw [hc', hP0, hQ0]; module
  have ff : b' - a = (α1 - 1) • P0 + β1 • R0 := by rw [hb', hP0, hR0]; module
  obtain ⟨E, hEd⟩ : ∃ E, ⟪c' - a, c' - a⟫ = E := ⟨_, rfl⟩
  obtain ⟨F, hFd⟩ : ∃ F, ⟪c' - a, b' - a⟫ = F := ⟨_, rfl⟩
  simp only [hEd, hFd] at hS hd1 hd2 H1 H2 H3
  have hΔ0 : det3 P0 Q0 R0 ≠ 0 := hdet
  have hα1p : 0 < α1 - 1 := by linarith
  have hβ1p : 0 < β1 := by linarith
  have hE : 0 < E := by
    rw [← hEd]
    apply real_inner_self_pos.2
    intro h0
    apply hΔ0
    have h2 : det3 (c' - a) Q0 R0 = (α1 - 1) * det3 P0 Q0 R0 := by
      rw [ee]; simp only [det3_expand]; simp; ring
    rw [h0] at h2
    have h3 : (α1 - 1) * det3 P0 Q0 R0 = 0 := by rw [← h2]; simp [det3_expand]
    rcases mul_eq_zero.1 h3 with h | h
    · exact absurd h hα1p.ne'
    · exact h
  set u0 : ℝ³ := F • (c' - a) - E • (b' - a) with hu0d
  have hu0 : u0 = ((α1 - 1) * (F - E)) • P0 + (β1 * F) • Q0 - (β1 * E) • R0 := by
    rw [hu0d, ee, ff]; module
  have hκ : 0 < β1 * E := mul_pos hβ1p hE
  obtain ⟨s, hsd⟩ : ∃ s, s = (β1 * E)⁻¹ := ⟨_, rfl⟩
  have hs0 : 0 < s := by rw [hsd]; positivity
  have hs : β1 * E * s = 1 := by rw [hsd]; field_simp
  set P : ℝ³ := s • P0 with hPd
  set Q : ℝ³ := s • Q0 with hQd
  set R : ℝ³ := -(s • u0) with hRd
  have hP0κ : P0 = (β1 * E) • P := by rw [hPd, smul_smul, hs, one_smul]
  have hQ0κ : Q0 = (β1 * E) • Q := by rw [hQd, smul_smul, hs, one_smul]
  have hR0' : R0 = ((α1 - 1) * (F - E)) • P + (β1 * F) • Q + R := by
    calc R0 = (β1 * E * s) • R0 := by rw [hs, one_smul]
      _ = _ := by rw [hPd, hQd, hRd, hu0]; module
  have hΔ : det3 P Q R ≠ 0 := by
    have e1 : det3 P Q R = s ^ 3 * (β1 * E) * det3 P0 Q0 R0 := by
      rw [hPd, hQd, hRd, hu0]
      simp only [det3_expand, PiLp.smul_apply, PiLp.add_apply, PiLp.sub_apply, PiLp.neg_apply, smul_eq_mul]
      ring
    rw [e1]
    exact mul_ne_zero (mul_ne_zero (pow_pos hs0 3).ne' hκ.ne') hΔ0
  have hβ6' := hβ6'
  have Ea : fpoint P Q R d (β1 * E, 0, 0) = a := by
    rw [k17f_fp]
    have : a = d + P0 := by rw [hP0]; abel
    rw [this, hP0κ]; module
  have Eb : fpoint P Q R d (0, β1 * E, 0) = b := by
    rw [k17f_fp]
    have : b = d + Q0 := by rw [hQ0]; abel
    rw [this, hQ0κ]; module
  have Ec : fpoint P Q R d ((α1 - 1) * (F - E), β1 * F, 1) = c := by
    rw [k17f_fp]
    have : c = d + R0 := by rw [hR0]; abel
    rw [this, hR0']; module
  have Ed : fpoint P Q R d (0, 0, 0) = d := by rw [k17f_fp]; module
  have Ec' : fpoint P Q R d (α1 * (β1 * E), β1 * (β1 * E), 0) = c' := by
    rw [k17f_fp, hc', hP0κ, hQ0κ]; module
  have Eb' : fpoint P Q R d (α1 * (β1 * E) + β1 * ((α1 - 1) * (F - E)), β1 * (β1 * F), β1) = b' := by
    rw [k17f_fp, hb', hR0', hP0κ]; module
  have Ea' : fpoint P Q R d (γ6 * ((α1 - 1) * (F - E)), β6 * (β1 * E) + γ6 * (β1 * F), γ6) = a' := by
    rw [k17f_fp, ha', hR0', hQ0κ]; module
  have hz : ∀ t, ⟪fpoint P Q R d t, R⟫ = -(s * ⟪fpoint P Q R d t, u0⟫) := by
    intro t; rw [hRd, inner_neg_right, real_inner_smul_right]
  have step_lt : ∀ (L : List (ℝ × ℝ)) (X Y : ℝ × ℝ × ℝ),
      ⟪fpoint P Q R d Y, u0⟫ < ⟪fpoint P Q R d X, u0⟫ → K25Step P Q R d L X Y := by
    intro L X Y h
    refine ⟨?_, fun heq => ?_⟩
    · rw [hz, hz]; nlinarith [mul_pos hs0 (sub_pos.2 h)]
    · exfalso; rw [hz, hz] at heq; nlinarith [mul_pos hs0 (sub_pos.2 h)]
  -- Gram facts
  have hfe : ⟪b' - a, c' - a⟫ = F := by rw [real_inner_comm]; exact hFd
  have hfu : ⟪b' - a, u0⟫ = F * F - E * ⟪b' - a, b' - a⟫ := by
    rw [hu0d, inner_sub_right, real_inner_smul_right, real_inner_smul_right, hfe]
  have hG : 0 < E * ⟪b' - a, b' - a⟫ - F * F := by
    set w : ℝ³ := E • (b' - a) - F • (c' - a) with hwd
    have hw0 : w ≠ 0 := by
      intro h0
      have e1 : det3 P0 Q0 w = E * β1 * det3 P0 Q0 R0 := by
        rw [hwd, ee, ff]
        simp only [det3_expand, PiLp.smul_apply, PiLp.add_apply, PiLp.sub_apply, smul_eq_mul]
        ring
      have hne : E * β1 * det3 P0 Q0 R0 ≠ 0 := mul_ne_zero (mul_ne_zero hE.ne' hβ1p.ne') hΔ0
      apply hne; rw [← e1, h0]; simp [det3_expand]
    have hww := real_inner_self_pos.2 hw0
    have key2 : ∀ (x y : ℝ³) (E F G : ℝ), ⟪x, x⟫ = E → ⟪x, y⟫ = F → ⟪y, y⟫ = G →
        ⟪E • y - F • x, E • y - F • x⟫ = E * (E * G - F * F) := by
      intro x y E F G h1 h2 h3
      have h4 : ⟪y, x⟫ = F := by rw [real_inner_comm]; exact h2
      simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right, h1, h2, h3, h4]
      ring
    have e2 : ⟪w, w⟫ = E * (E * ⟪b' - a, b' - a⟫ - F * F) :=
      key2 (c' - a) (b' - a) E F _ hEd hFd rfl
    rw [e2] at hww
    exact (mul_pos_iff_of_pos_left hE).1 hww
  have hf : ⟪b' - a, u0⟫ < 0 := by rw [hfu]; nlinarith
  have heu : ⟪c' - a, u0⟫ = 0 := by
    rw [hu0d, inner_sub_right, real_inner_smul_right, real_inner_smul_right, hEd, hFd]; ring
  have d1 : ⟪fpoint P Q R d (k28h5bY α1 β1 β6 γ6 E F 0), u0⟫ <
      ⟪fpoint P Q R d (k28h5bY α1 β1 β6 γ6 E F 4), u0⟫ := by
    rw [k28h5bY_0, k28h5bY_4, Eb', Ec]; rw [inner_sub_left] at hd1; linarith
  have d2 : ⟪fpoint P Q R d (k28h5bY α1 β1 β6 γ6 E F 0), u0⟫ <
      ⟪fpoint P Q R d (k28h5bY α1 β1 β6 γ6 E F 1), u0⟫ := by
    rw [k28h5bY_0, k28h5bY_1, Eb', Ea]; rw [inner_sub_left] at hf; linarith
  have d4 : ⟪fpoint P Q R d (k28h5bY α1 β1 β6 γ6 E F 4), u0⟫ <
      ⟪fpoint P Q R d (k28h5bY α1 β1 β6 γ6 E F 3), u0⟫ := by
    rw [k28h5bY_4, k28h5bY_3, Ec, Ea']; rw [inner_sub_left] at hd2; linarith
  have eqc : ⟪fpoint P Q R d (k28h5bY α1 β1 β6 γ6 E F 1), u0⟫ =
      ⟪fpoint P Q R d (k28h5bY α1 β1 β6 γ6 E F 2), u0⟫ := by
    rw [k28h5bY_1, k28h5bY_2, Ea, Ec']; rw [inner_sub_left] at heu; linarith
  -- ray witness
  obtain ⟨W, hWd⟩ : ∃ W, W = ⟪P0, c' - a⟫ := ⟨_, rfl⟩
  have hW0 : 0 ≤ W := by
    have : a - c' = -(c' - a) := by abel
    rw [hWd]; rw [this, inner_neg_right] at hW; linarith
  obtain ⟨μ, hμd⟩ : ∃ μ, μ = E / (W + 1) := ⟨_, rfl⟩
  have hμ : 0 < μ := by rw [hμd]; positivity
  have hμW : μ * (W + 1) = E := by rw [hμd]; field_simp
  refine ⟨R, k17f_r0 hΔ, ?_⟩
  refine k25_tie_cell (V8 a a' b b' c c' d) P Q R d hΔ (k := 5) (by norm_num)
    (k28h5bY α1 β1 β6 γ6 E F) (k28h5bY_inj hα1 hβ1 hγ6' hγ6 hE) ?_
    [(⟪a - c', P⟫, ⟪a - c', Q⟫), (β1, -(α1 - 1))] (by simp) ?_ ?_ 0 ?_ ?_ ?_
    (ρ1 := (β1 * E) * (μ - (α1 - 1))) (ρ2 := -((β1 * E) * β1)) (δ1 := 0) (δ2 := 0) ?_
  · intro i
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
    · rw [k28h5bY_0, Eb']; simp [V8]
    · rw [k28h5bY_1, Ea]; simp [V8]
    · rw [k28h5bY_2, Ec']; simp [V8]
    · rw [k28h5bY_3, Ea']; simp [V8]
    · rw [k28h5bY_4, Ec]; simp [V8]
  · intro v1 v2 hv D hD
    have h2 := hv (β1, -(α1 - 1)) (by simp)
    simp only at h2
    exact (k28h5b_tsc hD hα1 hβ1 hβ6' hβ6 hγ6' hγ6 hσ hE hS H1 H2 H3 (by linarith)).1
  · intro y hy hyx
    have hV : y = fpoint P Q R d (β1 * E, 0, 0) ∨ y = fpoint P Q R d (α1 * (β1 * E), β1 * (β1 * E), 0) ∨
        y = fpoint P Q R d (0, β1 * E, 0) ∨
        y = fpoint P Q R d (γ6 * ((α1 - 1) * (F - E)), β6 * (β1 * E) + γ6 * (β1 * F), γ6) ∨
        y = fpoint P Q R d (α1 * (β1 * E) + β1 * ((α1 - 1) * (F - E)), β1 * (β1 * F), β1) ∨
        y = fpoint P Q R d (0, 0, 0) ∨ y = fpoint P Q R d ((α1 - 1) * (F - E), β1 * F, 1) := by
      rw [Ea, Ed, Eb, Ea', Ec, Eb', Ec']
      simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
      tauto
    have hT : ∀ v1 v2 : ℝ, k18Cone [(⟪a - c', P⟫, ⟪a - c', Q⟫), (β1, -(α1 - 1))] v1 v2 → ∀ D : ℝ, 0 < D →
        ∀ t ∈ [((0 : ℝ), (0 : ℝ), (0 : ℝ)), (0, β1 * E, 0)], ∀ i : ZMod 5,
          TSc D (k28h5bY α1 β1 β6 γ6 E F (i + 1) - k28h5bY α1 β1 β6 γ6 E F i)
            (t - k28h5bY α1 β1 β6 γ6 E F i) (v1, v2, 0) := by
      intro v1 v2 hv D hD
      have h2 := hv (β1, -(α1 - 1)) (by simp)
      simp only at h2
      exact (k28h5b_tsc hD hα1 hβ1 hβ6' hβ6 hγ6' hγ6 hσ hE hS H1 H2 H3 (by linarith)).2
    have nm : ∀ j, y ≠ fpoint P Q R d (k28h5bY α1 β1 β6 γ6 E F j) := hyx
    rcases hV with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (nm 1 (by rw [k28h5bY_1])).elim
    · exact (nm 2 (by rw [k28h5bY_2])).elim
    · exact ⟨_, rfl, fun v1 v2 hC D hD i => hT v1 v2 hC D hD _ (by simp) i⟩
    · exact (nm 3 (by rw [k28h5bY_3])).elim
    · exact (nm 0 (by rw [k28h5bY_0])).elim
    · exact ⟨_, rfl, fun v1 v2 hC D hD i => hT v1 v2 hC D hD _ (by simp) i⟩
    · exact (nm 4 (by rw [k28h5bY_4])).elim
  · obtain ⟨e0, e1, e2, e3, e4, f0, f1, f2, f3, f4⟩ := k19_z5
    rw [e0]; exact step_lt _ _ _ d1
  · obtain ⟨e0, e1, e2, e3, e4, f0, f1, f2, f3, f4⟩ := k19_z5
    rw [f0]; exact step_lt _ _ _ d2
  · obtain ⟨e0, e1, e2, e3, e4, f0, f1, f2, f3, f4⟩ := k19_z5
    intro i hi
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl hi
    · left; rw [e1]; exact step_lt _ _ _ d2
    · left; rw [e2]
      refine ⟨le_of_eq (by rw [hz, hz, eqc]), fun _ v1 v2 hv => ?_⟩
      have h1 := hv (⟪a - c', P⟫, ⟪a - c', Q⟫) (by simp)
      simp only at h1
      rw [k28h5bY_1, k28h5bY_2, Ea, Ec']
      simpa [inner_sub_left] using h1
    · right; rw [f3]; exact step_lt _ _ _ d4
    · right; rw [f4]; exact step_lt _ _ _ d1
  · intro l hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    have hvec : ((β1 * E) * (μ - (α1 - 1))) • P + (-((β1 * E) * β1)) • Q = -(c' - a) + μ • P0 := by
      have : -(c' - a) + μ • P0 = (μ - (α1 - 1)) • P0 + (-β1) • Q0 := by rw [ee]; module
      rw [this, hP0κ, hQ0κ]; module
    rcases hl with rfl | rfl
    · left
      simp only
      rw [mul_comm ⟪a - c', P⟫, mul_comm ⟪a - c', Q⟫, ← real_inner_smul_right, ← real_inner_smul_right, ← inner_add_right, hvec]
      have e3' : a - c' = -(c' - a) := by abel
      have hWc : ⟪c' - a, P0⟫ = W := by rw [real_inner_comm]; exact hWd.symm
      simp only [e3', inner_add_right, inner_neg_left, inner_neg_right, real_inner_smul_right, hEd, hWc]
      nlinarith [hμW]
    · left
      simp only
      nlinarith [mul_pos (mul_pos hκ hβ1p) hμ]

end C2
end Type08Sp
end Minimality
