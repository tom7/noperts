module

public import Minimality.Type08S.C2K17AA
public import Minimality.Type08S.C2K17AB
public import Minimality.Type08S.C2K17AR

@[expose] public section


set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
open scoped RealInnerProductSpace Topology
open Finset Filter
namespace Minimality
namespace Type08Sp
open C2

/-- Weight of a frame point against a tilt `fcomb p q r v1 v2 0` in canonical atoms. -/
theorem k17a_wexp (p q r d : ℝ³) (t : ℝ × ℝ × ℝ) (v1 v2 : ℝ) :
    ⟪fpoint p q r d t, fcomb p q r v1 v2 0⟫ =
      v1 * (⟪d, p⟫ + t.1 * ⟪p, p⟫ + t.2.1 * ⟪p, q⟫ + t.2.2 * ⟪p, r⟫) +
      v2 * (⟪d, q⟫ + t.1 * ⟪p, q⟫ + t.2.1 * ⟪q, q⟫ + t.2.2 * ⟪q, r⟫) := by
  have h : ∀ x : ℝ³, ⟪x, fcomb p q r v1 v2 0⟫ = v1 * ⟪x, p⟫ + v2 * ⟪x, q⟫ := by
    intro x; simp [fcomb, inner_add_right, inner_smul_right]
  rw [inner_fpoint, h, h, h, h]
  rw [real_inner_comm p q, real_inner_comm p r, real_inner_comm q r]
  ring

theorem k17a_rel_atoms {a b c d : ℝ³} {β1 : ℝ} (hrel : K16Rel a b c d 1 β1) (hρ : ⟪a - d, b - c⟫ = 0) :
    ⟪a - d, c - d⟫ * ⟪b - c, b - c⟫ = -(β1 - 1) * (⟪c - d, c - d⟫ * ⟪b - c, b - c⟫ - ⟪c - d, b - c⟫ ^ 2) := by
  obtain ⟨h1, -⟩ := hrel
  have hb : b - d = (c - d) + (b - c) := by abel
  have hb2 : ⟪a - d, b - d⟫ = ⟪a - d, c - d⟫ := by
    rw [hb, inner_add_right, hρ]; ring
  rw [hb2] at h1
  rw [hb] at h1
  simp only [inner_add_left, inner_add_right] at h1
  have := real_inner_comm (c - d) (b - c)
  rw [this] at h1
  linear_combination h1

set_option maxHeartbeats 6400000 in
theorem k17a_dn2_D1 {a a' b b' c c' d : ℝ³} {β1 β6 γ6 : ℝ}
    (hdet : det3 (a - d) (b - d) (c - d) ≠ 0)
    (hc' : c' = d + (1:ℝ) • (a - d) + β1 • (b - d)) (hb' : b' = d + (1:ℝ) • (a - d) + β1 • (c - d))
    (ha' : a' = d + β6 • (b - d) + γ6 • (c - d))
    (hβ1 : 0 < β1) (hβ6 : 0 < β6) (hγ6 : 0 < γ6) (hs : 1 < β6 + γ6)
    (hrel : K16Rel a b c d 1 β1) (hD : K6sD1 a a' b b' c c' d) :
    HasLexCell (V8 a a' b b' c c' d) := by
  obtain ⟨hρ, hζ⟩ := hD
  have hr := k17a_rel_atoms hrel hρ
  have hrr : 0 < ⟪b - c, b - c⟫ := by
    apply real_inner_self_pos.2
    intro h0
    apply hdet
    have : b = c := sub_eq_zero.1 h0
    subst this
    simp only [det3_expand, PiLp.sub_apply]; ring
  have hbd : 0 < ⟪b - d, b - d⟫ := by
    apply real_inner_self_pos.2
    intro h0
    apply hdet
    have : b = d := sub_eq_zero.1 h0
    subst this
    simp only [det3_expand, PiLp.sub_apply]; ring
  have hb : b - d = (c - d) + (b - c) := by abel
  have hcd : c' - d = (a - d) + β1 • ((c - d) + (b - c)) := by rw [hc', ← hb]; module
  have hq : ⟪c - d, b - c⟫ = -⟪b - c, b - c⟫ := by
    rw [hcd, inner_add_left, inner_smul_left, inner_add_left, hρ] at hζ
    simp only [conj_trivial] at hζ
    have : β1 * (⟪c - d, b - c⟫ + ⟪b - c, b - c⟫) = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hβ1.ne'
    · linarith
  have hbb : ⟪b - d, b - d⟫ = ⟪c - d, c - d⟫ - ⟪b - c, b - c⟫ := by
    rw [hb]; simp only [inner_add_left, inner_add_right]
    have := real_inner_comm (c - d) (b - c)
    linarith
  -- pq = -(β1-1)(qq-rr)
  have hpq : ⟪a - d, c - d⟫ = -(β1 - 1) * (⟪c - d, c - d⟫ - ⟪b - c, b - c⟫) := by
    have h2 : (⟪a - d, c - d⟫ + (β1 - 1) * (⟪c - d, c - d⟫ - ⟪b - c, b - c⟫)) * ⟪b - c, b - c⟫ = 0 := by
      rw [hq] at hr; linear_combination hr
    rcases mul_eq_zero.1 h2 with h | h
    · linarith
    · exact absurd h hrr.ne'
  refine k17a_cell1_gen (u2 := β1 - (β6 + γ6)) (t2 := (β6 + γ6) - 1) hdet hc' hb' ha' one_pos hβ1 hβ6 hγ6 hs
    (by linarith) (by nlinarith) (by linarith) ?_ ?_ ?_
  · intro lam h0 h1; nlinarith
  · intro lam h0 h1; nlinarith
  · intro lam h0 h1 w hw hinj'
    have hz : ∀ t : ℝ × ℝ × ℝ, ⟪fpoint (a - d) (c - d) (b - c) d t, b - c⟫ =
        ⟪d, b - c⟫ + t.1 * ⟪a - d, b - c⟫ + t.2.1 * ⟪c - d, b - c⟫ + t.2.2 * ⟪b - c, b - c⟫ :=
      fun t => inner_fpoint _ _ _ _ _ _
    have e0 := hw 0; have e3 := hw 3; have e4 := hw 4
    simp only [k5b_cyc1, pc5_0, pc5_3, pc5_4, k17a_wexp] at e0 e3 e4
    refine k17a_lex_D1 _ w hinj' ?_ ?_ ?_ ?_ ?_
    · simp only [k5b_cyc1, pc5_0, pc5_1, hz, hρ, hq]; nlinarith
    · simp only [k5b_cyc1, pc5_2, pc5_3, hz, hρ, hq]; nlinarith
    · simp only [k5b_cyc1, pc5_0, pc5_4, hz, hρ, hq]; ring
    · simp only [k5b_cyc1, pc5_3, pc5_4, hz, hρ, hq]; ring
    · rw [e3, e4, hρ, hq]
      have hpos : 0 < ⟪c - d, c - d⟫ - ⟪b - c, b - c⟫ := by linarith
      nlinarith [mul_pos hpos (mul_pos (sub_pos.2 h1) (sub_pos.2 hs))]

set_option maxHeartbeats 6400000 in
theorem k17a_dn2_D2 {a a' b b' c c' d : ℝ³} {β1 β6 γ6 : ℝ}
    (hdet : det3 (a - d) (b - d) (c - d) ≠ 0)
    (hc' : c' = d + (1:ℝ) • (a - d) + β1 • (b - d)) (hb' : b' = d + (1:ℝ) • (a - d) + β1 • (c - d))
    (ha' : a' = d + β6 • (b - d) + γ6 • (c - d))
    (hβ1 : 0 < β1) (hβ6 : 0 < β6) (hγ6 : 0 < γ6) (hs : 1 < β6 + γ6)
    (hrel : K16Rel a b c d 1 β1) (hD : K6sD2 a a' b b' c c' d) :
    HasLexCell (V8 a a' b b' c c' d) := by
  obtain ⟨hρ, hζ, -⟩ := hD
  have hr := k17a_rel_atoms hrel hρ
  have hrr : 0 < ⟪b - c, b - c⟫ := by
    apply real_inner_self_pos.2
    intro h0
    apply hdet
    have : b = c := sub_eq_zero.1 h0
    subst this
    simp only [det3_expand, PiLp.sub_apply]; ring
  have hqq : 0 < ⟪c - d, c - d⟫ := by
    apply real_inner_self_pos.2
    intro h0
    apply hdet
    have : c = d := sub_eq_zero.1 h0
    subst this
    simp only [det3_expand, PiLp.sub_apply]; ring
  have hbd : b' - d = (a - d) + β1 • (c - d) := by rw [hb']; module
  have hq : ⟪c - d, b - c⟫ = 0 := by
    rw [hbd, inner_add_left, inner_smul_left, hρ] at hζ
    simp only [conj_trivial] at hζ
    have : β1 * ⟪c - d, b - c⟫ = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hβ1.ne'
    · exact h
  have hpq : ⟪a - d, c - d⟫ = -(β1 - 1) * ⟪c - d, c - d⟫ := by
    have h2 : (⟪a - d, c - d⟫ + (β1 - 1) * ⟪c - d, c - d⟫) * ⟪b - c, b - c⟫ = 0 := by
      rw [hq] at hr; linear_combination hr
    rcases mul_eq_zero.1 h2 with h | h
    · linarith
    · exact absurd h hrr.ne'
  refine k17a_cell1_gen (u2 := β1 - 1) (t2 := 1) hdet hc' hb' ha' one_pos hβ1 hβ6 hγ6 hs
    (by linarith) (by nlinarith) (by norm_num) ?_ ?_ ?_
  · intro lam h0 h1; nlinarith
  · intro lam h0 h1; nlinarith
  · intro lam h0 h1 w hw hinj'
    have hz : ∀ t : ℝ × ℝ × ℝ, ⟪fpoint (a - d) (c - d) (b - c) d t, b - c⟫ =
        ⟪d, b - c⟫ + t.1 * ⟪a - d, b - c⟫ + t.2.1 * ⟪c - d, b - c⟫ + t.2.2 * ⟪b - c, b - c⟫ :=
      fun t => inner_fpoint _ _ _ _ _ _
    have e0 := hw 0; have e1 := hw 1
    simp only [k5b_cyc1, pc5_0, pc5_1, k17a_wexp] at e0 e1
    refine k17a_lex_D2 _ w hinj' ?_ ?_ ?_ ?_ ?_
    · simp only [k5b_cyc1, pc5_0, pc5_1, hz, hρ, hq]; ring
    · simp only [k5b_cyc1, pc5_0, pc5_4, hz, hρ, hq]; ring
    · simp only [k5b_cyc1, pc5_0, pc5_2, hz, hρ, hq]; nlinarith
    · simp only [k5b_cyc1, pc5_0, pc5_3, hz, hρ, hq]; nlinarith
    · rw [e0, e1, hρ, hq]
      nlinarith [mul_pos hβ1 (mul_pos hqq h0)]

/-- **S1.10** (`K6sDN2one`, `α1 = 1`, D1 or D2): the cell `(a,d,b,a',b')` at `b - c`, no split literal, no leftover. -/
theorem k17a_dn2one {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (h : K6sDN2one a a' b b' c c' d) :
    HasLexCell (V8 a a' b b' c c' d) := by
  obtain ⟨hκ, hN2, hD, β, hc2⟩ := h
  obtain ⟨α1, β1, β6, γ6, hdet, hc', hb', ha', hα1, hβ1, h1, hβ6, hγ6, h3⟩ := k6m_coords_n2 W hκ hN2
  have hu := k5b_coeff3 hdet (x := α1) (y := β1) (z := 0) (x' := 1) (y' := β) (z' := 0)
    (by have e := hc'.symm.trans hc2; linear_combination (norm := module) e)
  obtain ⟨rfl, rfl, -⟩ := hu
  have hρ : ⟪a - d, b - c⟫ = 0 := by rcases hD with hD | hD <;> exact hD.1
  have hrel := k17a_n2_rel W hκ hN2 hρ hdet hc' ha' hα1 hγ6 h3
  rcases hD with hD | hD
  · exact k17a_dn2_D1 hdet hc' hb' ha' hβ1 hβ6 hγ6 h3 hrel hD
  · exact k17a_dn2_D2 hdet hc' hb' ha' hβ1 hβ6 hγ6 h3 hrel hD

end Type08Sp
end Minimality
