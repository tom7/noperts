module

public import Minimality.Type08S.C2K22C1bE

@[expose] public section


/-!
# K22C1b / F: `K22C1Left` minus the edge-on cells `C⁻`, `C⁺` (view `w = λ q + r` in the base plane)

`K22C1Left` (right prismatoid, `pq = pr = 0`).  Choice of `λ > 0` (`Q = λ qq + qr`, `R = λ qr + rr`):
* `qr < 0`: `λ = -qr / (2 qq)`, `Q < 0 < R`, cell `C⁻` (i);
* `qr ≥ 0`, `β1 > 1`: `λ = (γ4 rr - β1 qr) / (2 (β1 qq + 1))`, `β1 Q < γ4 R`, `C⁻` (ii)  (uses `β1 (1-γ6) < γ4` and
  `⟪c-d, c-a'⟫ ≥ 0`);
* `qr ≥ 0`, `β1 < 1`, `qr < (1-γ6) rr`: `λ = ((1-γ6) rr - qr) / (2 (qq + 1))`, `Q + γ6 R < R`, `C⁺` (iv);
* `qr ≥ 0`, `β1 < 1`, `γ4 < 1`, `qr = (1-γ6) rr`: `λ = 1`, `C⁺` (v);
* `qr ≥ 0`, `β1 = 1 < γ4`, `γ4 qr < qq`: `λ = (γ4 rr - qr)/(qq - γ4 qr) + 1`, `γ4 R < Q`, `C⁻` (iii).
Leftover `K22C1bLeft`: `β1 = 1`, `qr ≥ 0`, (`γ4 < 1` or `qq ≤ γ4 qr`); or `β1 < 1 ≤ γ4`, `⟪c-d, c-a'⟫ = 0`.
-/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

/-- Leftover of `K22C1Left` after the edge-on cells. -/
def K22C1bLeft (a a' b b' c c' d : ℝ³) : Prop :=
  ⟪a - d, b - d⟫ = 0 ∧ ⟪a - d, c - d⟫ = 0 ∧
  ∃ β1 γ4 γ6 : ℝ, det3 (a - d) (b - d) (c - d) ≠ 0 ∧
    c' = d + (1 : ℝ) • (a - d) + β1 • (b - d) ∧ b' = d + (1 : ℝ) • (a - d) + γ4 • (c - d) ∧
    a' = d + (1 : ℝ) • (b - d) + γ6 • (c - d) ∧ 0 < β1 ∧ 0 < γ4 ∧ 0 < γ6 ∧ γ6 < 1 ∧ β1 * (1 - γ6) < γ4 ∧
    ((β1 = 1 ∧ 0 ≤ ⟪b - d, c - d⟫ ∧ (γ4 < 1 ∨ (1 < γ4 ∧ ⟪b - d, b - d⟫ ≤ γ4 * ⟪b - d, c - d⟫))) ∨
      (β1 < 1 ∧ ⟪c - d, c - a'⟫ = 0 ∧ 1 ≤ γ4))

set_option maxHeartbeats 3200000 in
theorem k22c1b_edge {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d)
    (h : K6t3LeftPc a a' b b' c c' d) (hL : K22C1Left a a' b b' c c' d) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K22C1bLeft a a' b b' c c' d := by
  obtain ⟨hpq, hpr, β1, γ4, γ6, hdet, hc', hb', ha', hβ1, hγ4, hγ6, hγ61, hne⟩ := hL
  obtain ⟨h5, hu, hwc⟩ := h
  obtain ⟨β1', γ4', γ6', -, hc'', hb'', ha'', -, -, -, -, hfr⟩ := k17gc_pc_frame W h5
  have hq0 : b - d ≠ 0 := by intro h0; apply hdet; rw [h0]; simp [det3_expand]
  have hr0 : c - d ≠ 0 := by intro h0; apply hdet; rw [h0]; simp [det3_expand]
  have eβ : β1' = β1 := by
    have : (β1' - β1) • (b - d) = 0 := by
      have := hc''.symm.trans hc'; rw [sub_smul]
      have h2 : β1' • (b - d) = β1 • (b - d) := by
        have := congrArg (fun x => x - d - (1 : ℝ) • (a - d)) this; simpa using this
      rw [h2, sub_self]
    rcases smul_eq_zero.1 this with h' | h'
    · linarith
    · exact (hq0 h').elim
  have eγ4 : γ4' = γ4 := by
    have : (γ4' - γ4) • (c - d) = 0 := by
      have := hb''.symm.trans hb'; rw [sub_smul]
      have h2 : γ4' • (c - d) = γ4 • (c - d) := by
        have := congrArg (fun x => x - d - (1 : ℝ) • (a - d)) this; simpa using this
      rw [h2, sub_self]
    rcases smul_eq_zero.1 this with h' | h'
    · linarith
    · exact (hr0 h').elim
  have eγ6 : γ6' = γ6 := by
    have : (γ6' - γ6) • (c - d) = 0 := by
      have := ha''.symm.trans ha'; rw [sub_smul]
      have h2 : γ6' • (c - d) = γ6 • (c - d) := by
        have := congrArg (fun x => x - d - (1 : ℝ) • (b - d)) this; simpa using this
      rw [h2, sub_self]
    rcases smul_eq_zero.1 this with h' | h'
    · linarith
    · exact (hr0 h').elim
  rw [eβ, eγ4, eγ6] at hfr
  -- Gram data
  obtain ⟨qq, hqq⟩ : ∃ x, ⟪b - d, b - d⟫ = x := ⟨_, rfl⟩
  obtain ⟨rr, hrr⟩ : ∃ x, ⟪c - d, c - d⟫ = x := ⟨_, rfl⟩
  obtain ⟨qr, hqr⟩ : ∃ x, ⟪b - d, c - d⟫ = x := ⟨_, rfl⟩
  have hrq : ⟪c - d, b - d⟫ = qr := by rw [real_inner_comm]; exact hqr
  have hqqp : 0 < qq := hqq ▸ real_inner_self_pos.2 hq0
  have hrrp : 0 < rr := hrr ▸ real_inner_self_pos.2 hr0
  have hcs : qr * qr < qq * rr := by
    have hu0 : rr • (b - d) - qr • (c - d) ≠ 0 := by
      intro h0
      have e : rr • (b - d) = qr • (c - d) := sub_eq_zero.1 h0
      have h1 : det3 (a - d) (rr • (b - d)) (c - d) = rr * det3 (a - d) (b - d) (c - d) := by
        simp only [det3_expand, PiLp.smul_apply, smul_eq_mul]; ring
      have h2 : det3 (a - d) (qr • (c - d)) (c - d) = 0 := by
        simp only [det3_expand, PiLp.smul_apply, smul_eq_mul]; ring
      rw [e, h2] at h1
      exact hdet (by
        rcases mul_eq_zero.1 h1.symm with h3 | h3
        · linarith
        · exact h3)
    have := real_inner_self_pos.2 hu0
    have key : ∀ x y : ℝ³, ⟪rr • x - qr • y, rr • x - qr • y⟫ =
        rr * rr * ⟪x, x⟫ - 2 * rr * qr * ⟪x, y⟫ + qr * qr * ⟪y, y⟫ := by
      intro x y
      simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
        real_inner_comm x y]
      ring
    rw [key, hqq, hqr, hrr] at this
    nlinarith
  have hwc' : 0 ≤ (1 - γ6) * rr - qr := by
    have e : c - a' = (1 - γ6) • (c - d) - (b - d) := by rw [ha']; module
    rw [e, inner_sub_right, inner_smul_right, hrr, hrq] at hwc
    linarith
  have hQ : ∀ l : ℝ, ⟪b - d, l • (b - d) + (c - d)⟫ = l * qq + qr := by
    intro l; rw [inner_add_right, real_inner_smul_right, hqq, hqr]
  have hR : ∀ l : ℝ, ⟪c - d, l • (b - d) + (c - d)⟫ = l * qr + rr := by
    intro l; rw [inner_add_right, real_inner_smul_right, hrq, hrr]
  have cellM := fun l (hl : 0 < l) hreg =>
    k22c1b_cellM (Q := l * qq + qr) (R := l * qr + rr) hpq hpr hdet hc' hb' ha' hβ1 hγ4 hγ6 hγ61 hl
      (hQ l) (hR l) hreg
  have cellP := fun l (hl : 0 < l) hreg =>
    k22c1b_cellP (Q := l * qq + qr) (R := l * qr + rr) hpq hpr hdet hc' hb' ha' hβ1 hγ4 hγ6 hγ61 hl
      (hQ l) (hR l) hreg
  rcases lt_or_ge qr 0 with hneg | hnn
  · -- (i)
    left
    have hl : 0 < -qr / (2 * qq) := div_pos (by linarith) (by linarith)
    refine cellM _ hl (Or.inl ⟨?_, ?_⟩)
    · rw [div_mul_eq_mul_div, div_add' _ _ _ (by positivity)]
      apply div_neg_of_neg_of_pos _ (by positivity); nlinarith
    · rw [div_mul_eq_mul_div, div_add' _ _ _ (by positivity)]
      apply div_pos _ (by positivity); nlinarith
  rcases lt_trichotomy β1 1 with hb1 | hb1 | hb1
  · by_cases hq1 : qr < (1 - γ6) * rr
    · -- (iv)
      left
      set E := (1 - γ6) * rr - qr with hE
      have hEp : 0 < E := by linarith
      set l := E / (2 * (qq + 1)) with hl
      have hl0 : 0 < l := div_pos hEp (by linarith)
      have hlq : l * qq < E := by
        rw [hl, div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]; nlinarith
      refine cellP l hl0 (Or.inl ⟨hb1, by nlinarith, ?_⟩)
      nlinarith [mul_nonneg hl0.le hnn, mul_nonneg (mul_nonneg hl0.le hnn) (by linarith : (0:ℝ) ≤ 1 - γ6)]
    · by_cases hg : γ4 < 1
      · -- (v)
        left
        refine cellP 1 one_pos (Or.inr ⟨hb1, hg, by nlinarith, by nlinarith, ?_⟩)
        have e1 : (1 - γ6) * qr * rr ≤ qr * qr := by nlinarith
        have e2 : (1 - γ6) * qr < qq := by
          by_contra hc; push_neg at hc
          nlinarith [mul_le_mul_of_nonneg_right hc hrrp.le]
        nlinarith
      · -- leftover
        right
        refine ⟨hpq, hpr, β1, γ4, γ6, hdet, hc', hb', ha', hβ1, hγ4, hγ6, hγ61, hfr, Or.inr ⟨hb1, ?_, by linarith⟩⟩
        have e : c - a' = (1 - γ6) • (c - d) - (b - d) := by rw [ha']; module
        rw [e, inner_sub_right, inner_smul_right, hrr, hrq]
        linarith
  · -- β1 = 1
    subst hb1
    have hg1 : γ4 ≠ 1 := hne.resolve_left (fun h' => h' rfl)
    by_cases hg : 1 < γ4 ∧ γ4 * qr < qq
    · -- (iii)
      left
      obtain ⟨hg, hgq⟩ := hg
      have hD : 0 < qq - γ4 * qr := by linarith
      have hN : 0 < γ4 * rr - qr := by nlinarith
      set l := (γ4 * rr - qr) / (qq - γ4 * qr) + 1 with hl
      have hl0 : 0 < l := by positivity
      have hlD : l * (qq - γ4 * qr) = (γ4 * rr - qr) + (qq - γ4 * qr) := by
        rw [hl, add_mul, div_mul_cancel₀ _ hD.ne']; ring
      refine cellM l hl0 (Or.inr (Or.inr ⟨rfl, hg, by nlinarith, by nlinarith⟩))
    · right
      refine ⟨hpq, hpr, 1, γ4, γ6, hdet, hc', hb', ha', hβ1, hγ4, hγ6, hγ61, hfr, Or.inl ⟨rfl, hqr ▸ hnn, ?_⟩⟩
      rcases lt_or_gt_of_ne hg1 with h' | h'
      · exact Or.inl h'
      · right; refine ⟨h', ?_⟩; push_neg at hg; rw [hqq, hqr]; exact hg h'
  · -- (ii)
    left
    set E := γ4 * rr - β1 * qr with hE
    have hEp : 0 < E := by nlinarith
    set l := E / (2 * (β1 * qq + 1)) with hl
    have hl0 : 0 < l := div_pos hEp (by nlinarith)
    have hlq : l * (β1 * qq) < E := by
      rw [hl, div_mul_eq_mul_div, div_lt_iff₀ (by nlinarith)]
      nlinarith [mul_pos hEp (by nlinarith : (0:ℝ) < β1 * qq + 2)]
    refine cellM l hl0 (Or.inr (Or.inl ⟨hb1, by nlinarith, ?_⟩))
    nlinarith [mul_nonneg (mul_nonneg hl0.le hnn) hγ4.le]

end C2
end Type08Sp
end Minimality
