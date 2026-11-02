module

public import Minimality.Type08S.C2K20ZA

@[expose] public section


/-!
# K21 / A: prism corners of the T/T' strata closed by `k20_prism3`

* `k21_pa_frame`, `k21_pa_prism`: Pa (`T'`, `κ_c = 0`) at `β1 = 1`: `γ4 = 1`; with `pq = pr = 0` a right prism over
  `(d,b,c)` along `p` (heights `1, 1, α4`), `a'` beyond `bc`.  Generalizes `k20_s15_corner` (no `α4 = 1`).
* `k21_pa_pq`: in `K17fLeftPa` at `β1 = 1`, `pq = 0` or a lex cell.
* `k21_b11`: Ta B11 (`β1 = 1`, `pq = pr = 0`, `T`): right prism along `p` (heights `1, α1, α4`), `a'` beyond `bc`.
* `k21_tca41`: Tc A41 (`α4 = 1`, `qr = pr = 0`, `T`, `κ_a = 0` ⟹ `β6 = 1`): right prism along `r` over `(d,a,b)`
  (heights `1, γ4, 1`), `c'` beyond `ab`.
-/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1600000

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

theorem k21_pa_frame {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (h : K5ZsPa a a' b b' c c' d)
    (hβ : det3 (a - d) (c' - b) (c - d) * det3 (a - d) (b - d) (c - d) = 0) :
    ∃ α4 β6 γ6 : ℝ, det3 (a - d) (b - d) (c - d) ≠ 0 ∧
      c' = d + (1 : ℝ) • (a - d) + (1 : ℝ) • (b - d) ∧ b' = d + α4 • (a - d) + (1 : ℝ) • (c - d) ∧
      a' = d + β6 • (b - d) + γ6 • (c - d) ∧ 0 < α4 ∧ 1 < β6 + γ6 := by
  obtain ⟨α1, α4, β1, γ4, β6, γ6, hdet, hc', hb', ha', -, -, -, hα4p, -, -, -, -, hβγ, -, -⟩ :=
    norm08w_coords W
  obtain ⟨hT', -, hκ, -⟩ := h
  set P := a - d with hP
  set Q := b - d with hQ
  set R := c - d with hR
  have eb : b = d + Q := by simp [Q]
  have ec : c = d + R := by simp [R]
  have ea : a = d + P := by simp [P]
  obtain ⟨t, ht⟩ := hT'
  have hα1 : α1 = 1 := by
    have e : (α1 - 1) • P + (β1 - t) • Q + (0 : ℝ) • R = 0 := by
      have : (α1 - 1) • P + (β1 - t) • Q + (0 : ℝ) • R = (c' - a) - t • Q := by rw [hc', ea]; module
      rw [this, ht]; exact sub_self _
    have := (det3_indep hdet e).1; linarith
  have hβ1 : β1 = 1 := by
    rcases mul_eq_zero.1 hβ with h0 | h0
    · have e2 : det3 P (c' - b) R = (β1 - 1) * det3 P Q R := by
        rw [show c' - b = α1 • P + (β1 - 1) • Q + (0 : ℝ) • R by rw [hc', eb]; module]
        have := k20_det_lin P Q R 1 0 0 α1 (β1 - 1) 0 0 0 1
        simp only [one_smul, zero_smul, add_zero, zero_add] at this ⊢
        rw [this]; ring
      rw [e2] at h0
      rcases mul_eq_zero.1 h0 with h | h
      · linarith
      · exact absurd h hdet
    · exact absurd h0 hdet
  have hγ4 : γ4 = 1 := by
    have e2 : det3 (c - b) (b' - b) (c' - b) = (1 - γ4) * det3 P Q R := by
      rw [show c - b = (0 : ℝ) • P + (-1 : ℝ) • Q + (1 : ℝ) • R by rw [ec, eb]; module,
        show b' - b = α4 • P + (-1 : ℝ) • Q + γ4 • R by rw [hb', eb]; module,
        show c' - b = α1 • P + (β1 - 1) • Q + (0 : ℝ) • R by rw [hc', eb]; module,
        k20_det_lin, hα1, hβ1]; ring
    rw [e2] at hκ
    rcases mul_eq_zero.1 hκ with h | h
    · linarith
    · exact absurd h hdet
  subst hα1 hβ1 hγ4
  exact ⟨α4, β6, γ6, hdet, hc', hb', ha', hα4p, hβγ⟩

/-- Pa at `β1 = 1` with `pq = pr = 0` is Rupert (any `α4`). -/
theorem k21_pa_prism {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (h : K5ZsPa a a' b b' c c' d)
    (hβ : det3 (a - d) (c' - b) (c - d) * det3 (a - d) (b - d) (c - d) = 0)
    (hpq : ⟪a - d, b - d⟫ = 0) (hpr : ⟪a - d, c - d⟫ = 0) :
    IsRupert (V8 a a' b b' c c' d) := by
  obtain ⟨α4, β6, γ6, hdet, hc', hb', ha', hα4, hβγ⟩ := k21_pa_frame W h hβ
  set P := a - d with hP
  set Q := b - d with hQ
  set R := c - d with hR
  have key := k20_prism3 d P Q R (β := β6) (γ := γ6) (z0 := 1) (z1 := 1) (z2 := α4) hpq hpr
    (by intro h0; apply hdet; rw [← h0]; simp only [det3_expand]; ring) one_pos one_pos hα4 hβγ
  have q1 : d + Q = b := by simp [Q]
  have q2 : d + R = c := by simp [R]
  have q3 : d + (β6 • Q + γ6 • R) = a' := by rw [ha', add_assoc]
  have q4 : d + (1 : ℝ) • P = a := by simp [P]
  have q5 : d + Q + (1 : ℝ) • P = c' := by rw [hc']; module
  have q6 : d + R + α4 • P = b' := by rw [hb']; module
  rw [q5, q6, q3, q4, q1, q2] at key
  convert key using 1
  ext x; simp only [V8, Finset.mem_insert, Finset.mem_singleton]; tauto

/-- In `K17fLeftPa` at `β1 = 1`: a lex cell, or `pq = 0`. -/
theorem k21_pa_pq {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (h : K17fLeftPa a a' b b' c c' d)
    (hβ : det3 (a - d) (c' - b) (c - d) * det3 (a - d) (b - d) (c - d) = 0) :
    HasLexCell (V8 a a' b b' c c' d) ∨ ⟪a - d, b - d⟫ = 0 := by
  obtain ⟨hctx, hL⟩ := h
  obtain ⟨α4, β6, γ6, hdet, hc', hb', ha', hα4, hβγ⟩ := k21_pa_frame W hctx hβ
  have hb'c : ⟪b' - c, d - b⟫ = 0 → ⟪a - d, b - d⟫ = 0 := by
    intro h0
    have e : b' - c = α4 • (a - d) := by rw [hb']; module
    rw [e, real_inner_smul_left, ← neg_sub b d, inner_neg_right] at h0
    rcases mul_eq_zero.1 h0 with h | h
    · linarith
    · linarith
  rcases hL with ⟨h1, h2, -⟩ | ⟨h0, -, -, -⟩ | ⟨hα, -, hβ' | h0⟩
  · right; rw [← neg_sub b d, inner_neg_right] at h2; linarith
  · exact Or.inr (hb'c h0)
  · rcases k17gc_s15 W hctx hα hβ with h3 | hZ
    · exact Or.inl h3
    · right
      have e : a - c' = (-1 : ℝ) • (b - d) := by rw [hc']; module
      rw [e, real_inner_smul_right] at hZ; linarith
  · exact Or.inr (hb'c h0)

/-- Ta B11 (`K17hTaB11`) is Rupert: right prism over `(d,b,c)` along `p`, heights `1, α1, α4`. -/
theorem k21_b11 {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (h : K17hTaB11 a a' b b' c c' d) :
    IsRupert (V8 a a' b b' c c' d) := by
  obtain ⟨-, ⟨hT, hκ, hβ, hpq⟩, hpr⟩ := h
  obtain ⟨α1, α4, β1, γ4, β6, hdet, hc', hb', ha', hα1, -, -, hα4, -, -, hβ6, -⟩ := norm08w_coordsT W hT
  set P := a - d with hP
  set Q := b - d with hQ
  set R := c - d with hR
  have eb : b = d + Q := by simp [Q]
  have ec : c = d + R := by simp [R]
  have hβ1 : β1 = 1 := by
    have e2 : det3 P (c' - b) R = (β1 - 1) * det3 P Q R := by
      rw [show c' - b = α1 • P + (β1 - 1) • Q + (0 : ℝ) • R by rw [hc', eb]; module]
      have := k20_det_lin P Q R 1 0 0 α1 (β1 - 1) 0 0 0 1
      simp only [one_smul, zero_smul, add_zero, zero_add] at this ⊢
      rw [this]; ring
    rw [e2] at hβ
    rcases mul_eq_zero.1 hβ with h | h
    · linarith
    · exact absurd h hdet
  have hγ4 : γ4 = 1 := by
    have e2 : det3 (c - b) (b' - b) (c' - b) = α1 * (1 - γ4) * det3 P Q R := by
      rw [show c - b = (0 : ℝ) • P + (-1 : ℝ) • Q + (1 : ℝ) • R by rw [ec, eb]; module,
        show b' - b = α4 • P + (-1 : ℝ) • Q + γ4 • R by rw [hb', eb]; module,
        show c' - b = α1 • P + (β1 - 1) • Q + (0 : ℝ) • R by rw [hc', eb]; module,
        k20_det_lin, hβ1]; ring
    rw [e2] at hκ
    rcases mul_eq_zero.1 hκ with h | h
    · rcases mul_eq_zero.1 h with h | h
      · linarith
      · linarith
    · exact absurd h hdet
  subst hβ1 hγ4
  have key := k20_prism3 d P Q R (β := β6) (γ := 1) (z0 := 1) (z1 := α1) (z2 := α4)
    (by rw [real_inner_comm]; exact hpq) hpr
    (by intro h0; apply hdet; rw [← h0]; simp only [det3_expand]; ring) one_pos hα1 hα4 (by linarith)
  have q1 : d + Q = b := by simp [Q]
  have q2 : d + R = c := by simp [R]
  have q3 : d + (β6 • Q + (1 : ℝ) • R) = a' := by rw [ha', add_assoc]
  have q4 : d + (1 : ℝ) • P = a := by simp [P]
  have q5 : d + Q + α1 • P = c' := by rw [hc']; module
  have q6 : d + R + α4 • P = b' := by rw [hb']; module
  rw [q5, q6, q3, q4, q1, q2] at key
  convert key using 1
  ext x; simp only [V8, Finset.mem_insert, Finset.mem_singleton]; tauto

/-- Tc A41 (`K17hTcA41`) is Rupert: right prism over `(d,a,b)` along `r`, heights `1, γ4, 1`, `c'` beyond `ab`. -/
theorem k21_tca41 {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (h : K17hTcA41 a a' b b' c c' d) :
    IsRupert (V8 a a' b b' c c' d) := by
  obtain ⟨-, ⟨hT, hκa, hα⟩, hqr, hpr⟩ := h
  obtain ⟨α1, α4, β1, γ4, β6, hdet, hc', hb', ha', hα1, hβ1, hαβ, hα4, hγ4, -, hβ6, -⟩ := norm08w_coordsT W hT
  set P := a - d with hP
  set Q := b - d with hQ
  set R := c - d with hR
  have eb : b = d + Q := by simp [Q]
  have ea : a = d + P := by simp [P]
  have hα41 : α4 = 1 := by
    have e2 : det3 (b' - a) Q R = (α4 - 1) * det3 P Q R := by
      rw [show b' - a = (α4 - 1) • P + (0 : ℝ) • Q + γ4 • R by rw [hb', ea]; module]
      have := k20_det_lin P Q R (α4 - 1) 0 γ4 0 1 0 0 0 1
      simp only [one_smul, zero_smul, add_zero, zero_add] at this ⊢
      rw [this]; ring
    rw [e2] at hα
    rcases mul_eq_zero.1 hα with h | h
    · linarith
    · exact absurd h hdet
  subst hα41
  have hβ61 : β6 = 1 := by
    have e2 : det3 (b - a) (a' - a) (b' - a) = γ4 * (1 - β6) * det3 P Q R := by
      rw [show b - a = (-1 : ℝ) • P + (1 : ℝ) • Q + (0 : ℝ) • R by rw [ea, eb]; module,
        show a' - a = (-1 : ℝ) • P + β6 • Q + (1 : ℝ) • R by rw [ha', ea]; module,
        show b' - a = (0 : ℝ) • P + (0 : ℝ) • Q + γ4 • R by rw [hb', ea]; module,
        k20_det_lin]; ring
    rw [e2] at hκa
    rcases mul_eq_zero.1 hκa with h | h
    · rcases mul_eq_zero.1 h with h | h
      · linarith
      · linarith
    · exact absurd h hdet
  subst hβ61
  have key := k20_prism3 d R P Q (β := α1) (γ := β1) (z0 := 1) (z1 := γ4) (z2 := 1)
    (by rw [real_inner_comm]; exact hpr) (by rw [real_inner_comm]; exact hqr) hdet one_pos hγ4 one_pos hαβ
  have q1 : d + P = a := by simp [P]
  have q2 : d + Q = b := by simp [Q]
  have q3 : d + (α1 • P + β1 • Q) = c' := by rw [hc', add_assoc]
  have q4 : d + (1 : ℝ) • R = c := by simp [R]
  have q5 : d + P + γ4 • R = b' := by rw [hb']; module
  have q6 : d + Q + (1 : ℝ) • R = a' := by rw [ha']; module
  rw [q5, q6, q3, q4, q1, q2] at key
  convert key using 1
  ext x; simp only [V8, Finset.mem_insert, Finset.mem_singleton]; tauto

end C2
end Type08Sp
end Minimality
