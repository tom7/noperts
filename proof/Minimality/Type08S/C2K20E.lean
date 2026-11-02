module

public import Minimality.Type08S.C2K20D
public import Minimality.Type08S.C2K17GB1
public import Minimality.Type08S.C2K17GB3
public import Minimality.Type08S.C2K5LB
public import Minimality.Type08S.C2K5ZD

@[expose] public section


/-!
# K20 / E: the S1.5 corner and the S1.4 leftover are Rupert (truncated right prisms plus a base point)

* `k20_s15_corner`: K18's S1.5 corner (`k18_s15_tie`'s leftover `pq = pr = 0`).  `T'`, `hβ`, `hα` and the
  `b c b' c'` coplanarity force `α1 = β1 = α4 = γ4 = 1`: a right prism over `(d,b,c)` (axis `p = a - d`) with `a'`
  in the base plane beyond `bc`.  On part of this corner there is NO lex cell at any view (K20 numerics), so the
  closure is `IsRupert`, not `HasLexCell`.
* `k20_s14`: S1.4 (`k17gb_s14a`'s hypotheses, `β6 = 1`) at the tie `⟪a-b',a-c'⟫ = 0` (`pr = 0`): `qr = pr = 0`,
  a truncated right prism over `(d,a,b)` along `r = c - d` (heights `1, γ4, 1`) with `c'` in the base plane beyond `ab`.
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

theorem k20_det_lin (P Q R : ℝ³) (x1 y1 z1 x2 y2 z2 x3 y3 z3 : ℝ) :
    det3 (x1 • P + y1 • Q + z1 • R) (x2 • P + y2 • Q + z2 • R) (x3 • P + y3 • Q + z3 • R) =
      (x1 * (y2 * z3 - z2 * y3) - y1 * (x2 * z3 - z2 * x3) + z1 * (x2 * y3 - y2 * x3)) * det3 P Q R := by
  simp only [det3_expand, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring

theorem k20_s15_corner {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (h : K5ZsPa a a' b b' c c' d)
    (hα : det3 (b' - a) (b - d) (c - d) = 0)
    (hβ : det3 (a - d) (c' - b) (c - d) * det3 (a - d) (b - d) (c - d) = 0)
    (hpq : ⟪a - d, b - d⟫ = 0) (hpr : ⟪a - d, c - d⟫ = 0) :
    IsRupert (V8 a a' b b' c c' d) := by
  obtain ⟨α1, α4, β1, γ4, β6, γ6, hdet, hc', hb', ha', -, -, -, -, -, -, -, -, hβγ, -, -⟩ :=
    norm08w_coords W
  obtain ⟨hT', -, hκ, -⟩ := h
  set P := a - d with hP
  set Q := b - d with hQ
  set R := c - d with hR
  have eb : b = d + Q := by simp [Q]
  have ec : c = d + R := by simp [R]
  have ea : a = d + P := by simp [P]
  -- α1 = 1 (T')
  obtain ⟨t, ht⟩ := hT'
  have hα1 : α1 = 1 := by
    have e : (α1 - 1) • P + (β1 - t) • Q + (0 : ℝ) • R = 0 := by
      have : (α1 - 1) • P + (β1 - t) • Q + (0 : ℝ) • R = (c' - a) - t • Q := by rw [hc', ea]; module
      rw [this, ht]; exact sub_self _
    have := (det3_indep hdet e).1; linarith
  -- β1 = 1
  have hβ1 : β1 = 1 := by
    rcases mul_eq_zero.1 hβ with h0 | h0
    · have : c' - b = (0 : ℝ) • P + (β1 - 1) • Q + (0 : ℝ) • R + α1 • P := by rw [hc', eb]; module
      have e2 : det3 P (c' - b) R = (β1 - 1) * det3 P Q R := by
        rw [show c' - b = α1 • P + (β1 - 1) • Q + (0 : ℝ) • R by rw [hc', eb]; module]
        have := k20_det_lin P Q R 1 0 0 α1 (β1 - 1) 0 0 0 1
        simp only [one_smul, zero_smul, add_zero, zero_add] at this ⊢
        rw [this]; ring
      rw [e2] at h0
      rcases mul_eq_zero.1 h0 with h | h
      · linarith
      · exact absurd h hdet
    · exact absurd h0 hdet
  -- α4 = 1
  have hα4 : α4 = 1 := by
    have e2 : det3 (b' - a) Q R = (α4 - 1) * det3 P Q R := by
      rw [show b' - a = (α4 - 1) • P + (0 : ℝ) • Q + γ4 • R by rw [hb', ea]; module]
      have := k20_det_lin P Q R (α4 - 1) 0 γ4 0 1 0 0 0 1
      simp only [one_smul, zero_smul, add_zero, zero_add] at this ⊢
      rw [this]; ring
    rw [e2] at hα
    rcases mul_eq_zero.1 hα with h | h
    · linarith
    · exact absurd h hdet
  -- γ4 = 1 (b, c, b', c' coplanar)
  have hγ4 : γ4 = 1 := by
    have e2 : det3 (c - b) (b' - b) (c' - b) = (1 - γ4) * det3 P Q R := by
      rw [show c - b = (0 : ℝ) • P + (-1 : ℝ) • Q + (1 : ℝ) • R by rw [ec, eb]; module,
        show b' - b = α4 • P + (-1 : ℝ) • Q + γ4 • R by rw [hb', eb]; module,
        show c' - b = α1 • P + (β1 - 1) • Q + (0 : ℝ) • R by rw [hc', eb]; module,
        k20_det_lin, hα1, hβ1, hα4]; ring
    rw [e2] at hκ
    rcases mul_eq_zero.1 hκ with h | h
    · linarith
    · exact absurd h hdet
  subst hα1 hβ1 hα4 hγ4
  have key := k20_prism3 d P Q R (β := β6) (γ := γ6) (z0 := 1) (z1 := 1) (z2 := 1) hpq hpr
    (by intro h0; apply hdet; rw [← h0]; simp only [det3_expand]; ring) one_pos one_pos one_pos hβγ
  have q1 : d + Q = b := by simp [Q]
  have q2 : d + R = c := by simp [R]
  have q3 : d + (β6 • Q + γ6 • R) = a' := by rw [ha', add_assoc]
  have q4 : d + (1 : ℝ) • P = a := by simp [P]
  have q5 : d + Q + (1 : ℝ) • P = c' := by rw [hc']; module
  have q6 : d + R + (1 : ℝ) • P = b' := by rw [hb']; module
  rw [q5, q6, q3, q4, q1, q2] at key
  convert key using 1
  ext x; simp only [V8, Finset.mem_insert, Finset.mem_singleton]; tauto

theorem k20_s14 {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (hT' : ¬ IsT' a b c' d)
    (h : K6tTaA41 a a' b b' c c' d) (hz : ⟪d - b, a - b'⟫ = 0)
    (hβ6 : det3 (a' - b) (c - d) (a - d) = 0) (h0 : ⟪a - b', a - c'⟫ = 0) :
    IsRupert (V8 a a' b b' c c' d) := by
  obtain ⟨α1, β1, γ4, β6, hdet, hc', hb', ha', hα1, hβ1, hγ4, hβ6', hqr, hL⟩ :=
    k17gb_a41_frame W hT' h hz
  have h61 := k17gb_b61 hdet ha' hβ6
  subst h61
  have hpr : ⟪a - d, c - d⟫ = 0 := by
    rw [h0] at hL
    have hpos : 0 < γ4 * (α1 - 1) := mul_pos (by linarith) (by linarith)
    rcases mul_eq_zero.1 hL.symm with h | h
    · linarith
    · exact h
  set P := a - d with hP
  set Q := b - d with hQ
  set R := c - d with hR
  have key := k20_prism3 d R P Q (β := α1) (γ := β1) (z0 := 1) (z1 := γ4) (z2 := 1)
    (by rw [real_inner_comm]; exact hpr) (by rw [real_inner_comm]; exact hqr) hdet one_pos
    (by linarith) one_pos (by linarith)
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
