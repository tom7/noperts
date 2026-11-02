module

public import Minimality.Type08S.C2K6TCM
public import Minimality.Type08S.C2K6TCN

@[expose] public section

set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
open scoped RealInnerProductSpace Topology
open Finset Filter
namespace Minimality
namespace Type08Sp
namespace C2

/-- **Pa cell `(a,c',a',b')` at `R`, frame form** `(P,Q,R) = (b - d, c - d, (a - d) + s (c - d))`.
Depth hypothesis `u = ⟪P,R⟫ ≤ 0`; if `u = 0` the tie `a ~ c'` is broken by a tilt with `⟪P, v⟫ < 0`, which exists when
`⟪P,Q⟫ > 0` (`hn`, `hn'`: the tilt line `v = (β6, -n - λ)` with `β6 ⟪P,P⟫ ≤ n ⟪P,Q⟫`). -/
theorem k6t3_pa_frame (V : Finset ℝ³) (P Q R d : ℝ³) (hΔ : det3 P Q R ≠ 0) {s b6 g6 a4 n : ℝ}
    (hs : 0 < s) (hb6 : 0 < b6) (hg6 : 0 < g6) (hg61 : g6 < 1) (hcv : 1 < b6 + g6) (ha4 : 0 < a4)
    (hu : ⟪P, R⟫ ≤ 0) (hn1 : 1 ≤ n) (hn' : ⟪P, R⟫ = 0 → 0 < ⟪P, Q⟫)
    (hn : ⟪P, R⟫ = 0 → b6 * ⟪P, P⟫ ≤ n * ⟪P, Q⟫)
    (hmem : ∀ i, fpoint P Q R d (k6t3_paX s b6 g6 a4 i) ∈ V)
    (hVall : ∀ y ∈ V, y = fpoint P Q R d (0, 0, 0) ∨ y = fpoint P Q R d (1, 0, 0) ∨ y = fpoint P Q R d (0, 1, 0) ∨
      y = fpoint P Q R d (0, -s, 1) ∨ y = fpoint P Q R d (0, 1, a4) ∨ y = fpoint P Q R d (1 + s, -s, 1) ∨
      y = fpoint P Q R d (b6, g6, 0)) :
    HasLexCellAt V R := by
  have hA := k5d_hA hΔ
  have hPv : ∀ v1 v2 : ℝ, ⟪P, fcomb P Q R v1 v2 0⟫ = v1 * ⟪P, P⟫ + v2 * ⟪P, Q⟫ := by
    intro v1 v2
    simp only [fcomb, inner_add_right, real_inner_smul_right, zero_smul, add_zero, mul_zero]
  have hb6' : 0 < b6 := hb6
  refine k6t3_cell V P Q R d hΔ (k := 4) (by norm_num) (k6t3_paX s b6 g6 a4) ?_ hmem
    [((0 : ℝ), (0 : ℝ), (0 : ℝ)), (1, 0, 0), (0, 1, 0)] ?_
    (u1 := b6) (u2 := -n) (t1 := 0) (t2 := -1) (lo := 0) (hi := 1)
    (by simp; exact hb6.ne') (by norm_num)
    (fun v1 v2 => 0 < v1 ∧ b6 * v2 + (1 - g6) * v1 < 0 ∧ (⟪P, R⟫ = 0 → v1 * ⟪P, P⟫ + v2 * ⟪P, Q⟫ < 0)) ?_ ?_
    [(0, -s, 1), (1 + s, -s, 1), (b6, g6, 0), (0, 1, a4), (0, 0, 0), (1, 0, 0), (0, 1, 0)] ?_ ?_
  · intro i j h
    have e1 := congrArg Prod.fst h
    have e2 := congrArg (fun t => t.2.1) h
    have e3 := congrArg (fun t => t.2.2) h
    rcases z4_cases i with rfl | rfl | rfl | rfl <;> rcases z4_cases j with rfl | rfl | rfl | rfl <;>
      first | rfl | (exfalso; simp only [k6t3_paX_0, k6t3_paX_1, k6t3_paX_2, k6t3_paX_3] at e1 e2 e3; linarith)
  · intro y hy
    rcases hVall y hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inr ⟨_, by simp, rfl⟩
    · exact Or.inr ⟨_, by simp, rfl⟩
    · exact Or.inr ⟨_, by simp, rfl⟩
    · exact Or.inl ⟨0, rfl⟩
    · exact Or.inl ⟨3, rfl⟩
    · exact Or.inl ⟨1, rfl⟩
    · exact Or.inl ⟨2, rfl⟩
  · intro lam h0 h1
    simp only [mul_zero, add_zero, zero_add, mul_one]
    refine ⟨hb6, ?_, ?_⟩
    · nlinarith
    · intro h0u
      have := hn h0u
      have := hn' h0u
      nlinarith
  · intro v1 v2 hv
    obtain ⟨hv1, hv2, -⟩ := hv
    exact k6t3_pa_tsc hs hb6 hg6 hg61 hcv ha4 hv1 hv2
  · intro i
    rcases z4_cases i with rfl | rfl | rfl | rfl <;>
      simp [k6t3_paX_0, k6t3_paX_1, k6t3_paX_2, k6t3_paX_3]
  · intro v1 v2 hCv k0 U T B hfw htie2 hinj
    obtain ⟨-, -, hC3⟩ := hCv
    have hL : ∀ i : ZMod 4, k6t3_paX s b6 g6 a4 i ∈
        [(0, -s, 1), (1 + s, -s, 1), (b6, g6, 0), (0, 1, a4), (0, 0, 0), (1, 0, 0), (0, 1, 0)] := by
      intro i
      rcases z4_cases i with rfl | rfl | rfl | rfl <;>
        simp [k6t3_paX_0, k6t3_paX_1, k6t3_paX_2, k6t3_paX_3]
    refine k6t3_pa_real (u := ⟪P, R⟫) (t := ⟪Q, R⟫) (A := ⟪R, R⟫) hs hb6 hg6 hg61 hcv ha4 hA hu ?_
      (k6t2_hdep hL hfw) hinj
    intro hu0
    have h3 := hC3 hu0
    have := htie2 (1 + s, -s, 1) (by simp) (0, -s, 1) (by simp)
      (by simp only; rw [hu0]; ring) (by
        simp only [hPv]
        nlinarith)
    simp only at this
    nlinarith

end C2
end Type08Sp
end Minimality
