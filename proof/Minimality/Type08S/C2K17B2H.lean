module

public import Minimality.Type08S.C2K17B2B

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
namespace C2

/-- Rule 12/3 cycle `(c, d, a, c', a')` at `b' - m(d,c)`, same frame as rule 13. -/
noncomputable def k17b2Cy12 (α β β6 γ6 : ℝ) : ZMod 5 → ℝ × ℝ × ℝ :=
  ![(-α, 0, 1), (0, 0, 0), (β - 1 / 2, 0, 0), (α * (β - 1 / 2), β, 0), (-α * γ6, β6, γ6)]

theorem k17b2Cy12_0 : k17b2Cy12 α β β6 γ6 0 = (-α, 0, 1) := rfl
theorem k17b2Cy12_1 : k17b2Cy12 α β β6 γ6 1 = (0, 0, 0) := rfl
theorem k17b2Cy12_2 : k17b2Cy12 α β β6 γ6 2 = (β - 1 / 2, 0, 0) := rfl
theorem k17b2Cy12_3 : k17b2Cy12 α β β6 γ6 3 = (α * (β - 1 / 2), β, 0) := rfl
theorem k17b2Cy12_4 : k17b2Cy12 α β β6 γ6 4 = (-α * γ6, β6, γ6) := rfl

theorem k17b2Cy12_inj {α β β6 γ6 : ℝ} (hα : 0 < α) (hβ : 1 < β) (hβ6 : 0 < β6) (hγ6 : 0 < γ6) :
    ∀ i j : ZMod 5, k17b2Cy12 α β β6 γ6 i = k17b2Cy12 α β β6 γ6 j → i = j := by
  intro i j h
  have e1 := congrArg Prod.fst h
  have e2 := congrArg (fun t => t.2.1) h
  have e3 := congrArg (fun t => t.2.2) h
  have := mul_pos hα hγ6
  have := mul_pos hα (by linarith : (0:ℝ) < β - 1 / 2)
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;> rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    first | rfl | (exfalso; simp only [k17b2Cy12_0, k17b2Cy12_1, k17b2Cy12_2, k17b2Cy12_3, k17b2Cy12_4] at e1 e2 e3; nlinarith)

set_option maxHeartbeats 6400000 in
theorem k17b2_p12_tsc {α β β6 γ6 v1 v2 : ℝ} (hα : 1 < α) (hβ : 1 < β) (hβ6 : 1 < β6) (hγ6 : 1 < γ6) (hv2 : v2 < 0) :
    (∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      TSc 1 (k17b2Cy12 α β β6 γ6 (i + 1) - k17b2Cy12 α β β6 γ6 i) (k17b2Cy12 α β β6 γ6 j - k17b2Cy12 α β β6 γ6 i) (v1, v2, 0)) ∧
    (∀ p ∈ [(-α / 2, (0 : ℝ), β), ((0 : ℝ), (1 : ℝ), (0 : ℝ))], ∀ i : ZMod 5,
      TSc 1 (k17b2Cy12 α β β6 γ6 (i + 1) - k17b2Cy12 α β β6 γ6 i) (p - k17b2Cy12 α β β6 γ6 i) (v1, v2, 0)) := by
  obtain ⟨f0, f1, f2, f3, f4⟩ := z5_add
  have a1 : 0 < α - 1 := by linarith
  have b1 : 0 < β - 1 := by linarith
  have c1 : 0 < β6 - 1 := by linarith
  have g1 : 0 < γ6 - 1 := by linarith
  have a0 : 0 < α := by linarith
  have b0 : 0 < β := by linarith
  have c0 : 0 < β6 := by linarith
  have g0 : 0 < γ6 := by linarith
  have m0 : 0 < β - 1 / 2 := by linarith
  have nv : 0 < -v2 := by linarith
  have p1 := mul_pos a0 b0
  have p2 := mul_pos a0 g0
  have p3 := mul_pos b0 c0
  have p4 := mul_pos b0 g0
  have p5 := mul_pos a0 c0
  have p6 := mul_pos a1 b0
  have p7 := mul_pos a1 c0
  have p8 := mul_pos a1 g0
  have p9 := mul_pos b0 nv
  have p10 := mul_pos a0 nv
  have p11 := mul_pos g0 nv
  have p12 := mul_pos c0 nv
  have p13 := mul_pos (mul_pos a0 b0) nv
  have p14 := mul_pos (mul_pos a0 g0) nv
  have p15 := mul_pos (mul_pos b0 b0) nv
  have p16 := mul_pos (mul_pos a0 b0) g0
  have p17 := mul_pos (mul_pos a0 b0) c0
  have p20 := mul_pos (mul_pos a1 b0) g0
  have p21 := mul_pos (mul_pos a1 b0) c0
  have p23 := mul_pos (mul_pos b0 c0) g0
  have p24 := mul_pos (mul_pos a0 c0) g0
  have q1 := mul_pos m0 a0
  have q2 := mul_pos m0 a1
  have q3 := mul_pos m0 c0
  have q4 := mul_pos m0 g0
  have q5 := mul_pos m0 b0
  have q6 := mul_pos (mul_pos m0 a0) g0
  have q7 := mul_pos (mul_pos m0 a1) c0
  have q8 := mul_pos (mul_pos m0 nv) a0
  have q9 := mul_pos (mul_pos m0 nv) b0
  have q10 := mul_pos (mul_pos m0 nv) g0
  have q11 := mul_pos (mul_pos m0 a0) b0
  have q12 := mul_pos (mul_pos m0 a0) c0
  have q14 := mul_pos (mul_pos m0 nv) c0
  have q15 := mul_pos (mul_pos m0 nv) m0
  have q16 := mul_pos (mul_pos m0 a1) nv
  constructor
  · intro i j h1 h2
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl h1
      | exact (h2 (by decide)).elim
      | (simp only [TSc, d3, k17b2Cy12_0, k17b2Cy12_1, k17b2Cy12_2, k17b2Cy12_3, k17b2Cy12_4, f0, f1, f2, f3, f4,
          Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
         first | (left; nlinarith) | (right; refine ⟨by ring, by nlinarith⟩))
  · intro p hp i
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;>
      rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      (simp only [TSc, d3, k17b2Cy12_0, k17b2Cy12_1, k17b2Cy12_2, k17b2Cy12_3, k17b2Cy12_4, f0, f1, f2, f3, f4,
          Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
       first | (left; nlinarith) | (right; refine ⟨by ring, by nlinarith⟩))


set_option maxHeartbeats 3200000 in
theorem k17b2_p12_frame (V : Finset ℝ³) (P Q R d0 : ℝ³) (hΔ : det3 P Q R ≠ 0) {α β β6 γ6 : ℝ}
    (hα : 1 < α) (hβ : 1 < β) (hβ6 : 1 < β6) (hγ6 : 1 < γ6)
    (hmem : ∀ i, fpoint P Q R d0 (k17b2Cy12 α β β6 γ6 i) ∈ V)
    (hVall : ∀ y ∈ V, y = fpoint P Q R d0 (-α, 0, 1) ∨ y = fpoint P Q R d0 (0, 0, 0) ∨
      y = fpoint P Q R d0 (β - 1 / 2, 0, 0) ∨ y = fpoint P Q R d0 (α * (β - 1 / 2), β, 0) ∨
      y = fpoint P Q R d0 (-α * γ6, β6, γ6) ∨ y = fpoint P Q R d0 (-α / 2, 0, β) ∨ y = fpoint P Q R d0 (0, 1, 0))
    (h01 : ⟪fpoint P Q R d0 (0, 0, 0), R⟫ < ⟪fpoint P Q R d0 (β - 1 / 2, 0, 0), R⟫)
    (h12 : ⟪fpoint P Q R d0 (β - 1 / 2, 0, 0), R⟫ < ⟪fpoint P Q R d0 (α * (β - 1 / 2), β, 0), R⟫)
    (h23 : ⟪fpoint P Q R d0 (α * (β - 1 / 2), β, 0), R⟫ < ⟪fpoint P Q R d0 (-α * γ6, β6, γ6), R⟫)
    (h43 : ⟪fpoint P Q R d0 (-α, 0, 1), R⟫ < ⟪fpoint P Q R d0 (-α * γ6, β6, γ6), R⟫) :
    HasLexCellAt V R := by
  refine cyc_cell V P Q R d0 hΔ (k := 5) (by norm_num) (k17b2Cy12 α β β6 γ6)
    (k17b2Cy12_inj (by linarith) (by linarith) (by linarith) (by linarith)) hmem
    [(-α / 2, (0 : ℝ), β), ((0 : ℝ), (1 : ℝ), (0 : ℝ))] ?_
    (u1 := 0) (u2 := -1) (t1 := 1) (t2 := 0) (lo := 0) (hi := 1) (by norm_num) (by norm_num)
    (fun v1 v2 => v2 < 0) ?_ ?_ ?_
  · intro y hy
    rcases hVall y hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, rfl⟩
    · exact Or.inl ⟨1, rfl⟩
    · exact Or.inl ⟨2, rfl⟩
    · exact Or.inl ⟨3, rfl⟩
    · exact Or.inl ⟨4, rfl⟩
    · exact Or.inr ⟨_, by simp, rfl⟩
    · exact Or.inr ⟨_, by simp, rfl⟩
  · intro lam h0 h1
    simp only [mul_zero, add_zero, zero_add, mul_one]
    norm_num
  · intro v1 v2 hv2
    exact k17b2_p12_tsc hα hβ hβ6 hγ6 hv2
  · intro v1 v2 _ hL
    obtain ⟨f0, f1, f2, f3, f4⟩ := z5_add
    refine lexUni_unshift1 ?_
    refine k17b_pent_uni _ _ ?_ ?_ ?_ ?_ ?_
    · intro i j e1 e2; exact add_right_cancel (hL _ _ e1 e2)
    · simpa only [f0, f1, k17b2Cy12_1, k17b2Cy12_2] using h01
    · simpa only [f1, f2, k17b2Cy12_2, k17b2Cy12_3] using h12
    · simpa only [f2, f3, k17b2Cy12_3, k17b2Cy12_4] using h23
    · simpa only [f4, f3, k17b2Cy12_0, k17b2Cy12_4] using h43

set_option maxHeartbeats 12800000 in
/-- **K6M2 rule 12 cell** (view `W = b' - m(d,c)`, cell `(c, d, a, c', a')`): `d < a < c' < a'`, `c < a'` at `W`. -/
theorem k17b2_r12 {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ}
    (hdet : det3 (a - d) (b - d) (c - d) ≠ 0)
    (hc' : c' = d + α1 • (a - d) + β1 • (b - d)) (hb' : b' = d + α1 • (a - d) + β1 • (c - d))
    (ha' : a' = d + β6 • (b - d) + γ6 • (c - d))
    (hα1 : 1 < α1) (hβ1 : 1 < β1) (hβ6 : 1 < β6) (hγ6 : 1 < γ6)
    (h1 : 0 < ⟪a - d, b' - (1 / 2 : ℝ) • (d + c)⟫) (h2 : 0 < ⟪c' - a, b' - (1 / 2 : ℝ) • (d + c)⟫)
    (h3 : 0 < ⟪a' - c', b' - (1 / 2 : ℝ) • (d + c)⟫) (h4 : 0 < ⟪a' - c, b' - (1 / 2 : ℝ) • (d + c)⟫) :
    HasLexCell (V8 a a' b b' c c' d) := by
  obtain ⟨p, rfl⟩ : ∃ p, a = d + p := ⟨a - d, by abel⟩
  obtain ⟨q, rfl⟩ : ∃ q, b = d + q := ⟨b - d, by abel⟩
  obtain ⟨r, rfl⟩ : ∃ r, c = d + r := ⟨c - d, by abel⟩
  simp only [add_sub_cancel_left] at hdet hc' hb' ha'
  subst hc' hb' ha'
  have hα0 : 0 < α1 := by linarith
  have hμ : 0 < β1 - 1 / 2 := by linarith
  have hμ0 : 2 * β1 - 1 ≠ 0 := by intro h; linarith
  have hμ1 : -1 + β1 * 2 ≠ 0 := by intro h; linarith
  have hinv : (-1 + β1 * 2)⁻¹ * (-1 + β1 * 2) = 1 := inv_mul_cancel₀ hμ1
  set Wv : ℝ³ := (d + α1 • p + β1 • r) - (1 / 2 : ℝ) • (d + (d + r)) with hWv
  set Rv : ℝ³ := (2 / (2 * β1 - 1)) • Wv with hRv
  set P : ℝ³ := (2 / (2 * β1 - 1)) • p with hP
  have hΔ : det3 P q Rv ≠ 0 := by
    have e : det3 P q Rv = (2 / (2 * β1 - 1)) * det3 p q r := by
      simp only [hP, hRv, hWv, det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
      field_simp; ring
    rw [e]; exact mul_ne_zero (div_pos (by norm_num) (by linarith)).ne' hdet
  have eC : fpoint P q Rv d (-α1, 0, 1) = d + r := by
    simp only [fpoint, fcomb, hP, hRv, hWv]
    match_scalars <;> field_simp <;> ring
  have eD : fpoint P q Rv d (0, 0, 0) = d := by simp [fpoint, fcomb]
  have eA : fpoint P q Rv d (β1 - 1 / 2, 0, 0) = d + p := by
    simp only [fpoint, fcomb, hP]; match_scalars <;> field_simp <;> first | ring1 | linear_combination hinv
  have eC' : fpoint P q Rv d (α1 * (β1 - 1 / 2), β1, 0) = d + α1 • p + β1 • q := by
    simp only [fpoint, fcomb, hP]; match_scalars <;> field_simp <;> first | ring1 | linear_combination hinv
  have eA' : fpoint P q Rv d (-α1 * γ6, β6, γ6) = d + β6 • q + γ6 • r := by
    simp only [fpoint, fcomb, hP, hRv, hWv]
    match_scalars <;> field_simp <;> ring
  have eB' : fpoint P q Rv d (-α1 / 2, 0, β1) = d + α1 • p + β1 • r := by
    simp only [fpoint, fcomb, hP, hRv, hWv]
    match_scalars <;> field_simp <;> first | ring1 | linear_combination hinv
  have eB : fpoint P q Rv d (0, 1, 0) = d + q := by simp only [fpoint, fcomb]; module
  have hi : ∀ x : ℝ³, ⟪x, Rv⟫ = (2 / (2 * β1 - 1)) * ⟪x, Wv⟫ := by
    intro x; rw [hRv, inner_smul_right]
  have hpos : 0 < 2 / (2 * β1 - 1) := div_pos (by norm_num) (by linarith)
  have inner_lt : ∀ X Y : ℝ³, 0 < ⟪Y - X, Wv⟫ → ⟪X, Rv⟫ < ⟪Y, Rv⟫ := by
    intro X Y h; rw [inner_sub_left] at h; rw [hi, hi]; nlinarith
  have h01 : ⟪d, Rv⟫ < ⟪d + p, Rv⟫ := inner_lt _ _ h1
  have h12 : ⟪d + p, Rv⟫ < ⟪d + α1 • p + β1 • q, Rv⟫ := inner_lt _ _ h2
  have h23 : ⟪d + α1 • p + β1 • q, Rv⟫ < ⟪d + β6 • q + γ6 • r, Rv⟫ := inner_lt _ _ h3
  have h43 : ⟪d + r, Rv⟫ < ⟪d + β6 • q + γ6 • r, Rv⟫ := inner_lt _ _ h4
  refine ⟨Rv, ?_, ?_⟩
  · intro h0; apply hΔ; rw [h0]; simp [det3_expand]
  refine k17b2_p12_frame (V8 (d + p) (d + β6 • q + γ6 • r) (d + q) (d + α1 • p + β1 • r) (d + r) (d + α1 • p + β1 • q) d)
    P q Rv d hΔ hα1 hβ1 hβ6 hγ6 ?_ ?_ ?_ ?_ ?_ ?_
  · intro i
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
    · simp only [k17b2Cy12_0, eC]; simp [V8]
    · simp only [k17b2Cy12_1, eD]; simp [V8]
    · simp only [k17b2Cy12_2, eA]; simp [V8]
    · simp only [k17b2Cy12_3, eC']; simp [V8]
    · simp only [k17b2Cy12_4, eA']; simp [V8]
  · intro y hy
    rw [eC, eD, eA, eC', eA', eB', eB]
    simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
    tauto
  · rw [eD, eA]; exact h01
  · rw [eA, eC']; exact h12
  · rw [eC', eA']; exact h23
  · rw [eC, eA']; exact h43


/-- **K6M2 rule 3** (view `U = c' - m(d,b)`, cell `(a, d, b, a', b')`): mirror of the rule 12 cell, `d < a < b' < a'`, `b < a'` at `U`. -/
theorem k17b2_r3 {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ}
    (hdet : det3 (a - d) (b - d) (c - d) ≠ 0)
    (hc' : c' = d + α1 • (a - d) + β1 • (b - d)) (hb' : b' = d + α1 • (a - d) + β1 • (c - d))
    (ha' : a' = d + β6 • (b - d) + γ6 • (c - d))
    (hα1 : 1 < α1) (hβ1 : 1 < β1) (hβ6 : 1 < β6) (hγ6 : 1 < γ6)
    (h1 : 0 < ⟪a - d, c' - (1 / 2 : ℝ) • (d + b)⟫) (h2 : 0 < ⟪b' - a, c' - (1 / 2 : ℝ) • (d + b)⟫)
    (h3 : 0 < ⟪a' - b', c' - (1 / 2 : ℝ) • (d + b)⟫) (h4 : 0 < ⟪a' - b, c' - (1 / 2 : ℝ) • (d + b)⟫) :
    HasLexCell (V8 a a' b b' c c' d) := by
  rw [← k17b_V8_swap]
  refine k17b2_r12 (a := a) (a' := a') (b := c) (b' := c') (c := b) (c' := b') (d := d) (α1 := α1) (β1 := β1)
    (β6 := γ6) (γ6 := β6) ?_ hb' hc' (by rw [ha']; abel) hα1 hβ1 hγ6 hβ6 h1 h2 h3 h4
  intro h; apply hdet
  have : det3 (a - d) (c - d) (b - d) = -det3 (a - d) (b - d) (c - d) := by
    simp only [det3_expand]; ring
  rw [this] at h; linarith

end C2
end Type08Sp
end Minimality
