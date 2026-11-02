module

public import Minimality.Type08S.C2K6TCI

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

/-- **Pc leaf 1, frame form**: frame `(P,Q,R) = (a-d, (b-d)/m, (c-a')/m)`, `m = 1 - γ6`;
`c = (0,1,1)`, `a' = (0,1,1-m)`, `b = (0,m,0)`, `b' = (1,g,g)`, `c' = (1,e,0)`.  Cell `(a,b',a',b,d)` at `R`
(`= (a,d,b,a',b')`), needs `e < g` and `⟪P,R⟫ > 0`. -/
theorem k6t3_pc1_frame' (V : Finset ℝ³) (P Q R d : ℝ³) (hΔ : det3 P Q R ≠ 0) {m g e : ℝ}
    (hm : 0 < m) (hm1 : m < 1) (hg : 0 < g) (he : 0 < e) (heg : e < g) (hu : 0 < ⟪P, R⟫ ∨ ⟪Q, R⟫ + ⟪R, R⟫ < 0)
    (hmem : ∀ i, fpoint P Q R d (k6t3_pcX m g i) ∈ V)
    (hVall : ∀ y ∈ V, y = fpoint P Q R d (0, 0, 0) ∨ y = fpoint P Q R d (1, 0, 0) ∨
      y = fpoint P Q R d (1, g, g) ∨ y = fpoint P Q R d (0, 1, 1) ∨ y = fpoint P Q R d (0, 1, 1 - m) ∨
      y = fpoint P Q R d (1, e, 0) ∨ y = fpoint P Q R d (0, m, 0)) :
    HasLexCellAt V R := by
  have hA := k5d_hA hΔ
  have g1 : 0 < 1 - m := by linarith
  refine k5d_cell V P Q R d hΔ (k := 5) (by norm_num) (k6t3_pcX m g) ?_ hmem
    [((0 : ℝ), (1 : ℝ), (1 : ℝ)), (1, e, 0)] ?_
    (u1 := -1) (u2 := 1 + g) (t1 := 0) (t2 := 1) (lo := 0) (hi := 1)
    (by norm_num) (by norm_num)
    (fun v1 v2 => v1 < 0 ∧ 0 < v2 + (1 - g) * v1) ?_ ?_
    [(1, 0, 0), (1, g, g), (0, 1, 1 - m), (0, m, 0), (0, 0, 0), (0, 1, 1), (1, e, 0)] ?_ ?_
  · intro i j h
    have e1 := congrArg Prod.fst h
    have e2 := congrArg (fun t => t.2.1) h
    have e3 := congrArg (fun t => t.2.2) h
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;> rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
      first | rfl | (exfalso; simp only [k6t3_pcX_0, k6t3_pcX_1, k6t3_pcX_2, k6t3_pcX_3, k6t3_pcX_4] at e1 e2 e3; linarith)
  · intro y hy
    rcases hVall y hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨4, rfl⟩
    · exact Or.inl ⟨0, rfl⟩
    · exact Or.inl ⟨1, rfl⟩
    · exact Or.inr ⟨_, by simp, rfl⟩
    · exact Or.inl ⟨2, rfl⟩
    · exact Or.inr ⟨_, by simp, rfl⟩
    · exact Or.inl ⟨3, rfl⟩
  · intro lam h0 h1
    simp only [mul_zero, add_zero, zero_add, mul_one]
    refine ⟨by norm_num, ?_⟩
    nlinarith
  · intro v1 v2 hv
    obtain ⟨hv1, hv2⟩ := hv
    exact k6t3_pc1_tsc hm hm1 hg he heg hv1 hv2
  · intro i
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      simp [k6t3_pcX_0, k6t3_pcX_1, k6t3_pcX_2, k6t3_pcX_3, k6t3_pcX_4]
  · intro v1 v2 _ k0 U T B hfw hinj
    refine k6t3_pc1_real' (u := ⟪P, R⟫) (t := ⟪Q, R⟫) (A := ⟪R, R⟫) hm hm1 hg hA hu ?_ hinj
    refine k6t2_hdep (L := [(1, 0, 0), (1, g, g), (0, 1, 1 - m), (0, m, 0), (0, 0, 0), (0, 1, 1), (1, e, 0)]) ?_ hfw
    intro i
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      simp [k6t3_pcX_0, k6t3_pcX_1, k6t3_pcX_2, k6t3_pcX_3, k6t3_pcX_4]


/-- **Pc leaf 2, frame form**: cell `(a,c',b',c,d)` at `R`, needs `e < g`, `⟪P,R⟫ < 0`, `0 ≤ ⟪c - d, R⟫ = ⟪Q,R⟫ + ⟪R,R⟫`. -/
theorem k6t3_pc2_frame (V : Finset ℝ³) (P Q R d : ℝ³) (hΔ : det3 P Q R ≠ 0) {m g e : ℝ}
    (hm : 0 < m) (hm1 : m < 1) (hg : 0 < g) (he : 0 < e) (heg : e < g) (hu : ⟪P, R⟫ < 0)
    (hw : 0 ≤ ⟪Q, R⟫ + ⟪R, R⟫)
    (hmem : ∀ i, fpoint P Q R d (k6t3_pcY g e i) ∈ V)
    (hVall : ∀ y ∈ V, y = fpoint P Q R d (0, 0, 0) ∨ y = fpoint P Q R d (1, 0, 0) ∨
      y = fpoint P Q R d (1, g, g) ∨ y = fpoint P Q R d (0, 1, 1) ∨ y = fpoint P Q R d (0, 1, 1 - m) ∨
      y = fpoint P Q R d (1, e, 0) ∨ y = fpoint P Q R d (0, m, 0)) :
    HasLexCellAt V R := by
  have hA := k5d_hA hΔ
  have g1 : 0 < 1 - m := by linarith
  refine k5d_cell V P Q R d hΔ (k := 5) (by norm_num) (k6t3_pcY g e) ?_ hmem
    [((0 : ℝ), (1 : ℝ), 1 - m), (0, m, 0)] ?_
    (u1 := 1) (u2 := -(1 + g)) (t1 := 0) (t2 := -1) (lo := 0) (hi := 1)
    (by norm_num) (by norm_num)
    (fun v1 v2 => 0 < v1 ∧ v2 + (1 - g) * v1 < 0) ?_ ?_
    [(1, 0, 0), (1, e, 0), (1, g, g), (0, 1, 1), (0, 0, 0), (0, 1, 1 - m), (0, m, 0)] ?_ ?_
  · intro i j h
    have e1 := congrArg Prod.fst h
    have e2 := congrArg (fun t => t.2.1) h
    have e3 := congrArg (fun t => t.2.2) h
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;> rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
      first | rfl | (exfalso; simp only [k6t3_pcY_0, k6t3_pcY_1, k6t3_pcY_2, k6t3_pcY_3, k6t3_pcY_4] at e1 e2 e3; linarith)
  · intro y hy
    rcases hVall y hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨4, rfl⟩
    · exact Or.inl ⟨0, rfl⟩
    · exact Or.inl ⟨2, rfl⟩
    · exact Or.inl ⟨3, rfl⟩
    · exact Or.inr ⟨_, by simp, rfl⟩
    · exact Or.inl ⟨1, rfl⟩
    · exact Or.inr ⟨_, by simp, rfl⟩
  · intro lam h0 h1
    simp only [mul_zero, add_zero, zero_add, mul_one]
    refine ⟨by norm_num, ?_⟩
    nlinarith
  · intro v1 v2 hv
    obtain ⟨hv1, hv2⟩ := hv
    exact k6t3_pc2_tsc hm hm1 hg he heg hv1 hv2
  · intro i
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      simp [k6t3_pcY_0, k6t3_pcY_1, k6t3_pcY_2, k6t3_pcY_3, k6t3_pcY_4]
  · intro v1 v2 _ k0 U T B hfw hinj
    refine k6t3_pc2_real (u := ⟪P, R⟫) (t := ⟪Q, R⟫) (A := ⟪R, R⟫) hg he heg hA hu hw ?_ hinj
    refine k6t2_hdep (L := [(1, 0, 0), (1, e, 0), (1, g, g), (0, 1, 1), (0, 0, 0), (0, 1, 1 - m), (0, m, 0)]) ?_ hfw
    intro i
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      simp [k6t3_pcY_0, k6t3_pcY_1, k6t3_pcY_2, k6t3_pcY_3, k6t3_pcY_4]

end C2
end Type08Sp
end Minimality
