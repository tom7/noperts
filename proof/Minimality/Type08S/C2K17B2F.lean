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

/-- Pentagon with peak at index 1: `z2 < z1`, `z3 < z2`, `z4 < z0 < z1`. -/
theorem k17b2_pent_uni4 (z w : ZMod 5 → ℝ) (hinj : ∀ i j, z i = z j → w i = w j → i = j)
    (h21 : z 2 < z 1) (h32 : z 3 < z 2) (h40 : z 4 < z 0) (h01 : z 0 < z 1) : LexUni z w := by
  obtain ⟨M, hM⟩ := exists_key z w hinj
  refine lexUni_of_key z w (fun i => M * z i + w i) hinj hM ?_
  have lt : ∀ i j, z i < z j → M * z i + w i < M * z j + w j := fun i j h => (hM i j).1 (Or.inl h)
  have hk := k6m_key_inj z w hinj M hM
  refine k5d_uni_of_nopair (by decide) _ hk ?_
  obtain ⟨s0, s1, s2, s3, s4⟩ := z5_sub1
  obtain ⟨f0, f1, f2, f3, f4⟩ := z5_add
  have k21 := lt _ _ h21
  have k32 := lt _ _ h32
  have k40 := lt _ _ h40
  have k01 := lt _ _ h01
  intro i j h1 h2 h3 ⟨⟨pi1, pi2⟩, ⟨pj1, pj2⟩⟩
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;> rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact h1 rfl
    | exact h2 (by decide)
    | exact h3 (by decide)
    | (simp only [s0, s1, s2, s3, s4, f0, f1, f2, f3, f4] at pi1 pi2 pj1 pj2
       linarith)

/-- Rule 13 cycle `(c, b', a, c', a')`, view `b' - m(d,c)`, frame `(p/μ, q, W/μ)` at `d`, `μ = β1 - 1/2`. -/
noncomputable def k17b2Cy13 (α β β6 γ6 : ℝ) : ZMod 5 → ℝ × ℝ × ℝ :=
  ![(-α, 0, 1), (-α / 2, 0, β), (β - 1 / 2, 0, 0), (α * (β - 1 / 2), β, 0), (-α * γ6, β6, γ6)]

theorem k17b2Cy13_0 : k17b2Cy13 α β β6 γ6 0 = (-α, 0, 1) := rfl
theorem k17b2Cy13_1 : k17b2Cy13 α β β6 γ6 1 = (-α / 2, 0, β) := rfl
theorem k17b2Cy13_2 : k17b2Cy13 α β β6 γ6 2 = (β - 1 / 2, 0, 0) := rfl
theorem k17b2Cy13_3 : k17b2Cy13 α β β6 γ6 3 = (α * (β - 1 / 2), β, 0) := rfl
theorem k17b2Cy13_4 : k17b2Cy13 α β β6 γ6 4 = (-α * γ6, β6, γ6) := rfl

theorem k17b2Cy13_inj {α β β6 γ6 : ℝ} (hα : 0 < α) (hβ : 1 < β) (hβ6 : 0 < β6) (hγ6 : 0 < γ6) :
    ∀ i j : ZMod 5, k17b2Cy13 α β β6 γ6 i = k17b2Cy13 α β β6 γ6 j → i = j := by
  intro i j h
  have e1 := congrArg Prod.fst h
  have e2 := congrArg (fun t => t.2.1) h
  have e3 := congrArg (fun t => t.2.2) h
  have := mul_pos hα hγ6
  have := mul_pos hα (by linarith : (0:ℝ) < β - 1 / 2)
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;> rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    first | rfl | (exfalso; simp only [k17b2Cy13_0, k17b2Cy13_1, k17b2Cy13_2, k17b2Cy13_3, k17b2Cy13_4] at e1 e2 e3; nlinarith)

set_option maxHeartbeats 6400000 in
theorem k17b2_p13_tsc {α β β6 γ6 v1 v2 : ℝ} (hα : 1 < α) (hβ : 1 < β) (hβ6 : 1 < β6) (hγ6 : 1 < γ6) (hv2 : 0 < v2) :
    (∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      TSc 1 (k17b2Cy13 α β β6 γ6 (i + 1) - k17b2Cy13 α β β6 γ6 i) (k17b2Cy13 α β β6 γ6 j - k17b2Cy13 α β β6 γ6 i) (v1, v2, 0)) ∧
    (∀ p ∈ [((0 : ℝ), (0 : ℝ), (0 : ℝ)), ((0 : ℝ), (1 : ℝ), (0 : ℝ))], ∀ i : ZMod 5,
      TSc 1 (k17b2Cy13 α β β6 γ6 (i + 1) - k17b2Cy13 α β β6 γ6 i) (p - k17b2Cy13 α β β6 γ6 i) (v1, v2, 0)) := by
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
  have p1 := mul_pos a0 b0
  have p2 := mul_pos a0 g0
  have p3 := mul_pos b0 c0
  have p4 := mul_pos b0 g0
  have p5 := mul_pos a0 c0
  have p6 := mul_pos a1 b0
  have p7 := mul_pos a1 c0
  have p8 := mul_pos a1 g0
  have p9 := mul_pos b0 hv2
  have p10 := mul_pos a0 hv2
  have p11 := mul_pos g0 hv2
  have p12 := mul_pos c0 hv2
  have p13 := mul_pos (mul_pos a0 b0) hv2
  have p14 := mul_pos (mul_pos a0 g0) hv2
  have p15 := mul_pos (mul_pos b0 b0) hv2
  have p16 := mul_pos (mul_pos a0 b0) g0
  have p17 := mul_pos (mul_pos a0 b0) c0
  have p18 := mul_pos (mul_pos b0 b0) g0
  have p19 := mul_pos (mul_pos b0 b0) c0
  have p20 := mul_pos (mul_pos a1 b0) g0
  have p21 := mul_pos (mul_pos a1 b0) c0
  have p22 := mul_pos (mul_pos a0 b0) b0
  have p23 := mul_pos (mul_pos b0 c0) g0
  have p24 := mul_pos (mul_pos a0 c0) g0
  have p25 := mul_pos (mul_pos a0 a0) g0
  have p26 := mul_pos b1 b0
  have p27 := mul_pos (mul_pos a0 b0) b1
  have p28 := mul_pos (mul_pos b0 hv2) c0
  have p29 := mul_pos (mul_pos b0 hv2) g0
  have p30 := mul_pos (mul_pos a0 hv2) g0
  have q1 := mul_pos m0 a0
  have q2 := mul_pos m0 a1
  have q3 := mul_pos m0 c0
  have q4 := mul_pos m0 g0
  have q5 := mul_pos m0 b0
  have q6 := mul_pos (mul_pos m0 a0) g0
  have q7 := mul_pos (mul_pos m0 a1) c0
  have q8 := mul_pos (mul_pos m0 hv2) a0
  have q9 := mul_pos (mul_pos m0 hv2) b0
  have q10 := mul_pos (mul_pos m0 hv2) g0
  have q11 := mul_pos (mul_pos m0 a0) b0
  have q12 := mul_pos (mul_pos m0 a0) c0
  have q13 := mul_pos (mul_pos m0 m0) a0
  have q14 := mul_pos (mul_pos m0 hv2) c0
  have q15 := mul_pos (mul_pos m0 hv2) m0
  have q16 := mul_pos (mul_pos m0 a1) hv2
  constructor
  · intro i j h1 h2
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl h1
      | exact (h2 (by decide)).elim
      | (simp only [TSc, d3, k17b2Cy13_0, k17b2Cy13_1, k17b2Cy13_2, k17b2Cy13_3, k17b2Cy13_4, f0, f1, f2, f3, f4,
          Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
         first | (left; nlinarith) | (right; refine ⟨by ring, by nlinarith⟩))
  · intro p hp i
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;>
      rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      (simp only [TSc, d3, k17b2Cy13_0, k17b2Cy13_1, k17b2Cy13_2, k17b2Cy13_3, k17b2Cy13_4, f0, f1, f2, f3, f4,
          Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
       first | (left; nlinarith) | (right; refine ⟨by ring, by nlinarith⟩))

end C2
end Type08Sp
end Minimality
