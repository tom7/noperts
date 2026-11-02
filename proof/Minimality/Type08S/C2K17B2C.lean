module

public import Minimality.Type08S.C2K17BA

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

/-- Rule 4 cycle `(c, d, a, c', a')` at the view `d - b'`, frame `(p/β1, q, (d-b')/β1)` based at `d`. -/
def k17b2Cy4 (α β β6 γ6 : ℝ) : ZMod 5 → ℝ × ℝ × ℝ :=
  ![(-α, 0, -1), (0, 0, 0), (β, 0, 0), (α * β, β, 0), (-α * γ6, β6, -γ6)]

theorem k17b2Cy4_0 : k17b2Cy4 α β β6 γ6 0 = (-α, 0, -1) := rfl
theorem k17b2Cy4_1 : k17b2Cy4 α β β6 γ6 1 = (0, 0, 0) := rfl
theorem k17b2Cy4_2 : k17b2Cy4 α β β6 γ6 2 = (β, 0, 0) := rfl
theorem k17b2Cy4_3 : k17b2Cy4 α β β6 γ6 3 = (α * β, β, 0) := rfl
theorem k17b2Cy4_4 : k17b2Cy4 α β β6 γ6 4 = (-α * γ6, β6, -γ6) := rfl

/-- Rule 5 cycle `(c, b', a, c', a')`. -/
def k17b2Cy5 (α β β6 γ6 : ℝ) : ZMod 5 → ℝ × ℝ × ℝ :=
  ![(-α, 0, -1), (0, 0, -β), (β, 0, 0), (α * β, β, 0), (-α * γ6, β6, -γ6)]

theorem k17b2Cy5_0 : k17b2Cy5 α β β6 γ6 0 = (-α, 0, -1) := rfl
theorem k17b2Cy5_1 : k17b2Cy5 α β β6 γ6 1 = (0, 0, -β) := rfl
theorem k17b2Cy5_2 : k17b2Cy5 α β β6 γ6 2 = (β, 0, 0) := rfl
theorem k17b2Cy5_3 : k17b2Cy5 α β β6 γ6 3 = (α * β, β, 0) := rfl
theorem k17b2Cy5_4 : k17b2Cy5 α β β6 γ6 4 = (-α * γ6, β6, -γ6) := rfl

theorem k17b2Cy4_inj {α β β6 γ6 : ℝ} (hα : 0 < α) (hβ : 0 < β) (hβ6 : 0 < β6) (hγ6 : 0 < γ6) :
    ∀ i j : ZMod 5, k17b2Cy4 α β β6 γ6 i = k17b2Cy4 α β β6 γ6 j → i = j := by
  intro i j h
  have e1 := congrArg Prod.fst h
  have e2 := congrArg (fun t => t.2.1) h
  have e3 := congrArg (fun t => t.2.2) h
  have := mul_pos hα hγ6
  have := mul_pos hα hβ
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;> rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    first | rfl | (exfalso; simp only [k17b2Cy4_0, k17b2Cy4_1, k17b2Cy4_2, k17b2Cy4_3, k17b2Cy4_4] at e1 e2 e3; nlinarith)

theorem k17b2Cy5_inj {α β β6 γ6 : ℝ} (hα : 0 < α) (hβ : 0 < β) (hβ6 : 0 < β6) (hγ6 : 0 < γ6) :
    ∀ i j : ZMod 5, k17b2Cy5 α β β6 γ6 i = k17b2Cy5 α β β6 γ6 j → i = j := by
  intro i j h
  have e1 := congrArg Prod.fst h
  have e2 := congrArg (fun t => t.2.1) h
  have e3 := congrArg (fun t => t.2.2) h
  have := mul_pos hα hγ6
  have := mul_pos hα hβ
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;> rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    first | rfl | (exfalso; simp only [k17b2Cy5_0, k17b2Cy5_1, k17b2Cy5_2, k17b2Cy5_3, k17b2Cy5_4] at e1 e2 e3; nlinarith)

set_option maxHeartbeats 6400000 in
theorem k17b2_p4_tsc {α β β6 γ6 v1 v2 : ℝ} (hα : 1 < α) (hβ : 1 < β) (hβ6 : 1 < β6) (hγ6 : 1 < γ6) (hv2 : 0 < v2) :
    (∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      TSc 1 (k17b2Cy4 α β β6 γ6 (i + 1) - k17b2Cy4 α β β6 γ6 i) (k17b2Cy4 α β β6 γ6 j - k17b2Cy4 α β β6 γ6 i) (v1, v2, 0)) ∧
    (∀ p ∈ [((0 : ℝ), (0 : ℝ), -β), ((0 : ℝ), (1 : ℝ), (0 : ℝ))], ∀ i : ZMod 5,
      TSc 1 (k17b2Cy4 α β β6 γ6 (i + 1) - k17b2Cy4 α β β6 γ6 i) (p - k17b2Cy4 α β β6 γ6 i) (v1, v2, 0)) := by
  obtain ⟨f0, f1, f2, f3, f4⟩ := z5_add
  have a1 : 0 < α - 1 := by linarith
  have b1 : 0 < β - 1 := by linarith
  have c1 : 0 < β6 - 1 := by linarith
  have g1 : 0 < γ6 - 1 := by linarith
  have a0 : 0 < α := by linarith
  have b0 : 0 < β := by linarith
  have c0 : 0 < β6 := by linarith
  have g0 : 0 < γ6 := by linarith
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
  constructor
  · intro i j h1 h2
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl h1
      | exact (h2 (by decide)).elim
      | (simp only [TSc, d3, k17b2Cy4_0, k17b2Cy4_1, k17b2Cy4_2, k17b2Cy4_3, k17b2Cy4_4, f0, f1, f2, f3, f4,
          Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
         first | (left; nlinarith) | (right; refine ⟨by ring, by nlinarith⟩))
  · intro p hp i
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;>
      rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      (simp only [TSc, d3, k17b2Cy4_0, k17b2Cy4_1, k17b2Cy4_2, k17b2Cy4_3, k17b2Cy4_4, f0, f1, f2, f3, f4,
          Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
       first | (left; nlinarith) | (right; refine ⟨by ring, by nlinarith⟩))


/-- Pentagon with peak at index 3 and valley at index 1: arcs `1 < 2 < 3` and `1 < 0 < 4 < 3`. -/
theorem k17b2_pent_uni3 (z w : ZMod 5 → ℝ) (hinj : ∀ i j, z i = z j → w i = w j → i = j)
    (h12 : z 1 < z 2) (h23 : z 2 < z 3) (h43 : z 4 < z 3) (h04 : z 0 < z 4) (h10 : z 1 < z 0) : LexUni z w := by
  obtain ⟨M, hM⟩ := exists_key z w hinj
  refine lexUni_of_key z w (fun i => M * z i + w i) hinj hM ?_
  have lt : ∀ i j, z i < z j → M * z i + w i < M * z j + w j := fun i j h => (hM i j).1 (Or.inl h)
  have hk := k6m_key_inj z w hinj M hM
  refine k5d_uni_of_nopair (by decide) _ hk ?_
  obtain ⟨s0, s1, s2, s3, s4⟩ := z5_sub1
  obtain ⟨f0, f1, f2, f3, f4⟩ := z5_add
  have k12 := lt _ _ h12
  have k23 := lt _ _ h23
  have k43 := lt _ _ h43
  have k04 := lt _ _ h04
  have k10 := lt _ _ h10
  intro i j h1 h2 h3 ⟨⟨pi1, pi2⟩, ⟨pj1, pj2⟩⟩
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;> rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact h1 rfl
    | exact h2 (by decide)
    | exact h3 (by decide)
    | (simp only [s0, s1, s2, s3, s4, f0, f1, f2, f3, f4] at pi1 pi2 pj1 pj2
       linarith)

set_option maxHeartbeats 6400000 in
theorem k17b2_p5_tsc {α β β6 γ6 v1 v2 : ℝ} (hα : 1 < α) (hβ : 1 < β) (hβ6 : 1 < β6) (hγ6 : 1 < γ6) (hv2 : v2 < 0) :
    (∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      TSc 1 (k17b2Cy5 α β β6 γ6 (i + 1) - k17b2Cy5 α β β6 γ6 i) (k17b2Cy5 α β β6 γ6 j - k17b2Cy5 α β β6 γ6 i) (v1, v2, 0)) ∧
    (∀ p ∈ [((0 : ℝ), (0 : ℝ), (0 : ℝ)), ((0 : ℝ), (1 : ℝ), (0 : ℝ))], ∀ i : ZMod 5,
      TSc 1 (k17b2Cy5 α β β6 γ6 (i + 1) - k17b2Cy5 α β β6 γ6 i) (p - k17b2Cy5 α β β6 γ6 i) (v1, v2, 0)) := by
  obtain ⟨f0, f1, f2, f3, f4⟩ := z5_add
  have a1 : 0 < α - 1 := by linarith
  have b1 : 0 < β - 1 := by linarith
  have c1 : 0 < β6 - 1 := by linarith
  have g1 : 0 < γ6 - 1 := by linarith
  have a0 : 0 < α := by linarith
  have b0 : 0 < β := by linarith
  have c0 : 0 < β6 := by linarith
  have g0 : 0 < γ6 := by linarith
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
  have p28 := mul_pos (mul_pos b0 nv) c0
  have p29 := mul_pos (mul_pos b0 nv) g0
  have p30 := mul_pos (mul_pos a0 nv) g0
  constructor
  · intro i j h1 h2
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl h1
      | exact (h2 (by decide)).elim
      | (simp only [TSc, d3, k17b2Cy5_0, k17b2Cy5_1, k17b2Cy5_2, k17b2Cy5_3, k17b2Cy5_4, f0, f1, f2, f3, f4,
          Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
         first | (left; nlinarith) | (right; refine ⟨by ring, by nlinarith⟩))
  · intro p hp i
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;>
      rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      (simp only [TSc, d3, k17b2Cy5_0, k17b2Cy5_1, k17b2Cy5_2, k17b2Cy5_3, k17b2Cy5_4, f0, f1, f2, f3, f4,
          Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
       first | (left; nlinarith) | (right; refine ⟨by ring, by nlinarith⟩))

end C2
end Type08Sp
end Minimality
