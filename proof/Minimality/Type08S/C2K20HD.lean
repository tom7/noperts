module

public import Minimality.Type08S.C2K20HC

@[expose] public section


/-!
# K20H5 / D: H5 rule r7 (line view `L14`, view `w = α1 (1-β6)(a-d) + (β1-1) γ6 (c-d)`), pentagon `(c, d, a, c', a')`: cycle, injectivity, TSc.
Frame `(a - d, b - d, w)`, `μ = 1/((β1-1) γ6)`, `ν = γ6 μ = 1/(β1-1)`, `A = α1 (1-β6)`:
`c = (-Aμ, 0, μ)`, `a' = (-Aν, β6, ν)`, `c' = (α1, β1, 0)`, `b = (0,1,0)`, `b' = (α1 - β1 A μ, 0, β1 μ)`.
-/
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

def k20R7Cyc (α β β6 μ ν : ℝ) : ZMod 5 → ℝ × ℝ × ℝ :=
  ![(-(α * (1 - β6) * μ), 0, μ), (0, 0, 0), (1, 0, 0), (α, β, 0), (-(α * (1 - β6) * ν), β6, ν)]

theorem k20R7Cyc_0 : k20R7Cyc α β β6 μ ν 0 = (-(α * (1 - β6) * μ), 0, μ) := rfl
theorem k20R7Cyc_1 : k20R7Cyc α β β6 μ ν 1 = (0, 0, 0) := rfl
theorem k20R7Cyc_2 : k20R7Cyc α β β6 μ ν 2 = (1, 0, 0) := rfl
theorem k20R7Cyc_3 : k20R7Cyc α β β6 μ ν 3 = (α, β, 0) := rfl
theorem k20R7Cyc_4 : k20R7Cyc α β β6 μ ν 4 = (-(α * (1 - β6) * ν), β6, ν) := rfl

theorem k20R7_inj {α β β6 μ ν : ℝ} (hα : 0 < α) (hβ : 0 < β) (hb6 : 0 < β6) (hμ : 0 < μ) (hν : 0 < ν) :
    ∀ i j : ZMod 5, k20R7Cyc α β β6 μ ν i = k20R7Cyc α β β6 μ ν j → i = j := by
  intro i j h
  have e1 := congrArg Prod.fst h
  have e2 := congrArg (fun t => t.2.1) h
  have e3 := congrArg (fun t => t.2.2) h
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;> rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    first | rfl | (exfalso; simp only [k20R7Cyc_0, k20R7Cyc_1, k20R7Cyc_2, k20R7Cyc_3, k20R7Cyc_4] at e1 e2 e3; nlinarith)

set_option maxHeartbeats 12800000 in
theorem k20R7_tsc {α β β6 γ6 μ ν v1 v2 : ℝ} (hα : 1 < α) (hβ : 1 < β) (hb6 : 0 < β6) (hb61 : β6 < 1)
    (hγ6 : 0 < γ6) (hγ61 : γ6 < 1) (hσ : β < β6 + γ6)
    (hμ : 0 < μ) (hν : 0 < ν) (hνμ : ν = γ6 * μ) (hνβ : ν * (β - 1) = 1)
    (hb : α - β * (α * (1 - β6)) * μ < 1)
    (hc1 : v2 < 0) (hc2 : 0 < v1 - α * ν * v2) :
    (∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      TSc 1 (k20R7Cyc α β β6 μ ν (i + 1) - k20R7Cyc α β β6 μ ν i)
        (k20R7Cyc α β β6 μ ν j - k20R7Cyc α β β6 μ ν i) (v1, v2, 0)) ∧
    (∀ t ∈ [((0 : ℝ), (1 : ℝ), (0 : ℝ)), (α - β * (α * (1 - β6)) * μ, 0, β * μ)], ∀ i : ZMod 5,
      TSc 1 (k20R7Cyc α β β6 μ ν (i + 1) - k20R7Cyc α β β6 μ ν i)
        (t - k20R7Cyc α β β6 μ ν i) (v1, v2, 0)) := by
  obtain ⟨f0, f1, f2, f3, f4⟩ := z5_add
  have hg1 : 0 < β6 - β * (1 - γ6) := by nlinarith
  have hα0 : 0 < α := by linarith
  have hβ0 : 0 < β := by linarith
  have a1 : 0 < α - 1 := by linarith
  have b1 : 0 < β - 1 := by linarith
  have c6 : 0 < 1 - β6 := by linarith
  have hA : 0 < α * (1 - β6) := mul_pos hα0 c6
  have hnv : 0 < -v2 := by linarith
  subst hνμ
  have hk : (γ6 * μ) * (β - 1) * v1 = v1 := by rw [hνβ]; ring
  have hk2 : (γ6 * μ) * (β - 1) * (α * (γ6 * μ) * v2) = α * (γ6 * μ) * v2 := by rw [hνβ]; ring
  have hσ1 : 0 < β6 + γ6 - 1 := by linarith
  have hq : α * β6 * (γ6 * μ * (β - 1)) = α * β6 := by rw [hνβ]; ring
  have p33 := mul_pos (mul_pos (mul_pos hα0 hb6) (mul_pos hμ b1)) hσ1
  have p1 := mul_pos hA hμ
  have p2 := mul_pos hA hν
  have p3 := mul_pos hα0 hμ
  have p4 := mul_pos hα0 hν
  have p5 := mul_pos hβ0 hμ
  have p6 := mul_pos hβ0 hν
  have p7 := mul_pos hb6 hμ
  have p8 := mul_pos hb6 hν
  have p9 := mul_pos hA hnv
  have p10 := mul_pos hα0 hnv
  have p11 := mul_pos hβ0 hnv
  have p12 := mul_pos hμ hnv
  have p13 := mul_pos hν hnv
  have p14 := mul_pos hb6 hnv
  have p15 := mul_pos (mul_pos hα0 hν) hnv
  have p16 := mul_pos (mul_pos hα0 hμ) hnv
  have p17 := mul_pos (mul_pos hA hμ) hnv
  have p18 := mul_pos (mul_pos hA hν) hnv
  have p19 := mul_pos hg1 hnv
  have p20 := mul_pos hg1 hA
  have p26 := mul_pos (mul_pos c6 hμ) hg1
  have p27 := mul_pos (mul_pos hA hμ) hg1
  have p28 := mul_pos (mul_pos hα0 hμ) hg1
  have p29 := mul_pos hγ6 hμ
  have p30 := mul_pos (mul_pos hγ6 hμ) hnv
  have p31 := mul_pos (sub_pos.2 hγ61) hμ
  have p32 := mul_pos (mul_pos (sub_pos.2 hγ61) hμ) hA
  have p21 := mul_pos (sub_pos.2 hb) hμ
  have p22 := mul_pos (sub_pos.2 hb) hnv
  have p23 := mul_pos (sub_pos.2 hb) hA
  have p24 := mul_pos (sub_pos.2 hb) hν
  have p25 := mul_pos (sub_pos.2 hb) hβ0
  constructor
  · intro i j h1 h2
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl h1
      | exact (h2 (by decide)).elim
      | (simp only [TSc, d3, k20R7Cyc_0, k20R7Cyc_1, k20R7Cyc_2, k20R7Cyc_3, k20R7Cyc_4, f0, f1, f2, f3, f4,
          Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
         first | (left; nlinarith) | (right; refine ⟨by first | ring1 | linear_combination (α * (1 - β6)) * hνβ | linear_combination (-(α * (1 - β6))) * hνβ, by nlinarith⟩))
  · intro t ht i
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl <;>
      rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      (simp only [TSc, d3, k20R7Cyc_0, k20R7Cyc_1, k20R7Cyc_2, k20R7Cyc_3, k20R7Cyc_4, f0, f1, f2, f3, f4,
          Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
       first | (left; nlinarith) | (right; refine ⟨by first | ring1 | linear_combination (α * (1 - β6)) * hνβ | linear_combination (-(α * (1 - β6))) * hνβ, by nlinarith⟩))

end C2
end Type08Sp
end Minimality
