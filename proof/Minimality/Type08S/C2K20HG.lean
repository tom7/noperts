module

public import Minimality.Type08S.C2K20HE

@[expose] public section


/-!
# K20H5 / G: H5 rule r8 (view `b' - a`), pentagon `(c, d, a, c', a')`: cycle, injectivity, TSc.
Frame `(a - d, b - d, u)`, `u = b' - a = (α1-1)(a-d) + β1 (c-d)`, `μ = 1/β1`, `ν = γ6 μ`:
`c = (-(α1-1) μ, 0, μ)`, `a' = (-(α1-1) ν, β6, ν)`, `c' = (α1, β1, 0)`, `b = (0,1,0)`, `b' = (1, 0, 1)` (over `a`).
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

def k20R8Cyc (α β β6 μ ν : ℝ) : ZMod 5 → ℝ × ℝ × ℝ :=
  ![(-((α - 1) * μ), 0, μ), (0, 0, 0), (1, 0, 0), (α, β, 0), (-((α - 1) * ν), β6, ν)]

theorem k20R8Cyc_0 : k20R8Cyc α β β6 μ ν 0 = (-((α - 1) * μ), 0, μ) := rfl
theorem k20R8Cyc_1 : k20R8Cyc α β β6 μ ν 1 = (0, 0, 0) := rfl
theorem k20R8Cyc_2 : k20R8Cyc α β β6 μ ν 2 = (1, 0, 0) := rfl
theorem k20R8Cyc_3 : k20R8Cyc α β β6 μ ν 3 = (α, β, 0) := rfl
theorem k20R8Cyc_4 : k20R8Cyc α β β6 μ ν 4 = (-((α - 1) * ν), β6, ν) := rfl

theorem k20R8_inj {α β β6 μ ν : ℝ} (hα : 1 < α) (hβ : 0 < β) (hb6 : 0 < β6) (hμ : 0 < μ) (hν : 0 < ν) :
    ∀ i j : ZMod 5, k20R8Cyc α β β6 μ ν i = k20R8Cyc α β β6 μ ν j → i = j := by
  intro i j h
  have e1 := congrArg Prod.fst h
  have e2 := congrArg (fun t => t.2.1) h
  have e3 := congrArg (fun t => t.2.2) h
  have a1 : 0 < α - 1 := by linarith
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;> rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    first | rfl | (exfalso; simp only [k20R8Cyc_0, k20R8Cyc_1, k20R8Cyc_2, k20R8Cyc_3, k20R8Cyc_4] at e1 e2 e3; nlinarith)

set_option maxHeartbeats 12800000 in
theorem k20R8_tsc {α β β6 γ6 μ ν v1 v2 : ℝ} (hα : 1 < α) (hβ : 1 < β) (hb6 : 0 < β6) (hb61 : β6 < 1)
    (hγ6 : 0 < γ6) (hγ61 : γ6 < 1) (hσ : β < β6 + γ6)
    (hμ : 0 < μ) (hμβ : μ * β = 1) (hν : ν = γ6 * μ)
    (hlit : α * β * (1 - β6) < γ6 * (α - 1) * (β - 1))
    (hc1 : v2 < 0) (hc2 : 0 < β * v1 - (α - 1) * v2) :
    (∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      TSc 1 (k20R8Cyc α β β6 μ ν (i + 1) - k20R8Cyc α β β6 μ ν i)
        (k20R8Cyc α β β6 μ ν j - k20R8Cyc α β β6 μ ν i) (v1, v2, 0)) ∧
    (∀ t ∈ [((0 : ℝ), (1 : ℝ), (0 : ℝ)), ((1 : ℝ), (0 : ℝ), (1 : ℝ))], ∀ i : ZMod 5,
      TSc 1 (k20R8Cyc α β β6 μ ν (i + 1) - k20R8Cyc α β β6 μ ν i)
        (t - k20R8Cyc α β β6 μ ν i) (v1, v2, 0)) := by
  obtain ⟨f0, f1, f2, f3, f4⟩ := z5_add
  subst hν
  have hg1 : 0 < β6 - β * (1 - γ6) := by nlinarith
  have hα0 : 0 < α := by linarith
  have hβ0 : 0 < β := by linarith
  have a1 : 0 < α - 1 := by linarith
  have b1 : 0 < β - 1 := by linarith
  have c6 : 0 < 1 - β6 := by linarith
  have hnv : 0 < -v2 := by linarith
  have hq8 : α * (1 - β6) * (μ * β) = α * (1 - β6) := by rw [hμβ]; ring
  have hl8 : 0 < γ6 * (α - 1) * (β - 1) * μ - α * (1 - β6) := by
    nlinarith [mul_lt_mul_of_pos_right hlit hμ]
  have hk : β * v1 - (α - 1) * v2 = β * v1 - (α - 1) * v2 := rfl
  have p1 := mul_pos a1 hμ
  have p2 := mul_pos (mul_pos a1 hμ) hγ6
  have p3 := mul_pos hα0 hμ
  have p4 := mul_pos hβ0 hμ
  have p5 := mul_pos hb6 hμ
  have p6 := mul_pos a1 hnv
  have p7 := mul_pos hβ0 hnv
  have p8 := mul_pos hμ hnv
  have p9 := mul_pos (mul_pos hγ6 hμ) hnv
  have p10 := mul_pos hg1 hnv
  have p11 := mul_pos hg1 hμ
  have p12 := mul_pos (mul_pos hg1 hμ) a1
  have p13 := mul_pos (mul_pos c6 hμ) hg1
  have p14 := mul_pos hl8 hnv
  have p15 := mul_pos hl8 hμ
  have p16 := mul_pos hl8 hα0
  have p17 := mul_pos (sub_pos.2 hγ61) hμ
  have p18 := mul_pos (mul_pos (sub_pos.2 hγ61) hμ) a1
  have p19 := mul_pos hc2 hμ
  have p20 := mul_pos hc2 (mul_pos hγ6 hμ)
  have p21 := mul_pos hc2 a1
  have p22 := mul_pos (mul_pos a1 hμ) hnv
  have p23 := mul_pos hγ6 hnv
  have p24 := mul_pos hc2 hγ6
  constructor
  · intro i j h1 h2
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl h1
      | exact (h2 (by decide)).elim
      | (simp only [TSc, d3, k20R8Cyc_0, k20R8Cyc_1, k20R8Cyc_2, k20R8Cyc_3, k20R8Cyc_4, f0, f1, f2, f3, f4,
          Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
         first | (left; nlinarith) | (right; refine ⟨by ring1, by nlinarith⟩))
  · intro t ht i
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl <;>
      rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      (simp only [TSc, d3, k20R8Cyc_0, k20R8Cyc_1, k20R8Cyc_2, k20R8Cyc_3, k20R8Cyc_4, f0, f1, f2, f3, f4,
          Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
       first | (left; nlinarith) | (right; refine ⟨by ring1, by nlinarith⟩))

end C2
end Type08Sp
end Minimality
