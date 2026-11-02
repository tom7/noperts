module

public import Minimality.Type08S.C2K17HZ

@[expose] public section


/-!
# K20H5 / A: H5 rule r3 (view `v = α1 (a-d) - (σ-β1)(c-d)`, the line view `L15`), pentagon `(b, d, a, b', c')`.
Frame `(a - d, b - d, v)`, `κ (σ - β1) = 1`, `w = γ6 κ = κ (β1 - β6) + 1`:
`c = (α κ, 0, -κ)`, `b' = (α (1 + β κ), 0, -β κ)`, `a' = (α w, β6, -w)`, `c' = (α, β, 0)`.
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

def k20R3Cyc (α β κ : ℝ) : ZMod 5 → ℝ × ℝ × ℝ :=
  ![(0, 1, 0), (0, 0, 0), (1, 0, 0), (α * (1 + β * κ), 0, -(β * κ)), (α, β, 0)]

theorem k20R3Cyc_0 : k20R3Cyc α β κ 0 = (0, 1, 0) := rfl
theorem k20R3Cyc_1 : k20R3Cyc α β κ 1 = (0, 0, 0) := rfl
theorem k20R3Cyc_2 : k20R3Cyc α β κ 2 = (1, 0, 0) := rfl
theorem k20R3Cyc_3 : k20R3Cyc α β κ 3 = (α * (1 + β * κ), 0, -(β * κ)) := rfl
theorem k20R3Cyc_4 : k20R3Cyc α β κ 4 = (α, β, 0) := rfl

theorem k20R3_inj {α β κ : ℝ} (hα : 0 < α) (hβ : 0 < β) (hκ : 0 < κ) :
    ∀ i j : ZMod 5, k20R3Cyc α β κ i = k20R3Cyc α β κ j → i = j := by
  intro i j h
  have e1 := congrArg Prod.fst h
  have e2 := congrArg (fun t => t.2.1) h
  have e3 := congrArg (fun t => t.2.2) h
  have hb : 0 < β * κ := mul_pos hβ hκ
  have hab : 0 < α * (1 + β * κ) := mul_pos hα (by linarith)
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;> rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    first | rfl | (exfalso; simp only [k20R3Cyc_0, k20R3Cyc_1, k20R3Cyc_2, k20R3Cyc_3, k20R3Cyc_4] at e1 e2 e3; nlinarith)

set_option maxHeartbeats 6400000 in
theorem k20R3_tsc {α β β6 w κ v1 v2 : ℝ} (hα : 1 < α) (hβ : 1 < β) (hb6 : 0 < β6) (hb61 : β6 < 1)
    (hκ : 0 < κ) (hw : w = κ * (β - β6) + 1)
    (hc1 : 0 < v2) (hc2 : v1 + α * κ * v2 < 0) :
    (∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      TSc 1 (k20R3Cyc α β κ (i + 1) - k20R3Cyc α β κ i)
        (k20R3Cyc α β κ j - k20R3Cyc α β κ i) (v1, v2, 0)) ∧
    (∀ t ∈ [((α * κ : ℝ), (0 : ℝ), -κ), (α * w, β6, -w)], ∀ i : ZMod 5,
      TSc 1 (k20R3Cyc α β κ (i + 1) - k20R3Cyc α β κ i)
        (t - k20R3Cyc α β κ i) (v1, v2, 0)) := by
  obtain ⟨f0, f1, f2, f3, f4⟩ := z5_add
  subst hw
  have a1 : 0 < α - 1 := by linarith
  have b1 : 0 < β - 1 := by linarith
  have c6 : 0 < 1 - β6 := by linarith
  have bb : 0 < β - β6 := by linarith
  have hα0 : 0 < α := by linarith
  have hβ0 : 0 < β := by linarith
  have k1 := mul_pos hα0 hκ
  have k2 := mul_pos hβ0 hκ
  have k3 := mul_pos hκ bb
  have k4 := mul_pos (mul_pos hα0 hβ0) hκ
  have k5 := mul_pos hα0 hβ0
  have k6 := mul_pos hα0 b1
  have k7 := mul_pos hα0 hb6
  have k8 := mul_pos hβ0 hb6
  have k9 := mul_pos (mul_pos hκ hα0) b1
  have k10 := mul_pos (mul_pos hκ hα0) hb6
  have k11 := mul_pos (mul_pos hκ hβ0) b1
  have k12 := mul_pos hα0 c6
  have k13 := mul_pos hβ0 c6
  have k14 := mul_pos (mul_pos hκ hα0) bb
  have k15 := mul_pos (mul_pos hκ hα0) (mul_pos hκ hβ0)
  have hv2 : 0 < α * v2 := mul_pos hα0 hc1
  have hv3 : 0 < κ * v2 := mul_pos hκ hc1
  have hv4 : 0 < β * v2 := mul_pos hβ0 hc1
  have hv5 : 0 < α * κ * v2 := mul_pos k1 hc1
  have hv6 : 0 < β * κ * v2 := mul_pos k2 hc1
  have hv7 : 0 < α * β * κ * v2 := mul_pos k4 hc1
  have hn : 0 < -(v1 + α * κ * v2) := by linarith
  have hn2 := mul_pos hβ0 hn
  have hn3 := mul_pos hκ hn
  have hn4 := mul_pos hα0 hn
  have hn5 := mul_pos k2 hn
  constructor
  · intro i j h1 h2
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl h1
      | exact (h2 (by decide)).elim
      | (simp only [TSc, d3, k20R3Cyc_0, k20R3Cyc_1, k20R3Cyc_2, k20R3Cyc_3, k20R3Cyc_4, f0, f1, f2, f3, f4,
          Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
         first | (left; nlinarith) | (right; refine ⟨by ring, by nlinarith⟩))
  · intro t ht i
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl <;>
      rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      (simp only [TSc, d3, k20R3Cyc_0, k20R3Cyc_1, k20R3Cyc_2, k20R3Cyc_3, k20R3Cyc_4, f0, f1, f2, f3, f4,
          Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
       first | (left; nlinarith) | (right; refine ⟨by ring, by nlinarith⟩))

end C2
end Type08Sp
end Minimality
