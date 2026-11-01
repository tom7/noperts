module

public import Minimality.Type08S.C2K5LL

@[expose] public section


/-!
# K5L / M: QTc `α4 > 1`: the two cycles at `a - b'` (TSc tables)
Frame `(q, r, u0 = a - b')`: `d = 0, b = (1,0,0), c = (0,1,0), a = (0,κ,σ), b' = (0,κ,σ-1), c' = (β1, κα1, α1σ), a' = (β6, 1, 0)`,
`κ < 0, σ < 0, κ(1-β6) = 1` (`κ_c = 0` at `T`), `1 < α1`, `(σ-1)(1-β1) ≤ α1(σ-κ)` (`κ_a ≥ 0`, `κ_b > 0`).
* cell 1 (`ζ(d,b) > 0`): cycle `(a, c', a', c, d)`, cone `v1 > 0, κ(α1-1) v1 < β1 v2`.
* cell 2 (`ζ(d,b) < 0`): cycle `(b', c', a', c)`, cone `v1 < 0, β1 v2 < κ(α1-1) v1`.
-/
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

def kmCyc1 (κ σ α1 β1 β6 : ℝ) : ZMod 5 → ℝ × ℝ × ℝ :=
  ![(0, κ, σ), (β1, κ * α1, α1 * σ), (β6, 1, 0), (0, 1, 0), (0, 0, 0)]

theorem kmCyc1_0 : kmCyc1 κ σ α1 β1 β6 0 = (0, κ, σ) := rfl
theorem kmCyc1_1 : kmCyc1 κ σ α1 β1 β6 1 = (β1, κ * α1, α1 * σ) := rfl
theorem kmCyc1_2 : kmCyc1 κ σ α1 β1 β6 2 = (β6, 1, 0) := rfl
theorem kmCyc1_3 : kmCyc1 κ σ α1 β1 β6 3 = (0, 1, 0) := rfl
theorem kmCyc1_4 : kmCyc1 κ σ α1 β1 β6 4 = (0, 0, 0) := rfl

set_option maxHeartbeats 3200000 in
theorem km1_tsc {κ σ α1 β1 β6 v1 v2 : ℝ} (hκ : κ < 0) (hσ : σ < 0) (hα1 : 1 < α1) (hβ1 : 0 < β1)
    (hb6 : 1 < β6) (hκ6 : κ * (1 - β6) = 1) (hE : (σ - 1) * (1 - β1) ≤ α1 * (σ - κ))
    (hv1 : 0 < v1) (hcone : κ * (α1 - 1) * v1 < β1 * v2) :
    (∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      TSc 1 (kmCyc1 κ σ α1 β1 β6 (i + 1) - kmCyc1 κ σ α1 β1 β6 i)
        (kmCyc1 κ σ α1 β1 β6 j - kmCyc1 κ σ α1 β1 β6 i) (v1, v2, 0)) ∧
    (∀ t ∈ [((1 : ℝ), (0 : ℝ), (0 : ℝ)), (0, κ, σ - 1)], ∀ i : ZMod 5,
      TSc 1 (kmCyc1 κ σ α1 β1 β6 (i + 1) - kmCyc1 κ σ α1 β1 β6 i) (t - kmCyc1 κ σ α1 β1 β6 i) (v1, v2, 0)) := by
  obtain ⟨f0, f1, f2, f3, f4⟩ := z5_add
  have nk : 0 < -κ := by linarith
  have ns : 0 < -σ := by linarith
  have a1 : 0 < α1 - 1 := by linarith
  have b6 : 0 < β6 - 1 := by linarith
  have h1 := mul_pos nk hv1
  have h2 := mul_pos ns hv1
  have h3 := mul_pos hβ1 nk
  have h4 := mul_pos (mul_pos nk a1) hv1
  have h5 := mul_pos nk b6
  have h6 := mul_pos hβ1 b6
  have h7 := mul_pos (mul_pos hβ1 nk) b6
  have h8 := mul_pos (mul_pos nk a1) b6
  have h9 := mul_pos ns a1
  have h10 := mul_pos (mul_pos ns a1) hv1
  have h11 := mul_pos ns (sub_pos.2 hcone)
  have h12 := mul_pos hβ1 ns
  have h13 := mul_pos (mul_pos hβ1 ns) b6
  have h14 := mul_pos nk (sub_pos.2 hcone)
  have h15 := mul_pos b6 (sub_pos.2 hcone)
  have h16 := mul_pos (mul_pos nk a1) (sub_pos.2 hcone)
  constructor
  · intro i j h1 h2
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl h1
      | exact (h2 (by decide)).elim
      | (simp only [TSc, d3, kmCyc1_0, kmCyc1_1, kmCyc1_2, kmCyc1_3, kmCyc1_4, f0, f1, f2, f3, f4,
          Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
         first | (left; nlinarith) | (right; refine ⟨by ring, by nlinarith⟩))
  · intro t ht i
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl <;>
      rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      (simp only [TSc, d3, kmCyc1_0, kmCyc1_1, kmCyc1_2, kmCyc1_3, kmCyc1_4, f0, f1, f2, f3, f4,
          Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
       first | (left; nlinarith) | (right; refine ⟨by ring, by nlinarith⟩))

def kmCyc2 (κ σ α1 β1 β6 : ℝ) : ZMod 4 → ℝ × ℝ × ℝ :=
  ![(0, κ, σ - 1), (β1, κ * α1, α1 * σ), (β6, 1, 0), (0, 1, 0)]

theorem kmCyc2_0 : kmCyc2 κ σ α1 β1 β6 0 = (0, κ, σ - 1) := rfl
theorem kmCyc2_1 : kmCyc2 κ σ α1 β1 β6 1 = (β1, κ * α1, α1 * σ) := rfl
theorem kmCyc2_2 : kmCyc2 κ σ α1 β1 β6 2 = (β6, 1, 0) := rfl
theorem kmCyc2_3 : kmCyc2 κ σ α1 β1 β6 3 = (0, 1, 0) := rfl

set_option maxHeartbeats 3200000 in
theorem km2_tsc {κ σ α1 β1 β6 v1 v2 : ℝ} (hκ : κ < 0) (hσ : σ < 0) (hα1 : 1 < α1) (hβ1 : 0 < β1)
    (hb6 : 1 < β6) (hκ6 : κ * (1 - β6) = 1) (hE : (σ - 1) * (1 - β1) ≤ α1 * (σ - κ))
    (hv1 : v1 < 0) (hcone : β1 * v2 < κ * (α1 - 1) * v1) :
    (∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
      TSc 1 (kmCyc2 κ σ α1 β1 β6 (i + 1) - kmCyc2 κ σ α1 β1 β6 i)
        (kmCyc2 κ σ α1 β1 β6 j - kmCyc2 κ σ α1 β1 β6 i) (v1, v2, 0)) ∧
    (∀ t ∈ [((0 : ℝ), κ, σ), (0, 0, 0), (1, 0, 0)], ∀ i : ZMod 4,
      TSc 1 (kmCyc2 κ σ α1 β1 β6 (i + 1) - kmCyc2 κ σ α1 β1 β6 i) (t - kmCyc2 κ σ α1 β1 β6 i) (v1, v2, 0)) := by
  obtain ⟨s0, s1, s2, s3⟩ := z4_add
  have nk : 0 < -κ := by linarith
  have ns : 0 < -σ := by linarith
  have a1 : 0 < α1 - 1 := by linarith
  have b6 : 0 < β6 - 1 := by linarith
  have nv : 0 < -v1 := by linarith
  have h1 := mul_pos nk nv
  have h2 := mul_pos ns nv
  have h3 := mul_pos hβ1 nk
  have h4 := mul_pos (mul_pos nk a1) nv
  have h5 := mul_pos nk b6
  have h6 := mul_pos hβ1 b6
  have h7 := mul_pos (mul_pos hβ1 nk) b6
  have h8 := mul_pos (mul_pos nk a1) b6
  have h9 := mul_pos ns a1
  have h10 := mul_pos (mul_pos ns a1) nv
  have h11 := mul_pos ns (sub_pos.2 hcone)
  have h12 := mul_pos hβ1 ns
  have h13 := mul_pos (mul_pos hβ1 ns) b6
  have h14 := mul_pos nk (sub_pos.2 hcone)
  have h15 := mul_pos b6 (sub_pos.2 hcone)
  have h16 := mul_pos (mul_pos nk a1) (sub_pos.2 hcone)
  have h17 : 0 < 1 - σ := by linarith
  have h18 := mul_pos h17 nv
  have h19 := mul_pos (sub_pos.2 hcone) h17
  constructor
  · intro i j h1 h2
    rcases z4_cases i with rfl | rfl | rfl | rfl <;>
      rcases z4_cases j with rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl h1
      | exact (h2 (by decide)).elim
      | (simp only [TSc, d3, kmCyc2_0, kmCyc2_1, kmCyc2_2, kmCyc2_3, s0, s1, s2, s3,
          Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
         first | (left; nlinarith) | (right; refine ⟨by ring, by nlinarith⟩))
  · intro t ht i
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl <;>
      rcases z4_cases i with rfl | rfl | rfl | rfl <;>
      (simp only [TSc, d3, kmCyc2_0, kmCyc2_1, kmCyc2_2, kmCyc2_3, s0, s1, s2, s3,
          Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
       first | (left; nlinarith) | (right; refine ⟨by ring, by nlinarith⟩))

end C2
end Type08Sp
end Minimality
