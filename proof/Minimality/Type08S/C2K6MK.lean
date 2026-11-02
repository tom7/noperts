module

public import Minimality.Type08S.C2K6MJ

@[expose] public section


set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped RealInnerProductSpace Topology
open Finset Filter
namespace Minimality
namespace Type08Sp
namespace C2

/-- H2 cell 1: pentagon `(a, c', a', c, d)` in the `a - b'` frame, `a' = (β6, γ6, 0)`. -/
def k6mHCyc1 (κ σ α1 β1 β6 γ6 : ℝ) : ZMod 5 → ℝ × ℝ × ℝ :=
  ![(0, κ, σ), (β1, κ * α1, α1 * σ), (β6, γ6, 0), (0, 1, 0), (0, 0, 0)]

theorem k6mHCyc1_0 : k6mHCyc1 κ σ α1 β1 β6 γ6 0 = (0, κ, σ) := rfl
theorem k6mHCyc1_1 : k6mHCyc1 κ σ α1 β1 β6 γ6 1 = (β1, κ * α1, α1 * σ) := rfl
theorem k6mHCyc1_2 : k6mHCyc1 κ σ α1 β1 β6 γ6 2 = (β6, γ6, 0) := rfl
theorem k6mHCyc1_3 : k6mHCyc1 κ σ α1 β1 β6 γ6 3 = (0, 1, 0) := rfl
theorem k6mHCyc1_4 : k6mHCyc1 κ σ α1 β1 β6 γ6 4 = (0, 0, 0) := rfl

/-- H2 cell 2: quadrilateral `(b', c', a', c)`. -/
def k6mHCyc2 (κ σ α1 β1 β6 γ6 : ℝ) : ZMod 4 → ℝ × ℝ × ℝ :=
  ![(0, κ, σ - 1), (β1, κ * α1, α1 * σ), (β6, γ6, 0), (0, 1, 0)]

theorem k6mHCyc2_0 : k6mHCyc2 κ σ α1 β1 β6 γ6 0 = (0, κ, σ - 1) := rfl
theorem k6mHCyc2_1 : k6mHCyc2 κ σ α1 β1 β6 γ6 1 = (β1, κ * α1, α1 * σ) := rfl
theorem k6mHCyc2_2 : k6mHCyc2 κ σ α1 β1 β6 γ6 2 = (β6, γ6, 0) := rfl
theorem k6mHCyc2_3 : k6mHCyc2 κ σ α1 β1 β6 γ6 3 = (0, 1, 0) := rfl

set_option maxHeartbeats 3200000 in
theorem k6m_hc1_tsc {κ σ α1 β1 β6 γ6 v1 v2 : ℝ} (hκ : κ < 0) (hσ : σ < 0) (hα1 : 1 < α1) (hβ1 : 0 < β1)
    (hb6 : 1 < β6) (hγ6 : 0 < γ6) (hγ61 : γ6 < 1)
    (hbc : 0 < -κ * α1 * (β6 - β1) - (γ6 - κ * α1) * (1 - β1))
    (hcc : 0 < β1 * (γ6 - κ * α1) - κ * (α1 - 1) * (β6 - β1))
    (haa : 0 < (β6 - β1) * (1 - γ6) + β6 * (γ6 - κ * α1))
    (hE : (σ - 1) * (1 - β1) ≤ α1 * (σ - κ))
    (hv1 : 0 < v1) (hcone : κ * (α1 - 1) * v1 < β1 * v2) :
    (∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      TSc 1 (k6mHCyc1 κ σ α1 β1 β6 γ6 (i + 1) - k6mHCyc1 κ σ α1 β1 β6 γ6 i)
        (k6mHCyc1 κ σ α1 β1 β6 γ6 j - k6mHCyc1 κ σ α1 β1 β6 γ6 i) (v1, v2, 0)) ∧
    (∀ t ∈ [((1 : ℝ), (0 : ℝ), (0 : ℝ)), (0, κ, σ - 1)], ∀ i : ZMod 5,
      TSc 1 (k6mHCyc1 κ σ α1 β1 β6 γ6 (i + 1) - k6mHCyc1 κ σ α1 β1 β6 γ6 i)
        (t - k6mHCyc1 κ σ α1 β1 β6 γ6 i) (v1, v2, 0)) := by
  obtain ⟨f0, f1, f2, f3, f4⟩ := z5_add
  have nk : 0 < -κ := by linarith
  have ns : 0 < -σ := by linarith
  have a1 : 0 < α1 - 1 := by linarith
  have b6 : 0 < β6 - 1 := by linarith
  have g1 : 0 < 1 - γ6 := by linarith
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
  have h17 := mul_pos ns hγ6
  have h18 := mul_pos nk hγ6
  have h19 := mul_pos ns g1
  have h20 := mul_pos nk g1
  have h21 := mul_pos ns hbc
  have h22 := mul_pos ns hcc
  have h23 := mul_pos ns haa
  have h24 := mul_pos hv1 hbc
  have h25 := mul_pos hv1 hcc
  have h26 := mul_pos hv1 haa
  have h27 := mul_pos (sub_pos.2 hcone) hbc
  have h28 := mul_pos (sub_pos.2 hcone) hcc
  have h29 := mul_pos (sub_pos.2 hcone) haa
  constructor
  · intro i j h1 h2
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl h1
      | exact (h2 (by decide)).elim
      | (simp only [TSc, d3, k6mHCyc1_0, k6mHCyc1_1, k6mHCyc1_2, k6mHCyc1_3, k6mHCyc1_4, f0, f1, f2, f3, f4,
          Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
         first | (left; nlinarith) | (right; refine ⟨by ring, by nlinarith⟩))
  · intro t ht i
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl <;>
      rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      (simp only [TSc, d3, k6mHCyc1_0, k6mHCyc1_1, k6mHCyc1_2, k6mHCyc1_3, k6mHCyc1_4, f0, f1, f2, f3, f4,
          Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
       first | (left; nlinarith) | (right; refine ⟨by ring, by nlinarith⟩))

set_option maxHeartbeats 3200000 in
theorem k6m_hc2_tsc {κ σ α1 β1 β6 γ6 v1 v2 : ℝ} (hκ : κ < 0) (hσ : σ < 0) (hα1 : 1 < α1) (hβ1 : 0 < β1)
    (hb6 : 1 < β6) (hγ6 : 0 < γ6) (hγ61 : γ6 < 1)
    (hbc : 0 < -κ * α1 * (β6 - β1) - (γ6 - κ * α1) * (1 - β1))
    (hcc : 0 < β1 * (γ6 - κ * α1) - κ * (α1 - 1) * (β6 - β1))
    (haa : 0 < (β6 - β1) * (1 - γ6) + β6 * (γ6 - κ * α1)) (hE : (σ - 1) * (1 - β1) ≤ α1 * (σ - κ))
    (hv1 : v1 < 0) (hcone : β1 * v2 < κ * (α1 - 1) * v1) :
    (∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
      TSc 1 (k6mHCyc2 κ σ α1 β1 β6 γ6 (i + 1) - k6mHCyc2 κ σ α1 β1 β6 γ6 i)
        (k6mHCyc2 κ σ α1 β1 β6 γ6 j - k6mHCyc2 κ σ α1 β1 β6 γ6 i) (v1, v2, 0)) ∧
    (∀ t ∈ [((0 : ℝ), κ, σ), (0, 0, 0), (1, 0, 0)], ∀ i : ZMod 4,
      TSc 1 (k6mHCyc2 κ σ α1 β1 β6 γ6 (i + 1) - k6mHCyc2 κ σ α1 β1 β6 γ6 i) (t - k6mHCyc2 κ σ α1 β1 β6 γ6 i) (v1, v2, 0)) := by
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
  have g1 : 0 < 1 - γ6 := by linarith
  have h30 := mul_pos ns hγ6
  have h31 := mul_pos nk hγ6
  have h32 := mul_pos ns g1
  have h33 := mul_pos nk g1
  have h34 := mul_pos ns hbc
  have h35 := mul_pos ns hcc
  have h36 := mul_pos ns haa
  have h37 := mul_pos nv hbc
  have h38 := mul_pos nv hcc
  have h39 := mul_pos nv haa
  have h40 := mul_pos (sub_pos.2 hcone) hbc
  have h41 := mul_pos (sub_pos.2 hcone) hcc
  have h42 := mul_pos (sub_pos.2 hcone) haa
  constructor
  · intro i j h1 h2
    rcases z4_cases i with rfl | rfl | rfl | rfl <;>
      rcases z4_cases j with rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl h1
      | exact (h2 (by decide)).elim
      | (simp only [TSc, d3, k6mHCyc2_0, k6mHCyc2_1, k6mHCyc2_2, k6mHCyc2_3, s0, s1, s2, s3,
          Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
         first | (left; nlinarith) | (right; refine ⟨by ring, by nlinarith⟩))
  · intro t ht i
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl <;>
      rcases z4_cases i with rfl | rfl | rfl | rfl <;>
      (simp only [TSc, d3, k6mHCyc2_0, k6mHCyc2_1, k6mHCyc2_2, k6mHCyc2_3, s0, s1, s2, s3,
          Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
       first | (left; nlinarith) | (right; refine ⟨by ring, by nlinarith⟩))


end C2
end Type08Sp
end Minimality
