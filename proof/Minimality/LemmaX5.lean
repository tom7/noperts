module

public import Minimality.Quad05Leaf
public import Minimality.FaceChordFac
public import Minimality.RimFromSigns
public import Minimality.Q45Signs
public import Minimality.Type24SAT.K24.Par2546

@[expose] public section

open scoped RealInnerProductSpace Topology
open Finset Filter
open Minimality Minimality.H21 Minimality.T24.SAT Minimality.T24.Quad05 Minimality.RimFromSigns Minimality.T24.Q45

namespace Minimality.T24.X5

/-- The perturbed view direction for Lemma X5 on facet `0345` (facet 3).
With chord edge `4 -> 0` and middle `5`, `u_X5 x η = (x 0 - x 5) + η • (x 4 - x 5)`. -/
def u_X5 (x : Fin 7 → ℝ³) (η : ℝ) : ℝ³ :=
  (x 0 - x 5) + η • (x 4 - x 5)

/-- Algebraic decomposition of vertex 3 as a chord middle over edge `0 -> 4`
along the perturbed view `u_X5 x η`. -/
theorem x3_middle_X5 (x : Fin 7 → ℝ³) (s t η : ℝ) (hη1 : 1 + η ≠ 0)
    (hdecomp : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0)) :
    x 3 = x 0 + (s + t * η / (1 + η)) • (x 4 - x 0) + (-t / (1 + η)) • u_X5 x η := by
  ext j
  have hd := congr_arg (fun (v : ℝ³) => v j) hdecomp
  simp only [u_X5, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at hd ⊢
  set A := s + t * η / (1 + η)
  set B := -t / (1 + η)
  have hA : A * (1 + η) = s * (1 + η) + t * η := by
    dsimp [A]
    rw [add_mul, div_mul_cancel₀ _ hη1]
  have hB : B * (1 + η) = -t := by
    dsimp [B]
    rw [div_mul_cancel₀ _ hη1]
  apply mul_right_cancel₀ hη1
  calc
    (x 3 j) * (1 + η) = (x 0 j + (s * (x 4 j - x 0 j) + t * (x 5 j - x 0 j))) * (1 + η) := by
      rw [show x 3 j = x 0 j + (x 3 j - x 0 j) by ring, hd]
    _ = (x 0 j + A * (x 4 j - x 0 j) + B * (x 0 j - x 5 j + η * (x 4 j - x 5 j))) * (1 + η) := by
      linear_combination - (x 4 j - x 0 j) * hA - (x 0 j - x 5 j + η * (x 4 j - x 5 j)) * hB

/-- Direct application of `isRupert_quadChord` at a specific parameter `η`
satisfying the open middle and depth inequalities. -/
theorem isRupert_of_X5_witness {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (s t : ℝ) (hdecomp : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0))
    {η : ℝ} (hη : 0 ≤ η) (hη1 : 1 + η ≠ 0)
    (hs₀ : 0 < s + t * η / (1 + η)) (hs₁ : s + t * η / (1 + η) < 1)
    (hδ : -t / (1 + η) ≠ 0)
    {ρ : ℝ} (hρ : ρ ≠ 0)
    (hcyc : ∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
      0 < ρ * det3 (quad (x 6) (x 4) (x 0) (x 2) (i + 1) - quad (x 6) (x 4) (x 0) (x 2) i)
        (quad (x 6) (x 4) (x 0) (x 2) j - quad (x 6) (x 4) (x 0) (x 2) i) (u_X5 x η))
    (hI : ∀ i : ZMod 4,
      0 < ρ * det3 (quad (x 6) (x 4) (x 0) (x 2) (i + 1) - quad (x 6) (x 4) (x 0) (x 2) i)
        (x 1 - quad (x 6) (x 4) (x 0) (x 2) i) (u_X5 x η))
    (hPA : ⟪x 6, u_X5 x η⟫ < ⟪x 4, u_X5 x η⟫)
    (hAB : ⟪x 4, u_X5 x η⟫ < ⟪x 0, u_X5 x η⟫)
    (hQP : ⟪x 2, u_X5 x η⟫ ≠ ⟪x 6, u_X5 x η⟫)
    (hQA : ⟪x 2, u_X5 x η⟫ ≠ ⟪x 4, u_X5 x η⟫)
    (hQB : ⟪x 2, u_X5 x η⟫ ≠ ⟪x 0, u_X5 x η⟫)
    (hS3 : 0 < det3 (x 0 - x 5) (x 4 - x 5) (x 2 - x 6) * det3 (x 0 - x 5) (x 4 - x 5) (x 1 - x 5))
    (hS4 : det3 (x 0 - x 5) (x 4 - x 5) (cross (x 0 - x 4) (x 2 - x 4)) ≠ 0 ∨
      ⟪x 2 - x 4, x 0 - x 4⟫ < 0 ∨ ⟪x 2 - x 0, x 4 - x 0⟫ < 0) :
    IsRupert (univ.image x) := by
  have hcov : ∀ j : Fin 7, j = 5 ∨ j = 3 ∨ j = 4 ∨ j = 0 ∨ j = 6 ∨ j = 2 ∨ j = 1 := by
    intro j; fin_cases j <;> decide
  have hlab : [(5 : Fin 7), 3, 4, 0, 6, 2].Nodup := by decide
  have hoS : (5 : Fin 7) ∈ s0x_S24 3 := by decide
  have hAS : (4 : Fin 7) ∈ s0x_S24 3 := by decide
  have hBS : (0 : Fin 7) ∈ s0x_S24 3 := by decide
  have hPS : (6 : Fin 7) ∉ s0x_S24 3 := by decide
  have hQS : (2 : Fin 7) ∉ s0x_S24 3 := by decide
  have hIS : (1 : Fin 7) ∉ s0x_S24 3 := by decide
  have hu : u_X5 x η = (x 0 - x 5) + η • (x 4 - x 5) := rfl
  have h3 := x3_middle_X5 x s t η hη1 hdecomp
  have hw : ((2 : Fin 7) = 2 ∧ (6 : Fin 7) = 6) ∨ ((2 : Fin 7) = 6 ∧ (6 : Fin 7) = 2) :=
    Or.inl ⟨rfl, rfl⟩
  exact isRupert_quadChord F hcov hlab hoS hAS hBS hPS hQS hIS hη hu hρ hcyc hI
    h3 hs₀ hs₁ hδ hPA hAB hQP hQA hQB hw hS3 hS4

/-- **Lemma X5 (Q45X24.md / Q45PROOF24.md): Corner Leaf at `e5 - ε e4`.**
For a Type 24 OB1 solid (`F : S0xFac 9 s0x_S24 x`), when `σ < 1` (where `x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0)`
is the quad decomposition of Lemma M with `s < 1`), `g45 = ⟪x 4 - x 0, x 5 - x 0⟫ > 0`, and the special positions
S1-S4 hold, the solid is Rupert (`IsRupert (univ.image x)`). -/
theorem lemma_X5 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (s t : ℝ) (hdecomp : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0))
    (hs0 : 0 < s) (hs : s < 1) (ht : 0 < t)
    (hg45 : 0 < ⟪x 4 - x 0, x 5 - x 0⟫)
    (hS1 : ⟪x 2 - x 0, x 0 - x 5⟫ ≠ 0 ∧ ⟪x 2 - x 4, x 0 - x 5⟫ ≠ 0 ∧ ⟪x 2 - x 6, x 0 - x 5⟫ ≠ 0)
    (hS2 : ⟪x 6 - x 4, x 0 - x 5⟫ < 0)
    (hS3 : 0 < det3 (x 0 - x 5) (x 4 - x 5) (x 2 - x 6) * det3 (x 0 - x 5) (x 4 - x 5) (x 1 - x 5))
    (hS4 : det3 (x 0 - x 5) (x 4 - x 5) (cross (x 0 - x 4) (x 2 - x 4)) ≠ 0 ∨
      ⟪x 2 - x 4, x 0 - x 4⟫ < 0 ∨ ⟪x 2 - x 0, x 4 - x 0⟫ < 0)
    (hcyc_I : ∃ ρ : ℝ, ρ ≠ 0 ∧ ∀ᶠ η in 𝓝[>] (0 : ℝ),
      (∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
        0 < ρ * det3 (quad (x 6) (x 4) (x 0) (x 2) (i + 1) - quad (x 6) (x 4) (x 0) (x 2) i)
          (quad (x 6) (x 4) (x 0) (x 2) j - quad (x 6) (x 4) (x 0) (x 2) i) (u_X5 x η)) ∧
      (∀ i : ZMod 4,
        0 < ρ * det3 (quad (x 6) (x 4) (x 0) (x 2) (i + 1) - quad (x 6) (x 4) (x 0) (x 2) i)
          (x 1 - quad (x 6) (x 4) (x 0) (x 2) i) (u_X5 x η))) :
    IsRupert (univ.image x) := by
  obtain ⟨ρ, hρ, hcyc_I_ev⟩ := hcyc_I
  have ev_pos : ∀ᶠ η in 𝓝[>] (0 : ℝ), 0 ≤ η := by
    filter_upwards [self_mem_nhdsWithin] with η hη
    exact le_of_lt hη
  have ev_hη1 : ∀ᶠ η in 𝓝[>] (0 : ℝ), 1 + η ≠ 0 := by
    have hc : ContinuousAt (fun η : ℝ => 1 + η) 0 := by fun_prop
    have hne : (1 : ℝ) + 0 ≠ 0 := by norm_num
    exact (ContinuousAt.eventually_ne hc hne).filter_mono nhdsWithin_le_nhds
  have ev_s0 : ∀ᶠ η in 𝓝[>] (0 : ℝ), 0 < s + t * η / (1 + η) := by
    have hc : ContinuousAt (fun η : ℝ => s + t * η / (1 + η)) 0 := by
      exact ContinuousAt.add continuousAt_const
        (ContinuousAt.div (by fun_prop) (by fun_prop) (by norm_num : (1 : ℝ) + 0 ≠ 0))
    have hval : 0 < s + t * (0 : ℝ) / (1 + 0) := by
      have : s + t * (0 : ℝ) / (1 + 0) = s := by ring
      rw [this]
      exact hs0
    exact (ContinuousAt.eventually_lt (continuousAt_const (x := 0)) hc hval).filter_mono nhdsWithin_le_nhds
  have ev_s1 : ∀ᶠ η in 𝓝[>] (0 : ℝ), s + t * η / (1 + η) < 1 := by
    have hc : ContinuousAt (fun η : ℝ => s + t * η / (1 + η)) 0 :=
      ContinuousAt.add continuousAt_const
        (ContinuousAt.div (by fun_prop) (by fun_prop) (by norm_num : (1 : ℝ) + 0 ≠ 0))
    have hval : s + t * (0 : ℝ) / (1 + 0) < 1 := by
      have : s + t * (0 : ℝ) / (1 + 0) = s := by ring
      rw [this]
      exact hs
    exact (ContinuousAt.eventually_lt hc (continuousAt_const (x := 0)) hval).filter_mono nhdsWithin_le_nhds
  have ev_δ : ∀ᶠ η in 𝓝[>] (0 : ℝ), -t / (1 + η) ≠ 0 := by
    have hc : ContinuousAt (fun η : ℝ => -t / (1 + η)) 0 :=
      ContinuousAt.div (by fun_prop) (by fun_prop) (by norm_num : (1 : ℝ) + 0 ≠ 0)
    have hval : -t / (1 + (0 : ℝ)) ≠ 0 := by
      have : -t / (1 + (0 : ℝ)) = -t := by ring
      rw [this]
      exact neg_ne_zero.mpr ht.ne'
    exact (ContinuousAt.eventually_ne hc hval).filter_mono nhdsWithin_le_nhds
  have ev_u : ContinuousAt (fun η : ℝ => u_X5 x η) 0 := by
    dsimp [u_X5]
    fun_prop
  have ev_inner_lt (v : ℝ³) (hv : ⟪v, x 0 - x 5⟫ < 0) : ∀ᶠ η in 𝓝[>] (0 : ℝ), ⟪v, u_X5 x η⟫ < 0 := by
    have hc : ContinuousAt (fun η : ℝ => ⟪v, u_X5 x η⟫) 0 :=
      ContinuousAt.inner continuousAt_const ev_u
    have hval : ⟪v, u_X5 x (0 : ℝ)⟫ < 0 := by
      have : u_X5 x 0 = x 0 - x 5 := by
        dsimp [u_X5]
        rw [zero_smul, add_zero]
      rw [this]
      exact hv
    exact (ContinuousAt.eventually_lt hc (continuousAt_const (x := 0)) hval).filter_mono nhdsWithin_le_nhds
  have ev_inner_ne (v : ℝ³) (hv : ⟪v, x 0 - x 5⟫ ≠ 0) : ∀ᶠ η in 𝓝[>] (0 : ℝ), ⟪v, u_X5 x η⟫ ≠ 0 := by
    have hc : ContinuousAt (fun η : ℝ => ⟪v, u_X5 x η⟫) 0 :=
      ContinuousAt.inner continuousAt_const ev_u
    have hval : ⟪v, u_X5 x (0 : ℝ)⟫ ≠ 0 := by
      have : u_X5 x 0 = x 0 - x 5 := by
        dsimp [u_X5]
        rw [zero_smul, add_zero]
      rw [this]
      exact hv
    exact (ContinuousAt.eventually_ne hc hval).filter_mono nhdsWithin_le_nhds
  have h405 : ⟪x 4 - x 0, x 0 - x 5⟫ < 0 := by
    have : x 0 - x 5 = - (x 5 - x 0) := by
      ext j
      simp only [PiLp.sub_apply, PiLp.neg_apply]
      ring
    rw [this, inner_neg_right]
    linarith [hg45]
  have ev_PA := ev_inner_lt (x 6 - x 4) hS2
  have ev_AB := ev_inner_lt (x 4 - x 0) h405
  have ev_QP := ev_inner_ne (x 2 - x 6) hS1.2.2
  have ev_QA := ev_inner_ne (x 2 - x 4) hS1.2.1
  have ev_QB := ev_inner_ne (x 2 - x 0) hS1.1

  have hall := ev_pos.and (ev_hη1.and (ev_s0.and (ev_s1.and (ev_δ.and (ev_PA.and (ev_AB.and (ev_QP.and (ev_QA.and (ev_QB.and hcyc_I_ev)))))))))
  obtain ⟨η, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, hcyc, hI⟩ := hall.exists

  have hPA_η : ⟪x 6, u_X5 x η⟫ < ⟪x 4, u_X5 x η⟫ := by
    have := inner_sub_left (𝕜 := ℝ) (x 6) (x 4) (u_X5 x η)
    linarith
  have hAB_η : ⟪x 4, u_X5 x η⟫ < ⟪x 0, u_X5 x η⟫ := by
    have := inner_sub_left (𝕜 := ℝ) (x 4) (x 0) (u_X5 x η)
    linarith
  have hQP_η : ⟪x 2, u_X5 x η⟫ ≠ ⟪x 6, u_X5 x η⟫ := by
    intro h
    apply h7
    rw [inner_sub_left (𝕜 := ℝ), h, sub_self]
  have hQA_η : ⟪x 2, u_X5 x η⟫ ≠ ⟪x 4, u_X5 x η⟫ := by
    intro h
    apply h8
    rw [inner_sub_left (𝕜 := ℝ), h, sub_self]
  have hQB_η : ⟪x 2, u_X5 x η⟫ ≠ ⟪x 0, u_X5 x η⟫ := by
    intro h
    apply h9
    rw [inner_sub_left (𝕜 := ℝ), h, sub_self]

  exact isRupert_of_X5_witness F s t hdecomp h0 h1 h2 h3 h4 hρ hcyc hI
    hPA_η hAB_η hQP_η hQA_η hQB_η hS3 hS4

/-- Strict convexity of rim `quad (x 6) (x 4) (x 0) (x 2)` and vertex 1 strictly inside
from the silhouette facet signs at view `u`.
Along ridge 26 between facet 7 (`236`) and facet 5 (`126`),
facet 7 is back (`hN7 < 0`) and facet 5 is front (`0 < hN5`). -/
theorem lemmaX5_quad_signs {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) {u : ℝ³}
    (hN3 : ⟪F.N 3, u⟫ = 0)
    (hN4 : 0 < ⟪F.N 4, u⟫) (hN8 : ⟪F.N 8, u⟫ < 0)
    (hN0 : 0 < ⟪F.N 0, u⟫) (hN2 : ⟪F.N 2, u⟫ < 0)
    (hN7 : ⟪F.N 7, u⟫ < 0) (hN5 : 0 < ⟪F.N 5, u⟫) :
    ∃ ρ : ℝ, ρ ≠ 0 ∧
      (∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
        0 < ρ * det3 (quad (x 6) (x 4) (x 0) (x 2) (i + 1) - quad (x 6) (x 4) (x 0) (x 2) i)
          (quad (x 6) (x 4) (x 0) (x 2) j - quad (x 6) (x 4) (x 0) (x 2) i) u) ∧
      (∀ i : ZMod 4,
        0 < ρ * det3 (quad (x 6) (x 4) (x 0) (x 2) (i + 1) - quad (x 6) (x 4) (x 0) (x 2) i)
          (x 1 - quad (x 6) (x 4) (x 0) (x 2) i) u) :=
  rim6402_of_signs F hN3 hN4 hN8 hN0 hN2 hN7 hN5

/-- **Lemma X5' (Q45X24.md / Q45THEOREM24.md): Corner Leaf at `e5 - ε e4` with genuine satisfiable facet signs.**
In the corner frame at vertex 1:
- `hN5 : 0 < ⟪F.N 5, x 0 - x 5⟫` iff `a5 > 1` (the true condition in the `a4, a5 > 1` regime).
- `hN7 : ⟪F.N 7, x 0 - x 5⟫ < 0` (facet 236 facing back).
- `hN8 : ⟪F.N 8, x 0 - x 5⟫ < 0` (facet 346 facing back). -/
theorem lemma_X5' {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (s t : ℝ) (hdecomp : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0))
    (hs0 : 0 < s) (hs : s < 1) (ht : 0 < t)
    (hg45 : 0 < ⟪x 4 - x 0, x 5 - x 0⟫)
    (hS1 : ⟪x 2 - x 0, x 0 - x 5⟫ ≠ 0 ∧ ⟪x 2 - x 4, x 0 - x 5⟫ ≠ 0 ∧ ⟪x 2 - x 6, x 0 - x 5⟫ ≠ 0)
    (hS2 : ⟪x 6 - x 4, x 0 - x 5⟫ < 0)
    (hS3 : 0 < det3 (x 0 - x 5) (x 4 - x 5) (x 2 - x 6) * det3 (x 0 - x 5) (x 4 - x 5) (x 1 - x 5))
    (hS4 : det3 (x 0 - x 5) (x 4 - x 5) (cross (x 0 - x 4) (x 2 - x 4)) ≠ 0 ∨
      ⟪x 2 - x 4, x 0 - x 4⟫ < 0 ∨ ⟪x 2 - x 0, x 4 - x 0⟫ < 0)
    (hN5 : 0 < ⟪F.N 5, x 0 - x 5⟫)
    (hN7 : ⟪F.N 7, x 0 - x 5⟫ < 0)
    (hN8 : ⟪F.N 8, x 0 - x 5⟫ < 0) :
    IsRupert (univ.image x) := by
  have hN0 : 0 < ⟪F.N 0, x 0 - x 5⟫ := by
    have := (F.hN 0 (x 0) (x 5)).symm
    rw [F.zero 0 0 (by decide)] at this
    linarith [F.neg 0 5 (by decide)]

  have hN4 : 0 < ⟪F.N 4, x 0 - x 5⟫ := by
    have := (F.hN 4 (x 0) (x 5)).symm
    rw [F.zero 4 0 (by decide)] at this
    linarith [F.neg 4 5 (by decide)]

  have hN2_slope : ⟪F.N 2, x 4 - x 5⟫ < 0 := by
    have := (F.hN 2 (x 4) (x 5)).symm
    rw [F.zero 2 5 (by decide)] at this
    linarith [F.neg 2 4 (by decide)]
  have ev_u : ContinuousAt (u_X5 x) 0 := by
    change ContinuousAt (fun η : ℝ => (x 0 - x 5) + η • (x 4 - x 5)) 0
    fun_prop
  have ev_pos : ∀ᶠ η in 𝓝[>] (0 : ℝ), 0 ≤ η :=
    eventually_mem_nhdsWithin.mono fun _ h => le_of_lt h
  have ev_hη1 : ∀ᶠ η in 𝓝[>] (0 : ℝ), 1 + η ≠ 0 := by
    have hc : ContinuousAt (fun η : ℝ => 1 + η) 0 := by fun_prop
    have hne : (1 : ℝ) + 0 ≠ 0 := by norm_num
    exact (ContinuousAt.eventually_ne hc hne).filter_mono nhdsWithin_le_nhds
  have ev_s0 : ∀ᶠ η in 𝓝[>] (0 : ℝ), 0 < s + t * η / (1 + η) := by
    have hc : ContinuousAt (fun η : ℝ => s + t * η / (1 + η)) 0 :=
      ContinuousAt.add continuousAt_const (ContinuousAt.div (by fun_prop) (by fun_prop) (by norm_num : (1 : ℝ) + 0 ≠ 0))
    have hval : 0 < s + t * (0 : ℝ) / (1 + 0) := by
      rw [mul_zero, zero_div, add_zero]
      exact hs0
    exact (ContinuousAt.eventually_lt (continuousAt_const (x := 0)) hc hval).filter_mono nhdsWithin_le_nhds
  have ev_s1 : ∀ᶠ η in 𝓝[>] (0 : ℝ), s + t * η / (1 + η) < 1 := by
    have hc : ContinuousAt (fun η : ℝ => s + t * η / (1 + η)) 0 :=
      ContinuousAt.add continuousAt_const (ContinuousAt.div (by fun_prop) (by fun_prop) (by norm_num : (1 : ℝ) + 0 ≠ 0))
    have hval : s + t * (0 : ℝ) / (1 + 0) < 1 := by
      rw [mul_zero, zero_div, add_zero]
      exact hs
    exact (ContinuousAt.eventually_lt hc (continuousAt_const (x := 0)) hval).filter_mono nhdsWithin_le_nhds
  have ev_δ : ∀ᶠ η in 𝓝[>] (0 : ℝ), -t / (1 + η) ≠ 0 := by
    have hc : ContinuousAt (fun η : ℝ => -t / (1 + η)) 0 :=
      ContinuousAt.div (by fun_prop) (by fun_prop) (by norm_num : (1 : ℝ) + 0 ≠ 0)
    have hval : -t / ((1 : ℝ) + 0) ≠ 0 := by
      rw [add_zero, div_one]
      linarith [ht]
    exact (ContinuousAt.eventually_ne hc hval).filter_mono nhdsWithin_le_nhds
  have ev_inner_lt (v : ℝ³) (hv : ⟪v, x 0 - x 5⟫ < 0) : ∀ᶠ η in 𝓝[>] (0 : ℝ), ⟪v, u_X5 x η⟫ < 0 := by
    have hc : ContinuousAt (fun η : ℝ => ⟪v, u_X5 x η⟫) 0 :=
      ContinuousAt.inner continuousAt_const ev_u
    have hval : ⟪v, u_X5 x (0 : ℝ)⟫ < 0 := by
      have : u_X5 x 0 = x 0 - x 5 := by
        dsimp [u_X5]
        rw [zero_smul, add_zero]
      rw [this]
      exact hv
    exact (ContinuousAt.eventually_lt hc (continuousAt_const (x := 0)) hval).filter_mono nhdsWithin_le_nhds
  have ev_inner_gt (v : ℝ³) (hv : 0 < ⟪v, x 0 - x 5⟫) : ∀ᶠ η in 𝓝[>] (0 : ℝ), 0 < ⟪v, u_X5 x η⟫ := by
    have hc : ContinuousAt (fun η : ℝ => ⟪v, u_X5 x η⟫) 0 :=
      ContinuousAt.inner continuousAt_const ev_u
    have hval : 0 < ⟪v, u_X5 x (0 : ℝ)⟫ := by
      have : u_X5 x 0 = x 0 - x 5 := by
        dsimp [u_X5]
        rw [zero_smul, add_zero]
      rw [this]
      exact hv
    exact (ContinuousAt.eventually_lt (continuousAt_const (x := 0)) hc hval).filter_mono nhdsWithin_le_nhds
  have ev_inner_ne (v : ℝ³) (hv : ⟪v, x 0 - x 5⟫ ≠ 0) : ∀ᶠ η in 𝓝[>] (0 : ℝ), ⟪v, u_X5 x η⟫ ≠ 0 := by
    have hc : ContinuousAt (fun η : ℝ => ⟪v, u_X5 x η⟫) 0 :=
      ContinuousAt.inner continuousAt_const ev_u
    have hval : ⟪v, u_X5 x (0 : ℝ)⟫ ≠ 0 := by
      have : u_X5 x 0 = x 0 - x 5 := by
        dsimp [u_X5]
        rw [zero_smul, add_zero]
      rw [this]
      exact hv
    exact (ContinuousAt.eventually_ne hc hval).filter_mono nhdsWithin_le_nhds
  have h405 : ⟪x 4 - x 0, x 0 - x 5⟫ < 0 := by
    have : x 0 - x 5 = - (x 5 - x 0) := by
      ext j
      simp only [PiLp.sub_apply, PiLp.neg_apply]
      ring
    rw [this, inner_neg_right]
    linarith [hg45]

  have hN3_η (η : ℝ) : ⟪F.N 3, u_X5 x η⟫ = 0 := by
    dsimp [u_X5]
    rw [inner_add_right, real_inner_smul_right]
    have hz0 : ⟪F.N 3, x 0 - x 5⟫ = 0 := by
      have := (F.hN 3 (x 0) (x 5)).symm
      rw [F.zero 3 0 (by decide), F.zero 3 5 (by decide), sub_self] at this
      exact this
    have hz4 : ⟪F.N 3, x 4 - x 5⟫ = 0 := by
      have := (F.hN 3 (x 4) (x 5)).symm
      rw [F.zero 3 4 (by decide), F.zero 3 5 (by decide), sub_self] at this
      exact this
    rw [hz0, hz4, mul_zero, add_zero]

  have ev_N2 : ∀ᶠ η in 𝓝[>] (0 : ℝ), ⟪F.N 2, u_X5 x η⟫ < 0 := by
    filter_upwards [self_mem_nhdsWithin] with η hη
    dsimp [u_X5]
    rw [inner_add_right, real_inner_smul_right]
    have hz0 : ⟪F.N 2, x 0 - x 5⟫ = 0 := by
      have := (F.hN 2 (x 0) (x 5)).symm
      rw [F.zero 2 0 (by decide), F.zero 2 5 (by decide), sub_self] at this
      exact this
    rw [hz0, zero_add]
    have : η * ⟪F.N 2, x 4 - x 5⟫ < 0 := mul_neg_of_pos_of_neg hη hN2_slope
    exact this

  have ev_PA := ev_inner_lt (x 6 - x 4) hS2
  have ev_AB := ev_inner_lt (x 4 - x 0) h405
  have ev_QP := ev_inner_ne (x 2 - x 6) hS1.2.2
  have ev_QA := ev_inner_ne (x 2 - x 4) hS1.2.1
  have ev_QB := ev_inner_ne (x 2 - x 0) hS1.1

  have ev_N4 := ev_inner_gt (F.N 4) hN4
  have ev_N8 := ev_inner_lt (F.N 8) hN8
  have ev_N0 := ev_inner_gt (F.N 0) hN0
  have ev_N7 := ev_inner_lt (F.N 7) hN7
  have ev_N5 := ev_inner_gt (F.N 5) hN5

  have hall := ev_pos.and (ev_hη1.and (ev_s0.and (ev_s1.and (ev_δ.and (ev_PA.and (ev_AB.and (ev_QP.and (ev_QA.and (ev_QB.and (ev_N4.and (ev_N8.and (ev_N0.and (ev_N2.and (ev_N7.and ev_N5))))))))))))))
  obtain ⟨η, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, hN4_η, hN8_η, hN0_η, hN2_η, hN7_η, hN5_η⟩ := hall.exists

  have hPA_η : ⟪x 6, u_X5 x η⟫ < ⟪x 4, u_X5 x η⟫ := by
    have := inner_sub_left (𝕜 := ℝ) (x 6) (x 4) (u_X5 x η)
    linarith
  have hAB_η : ⟪x 4, u_X5 x η⟫ < ⟪x 0, u_X5 x η⟫ := by
    have := inner_sub_left (𝕜 := ℝ) (x 4) (x 0) (u_X5 x η)
    linarith
  have hQP_η : ⟪x 2, u_X5 x η⟫ ≠ ⟪x 6, u_X5 x η⟫ := by
    intro h
    apply h7
    rw [inner_sub_left (𝕜 := ℝ), h, sub_self]
  have hQA_η : ⟪x 2, u_X5 x η⟫ ≠ ⟪x 4, u_X5 x η⟫ := by
    intro h
    apply h8
    rw [inner_sub_left (𝕜 := ℝ), h, sub_self]
  have hQB_η : ⟪x 2, u_X5 x η⟫ ≠ ⟪x 0, u_X5 x η⟫ := by
    intro h
    apply h9
    rw [inner_sub_left (𝕜 := ℝ), h, sub_self]

  obtain ⟨ρ, hρ, hcyc, hI⟩ := lemmaX5_quad_signs F (hN3_η η) hN4_η hN8_η hN0_η hN2_η hN7_η hN5_η

  exact isRupert_of_X5_witness F s t hdecomp h0 h1 h2 h3 h4 hρ hcyc hI
    hPA_η hAB_η hQP_η hQA_η hQB_η hS3 hS4

/-- The perturbed view direction for Lemma X4 on facet `0345` (facet 3).
With chord edge `5 -> 0` and middle `4`, `u_X4 x η = (x 0 - x 4) + η • (x 5 - x 4)`. -/
def u_X4 (x : Fin 7 → ℝ³) (η : ℝ) : ℝ³ :=
  (x 0 - x 4) + η • (x 5 - x 4)

/-- Algebraic decomposition of vertex 3 as a chord middle over edge `0 -> 5`
along the perturbed view `u_X4 x η`. -/
theorem x3_middle_X4 (x : Fin 7 → ℝ³) (s t η : ℝ) (hη1 : 1 + η ≠ 0)
    (hdecomp : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0)) :
    x 3 = x 0 + (t + s * η / (1 + η)) • (x 5 - x 0) + (-s / (1 + η)) • u_X4 x η := by
  ext j
  have hd := congr_arg (fun (v : ℝ³) => v j) hdecomp
  simp only [u_X4, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at hd ⊢
  set A := t + s * η / (1 + η)
  set B := -s / (1 + η)
  have hA : A * (1 + η) = t * (1 + η) + s * η := by
    dsimp [A]
    rw [add_mul, div_mul_cancel₀ _ hη1]
  have hB : B * (1 + η) = -s := by
    dsimp [B]
    rw [div_mul_cancel₀ _ hη1]
  apply mul_right_cancel₀ hη1
  calc
    (x 3 j) * (1 + η) = (x 0 j + (s * (x 4 j - x 0 j) + t * (x 5 j - x 0 j))) * (1 + η) := by
      rw [show x 3 j = x 0 j + (x 3 j - x 0 j) by ring, hd]
    _ = (x 0 j + A * (x 5 j - x 0 j) + B * (x 0 j - x 4 j + η * (x 5 j - x 4 j))) * (1 + η) := by
      linear_combination - (x 5 j - x 0 j) * hA - (x 0 j - x 4 j + η * (x 5 j - x 4 j)) * hB

/-- Direct application of `isRupert_quadChord` for Lemma X4 at a specific parameter `η`
satisfying the open middle and depth inequalities. -/
theorem isRupert_of_X4_witness {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (s t : ℝ) (hdecomp : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0))
    {η : ℝ} (hη : 0 ≤ η) (hη1 : 1 + η ≠ 0)
    (ht₀ : 0 < t + s * η / (1 + η)) (ht₁ : t + s * η / (1 + η) < 1)
    (hδ : -s / (1 + η) ≠ 0)
    {ρ : ℝ} (hρ : ρ ≠ 0)
    (hcyc : ∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
      0 < ρ * det3 (quad (x 2) (x 5) (x 0) (x 6) (i + 1) - quad (x 2) (x 5) (x 0) (x 6) i)
        (quad (x 2) (x 5) (x 0) (x 6) j - quad (x 2) (x 5) (x 0) (x 6) i) (u_X4 x η))
    (hI : ∀ i : ZMod 4,
      0 < ρ * det3 (quad (x 2) (x 5) (x 0) (x 6) (i + 1) - quad (x 2) (x 5) (x 0) (x 6) i)
        (x 1 - quad (x 2) (x 5) (x 0) (x 6) i) (u_X4 x η))
    (hPA : ⟪x 2, u_X4 x η⟫ < ⟪x 5, u_X4 x η⟫)
    (hAB : ⟪x 5, u_X4 x η⟫ < ⟪x 0, u_X4 x η⟫)
    (hQP : ⟪x 6, u_X4 x η⟫ ≠ ⟪x 2, u_X4 x η⟫)
    (hQA : ⟪x 6, u_X4 x η⟫ ≠ ⟪x 5, u_X4 x η⟫)
    (hQB : ⟪x 6, u_X4 x η⟫ ≠ ⟪x 0, u_X4 x η⟫)
    (hS3 : 0 < det3 (x 0 - x 4) (x 5 - x 4) (x 6 - x 2) * det3 (x 0 - x 4) (x 5 - x 4) (x 1 - x 4))
    (hS4 : det3 (x 0 - x 4) (x 5 - x 4) (cross (x 0 - x 5) (x 6 - x 5)) ≠ 0 ∨
      ⟪x 6 - x 5, x 0 - x 5⟫ < 0 ∨ ⟪x 6 - x 0, x 5 - x 0⟫ < 0) :
    IsRupert (univ.image x) := by
  have hcov : ∀ j : Fin 7, j = 4 ∨ j = 3 ∨ j = 5 ∨ j = 0 ∨ j = 2 ∨ j = 6 ∨ j = 1 := by
    intro j; fin_cases j <;> decide
  have hlab : [(4 : Fin 7), 3, 5, 0, 2, 6].Nodup := by decide
  have hoS : (4 : Fin 7) ∈ s0x_S24 3 := by decide
  have hAS : (5 : Fin 7) ∈ s0x_S24 3 := by decide
  have hBS : (0 : Fin 7) ∈ s0x_S24 3 := by decide
  have hPS : (2 : Fin 7) ∉ s0x_S24 3 := by decide
  have hQS : (6 : Fin 7) ∉ s0x_S24 3 := by decide
  have hIS : (1 : Fin 7) ∉ s0x_S24 3 := by decide
  have hu : u_X4 x η = (x 0 - x 4) + η • (x 5 - x 4) := rfl
  have h3 := x3_middle_X4 x s t η hη1 hdecomp
  have hw : ((6 : Fin 7) = 6 ∧ (2 : Fin 7) = 2) ∨ ((6 : Fin 7) = 2 ∧ (2 : Fin 7) = 6) :=
    Or.inl ⟨rfl, rfl⟩
  exact isRupert_quadChord F hcov hlab hoS hAS hBS hPS hQS hIS hη hu hρ hcyc hI
    h3 ht₀ ht₁ hδ hPA hAB hQP hQA hQB hw hS3 hS4

/-- Strict convexity of rim `quad (x 2) (x 5) (x 0) (x 6)` and vertex 1 strictly inside
from the silhouette facet signs at view `u`.
Along ridge 62 between facet 7 (`236`) and facet 5 (`126`),
facet 7 is back (`hN7 < 0`) and facet 5 is front (`0 < hN5`). -/
theorem lemmaX4_quad_signs {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) {u : ℝ³}
    (hN3 : ⟪F.N 3, u⟫ = 0)
    (hN2 : 0 < ⟪F.N 2, u⟫) (hN6 : ⟪F.N 6, u⟫ < 0)
    (hN1 : 0 < ⟪F.N 1, u⟫) (hN4 : ⟪F.N 4, u⟫ < 0)
    (hN7 : ⟪F.N 7, u⟫ < 0) (hN5 : 0 < ⟪F.N 5, u⟫) :
    ∃ ρ : ℝ, ρ ≠ 0 ∧
      (∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
        0 < ρ * det3 (quad (x 2) (x 5) (x 0) (x 6) (i + 1) - quad (x 2) (x 5) (x 0) (x 6) i)
          (quad (x 2) (x 5) (x 0) (x 6) j - quad (x 2) (x 5) (x 0) (x 6) i) u) ∧
      (∀ i : ZMod 4,
        0 < ρ * det3 (quad (x 2) (x 5) (x 0) (x 6) (i + 1) - quad (x 2) (x 5) (x 0) (x 6) i)
          (x 1 - quad (x 2) (x 5) (x 0) (x 6) i) u) :=
  rim6052_of_signs F hN3 hN2 hN6 hN1 hN4 hN7 hN5

/-- **Lemma X4' (Q45X24.md / Q45THEOREM24.md): Mirror Corner Leaf at `e4 - ε e5` with genuine satisfiable facet signs.**
In the corner frame at vertex 1:
- `hN5 : 0 < ⟪F.N 5, x 0 - x 4⟫` iff `a4 > 1` (the true condition in the `a4, a5 > 1` regime).
- `hN7 : ⟪F.N 7, x 0 - x 4⟫ < 0` (facet 236 facing back).
- `hN6 : ⟪F.N 6, x 0 - x 4⟫ < 0` (facet 235 facing back). -/
theorem lemma_X4' {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (s t : ℝ) (hdecomp : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0))
    (hs : 0 < s) (ht0 : 0 < t) (ht : t < 1)
    (hg45 : 0 < ⟪x 4 - x 0, x 5 - x 0⟫)
    (hS1 : ⟪x 6 - x 0, x 0 - x 4⟫ ≠ 0 ∧ ⟪x 6 - x 5, x 0 - x 4⟫ ≠ 0 ∧ ⟪x 6 - x 2, x 0 - x 4⟫ ≠ 0)
    (hS2 : ⟪x 2 - x 5, x 0 - x 4⟫ < 0)
    (hS3 : 0 < det3 (x 0 - x 4) (x 5 - x 4) (x 6 - x 2) * det3 (x 0 - x 4) (x 5 - x 4) (x 1 - x 4))
    (hS4 : det3 (x 0 - x 4) (x 5 - x 4) (cross (x 0 - x 5) (x 6 - x 5)) ≠ 0 ∨
      ⟪x 6 - x 5, x 0 - x 5⟫ < 0 ∨ ⟪x 6 - x 0, x 5 - x 0⟫ < 0)
    (hN5 : 0 < ⟪F.N 5, x 0 - x 4⟫)
    (hN7 : ⟪F.N 7, x 0 - x 4⟫ < 0)
    (hN6 : ⟪F.N 6, x 0 - x 4⟫ < 0) :
    IsRupert (univ.image x) := by
  have hN1 : 0 < ⟪F.N 1, x 0 - x 4⟫ := by
    have := (F.hN 1 (x 0) (x 4)).symm
    rw [F.zero 1 0 (by decide)] at this
    linarith [F.neg 1 4 (by decide)]

  have hN2 : 0 < ⟪F.N 2, x 0 - x 4⟫ := by
    have := (F.hN 2 (x 0) (x 4)).symm
    rw [F.zero 2 0 (by decide)] at this
    linarith [F.neg 2 4 (by decide)]

  have hN4_slope : ⟪F.N 4, x 5 - x 4⟫ < 0 := by
    have := (F.hN 4 (x 5) (x 4)).symm
    rw [F.zero 4 4 (by decide)] at this
    linarith [F.neg 4 5 (by decide)]

  have ev_u : ContinuousAt (u_X4 x) 0 := by
    change ContinuousAt (fun η : ℝ => (x 0 - x 4) + η • (x 5 - x 4)) 0
    fun_prop
  have ev_pos : ∀ᶠ η in 𝓝[>] (0 : ℝ), 0 ≤ η :=
    eventually_mem_nhdsWithin.mono fun _ h => le_of_lt h
  have ev_hη1 : ∀ᶠ η in 𝓝[>] (0 : ℝ), 1 + η ≠ 0 := by
    have hc : ContinuousAt (fun η : ℝ => 1 + η) 0 := by fun_prop
    have hne : (1 : ℝ) + 0 ≠ 0 := by norm_num
    exact (ContinuousAt.eventually_ne hc hne).filter_mono nhdsWithin_le_nhds
  have ev_t0 : ∀ᶠ η in 𝓝[>] (0 : ℝ), 0 < t + s * η / (1 + η) := by
    have hc : ContinuousAt (fun η : ℝ => t + s * η / (1 + η)) 0 :=
      ContinuousAt.add continuousAt_const (ContinuousAt.div (by fun_prop) (by fun_prop) (by norm_num : (1 : ℝ) + 0 ≠ 0))
    have hval : 0 < t + s * (0 : ℝ) / (1 + 0) := by
      rw [mul_zero, zero_div, add_zero]
      exact ht0
    exact (ContinuousAt.eventually_lt (continuousAt_const (x := 0)) hc hval).filter_mono nhdsWithin_le_nhds
  have ev_t1 : ∀ᶠ η in 𝓝[>] (0 : ℝ), t + s * η / (1 + η) < 1 := by
    have hc : ContinuousAt (fun η : ℝ => t + s * η / (1 + η)) 0 :=
      ContinuousAt.add continuousAt_const (ContinuousAt.div (by fun_prop) (by fun_prop) (by norm_num : (1 : ℝ) + 0 ≠ 0))
    have hval : t + s * (0 : ℝ) / (1 + 0) < 1 := by
      rw [mul_zero, zero_div, add_zero]
      exact ht
    exact (ContinuousAt.eventually_lt hc (continuousAt_const (x := 0)) hval).filter_mono nhdsWithin_le_nhds
  have ev_δ : ∀ᶠ η in 𝓝[>] (0 : ℝ), -s / (1 + η) ≠ 0 := by
    have hc : ContinuousAt (fun η : ℝ => -s / (1 + η)) 0 :=
      ContinuousAt.div (by fun_prop) (by fun_prop) (by norm_num : (1 : ℝ) + 0 ≠ 0)
    have hval : -s / ((1 : ℝ) + 0) ≠ 0 := by
      rw [add_zero, div_one]
      linarith [hs]
    exact (ContinuousAt.eventually_ne hc hval).filter_mono nhdsWithin_le_nhds
  have ev_inner_lt (v : ℝ³) (hv : ⟪v, x 0 - x 4⟫ < 0) : ∀ᶠ η in 𝓝[>] (0 : ℝ), ⟪v, u_X4 x η⟫ < 0 := by
    have hc : ContinuousAt (fun η : ℝ => ⟪v, u_X4 x η⟫) 0 :=
      ContinuousAt.inner continuousAt_const ev_u
    have hval : ⟪v, u_X4 x (0 : ℝ)⟫ < 0 := by
      have : u_X4 x 0 = x 0 - x 4 := by
        dsimp [u_X4]
        rw [zero_smul, add_zero]
      rw [this]
      exact hv
    exact (ContinuousAt.eventually_lt hc (continuousAt_const (x := 0)) hval).filter_mono nhdsWithin_le_nhds
  have ev_inner_gt (v : ℝ³) (hv : 0 < ⟪v, x 0 - x 4⟫) : ∀ᶠ η in 𝓝[>] (0 : ℝ), 0 < ⟪v, u_X4 x η⟫ := by
    have hc : ContinuousAt (fun η : ℝ => ⟪v, u_X4 x η⟫) 0 :=
      ContinuousAt.inner continuousAt_const ev_u
    have hval : 0 < ⟪v, u_X4 x (0 : ℝ)⟫ := by
      have : u_X4 x 0 = x 0 - x 4 := by
        dsimp [u_X4]
        rw [zero_smul, add_zero]
      rw [this]
      exact hv
    exact (ContinuousAt.eventually_lt (continuousAt_const (x := 0)) hc hval).filter_mono nhdsWithin_le_nhds
  have ev_inner_ne (v : ℝ³) (hv : ⟪v, x 0 - x 4⟫ ≠ 0) : ∀ᶠ η in 𝓝[>] (0 : ℝ), ⟪v, u_X4 x η⟫ ≠ 0 := by
    have hc : ContinuousAt (fun η : ℝ => ⟪v, u_X4 x η⟫) 0 :=
      ContinuousAt.inner continuousAt_const ev_u
    have hval : ⟪v, u_X4 x (0 : ℝ)⟫ ≠ 0 := by
      have : u_X4 x 0 = x 0 - x 4 := by
        dsimp [u_X4]
        rw [zero_smul, add_zero]
      rw [this]
      exact hv
    exact (ContinuousAt.eventually_ne hc hval).filter_mono nhdsWithin_le_nhds
  have h504 : ⟪x 5 - x 0, x 0 - x 4⟫ < 0 := by
    have : x 0 - x 4 = - (x 4 - x 0) := by
      ext j
      simp only [PiLp.sub_apply, PiLp.neg_apply]
      ring
    rw [this, inner_neg_right]
    have : ⟪x 5 - x 0, x 4 - x 0⟫ = ⟪x 4 - x 0, x 5 - x 0⟫ := real_inner_comm _ _
    rw [this]
    linarith [hg45]

  have hN3_η (η : ℝ) : ⟪F.N 3, u_X4 x η⟫ = 0 := by
    dsimp [u_X4]
    rw [inner_add_right, real_inner_smul_right]
    have hz0 : ⟪F.N 3, x 0 - x 4⟫ = 0 := by
      have := (F.hN 3 (x 0) (x 4)).symm
      rw [F.zero 3 0 (by decide), F.zero 3 4 (by decide), sub_self] at this
      exact this
    have hz5 : ⟪F.N 3, x 5 - x 4⟫ = 0 := by
      have := (F.hN 3 (x 5) (x 4)).symm
      rw [F.zero 3 5 (by decide), F.zero 3 4 (by decide), sub_self] at this
      exact this
    rw [hz0, hz5, mul_zero, add_zero]

  have ev_N4 : ∀ᶠ η in 𝓝[>] (0 : ℝ), ⟪F.N 4, u_X4 x η⟫ < 0 := by
    filter_upwards [self_mem_nhdsWithin] with η hη
    dsimp [u_X4]
    rw [inner_add_right, real_inner_smul_right]
    have hz0 : ⟪F.N 4, x 0 - x 4⟫ = 0 := by
      have := (F.hN 4 (x 0) (x 4)).symm
      rw [F.zero 4 0 (by decide), F.zero 4 4 (by decide), sub_self] at this
      exact this
    rw [hz0, zero_add]
    have : η * ⟪F.N 4, x 5 - x 4⟫ < 0 := mul_neg_of_pos_of_neg hη hN4_slope
    exact this

  have ev_PA := ev_inner_lt (x 2 - x 5) hS2
  have ev_AB := ev_inner_lt (x 5 - x 0) h504
  have ev_QP := ev_inner_ne (x 6 - x 2) hS1.2.2
  have ev_QA := ev_inner_ne (x 6 - x 5) hS1.2.1
  have ev_QB := ev_inner_ne (x 6 - x 0) hS1.1

  have ev_N2 := ev_inner_gt (F.N 2) hN2
  have ev_N6 := ev_inner_lt (F.N 6) hN6
  have ev_N1 := ev_inner_gt (F.N 1) hN1
  have ev_N7 := ev_inner_lt (F.N 7) hN7
  have ev_N5 := ev_inner_gt (F.N 5) hN5

  have hall := ev_pos.and (ev_hη1.and (ev_t0.and (ev_t1.and (ev_δ.and (ev_PA.and (ev_AB.and (ev_QP.and (ev_QA.and (ev_QB.and (ev_N2.and (ev_N6.and (ev_N1.and (ev_N4.and (ev_N7.and ev_N5))))))))))))))
  obtain ⟨η, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, hN2_η, hN6_η, hN1_η, hN4_η, hN7_η, hN5_η⟩ := hall.exists

  have hPA_η : ⟪x 2, u_X4 x η⟫ < ⟪x 5, u_X4 x η⟫ := by
    have := inner_sub_left (𝕜 := ℝ) (x 2) (x 5) (u_X4 x η)
    linarith
  have hAB_η : ⟪x 5, u_X4 x η⟫ < ⟪x 0, u_X4 x η⟫ := by
    have := inner_sub_left (𝕜 := ℝ) (x 5) (x 0) (u_X4 x η)
    linarith
  have hQP_η : ⟪x 6, u_X4 x η⟫ ≠ ⟪x 2, u_X4 x η⟫ := by
    intro h
    apply h7
    rw [inner_sub_left (𝕜 := ℝ), h, sub_self]
  have hQA_η : ⟪x 6, u_X4 x η⟫ ≠ ⟪x 5, u_X4 x η⟫ := by
    intro h
    apply h8
    rw [inner_sub_left (𝕜 := ℝ), h, sub_self]
  have hQB_η : ⟪x 6, u_X4 x η⟫ ≠ ⟪x 0, u_X4 x η⟫ := by
    intro h
    apply h9
    rw [inner_sub_left (𝕜 := ℝ), h, sub_self]

  obtain ⟨ρ, hρ, hcyc, hI⟩ := lemmaX4_quad_signs F (hN3_η η) hN2_η hN6_η hN1_η hN4_η hN7_η hN5_η

  exact isRupert_of_X4_witness F s t hdecomp h0 h1 h2 h3 h4 hρ hcyc hI
    hPA_η hAB_η hQP_η hQA_η hQB_η hS3 hS4

end Minimality.T24.X5
