module

public import Mathlib
public import Minimality.DiagCross
public import Minimality.RimCell
public import Minimality.Slide
public import Minimality.UnimodalCert
public import Minimality.FaceChordFac
public import Minimality.Q45Signs
public import Minimality.Q45Orient
public import Minimality.CornerU
public import Minimality.Q45Leaf
public import Minimality.RimFromSigns

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped RealInnerProductSpace Topology
open Filter Finset
open Minimality Minimality.H21 Minimality.FaceChord Minimality.T24.SAT Minimality.T24.RimFromSigns

namespace Minimality.T24.Q45

/-- Rewrite lemma for rim 6452 (DiagCross kappa convention):
`κ(6, 4, 5, 2) = - det3 (x 5 - x 6) (x 2 - x 6) (x 4 - x 6)`.
The RHS is `kJ` in Q45THEOREM24. -/
theorem kappa_rim6452 (x : Fin 7 → ℝ³) :
    det3 (quad (x 6) (x 4) (x 5) (x 2) 2 - quad (x 6) (x 4) (x 5) (x 2) 0)
         (quad (x 6) (x 4) (x 5) (x 2) 3 - quad (x 6) (x 4) (x 5) (x 2) 1)
         (quad (x 6) (x 4) (x 5) (x 2) 0 - quad (x 6) (x 4) (x 5) (x 2) 1) =
      - det3 (x 5 - x 6) (x 2 - x 6) (x 4 - x 6) := by
  change det3 (x 5 - x 6) (x 2 - x 4) (x 6 - x 4) = - det3 (x 5 - x 6) (x 2 - x 6) (x 4 - x 6)
  simp only [det3_expand, PiLp.sub_apply]
  ring

/-- Helper for unimodality when 0 < ρ * κ (Lemma K rules out 2-high) and base condition rules out 6-high. -/
theorem unimodal_quad_Kplus (p : ZMod 4 → ℝ³) (u : ℝ³) (ρ : ℝ)
    (hinj : Function.Injective (fun i => ⟪p i, u⟫))
    (hcyc : ∀ i, 0 < ρ * triD p u i)
    (hk : 0 < ρ * det3 (p 2 - p 0) (p 3 - p 1) (p 0 - p 1))
    (h6lo : min ⟪p 0, u⟫ ⟪p 2, u⟫ < max ⟪p 1, u⟫ ⟪p 3, u⟫) :
    Minimality.StrictUnimodal (fun i => ⟪p i, u⟫) := by
  have hnot_low := diagCross_not_low p u hcyc hk
  have hmin_lt := min_lt_max_of_not_le hnot_low
  have hn := hn_of_min_lt_max (z := fun i => ⟪p i, u⟫) h6lo
  have hp := hp_of_min_lt_max (z := fun i => ⟪p i, u⟫) hmin_lt
  have hcyc_uni := Minimality.RimCell.isCyclicUnimodal_four (fun i => ⟪p i, u⟫) hinj hn hp
  exact Minimality.strictUnimodal_of_cyclic (by decide) hcyc_uni

/-- Helper for unimodality when ρ * κ < 0 (Lemma K rules out 6-high) and base condition rules out 2-high. -/
theorem unimodal_quad_Kminus (p : ZMod 4 → ℝ³) (u : ℝ³) (ρ : ℝ)
    (hinj : Function.Injective (fun i => ⟪p i, u⟫))
    (hcyc : ∀ i, 0 < ρ * triD p u i)
    (hk : ρ * det3 (p 2 - p 0) (p 3 - p 1) (p 0 - p 1) < 0)
    (h2lo : min ⟪p 1, u⟫ ⟪p 3, u⟫ < max ⟪p 0, u⟫ ⟪p 2, u⟫) :
    Minimality.StrictUnimodal (fun i => ⟪p i, u⟫) := by
  have hnot_high := diagCross_not_high p u hcyc hk
  have hmin_lt := min_lt_max_of_not_le hnot_high
  have hn := hn_of_min_lt_max (z := fun i => ⟪p i, u⟫) hmin_lt
  have hp := hp_of_min_lt_max (z := fun i => ⟪p i, u⟫) h2lo
  have hcyc_uni := Minimality.RimCell.isCyclicUnimodal_four (fun i => ⟪p i, u⟫) hinj hn hp
  exact Minimality.strictUnimodal_of_cyclic (by decide) hcyc_uni

/-- Helper for unimodality when κ = 0 (Lemma K rules out both strict alternations). -/
theorem unimodal_quad_K0 (p : ZMod 4 → ℝ³) (u : ℝ³) (ρ : ℝ)
    (hinj : Function.Injective (fun i => ⟪p i, u⟫))
    (hcyc : ∀ i, 0 < ρ * triD p u i)
    (hk : det3 (p 2 - p 0) (p 3 - p 1) (p 0 - p 1) = 0) :
    Minimality.StrictUnimodal (fun i => ⟪p i, u⟫) := by
  have hz := diagCross_zero p u hcyc hk
  have h_le1 : min ⟪p 0, u⟫ ⟪p 2, u⟫ ≤ max ⟪p 1, u⟫ ⟪p 3, u⟫ := not_lt.mp hz.1
  have h_le2 : min ⟪p 1, u⟫ ⟪p 3, u⟫ ≤ max ⟪p 0, u⟫ ⟪p 2, u⟫ := not_lt.mp hz.2
  have hneq : ∀ i j : ZMod 4, i ≠ j → ⟪p i, u⟫ ≠ ⟪p j, u⟫ := fun i j hij he => hij (hinj he)
  have h_lt1 : min ⟪p 0, u⟫ ⟪p 2, u⟫ < max ⟪p 1, u⟫ ⟪p 3, u⟫ := by
    rcases lt_or_eq_of_le h_le1 with hlt | heq
    · exact hlt
    · exfalso
      rcases min_choice ⟪p 0, u⟫ ⟪p 2, u⟫ with hm0 | hm2
      · rw [hm0] at heq
        rcases max_choice ⟪p 1, u⟫ ⟪p 3, u⟫ with hM1 | hM3
        · rw [hM1] at heq; exact hneq 0 1 (by decide) heq
        · rw [hM3] at heq; exact hneq 0 3 (by decide) heq
      · rw [hm2] at heq
        rcases max_choice ⟪p 1, u⟫ ⟪p 3, u⟫ with hM1 | hM3
        · rw [hM1] at heq; exact hneq 2 1 (by decide) heq
        · rw [hM3] at heq; exact hneq 2 3 (by decide) heq
  have h_lt2 : min ⟪p 1, u⟫ ⟪p 3, u⟫ < max ⟪p 0, u⟫ ⟪p 2, u⟫ := by
    rcases lt_or_eq_of_le h_le2 with hlt | heq
    · exact hlt
    · exfalso
      rcases min_choice ⟪p 1, u⟫ ⟪p 3, u⟫ with hm1 | hm3
      · rw [hm1] at heq
        rcases max_choice ⟪p 0, u⟫ ⟪p 2, u⟫ with hM0 | hM2
        · rw [hM0] at heq; exact hneq 1 0 (by decide) heq
        · rw [hM2] at heq; exact hneq 1 2 (by decide) heq
      · rw [hm3] at heq
        rcases max_choice ⟪p 0, u⟫ ⟪p 2, u⟫ with hM0 | hM2
        · rw [hM0] at heq; exact hneq 3 0 (by decide) heq
        · rw [hM2] at heq; exact hneq 3 2 (by decide) heq
  have hn := hn_of_min_lt_max (z := fun i => ⟪p i, u⟫) h_lt1
  have hp := hp_of_min_lt_max (z := fun i => ⟪p i, u⟫) h_lt2
  have hcyc_uni := Minimality.RimCell.isCyclicUnimodal_four (fun i => ⟪p i, u⟫) hinj hn hp
  exact Minimality.strictUnimodal_of_cyclic (by decide) hcyc_uni

/-- Signs on J0: for any α, β > 0 with α(1-s) + βt > 0, αs + β(1-t) > 0, and ⟪F.N 5, u⟫ < 0,
all seven silhouette signs required by `lemmaR_quad_signs` hold. -/
theorem lemma_signs_J0 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (s t α β : ℝ)
    (hs0 : 0 < s)
    (ht : 0 < t)
    (hst : 1 < s + t)
    (hdecomp : x 3 - x 0 = s • e4 x + t • e5 x)
    (hα : 0 < α)
    (hβ : 0 < β)
    (h8 : 0 < α * (1 - s) + β * t)
    (h6 : 0 < α * s + β * (1 - t))
    (hN5 : ⟪F.N 5, u_Pi x α β⟫ < 0) :
    ⟪F.N 3, u_Pi x α β⟫ = 0 ∧
    ⟪F.N 2, u_Pi x α β⟫ < 0 ∧
    ⟪F.N 4, u_Pi x α β⟫ < 0 ∧
    ⟪F.N 5, u_Pi x α β⟫ < 0 ∧
    0 < ⟪F.N 6, u_Pi x α β⟫ ∧
    0 < ⟪F.N 7, u_Pi x α β⟫ ∧
    0 < ⟪F.N 8, u_Pi x α β⟫ := by
  have h3 : ⟪F.N 3, u_Pi x α β⟫ = 0 := inner_N3_u_Pi F α β
  have h2 : ⟪F.N 2, u_Pi x α β⟫ < 0 := by
    rw [inner_N2_u_Pi F α β]
    exact mul_neg_of_pos_of_neg hβ (inner_N2_e4_neg F)
  have h4 : ⟪F.N 4, u_Pi x α β⟫ < 0 := by
    rw [inner_N4_u_Pi F α β]
    exact mul_neg_of_pos_of_neg hα (inner_N4_e5_neg F)
  have h6_pos : 0 < ⟪F.N 6, u_Pi x α β⟫ := by
    have hrel := inner_N6_u_Pi F s t α β hdecomp
    have hpos : 0 < (α * s + β * (1 - t)) * ⟪F.N 6, e5 x⟫ := mul_pos h6 (inner_N6_e5_pos F)
    rw [← hrel] at hpos
    exact pos_of_mul_pos_right hpos hs0.le
  have h8_pos : 0 < ⟪F.N 8, u_Pi x α β⟫ := by
    have hrel := inner_N8_u_Pi F s t α β hdecomp
    have hpos : 0 < (α * (1 - s) + β * t) * ⟪F.N 8, e4 x⟫ := mul_pos h8 (inner_N8_e4_pos F)
    rw [← hrel] at hpos
    exact pos_of_mul_pos_right hpos ht.le
  have h7_pos : 0 < ⟪F.N 7, u_Pi x α β⟫ := by
    have hrel := inner_N7_u_Pi F s t α β hdecomp
    have hterm1 : 0 < (α * (1 - s) + β * t) * ⟪F.N 7, e35 x⟫ := mul_pos h8 (inner_N7_e35_pos F)
    have hterm2 : 0 < (α * s + β * (1 - t)) * ⟪F.N 7, e34 x⟫ := mul_pos h6 (inner_N7_e34_pos F)
    have hsum : 0 < (α * (1 - s) + β * t) * ⟪F.N 7, e35 x⟫ + (α * s + β * (1 - t)) * ⟪F.N 7, e34 x⟫ :=
      add_pos hterm1 hterm2
    rw [← hrel] at hsum
    have hD : 0 < s + t - 1 := by linarith
    exact pos_of_mul_pos_right hsum hD.le
  exact ⟨h3, h2, h4, hN5, h6_pos, h7_pos, h8_pos⟩

/-- Middle vertex 0 decomposition on chord 4 -> 5 for any view in Pi. -/
theorem middle_quad_x0 (x : Fin 7 → ℝ³) (α β : ℝ) (hsum : α + β ≠ 0) :
    x 0 = x 4 + (α / (α + β)) • (x 5 - x 4) + (- (1 / (α + β))) • u_Pi x α β := by
  ext j
  dsimp [u_Pi, e4, e5]
  have : (x 0 j) = x 4 j + (α / (α + β)) * (x 5 j - x 4 j) + (- (1 / (α + β))) * (α * (x 5 j - x 0 j) + β * (x 4 j - x 0 j)) := by
    field_simp
    ring
  exact this

/-- Middle vertex 3 decomposition on chord 4 -> 5 for any view in Pi. -/
theorem middle_quad_x3 (x : Fin 7 → ℝ³) (s t α β : ℝ)
    (hdecomp : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0))
    (hsum : α + β ≠ 0) :
    x 3 = x 4 + (((1 - s) * α + t * β) / (α + β)) • (x 5 - x 4) + ((s + t - 1) / (α + β)) • u_Pi x α β := by
  ext j
  have hdj := congr_arg (fun (v : ℝ³) => v j) hdecomp
  dsimp [u_Pi, e4, e5] at hdj ⊢
  have : x 3 j = x 0 j + s * (x 4 j - x 0 j) + t * (x 5 j - x 0 j) := by
    linear_combination hdj
  rw [this]
  field_simp
  ring

/-- Middle coefficients bounds on J0. -/
theorem middle_bounds_J0 (s t α β : ℝ)
    (hst : 1 < s + t)
    (hα : 0 < α)
    (hβ : 0 < β)
    (h8 : 0 < α * (1 - s) + β * t)
    (h6 : 0 < α * s + β * (1 - t)) :
    (0 < α / (α + β) ∧ α / (α + β) < 1 ∧ - (1 / (α + β)) ≠ 0) ∧
    (0 < (((1 - s) * α + t * β) / (α + β)) ∧
     (((1 - s) * α + t * β) / (α + β)) < 1 ∧
     (s + t - 1) / (α + β) ≠ 0) := by
  have hab : 0 < α + β := add_pos hα hβ
  have hs0_pos : 0 < α / (α + β) := div_pos hα hab
  have hs0_lt1 : α / (α + β) < 1 := (div_lt_one hab).mpr (lt_add_of_pos_right α hβ)
  have hd0_ne : - (1 / (α + β)) ≠ 0 := by
    have : 0 < 1 / (α + β) := one_div_pos.mpr hab
    linarith
  have h8' : 0 < (1 - s) * α + t * β := by linarith [h8]
  have hs3_pos : 0 < ((1 - s) * α + t * β) / (α + β) := div_pos h8' hab
  have hs3_lt1 : ((1 - s) * α + t * β) / (α + β) < 1 := by
    rw [div_lt_one hab]
    linarith [h6]
  have hd3_ne : (s + t - 1) / (α + β) ≠ 0 := by
    have hnum : 0 < s + t - 1 := by linarith
    have : 0 < (s + t - 1) / (α + β) := div_pos hnum hab
    linarith
  exact ⟨⟨hs0_pos, hs0_lt1, hd0_ne⟩, ⟨hs3_pos, hs3_lt1, hd3_ne⟩⟩

lemma middle_vertices_J0 (q : Fin 7) (hqS : q ∈ s0x_S24 3)
    (hqr : ∀ j : ZMod 4, q ≠ quad 6 4 5 2 j) :
    q = 0 ∨ q = 3 := by
  revert q
  decide

lemma exterior_vertices_J0 (q : Fin 7) (hqS : q ∉ s0x_S24 3)
    (hqr : ∀ j : ZMod 4, q ≠ quad 6 4 5 2 j) :
    q = 1 := by
  revert q
  decide

lemma w_candidates_J0 (m : ZMod 4) (hmS : quad 6 4 5 2 m ∉ s0x_S24 3) :
    m = 0 ∨ m = 3 := by
  revert m
  decide

/-- **Leaf K0 (kJ = 0, Planar Rim 6452)**:
When `kJ = -det3 (x 5 - x 6) (x 2 - x 6) (x 4 - x 6) = 0`, the DiagCross orientation
`κ(6, 4, 5, 2)` vanishes identically. By `diagCross_zero`, neither strict alternation
can occur at any view on `J0`. With distinct rim depths, the quad is strictly unimodal.
- View: interior view along open arc `J0`.
- Rim: 6 4 5 2 (ridges 4-6, 5-2, 2-6, edge-on chord 4-5).
- Chord: 4 -> 5. Middles: 0, 3. Farther: w ∈ {2, 6}.
- Hypotheses:
  * `ha4`, `ha5`: corner-frame coordinate conditions `a4 > 1` and `a5 > 1`.
  * `hs0`, `ht`, `hst`, `hdecomp`: Lemma M decomposition of vertex 3 on facet 3.
  * `hk0`: case condition `kJ = 0`, i.e. `det3 (x 5 - x 6) (x 2 - x 6) (x 4 - x 6) = 0`.
  * `hS2`: persistent tie exclusion (rim depths do not vanish identically on Pi).
  * `hS3`: farther vertex tie exclusion (`F.f 3 (x 2) ≠ F.f 3 (x 6)`).
  * `hS4`: chord 4-5 exclusion (foot of farther vertex off open segment (4, 5)). -/
theorem q45_K0 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (ha4 : ⟪F.N 5, x 4 - x 0⟫ < 0)
    (ha5 : ⟪F.N 5, x 5 - x 0⟫ < 0)
    (s t : ℝ)
    (hs0 : 0 < s)
    (ht : 0 < t)
    (hst : 1 < s + t)
    (hdecomp : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0))
    (hk0 : det3 (x 5 - x 6) (x 2 - x 6) (x 4 - x 6) = 0)
    (hS2 : ∀ i j : ZMod 4, i ≠ j →
      ⟪quad (x 6) (x 4) (x 5) (x 2) i - quad (x 6) (x 4) (x 5) (x 2) j, x 5 - x 0⟫ ≠ 0 ∨
      ⟪quad (x 6) (x 4) (x 5) (x 2) i - quad (x 6) (x 4) (x 5) (x 2) j, x 4 - x 0⟫ ≠ 0)
    (hS3 : F.f 3 (x 2) ≠ F.f 3 (x 6))
    (hS4 : ⟪F.N 3, cross (x 5 - x 4) (x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 4)⟫ ≠ 0 ∨
           ⟪x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 4, x 5 - x 4⟫ < 0 ∨
           ⟪x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 5, x 4 - x 5⟫ < 0) :
    FaceChordView F 3 := by
  set p_quad := quad (x 6) (x 4) (x 5) (x 2)
  set r : ZMod 4 → Fin 7 := quad 6 4 5 2
  have hr : ∀ i : ZMod 4, x (r i) = p_quad i := by
    intro i; fin_cases i <;> rfl
  set b := t • (x 5 - x 0) + s • (x 4 - x 0)
  set d := x 4 - x 0
  have hu_Pi : ∀ ε : ℝ, b + ε • d = u_Pi x t (s + ε) := by
    intro ε; ext j; simp [b, d, u_Pi, e4, e5]; ring
  have ev_eps : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  have ev_beta : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < s + ε := by
    have := eventually_pos_affine (A := s) (B := 1) (Or.inl hs0)
    filter_upwards [this] with ε hε; linarith
  have ev_8 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < t * (1 - s) + (s + ε) * t := by
    have : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < t + ε * t :=
      eventually_pos_affine (A := t) (B := t) (Or.inl ht)
    filter_upwards [this] with ε hε; linarith
  have ev_6 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < t * s + (s + ε) * (1 - t) := by
    have : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < s + ε * (1 - t) :=
      eventually_pos_affine (A := s) (B := 1 - t) (Or.inl hs0)
    filter_upwards [this] with ε hε; linarith
  have ev_N5 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ⟪F.N 5, b + ε • d⟫ < 0 := by
    have hlin : ∀ ε : ℝ, ⟪F.N 5, b + ε • d⟫ = ⟪F.N 5, b⟫ + ε * ⟪F.N 5, d⟫ := by
      intro ε; rw [inner_add_right, real_inner_smul_right]
    have hN5_b : ⟪F.N 5, b⟫ < 0 := by
      dsimp [b]
      rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
      have h1 : t * ⟪F.N 5, x 5 - x 0⟫ < 0 := mul_neg_of_pos_of_neg ht ha5
      have h2 : s * ⟪F.N 5, x 4 - x 0⟫ < 0 := mul_neg_of_pos_of_neg hs0 ha4
      linarith
    have hpos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < - ⟪F.N 5, b⟫ + ε * (- ⟪F.N 5, d⟫) :=
      eventually_pos_affine (A := - ⟪F.N 5, b⟫) (B := - ⟪F.N 5, d⟫) (Or.inl (by linarith [hN5_b]))
    filter_upwards [hpos] with ε hε; rw [hlin]; linarith
  have hgen : ∀ i j : ZMod 4, i ≠ j → ⟪p_quad i - p_quad j, b⟫ ≠ 0 ∨ ⟪p_quad i - p_quad j, d⟫ ≠ 0 := by
    intro i j hij
    have hs2 := hS2 i j hij
    by_cases hd0 : ⟪p_quad i - p_quad j, d⟫ = 0
    · left
      have h5 : ⟪p_quad i - p_quad j, x 5 - x 0⟫ ≠ 0 := by
        rcases hs2 with h5 | h4
        · exact h5
        · exact False.elim (h4 hd0)
      intro hb0
      have hb_expand : ⟪p_quad i - p_quad j, b⟫ =
          t * ⟪p_quad i - p_quad j, x 5 - x 0⟫ + s * ⟪p_quad i - p_quad j, d⟫ := by
        dsimp [b, d]
        rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
      rw [hd0, mul_zero, add_zero] at hb_expand
      rw [hb0] at hb_expand
      have : t * ⟪p_quad i - p_quad j, x 5 - x 0⟫ = 0 := hb_expand.symm
      rcases mul_eq_zero.mp this with ht0 | h50
      · linarith [ht]
      · exact h5 h50
    · right; exact hd0
  have ev_inj := eventually_injective_quad p_quad b d hgen
  have ev_all := ev_eps.and (ev_beta.and (ev_8.and (ev_6.and (ev_N5.and ev_inj))))
  obtain ⟨ε, hε, hβ, h8, h6, hN5_u, hinj_u⟩ := ev_all.exists
  set u := b + ε • d
  have hu_Pi_eq : u = u_Pi x t (s + ε) := hu_Pi ε
  have hN5_Pi : ⟪F.N 5, u_Pi x t (s + ε)⟫ < 0 := by rw [← hu_Pi_eq]; exact hN5_u
  have hsigns := lemma_signs_J0 F s t t (s + ε) hs0 ht hst hdecomp ht hβ h8 h6 hN5_Pi
  rw [← hu_Pi_eq] at hsigns
  have hN3 : ⟪F.N 3, u⟫ = 0 := hsigns.1
  have hN2 : ⟪F.N 2, u⟫ < 0 := hsigns.2.1
  have hN4 : ⟪F.N 4, u⟫ < 0 := hsigns.2.2.1
  have hN5 : ⟪F.N 5, u⟫ < 0 := hsigns.2.2.2.1
  have hN6 : 0 < ⟪F.N 6, u⟫ := hsigns.2.2.2.2.1
  have hN7 : 0 < ⟪F.N 7, u⟫ := hsigns.2.2.2.2.2.1
  have hN8 : 0 < ⟪F.N 8, u⟫ := hsigns.2.2.2.2.2.2
  obtain ⟨ρ, hρ_ne, hcyc, hin⟩ := lemmaR_quad_signs F hN3 hN2 hN4 hN5 hN6 hN7 hN8
  have h_triD (i : ZMod 4) : 0 < ρ * triD p_quad u i := by
    have hneq1 : (i + 2 : ZMod 4) ≠ i := by
      intro h
      have : (2 : ZMod 4) = 0 := by
        calc (2 : ZMod 4) = (i + 2) - i := by ring
        _ = i - i := by rw [h]
        _ = 0 := sub_self i
      revert this; decide
    have hneq2 : (i + 2 : ZMod 4) ≠ i + 1 := by
      intro h
      have : (1 : ZMod 4) = 0 := by
        calc (1 : ZMod 4) = (i + 2) - (i + 1) := by ring
        _ = (i + 1) - (i + 1) := by rw [h]
        _ = 0 := sub_self _
      revert this; decide
    exact hcyc i (i + 2) hneq1 hneq2
  have hk0_quad : det3 (p_quad 2 - p_quad 0) (p_quad 3 - p_quad 1) (p_quad 0 - p_quad 1) = 0 := by
    dsimp [p_quad]
    rw [kappa_rim6452 x, hk0, neg_zero]
  have h_uni := unimodal_quad_K0 p_quad u ρ hinj_u h_triD hk0_quad
  have h_mb := middle_bounds_J0 s t t (s + ε) hst ht hβ h8 h6
  set a : ZMod 4 := 1
  set w : ZMod 4 := if F.f 3 (x 2) < F.f 3 (x 6) then 3 else 0
  refine ⟨u, 4, inferInstance, r, a, w, ρ, hN3, by decide, ?_, ?_, hρ_ne, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show r 1 ∈ s0x_S24 3
    decide
  · show r (1 + 1) ∈ s0x_S24 3
    decide
  · intro i j hj1 hj2
    simp_rw [hr]
    exact hcyc i j hj1 hj2
  · intro q hqS hqr i
    have hq1 := exterior_vertices_J0 q hqS hqr
    subst hq1
    simp_rw [hr]
    exact hin i
  · intro q hqS hqr
    have hq03 := middle_vertices_J0 q hqS hqr
    have hra : x (r a) = x 4 := rfl
    have hra1 : x (r (a + 1)) = x 5 := rfl
    rw [hra, hra1]
    rcases hq03 with rfl | rfl
    · refine ⟨t / (t + (s + ε)), - (1 / (t + (s + ε))), h_mb.1.1, h_mb.1.2.1, h_mb.1.2.2, ?_⟩
      rw [hu_Pi_eq]
      exact middle_quad_x0 x t (s + ε) (by linarith [ht, hβ])
    · refine ⟨((1 - s) * t + t * (s + ε)) / (t + (s + ε)), (s + t - 1) / (t + (s + ε)), h_mb.2.1, h_mb.2.2.1, h_mb.2.2.2, ?_⟩
      rw [hu_Pi_eq]
      exact middle_quad_x3 x s t t (s + ε) hdecomp (by linarith [ht, hβ])
  · simp_rw [hr]
    exact hinj_u
  · simp_rw [hr]
    exact Or.inl h_uni
  · dsimp [w, r, quad]
    split_ifs <;> decide
  · intro m hmw hmS
    dsimp [w] at hmw ⊢
    split_ifs at hmw ⊢ with h26
    · have hcand := w_candidates_J0 m hmS
      rcases hcand with rfl | rfl
      · show F.f 3 (x 2) < F.f 3 (x 6); exact h26
      · exact False.elim (hmw rfl)
    · have hcand := w_candidates_J0 m hmS
      rcases hcand with rfl | rfl
      · exact False.elim (hmw rfl)
      · show F.f 3 (x 6) < F.f 3 (x 2)
        have : F.f 3 (x 2) ≠ F.f 3 (x 6) := hS3
        exact lt_of_le_of_ne (not_lt.mp h26) this.symm
  · have hra : x (r a) = x 4 := rfl
    have hra1 : x (r (a + 1)) = x 5 := rfl
    rw [hra, hra1]
    dsimp [w]
    split_ifs with h26
    · have hrw : r 3 = 2 := rfl
      rw [hrw]
      have hs4' := hS4
      split_ifs at hs4'
      exact hs4'
    · have hrw : r 0 = 6 := rfl
      rw [hrw]
      have hs4' := hS4
      split_ifs at hs4'
      exact hs4'

/-- **Leaf K+ (Subcase s ≤ 1, E5 = e5)**:
When `ρ0 * kJ > 0` and weak 6-high fails strictly at base `e5 = x 5 - x 0`.
- Views: `u_ε = e5 + ε • e4` in `J0` for small `ε > 0`.
- Rim: 6 4 5 2, chord 4 -> 5, middles 0, 3, farther w ∈ {2, 6}.
- Lemma K rules out 2-high everywhere on `J0`.
- Open condition `h6lo` rules out 6-high near `e5`. -/
theorem q45_Kplus_s_le_one {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (ha5 : ⟪F.N 5, x 5 - x 0⟫ < 0)
    (s t : ℝ)
    (hs0 : 0 < s)
    (ht : 0 < t)
    (hst : 1 < s + t)
    (hdecomp : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0))
    (hk : det3 (x 5 - x 6) (x 2 - x 6) (x 4 - x 6) * det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) < 0)
    (hs : s ≤ 1)
    (h6lo : min ⟪x 6, x 5 - x 0⟫ ⟪x 5, x 5 - x 0⟫ < max ⟪x 4, x 5 - x 0⟫ ⟪x 2, x 5 - x 0⟫)
    (hS2 : ∀ i j : ZMod 4, i ≠ j →
      ⟪quad (x 6) (x 4) (x 5) (x 2) i - quad (x 6) (x 4) (x 5) (x 2) j, x 5 - x 0⟫ ≠ 0 ∨
      ⟪quad (x 6) (x 4) (x 5) (x 2) i - quad (x 6) (x 4) (x 5) (x 2) j, x 4 - x 0⟫ ≠ 0)
    (hS3 : F.f 3 (x 2) ≠ F.f 3 (x 6))
    (hS4 : ⟪F.N 3, cross (x 5 - x 4) (x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 4)⟫ ≠ 0 ∨
           ⟪x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 4, x 5 - x 4⟫ < 0 ∨
           ⟪x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 5, x 4 - x 5⟫ < 0) :
    FaceChordView F 3 := by
  set p_quad := quad (x 6) (x 4) (x 5) (x 2)
  set r : ZMod 4 → Fin 7 := quad 6 4 5 2
  have hr : ∀ i : ZMod 4, x (r i) = p_quad i := by
    intro i; fin_cases i <;> rfl
  set b := x 5 - x 0
  set d := x 4 - x 0
  have hu_Pi : ∀ ε : ℝ, b + ε • d = u_Pi x 1 ε := by
    intro ε; ext j; simp [b, d, u_Pi, e4, e5]
  have ev_eps : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  have ev_6 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < 1 * s + ε * (1 - t) := by
    have : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < s + ε * (1 - t) :=
      eventually_pos_affine (A := s) (B := 1 - t) (Or.inl hs0)
    filter_upwards [this] with ε hε
    linarith
  have ev_N5 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ⟪F.N 5, b + ε • d⟫ < 0 := by
    have hlin : ∀ ε : ℝ, ⟪F.N 5, b + ε • d⟫ = ⟪F.N 5, b⟫ + ε * ⟪F.N 5, d⟫ := by
      intro ε; rw [inner_add_right, real_inner_smul_right]
    have hpos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < - ⟪F.N 5, b⟫ + ε * (- ⟪F.N 5, d⟫) :=
      eventually_pos_affine (A := - ⟪F.N 5, b⟫) (B := - ⟪F.N 5, d⟫) (Or.inl (by linarith [ha5]))
    filter_upwards [hpos] with ε hε
    rw [hlin]; linarith
  have ev_6lo : ∀ᶠ ε in 𝓝[>] (0 : ℝ), min ⟪p_quad 0, b + ε • d⟫ ⟪p_quad 2, b + ε • d⟫ < max ⟪p_quad 1, b + ε • d⟫ ⟪p_quad 3, b + ε • d⟫ :=
    eventually_min02_lt_max13 p_quad b d h6lo
  have ev_inj : ∀ᶠ ε in 𝓝[>] (0 : ℝ), Function.Injective (fun i => ⟪p_quad i, b + ε • d⟫) :=
    eventually_injective_quad p_quad b d hS2
  have ev_all := ev_eps.and (ev_6.and (ev_N5.and (ev_6lo.and ev_inj)))
  obtain ⟨ε, hε, h6, hN5_u, h6lo_u, hinj_u⟩ := ev_all.exists
  set u := b + ε • d
  have hu_Pi_eq : u = u_Pi x 1 ε := hu_Pi ε
  have h8 : 0 < 1 * (1 - s) + ε * t := by nlinarith [hs, ht, hε]
  have hN5_Pi : ⟪F.N 5, u_Pi x 1 ε⟫ < 0 := by rw [← hu_Pi_eq]; exact hN5_u
  have hsigns := lemma_signs_J0 F s t 1 ε hs0 ht hst hdecomp one_pos hε h8 h6 hN5_Pi
  rw [← hu_Pi_eq] at hsigns
  have hN3 : ⟪F.N 3, u⟫ = 0 := hsigns.1
  have hN2 : ⟪F.N 2, u⟫ < 0 := hsigns.2.1
  have hN4 : ⟪F.N 4, u⟫ < 0 := hsigns.2.2.1
  have hN5 : ⟪F.N 5, u⟫ < 0 := hsigns.2.2.2.1
  have hN6 : 0 < ⟪F.N 6, u⟫ := hsigns.2.2.2.2.1
  have hN7 : 0 < ⟪F.N 7, u⟫ := hsigns.2.2.2.2.2.1
  have hN8 : 0 < ⟪F.N 8, u⟫ := hsigns.2.2.2.2.2.2
  obtain ⟨ρ, hρ_ne, hcyc, hin⟩ := lemmaR_quad_signs F hN3 hN2 hN4 hN5 hN6 hN7 hN8
  have hin3 := hin 3
  have h3_eq : quad (x 6) (x 4) (x 5) (x 2) (3 + 1) - quad (x 6) (x 4) (x 5) (x 2) 3 = x 6 - x 2 := by
    show quad (x 6) (x 4) (x 5) (x 2) 0 - quad (x 6) (x 4) (x 5) (x 2) 3 = x 6 - x 2
    rfl
  have h3_1 : x 1 - quad (x 6) (x 4) (x 5) (x 2) 3 = x 1 - x 2 := by
    show x 1 - quad (x 6) (x 4) (x 5) (x 2) 3 = x 1 - x 2
    rfl
  rw [h3_eq, h3_1] at hin3
  have h_rho_om := rho_mul_omega_pos_of_inner_neg F u ρ hin3 hN5
  set Ω := det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1)
  have h_om_ne := omega_ne_zero F
  have h_om_sq : 0 < Ω ^ 2 := sq_pos_of_ne_zero h_om_ne
  have hkap := kappa_rim6452 x
  have h_om_kap : 0 < Ω * det3 (p_quad 2 - p_quad 0) (p_quad 3 - p_quad 1) (p_quad 0 - p_quad 1) := by
    dsimp [p_quad]
    rw [hkap]
    linarith [hk]
  have hk_pos : 0 < ρ * det3 (p_quad 2 - p_quad 0) (p_quad 3 - p_quad 1) (p_quad 0 - p_quad 1) := by
    have hprod : 0 < (ρ * Ω) * (Ω * det3 (p_quad 2 - p_quad 0) (p_quad 3 - p_quad 1) (p_quad 0 - p_quad 1)) :=
      mul_pos h_rho_om h_om_kap
    have : (ρ * Ω) * (Ω * det3 (p_quad 2 - p_quad 0) (p_quad 3 - p_quad 1) (p_quad 0 - p_quad 1)) =
        Ω ^ 2 * (ρ * det3 (p_quad 2 - p_quad 0) (p_quad 3 - p_quad 1) (p_quad 0 - p_quad 1)) := by ring
    rw [this] at hprod
    exact pos_of_mul_pos_right hprod h_om_sq.le
  have h_triD (i : ZMod 4) : 0 < ρ * triD p_quad u i := by
    have hneq1 : (i + 2 : ZMod 4) ≠ i := by
      intro h
      have : (2 : ZMod 4) = 0 := by
        calc (2 : ZMod 4) = (i + 2) - i := by ring
        _ = i - i := by rw [h]
        _ = 0 := sub_self i
      revert this; decide
    have hneq2 : (i + 2 : ZMod 4) ≠ i + 1 := by
      intro h
      have : (1 : ZMod 4) = 0 := by
        calc (1 : ZMod 4) = (i + 2) - (i + 1) := by ring
        _ = (i + 1) - (i + 1) := by rw [h]
        _ = 0 := sub_self _
      revert this; decide
    exact hcyc i (i + 2) hneq1 hneq2
  have h_uni := unimodal_quad_Kplus p_quad u ρ hinj_u h_triD hk_pos h6lo_u
  have h_mb := middle_bounds_J0 s t 1 ε hst one_pos hε h8 h6
  set a : ZMod 4 := 1
  set w : ZMod 4 := if F.f 3 (x 2) < F.f 3 (x 6) then 3 else 0
  refine ⟨u, 4, inferInstance, r, a, w, ρ, hN3, by decide, ?_, ?_, hρ_ne, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show r 1 ∈ s0x_S24 3
    decide
  · show r (1 + 1) ∈ s0x_S24 3
    decide
  · intro i j hj1 hj2
    simp_rw [hr]
    exact hcyc i j hj1 hj2
  · intro q hqS hqr i
    have hq1 := exterior_vertices_J0 q hqS hqr
    subst hq1
    simp_rw [hr]
    exact hin i
  · intro q hqS hqr
    have hq03 := middle_vertices_J0 q hqS hqr
    have hra : x (r a) = x 4 := rfl
    have hra1 : x (r (a + 1)) = x 5 := rfl
    rw [hra, hra1]
    rcases hq03 with rfl | rfl
    · refine ⟨1 / (1 + ε), - (1 / (1 + ε)), h_mb.1.1, h_mb.1.2.1, h_mb.1.2.2, ?_⟩
      rw [hu_Pi_eq]
      exact middle_quad_x0 x 1 ε (by linarith [hε])
    · refine ⟨((1 - s) * 1 + t * ε) / (1 + ε), (s + t - 1) / (1 + ε), h_mb.2.1, h_mb.2.2.1, h_mb.2.2.2, ?_⟩
      rw [hu_Pi_eq]
      exact middle_quad_x3 x s t 1 ε hdecomp (by linarith [hε])
  · simp_rw [hr]
    exact hinj_u
  · simp_rw [hr]
    exact Or.inl h_uni
  · dsimp [w, r, quad]
    split_ifs <;> decide
  · intro m hmw hmS
    dsimp [w] at hmw ⊢
    split_ifs at hmw ⊢ with h26
    · have hcand := w_candidates_J0 m hmS
      rcases hcand with rfl | rfl
      · show F.f 3 (x 2) < F.f 3 (x 6); exact h26
      · exact False.elim (hmw rfl)
    · have hcand := w_candidates_J0 m hmS
      rcases hcand with rfl | rfl
      · exact False.elim (hmw rfl)
      · show F.f 3 (x 6) < F.f 3 (x 2)
        have : F.f 3 (x 2) ≠ F.f 3 (x 6) := hS3
        exact lt_of_le_of_ne (not_lt.mp h26) this.symm
  · have hra : x (r a) = x 4 := rfl
    have hra1 : x (r (a + 1)) = x 5 := rfl
    rw [hra, hra1]
    dsimp [w]
    split_ifs with h26
    · have hrw : r 3 = 2 := rfl
      rw [hrw]
      have hs4' := hS4
      split_ifs at hs4'
      exact hs4'
    · have hrw : r 0 = 6 := rfl
      rw [hrw]
      have hs4' := hS4
      split_ifs at hs4'
      exact hs4'

/-- **Leaf K+ (Subcase 1 < s, E5 = e34)**:
When `ρ0 * kJ > 0` and weak 6-high fails strictly at base `e34 = x 3 - x 4`.
- Views: `u_ε = (x 3 - x 4) + ε • (x 4 - x 0)` in `J0` for small `ε > 0`.
- Rim: 6 4 5 2, chord 4 -> 5, middles 0, 3, farther w ∈ {2, 6}.
- Lemma K rules out 2-high everywhere on `J0`.
- Open condition `h6lo` rules out 6-high near `e34`. -/
theorem q45_Kplus_s_gt_one {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (ha34 : ⟪F.N 5, x 3 - x 4⟫ < 0)
    (s t : ℝ)
    (hs0 : 0 < s)
    (ht : 0 < t)
    (hst : 1 < s + t)
    (hdecomp : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0))
    (hk : det3 (x 5 - x 6) (x 2 - x 6) (x 4 - x 6) * det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) < 0)
    (hs : 1 < s)
    (h6lo : min ⟪x 6, x 3 - x 4⟫ ⟪x 5, x 3 - x 4⟫ < max ⟪x 4, x 3 - x 4⟫ ⟪x 2, x 3 - x 4⟫)
    (hS2 : ∀ i j : ZMod 4, i ≠ j →
      ⟪quad (x 6) (x 4) (x 5) (x 2) i - quad (x 6) (x 4) (x 5) (x 2) j, x 3 - x 4⟫ ≠ 0 ∨
      ⟪quad (x 6) (x 4) (x 5) (x 2) i - quad (x 6) (x 4) (x 5) (x 2) j, x 4 - x 0⟫ ≠ 0)
    (hS3 : F.f 3 (x 2) ≠ F.f 3 (x 6))
    (hS4 : ⟪F.N 3, cross (x 5 - x 4) (x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 4)⟫ ≠ 0 ∨
           ⟪x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 4, x 5 - x 4⟫ < 0 ∨
           ⟪x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 5, x 4 - x 5⟫ < 0) :
    FaceChordView F 3 := by
  set p_quad := quad (x 6) (x 4) (x 5) (x 2)
  set r : ZMod 4 → Fin 7 := quad 6 4 5 2
  have hr : ∀ i : ZMod 4, x (r i) = p_quad i := by
    intro i; fin_cases i <;> rfl
  set b := x 3 - x 4
  set d := x 4 - x 0
  have hu_Pi : ∀ ε : ℝ, b + ε • d = u_Pi x t (s - 1 + ε) := by
    intro ε; ext j
    have hdj := congr_arg (fun (v : ℝ³) => v j) hdecomp
    dsimp [b, d, u_Pi, e4, e5, e34] at hdj ⊢
    linear_combination hdj
  have ev_eps : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  have ev_beta : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < s - 1 + ε := by
    have := eventually_pos_affine (A := s - 1) (B := 1) (Or.inl (by linarith [hs]))
    filter_upwards [this] with ε hε; linarith
  have ev_6 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < t * s + (s - 1 + ε) * (1 - t) := by
    have hA : 0 < t * s + (s - 1) * (1 - t) := by linarith [hst]
    have := eventually_pos_affine (A := t * s + (s - 1) * (1 - t)) (B := 1 - t) (Or.inl hA)
    filter_upwards [this] with ε hε
    have : t * s + (s - 1 + ε) * (1 - t) = t * s + (s - 1) * (1 - t) + ε * (1 - t) := by ring
    rw [this]; exact hε
  have ev_N5 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ⟪F.N 5, b + ε • d⟫ < 0 := by
    have hlin : ∀ ε : ℝ, ⟪F.N 5, b + ε • d⟫ = ⟪F.N 5, b⟫ + ε * ⟪F.N 5, d⟫ := by
      intro ε; rw [inner_add_right, real_inner_smul_right]
    have hpos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < - ⟪F.N 5, b⟫ + ε * (- ⟪F.N 5, d⟫) :=
      eventually_pos_affine (A := - ⟪F.N 5, b⟫) (B := - ⟪F.N 5, d⟫) (Or.inl (by linarith [ha34]))
    filter_upwards [hpos] with ε hε
    rw [hlin]; linarith
  have ev_6lo : ∀ᶠ ε in 𝓝[>] (0 : ℝ), min ⟪p_quad 0, b + ε • d⟫ ⟪p_quad 2, b + ε • d⟫ < max ⟪p_quad 1, b + ε • d⟫ ⟪p_quad 3, b + ε • d⟫ :=
    eventually_min02_lt_max13 p_quad b d h6lo
  have ev_inj : ∀ᶠ ε in 𝓝[>] (0 : ℝ), Function.Injective (fun i => ⟪p_quad i, b + ε • d⟫) :=
    eventually_injective_quad p_quad b d hS2
  have ev_all := ev_eps.and (ev_beta.and (ev_6.and (ev_N5.and (ev_6lo.and ev_inj))))
  obtain ⟨ε, hε, hβ, h6, hN5_u, h6lo_u, hinj_u⟩ := ev_all.exists
  set u := b + ε • d
  have hu_Pi_eq : u = u_Pi x t (s - 1 + ε) := hu_Pi ε
  have h8 : 0 < t * (1 - s) + (s - 1 + ε) * t := by
    have : t * (1 - s) + (s - 1 + ε) * t = ε * t := by ring
    rw [this]; exact mul_pos hε ht
  have hN5_Pi : ⟪F.N 5, u_Pi x t (s - 1 + ε)⟫ < 0 := by rw [← hu_Pi_eq]; exact hN5_u
  have hsigns := lemma_signs_J0 F s t t (s - 1 + ε) hs0 ht hst hdecomp ht hβ h8 h6 hN5_Pi
  rw [← hu_Pi_eq] at hsigns
  have hN3 : ⟪F.N 3, u⟫ = 0 := hsigns.1
  have hN2 : ⟪F.N 2, u⟫ < 0 := hsigns.2.1
  have hN4 : ⟪F.N 4, u⟫ < 0 := hsigns.2.2.1
  have hN5 : ⟪F.N 5, u⟫ < 0 := hsigns.2.2.2.1
  have hN6 : 0 < ⟪F.N 6, u⟫ := hsigns.2.2.2.2.1
  have hN7 : 0 < ⟪F.N 7, u⟫ := hsigns.2.2.2.2.2.1
  have hN8 : 0 < ⟪F.N 8, u⟫ := hsigns.2.2.2.2.2.2
  obtain ⟨ρ, hρ_ne, hcyc, hin⟩ := lemmaR_quad_signs F hN3 hN2 hN4 hN5 hN6 hN7 hN8
  have hin3 := hin 3
  have h3_eq : quad (x 6) (x 4) (x 5) (x 2) (3 + 1) - quad (x 6) (x 4) (x 5) (x 2) 3 = x 6 - x 2 := by
    show quad (x 6) (x 4) (x 5) (x 2) 0 - quad (x 6) (x 4) (x 5) (x 2) 3 = x 6 - x 2
    rfl
  have h3_1 : x 1 - quad (x 6) (x 4) (x 5) (x 2) 3 = x 1 - x 2 := by
    show x 1 - quad (x 6) (x 4) (x 5) (x 2) 3 = x 1 - x 2
    rfl
  rw [h3_eq, h3_1] at hin3
  have h_rho_om := rho_mul_omega_pos_of_inner_neg F u ρ hin3 hN5
  set Ω := det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1)
  have h_om_ne := omega_ne_zero F
  have h_om_sq : 0 < Ω ^ 2 := sq_pos_of_ne_zero h_om_ne
  have hkap := kappa_rim6452 x
  have h_om_kap : 0 < Ω * det3 (p_quad 2 - p_quad 0) (p_quad 3 - p_quad 1) (p_quad 0 - p_quad 1) := by
    dsimp [p_quad]
    rw [hkap]
    linarith [hk]
  have hk_pos : 0 < ρ * det3 (p_quad 2 - p_quad 0) (p_quad 3 - p_quad 1) (p_quad 0 - p_quad 1) := by
    have hprod : 0 < (ρ * Ω) * (Ω * det3 (p_quad 2 - p_quad 0) (p_quad 3 - p_quad 1) (p_quad 0 - p_quad 1)) :=
      mul_pos h_rho_om h_om_kap
    have : (ρ * Ω) * (Ω * det3 (p_quad 2 - p_quad 0) (p_quad 3 - p_quad 1) (p_quad 0 - p_quad 1)) =
        Ω ^ 2 * (ρ * det3 (p_quad 2 - p_quad 0) (p_quad 3 - p_quad 1) (p_quad 0 - p_quad 1)) := by ring
    rw [this] at hprod
    exact pos_of_mul_pos_right hprod h_om_sq.le
  have h_triD (i : ZMod 4) : 0 < ρ * triD p_quad u i := by
    have hneq1 : (i + 2 : ZMod 4) ≠ i := by
      intro h
      have : (2 : ZMod 4) = 0 := by
        calc (2 : ZMod 4) = (i + 2) - i := by ring
        _ = i - i := by rw [h]
        _ = 0 := sub_self i
      revert this; decide
    have hneq2 : (i + 2 : ZMod 4) ≠ i + 1 := by
      intro h
      have : (1 : ZMod 4) = 0 := by
        calc (1 : ZMod 4) = (i + 2) - (i + 1) := by ring
        _ = (i + 1) - (i + 1) := by rw [h]
        _ = 0 := sub_self _
      revert this; decide
    exact hcyc i (i + 2) hneq1 hneq2
  have h_uni := unimodal_quad_Kplus p_quad u ρ hinj_u h_triD hk_pos h6lo_u
  have h_mb := middle_bounds_J0 s t t (s - 1 + ε) hst ht hβ h8 h6
  set a : ZMod 4 := 1
  set w : ZMod 4 := if F.f 3 (x 2) < F.f 3 (x 6) then 3 else 0
  refine ⟨u, 4, inferInstance, r, a, w, ρ, hN3, by decide, ?_, ?_, hρ_ne, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show r 1 ∈ s0x_S24 3
    decide
  · show r (1 + 1) ∈ s0x_S24 3
    decide
  · intro i j hj1 hj2
    simp_rw [hr]
    exact hcyc i j hj1 hj2
  · intro q hqS hqr i
    have hq1 := exterior_vertices_J0 q hqS hqr
    subst hq1
    simp_rw [hr]
    exact hin i
  · intro q hqS hqr
    have hq03 := middle_vertices_J0 q hqS hqr
    have hra : x (r a) = x 4 := rfl
    have hra1 : x (r (a + 1)) = x 5 := rfl
    rw [hra, hra1]
    rcases hq03 with rfl | rfl
    · refine ⟨t / (t + (s - 1 + ε)), - (1 / (t + (s - 1 + ε))), h_mb.1.1, h_mb.1.2.1, h_mb.1.2.2, ?_⟩
      rw [hu_Pi_eq]
      exact middle_quad_x0 x t (s - 1 + ε) (by linarith [ht, hβ])
    · refine ⟨((1 - s) * t + t * (s - 1 + ε)) / (t + (s - 1 + ε)), (s + t - 1) / (t + (s - 1 + ε)), h_mb.2.1, h_mb.2.2.1, h_mb.2.2.2, ?_⟩
      rw [hu_Pi_eq]
      exact middle_quad_x3 x s t t (s - 1 + ε) hdecomp (by linarith [ht, hβ])
  · simp_rw [hr]
    exact hinj_u
  · simp_rw [hr]
    exact Or.inl h_uni
  · dsimp [w, r, quad]
    split_ifs <;> decide
  · intro m hmw hmS
    dsimp [w] at hmw ⊢
    split_ifs at hmw ⊢ with h26
    · have hcand := w_candidates_J0 m hmS
      rcases hcand with rfl | rfl
      · show F.f 3 (x 2) < F.f 3 (x 6); exact h26
      · exact False.elim (hmw rfl)
    · have hcand := w_candidates_J0 m hmS
      rcases hcand with rfl | rfl
      · exact False.elim (hmw rfl)
      · show F.f 3 (x 6) < F.f 3 (x 2)
        have : F.f 3 (x 2) ≠ F.f 3 (x 6) := hS3
        exact lt_of_le_of_ne (not_lt.mp h26) this.symm
  · have hra : x (r a) = x 4 := rfl
    have hra1 : x (r (a + 1)) = x 5 := rfl
    rw [hra, hra1]
    dsimp [w]
    split_ifs with h26
    · have hrw : r 3 = 2 := rfl
      rw [hrw]
      have hs4' := hS4
      split_ifs at hs4'
      exact hs4'
    · have hrw : r 0 = 6 := rfl
      rw [hrw]
      have hs4' := hS4
      split_ifs at hs4'
      exact hs4'

/-- **Leaf K+ (Unified Dispatcher Form)**:
Dispatches between `s ≤ 1` (`E5 = e5`) and `1 < s` (`E5 = e34`). -/
theorem q45_Kplus {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (ha4 : ⟪F.N 5, x 4 - x 0⟫ < 0)
    (ha5 : ⟪F.N 5, x 5 - x 0⟫ < 0)
    (s t : ℝ)
    (hs0 : 0 < s)
    (ht : 0 < t)
    (hst : 1 < s + t)
    (hdecomp : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0))
    (hk : det3 (x 5 - x 6) (x 2 - x 6) (x 4 - x 6) * det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) < 0)
    (hE5 : (s ≤ 1 ∧ min ⟪x 6, x 5 - x 0⟫ ⟪x 5, x 5 - x 0⟫ < max ⟪x 4, x 5 - x 0⟫ ⟪x 2, x 5 - x 0⟫) ∨
           (1 < s ∧ min ⟪x 6, x 3 - x 4⟫ ⟪x 5, x 3 - x 4⟫ < max ⟪x 4, x 3 - x 4⟫ ⟪x 2, x 3 - x 4⟫))
    (hS2_e5 : ∀ i j : ZMod 4, i ≠ j →
      ⟪quad (x 6) (x 4) (x 5) (x 2) i - quad (x 6) (x 4) (x 5) (x 2) j, x 5 - x 0⟫ ≠ 0 ∨
      ⟪quad (x 6) (x 4) (x 5) (x 2) i - quad (x 6) (x 4) (x 5) (x 2) j, x 4 - x 0⟫ ≠ 0)
    (hS2_e34 : ∀ i j : ZMod 4, i ≠ j →
      ⟪quad (x 6) (x 4) (x 5) (x 2) i - quad (x 6) (x 4) (x 5) (x 2) j, x 3 - x 4⟫ ≠ 0 ∨
      ⟪quad (x 6) (x 4) (x 5) (x 2) i - quad (x 6) (x 4) (x 5) (x 2) j, x 4 - x 0⟫ ≠ 0)
    (hS3 : F.f 3 (x 2) ≠ F.f 3 (x 6))
    (hS4 : ⟪F.N 3, cross (x 5 - x 4) (x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 4)⟫ ≠ 0 ∨
           ⟪x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 4, x 5 - x 4⟫ < 0 ∨
           ⟪x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 5, x 4 - x 5⟫ < 0) :
    FaceChordView F 3 := by
  rcases hE5 with ⟨hs, h6lo⟩ | ⟨hs, h6lo⟩
  · exact q45_Kplus_s_le_one F ha5 s t hs0 ht hst hdecomp hk hs h6lo hS2_e5 hS3 hS4
  · have ha34 : ⟪F.N 5, x 3 - x 4⟫ < 0 := by
      have hd : x 3 - x 4 = (s - 1) • (x 4 - x 0) + t • (x 5 - x 0) := by
        calc
          x 3 - x 4 = (x 3 - x 0) - (x 4 - x 0) := by abel
          _ = (s • (x 4 - x 0) + t • (x 5 - x 0)) - (x 4 - x 0) := by rw [hdecomp]
          _ = (s - 1) • (x 4 - x 0) + t • (x 5 - x 0) := by
            ext j; simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
      rw [hd, inner_add_right, real_inner_smul_right, real_inner_smul_right]
      have h1 : (s - 1) * ⟪F.N 5, x 4 - x 0⟫ < 0 := mul_neg_of_pos_of_neg (by linarith [hs]) ha4
      have h2 : t * ⟪F.N 5, x 5 - x 0⟫ < 0 := mul_neg_of_pos_of_neg ht ha5
      linarith
    exact q45_Kplus_s_gt_one F ha34 s t hs0 ht hst hdecomp hk hs h6lo hS2_e34 hS3 hS4

/-- **Leaf K- (Subcase t ≤ 1, E4 = e4)**:
When `0 < ρ0 * kJ` (i.e. `0 < det3(256-plane) * Ω`) and weak 2-high fails strictly at base `e4 = x 4 - x 0`.
- Views: `u_ε = e4 + ε • e5` in `J0` for small `ε > 0`.
- Rim: 6 4 5 2, chord 4 -> 5, middles 0, 3, farther w ∈ {2, 6}.
- Lemma K rules out 6-high everywhere on `J0`.
- Open condition `h2lo` rules out 2-high near `e4`. -/
theorem q45_Kminus_t_le_one {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (ha4 : ⟪F.N 5, x 4 - x 0⟫ < 0)
    (s t : ℝ)
    (hs0 : 0 < s)
    (ht : 0 < t)
    (hst : 1 < s + t)
    (hdecomp : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0))
    (hk : 0 < det3 (x 5 - x 6) (x 2 - x 6) (x 4 - x 6) * det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1))
    (ht1 : t ≤ 1)
    (h2lo : min ⟪x 4, x 4 - x 0⟫ ⟪x 2, x 4 - x 0⟫ < max ⟪x 6, x 4 - x 0⟫ ⟪x 5, x 4 - x 0⟫)
    (hS2 : ∀ i j : ZMod 4, i ≠ j →
      ⟪quad (x 6) (x 4) (x 5) (x 2) i - quad (x 6) (x 4) (x 5) (x 2) j, x 4 - x 0⟫ ≠ 0 ∨
      ⟪quad (x 6) (x 4) (x 5) (x 2) i - quad (x 6) (x 4) (x 5) (x 2) j, x 5 - x 0⟫ ≠ 0)
    (hS3 : F.f 3 (x 2) ≠ F.f 3 (x 6))
    (hS4 : ⟪F.N 3, cross (x 5 - x 4) (x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 4)⟫ ≠ 0 ∨
           ⟪x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 4, x 5 - x 4⟫ < 0 ∨
           ⟪x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 5, x 4 - x 5⟫ < 0) :
    FaceChordView F 3 := by
  set p_quad := quad (x 6) (x 4) (x 5) (x 2)
  set r : ZMod 4 → Fin 7 := quad 6 4 5 2
  have hr : ∀ i : ZMod 4, x (r i) = p_quad i := by
    intro i; fin_cases i <;> rfl
  set b := x 4 - x 0
  set d := x 5 - x 0
  have hu_Pi : ∀ ε : ℝ, b + ε • d = u_Pi x ε 1 := by
    intro ε; ext j; simp [b, d, u_Pi, e4, e5]; ring
  have ev_eps : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  have ev_8 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε * (1 - s) + 1 * t := by
    have : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < t + ε * (1 - s) :=
      eventually_pos_affine (A := t) (B := 1 - s) (Or.inl ht)
    filter_upwards [this] with ε hε
    linarith
  have ev_N5 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ⟪F.N 5, b + ε • d⟫ < 0 := by
    have hlin : ∀ ε : ℝ, ⟪F.N 5, b + ε • d⟫ = ⟪F.N 5, b⟫ + ε * ⟪F.N 5, d⟫ := by
      intro ε; rw [inner_add_right, real_inner_smul_right]
    have hpos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < - ⟪F.N 5, b⟫ + ε * (- ⟪F.N 5, d⟫) :=
      eventually_pos_affine (A := - ⟪F.N 5, b⟫) (B := - ⟪F.N 5, d⟫) (Or.inl (by linarith [ha4]))
    filter_upwards [hpos] with ε hε
    rw [hlin]; linarith
  have ev_2lo : ∀ᶠ ε in 𝓝[>] (0 : ℝ), min ⟪p_quad 1, b + ε • d⟫ ⟪p_quad 3, b + ε • d⟫ < max ⟪p_quad 0, b + ε • d⟫ ⟪p_quad 2, b + ε • d⟫ :=
    eventually_min13_lt_max02 p_quad b d h2lo
  have ev_inj : ∀ᶠ ε in 𝓝[>] (0 : ℝ), Function.Injective (fun i => ⟪p_quad i, b + ε • d⟫) :=
    eventually_injective_quad p_quad b d hS2
  have ev_all := ev_eps.and (ev_8.and (ev_N5.and (ev_2lo.and ev_inj)))
  obtain ⟨ε, hε, h8, hN5_u, h2lo_u, hinj_u⟩ := ev_all.exists
  set u := b + ε • d
  have hu_Pi_eq : u = u_Pi x ε 1 := hu_Pi ε
  have h6 : 0 < ε * s + 1 * (1 - t) := by nlinarith [ht1, hs0, hε]
  have hN5_Pi : ⟪F.N 5, u_Pi x ε 1⟫ < 0 := by rw [← hu_Pi_eq]; exact hN5_u
  have hsigns := lemma_signs_J0 F s t ε 1 hs0 ht hst hdecomp hε one_pos h8 h6 hN5_Pi
  rw [← hu_Pi_eq] at hsigns
  have hN3 : ⟪F.N 3, u⟫ = 0 := hsigns.1
  have hN2 : ⟪F.N 2, u⟫ < 0 := hsigns.2.1
  have hN4 : ⟪F.N 4, u⟫ < 0 := hsigns.2.2.1
  have hN5 : ⟪F.N 5, u⟫ < 0 := hsigns.2.2.2.1
  have hN6 : 0 < ⟪F.N 6, u⟫ := hsigns.2.2.2.2.1
  have hN7 : 0 < ⟪F.N 7, u⟫ := hsigns.2.2.2.2.2.1
  have hN8 : 0 < ⟪F.N 8, u⟫ := hsigns.2.2.2.2.2.2
  obtain ⟨ρ, hρ_ne, hcyc, hin⟩ := lemmaR_quad_signs F hN3 hN2 hN4 hN5 hN6 hN7 hN8
  have hin3 := hin 3
  have h3_eq : quad (x 6) (x 4) (x 5) (x 2) (3 + 1) - quad (x 6) (x 4) (x 5) (x 2) 3 = x 6 - x 2 := by
    show quad (x 6) (x 4) (x 5) (x 2) 0 - quad (x 6) (x 4) (x 5) (x 2) 3 = x 6 - x 2
    rfl
  have h3_1 : x 1 - quad (x 6) (x 4) (x 5) (x 2) 3 = x 1 - x 2 := by
    show x 1 - quad (x 6) (x 4) (x 5) (x 2) 3 = x 1 - x 2
    rfl
  rw [h3_eq, h3_1] at hin3
  have h_rho_om := rho_mul_omega_pos_of_inner_neg F u ρ hin3 hN5
  set Ω := det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1)
  have h_om_ne := omega_ne_zero F
  have h_om_sq : 0 < Ω ^ 2 := sq_pos_of_ne_zero h_om_ne
  have hkap := kappa_rim6452 x
  have h_om_kap : Ω * det3 (p_quad 2 - p_quad 0) (p_quad 3 - p_quad 1) (p_quad 0 - p_quad 1) < 0 := by
    dsimp [p_quad]
    rw [hkap]
    linarith [hk]
  have hk_neg : ρ * det3 (p_quad 2 - p_quad 0) (p_quad 3 - p_quad 1) (p_quad 0 - p_quad 1) < 0 := by
    have hprod : (ρ * Ω) * (Ω * det3 (p_quad 2 - p_quad 0) (p_quad 3 - p_quad 1) (p_quad 0 - p_quad 1)) < 0 :=
      mul_neg_of_pos_of_neg h_rho_om h_om_kap
    have : (ρ * Ω) * (Ω * det3 (p_quad 2 - p_quad 0) (p_quad 3 - p_quad 1) (p_quad 0 - p_quad 1)) =
        Ω ^ 2 * (ρ * det3 (p_quad 2 - p_quad 0) (p_quad 3 - p_quad 1) (p_quad 0 - p_quad 1)) := by ring
    rw [this] at hprod
    exact neg_of_mul_neg_right hprod h_om_sq.le
  have h_triD (i : ZMod 4) : 0 < ρ * triD p_quad u i := by
    have hneq1 : (i + 2 : ZMod 4) ≠ i := by
      intro h
      have : (2 : ZMod 4) = 0 := by
        calc (2 : ZMod 4) = (i + 2) - i := by ring
        _ = i - i := by rw [h]
        _ = 0 := sub_self i
      revert this; decide
    have hneq2 : (i + 2 : ZMod 4) ≠ i + 1 := by
      intro h
      have : (1 : ZMod 4) = 0 := by
        calc (1 : ZMod 4) = (i + 2) - (i + 1) := by ring
        _ = (i + 1) - (i + 1) := by rw [h]
        _ = 0 := sub_self _
      revert this; decide
    exact hcyc i (i + 2) hneq1 hneq2
  have h_uni := unimodal_quad_Kminus p_quad u ρ hinj_u h_triD hk_neg h2lo_u
  have h_mb := middle_bounds_J0 s t ε 1 hst hε one_pos h8 h6
  set a : ZMod 4 := 1
  set w : ZMod 4 := if F.f 3 (x 2) < F.f 3 (x 6) then 3 else 0
  refine ⟨u, 4, inferInstance, r, a, w, ρ, hN3, by decide, ?_, ?_, hρ_ne, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show r 1 ∈ s0x_S24 3
    decide
  · show r (1 + 1) ∈ s0x_S24 3
    decide
  · intro i j hj1 hj2
    simp_rw [hr]
    exact hcyc i j hj1 hj2
  · intro q hqS hqr i
    have hq1 := exterior_vertices_J0 q hqS hqr
    subst hq1
    simp_rw [hr]
    exact hin i
  · intro q hqS hqr
    have hq03 := middle_vertices_J0 q hqS hqr
    have hra : x (r a) = x 4 := rfl
    have hra1 : x (r (a + 1)) = x 5 := rfl
    rw [hra, hra1]
    rcases hq03 with rfl | rfl
    · refine ⟨ε / (ε + 1), - (1 / (ε + 1)), h_mb.1.1, h_mb.1.2.1, h_mb.1.2.2, ?_⟩
      rw [hu_Pi_eq]
      exact middle_quad_x0 x ε 1 (by linarith [hε])
    · refine ⟨((1 - s) * ε + t * 1) / (ε + 1), (s + t - 1) / (ε + 1), h_mb.2.1, h_mb.2.2.1, h_mb.2.2.2, ?_⟩
      rw [hu_Pi_eq]
      exact middle_quad_x3 x s t ε 1 hdecomp (by linarith [hε])
  · simp_rw [hr]
    exact hinj_u
  · simp_rw [hr]
    exact Or.inl h_uni
  · dsimp [w, r, quad]
    split_ifs <;> decide
  · intro m hmw hmS
    dsimp [w] at hmw ⊢
    split_ifs at hmw ⊢ with h26
    · have hcand := w_candidates_J0 m hmS
      rcases hcand with rfl | rfl
      · show F.f 3 (x 2) < F.f 3 (x 6); exact h26
      · exact False.elim (hmw rfl)
    · have hcand := w_candidates_J0 m hmS
      rcases hcand with rfl | rfl
      · exact False.elim (hmw rfl)
      · show F.f 3 (x 6) < F.f 3 (x 2)
        have : F.f 3 (x 2) ≠ F.f 3 (x 6) := hS3
        exact lt_of_le_of_ne (not_lt.mp h26) this.symm
  · have hra : x (r a) = x 4 := rfl
    have hra1 : x (r (a + 1)) = x 5 := rfl
    rw [hra, hra1]
    dsimp [w]
    split_ifs with h26
    · have hrw : r 3 = 2 := rfl
      rw [hrw]
      have hs4' := hS4
      split_ifs at hs4'
      exact hs4'
    · have hrw : r 0 = 6 := rfl
      rw [hrw]
      have hs4' := hS4
      split_ifs at hs4'
      exact hs4'

/-- **Leaf K- (Subcase 1 < t, E4 = e35)**:
When `0 < ρ0 * kJ` and weak 2-high fails strictly at base `e35 = x 3 - x 5`.
- Views: `u_ε = (x 3 - x 5) + ε • (x 5 - x 0)` in `J0` for small `ε > 0`.
- Rim: 6 4 5 2, chord 4 -> 5, middles 0, 3, farther w ∈ {2, 6}.
- Lemma K rules out 6-high everywhere on `J0`.
- Open condition `h2lo` rules out 2-high near `e35`. -/
theorem q45_Kminus_t_gt_one {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (ha35 : ⟪F.N 5, x 3 - x 5⟫ < 0)
    (s t : ℝ)
    (hs0 : 0 < s)
    (ht : 0 < t)
    (hst : 1 < s + t)
    (hdecomp : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0))
    (hk : 0 < det3 (x 5 - x 6) (x 2 - x 6) (x 4 - x 6) * det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1))
    (ht1 : 1 < t)
    (h2lo : min ⟪x 4, x 3 - x 5⟫ ⟪x 2, x 3 - x 5⟫ < max ⟪x 6, x 3 - x 5⟫ ⟪x 5, x 3 - x 5⟫)
    (hS2 : ∀ i j : ZMod 4, i ≠ j →
      ⟪quad (x 6) (x 4) (x 5) (x 2) i - quad (x 6) (x 4) (x 5) (x 2) j, x 3 - x 5⟫ ≠ 0 ∨
      ⟪quad (x 6) (x 4) (x 5) (x 2) i - quad (x 6) (x 4) (x 5) (x 2) j, x 5 - x 0⟫ ≠ 0)
    (hS3 : F.f 3 (x 2) ≠ F.f 3 (x 6))
    (hS4 : ⟪F.N 3, cross (x 5 - x 4) (x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 4)⟫ ≠ 0 ∨
           ⟪x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 4, x 5 - x 4⟫ < 0 ∨
           ⟪x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 5, x 4 - x 5⟫ < 0) :
    FaceChordView F 3 := by
  set p_quad := quad (x 6) (x 4) (x 5) (x 2)
  set r : ZMod 4 → Fin 7 := quad 6 4 5 2
  have hr : ∀ i : ZMod 4, x (r i) = p_quad i := by
    intro i; fin_cases i <;> rfl
  set b := x 3 - x 5
  set d := x 5 - x 0
  have hu_Pi : ∀ ε : ℝ, b + ε • d = u_Pi x (t - 1 + ε) s := by
    intro ε; ext j
    have hdj := congr_arg (fun (v : ℝ³) => v j) hdecomp
    dsimp [b, d, u_Pi, e4, e5, e35] at hdj ⊢
    linear_combination hdj
  have ev_eps : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  have ev_alpha : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < t - 1 + ε := by
    have := eventually_pos_affine (A := t - 1) (B := 1) (Or.inl (by linarith [ht1]))
    filter_upwards [this] with ε hε; linarith
  have ev_8 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < (t - 1 + ε) * (1 - s) + s * t := by
    have hA : 0 < (t - 1) * (1 - s) + s * t := by linarith [hst]
    have := eventually_pos_affine (A := (t - 1) * (1 - s) + s * t) (B := 1 - s) (Or.inl hA)
    filter_upwards [this] with ε hε
    have : (t - 1 + ε) * (1 - s) + s * t = (t - 1) * (1 - s) + s * t + ε * (1 - s) := by ring
    rw [this]; exact hε
  have ev_N5 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ⟪F.N 5, b + ε • d⟫ < 0 := by
    have hlin : ∀ ε : ℝ, ⟪F.N 5, b + ε • d⟫ = ⟪F.N 5, b⟫ + ε * ⟪F.N 5, d⟫ := by
      intro ε; rw [inner_add_right, real_inner_smul_right]
    have hpos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < - ⟪F.N 5, b⟫ + ε * (- ⟪F.N 5, d⟫) :=
      eventually_pos_affine (A := - ⟪F.N 5, b⟫) (B := - ⟪F.N 5, d⟫) (Or.inl (by linarith [ha35]))
    filter_upwards [hpos] with ε hε
    rw [hlin]; linarith
  have ev_2lo : ∀ᶠ ε in 𝓝[>] (0 : ℝ), min ⟪p_quad 1, b + ε • d⟫ ⟪p_quad 3, b + ε • d⟫ < max ⟪p_quad 0, b + ε • d⟫ ⟪p_quad 2, b + ε • d⟫ :=
    eventually_min13_lt_max02 p_quad b d h2lo
  have ev_inj : ∀ᶠ ε in 𝓝[>] (0 : ℝ), Function.Injective (fun i => ⟪p_quad i, b + ε • d⟫) :=
    eventually_injective_quad p_quad b d hS2
  have ev_all := ev_eps.and (ev_alpha.and (ev_8.and (ev_N5.and (ev_2lo.and ev_inj))))
  obtain ⟨ε, hε, hα, h8, hN5_u, h2lo_u, hinj_u⟩ := ev_all.exists
  set u := b + ε • d
  have hu_Pi_eq : u = u_Pi x (t - 1 + ε) s := hu_Pi ε
  have h6 : 0 < (t - 1 + ε) * s + s * (1 - t) := by
    have : (t - 1 + ε) * s + s * (1 - t) = ε * s := by ring
    rw [this]; exact mul_pos hε hs0
  have hN5_Pi : ⟪F.N 5, u_Pi x (t - 1 + ε) s⟫ < 0 := by rw [← hu_Pi_eq]; exact hN5_u
  have hsigns := lemma_signs_J0 F s t (t - 1 + ε) s hs0 ht hst hdecomp hα hs0 h8 h6 hN5_Pi
  rw [← hu_Pi_eq] at hsigns
  have hN3 : ⟪F.N 3, u⟫ = 0 := hsigns.1
  have hN2 : ⟪F.N 2, u⟫ < 0 := hsigns.2.1
  have hN4 : ⟪F.N 4, u⟫ < 0 := hsigns.2.2.1
  have hN5 : ⟪F.N 5, u⟫ < 0 := hsigns.2.2.2.1
  have hN6 : 0 < ⟪F.N 6, u⟫ := hsigns.2.2.2.2.1
  have hN7 : 0 < ⟪F.N 7, u⟫ := hsigns.2.2.2.2.2.1
  have hN8 : 0 < ⟪F.N 8, u⟫ := hsigns.2.2.2.2.2.2
  obtain ⟨ρ, hρ_ne, hcyc, hin⟩ := lemmaR_quad_signs F hN3 hN2 hN4 hN5 hN6 hN7 hN8
  have hin3 := hin 3
  have h3_eq : quad (x 6) (x 4) (x 5) (x 2) (3 + 1) - quad (x 6) (x 4) (x 5) (x 2) 3 = x 6 - x 2 := by
    show quad (x 6) (x 4) (x 5) (x 2) 0 - quad (x 6) (x 4) (x 5) (x 2) 3 = x 6 - x 2
    rfl
  have h3_1 : x 1 - quad (x 6) (x 4) (x 5) (x 2) 3 = x 1 - x 2 := by
    show x 1 - quad (x 6) (x 4) (x 5) (x 2) 3 = x 1 - x 2
    rfl
  rw [h3_eq, h3_1] at hin3
  have h_rho_om := rho_mul_omega_pos_of_inner_neg F u ρ hin3 hN5
  set Ω := det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1)
  have h_om_ne := omega_ne_zero F
  have h_om_sq : 0 < Ω ^ 2 := sq_pos_of_ne_zero h_om_ne
  have hkap := kappa_rim6452 x
  have h_om_kap : Ω * det3 (p_quad 2 - p_quad 0) (p_quad 3 - p_quad 1) (p_quad 0 - p_quad 1) < 0 := by
    dsimp [p_quad]
    rw [hkap]
    linarith [hk]
  have hk_neg : ρ * det3 (p_quad 2 - p_quad 0) (p_quad 3 - p_quad 1) (p_quad 0 - p_quad 1) < 0 := by
    have hprod : (ρ * Ω) * (Ω * det3 (p_quad 2 - p_quad 0) (p_quad 3 - p_quad 1) (p_quad 0 - p_quad 1)) < 0 :=
      mul_neg_of_pos_of_neg h_rho_om h_om_kap
    have : (ρ * Ω) * (Ω * det3 (p_quad 2 - p_quad 0) (p_quad 3 - p_quad 1) (p_quad 0 - p_quad 1)) =
        Ω ^ 2 * (ρ * det3 (p_quad 2 - p_quad 0) (p_quad 3 - p_quad 1) (p_quad 0 - p_quad 1)) := by ring
    rw [this] at hprod
    exact neg_of_mul_neg_right hprod h_om_sq.le
  have h_triD (i : ZMod 4) : 0 < ρ * triD p_quad u i := by
    have hneq1 : (i + 2 : ZMod 4) ≠ i := by
      intro h
      have : (2 : ZMod 4) = 0 := by
        calc (2 : ZMod 4) = (i + 2) - i := by ring
        _ = i - i := by rw [h]
        _ = 0 := sub_self i
      revert this; decide
    have hneq2 : (i + 2 : ZMod 4) ≠ i + 1 := by
      intro h
      have : (1 : ZMod 4) = 0 := by
        calc (1 : ZMod 4) = (i + 2) - (i + 1) := by ring
        _ = (i + 1) - (i + 1) := by rw [h]
        _ = 0 := sub_self _
      revert this; decide
    exact hcyc i (i + 2) hneq1 hneq2
  have h_uni := unimodal_quad_Kminus p_quad u ρ hinj_u h_triD hk_neg h2lo_u
  have h_mb := middle_bounds_J0 s t (t - 1 + ε) s hst hα hs0 h8 h6
  set a : ZMod 4 := 1
  set w : ZMod 4 := if F.f 3 (x 2) < F.f 3 (x 6) then 3 else 0
  refine ⟨u, 4, inferInstance, r, a, w, ρ, hN3, by decide, ?_, ?_, hρ_ne, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show r 1 ∈ s0x_S24 3
    decide
  · show r (1 + 1) ∈ s0x_S24 3
    decide
  · intro i j hj1 hj2
    simp_rw [hr]
    exact hcyc i j hj1 hj2
  · intro q hqS hqr i
    have hq1 := exterior_vertices_J0 q hqS hqr
    subst hq1
    simp_rw [hr]
    exact hin i
  · intro q hqS hqr
    have hq03 := middle_vertices_J0 q hqS hqr
    have hra : x (r a) = x 4 := rfl
    have hra1 : x (r (a + 1)) = x 5 := rfl
    rw [hra, hra1]
    rcases hq03 with rfl | rfl
    · refine ⟨(t - 1 + ε) / ((t - 1 + ε) + s), - (1 / ((t - 1 + ε) + s)), h_mb.1.1, h_mb.1.2.1, h_mb.1.2.2, ?_⟩
      rw [hu_Pi_eq]
      exact middle_quad_x0 x (t - 1 + ε) s (by linarith [hα, hs0])
    · refine ⟨((1 - s) * (t - 1 + ε) + t * s) / ((t - 1 + ε) + s), (s + t - 1) / ((t - 1 + ε) + s), h_mb.2.1, h_mb.2.2.1, h_mb.2.2.2, ?_⟩
      rw [hu_Pi_eq]
      exact middle_quad_x3 x s t (t - 1 + ε) s hdecomp (by linarith [hα, hs0])
  · simp_rw [hr]
    exact hinj_u
  · simp_rw [hr]
    exact Or.inl h_uni
  · dsimp [w, r, quad]
    split_ifs <;> decide
  · intro m hmw hmS
    dsimp [w] at hmw ⊢
    split_ifs at hmw ⊢ with h26
    · have hcand := w_candidates_J0 m hmS
      rcases hcand with rfl | rfl
      · show F.f 3 (x 2) < F.f 3 (x 6); exact h26
      · exact False.elim (hmw rfl)
    · have hcand := w_candidates_J0 m hmS
      rcases hcand with rfl | rfl
      · exact False.elim (hmw rfl)
      · show F.f 3 (x 6) < F.f 3 (x 2)
        have : F.f 3 (x 2) ≠ F.f 3 (x 6) := hS3
        exact lt_of_le_of_ne (not_lt.mp h26) this.symm
  · have hra : x (r a) = x 4 := rfl
    have hra1 : x (r (a + 1)) = x 5 := rfl
    rw [hra, hra1]
    dsimp [w]
    split_ifs with h26
    · have hrw : r 3 = 2 := rfl
      rw [hrw]
      have hs4' := hS4
      split_ifs at hs4'
      exact hs4'
    · have hrw : r 0 = 6 := rfl
      rw [hrw]
      have hs4' := hS4
      split_ifs at hs4'
      exact hs4'

/-- **Leaf K- (Unified Dispatcher Form)**:
Dispatches between `t ≤ 1` (`E4 = e4`) and `1 < t` (`E4 = e35`). -/
theorem q45_Kminus {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (ha4 : ⟪F.N 5, x 4 - x 0⟫ < 0)
    (ha5 : ⟪F.N 5, x 5 - x 0⟫ < 0)
    (s t : ℝ)
    (hs0 : 0 < s)
    (ht : 0 < t)
    (hst : 1 < s + t)
    (hdecomp : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0))
    (hk : 0 < det3 (x 5 - x 6) (x 2 - x 6) (x 4 - x 6) * det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1))
    (hE4 : (t ≤ 1 ∧ min ⟪x 4, x 4 - x 0⟫ ⟪x 2, x 4 - x 0⟫ < max ⟪x 6, x 4 - x 0⟫ ⟪x 5, x 4 - x 0⟫) ∨
           (1 < t ∧ min ⟪x 4, x 3 - x 5⟫ ⟪x 2, x 3 - x 5⟫ < max ⟪x 6, x 3 - x 5⟫ ⟪x 5, x 3 - x 5⟫))
    (hS2_e4 : ∀ i j : ZMod 4, i ≠ j →
      ⟪quad (x 6) (x 4) (x 5) (x 2) i - quad (x 6) (x 4) (x 5) (x 2) j, x 4 - x 0⟫ ≠ 0 ∨
      ⟪quad (x 6) (x 4) (x 5) (x 2) i - quad (x 6) (x 4) (x 5) (x 2) j, x 5 - x 0⟫ ≠ 0)
    (hS2_e35 : ∀ i j : ZMod 4, i ≠ j →
      ⟪quad (x 6) (x 4) (x 5) (x 2) i - quad (x 6) (x 4) (x 5) (x 2) j, x 3 - x 5⟫ ≠ 0 ∨
      ⟪quad (x 6) (x 4) (x 5) (x 2) i - quad (x 6) (x 4) (x 5) (x 2) j, x 5 - x 0⟫ ≠ 0)
    (hS3 : F.f 3 (x 2) ≠ F.f 3 (x 6))
    (hS4 : ⟪F.N 3, cross (x 5 - x 4) (x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 4)⟫ ≠ 0 ∨
           ⟪x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 4, x 5 - x 4⟫ < 0 ∨
           ⟪x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 5, x 4 - x 5⟫ < 0) :
    FaceChordView F 3 := by
  rcases hE4 with ⟨ht1, h2lo⟩ | ⟨ht1, h2lo⟩
  · exact q45_Kminus_t_le_one F ha4 s t hs0 ht hst hdecomp hk ht1 h2lo hS2_e4 hS3 hS4
  · have ha35 : ⟪F.N 5, x 3 - x 5⟫ < 0 := by
      have hd : x 3 - x 5 = s • (x 4 - x 0) + (t - 1) • (x 5 - x 0) := by
        calc
          x 3 - x 5 = (x 3 - x 0) - (x 5 - x 0) := by abel
          _ = (s • (x 4 - x 0) + t • (x 5 - x 0)) - (x 5 - x 0) := by rw [hdecomp]
          _ = s • (x 4 - x 0) + (t - 1) • (x 5 - x 0) := by
            ext j; simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
      rw [hd, inner_add_right, real_inner_smul_right, real_inner_smul_right]
      have h1 : s * ⟪F.N 5, x 4 - x 0⟫ < 0 := mul_neg_of_pos_of_neg hs0 ha4
      have h2 : (t - 1) * ⟪F.N 5, x 5 - x 0⟫ < 0 := mul_neg_of_pos_of_neg (by linarith [ht1]) ha5
      linarith
    exact q45_Kminus_t_gt_one F ha35 s t hs0 ht hst hdecomp hk ht1 h2lo hS2_e35 hS3 hS4

/-- **Leaf K- (companion) (Subcase s ≤ 1, E5 = e5)**:
When `ρ0 * kJ < 0` and weak 6-high fails strictly at base `e5 = x 5 - x 0`.
- Views: `u_ε = e5 + ε • e4` in `J0` for small `ε > 0`.
- Rim: 6 4 5 2, chord 4 -> 5, middles 0, 3, farther w ∈ {2, 6}.
- Lemma K (other sense) rules out 6-high everywhere on `J0`.
- Open condition `h2lo` rules out 2-high near `e5`. -/
theorem rj0h_Kminus_e5 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (ha5 : ⟪F.N 5, x 5 - x 0⟫ < 0)
    (s t : ℝ)
    (hs0 : 0 < s)
    (ht : 0 < t)
    (hst : 1 < s + t)
    (hdecomp : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0))
    (hk : 0 < det3 (x 5 - x 6) (x 2 - x 6) (x 4 - x 6) * det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1))
    (hs : s ≤ 1)
    (h2lo : min ⟪x 4, x 5 - x 0⟫ ⟪x 2, x 5 - x 0⟫ < max ⟪x 6, x 5 - x 0⟫ ⟪x 5, x 5 - x 0⟫)
    (hS2 : ∀ i j : ZMod 4, i ≠ j →
      ⟪quad (x 6) (x 4) (x 5) (x 2) i - quad (x 6) (x 4) (x 5) (x 2) j, x 5 - x 0⟫ ≠ 0 ∨
      ⟪quad (x 6) (x 4) (x 5) (x 2) i - quad (x 6) (x 4) (x 5) (x 2) j, x 4 - x 0⟫ ≠ 0)
    (hS3 : F.f 3 (x 2) ≠ F.f 3 (x 6))
    (hS4 : ⟪F.N 3, cross (x 5 - x 4) (x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 4)⟫ ≠ 0 ∨
           ⟪x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 4, x 5 - x 4⟫ < 0 ∨
           ⟪x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 5, x 4 - x 5⟫ < 0) :
    FaceChordView F 3 := by
  set p_quad := quad (x 6) (x 4) (x 5) (x 2)
  set r : ZMod 4 → Fin 7 := quad 6 4 5 2
  have hr : ∀ i : ZMod 4, x (r i) = p_quad i := by
    intro i; fin_cases i <;> rfl
  set b := x 5 - x 0
  set d := x 4 - x 0
  have hu_Pi : ∀ ε : ℝ, b + ε • d = u_Pi x 1 ε := by
    intro ε; ext j; simp [b, d, u_Pi, e4, e5]
  have ev_eps : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  have ev_6 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < 1 * s + ε * (1 - t) := by
    have : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < s + ε * (1 - t) :=
      eventually_pos_affine (A := s) (B := 1 - t) (Or.inl hs0)
    filter_upwards [this] with ε hε
    linarith
  have ev_N5 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ⟪F.N 5, b + ε • d⟫ < 0 := by
    have hlin : ∀ ε : ℝ, ⟪F.N 5, b + ε • d⟫ = ⟪F.N 5, b⟫ + ε * ⟪F.N 5, d⟫ := by
      intro ε; rw [inner_add_right, real_inner_smul_right]
    have hpos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < - ⟪F.N 5, b⟫ + ε * (- ⟪F.N 5, d⟫) :=
      eventually_pos_affine (A := - ⟪F.N 5, b⟫) (B := - ⟪F.N 5, d⟫) (Or.inl (by linarith [ha5]))
    filter_upwards [hpos] with ε hε
    rw [hlin]; linarith
  have ev_2lo : ∀ᶠ ε in 𝓝[>] (0 : ℝ), min ⟪p_quad 1, b + ε • d⟫ ⟪p_quad 3, b + ε • d⟫ < max ⟪p_quad 0, b + ε • d⟫ ⟪p_quad 2, b + ε • d⟫ :=
    eventually_min13_lt_max02 p_quad b d h2lo
  have ev_inj : ∀ᶠ ε in 𝓝[>] (0 : ℝ), Function.Injective (fun i => ⟪p_quad i, b + ε • d⟫) :=
    eventually_injective_quad p_quad b d hS2
  have ev_all := ev_eps.and (ev_6.and (ev_N5.and (ev_2lo.and ev_inj)))
  obtain ⟨ε, hε, h6, hN5_u, h2lo_u, hinj_u⟩ := ev_all.exists
  set u := b + ε • d
  have hu_Pi_eq : u = u_Pi x 1 ε := hu_Pi ε
  have h8 : 0 < 1 * (1 - s) + ε * t := by nlinarith [hs, ht, hε]
  have hN5_Pi : ⟪F.N 5, u_Pi x 1 ε⟫ < 0 := by rw [← hu_Pi_eq]; exact hN5_u
  have hsigns := lemma_signs_J0 F s t 1 ε hs0 ht hst hdecomp one_pos hε h8 h6 hN5_Pi
  rw [← hu_Pi_eq] at hsigns
  have hN3 : ⟪F.N 3, u⟫ = 0 := hsigns.1
  have hN2 : ⟪F.N 2, u⟫ < 0 := hsigns.2.1
  have hN4 : ⟪F.N 4, u⟫ < 0 := hsigns.2.2.1
  have hN5 : ⟪F.N 5, u⟫ < 0 := hsigns.2.2.2.1
  have hN6 : 0 < ⟪F.N 6, u⟫ := hsigns.2.2.2.2.1
  have hN7 : 0 < ⟪F.N 7, u⟫ := hsigns.2.2.2.2.2.1
  have hN8 : 0 < ⟪F.N 8, u⟫ := hsigns.2.2.2.2.2.2
  obtain ⟨ρ, hρ_ne, hcyc, hin⟩ := lemmaR_quad_signs F hN3 hN2 hN4 hN5 hN6 hN7 hN8
  have hin3 := hin 3
  have h3_eq : quad (x 6) (x 4) (x 5) (x 2) (3 + 1) - quad (x 6) (x 4) (x 5) (x 2) 3 = x 6 - x 2 := by
    show quad (x 6) (x 4) (x 5) (x 2) 0 - quad (x 6) (x 4) (x 5) (x 2) 3 = x 6 - x 2
    rfl
  have h3_1 : x 1 - quad (x 6) (x 4) (x 5) (x 2) 3 = x 1 - x 2 := by
    show x 1 - quad (x 6) (x 4) (x 5) (x 2) 3 = x 1 - x 2
    rfl
  rw [h3_eq, h3_1] at hin3
  have h_rho_om := rho_mul_omega_pos_of_inner_neg F u ρ hin3 hN5
  set Ω := det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1)
  have h_om_ne := omega_ne_zero F
  have h_om_sq : 0 < Ω ^ 2 := sq_pos_of_ne_zero h_om_ne
  have hkap := kappa_rim6452 x
  have h_om_kap : Ω * det3 (p_quad 2 - p_quad 0) (p_quad 3 - p_quad 1) (p_quad 0 - p_quad 1) < 0 := by
    dsimp [p_quad]
    rw [hkap]
    linarith [hk]
  have hk_neg : ρ * det3 (p_quad 2 - p_quad 0) (p_quad 3 - p_quad 1) (p_quad 0 - p_quad 1) < 0 := by
    have hprod : (ρ * Ω) * (Ω * det3 (p_quad 2 - p_quad 0) (p_quad 3 - p_quad 1) (p_quad 0 - p_quad 1)) < 0 :=
      mul_neg_of_pos_of_neg h_rho_om h_om_kap
    have : (ρ * Ω) * (Ω * det3 (p_quad 2 - p_quad 0) (p_quad 3 - p_quad 1) (p_quad 0 - p_quad 1)) =
        Ω ^ 2 * (ρ * det3 (p_quad 2 - p_quad 0) (p_quad 3 - p_quad 1) (p_quad 0 - p_quad 1)) := by ring
    rw [this] at hprod
    exact neg_of_mul_neg_right hprod h_om_sq.le
  have h_triD (i : ZMod 4) : 0 < ρ * triD p_quad u i := by
    have hneq1 : (i + 2 : ZMod 4) ≠ i := by
      intro h
      have : (2 : ZMod 4) = 0 := by
        calc (2 : ZMod 4) = (i + 2) - i := by ring
        _ = i - i := by rw [h]
        _ = 0 := sub_self i
      revert this; decide
    have hneq2 : (i + 2 : ZMod 4) ≠ i + 1 := by
      intro h
      have : (1 : ZMod 4) = 0 := by
        calc (1 : ZMod 4) = (i + 2) - (i + 1) := by ring
        _ = (i + 1) - (i + 1) := by rw [h]
        _ = 0 := sub_self _
      revert this; decide
    exact hcyc i (i + 2) hneq1 hneq2
  have h_uni := unimodal_quad_Kminus p_quad u ρ hinj_u h_triD hk_neg h2lo_u
  have h_mb := middle_bounds_J0 s t 1 ε hst one_pos hε h8 h6
  set a : ZMod 4 := 1
  set w : ZMod 4 := if F.f 3 (x 2) < F.f 3 (x 6) then 3 else 0
  refine ⟨u, 4, inferInstance, r, a, w, ρ, hN3, by decide, ?_, ?_, hρ_ne, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show r 1 ∈ s0x_S24 3
    decide
  · show r (1 + 1) ∈ s0x_S24 3
    decide
  · intro i j hj1 hj2
    simp_rw [hr]
    exact hcyc i j hj1 hj2
  · intro q hqS hqr i
    have hq1 := exterior_vertices_J0 q hqS hqr
    subst hq1
    simp_rw [hr]
    exact hin i
  · intro q hqS hqr
    have hq03 := middle_vertices_J0 q hqS hqr
    have hra : x (r a) = x 4 := rfl
    have hra1 : x (r (a + 1)) = x 5 := rfl
    rw [hra, hra1]
    rcases hq03 with rfl | rfl
    · refine ⟨1 / (1 + ε), - (1 / (1 + ε)), h_mb.1.1, h_mb.1.2.1, h_mb.1.2.2, ?_⟩
      rw [hu_Pi_eq]
      exact middle_quad_x0 x 1 ε (by linarith [hε])
    · refine ⟨((1 - s) * 1 + t * ε) / (1 + ε), (s + t - 1) / (1 + ε), h_mb.2.1, h_mb.2.2.1, h_mb.2.2.2, ?_⟩
      rw [hu_Pi_eq]
      exact middle_quad_x3 x s t 1 ε hdecomp (by linarith [hε])
  · simp_rw [hr]
    exact hinj_u
  · simp_rw [hr]
    exact Or.inl h_uni
  · dsimp [w, r, quad]
    split_ifs <;> decide
  · intro m hmw hmS
    dsimp [w] at hmw ⊢
    split_ifs at hmw ⊢ with h26
    · have hcand := w_candidates_J0 m hmS
      rcases hcand with rfl | rfl
      · show F.f 3 (x 2) < F.f 3 (x 6); exact h26
      · exact False.elim (hmw rfl)
    · have hcand := w_candidates_J0 m hmS
      rcases hcand with rfl | rfl
      · exact False.elim (hmw rfl)
      · show F.f 3 (x 6) < F.f 3 (x 2)
        have : F.f 3 (x 2) ≠ F.f 3 (x 6) := hS3
        exact lt_of_le_of_ne (not_lt.mp h26) this.symm
  · have hra : x (r a) = x 4 := rfl
    have hra1 : x (r (a + 1)) = x 5 := rfl
    rw [hra, hra1]
    dsimp [w]
    split_ifs with h26
    · have hrw : r 3 = 2 := rfl
      rw [hrw]
      have hs4' := hS4
      split_ifs at hs4'
      exact hs4'
    · have hrw : r 0 = 6 := rfl
      rw [hrw]
      have hs4' := hS4
      split_ifs at hs4'
      exact hs4'

/-- **Leaf K- (companion) (Subcase 1 < s, E5 = e34)**:
When `ρ0 * kJ < 0` and weak 6-high fails strictly at base `e34 = x 3 - x 4`.
- Views: `u_ε = (x 3 - x 4) + ε • (x 4 - x 0)` in `J0` for small `ε > 0`.
- Rim: 6 4 5 2, chord 4 -> 5, middles 0, 3, farther w ∈ {2, 6}.
- Lemma K (other sense) rules out 6-high everywhere on `J0`.
- Open condition `h2lo` rules out 2-high near `e34`. -/
theorem rj0h_Kminus_e34 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (ha34 : ⟪F.N 5, x 3 - x 4⟫ < 0)
    (s t : ℝ)
    (hs0 : 0 < s)
    (ht : 0 < t)
    (hst : 1 < s + t)
    (hdecomp : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0))
    (hk : 0 < det3 (x 5 - x 6) (x 2 - x 6) (x 4 - x 6) * det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1))
    (hs : 1 < s)
    (h2lo : min ⟪x 4, x 3 - x 4⟫ ⟪x 2, x 3 - x 4⟫ < max ⟪x 6, x 3 - x 4⟫ ⟪x 5, x 3 - x 4⟫)
    (hS2 : ∀ i j : ZMod 4, i ≠ j →
      ⟪quad (x 6) (x 4) (x 5) (x 2) i - quad (x 6) (x 4) (x 5) (x 2) j, x 3 - x 4⟫ ≠ 0 ∨
      ⟪quad (x 6) (x 4) (x 5) (x 2) i - quad (x 6) (x 4) (x 5) (x 2) j, x 4 - x 0⟫ ≠ 0)
    (hS3 : F.f 3 (x 2) ≠ F.f 3 (x 6))
    (hS4 : ⟪F.N 3, cross (x 5 - x 4) (x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 4)⟫ ≠ 0 ∨
           ⟪x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 4, x 5 - x 4⟫ < 0 ∨
           ⟪x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 5, x 4 - x 5⟫ < 0) :
    FaceChordView F 3 := by
  set p_quad := quad (x 6) (x 4) (x 5) (x 2)
  set r : ZMod 4 → Fin 7 := quad 6 4 5 2
  have hr : ∀ i : ZMod 4, x (r i) = p_quad i := by
    intro i; fin_cases i <;> rfl
  set b := x 3 - x 4
  set d := x 4 - x 0
  have hu_Pi : ∀ ε : ℝ, b + ε • d = u_Pi x t (s - 1 + ε) := by
    intro ε; ext j
    have hdj := congr_arg (fun (v : ℝ³) => v j) hdecomp
    dsimp [b, d, u_Pi, e4, e5, e34] at hdj ⊢
    linear_combination hdj
  have ev_eps : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  have ev_beta : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < s - 1 + ε := by
    have := eventually_pos_affine (A := s - 1) (B := 1) (Or.inl (by linarith [hs]))
    filter_upwards [this] with ε hε; linarith
  have ev_6 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < t * s + (s - 1 + ε) * (1 - t) := by
    have hA : 0 < t * s + (s - 1) * (1 - t) := by linarith [hst]
    have := eventually_pos_affine (A := t * s + (s - 1) * (1 - t)) (B := 1 - t) (Or.inl hA)
    filter_upwards [this] with ε hε
    have : t * s + (s - 1 + ε) * (1 - t) = t * s + (s - 1) * (1 - t) + ε * (1 - t) := by ring
    rw [this]; exact hε
  have ev_N5 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ⟪F.N 5, b + ε • d⟫ < 0 := by
    have hlin : ∀ ε : ℝ, ⟪F.N 5, b + ε • d⟫ = ⟪F.N 5, b⟫ + ε * ⟪F.N 5, d⟫ := by
      intro ε; rw [inner_add_right, real_inner_smul_right]
    have hpos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < - ⟪F.N 5, b⟫ + ε * (- ⟪F.N 5, d⟫) :=
      eventually_pos_affine (A := - ⟪F.N 5, b⟫) (B := - ⟪F.N 5, d⟫) (Or.inl (by linarith [ha34]))
    filter_upwards [hpos] with ε hε
    rw [hlin]; linarith
  have ev_2lo : ∀ᶠ ε in 𝓝[>] (0 : ℝ), min ⟪p_quad 1, b + ε • d⟫ ⟪p_quad 3, b + ε • d⟫ < max ⟪p_quad 0, b + ε • d⟫ ⟪p_quad 2, b + ε • d⟫ :=
    eventually_min13_lt_max02 p_quad b d h2lo
  have ev_inj : ∀ᶠ ε in 𝓝[>] (0 : ℝ), Function.Injective (fun i => ⟪p_quad i, b + ε • d⟫) :=
    eventually_injective_quad p_quad b d hS2
  have ev_all := ev_eps.and (ev_beta.and (ev_6.and (ev_N5.and (ev_2lo.and ev_inj))))
  obtain ⟨ε, hε, hβ, h6, hN5_u, h2lo_u, hinj_u⟩ := ev_all.exists
  set u := b + ε • d
  have hu_Pi_eq : u = u_Pi x t (s - 1 + ε) := hu_Pi ε
  have h8 : 0 < t * (1 - s) + (s - 1 + ε) * t := by
    have : t * (1 - s) + (s - 1 + ε) * t = ε * t := by ring
    rw [this]; exact mul_pos hε ht
  have hN5_Pi : ⟪F.N 5, u_Pi x t (s - 1 + ε)⟫ < 0 := by rw [← hu_Pi_eq]; exact hN5_u
  have hsigns := lemma_signs_J0 F s t t (s - 1 + ε) hs0 ht hst hdecomp ht hβ h8 h6 hN5_Pi
  rw [← hu_Pi_eq] at hsigns
  have hN3 : ⟪F.N 3, u⟫ = 0 := hsigns.1
  have hN2 : ⟪F.N 2, u⟫ < 0 := hsigns.2.1
  have hN4 : ⟪F.N 4, u⟫ < 0 := hsigns.2.2.1
  have hN5 : ⟪F.N 5, u⟫ < 0 := hsigns.2.2.2.1
  have hN6 : 0 < ⟪F.N 6, u⟫ := hsigns.2.2.2.2.1
  have hN7 : 0 < ⟪F.N 7, u⟫ := hsigns.2.2.2.2.2.1
  have hN8 : 0 < ⟪F.N 8, u⟫ := hsigns.2.2.2.2.2.2
  obtain ⟨ρ, hρ_ne, hcyc, hin⟩ := lemmaR_quad_signs F hN3 hN2 hN4 hN5 hN6 hN7 hN8
  have hin3 := hin 3
  have h3_eq : quad (x 6) (x 4) (x 5) (x 2) (3 + 1) - quad (x 6) (x 4) (x 5) (x 2) 3 = x 6 - x 2 := by
    show quad (x 6) (x 4) (x 5) (x 2) 0 - quad (x 6) (x 4) (x 5) (x 2) 3 = x 6 - x 2
    rfl
  have h3_1 : x 1 - quad (x 6) (x 4) (x 5) (x 2) 3 = x 1 - x 2 := by
    show x 1 - quad (x 6) (x 4) (x 5) (x 2) 3 = x 1 - x 2
    rfl
  rw [h3_eq, h3_1] at hin3
  have h_rho_om := rho_mul_omega_pos_of_inner_neg F u ρ hin3 hN5
  set Ω := det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1)
  have h_om_ne := omega_ne_zero F
  have h_om_sq : 0 < Ω ^ 2 := sq_pos_of_ne_zero h_om_ne
  have hkap := kappa_rim6452 x
  have h_om_kap : Ω * det3 (p_quad 2 - p_quad 0) (p_quad 3 - p_quad 1) (p_quad 0 - p_quad 1) < 0 := by
    dsimp [p_quad]
    rw [hkap]
    linarith [hk]
  have hk_neg : ρ * det3 (p_quad 2 - p_quad 0) (p_quad 3 - p_quad 1) (p_quad 0 - p_quad 1) < 0 := by
    have hprod : (ρ * Ω) * (Ω * det3 (p_quad 2 - p_quad 0) (p_quad 3 - p_quad 1) (p_quad 0 - p_quad 1)) < 0 :=
      mul_neg_of_pos_of_neg h_rho_om h_om_kap
    have : (ρ * Ω) * (Ω * det3 (p_quad 2 - p_quad 0) (p_quad 3 - p_quad 1) (p_quad 0 - p_quad 1)) =
        Ω ^ 2 * (ρ * det3 (p_quad 2 - p_quad 0) (p_quad 3 - p_quad 1) (p_quad 0 - p_quad 1)) := by ring
    rw [this] at hprod
    exact neg_of_mul_neg_right hprod h_om_sq.le
  have h_triD (i : ZMod 4) : 0 < ρ * triD p_quad u i := by
    have hneq1 : (i + 2 : ZMod 4) ≠ i := by
      intro h
      have : (2 : ZMod 4) = 0 := by
        calc (2 : ZMod 4) = (i + 2) - i := by ring
        _ = i - i := by rw [h]
        _ = 0 := sub_self i
      revert this; decide
    have hneq2 : (i + 2 : ZMod 4) ≠ i + 1 := by
      intro h
      have : (1 : ZMod 4) = 0 := by
        calc (1 : ZMod 4) = (i + 2) - (i + 1) := by ring
        _ = (i + 1) - (i + 1) := by rw [h]
        _ = 0 := sub_self _
      revert this; decide
    exact hcyc i (i + 2) hneq1 hneq2
  have h_uni := unimodal_quad_Kminus p_quad u ρ hinj_u h_triD hk_neg h2lo_u
  have h_mb := middle_bounds_J0 s t t (s - 1 + ε) hst ht hβ h8 h6
  set a : ZMod 4 := 1
  set w : ZMod 4 := if F.f 3 (x 2) < F.f 3 (x 6) then 3 else 0
  refine ⟨u, 4, inferInstance, r, a, w, ρ, hN3, by decide, ?_, ?_, hρ_ne, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show r 1 ∈ s0x_S24 3
    decide
  · show r (1 + 1) ∈ s0x_S24 3
    decide
  · intro i j hj1 hj2
    simp_rw [hr]
    exact hcyc i j hj1 hj2
  · intro q hqS hqr i
    have hq1 := exterior_vertices_J0 q hqS hqr
    subst hq1
    simp_rw [hr]
    exact hin i
  · intro q hqS hqr
    have hq03 := middle_vertices_J0 q hqS hqr
    have hra : x (r a) = x 4 := rfl
    have hra1 : x (r (a + 1)) = x 5 := rfl
    rw [hra, hra1]
    rcases hq03 with rfl | rfl
    · refine ⟨t / (t + (s - 1 + ε)), - (1 / (t + (s - 1 + ε))), h_mb.1.1, h_mb.1.2.1, h_mb.1.2.2, ?_⟩
      rw [hu_Pi_eq]
      exact middle_quad_x0 x t (s - 1 + ε) (by linarith [ht, hβ])
    · refine ⟨((1 - s) * t + t * (s - 1 + ε)) / (t + (s - 1 + ε)), (s + t - 1) / (t + (s - 1 + ε)), h_mb.2.1, h_mb.2.2.1, h_mb.2.2.2, ?_⟩
      rw [hu_Pi_eq]
      exact middle_quad_x3 x s t t (s - 1 + ε) hdecomp (by linarith [ht, hβ])
  · simp_rw [hr]
    exact hinj_u
  · simp_rw [hr]
    exact Or.inl h_uni
  · dsimp [w, r, quad]
    split_ifs <;> decide
  · intro m hmw hmS
    dsimp [w] at hmw ⊢
    split_ifs at hmw ⊢ with h26
    · have hcand := w_candidates_J0 m hmS
      rcases hcand with rfl | rfl
      · show F.f 3 (x 2) < F.f 3 (x 6); exact h26
      · exact False.elim (hmw rfl)
    · have hcand := w_candidates_J0 m hmS
      rcases hcand with rfl | rfl
      · exact False.elim (hmw rfl)
      · show F.f 3 (x 6) < F.f 3 (x 2)
        have : F.f 3 (x 2) ≠ F.f 3 (x 6) := hS3
        exact lt_of_le_of_ne (not_lt.mp h26) this.symm
  · have hra : x (r a) = x 4 := rfl
    have hra1 : x (r (a + 1)) = x 5 := rfl
    rw [hra, hra1]
    dsimp [w]
    split_ifs with h26
    · have hrw : r 3 = 2 := rfl
      rw [hrw]
      have hs4' := hS4
      split_ifs at hs4'
      exact hs4'
    · have hrw : r 0 = 6 := rfl
      rw [hrw]
      have hs4' := hS4
      split_ifs at hs4'
      exact hs4'


end Minimality.T24.Q45
