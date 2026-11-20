module

public import Minimality.RX16
public import Minimality.RF346C

@[expose] public section

set_option autoImplicit true
set_option relaxedAutoImplicit true

open scoped RealInnerProductSpace Topology
open Filter Finset
open Minimality Minimality.H21 Minimality.FaceChord Minimality.T24.SAT Minimality.RimFromSigns
open Minimality.T24.Q45 Minimality.T24.R012 Minimality.T24.R046 Minimality.T24.RX16

namespace Minimality.T24.RX16B

variable {x : Fin 7 → ℝ³}

/-- The 5-rim `(2, 5, 3, 6, 1)`: chord `1 → 2` of facet 012 is the edge from index `4` to index `0`
(vertex `0` is the middle over it, vertex `4` is inside). -/
def rim5 : ZMod 5 → Fin 7
  | 0 => 2
  | 1 => 5
  | 2 => 3
  | 3 => 6
  | 4 => 1

theorem rim5_data (F : S0xFac 9 s0x_S24 x) {u : ℝ³}
    (hN0 : ⟪F.N 0, u⟫ = 0) (h1 : 0 < ⟪F.N 1, u⟫) (h2 : 0 < ⟪F.N 2, u⟫) (h3 : 0 < ⟪F.N 3, u⟫)
    (h5 : ⟪F.N 5, u⟫ < 0) (h6 : ⟪F.N 6, u⟫ < 0) (h7 : ⟪F.N 7, u⟫ < 0) (h8 : 0 < ⟪F.N 8, u⟫) :
    ∃ ρ : ℝ, ρ ≠ 0 ∧ StrictConvex5 (fun i => x (rim5 i)) u ρ ∧
      (∀ i : ZMod 5, 0 < ρ * det3 (x (rim5 (i + 1)) - x (rim5 i)) (x 4 - x (rim5 i)) u) := by
  have hne_01 : cross u (x 5 - x 2) ≠ 0 :=
    cross_ne_zero_of_facet_sign F 2 2 5 (by decide) (by decide) h2.ne' 5 (by decide) (by decide)
  have hne_12 : cross u (x 3 - x 5) ≠ 0 :=
    cross_ne_zero_of_facet_sign F 6 5 3 (by decide) (by decide) h6.ne 2 (by decide) (by decide)
  have hne_23 : cross u (x 6 - x 3) ≠ 0 :=
    cross_ne_zero_of_facet_sign F 8 3 6 (by decide) (by decide) h8.ne' 3 (by decide) (by decide)
  have hne_34 : cross u (x 1 - x 6) ≠ 0 :=
    cross_ne_zero_of_facet_sign F 1 6 1 (by decide) (by decide) h1.ne' 4 (by decide) (by decide)
  have hne_40 : cross u (x 2 - x 1) ≠ 0 :=
    cross_ne_zero_of_facet_sign F 5 1 2 (by decide) (by decide) h5.ne 1 (by decide) (by decide)
  exact fiveRim_of_signs F (u := u) rim5 4 6 2 6 3 7 8 5 1 0
    (by decide) (by decide) hN0
    ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ ⟨h6, h2⟩
    ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ ⟨h6, h3⟩
    ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ ⟨h7, h8⟩
    ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ ⟨h5, h1⟩
    hne_01 hne_12 hne_23 hne_34 hne_40
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

/-- **q012_x16, branch `-1 < t16 < 0`, pentagon (the `N6 < 0` side of `q012_x16_hi`)**: the base view
`u16` (depths of `1` and `6` tied) perturbed along `x1 - x2`; with `N6 < 0` vertex `5` is on the rim
`(2,5,3,6,1)`, chord `1 → 2`, middle `0`, interior `4`. The tie `z1 = z6` is broken by the tilt inside
`LexTop`. -/
theorem q012_x16_pent (F : S0xFac 9 s0x_S24 x)
    (ht1 : -1 < t16 x) (ht0 : t16 x < 0)
    (h3 : 0 < ⟪F.N 3, u16 x⟫) (h6 : ⟪F.N 6, u16 x⟫ < 0) (h7 : ⟪F.N 7, u16 x⟫ < 0)
    (h8 : 0 < ⟪F.N 8, u16 x⟫)
    (hU : ∃ t : ZMod 5, LexTop (fun i => x (rim5 i)) (u16 x) (x 1 - x 2) t)
    (hgen : ∀ i j : ZMod 5, i ≠ j →
      ⟪x (rim5 i) - x (rim5 j), u16 x⟫ ≠ 0 ∨ ⟪x (rim5 i) - x (rim5 j), x 1 - x 2⟫ ≠ 0)
    (w : ZMod 5) (hw : w = 1 ∨ w = 2 ∨ w = 3)
    (hfar : ∀ m : ZMod 5, m ≠ w → rim5 m ∉ s0x_S24 0 → F.f 0 (x (rim5 w)) < F.f 0 (x (rim5 m)))
    (hoff : ⟪F.N 0, cross (x 2 - x 1) (x (rim5 w) - x 1)⟫ ≠ 0 ∨
      ⟪x (rim5 w) - x 1, x 2 - x 1⟫ < 0 ∨ ⟪x (rim5 w) - x 2, x 1 - x 2⟫ < 0) :
    FaceChordView F 0 := by
  set b : ℝ³ := u16 x with hb
  set c : ℝ³ := x 1 - x 2 with hc
  set p : ZMod 5 → ℝ³ := fun i => x (rim5 i) with hp
  have ev0 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  have evs : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ⟪F.N 3, b + ε • c⟫ ∧ ⟪F.N 6, b + ε • c⟫ < 0 ∧
      ⟪F.N 7, b + ε • c⟫ < 0 ∧ 0 < ⟪F.N 8, b + ε • c⟫ := by
    filter_upwards [evp' _ _ _ (Or.inl h3), evn' _ _ _ (Or.inl h6), evn' _ _ _ (Or.inl h7),
      evp' _ _ _ (Or.inl h8)] with ε e3 e6 e7 e8
    exact ⟨e3, e6, e7, e8⟩
  have et1 := ev_aff_gt (-1) (t16 x) (-1) ht1
  have et0 := ev_aff_lt 0 (t16 x) (-1) ht0
  obtain ⟨t, ht⟩ := hU
  have hinj := ev_injective_k b c p hgen
  have hZ : ∀ᶠ ε in 𝓝[>] (0 : ℝ), Function.Injective (fun i => ⟪p i, b + ε • c⟫) ∧
      UniOrSep p (b + ε • c) := by
    filter_upwards [ev_lexTop p b c t ht, hinj] with ε h hi
    exact ⟨hi, Or.inl (strictUnimodal_of_cyclic (by decide)
      (isCyclicUnimodal_of_top (by norm_num) hi t h))⟩
  obtain ⟨ε, ⟨e3, e6, e7, e8⟩, hε, ⟨hinj', hz⟩, ht1', ht0'⟩ :=
    (evs.and (ev0.and (hZ.and (et1.and et0)))).exists
  have hε' : (0 : ℝ) < ε := hε
  have hv : b + ε • c = u0 x (t16 x - ε) := view_neg x _ _
  set t' := t16 x - ε with ht'
  have ht1'' : -1 < t' := by rw [ht']; linarith
  have ht0'' : t' < 0 := by rw [ht']; linarith
  have hN0 : ⟪F.N 0, b + ε • c⟫ = 0 := by rw [hv]; exact inner_N0_u0 F _
  have e1 : 0 < ⟪F.N 1, b + ε • c⟫ := by
    rw [hv, inner_N1_u0]; nlinarith [lambda1_pos F]
  have e2 : 0 < ⟪F.N 2, b + ε • c⟫ := by
    rw [hv, inner_N2_u0]; nlinarith [lambda2_pos F]
  have e5 : ⟪F.N 5, b + ε • c⟫ < 0 := by rw [hv]; exact inner_N5_u0_neg F _
  obtain ⟨ρ, hρ, hcv, hin4⟩ := rim5_data F hN0 e1 e2 e3 e5 e6 e7 e8
  have hw' : rim5 w ∉ s0x_S24 0 := by rcases hw with rfl | rfl | rfl <;> decide
  refine ⟨b + ε • c, 5, inferInstance, rim5, 4, w, ρ, hN0, by decide, by decide, by decide, hρ,
    hcv, ?_, ?_, hinj', hz, hw', hfar, hoff⟩
  · intro q hq0 hqr i
    have hq4 : q = 4 := by
      fin_cases q <;> first | rfl | (exfalso; revert hq0; decide) | (exfalso; exact hqr 1 rfl) |
        (exfalso; exact hqr 2 rfl) | (exfalso; exact hqr 3 rfl)
    subst hq4
    exact hin4 i
  · intro q hq0 hqr
    have hq0' : q = 0 := by
      fin_cases q <;> first | rfl | (exfalso; revert hq0; decide) | (exfalso; exact hqr 0 rfl) |
        (exfalso; exact hqr 4 rfl)
    subst hq0'
    refine ⟨-t', 1, by linarith, by linarith, one_ne_zero, ?_⟩
    change x 0 = x 1 + (-t') • (x 2 - x 1) + (1 : ℝ) • (b + ε • c)
    rw [hv]
    simp only [u0]
    ext j
    simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
    ring

/-- The 6-rim `(1, 0, 5, 3, 4, 6)`: chord `1 → 0` of facet 012 is the edge from index `0` to index `1`
(vertex `2` is the middle over it). -/
def rim6 : ZMod 6 → Fin 7
  | 0 => 1
  | 1 => 0
  | 2 => 5
  | 3 => 3
  | 4 => 4
  | 5 => 6

theorem rim6_data (F : S0xFac 9 s0x_S24 x) {u : ℝ³}
    (hN0 : ⟪F.N 0, u⟫ = 0) (h1 : 0 < ⟪F.N 1, u⟫) (h2 : ⟪F.N 2, u⟫ < 0) (h3 : 0 < ⟪F.N 3, u⟫)
    (h4 : 0 < ⟪F.N 4, u⟫) (h5 : ⟪F.N 5, u⟫ < 0) (h6 : ⟪F.N 6, u⟫ < 0) (h8 : ⟪F.N 8, u⟫ < 0) :
    ∃ ρ : ℝ, ρ ≠ 0 ∧ ∀ i j : ZMod 6, j ≠ i → j ≠ i + 1 →
      0 < ρ * det3 (x (rim6 (i + 1)) - x (rim6 i)) (x (rim6 j) - x (rim6 i)) u := by
  have n01 : cross u (x 0 - x 1) ≠ 0 :=
    cross_ne_zero_of_facet_sign F 1 1 0 (by decide) (by decide) h1.ne' 5 (by decide) (by decide)
  have n12 : cross u (x 5 - x 0) ≠ 0 :=
    cross_ne_zero_of_facet_sign F 2 0 5 (by decide) (by decide) h2.ne 4 (by decide) (by decide)
  have n23 : cross u (x 3 - x 5) ≠ 0 :=
    cross_ne_zero_of_facet_sign F 6 5 3 (by decide) (by decide) h6.ne 2 (by decide) (by decide)
  have n34 : cross u (x 4 - x 3) ≠ 0 :=
    cross_ne_zero_of_facet_sign F 3 3 4 (by decide) (by decide) h3.ne' 6 (by decide) (by decide)
  have n45 : cross u (x 6 - x 4) ≠ 0 :=
    cross_ne_zero_of_facet_sign F 4 4 6 (by decide) (by decide) h4.ne' 3 (by decide) (by decide)
  have n50 : cross u (x 1 - x 6) ≠ 0 :=
    cross_ne_zero_of_facet_sign F 1 6 1 (by decide) (by decide) h1.ne' 4 (by decide) (by decide)
  obtain ⟨σ0, hσ0n, hσ0⟩ := det3_sign_edgeOn F 0 1 0 (by decide) (by decide) u hN0 n01
  obtain ⟨σ1, -, hσ1⟩ := det3_sign_ridge F 2 3 0 5 ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ u ⟨h2, h3⟩ n12
  obtain ⟨σ2, -, hσ2⟩ := det3_sign_ridge F 6 3 5 3 ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ u ⟨h6, h3⟩ n23
  obtain ⟨σ3, -, hσ3⟩ := det3_sign_ridge F 8 3 3 4 ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ u ⟨h8, h3⟩ n34
  obtain ⟨σ4, -, hσ4⟩ := det3_sign_ridge F 8 4 4 6 ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ u ⟨h8, h4⟩ n45
  obtain ⟨σ5, -, hσ5⟩ := det3_sign_ridge F 5 1 6 1 ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ u ⟨h5, h1⟩ n50
  have c0 := Minimality.det3_cycle_triangle (x 1) (x 0) (x 5) u
  have c1 := Minimality.det3_cycle_triangle (x 0) (x 5) (x 3) u
  have c2 := Minimality.det3_cycle_triangle (x 5) (x 3) (x 4) u
  have c3 := Minimality.det3_cycle_triangle (x 3) (x 4) (x 6) u
  have c4 := Minimality.det3_cycle_triangle (x 4) (x 6) (x 1) u
  have p01 : 0 < σ0 * σ1 := sign_prod (hσ0 5 (by decide)) (by rw [c0]; exact hσ1 1 (by decide))
  have p12 : 0 < σ1 * σ2 := sign_prod (hσ1 3 (by decide)) (by rw [c1]; exact hσ2 0 (by decide))
  have p23 : 0 < σ2 * σ3 := sign_prod (hσ2 4 (by decide)) (by rw [c2]; exact hσ3 5 (by decide))
  have p34 : 0 < σ3 * σ4 := sign_prod (hσ3 6 (by decide)) (by rw [c3]; exact hσ4 3 (by decide))
  have p45 : 0 < σ4 * σ5 := sign_prod (hσ4 1 (by decide)) (by rw [c4]; exact hσ5 4 (by decide))
  have s01 := p01
  have s02 := sign_transfer s01 p12
  have s03 := sign_transfer s02 p23
  have s04 := sign_transfer s03 p34
  have s05 := sign_transfer s04 p45
  refine ⟨σ0, hσ0n, ?_⟩
  intro i j hj1 hj2
  rcases zmod6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;>
  rcases zmod6_cases j with rfl | rfl | rfl | rfl | rfl | rfl
  · exact False.elim (hj1 rfl)
  · exact False.elim (hj2 rfl)
  · exact hσ0 5 (by decide)
  · exact hσ0 3 (by decide)
  · exact hσ0 4 (by decide)
  · exact hσ0 6 (by decide)
  · exact sign_transfer s01 (hσ1 1 (by decide))
  · exact False.elim (hj1 rfl)
  · exact False.elim (hj2 rfl)
  · exact sign_transfer s01 (hσ1 3 (by decide))
  · exact sign_transfer s01 (hσ1 4 (by decide))
  · exact sign_transfer s01 (hσ1 6 (by decide))
  · exact sign_transfer s02 (hσ2 1 (by decide))
  · exact sign_transfer s02 (hσ2 0 (by decide))
  · exact False.elim (hj1 rfl)
  · exact False.elim (hj2 rfl)
  · exact sign_transfer s02 (hσ2 4 (by decide))
  · exact sign_transfer s02 (hσ2 6 (by decide))
  · exact sign_transfer s03 (hσ3 1 (by decide))
  · exact sign_transfer s03 (hσ3 0 (by decide))
  · exact sign_transfer s03 (hσ3 5 (by decide))
  · exact False.elim (hj1 rfl)
  · exact False.elim (hj2 rfl)
  · exact sign_transfer s03 (hσ3 6 (by decide))
  · exact sign_transfer s04 (hσ4 1 (by decide))
  · exact sign_transfer s04 (hσ4 0 (by decide))
  · exact sign_transfer s04 (hσ4 5 (by decide))
  · exact sign_transfer s04 (hσ4 3 (by decide))
  · exact False.elim (hj1 rfl)
  · exact False.elim (hj2 rfl)
  · exact False.elim (hj2 rfl)
  · exact sign_transfer s05 (hσ5 0 (by decide))
  · exact sign_transfer s05 (hσ5 5 (by decide))
  · exact sign_transfer s05 (hσ5 3 (by decide))
  · exact sign_transfer s05 (hσ5 4 (by decide))
  · exact False.elim (hj1 rfl)

/-- **q012_x16, branch `t16 < -1`, hexagon (the `N3 > 0` side of `q012_x16_lo`)**: base view `u16`
perturbed along `x2 - x1`; with `N3 > 0, N4 > 0, N6 < 0, N8 < 0` the rim is `(1,0,5,3,4,6)`,
chord `1 → 0`, middle `2`; the tie `z1 = z6` is broken by the tilt inside `LexTop`. -/
theorem q012_x16_hex (F : S0xFac 9 s0x_S24 x)
    (ht : t16 x < -1)
    (h3 : 0 < ⟪F.N 3, u16 x⟫) (h4 : 0 < ⟪F.N 4, u16 x⟫) (h6 : ⟪F.N 6, u16 x⟫ < 0)
    (h8 : ⟪F.N 8, u16 x⟫ < 0)
    (hU : ∃ t : ZMod 6, LexTop (fun i => x (rim6 i)) (u16 x) (x 2 - x 1) t)
    (hgen : ∀ i j : ZMod 6, i ≠ j →
      ⟪x (rim6 i) - x (rim6 j), u16 x⟫ ≠ 0 ∨ ⟪x (rim6 i) - x (rim6 j), x 2 - x 1⟫ ≠ 0)
    (w : ZMod 6) (hw : w = 2 ∨ w = 3 ∨ w = 4 ∨ w = 5)
    (hfar : ∀ m : ZMod 6, m ≠ w → rim6 m ∉ s0x_S24 0 → F.f 0 (x (rim6 w)) < F.f 0 (x (rim6 m)))
    (hoff : ⟪F.N 0, cross (x 0 - x 1) (x (rim6 w) - x 1)⟫ ≠ 0 ∨
      ⟪x (rim6 w) - x 1, x 0 - x 1⟫ < 0 ∨ ⟪x (rim6 w) - x 0, x 1 - x 0⟫ < 0) :
    FaceChordView F 0 := by
  set b : ℝ³ := u16 x with hb
  set c : ℝ³ := x 2 - x 1 with hc
  set p : ZMod 6 → ℝ³ := fun i => x (rim6 i) with hp
  have ev0 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  have evs : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ⟪F.N 3, b + ε • c⟫ ∧ 0 < ⟪F.N 4, b + ε • c⟫ ∧
      ⟪F.N 6, b + ε • c⟫ < 0 ∧ ⟪F.N 8, b + ε • c⟫ < 0 := by
    filter_upwards [evp' _ _ _ (Or.inl h3), evp' _ _ _ (Or.inl h4), evn' _ _ _ (Or.inl h6),
      evn' _ _ _ (Or.inl h8)] with ε e3 e4 e6 e8
    exact ⟨e3, e4, e6, e8⟩
  have et := ev_aff_lt (-1) (t16 x) 1 ht
  obtain ⟨t, htop⟩ := hU
  have hinj := ev_injective_k b c p hgen
  have hZ : ∀ᶠ ε in 𝓝[>] (0 : ℝ), Function.Injective (fun i => ⟪p i, b + ε • c⟫) ∧
      UniOrSep p (b + ε • c) := by
    filter_upwards [ev_lexTop p b c t htop, hinj] with ε h hi
    exact ⟨hi, Or.inl (strictUnimodal_of_cyclic (by decide)
      (isCyclicUnimodal_of_top (by norm_num) hi t h))⟩
  obtain ⟨ε, ⟨e3, e4, e6, e8⟩, hε, ⟨hinj', hz⟩, het⟩ := (evs.and (ev0.and (hZ.and et))).exists
  have hε' : (0 : ℝ) < ε := hε
  have hv : b + ε • c = u0 x (t16 x + ε) := (u0_add x _ _).symm
  set t' := t16 x + ε with ht'
  have ht1 : t' < -1 := by rw [ht']; linarith
  have hN0 : ⟪F.N 0, b + ε • c⟫ = 0 := by rw [hv]; exact inner_N0_u0 F _
  have e1 : 0 < ⟪F.N 1, b + ε • c⟫ := by
    rw [hv, inner_N1_u0]; nlinarith [lambda1_pos F]
  have e2 : ⟪F.N 2, b + ε • c⟫ < 0 := by
    rw [hv, inner_N2_u0]; nlinarith [lambda2_pos F]
  have e5 : ⟪F.N 5, b + ε • c⟫ < 0 := by rw [hv]; exact inner_N5_u0_neg F _
  obtain ⟨ρ, hρ, hcv⟩ := rim6_data F hN0 e1 e2 e3 e4 e5 e6 e8
  have hw' : rim6 w ∉ s0x_S24 0 := by rcases hw with rfl | rfl | rfl | rfl <;> decide
  have htn : t' ≠ 0 := by intro h; rw [h] at ht1; linarith
  refine ⟨b + ε • c, 6, inferInstance, rim6, 0, w, ρ, hN0, by decide, by decide, by decide,
    hρ, hcv, ?_, ?_, hinj', hz, hw', hfar, hoff⟩
  · intro q hq0 hqr i
    exfalso
    fin_cases q
    · exact hq0 (by decide)
    · exact hq0 (by decide)
    · exact hq0 (by decide)
    · exact hqr 3 rfl
    · exact hqr 4 rfl
    · exact hqr 2 rfl
    · exact hqr 5 rfl
  · intro q hq0 hqr
    have hq2 : q = 2 := by
      fin_cases q <;> first | rfl | (exfalso; revert hq0; decide) | (exfalso; exact hqr 0 rfl) |
        (exfalso; exact hqr 1 rfl)
    subst hq2
    refine ⟨-1 / t', 1 / t', ?_, ?_, by simpa using htn, ?_⟩
    · exact div_pos_of_neg_of_neg (by norm_num) (by linarith)
    · rw [div_lt_one_of_neg (by linarith)]; linarith
    · change x 2 = x 1 + (-1 / t') • (x 0 - x 1) + (1 / t') • (b + ε • c)
      rw [hv]
      simp only [u0]
      ext j
      simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
      field_simp
      ring

end Minimality.T24.RX16B
