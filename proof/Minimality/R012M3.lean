module

public import Minimality.R012
public import Minimality.FiveRim
public import Minimality.FaceChordFac
public import Minimality.Q45Leaf
public import Minimality.Q45Signs
public import Minimality.Q45Orient
public import Minimality.CornerU
public import Minimality.RimFromSigns
public import Minimality.DiagCross
public import Minimality.SplitTie
public import Minimality.Q45J0
public import Minimality.Type24SAT.K24.Wire24
public import Minimality.Type24SAT.Facets24
public import Minimality.ZModLemmas
public import Minimality.R012M

@[expose] public section

set_option autoImplicit true
set_option relaxedAutoImplicit true
open scoped RealInnerProductSpace Topology
open Filter Finset
open Minimality Minimality.H21 Minimality.FaceChord Minimality.T24.SAT Minimality.RimFromSigns
open Minimality.T24.Q45 Minimality.T24.R012

namespace Minimality.T24.R012

variable {x : Fin 7 → ℝ³}

private lemma view_inner (F : S0xFac 9 s0x_S24 x) (t : Fin 9) (b c : ℝ³) (ε : ℝ) :
    ⟪F.N t, b + ε • c⟫ = ⟪F.N t, b⟫ + ε * ⟪F.N t, c⟫ := by
  rw [inner_add_right, real_inner_smul_right]

/-! ### The tilt `u0(-1 + ε) = (x0 - x2) + ε (x2 - x1)` on facet 012: middle `0` over the chord `2 → 1` -/

lemma inner_N0_uP (F : S0xFac 9 s0x_S24 x) (ε : ℝ) :
    ⟪F.N 0, (x 0 - x 2) + ε • (x 2 - x 1)⟫ = 0 := by
  rw [view_inner, F.inner_sub, F.inner_sub, F.zero 0 0 (by decide), F.zero 0 2 (by decide),
    F.zero 0 1 (by decide)]; ring

/-- Facet signs along `u_ε = (x0 - x2) + ε (x2 - x1)`, common to the 5-rim and the 6-rim cases. -/
theorem ev_signsP (F : S0xFac 9 s0x_S24 x) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      0 < ⟪F.N 1, (x 0 - x 2) + ε • (x 2 - x 1)⟫ ∧ ⟪F.N 5, (x 0 - x 2) + ε • (x 2 - x 1)⟫ < 0 ∧
      ⟪F.N 7, (x 0 - x 2) + ε • (x 2 - x 1)⟫ < 0 ∧ ⟪F.N 6, (x 0 - x 2) + ε • (x 2 - x 1)⟫ < 0 ∧
      0 < ⟪F.N 3, (x 0 - x 2) + ε • (x 2 - x 1)⟫ ∧ 0 < ⟪F.N 2, (x 0 - x 2) + ε • (x 2 - x 1)⟫ ∧
      0 < ⟪F.N 4, (x 0 - x 2) + ε • (x 2 - x 1)⟫ := by
  have z := fun (t : Fin 9) (i : Fin 7) (h : i ∈ s0x_S24 t) => F.zero t i h
  have s := fun (t : Fin 9) (a b : Fin 7) => F.inner_sub t a b
  have e1 := evp' (F.N 1) (x 0 - x 2) (x 2 - x 1) (Or.inl (by
    rw [s 1 0 2, z 1 0 (by decide)]; linarith [F.neg 1 2 (by decide)]))
  have e5 := evn' (F.N 5) (x 0 - x 2) (x 2 - x 1) (Or.inl (by
    rw [s 5 0 2, z 5 2 (by decide)]; linarith [F.neg 5 0 (by decide)]))
  have e7 := evn' (F.N 7) (x 0 - x 2) (x 2 - x 1) (Or.inl (by
    rw [s 7 0 2, z 7 2 (by decide)]; linarith [F.neg 7 0 (by decide)]))
  have e6 := evn' (F.N 6) (x 0 - x 2) (x 2 - x 1) (Or.inl (by
    rw [s 6 0 2, z 6 2 (by decide)]; linarith [F.neg 6 0 (by decide)]))
  have e3 := evp' (F.N 3) (x 0 - x 2) (x 2 - x 1) (Or.inl (by
    rw [s 3 0 2, z 3 0 (by decide)]; linarith [F.neg 3 2 (by decide)]))
  have e4 := evp' (F.N 4) (x 0 - x 2) (x 2 - x 1) (Or.inl (by
    rw [s 4 0 2, z 4 0 (by decide)]; linarith [F.neg 4 2 (by decide)]))
  have e2 := evp' (F.N 2) (x 0 - x 2) (x 2 - x 1) (Or.inr ⟨by
    rw [s 2 0 2, z 2 0 (by decide), z 2 2 (by decide)]; ring, by
    rw [s 2 2 1, z 2 2 (by decide)]; linarith [F.neg 2 1 (by decide)]⟩)
  filter_upwards [e1, e5, e7, e6, e3, e2, e4] with ε h1 h5 h7 h6 h3 h2 h4
  exact ⟨h1, h5, h7, h6, h3, h2, h4⟩

/-- The rim `(1, 6, 3, 5, 2)`; the chord `2 → 1` of facet 012 is the edge from index `4` to index `0`. -/
def rimP5 : ZMod 5 → Fin 7
  | 0 => 1
  | 1 => 6
  | 2 => 3
  | 3 => 5
  | 4 => 2

/-- Rim data for `(1, 6, 3, 5, 2)` (`⟪N8, u⟫ > 0`), vertex `4` inside. -/
theorem rim_dataP5 (F : S0xFac 9 s0x_S24 x) {u : ℝ³}
    (hN0 : ⟪F.N 0, u⟫ = 0) (h1 : 0 < ⟪F.N 1, u⟫) (h5 : ⟪F.N 5, u⟫ < 0) (h7 : ⟪F.N 7, u⟫ < 0)
    (h8 : 0 < ⟪F.N 8, u⟫) (h6 : ⟪F.N 6, u⟫ < 0) (h3 : 0 < ⟪F.N 3, u⟫) (h2 : 0 < ⟪F.N 2, u⟫) :
    ∃ ρ : ℝ, ρ ≠ 0 ∧ StrictConvexK (fun i => x (rimP5 i)) u ρ ∧
      (∀ i : ZMod 5, 0 < ρ * det3 (x (rimP5 (i + 1)) - x (rimP5 i)) (x 4 - x (rimP5 i)) u) := by
  have hne_01 : cross u (x 6 - x 1) ≠ 0 :=
    cross_ne_zero_of_facet_sign F 1 1 6 (by decide) (by decide) h1.ne' 0 (by decide) (by decide)
  have hne_12 : cross u (x 3 - x 6) ≠ 0 :=
    cross_ne_zero_of_facet_sign F 8 6 3 (by decide) (by decide) h8.ne' 1 (by decide) (by decide)
  have hne_23 : cross u (x 5 - x 3) ≠ 0 :=
    cross_ne_zero_of_facet_sign F 3 3 5 (by decide) (by decide) h3.ne' 7 (by decide) (by decide)
  have hne_34 : cross u (x 2 - x 5) ≠ 0 :=
    cross_ne_zero_of_facet_sign F 6 5 2 (by decide) (by decide) h6.ne 3 (by decide) (by decide)
  have hne_40 : cross u (x 1 - x 2) ≠ 0 :=
    cross_ne_zero_of_facet_sign F 5 2 1 (by decide) (by decide) h5.ne 2 (by decide) (by decide)
  exact fiveRim_of_signs F (u := u) rimP5 4 5 1 7 8 6 3 6 2 0
    (by decide) (by decide) hN0
    ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ ⟨h5, h1⟩
    ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ ⟨h7, h8⟩
    ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ ⟨h6, h3⟩
    ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ ⟨h6, h2⟩
    hne_01 hne_12 hne_23 hne_34 hne_40
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

theorem rho_omega_negP5 (ε : ℝ) {ρ : ℝ}
    (hc : StrictConvexK (fun i => x (rimP5 i)) ((x 0 - x 2) + ε • (x 2 - x 1)) ρ) :
    ρ * det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) < 0 := by
  have h := hc 4 1 (by decide) (by decide)
  have e : det3 (x (rimP5 (4 + 1)) - x (rimP5 4)) (x (rimP5 1) - x (rimP5 4)) ((x 0 - x 2) + ε • (x 2 - x 1)) =
      -det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) := by
    change det3 (x 1 - x 2) (x 6 - x 2) ((x 0 - x 2) + ε • (x 2 - x 1)) = _
    simp only [det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
  rw [e] at h
  have h1 : 0 < ρ * (-det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1)) := h
  by_contra hn; push Not at hn
  nlinarith

/-- **m1+ leaf, 5-rim case** (`⟪N8, x0 - x2⟫ > 0`): facet 012, rim `(1, 6, 3, 5, 2)` with middle `0` over the
chord `2 → 1`, view `u_ε = (x0 - x2) + ε (x2 - x1)` (`= u0(-1 + ε)`), `ε → 0+`; vertex `4` inside. -/
theorem m1p5_core (F : S0xFac 9 s0x_S24 x)
    (hN8 : 0 < ⟪F.N 8, x 0 - x 2⟫)
    (hU : (∃ t : ZMod 5, LexTop (fun i => x (rimP5 i)) (x 0 - x 2) (x 2 - x 1) t) ∨
      ∃ a c : ZMod 5, c ≠ a ∧ c ≠ a + 1 ∧
        LexDS (fun i => x (rimP5 i)) (-det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1)) (x 0 - x 2) (x 2 - x 1) a c)
    (hgen : ∀ i j : ZMod 5, i ≠ j →
      ⟪x (rimP5 i) - x (rimP5 j), x 0 - x 2⟫ ≠ 0 ∨ ⟪x (rimP5 i) - x (rimP5 j), x 2 - x 1⟫ ≠ 0)
    (w : ZMod 5) (hw : w = 1 ∨ w = 2 ∨ w = 3)
    (hfar : ∀ m : ZMod 5, m ≠ w → rimP5 m ∉ s0x_S24 0 → F.f 0 (x (rimP5 w)) < F.f 0 (x (rimP5 m)))
    (hoff : ⟪F.N 0, cross (x 1 - x 2) (x (rimP5 w) - x 2)⟫ ≠ 0 ∨
      ⟪x (rimP5 w) - x 2, x 1 - x 2⟫ < 0 ∨ ⟪x (rimP5 w) - x 1, x 2 - x 1⟫ < 0) :
    FaceChordView F 0 := by
  set b : ℝ³ := x 0 - x 2 with hb
  set c : ℝ³ := x 2 - x 1 with hc
  set Ω := det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) with hΩ
  set p : ZMod 5 → ℝ³ := fun i => x (rimP5 i) with hp
  have ev0 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  have evs := ev_signsP F
  have e8 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ⟪F.N 8, b + ε • c⟫ := evp' (F.N 8) b c (Or.inl hN8)
  have ev1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < 1 := by
    filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with ε h using h.2
  have hcvx : ∀ᶠ ε in 𝓝[>] (0 : ℝ), StrictConvexK p (b + ε • c) (-Ω) := by
    filter_upwards [evs, e8] with ε ⟨h1, h5, h7, h6, h3, h2, _⟩ h8
    obtain ⟨ρ, -, hcv, -⟩ := rim_dataP5 F (inner_N0_uP F ε) h1 h5 h7 h8 h6 h3 h2
    exact strictConvexK_of_rho (rho_omega_negP5 ε hcv) hcv
  have hinj := ev_injective_k b c p hgen
  have hZ : ∀ᶠ ε in 𝓝[>] (0 : ℝ), Function.Injective (fun i => ⟪p i, b + ε • c⟫) ∧
      UniOrSep p (b + ε • c) := by
    rcases hU with ⟨t, ht⟩ | ⟨a, c', hca, hca1, hd⟩
    · filter_upwards [ev_lexTop p b c t ht, hinj] with ε h hi
      exact ⟨hi, Or.inl (strictUnimodal_of_cyclic (by decide) (isCyclicUnimodal_of_top (by norm_num) hi t h))⟩
    · filter_upwards [ev_depthSepAt p (-Ω) b c a c' hca hca1 hcvx hd, hinj] with ε h hi
      exact ⟨hi, Or.inr ⟨a, c', h⟩⟩
  obtain ⟨ε, ⟨⟨h1, h5, h7, h6, h3, h2, -⟩, h8⟩, hε, h1lt, hinj', hz⟩ := ((evs.and e8).and (ev0.and (ev1.and hZ))).exists
  have hN0 := inner_N0_uP F ε
  obtain ⟨ρ, hρ, hcv, hin4⟩ := rim_dataP5 F hN0 h1 h5 h7 h8 h6 h3 h2
  have hε' : (0 : ℝ) < ε := hε
  have hw' : rimP5 w ∉ s0x_S24 0 := by rcases hw with rfl | rfl | rfl <;> decide
  refine ⟨b + ε • c, 5, inferInstance, rimP5, 4, w, ρ, hN0, by decide, by decide, by decide, hρ,
    hcv, ?_, ?_, hinj', hz, hw', hfar, hoff⟩
  · intro q hq0 hqr i
    have hq4 : q = 4 := by
      fin_cases q
      · exfalso; revert hq0; decide
      · exfalso; exact hqr 0 rfl
      · exfalso; exact hqr 4 rfl
      · exfalso; exact hqr 2 rfl
      · rfl
      · exfalso; exact hqr 3 rfl
      · exfalso; exact hqr 1 rfl
    subst hq4
    exact hin4 i
  · intro q hq0 hqr
    have hq0' : q = 0 := by
      fin_cases q
      · rfl
      · exfalso; exact hqr 0 rfl
      · exfalso; exact hqr 4 rfl
      · exfalso; revert hq0; decide
      · exfalso; revert hq0; decide
      · exfalso; revert hq0; decide
      · exfalso; revert hq0; decide
    subst hq0'
    refine ⟨ε, 1, hε', h1lt, one_ne_zero, ?_⟩
    · change x 0 = x 2 + ε • (x 1 - x 2) + (1 : ℝ) • ((x 0 - x 2) + ε • (x 2 - x 1))
      ext j
      simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
      ring


def rimP6 : ZMod 6 → Fin 7
  | 0 => 2
  | 1 => 1
  | 2 => 6
  | 3 => 4
  | 4 => 3
  | 5 => 5

theorem rho_omega_negP6 (ε : ℝ) {ρ : ℝ}
    (hc : StrictConvexK (fun i => x (rimP6 i)) ((x 0 - x 2) + ε • (x 2 - x 1)) ρ) :
    ρ * det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) < 0 := by
  have h := hc 0 2 (by decide) (by decide)
  have e : det3 (x (rimP6 (0 + 1)) - x (rimP6 0)) (x (rimP6 2) - x (rimP6 0)) ((x 0 - x 2) + ε • (x 2 - x 1)) =
      -det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) := by
    change det3 (x 1 - x 2) (x 6 - x 2) ((x 0 - x 2) + ε • (x 2 - x 1)) = _
    simp only [det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, PiLp.smul_apply, smul_eq_mul]; ring
  rw [e] at h
  have h1 : 0 < ρ * (-det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1)) := h
  by_contra hn; push Not at hn
  nlinarith

/-- Rim data for `(2, 1, 6, 4, 3, 5)` (`⟪N8, u⟫ < 0`). -/
theorem rim_dataP6 (F : S0xFac 9 s0x_S24 x) {u : ℝ³}
    (hN0 : ⟪F.N 0, u⟫ = 0) (h1 : 0 < ⟪F.N 1, u⟫) (h5 : ⟪F.N 5, u⟫ < 0) (h4 : 0 < ⟪F.N 4, u⟫)
    (h8 : ⟪F.N 8, u⟫ < 0) (h6 : ⟪F.N 6, u⟫ < 0) (h3 : 0 < ⟪F.N 3, u⟫) (h2 : 0 < ⟪F.N 2, u⟫) :
    ∃ ρ : ℝ, ρ ≠ 0 ∧ StrictConvexK (fun i => x (rimP6 i)) u ρ := by
  have n01 : cross u (x 1 - x 2) ≠ 0 :=
    cross_ne_zero_of_facet_sign F 5 2 1 (by decide) (by decide) h5.ne 2 (by decide) (by decide)
  have n12 : cross u (x 6 - x 1) ≠ 0 :=
    cross_ne_zero_of_facet_sign F 1 1 6 (by decide) (by decide) h1.ne' 0 (by decide) (by decide)
  have n23 : cross u (x 4 - x 6) ≠ 0 :=
    cross_ne_zero_of_facet_sign F 4 6 4 (by decide) (by decide) h4.ne' 1 (by decide) (by decide)
  have n34 : cross u (x 3 - x 4) ≠ 0 :=
    cross_ne_zero_of_facet_sign F 3 4 3 (by decide) (by decide) h3.ne' 4 (by decide) (by decide)
  have n45 : cross u (x 5 - x 3) ≠ 0 :=
    cross_ne_zero_of_facet_sign F 3 3 5 (by decide) (by decide) h3.ne' 8 (by decide) (by decide)
  have n50 : cross u (x 2 - x 5) ≠ 0 :=
    cross_ne_zero_of_facet_sign F 6 5 2 (by decide) (by decide) h6.ne 3 (by decide) (by decide)
  obtain ⟨σ0, hσ0n, hσ0⟩ := det3_sign_edgeOn F 0 2 1 (by decide) (by decide) u hN0 n01
  obtain ⟨σ1, -, hσ1⟩ := det3_sign_ridge F 5 1 1 6 ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ u ⟨h5, h1⟩ n12
  obtain ⟨σ2, -, hσ2⟩ := det3_sign_ridge F 8 4 6 4 ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ u ⟨h8, h4⟩ n23
  obtain ⟨σ3, -, hσ3⟩ := det3_sign_ridge F 8 3 4 3 ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ u ⟨h8, h3⟩ n34
  obtain ⟨σ4, -, hσ4⟩ := det3_sign_ridge F 6 3 3 5 ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ u ⟨h6, h3⟩ n45
  obtain ⟨σ5, -, hσ5⟩ := det3_sign_ridge F 6 2 5 2 ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ u ⟨h6, h2⟩ n50
  have c0 := Minimality.det3_cycle_triangle (x 2) (x 1) (x 6) u
  have c1 := Minimality.det3_cycle_triangle (x 1) (x 6) (x 4) u
  have c2 := Minimality.det3_cycle_triangle (x 6) (x 4) (x 3) u
  have c3 := Minimality.det3_cycle_triangle (x 4) (x 3) (x 5) u
  have c4 := Minimality.det3_cycle_triangle (x 3) (x 5) (x 2) u
  have p01 : 0 < σ0 * σ1 := sign_prod (hσ0 6 (by decide)) (by rw [c0]; exact hσ1 2 (by decide))
  have p12 : 0 < σ1 * σ2 := sign_prod (hσ1 4 (by decide)) (by rw [c1]; exact hσ2 1 (by decide))
  have p23 : 0 < σ2 * σ3 := sign_prod (hσ2 3 (by decide)) (by rw [c2]; exact hσ3 6 (by decide))
  have p34 : 0 < σ3 * σ4 := sign_prod (hσ3 5 (by decide)) (by rw [c3]; exact hσ4 4 (by decide))
  have p45 : 0 < σ4 * σ5 := sign_prod (hσ4 2 (by decide)) (by rw [c4]; exact hσ5 3 (by decide))
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
  · exact hσ0 6 (by decide)
  · exact hσ0 4 (by decide)
  · exact hσ0 3 (by decide)
  · exact hσ0 5 (by decide)
  · exact sign_transfer s01 (hσ1 2 (by decide))
  · exact False.elim (hj1 rfl)
  · exact False.elim (hj2 rfl)
  · exact sign_transfer s01 (hσ1 4 (by decide))
  · exact sign_transfer s01 (hσ1 3 (by decide))
  · exact sign_transfer s01 (hσ1 5 (by decide))
  · exact sign_transfer s02 (hσ2 2 (by decide))
  · exact sign_transfer s02 (hσ2 1 (by decide))
  · exact False.elim (hj1 rfl)
  · exact False.elim (hj2 rfl)
  · exact sign_transfer s02 (hσ2 3 (by decide))
  · exact sign_transfer s02 (hσ2 5 (by decide))
  · exact sign_transfer s03 (hσ3 2 (by decide))
  · exact sign_transfer s03 (hσ3 1 (by decide))
  · exact sign_transfer s03 (hσ3 6 (by decide))
  · exact False.elim (hj1 rfl)
  · exact False.elim (hj2 rfl)
  · exact sign_transfer s03 (hσ3 5 (by decide))
  · exact sign_transfer s04 (hσ4 2 (by decide))
  · exact sign_transfer s04 (hσ4 1 (by decide))
  · exact sign_transfer s04 (hσ4 6 (by decide))
  · exact sign_transfer s04 (hσ4 4 (by decide))
  · exact False.elim (hj1 rfl)
  · exact False.elim (hj2 rfl)
  · exact False.elim (hj2 rfl)
  · exact sign_transfer s05 (hσ5 1 (by decide))
  · exact sign_transfer s05 (hσ5 6 (by decide))
  · exact sign_transfer s05 (hσ5 4 (by decide))
  · exact sign_transfer s05 (hσ5 3 (by decide))
  · exact False.elim (hj1 rfl)

/-- **m1+ leaf, 6-rim case** (`⟪N8, x0 - x2⟫ < 0`): facet 012, rim `(2, 1, 6, 4, 3, 5)` with middle `0` over the
chord `2 → 1`, view `u_ε = (x0 - x2) + ε (x2 - x1)` (`= u0(-1 + ε)`), `ε → 0+`. Unimodal (`LexTop`) or
depth-separated (`LexDS`) rim at the base view `x0 - x2` with tilt `x2 - x1`. -/
theorem m1p6_core (F : S0xFac 9 s0x_S24 x)
    (hN8 : ⟪F.N 8, x 0 - x 2⟫ < 0)
    (hU : (∃ t : ZMod 6, LexTop (fun i => x (rimP6 i)) (x 0 - x 2) (x 2 - x 1) t) ∨
      ∃ a c : ZMod 6, c ≠ a ∧ c ≠ a + 1 ∧
        LexDS (fun i => x (rimP6 i)) (-det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1)) (x 0 - x 2) (x 2 - x 1) a c)
    (hgen : ∀ i j : ZMod 6, i ≠ j →
      ⟪x (rimP6 i) - x (rimP6 j), x 0 - x 2⟫ ≠ 0 ∨ ⟪x (rimP6 i) - x (rimP6 j), x 2 - x 1⟫ ≠ 0)
    (w : ZMod 6) (hw : w = 2 ∨ w = 3 ∨ w = 4 ∨ w = 5)
    (hfar : ∀ m : ZMod 6, m ≠ w → rimP6 m ∉ s0x_S24 0 → F.f 0 (x (rimP6 w)) < F.f 0 (x (rimP6 m)))
    (hoff : ⟪F.N 0, cross (x 1 - x 2) (x (rimP6 w) - x 2)⟫ ≠ 0 ∨
      ⟪x (rimP6 w) - x 2, x 1 - x 2⟫ < 0 ∨ ⟪x (rimP6 w) - x 1, x 2 - x 1⟫ < 0) :
    FaceChordView F 0 := by
  set b : ℝ³ := x 0 - x 2 with hb
  set c : ℝ³ := x 2 - x 1 with hc
  set Ω := det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) with hΩ
  set p : ZMod 6 → ℝ³ := fun i => x (rimP6 i) with hp
  have ev0 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  have evs := ev_signsP F
  have e8 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ⟪F.N 8, b + ε • c⟫ < 0 := evn' (F.N 8) b c (Or.inl hN8)
  have ev1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < 1 := by
    filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with ε h using h.2
  have hcvx : ∀ᶠ ε in 𝓝[>] (0 : ℝ), StrictConvexK p (b + ε • c) (-Ω) := by
    filter_upwards [evs, e8, ev0] with ε ⟨h1, h5, h7, h6, h3, h2, h4⟩ h8 hε
    obtain ⟨ρ, -, hcv⟩ := rim_dataP6 F (inner_N0_uP F ε) h1 h5 h4 h8 h6 h3 h2
    exact strictConvexK_of_rho (rho_omega_negP6 ε hcv) hcv
  have hinj := ev_injective_k b c p hgen
  have hZ : ∀ᶠ ε in 𝓝[>] (0 : ℝ), Function.Injective (fun i => ⟪p i, b + ε • c⟫) ∧
      UniOrSep p (b + ε • c) := by
    rcases hU with ⟨t, ht⟩ | ⟨a, c', hca, hca1, hd⟩
    · filter_upwards [ev_lexTop p b c t ht, hinj] with ε h hi
      exact ⟨hi, Or.inl (strictUnimodal_of_cyclic (by decide) (isCyclicUnimodal_of_top (by norm_num) hi t h))⟩
    · filter_upwards [ev_depthSepAt p (-Ω) b c a c' hca hca1 hcvx hd, hinj] with ε h hi
      exact ⟨hi, Or.inr ⟨a, c', h⟩⟩
  obtain ⟨ε, ⟨⟨h1, h5, h7, h6, h3, h2, h4⟩, h8⟩, hε, h1lt, hinj', hz⟩ := ((evs.and e8).and (ev0.and (ev1.and hZ))).exists
  have hN0 := inner_N0_uP F ε
  obtain ⟨ρ, hρ, hcv⟩ := rim_dataP6 F hN0 h1 h5 h4 h8 h6 h3 h2
  have hε' : (0 : ℝ) < ε := hε
  have hw' : rimP6 w ∉ s0x_S24 0 := by rcases hw with rfl | rfl | rfl | rfl <;> decide
  refine ⟨b + ε • c, 6, inferInstance, rimP6, 0, w, ρ, hN0, by decide, by decide, by decide, hρ,
    hcv, ?_, ?_, hinj', hz, hw', hfar, hoff⟩
  · intro q hq0 hqr i
    exfalso
    fin_cases q
    · revert hq0; decide
    · exact hqr 1 rfl
    · exact hqr 0 rfl
    · exact hqr 4 rfl
    · exact hqr 3 rfl
    · exact hqr 5 rfl
    · exact hqr 2 rfl
  · intro q hq0 hqr
    have hq0' : q = 0 := by
      fin_cases q
      · rfl
      · exfalso; exact hqr 1 rfl
      · exfalso; exact hqr 0 rfl
      · exfalso; revert hq0; decide
      · exfalso; revert hq0; decide
      · exfalso; revert hq0; decide
      · exfalso; revert hq0; decide
    subst hq0'
    refine ⟨ε, 1, hε', h1lt, one_ne_zero, ?_⟩
    change x 0 = x 2 + ε • (x 1 - x 2) + (1 : ℝ) • ((x 0 - x 2) + ε • (x 2 - x 1))
    ext j
    simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
    ring



end Minimality.T24.R012
