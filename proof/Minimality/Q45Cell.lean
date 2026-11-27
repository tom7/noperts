module

public import Minimality.Q45Leaf
public import Minimality.RimCellClosed
public import Minimality.EdgeTiltBD
public import Minimality.EdgeViewLink
public import Minimality.DiagCross
public import Minimality.CornerU
public import Minimality.ClosedCellLex


@[expose] public section

set_option autoImplicit true
set_option relaxedAutoImplicit true
open scoped RealInnerProductSpace Topology
open Filter Finset
open Minimality Minimality.H21 Minimality.FaceChord Minimality.T24.SAT Minimality.RimFromSigns
open Minimality.T24.Q45 Minimality.RimCell Minimality.EdgeViewLink Minimality.EdgeTilt

namespace Minimality.T24.Q45

lemma N3_ne {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : F.N 3 ≠ 0 := by
  intro h0
  have := F.inner_sub 3 1 0
  rw [h0, inner_zero_left, F.zero 3 0 (by decide)] at this
  have h1 := F.neg 3 1 (by decide)
  linarith

lemma N3_self {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : 0 < ⟪F.N 3, F.N 3⟫ :=
  real_inner_self_pos.2 (N3_ne F)

lemma ev_lex_pos (v b d : ℝ³) (h : 0 < ⟪v, b⟫ ∨ (⟪v, b⟫ = 0 ∧ 0 < ⟪v, d⟫)) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ⟪v, b + ε • d⟫ := by
  have := Minimality.eventually_pos_affine (A := ⟪v, b⟫) (B := ⟪v, d⟫) h
  filter_upwards [this] with ε hε
  rw [inner_add_right, inner_smul_right]; exact hε

lemma diag_neg_of {p : ZMod 4 → ℝ³} {u : ℝ³} {l k : ZMod 4}
    (hl : l ∈ ({0, 2} : Finset (ZMod 4))) (hk : k ∈ ({1, 3} : Finset (ZMod 4)))
    (h : ⟪p l, u⟫ < ⟪p k, u⟫) : ∃ pr ∈ diagPairs, ⟪p pr.1 - p pr.2, u⟫ < 0 :=
  ⟨(l, k), Finset.mem_product.2 ⟨hl, hk⟩, by rw [inner_sub_left]; linarith⟩

lemma diag_pos_of {p : ZMod 4 → ℝ³} {u : ℝ³} {l k : ZMod 4}
    (hl : l ∈ ({0, 2} : Finset (ZMod 4))) (hk : k ∈ ({1, 3} : Finset (ZMod 4)))
    (h : ⟪p k, u⟫ < ⟪p l, u⟫) : ∃ pr ∈ diagPairs, 0 < ⟪p pr.1 - p pr.2, u⟫ :=
  ⟨(l, k), Finset.mem_product.2 ⟨hl, hk⟩, by rw [inner_sub_left]; linarith⟩

lemma diag_pos_of_not_low (p : ZMod 4 → ℝ³) (u : ℝ³) {ρ : ℝ}
    (hcyc : ∀ i, 0 < ρ * triD p u i) (hk : 0 < ρ * det3 (p 2 - p 0) (p 3 - p 1) (p 0 - p 1)) :
    ∃ pr ∈ diagPairs, 0 < ⟪p pr.1 - p pr.2, u⟫ := by
  have h := hp_of_min_lt_max (z := fun i => ⟪p i, u⟫)
    (min_lt_max_of_not_le (diagCross_not_low p u hcyc hk))
  rcases h with h | h | h | h
  · exact diag_pos_of (l := 0) (by decide) (by decide) h
  · exact diag_pos_of (l := 0) (k := 3) (by decide) (by decide) h
  · exact diag_pos_of (l := 2) (k := 1) (by decide) (by decide) h
  · exact diag_pos_of (l := 2) (k := 3) (by decide) (by decide) h

lemma diag_neg_of_not_high (p : ZMod 4 → ℝ³) (u : ℝ³) {ρ : ℝ}
    (hcyc : ∀ i, 0 < ρ * triD p u i) (hk : ρ * det3 (p 2 - p 0) (p 3 - p 1) (p 0 - p 1) < 0) :
    ∃ pr ∈ diagPairs, ⟪p pr.1 - p pr.2, u⟫ < 0 := by
  have h := hn_of_min_lt_max (z := fun i => ⟪p i, u⟫)
    (min_lt_max_of_not_le (diagCross_not_high p u hcyc hk))
  rcases h with h | h | h | h
  · exact diag_neg_of (l := 0) (k := 1) (by decide) (by decide) h
  · exact diag_neg_of (l := 0) (k := 3) (by decide) (by decide) h
  · exact diag_neg_of (l := 2) (k := 1) (by decide) (by decide) h
  · exact diag_neg_of (l := 2) (k := 3) (by decide) (by decide) h

lemma triD_of_cyc (p : ZMod 4 → ℝ³) (u : ℝ³) (ρ : ℝ)
    (hcyc : ∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
      0 < ρ * det3 (p (i + 1) - p i) (p j - p i) u) (i : ZMod 4) : 0 < ρ * triD p u i := by
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

lemma rho_om_neg {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) {u : ℝ³} {ρ : ℝ}
    (hin3 : 0 < ρ * det3 (x 6 - x 2) (x 1 - x 2) u) (hN5 : 0 < ⟪F.N 5, u⟫) :
    ρ * det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) < 0 := by
  have h := rimOrient F u ρ hin3
  set Ω := det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1)
  nlinarith [h, hN5]

lemma rk_pos {ρ Ω κ : ℝ} (h1 : ρ * Ω < 0) (h2 : Ω * κ < 0) : 0 < ρ * κ := by
  have hprod : 0 < (ρ * Ω) * (Ω * κ) := mul_pos_of_neg_of_neg h1 h2
  have : (ρ * Ω) * (Ω * κ) = Ω ^ 2 * (ρ * κ) := by ring
  rw [this] at hprod
  exact pos_of_mul_pos_right hprod (sq_nonneg Ω)

lemma rk_neg {ρ Ω κ : ℝ} (h1 : ρ * Ω < 0) (h2 : 0 < Ω * κ) : ρ * κ < 0 := by
  have hprod : (ρ * Ω) * (Ω * κ) < 0 := mul_neg_of_neg_of_pos h1 h2
  have : (ρ * Ω) * (Ω * κ) = Ω ^ 2 * (ρ * κ) := by ring
  rw [this] at hprod
  exact neg_of_mul_neg_right hprod (sq_nonneg Ω)

private lemma inj_quad {a b c d : Fin 7} (h : a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d) :
    Function.Injective (quad a b c d) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> first | rfl | exact absurd hij (by simp [quad]; tauto)

/-- Cells of the four corner leaves (Lean orientation). -/
def UB1 : Finset (Fin 9) := {0, 4, 5}
def DB1 : Finset (Fin 9) := {2, 3, 7, 8}
theorem cycB1 : S0xCycUD s0x_S24 (quad 6 4 0 2) UB1 DB1 := by decide

/-- The corner cell `B1` as a lex cell (`lexAny_of_closedCell_q4`); `q45_B1_cell` is its Rupert corollary. -/
theorem q45_B1_cell_lex {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (ha5 : ⟪F.N 5, x 5 - x 0⟫ < 0)
    (s t : ℝ) (hs0 : 0 < s) (ht : 0 < t) (hst : 1 < s + t)
    (hdecomp : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0))
    (hs1 : s < 1)
    (hlex : ∃ i ∈ ({4, 2} : Finset (Fin 7)), ∃ j ∈ ({6, 0} : Finset (Fin 7)),
      ⟪x i - x j, x 5 - x 0⟫ < 0 ∨ (⟪x i - x j, x 5 - x 0⟫ = 0 ∧ 0 < ⟪x i - x j, x 4 - x 0⟫)) :
    Gen.LexAny F := by
  have hx := inj_of_fac24 F
  have ev_lex : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ i ∈ ({4, 2} : Finset (Fin 7)), ∃ j ∈ ({6, 0} : Finset (Fin 7)),
      0 < ⟪x i - x j, u_B1 x ε⟫ := by
    obtain ⟨i, hi, j, hj, h⟩ := hlex
    have hb : 0 < ⟪x i - x j, -(x 5 - x 0)⟫ ∨ (⟪x i - x j, -(x 5 - x 0)⟫ = 0 ∧ 0 < ⟪x i - x j, x 4 - x 0⟫) := by
      simp only [inner_neg_right]
      rcases h with h | ⟨h1, h2⟩
      · exact Or.inl (by linarith)
      · exact Or.inr ⟨by linarith, h2⟩
    filter_upwards [ev_lex_pos _ _ _ hb] with ε hε
    refine ⟨i, hi, j, hj, ?_⟩
    have hu : u_B1 x ε = -(x 5 - x 0) + ε • (x 4 - x 0) := by
      dsimp [u_B1]; abel
    rw [hu]; exact hε
  obtain ⟨ε, hsig, i, hi, j, hj, hlexε⟩ :=
    ((eventually_signs_B1 F ha5 s t hs0 ht hst hdecomp hs1).and ev_lex).exists
  obtain ⟨hN3, hN4, hN8, hN0, hN2, hN7, hN5⟩ := hsig
  set u := u_B1 x ε with hu
  obtain ⟨ρ, -, hcyc, hin⟩ := rim6402_of_signs F hN3 hN4 hN8 hN0 hN2 hN7 hN5
  set p := quad (x 6) (x 4) (x 0) (x 2) with hp
  have hr : ∀ k : ZMod 4, x (quad 6 4 0 2 k) = p k := by intro k; fin_cases k <;> rfl
  have hin3 := hin 3
  have h3_eq : quad (x 6) (x 4) (x 0) (x 2) (3 + 1) - quad (x 6) (x 4) (x 0) (x 2) 3 = x 6 - x 2 := rfl
  have h3_1 : x 1 - quad (x 6) (x 4) (x 0) (x 2) 3 = x 1 - x 2 := rfl
  rw [h3_eq, h3_1] at hin3
  have hρΩ := rho_om_neg F hin3 hN5
  have hΩκ : det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) *
      det3 (p 2 - p 0) (p 3 - p 1) (p 0 - p 1) < 0 := by
    have h4 := omega_mul_det3_0246_pos_unconditional F
    have hk := kappa_rim6402 x
    rw [hp]; rw [hk]; linarith [h4]
  have hk_pos := rk_pos hρΩ hΩκ
  have hTD := triD_of_cyc p u ρ hcyc
  -- hp: positive diagonal form from Lemma K
  obtain ⟨pp, hpp, hpos⟩ := diag_pos_of_not_low p u hTD hk_pos
  -- hn: from the lex inequality
  have hI : ∀ q ∈ ({4, 2} : Finset (Fin 7)), ∃ k ∈ ({1, 3} : Finset (ZMod 4)), quad 6 4 0 2 k = q := by
    decide
  have hJ : ∀ q ∈ ({6, 0} : Finset (Fin 7)), ∃ k ∈ ({0, 2} : Finset (ZMod 4)), quad 6 4 0 2 k = q := by
    decide
  obtain ⟨k, hk, hkq⟩ := hI i hi
  obtain ⟨l, hl, hlq⟩ := hJ j hj
  have hn : ∃ pr ∈ diagPairs, ⟪x (quad 6 4 0 2 pr.1) - x (quad 6 4 0 2 pr.2), u⟫ < 0 := by
    refine ⟨(l, k), Finset.mem_product.2 ⟨hl, hk⟩, ?_⟩
    simp only
    rw [hkq, hlq]
    rw [inner_sub_left] at hlexε ⊢; linarith
  have hp' : ∃ pr ∈ diagPairs, 0 < ⟪x (quad 6 4 0 2 pr.1) - x (quad 6 4 0 2 pr.2), u⟫ := by
    refine ⟨pp, hpp, ?_⟩
    rw [hr, hr]; exact hpos
  -- the cell
  have hN3s := N3_self F
  have hnU : ∀ t ∈ UB1, 0 < ⟪F.N t, u⟫ ∨ (⟪F.N t, u⟫ = 0 ∧ 0 < ⟪F.N t, -F.N 3⟫) := by
    intro t ht; simp only [UB1, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl
    exacts [Or.inl hN0, Or.inl hN4, Or.inl hN5]
  have hnD : ∀ t ∈ DB1, ⟪F.N t, u⟫ < 0 ∨ (⟪F.N t, u⟫ = 0 ∧ ⟪F.N t, -F.N 3⟫ < 0) := by
    intro t ht; simp only [DB1, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · exact Or.inl hN2
    · exact Or.inr ⟨hN3, by rw [inner_neg_right]; linarith⟩
    · exact Or.inl hN7
    · exact Or.inl hN8
  obtain ⟨e', he'⟩ := (ev_cellAt_tilt F hnU hnD).exists
  have hcl : CellLe F UB1 DB1 u := by
    refine ⟨fun t ht => ?_, fun t ht => ?_⟩
    · rcases hnU t ht with h | ⟨h, -⟩
      · exact h.le
      · exact h.ge
    · rcases hnD t ht with h | ⟨h, -⟩
      · exact h.le
      · exact h.le
  exact lexAny_of_closedCell_q4 F hx (inj_quad (by decide)) cycB1 he' hcl hcl hn hp'

theorem q45_B1_cell {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (ha5 : ⟪F.N 5, x 5 - x 0⟫ < 0)
    (s t : ℝ) (hs0 : 0 < s) (ht : 0 < t) (hst : 1 < s + t)
    (hdecomp : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0))
    (hs1 : s < 1)
    (hlex : ∃ i ∈ ({4, 2} : Finset (Fin 7)), ∃ j ∈ ({6, 0} : Finset (Fin 7)),
      ⟪x i - x j, x 5 - x 0⟫ < 0 ∨ (⟪x i - x j, x 5 - x 0⟫ = 0 ∧ 0 < ⟪x i - x j, x 4 - x 0⟫)) :
    IsRupert (univ.image x) :=
  Gen.lexAny_isRupert F (inj_of_fac24 F) (q45_B1_cell_lex F ha5 s t hs0 ht hst hdecomp hs1 hlex)

def UB2 : Finset (Fin 9) := {2, 3, 5, 8}
def DB2 : Finset (Fin 9) := {6, 7}
theorem cycB2 : S0xCycUD s0x_S24 (quad 6 3 5 2) UB2 DB2 := by decide
def UC1 : Finset (Fin 9) := {1, 2, 5}
def DC1 : Finset (Fin 9) := {3, 4, 6, 7}
theorem cycC1 : S0xCycUD s0x_S24 (quad 6 0 5 2) UC1 DC1 := by decide
def UC2 : Finset (Fin 9) := {3, 4, 5, 6}
def DC2 : Finset (Fin 9) := {7, 8}
theorem cycC2 : S0xCycUD s0x_S24 (quad 6 4 3 2) UC2 DC2 := by decide

/-- The corner cell `B2` as a lex cell (`lexAny_of_closedCell_q4`); `q45_B2_cell` is its Rupert corollary. -/
theorem q45_B2_cell_lex {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (ha34 : ⟪F.N 5, x 3 - x 4⟫ < 0)
    (s t : ℝ) (ht : 0 < t)
    (hdecomp : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0))
    (hs1 : 1 < s)
    (hlex : ∃ i ∈ ({3, 2} : Finset (Fin 7)), ∃ j ∈ ({6, 5} : Finset (Fin 7)),
      ⟪x i - x j, x 3 - x 4⟫ < 0 ∨ (⟪x i - x j, x 3 - x 4⟫ = 0 ∧ ⟪x i - x j, x 5 - x 0⟫ < 0)) :
    Gen.LexAny F := by
  have hx := inj_of_fac24 F
  have hu_bd : ∀ ε, u_B2 x s t ε = -(x 3 - x 4) + ε • (-(x 5 - x 0)) := by
    intro ε
    have h34 : x 3 - x 4 = (s - 1) • (x 4 - x 0) + t • (x 5 - x 0) := by
      rw [show x 3 - x 4 = (x 3 - x 0) - (x 4 - x 0) by abel, hdecomp]; module
    dsimp [u_B2]; rw [h34]; module
  have ev_lex : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ i ∈ ({3, 2} : Finset (Fin 7)), ∃ j ∈ ({6, 5} : Finset (Fin 7)),
      0 < ⟪x i - x j, u_B2 x s t ε⟫ := by
    obtain ⟨i, hi, j, hj, h⟩ := hlex
    have hb : 0 < ⟪x i - x j, -(x 3 - x 4)⟫ ∨
        (⟪x i - x j, -(x 3 - x 4)⟫ = 0 ∧ 0 < ⟪x i - x j, -(x 5 - x 0)⟫) := by
      simp only [inner_neg_right]
      rcases h with h | ⟨h1, h2⟩
      · exact Or.inl (by linarith)
      · exact Or.inr ⟨by linarith, by linarith⟩
    filter_upwards [ev_lex_pos _ _ _ hb] with ε hε
    refine ⟨i, hi, j, hj, ?_⟩
    rw [hu_bd]; exact hε
  obtain ⟨ε, hsig, i, hi, j, hj, hlexε⟩ :=
    ((eventually_signs_B2 F ha34 s t hs1 ht hdecomp).and ev_lex).exists
  obtain ⟨hN3, hN7, hN8, hN6, hN2, hN5⟩ := hsig
  set u := u_B2 x s t ε with hu
  obtain ⟨ρ, -, hcyc, hin⟩ := rim6352_of_signs F hN3 hN7 hN8 hN6 hN2 hN5
  set p := quad (x 6) (x 3) (x 5) (x 2) with hp
  have hr : ∀ k : ZMod 4, x (quad 6 3 5 2 k) = p k := by intro k; fin_cases k <;> rfl
  have hin3 := hin 3
  have h3_eq : quad (x 6) (x 3) (x 5) (x 2) (3 + 1) - quad (x 6) (x 3) (x 5) (x 2) 3 = x 6 - x 2 := rfl
  have h3_1 : x 1 - quad (x 6) (x 3) (x 5) (x 2) 3 = x 1 - x 2 := rfl
  rw [h3_eq, h3_1] at hin3
  have hρΩ := rho_om_neg F hin3 hN5
  have hΩκ : det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) *
      det3 (p 2 - p 0) (p 3 - p 1) (p 0 - p 1) < 0 := by
    have h4 := omega_mul_det3_2356_pos_unconditional F
    have hk := kappa_rim6352 x
    rw [hp]; rw [hk]; linarith [h4]
  have hk_pos := rk_pos hρΩ hΩκ
  have hTD := triD_of_cyc p u ρ hcyc
  obtain ⟨pp, hpp, hpos⟩ := diag_pos_of_not_low p u hTD hk_pos
  have hI : ∀ q ∈ ({3, 2} : Finset (Fin 7)), ∃ k ∈ ({1, 3} : Finset (ZMod 4)), quad 6 3 5 2 k = q := by
    decide
  have hJ : ∀ q ∈ ({6, 5} : Finset (Fin 7)), ∃ k ∈ ({0, 2} : Finset (ZMod 4)), quad 6 3 5 2 k = q := by
    decide
  obtain ⟨k, hk, hkq⟩ := hI i hi
  obtain ⟨l, hl, hlq⟩ := hJ j hj
  have hn : ∃ pr ∈ diagPairs, ⟪x (quad 6 3 5 2 pr.1) - x (quad 6 3 5 2 pr.2), u⟫ < 0 := by
    refine ⟨(l, k), Finset.mem_product.2 ⟨hl, hk⟩, ?_⟩
    simp only
    rw [hkq, hlq]
    rw [inner_sub_left] at hlexε ⊢; linarith
  have hp' : ∃ pr ∈ diagPairs, 0 < ⟪x (quad 6 3 5 2 pr.1) - x (quad 6 3 5 2 pr.2), u⟫ := by
    refine ⟨pp, hpp, ?_⟩
    rw [hr, hr]; exact hpos
  have hN3s := N3_self F
  have hnU : ∀ t ∈ UB2, 0 < ⟪F.N t, u⟫ ∨ (⟪F.N t, u⟫ = 0 ∧ 0 < ⟪F.N t, F.N 3⟫) := by
    intro t ht; simp only [UB2, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · exact Or.inl hN2
    · exact Or.inr ⟨hN3, hN3s⟩
    · exact Or.inl hN5
    · exact Or.inl hN8
  have hnD : ∀ t ∈ DB2, ⟪F.N t, u⟫ < 0 ∨ (⟪F.N t, u⟫ = 0 ∧ ⟪F.N t, F.N 3⟫ < 0) := by
    intro t ht; simp only [DB2, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl
    · exact Or.inl hN6
    · exact Or.inl hN7
  obtain ⟨e', he'⟩ := (ev_cellAt_tilt F hnU hnD).exists
  have hcl : CellLe F UB2 DB2 u := by
    refine ⟨fun t ht => ?_, fun t ht => ?_⟩
    · rcases hnU t ht with h | ⟨h, -⟩
      · exact h.le
      · exact h.ge
    · rcases hnD t ht with h | ⟨h, -⟩
      · exact h.le
      · exact h.le
  exact lexAny_of_closedCell_q4 F hx (inj_quad (by decide)) cycB2 he' hcl hcl hn hp'

theorem q45_B2_cell {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (ha34 : ⟪F.N 5, x 3 - x 4⟫ < 0)
    (s t : ℝ) (ht : 0 < t)
    (hdecomp : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0))
    (hs1 : 1 < s)
    (hlex : ∃ i ∈ ({3, 2} : Finset (Fin 7)), ∃ j ∈ ({6, 5} : Finset (Fin 7)),
      ⟪x i - x j, x 3 - x 4⟫ < 0 ∨ (⟪x i - x j, x 3 - x 4⟫ = 0 ∧ ⟪x i - x j, x 5 - x 0⟫ < 0)) :
    IsRupert (univ.image x) :=
  Gen.lexAny_isRupert F (inj_of_fac24 F) (q45_B2_cell_lex F ha34 s t ht hdecomp hs1 hlex)

/-- The corner cell `C1` as a lex cell (`lexAny_of_closedCell_q4`); `q45_C1_cell` is its Rupert corollary. -/
theorem q45_C1_cell_lex {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (ha4 : ⟪F.N 5, x 4 - x 0⟫ < 0)
    (s t : ℝ) (hs0 : 0 < s) (ht : 0 < t) (hst : 1 < s + t)
    (hdecomp : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0))
    (ht1 : t < 1)
    (hlex : ∃ i ∈ ({6, 5} : Finset (Fin 7)), ∃ j ∈ ({0, 2} : Finset (Fin 7)),
      ⟪x i - x j, x 4 - x 0⟫ < 0 ∨ (⟪x i - x j, x 4 - x 0⟫ = 0 ∧ 0 < ⟪x i - x j, x 5 - x 0⟫)) :
    Gen.LexAny F := by
  have hx := inj_of_fac24 F
  have ev_lex : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ i ∈ ({6, 5} : Finset (Fin 7)), ∃ j ∈ ({0, 2} : Finset (Fin 7)),
      0 < ⟪x i - x j, u_C1 x ε⟫ := by
    obtain ⟨i, hi, j, hj, h⟩ := hlex
    have hb : 0 < ⟪x i - x j, -(x 4 - x 0)⟫ ∨
        (⟪x i - x j, -(x 4 - x 0)⟫ = 0 ∧ 0 < ⟪x i - x j, x 5 - x 0⟫) := by
      simp only [inner_neg_right]
      rcases h with h | ⟨h1, h2⟩
      · exact Or.inl (by linarith)
      · exact Or.inr ⟨by linarith, h2⟩
    filter_upwards [ev_lex_pos _ _ _ hb] with ε hε
    refine ⟨i, hi, j, hj, ?_⟩
    have hu : u_C1 x ε = -(x 4 - x 0) + ε • (x 5 - x 0) := by
      dsimp [u_C1]; abel
    rw [hu]; exact hε
  obtain ⟨ε, hsig, i, hi, j, hj, hlexε⟩ :=
    ((eventually_signs_C1 F ha4 s t hs0 ht hst ht1 hdecomp).and ev_lex).exists
  obtain ⟨hN3, hN4, hN1, hN6, hN2, hN7, hN5⟩ := hsig
  set u := u_C1 x ε with hu
  obtain ⟨ρ, -, hcyc, hin⟩ := rim6052_canonical_of_signs F hN3 hN4 hN1 hN6 hN2 hN7 hN5
  set p := quad (x 6) (x 0) (x 5) (x 2) with hp
  have hr : ∀ k : ZMod 4, x (quad 6 0 5 2 k) = p k := by intro k; fin_cases k <;> rfl
  have hin3 := hin 3
  have h3_eq : quad (x 6) (x 0) (x 5) (x 2) (3 + 1) - quad (x 6) (x 0) (x 5) (x 2) 3 = x 6 - x 2 := rfl
  have h3_1 : x 1 - quad (x 6) (x 0) (x 5) (x 2) 3 = x 1 - x 2 := rfl
  rw [h3_eq, h3_1] at hin3
  have hρΩ := rho_om_neg F hin3 hN5
  have hΩκ : 0 < det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) *
      det3 (p 2 - p 0) (p 3 - p 1) (p 0 - p 1) := by
    have h4 := omega_mul_det3_0256_pos_unconditional F
    have hk := kappa_rim6052_canonical x
    rw [hp]; rw [hk]; exact h4
  have hk_neg := rk_neg hρΩ hΩκ
  have hTD := triD_of_cyc p u ρ hcyc
  obtain ⟨pn, hpn, hneg⟩ := diag_neg_of_not_high p u hTD hk_neg
  have hI : ∀ q ∈ ({6, 5} : Finset (Fin 7)), ∃ k ∈ ({0, 2} : Finset (ZMod 4)), quad 6 0 5 2 k = q := by
    decide
  have hJ : ∀ q ∈ ({0, 2} : Finset (Fin 7)), ∃ k ∈ ({1, 3} : Finset (ZMod 4)), quad 6 0 5 2 k = q := by
    decide
  obtain ⟨k, hk, hkq⟩ := hI i hi
  obtain ⟨l, hl, hlq⟩ := hJ j hj
  have hp' : ∃ pr ∈ diagPairs, 0 < ⟪x (quad 6 0 5 2 pr.1) - x (quad 6 0 5 2 pr.2), u⟫ := by
    refine ⟨(k, l), Finset.mem_product.2 ⟨hk, hl⟩, ?_⟩
    simp only
    rw [hkq, hlq]; exact hlexε
  have hn : ∃ pr ∈ diagPairs, ⟪x (quad 6 0 5 2 pr.1) - x (quad 6 0 5 2 pr.2), u⟫ < 0 := by
    refine ⟨pn, hpn, ?_⟩
    rw [hr, hr]; exact hneg
  have hN3s := N3_self F
  have hnU : ∀ t ∈ UC1, 0 < ⟪F.N t, u⟫ ∨ (⟪F.N t, u⟫ = 0 ∧ 0 < ⟪F.N t, -F.N 3⟫) := by
    intro t ht; simp only [UC1, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl
    exacts [Or.inl hN1, Or.inl hN2, Or.inl hN5]
  have hnD : ∀ t ∈ DC1, ⟪F.N t, u⟫ < 0 ∨ (⟪F.N t, u⟫ = 0 ∧ ⟪F.N t, -F.N 3⟫ < 0) := by
    intro t ht; simp only [DC1, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · exact Or.inr ⟨hN3, by rw [inner_neg_right]; linarith⟩
    · exact Or.inl hN4
    · exact Or.inl hN6
    · exact Or.inl hN7
  obtain ⟨e', he'⟩ := (ev_cellAt_tilt F hnU hnD).exists
  have hcl : CellLe F UC1 DC1 u := by
    refine ⟨fun t ht => ?_, fun t ht => ?_⟩
    · rcases hnU t ht with h | ⟨h, -⟩
      · exact h.le
      · exact h.ge
    · rcases hnD t ht with h | ⟨h, -⟩
      · exact h.le
      · exact h.le
  exact lexAny_of_closedCell_q4 F hx (inj_quad (by decide)) cycC1 he' hcl hcl hn hp'

theorem q45_C1_cell {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (ha4 : ⟪F.N 5, x 4 - x 0⟫ < 0)
    (s t : ℝ) (hs0 : 0 < s) (ht : 0 < t) (hst : 1 < s + t)
    (hdecomp : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0))
    (ht1 : t < 1)
    (hlex : ∃ i ∈ ({6, 5} : Finset (Fin 7)), ∃ j ∈ ({0, 2} : Finset (Fin 7)),
      ⟪x i - x j, x 4 - x 0⟫ < 0 ∨ (⟪x i - x j, x 4 - x 0⟫ = 0 ∧ 0 < ⟪x i - x j, x 5 - x 0⟫)) :
    IsRupert (univ.image x) :=
  Gen.lexAny_isRupert F (inj_of_fac24 F) (q45_C1_cell_lex F ha4 s t hs0 ht hst hdecomp ht1 hlex)

/-- The corner cell `C2` as a lex cell (`lexAny_of_closedCell_q4`); `q45_C2_cell` is its Rupert corollary. -/
theorem q45_C2_cell_lex {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (ha35 : ⟪F.N 5, x 3 - x 5⟫ < 0)
    (s t : ℝ) (hs0 : 0 < s)
    (hdecomp : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0))
    (ht1 : 1 < t)
    (hlex : ∃ i ∈ ({6, 3} : Finset (Fin 7)), ∃ j ∈ ({4, 2} : Finset (Fin 7)),
      ⟪x i - x j, x 3 - x 5⟫ < 0 ∨ (⟪x i - x j, x 3 - x 5⟫ = 0 ∧ ⟪x i - x j, x 4 - x 0⟫ < 0)) :
    Gen.LexAny F := by
  have hx := inj_of_fac24 F
  have hu_bd : ∀ ε, u_C2 x s t ε = -(x 3 - x 5) + ε • (-(x 4 - x 0)) := by
    intro ε
    have h35 : x 3 - x 5 = s • (x 4 - x 0) + (t - 1) • (x 5 - x 0) := by
      rw [show x 3 - x 5 = (x 3 - x 0) - (x 5 - x 0) by abel, hdecomp]; module
    dsimp [u_C2]; rw [h35]; module
  have ev_lex : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ i ∈ ({6, 3} : Finset (Fin 7)), ∃ j ∈ ({4, 2} : Finset (Fin 7)),
      0 < ⟪x i - x j, u_C2 x s t ε⟫ := by
    obtain ⟨i, hi, j, hj, h⟩ := hlex
    have hb : 0 < ⟪x i - x j, -(x 3 - x 5)⟫ ∨
        (⟪x i - x j, -(x 3 - x 5)⟫ = 0 ∧ 0 < ⟪x i - x j, -(x 4 - x 0)⟫) := by
      simp only [inner_neg_right]
      rcases h with h | ⟨h1, h2⟩
      · exact Or.inl (by linarith)
      · exact Or.inr ⟨by linarith, by linarith⟩
    filter_upwards [ev_lex_pos _ _ _ hb] with ε hε
    refine ⟨i, hi, j, hj, ?_⟩
    rw [hu_bd]; exact hε
  obtain ⟨ε, hsig, i, hi, j, hj, hlexε⟩ :=
    ((eventually_signs_C2 F ha35 s t hs0 ht1 hdecomp).and ev_lex).exists
  obtain ⟨hN3, hN8, hN4, hN7, hN6, hN5⟩ := hsig
  set u := u_C2 x s t ε with hu
  obtain ⟨ρ, -, hcyc, hin⟩ := rim6432_of_signs F hN3 hN8 hN4 hN7 hN6 hN5
  set p := quad (x 6) (x 4) (x 3) (x 2) with hp
  have hr : ∀ k : ZMod 4, x (quad 6 4 3 2 k) = p k := by intro k; fin_cases k <;> rfl
  have hin3 := hin 3
  have h3_eq : quad (x 6) (x 4) (x 3) (x 2) (3 + 1) - quad (x 6) (x 4) (x 3) (x 2) 3 = x 6 - x 2 := rfl
  have h3_1 : x 1 - quad (x 6) (x 4) (x 3) (x 2) 3 = x 1 - x 2 := rfl
  rw [h3_eq, h3_1] at hin3
  have hρΩ := rho_om_neg F hin3 hN5
  have hΩκ : 0 < det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) *
      det3 (p 2 - p 0) (p 3 - p 1) (p 0 - p 1) := by
    have h4 := omega_mul_det3_2346_pos_unconditional F
    have hk := kappa_rim6432 x
    rw [hp]; rw [hk]; exact h4
  have hk_neg := rk_neg hρΩ hΩκ
  have hTD := triD_of_cyc p u ρ hcyc
  obtain ⟨pn, hpn, hneg⟩ := diag_neg_of_not_high p u hTD hk_neg
  have hI : ∀ q ∈ ({6, 3} : Finset (Fin 7)), ∃ k ∈ ({0, 2} : Finset (ZMod 4)), quad 6 4 3 2 k = q := by
    decide
  have hJ : ∀ q ∈ ({4, 2} : Finset (Fin 7)), ∃ k ∈ ({1, 3} : Finset (ZMod 4)), quad 6 4 3 2 k = q := by
    decide
  obtain ⟨k, hk, hkq⟩ := hI i hi
  obtain ⟨l, hl, hlq⟩ := hJ j hj
  have hp' : ∃ pr ∈ diagPairs, 0 < ⟪x (quad 6 4 3 2 pr.1) - x (quad 6 4 3 2 pr.2), u⟫ := by
    refine ⟨(k, l), Finset.mem_product.2 ⟨hk, hl⟩, ?_⟩
    simp only
    rw [hkq, hlq]; exact hlexε
  have hn : ∃ pr ∈ diagPairs, ⟪x (quad 6 4 3 2 pr.1) - x (quad 6 4 3 2 pr.2), u⟫ < 0 := by
    refine ⟨pn, hpn, ?_⟩
    rw [hr, hr]; exact hneg
  have hN3s := N3_self F
  have hnU : ∀ t ∈ UC2, 0 < ⟪F.N t, u⟫ ∨ (⟪F.N t, u⟫ = 0 ∧ 0 < ⟪F.N t, F.N 3⟫) := by
    intro t ht; simp only [UC2, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · exact Or.inr ⟨hN3, hN3s⟩
    · exact Or.inl hN4
    · exact Or.inl hN5
    · exact Or.inl hN6
  have hnD : ∀ t ∈ DC2, ⟪F.N t, u⟫ < 0 ∨ (⟪F.N t, u⟫ = 0 ∧ ⟪F.N t, F.N 3⟫ < 0) := by
    intro t ht; simp only [DC2, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl
    · exact Or.inl hN7
    · exact Or.inl hN8
  obtain ⟨e', he'⟩ := (ev_cellAt_tilt F hnU hnD).exists
  have hcl : CellLe F UC2 DC2 u := by
    refine ⟨fun t ht => ?_, fun t ht => ?_⟩
    · rcases hnU t ht with h | ⟨h, -⟩
      · exact h.le
      · exact h.ge
    · rcases hnD t ht with h | ⟨h, -⟩
      · exact h.le
      · exact h.le
  exact lexAny_of_closedCell_q4 F hx (inj_quad (by decide)) cycC2 he' hcl hcl hn hp'

theorem q45_C2_cell {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (ha35 : ⟪F.N 5, x 3 - x 5⟫ < 0)
    (s t : ℝ) (hs0 : 0 < s)
    (hdecomp : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0))
    (ht1 : 1 < t)
    (hlex : ∃ i ∈ ({6, 3} : Finset (Fin 7)), ∃ j ∈ ({4, 2} : Finset (Fin 7)),
      ⟪x i - x j, x 3 - x 5⟫ < 0 ∨ (⟪x i - x j, x 3 - x 5⟫ = 0 ∧ ⟪x i - x j, x 4 - x 0⟫ < 0)) :
    IsRupert (univ.image x) :=
  Gen.lexAny_isRupert F (inj_of_fac24 F) (q45_C2_cell_lex F ha35 s t hs0 hdecomp ht1 hlex)

end Minimality.T24.Q45
