module

public import Minimality.Type24SAT.K24.ParStratum

@[expose] public section

/-!
# Type 24, `D` a parallelogram, `E ∥ G`: the double-overhang piece `R''`

On `R` (`05 ⊥ 23`, `05 ⊥ 06`: `D` a rectangle perpendicular to `E` and `G`) with `X i = ⟪x i - x 0, e⟫`, `e = x 4 - x 0`:
`R''` is `X 2 ≤ 0` and `|e|² ≤ X 6` (the front vertices overhang both ends of `04`; `1` never decides).
With `T = ⟪x 3 - x 6, x 2 - x 0⟫`:
* `X 2 < 0`, `T > 0`: leaf V12536 at `x 0 - x 2` (the view along `02`): depths `z 2 < z 5 < z 3 < z 6`.
* `T ≤ 0` or `X 2 = 0`, not both `X 2 = 0` and `X 6 = |e|²`: leaf P0264 (Q4); its closed cell contains the view
  `u_CH` along the line `C ∩ H`, `u_CH = α (x 2 - x 5) + β (x 0 - x 5)`, `α = f_H 5 - f_H 0`, `β = -f_H 5`.
  Negative diagonal form: `z 0 - z 2` at `u_CH` (`T ≤ 0`), or `z 0 - z 4` on the open cell (`X 2 = 0`: then
  `N_C` is a negative multiple of `e`); the positive one is at any point of the open cell.
* The box corner `X 2 = 0`, `X 6 = |e|²` with `T > 0` is `C ∥ I` (`box_ci`) outside that stratum's exclusion.
What remains (`isRupert_eg_par`): the box corner with `T ≤ 0`, `R₄'`.
-/

set_option autoImplicit false
open scoped RealInnerProductSpace
open Finset

namespace Minimality.T24.Par
open Minimality Minimality.H21 Minimality.T24.SAT

/-- Rim `1 2 5 3 6`: edges `12` (A, F), `25` (C, G), `53` (D, G), `36` (I, H), `61` (B, F). -/
def c12536 : ZMod 5 → Fin 7 := ![1, 2, 5, 3, 6]
def U12536 : Finset (Fin 9) := {0, 1, 2, 3, 4, 8}
def D12536 : Finset (Fin 9) := {5, 6, 7}
/-- Rim `0 2 6 4`: edges `02` (A, C), `26` (F, H), `64` (E, I), `40` (E, D). -/
def c0264 : ZMod 4 → Fin 7 := ![0, 2, 6, 4]
def U0264 : Finset (Fin 9) := {0, 1, 4, 5}
def D0264 : Finset (Fin 9) := {2, 3, 6, 7, 8}

theorem cyc12536 : S0xCycUD s0x_S24 c12536 U12536 D12536 := by decide
theorem cyc0264 : S0xCycUD s0x_S24 c0264 U0264 D0264 := by decide

/-- A robustly unimodal 5-cycle: `z 1 < z 2 < z 3 < z 4` (`z 0` free). -/
theorem robUni_v5d (z : ZMod 5 → ℝ) (h12 : z 1 < z 2) (h23 : z 2 < z 3) (h34 : z 3 < z 4) :
    RobUni z := by
  have tab : ((0 : ZMod 5) + 1 = 1) ∧
      ((0 : ZMod 5) + 2 = 2) ∧
      ((0 : ZMod 5) + 3 = 3) ∧
      ((0 : ZMod 5) + 4 = 4) ∧
      ((1 : ZMod 5) + 1 = 2) ∧
      ((1 : ZMod 5) + 2 = 3) ∧
      ((1 : ZMod 5) + 3 = 4) ∧
      ((1 : ZMod 5) + 4 = 0) ∧
      ((2 : ZMod 5) + 1 = 3) ∧
      ((2 : ZMod 5) + 2 = 4) ∧
      ((2 : ZMod 5) + 3 = 0) ∧
      ((2 : ZMod 5) + 4 = 1) ∧
      ((3 : ZMod 5) + 1 = 4) ∧
      ((3 : ZMod 5) + 2 = 0) ∧
      ((3 : ZMod 5) + 3 = 1) ∧
      ((3 : ZMod 5) + 4 = 2) ∧
      ((4 : ZMod 5) + 1 = 0) ∧
      ((4 : ZMod 5) + 2 = 1) ∧
      ((4 : ZMod 5) + 3 = 2) ∧
      ((4 : ZMod 5) + 4 = 3) := by decide
  obtain ⟨a01, a02, a03, a04, a11, a12, a13, a14, a21, a22, a23, a24, a31, a32, a33, a34, a41, a42, a43, a44⟩ := tab
  intro B b c d hb hbc hcd hd
  have hB : B = 0 ∨ B = 1 ∨ B = 2 ∨ B = 3 ∨ B = 4 := by revert B; decide
  have hbcd : (b = 1 ∧ c = 2 ∧ d = 3) ∨ (b = 1 ∧ c = 2 ∧ d = 4) ∨ (b = 1 ∧ c = 3 ∧ d = 4) ∨
      (b = 2 ∧ c = 3 ∧ d = 4) := by omega
  rintro ⟨h1, h2, h3, h4⟩
  rcases hbcd with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
  rcases hB with rfl | rfl | rfl | rfl | rfl <;>
  simp only [Nat.cast_one, Nat.cast_ofNat, a01, a02, a03, a04, a11, a12, a13, a14, a21, a22, a23, a24, a31, a32, a33, a34, a41, a42, a43, a44] at h1 h2 h3 h4 <;>
  linarith

/-- Two vectors `a`, `b` orthogonal to `g` with `vol3 a b g ≠ 0` span every vector orthogonal to `g`. -/
theorem span_perp {a b g v : ℝ³} (hD : vol3 a b g ≠ 0) (hg : g ≠ 0) (hv : ⟪v, g⟫ = 0)
    (ha : ⟪a, g⟫ = 0) (hb : ⟪b, g⟫ = 0) : ∃ l m : ℝ, v = l • a + m • b := by
  have h := vol3_smul_cramer a b g v
  have hgg : 0 < ⟪g, g⟫ := real_inner_self_pos.2 hg
  have h1 := congrArg (fun y => ⟪y, g⟫) h
  simp only [inner_add_left, real_inner_smul_left, hv, ha, hb] at h1
  have hz : vol3 a b v = 0 := by
    have : vol3 a b v * ⟪g, g⟫ = 0 := by linarith
    rcases mul_eq_zero.1 this with h0 | h0
    · exact h0
    · exact absurd h0 hgg.ne'
  rw [hz, zero_smul, add_zero] at h
  refine ⟨vol3 v b g / vol3 a b g, vol3 a v g / vol3 a b g, ?_⟩
  have h2 : v = (vol3 a b g)⁻¹ • (vol3 a b g • v) := by rw [smul_smul, inv_mul_cancel₀ hD, one_smul]
  rw [h, smul_add, smul_smul, smul_smul] at h2
  rw [div_eq_inv_mul, div_eq_inv_mul]
  exact h2

variable {x : Fin 7 → ℝ³}

/-- On `R`: `N_I = a e + b N_D` with `a > 0`; on `R''` (`X 6 ≥ |e|²`) moreover `b ≥ 0`, so
`f_I 0 - f_I 2 = -a X 2 - b f_D 2 ≥ 0`. -/
theorem rect_fI (F : S0xFac 9 s0x_S24 x) (hP : x 3 = x 4 + x 5 - x 0)
    (hE : ⟪F.N 4, x 2 - x 3⟫ = 0) (hw : ⟪x 5 - x 0, x 2 - x 3⟫ = 0)
    (hs : ⟪x 5 - x 0, x 6 - x 0⟫ = 0) (h6 : ⟪x 4 - x 0, x 4 - x 0⟫ ≤ ⟪x 6 - x 0, x 4 - x 0⟫) :
    ∃ a b : ℝ, 0 < a ∧ 0 ≤ b ∧ (⟪x 4 - x 0, x 4 - x 0⟫ < ⟪x 6 - x 0, x 4 - x 0⟫ → 0 < b) ∧
      F.f 8 (x 0) - F.f 8 (x 2) = -a * ⟪x 2 - x 0, x 4 - x 0⟫ - b * F.f 3 (x 2) := by
  obtain ⟨heg, hen, hng, -, hIg⟩ := rect_frame F hP hE hw hs
  have IS := F.inner_sub
  have hx := Minimality.H24.SAT.inj_of_fac F
  have he : x 4 - x 0 ≠ 0 := fun h => absurd (hx (sub_eq_zero.1 h)) (by decide)
  have hg : x 5 - x 0 ≠ 0 := fun h => absurd (hx (sub_eq_zero.1 h)) (by decide)
  have hD2 := F.neg 3 2 (by decide)
  have hn : F.N 3 ≠ 0 := by
    intro h; have := IS 3 2 0; rw [h, inner_zero_left, F.zero 3 0 (by decide)] at this; linarith
  obtain ⟨a, b, hab⟩ := orth_decomp he hn hg hen heg hng hIg
  have fI : ∀ i, F.f 8 (x i) = a * (⟪x i - x 0, x 4 - x 0⟫ - ⟪x 4 - x 0, x 4 - x 0⟫) + b * F.f 3 (x i) := by
    intro i
    have h1 := IS 8 i 4
    have h2 := IS 3 i 4
    rw [F.zero 8 4 (by decide), sub_zero] at h1
    rw [F.zero 3 4 (by decide), sub_zero] at h2
    rw [← h1, ← h2, hab, inner_add_left, real_inner_smul_left, real_inner_smul_left]
    have : ⟪x 4 - x 0, x i - x 4⟫ = ⟪x i - x 0, x 4 - x 0⟫ - ⟪x 4 - x 0, x 4 - x 0⟫ := by
      rw [show x i - x 4 = (x i - x 0) - (x 4 - x 0) by abel, inner_sub_right,
        real_inner_comm (x i - x 0) (x 4 - x 0)]
    rw [this]
  have hee : 0 < ⟪x 4 - x 0, x 4 - x 0⟫ := real_inner_self_pos.2 he
  have ha : 0 < a := by
    have := fI 0
    rw [F.zero 3 0 (by decide), mul_zero, add_zero, sub_self, inner_zero_left, zero_sub] at this
    have hI0 := F.neg 8 0 (by decide)
    by_contra h; push Not at h; nlinarith
  have e6 := fI 6
  rw [F.zero 8 6 (by decide)] at e6
  have hD6 := F.neg 3 6 (by decide)
  refine ⟨a, b, ha, ?_, ?_, ?_⟩
  · by_contra h; push Not at h; nlinarith [mul_nonneg ha.le (sub_nonneg.2 h6)]
  · intro h; by_contra hb; push Not at hb; nlinarith [mul_pos ha (sub_pos.2 h)]
  · have e0 := fI 0
    have e2 := fI 2
    rw [F.zero 3 0 (by decide), sub_self, inner_zero_left] at e0
    rw [e0, e2]; ring

/-- On `R''`: `N_C = a e + b N_D` with `a < 0 ≤ b`, hence `f_C 3 - f_C 6 ≥ 0`, strictly unless `X 2 = 0`
and `X 6 = |e|²`. -/
theorem rect_fC (F : S0xFac 9 s0x_S24 x) (hP : x 3 = x 4 + x 5 - x 0)
    (hE : ⟪F.N 4, x 2 - x 3⟫ = 0) (hw : ⟪x 5 - x 0, x 2 - x 3⟫ = 0)
    (hs : ⟪x 5 - x 0, x 6 - x 0⟫ = 0) (h2 : ⟪x 2 - x 0, x 4 - x 0⟫ ≤ 0)
    (h6 : ⟪x 4 - x 0, x 4 - x 0⟫ ≤ ⟪x 6 - x 0, x 4 - x 0⟫)
    (hnb : ⟪x 2 - x 0, x 4 - x 0⟫ < 0 ∨ ⟪x 4 - x 0, x 4 - x 0⟫ < ⟪x 6 - x 0, x 4 - x 0⟫) :
    F.f 2 (x 6) < F.f 2 (x 3) := by
  obtain ⟨heg, hen, hng, hCg, -⟩ := rect_frame F hP hE hw hs
  have IS := F.inner_sub
  have hx := Minimality.H24.SAT.inj_of_fac F
  have he : x 4 - x 0 ≠ 0 := fun h => absurd (hx (sub_eq_zero.1 h)) (by decide)
  have hg : x 5 - x 0 ≠ 0 := fun h => absurd (hx (sub_eq_zero.1 h)) (by decide)
  have hD2 := F.neg 3 2 (by decide)
  have hn : F.N 3 ≠ 0 := by
    intro h; have := IS 3 2 0; rw [h, inner_zero_left, F.zero 3 0 (by decide)] at this; linarith
  obtain ⟨a, b, hab⟩ := orth_decomp he hn hg hen heg hng hCg
  have fC : ∀ i, F.f 2 (x i) = a * ⟪x i - x 0, x 4 - x 0⟫ + b * F.f 3 (x i) := by
    intro i
    have h1 := IS 2 i 0
    have h2 := IS 3 i 0
    rw [F.zero 2 0 (by decide), sub_zero] at h1
    rw [F.zero 3 0 (by decide), sub_zero] at h2
    rw [← h1, ← h2, hab, inner_add_left, real_inner_smul_left, real_inner_smul_left,
      real_inner_comm (x i - x 0) (x 4 - x 0), real_inner_comm (x i - x 0) (F.N 3)]
  have hee : 0 < ⟪x 4 - x 0, x 4 - x 0⟫ := real_inner_self_pos.2 he
  have ha : a < 0 := by
    have := fC 4
    rw [F.zero 3 4 (by decide), mul_zero, add_zero] at this
    have hC4 := F.neg 2 4 (by decide)
    by_contra h; push Not at h; nlinarith
  have e2 := fC 2
  rw [F.zero 2 2 (by decide)] at e2
  have hb : 0 ≤ b := by
    by_contra h; push Not at h; nlinarith [mul_nonneg_of_nonpos_of_nonpos ha.le h2]
  have e3 := fC 3
  rw [F.zero 3 3 (by decide), mul_zero, add_zero,
    show x 3 - x 0 = (x 4 - x 0) + (x 5 - x 0) by rw [hP]; abel, inner_add_left,
    real_inner_comm (x 4 - x 0) (x 5 - x 0), heg, add_zero] at e3
  have e6 := fC 6
  have hD6 := F.neg 3 6 (by decide)
  rcases hnb with h | h
  · have hb' : 0 < b := by
      by_contra h'; push Not at h'
      have : b = 0 := le_antisymm h' hb
      rw [this, zero_mul, add_zero] at e2; nlinarith [mul_pos_of_neg_of_neg ha h]
    nlinarith [mul_nonneg_of_nonpos_of_nonpos ha.le (sub_nonpos.2 h6), mul_pos hb' (neg_pos.2 hD6)]
  · nlinarith [mul_pos_of_neg_of_neg ha (sub_neg.2 h), mul_nonneg hb (neg_nonneg.2 hD6.le)]

/-- Facts on `R`: `x 2 - x 5 ⊥ g`, `⟪x 2 - x 0, x 2 - x 3⟫ = |x 2 - x 5|² - X 2`. -/
theorem rect_p2 (F : S0xFac 9 s0x_S24 x) (hP : x 3 = x 4 + x 5 - x 0)
    (hE : ⟪F.N 4, x 2 - x 3⟫ = 0) (hw : ⟪x 5 - x 0, x 2 - x 3⟫ = 0)
    (hs : ⟪x 5 - x 0, x 6 - x 0⟫ = 0) :
    ⟪x 2 - x 5, x 5 - x 0⟫ = 0 ∧
      ⟪x 2 - x 5, x 2 - x 3⟫ = ⟪x 2 - x 5, x 2 - x 5⟫ - ⟪x 2 - x 0, x 4 - x 0⟫ := by
  obtain ⟨heg, -, -, -, -⟩ := rect_frame F hP hE hw hs
  have e25 : x 2 - x 5 = (x 2 - x 3) + (x 4 - x 0) := by rw [hP]; abel
  have o : ⟪x 2 - x 5, x 5 - x 0⟫ = 0 := by
    rw [e25, inner_add_left, real_inner_comm, hw, heg, add_zero]
  refine ⟨o, ?_⟩
  have e23 : x 2 - x 3 = (x 2 - x 5) - (x 4 - x 0) := by rw [hP]; abel
  have e20 : x 2 - x 0 = (x 2 - x 5) + (x 5 - x 0) := by abel
  rw [e23, inner_sub_right, e20, inner_add_left, real_inner_comm (x 4 - x 0) (x 5 - x 0), heg]; ring

open Minimality.RimCell in
/-- **`R''`, `X 2 < 0`, `T > 0`: leaf V12536 at the view along `02`.** -/
theorem isRupert_eg_R2v (F : S0xFac 9 s0x_S24 x) (hP : x 3 = x 4 + x 5 - x 0)
    (hE : ⟪F.N 4, x 2 - x 3⟫ = 0) (hw : ⟪x 5 - x 0, x 2 - x 3⟫ = 0)
    (hs : ⟪x 5 - x 0, x 6 - x 0⟫ = 0) (h2 : ⟪x 2 - x 0, x 4 - x 0⟫ < 0)
    (h6 : ⟪x 4 - x 0, x 4 - x 0⟫ ≤ ⟪x 6 - x 0, x 4 - x 0⟫) (hT : 0 < ⟪x 3 - x 6, x 2 - x 0⟫) :
    IsRupert (univ.image x) := by
  have IS := F.inner_sub
  have hx := Minimality.H24.SAT.inj_of_fac F
  obtain ⟨heg, -, -, -, -⟩ := rect_frame F hP hE hw hs
  obtain ⟨o25, -⟩ := rect_p2 F hP hE hw hs
  obtain ⟨aI, bI, haI, hbI, -, eI⟩ := rect_fI F hP hE hw hs h6
  have hp : x 2 - x 5 ≠ 0 := fun h => absurd (hx (sub_eq_zero.1 h)) (by decide)
  have hpp : 0 < ⟪x 2 - x 5, x 2 - x 5⟫ := real_inner_self_pos.2 hp
  have hD2 := F.neg 3 2 (by decide)
  have hI : 0 < F.f 8 (x 0) - F.f 8 (x 2) := by
    rw [eI]; nlinarith [mul_pos_of_neg_of_neg (neg_neg_of_pos haI) h2, mul_nonneg hbI (neg_nonneg.2 hD2.le)]
  have s02 : ∀ t, ⟪F.N t, x 0 - x 2⟫ = F.f t (x 0) - F.f t (x 2) := fun t => IS t 0 2
  have s03 : ∀ t, ⟪F.N t, x 0 - x 3⟫ = F.f t (x 0) - F.f t (x 3) := fun t => IS t 0 3
  have zA0 := F.zero 0 0 (by decide); have zA2 := F.zero 0 2 (by decide)
  have hA3 := F.neg 0 3 (by decide)
  have zB0 := F.zero 1 0 (by decide); have hB2 := F.neg 1 2 (by decide)
  have zC0 := F.zero 2 0 (by decide); have zC2 := F.zero 2 2 (by decide)
  have hC3 := F.neg 2 3 (by decide)
  have zD0 := F.zero 3 0 (by decide)
  have zE0 := F.zero 4 0 (by decide); have hE2 := F.neg 4 2 (by decide)
  have zF2 := F.zero 5 2 (by decide); have hF0 := F.neg 5 0 (by decide)
  have zG2 := F.zero 6 2 (by decide); have hG0 := F.neg 6 0 (by decide)
  have zH2 := F.zero 7 2 (by decide); have hH0 := F.neg 7 0 (by decide)
  obtain ⟨aV, hAV⟩ := exists_cellAt_of_lex (F := F) (U := U12536) (Dn := D12536)
    (u₀ := x 0 - x 2) (v := x 0 - x 3)
    (by
      intro t ht; simp only [U12536, Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
      · exact Or.inr ⟨by rw [s02, zA0, zA2]; simp, by rw [s03, zA0]; linarith⟩
      · exact Or.inl (by rw [s02, zB0]; linarith)
      · exact Or.inr ⟨by rw [s02, zC0, zC2]; simp, by rw [s03, zC0]; linarith⟩
      · exact Or.inl (by rw [s02, zD0]; linarith)
      · exact Or.inl (by rw [s02, zE0]; linarith)
      · exact Or.inl (by rw [s02]; linarith))
    (by
      intro t ht; simp only [D12536, Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl
      · exact Or.inl (by rw [s02, zF2]; linarith)
      · exact Or.inl (by rw [s02, zG2]; linarith)
      · exact Or.inl (by rw [s02, zH2]; linarith))
  refine isRupert_of_closedCell (u₀ := x 0 - x 2) (by norm_num) F hx (by decide) cyc12536 hAV ?_ ?_
  · refine ⟨fun t ht => ?_, fun t ht => ?_⟩
    · simp only [U12536, Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
      · rw [s02, zA0, zA2]; simp
      · rw [s02, zB0]; linarith
      · rw [s02, zC0, zC2]; simp
      · rw [s02, zD0]; linarith
      · rw [s02, zE0]; linarith
      · rw [s02]; linarith
    · simp only [D12536, Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl
      · rw [s02, zF2]; linarith
      · rw [s02, zG2]; linarith
      · rw [s02, zH2]; linarith
  · have c1 : c12536 1 = 2 := rfl
    have c2 : c12536 2 = 5 := rfl
    have c3 : c12536 3 = 3 := rfl
    have c4 : c12536 4 = 6 := rfl
    apply robUni_v5d
    · simp only [c1, c2]
      have : ⟪x 5 - x 2, x 0 - x 2⟫ = ⟪x 2 - x 5, x 2 - x 5⟫ := by
        rw [show x 5 - x 2 = -(x 2 - x 5) by abel, show x 0 - x 2 = -((x 2 - x 5) + (x 5 - x 0)) by abel,
          inner_neg_neg, inner_add_right, o25, add_zero]
      rw [inner_sub_left] at this; linarith
    · simp only [c2, c3]
      have : ⟪x 3 - x 5, x 0 - x 2⟫ = -⟪x 2 - x 0, x 4 - x 0⟫ := by
        rw [show x 3 - x 5 = x 4 - x 0 by rw [hP]; abel, show x 0 - x 2 = -(x 2 - x 0) by abel,
          inner_neg_right, real_inner_comm]
      rw [inner_sub_left] at this; linarith
    · simp only [c3, c4]
      have : ⟪x 6 - x 3, x 0 - x 2⟫ = ⟪x 3 - x 6, x 2 - x 0⟫ := by
        rw [show x 6 - x 3 = -(x 3 - x 6) by abel, show x 0 - x 2 = -(x 2 - x 0) by abel, inner_neg_neg]
      rw [inner_sub_left] at this; linarith

set_option maxHeartbeats 1000000 in
open Minimality.RimCell in
/-- **`R''`, `T ≤ 0` or `X 2 = 0`, not the box corner: leaf P0264 (Q4).**  The closed cell contains the view
`u_CH` along `C ∩ H`; for `T ≤ 0` the negative diagonal form is `z 0 - z 2` at `u_CH`, for `X 2 = 0` it is
`z 0 - z 4` on the whole open cell (`N_C` is then a negative multiple of `e`). -/
theorem isRupert_eg_R2c (F : S0xFac 9 s0x_S24 x) (hP : x 3 = x 4 + x 5 - x 0)
    (hE : ⟪F.N 4, x 2 - x 3⟫ = 0) (hw : ⟪x 5 - x 0, x 2 - x 3⟫ = 0)
    (hs : ⟪x 5 - x 0, x 6 - x 0⟫ = 0) (h2 : ⟪x 2 - x 0, x 4 - x 0⟫ ≤ 0)
    (h6 : ⟪x 4 - x 0, x 4 - x 0⟫ ≤ ⟪x 6 - x 0, x 4 - x 0⟫)
    (hT : ⟪x 3 - x 6, x 2 - x 0⟫ ≤ 0 ∨ ⟪x 2 - x 0, x 4 - x 0⟫ = 0)
    (hnb : ⟪x 2 - x 0, x 4 - x 0⟫ < 0 ∨ ⟪x 4 - x 0, x 4 - x 0⟫ < ⟪x 6 - x 0, x 4 - x 0⟫) :
    IsRupert (univ.image x) := by
  have IS := F.inner_sub
  have hx := Minimality.H24.SAT.inj_of_fac F
  obtain ⟨heg, hen, hng, hCg, hIg⟩ := rect_frame F hP hE hw hs
  obtain ⟨o25, ep2d⟩ := rect_p2 F hP hE hw hs
  obtain ⟨aI, bI, haI, hbI, hbI', eI⟩ := rect_fI F hP hE hw hs h6
  have hC36 := rect_fC F hP hE hw hs h2 h6 hnb
  set e := x 4 - x 0 with he_def
  set g := x 5 - x 0 with hg_def
  set w := x 6 - x 0 with hw_def
  set p := x 2 - x 5 with hp_def
  set d := x 2 - x 3 with hd_def
  have he0 : e ≠ 0 := fun h => absurd (hx (sub_eq_zero.1 h)) (by decide)
  have hg0 : g ≠ 0 := fun h => absurd (hx (sub_eq_zero.1 h)) (by decide)
  have hp0 : p ≠ 0 := fun h => absurd (hx (sub_eq_zero.1 h)) (by decide)
  clear_value e g w p d
  have hgg : 0 < ⟪g, g⟫ := real_inner_self_pos.2 hg0
  have hpp : 0 < ⟪p, p⟫ := real_inner_self_pos.2 hp0
  have hpd : p = d + e := by rw [hp_def, hd_def, he_def, hP]; abel
  have hwg : ⟪w, g⟫ = 0 := by rw [real_inner_comm]; exact hs
  have hdg : ⟪d, g⟫ = 0 := by rw [real_inner_comm]; exact hw
  -- facet values
  have zA0 := F.zero 0 0 (by decide); have zA2 := F.zero 0 2 (by decide); have hA5 := F.neg 0 5 (by decide)
  have zB0 := F.zero 1 0 (by decide); have zB6 := F.zero 1 6 (by decide)
  have hB2 := F.neg 1 2 (by decide); have hB4 := F.neg 1 4 (by decide); have hB5 := F.neg 1 5 (by decide)
  have zC0 := F.zero 2 0 (by decide); have zC2 := F.zero 2 2 (by decide); have zC5 := F.zero 2 5 (by decide)
  have hC3 := F.neg 2 3 (by decide); have hC4 := F.neg 2 4 (by decide); have hC6 := F.neg 2 6 (by decide)
  have zD0 := F.zero 3 0 (by decide); have zD3 := F.zero 3 3 (by decide); have zD4 := F.zero 3 4 (by decide)
  have zD5 := F.zero 3 5 (by decide); have hD2 := F.neg 3 2 (by decide); have hD6 := F.neg 3 6 (by decide)
  have zE0 := F.zero 4 0 (by decide); have zE4 := F.zero 4 4 (by decide); have zE6 := F.zero 4 6 (by decide)
  have hE5 := F.neg 4 5 (by decide)
  have zF2 := F.zero 5 2 (by decide); have zF6 := F.zero 5 6 (by decide)
  have hF3 := F.neg 5 3 (by decide); have hF5 := F.neg 5 5 (by decide)
  have zG2 := F.zero 6 2 (by decide); have zG5 := F.zero 6 5 (by decide); have hG0 := F.neg 6 0 (by decide)
  have zH2 := F.zero 7 2 (by decide); have zH3 := F.zero 7 3 (by decide); have zH6 := F.zero 7 6 (by decide)
  have hH0 := F.neg 7 0 (by decide); have hH4 := F.neg 7 4 (by decide); have hH5 := F.neg 7 5 (by decide)
  have hI2 := F.neg 8 2 (by decide)
  have ip : ∀ t (i j : Fin 7), ⟪F.N t, x i - x j⟫ = F.f t (x i) - F.f t (x j) := IS
  -- `f_E 2 = f_E 5`, `f_I 5 = f_I 0`
  have hE25 : F.f 4 (x 2) = F.f 4 (x 5) := by
    have h1 : ⟪F.N 4, p⟫ = 0 := by
      rw [hpd, inner_add_right, hE, he_def, ip, zE4, zE0]; ring
    rw [hp_def, ip] at h1; linarith
  have hI50 : F.f 8 (x 5) = F.f 8 (x 0) := by
    have := hIg; rw [hg_def, ip] at this; linarith
  -- `α = f_H 5 - f_H 0 > 0`
  set α := F.f 7 (x 5) - F.f 7 (x 0) with hα_def
  set β := -F.f 7 (x 5) with hβ_def
  have hα : 0 < α := by
    have h1 : ⟪F.N 7, x 5 - x 0⟫ = ⟪F.N 7, x 3 - x 4⟫ := by rw [show x 5 - x 0 = x 3 - x 4 by rw [hP]; abel]
    rw [ip, ip, zH3] at h1; rw [hα_def, h1]; linarith
  have hβ : 0 < β := by rw [hβ_def]; linarith
  set u := α • p + β • (x 0 - x 5) with hu_def
  have hu : ∀ t, ⟪F.N t, u⟫ = α * (F.f t (x 2) - F.f t (x 5)) + β * (F.f t (x 0) - F.f t (x 5)) := by
    intro t; rw [hu_def, inner_add_right, inner_smul_right, inner_smul_right, hp_def, ip, ip]
  -- `B` along `u`: `f_B 2 > f_B 5` (the trace of `p` in the plane of `E`)
  have hB25 : F.f 1 (x 5) < F.f 1 (x 2) := by
    have hD : vol3 w e g ≠ 0 := by
      have h := vol3_mul_inner (F.N 2) (F.N 3) (F.N 4) w e g
      have r1 : ⟪F.N 2, w⟫ = F.f 2 (x 6) := by rw [hw_def, ip, zC0]; ring
      have r2 : ⟪F.N 2, e⟫ = F.f 2 (x 4) := by rw [he_def, ip, zC0]; ring
      have r3 : ⟪F.N 2, g⟫ = 0 := hCg
      have r4 : ⟪F.N 3, w⟫ = F.f 3 (x 6) := by rw [hw_def, ip, zD0]; ring
      have r5 : ⟪F.N 3, e⟫ = 0 := by rw [real_inner_comm]; exact hen
      have r6 : ⟪F.N 3, g⟫ = 0 := hng
      have r7 : ⟪F.N 4, w⟫ = 0 := by rw [hw_def, ip, zE6, zE0]; ring
      have r8 : ⟪F.N 4, e⟫ = 0 := by rw [he_def, ip, zE4, zE0]; ring
      have r9 : ⟪F.N 4, g⟫ = F.f 4 (x 5) := by rw [hg_def, ip, zE0]; ring
      rw [r1, r2, r3, r4, r5, r6, r7, r8, r9] at h
      intro h0; rw [h0, mul_zero] at h
      have : F.f 2 (x 4) * (F.f 3 (x 6) * F.f 4 (x 5)) = 0 := by linear_combination h
      have : F.f 2 (x 4) * (F.f 3 (x 6) * F.f 4 (x 5)) < 0 :=
        mul_neg_of_neg_of_pos hC4 (mul_pos_of_neg_of_neg hD6 hE5)
      linarith
    obtain ⟨l, m, hlm⟩ := span_perp hD hg0 o25 hwg heg
    have aD := congrArg (fun y => ⟪F.N 3, y⟫) hlm
    have aC := congrArg (fun y => ⟪F.N 2, y⟫) hlm
    have aB := congrArg (fun y => ⟪F.N 1, y⟫) hlm
    simp only [inner_add_right, inner_smul_right] at aD aC aB
    rw [hp_def, hw_def, he_def, ip, ip, ip, zD5, zD0, zD4] at aD
    rw [hp_def, hw_def, he_def, ip, ip, ip, zC5, zC2, zC0] at aC
    rw [hp_def, hw_def, he_def, ip, ip, ip, zB0, zB6] at aB
    have hl : 0 < l := by
      by_contra h; push Not at h; linarith [mul_nonneg_of_nonpos_of_nonpos h hD6.le]
    have hm : m < 0 := by
      by_contra h; push Not at h; linarith [mul_neg_of_pos_of_neg hl hC6, mul_nonpos_of_nonneg_of_nonpos h hC4.le]
    linarith [mul_pos_of_neg_of_neg hm hB4]
  -- `F` along `u` (the trace of `w` in the plane of `E` in the frame `p, d`)
  have hD' : vol3 p d g ≠ 0 := by
    have h := vol3_mul_inner (F.N 2) (F.N 3) (F.N 4) p d g
    have r1 : ⟪F.N 2, p⟫ = 0 := by rw [hp_def, ip, zC2, zC5]; ring
    have r2 : ⟪F.N 2, d⟫ = -F.f 2 (x 3) := by rw [hd_def, ip, zC2]; ring
    have r3 : ⟪F.N 2, g⟫ = 0 := hCg
    have r4 : ⟪F.N 3, p⟫ = F.f 3 (x 2) := by rw [hp_def, ip, zD5]; ring
    have r5 : ⟪F.N 3, d⟫ = F.f 3 (x 2) := by rw [hd_def, ip, zD3]; ring
    have r6 : ⟪F.N 3, g⟫ = 0 := hng
    have r7 : ⟪F.N 4, p⟫ = 0 := by rw [hp_def, ip, hE25]; ring
    have r8 : ⟪F.N 4, d⟫ = 0 := hE
    have r9 : ⟪F.N 4, g⟫ = F.f 4 (x 5) := by rw [hg_def, ip, zE0]; ring
    rw [r1, r2, r3, r4, r5, r6, r7, r8, r9] at h
    intro h0; rw [h0, mul_zero] at h
    have : F.f 2 (x 3) * (F.f 3 (x 2) * F.f 4 (x 5)) = 0 := by linear_combination -h
    have : F.f 2 (x 3) * (F.f 3 (x 2) * F.f 4 (x 5)) < 0 :=
      mul_neg_of_neg_of_pos hC3 (mul_pos_of_neg_of_neg hD2 hE5)
    linarith
  obtain ⟨l', m', hlm'⟩ := span_perp hD' hg0 hwg o25 hdg
  have bC := congrArg (fun y => ⟪F.N 2, y⟫) hlm'
  have bH := congrArg (fun y => ⟪F.N 7, y⟫) hlm'
  have bF := congrArg (fun y => ⟪F.N 5, y⟫) hlm'
  simp only [inner_add_right, inner_smul_right] at bC bH bF
  rw [hp_def, hw_def, hd_def, ip, ip, ip, zC0, zC2, zC5] at bC
  rw [hp_def, hw_def, hd_def, ip, ip, ip, zH6, zH2, zH3] at bH
  rw [hp_def, hw_def, hd_def, ip, ip, ip, zF6, zF2] at bF
  have hm' : 1 + m' < 0 := by
    have : (1 + m') * F.f 2 (x 3) = F.f 2 (x 3) - F.f 2 (x 6) := by linear_combination bC
    by_contra h; push Not at h; linarith [mul_nonpos_of_nonneg_of_nonpos h hC3.le]
  have hFu : 0 < ⟪F.N 5, u⟫ := by
    rw [hu, zF2]
    have e1 : α * (0 - F.f 5 (x 5)) + β * (F.f 5 (x 0) - F.f 5 (x 5)) = -F.f 7 (x 5) * (m' * F.f 5 (x 3)) := by
      rw [hα_def, hβ_def]; linear_combination F.f 7 (x 5) * bF - F.f 5 (x 5) * bH
    rw [e1]
    have : 0 < m' * F.f 5 (x 3) := mul_pos_of_neg_of_neg (by linarith) hF3
    exact mul_pos (neg_pos.2 hH5) this
  -- the negative diagonal form `z 0 - z 2` at `u`
  have hf1 : ⟪x 3 - x 6, x 2 - x 0⟫ ≤ 0 → ⟪x 0 - x 2, u⟫ < 0 := by
    intro hT
    have q1 : x 0 - x 2 = -(p + g) := by rw [hp_def, hg_def]; abel
    have q2 : x 0 - x 5 = -g := by rw [hg_def]; abel
    have pg : ⟪p, g⟫ = 0 := o25
    have pg' : ⟪g, p⟫ = 0 := by rw [real_inner_comm]; exact pg
    have e1 : ⟪x 0 - x 2, u⟫ = -α * ⟪p, p⟫ + β * ⟪g, g⟫ := by
      rw [hu_def, q1, q2, inner_add_right, inner_smul_right, inner_smul_right, inner_neg_left, inner_neg_left,
        inner_neg_right, inner_add_left, inner_add_left]
      simp only [pg, pg']; ring
    have e2 : ⟪x 3 - x 6, x 2 - x 0⟫ = ⟪e, p⟫ + ⟪g, g⟫ - ⟪w, p⟫ := by
      rw [show x 3 - x 6 = e + g - w by rw [he_def, hg_def, hw_def, hP]; abel,
        show x 2 - x 0 = p + g by rw [hp_def, hg_def]; abel]
      simp only [inner_add_right, inner_sub_left, inner_add_left]
      rw [heg, pg', hwg]; ring
    have e3 : ⟪w, p⟫ = l' * ⟪p, p⟫ + m' * ⟪d, p⟫ := by
      rw [hlm', inner_add_left, real_inner_smul_left, real_inner_smul_left]
    have e4 : ⟪d, p⟫ = ⟪p, p⟫ - ⟪e, p⟫ := by
      rw [show d = p - e by rw [hpd]; abel, inner_sub_left]
    have e5 : ⟪d, p⟫ = ⟪p, p⟫ - ⟪x 2 - x 0, e⟫ := by rw [real_inner_comm]; exact ep2d
    have hdp : 0 < ⟪d, p⟫ := by rw [e5]; linarith
    have hbl : β * l' = α + β := by rw [hα_def, hβ_def]; linear_combination -bH
    rw [e1]
    rw [e2, e3] at hT
    have key : -α * ⟪p, p⟫ + β * ⟪g, g⟫ =
        β * (⟪e, p⟫ + ⟪g, g⟫ - (l' * ⟪p, p⟫ + m' * ⟪d, p⟫)) + β * ⟪d, p⟫ * (1 + m') := by
      linear_combination ⟪p, p⟫ * hbl - β * e4
    rw [key]
    have k1 : β * ⟪d, p⟫ * (1 + m') < 0 := mul_neg_of_pos_of_neg (mul_pos hβ hdp) hm'
    have k2 : β * (⟪e, p⟫ + ⟪g, g⟫ - (l' * ⟪p, p⟫ + m' * ⟪d, p⟫)) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hβ.le hT
    linarith
  -- the closed cell at `u` and the strict facings
  have hI : F.f 8 (x 2) - F.f 8 (x 0) < 0 := by
    rcases hnb with h | h
    · linarith [mul_pos_of_neg_of_neg (neg_neg_of_pos haI) h, mul_nonneg hbI (neg_nonneg.2 hD2.le)]
    · have := hbI' h
      linarith [mul_pos this (neg_pos.2 hD2), mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.2 haI.le) h2]
  have uA : 0 < ⟪F.N 0, u⟫ := by
    rw [hu, zA2, zA0]; linarith [mul_pos (add_pos hα hβ) (neg_pos.2 hA5)]
  have uB : 0 < ⟪F.N 1, u⟫ := by
    rw [hu, zB0]; linarith [mul_pos hα (sub_pos.2 hB25), mul_pos hβ (neg_pos.2 hB5)]
  have uE : 0 < ⟪F.N 4, u⟫ := by rw [hu, hE25, zE0]; linarith [mul_pos hβ (neg_pos.2 hE5)]
  have uC : ⟪F.N 2, u⟫ = 0 := by rw [hu, zC2, zC5, zC0]; ring
  have uD : ⟪F.N 3, u⟫ < 0 := by rw [hu, zD5, zD0]; linarith [mul_neg_of_pos_of_neg hα hD2]
  have uG : ⟪F.N 6, u⟫ < 0 := by rw [hu, zG2, zG5]; linarith [mul_neg_of_pos_of_neg hβ hG0]
  have uH : ⟪F.N 7, u⟫ = 0 := by rw [hu, zH2, hα_def, hβ_def]; ring
  have uI : ⟪F.N 8, u⟫ < 0 := by rw [hu, hI50]; linarith [mul_neg_of_pos_of_neg hα hI]
  have hcl : CellLe F U0264 D0264 u := by
    refine ⟨fun t ht => ?_, fun t ht => ?_⟩
    · simp only [U0264, Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl | rfl
      · exact uA.le
      · exact uB.le
      · exact uE.le
      · exact hFu.le
    · simp only [D0264, Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl | rfl | rfl
      · exact uC.le
      · exact uD.le
      · exact uG.le
      · exact uH.le
      · exact uI.le
  obtain ⟨a, ha⟩ := exists_cellAt_of_lex (F := F) (U := U0264) (Dn := D0264) (u₀ := u) (v := x 4 - x 2)
    (by
      intro t ht; simp only [U0264, Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl | rfl
      · exact Or.inl uA
      · exact Or.inl uB
      · exact Or.inl uE
      · exact Or.inl hFu)
    (by
      intro t ht; simp only [D0264, Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl | rfl | rfl
      · exact Or.inr ⟨by rw [uC]; simp, by rw [ip, zC2]; linarith⟩
      · exact Or.inl (by linarith)
      · exact Or.inl (by linarith)
      · exact Or.inr ⟨by rw [uH]; simp, by rw [ip, zH2]; linarith⟩
      · exact Or.inl (by linarith))
  -- a positive diagonal form at `a`: `x 6 - x 4 = λ e + ν N_D` with `λ ≥ 0 > ν`
  have hn3 : F.N 3 ≠ 0 := by
    intro h; have := ip 3 2 0; rw [h, inner_zero_left, zD0] at this; linarith
  obtain ⟨lam, nu, hln⟩ := orth_decomp he0 hn3 hg0 hen heg hng
    (show ⟪x 6 - x 4, g⟫ = 0 by
      rw [show x 6 - x 4 = w - e by rw [hw_def, he_def]; abel, inner_sub_left, hwg, heg, sub_zero])
  have hee : 0 < ⟪e, e⟫ := real_inner_self_pos.2 he0
  have hnn : 0 < ⟪F.N 3, F.N 3⟫ := real_inner_self_pos.2 hn3
  have hlam : 0 ≤ lam := by
    have h1 := congrArg (fun y => ⟪y, e⟫) hln
    simp only [inner_add_left, real_inner_smul_left] at h1
    rw [real_inner_comm e (F.N 3), hen, mul_zero, add_zero,
      show x 6 - x 4 = w - e by rw [hw_def, he_def]; abel, inner_sub_left] at h1
    by_contra h; push Not at h; linarith [mul_neg_of_neg_of_pos h hee]
  have hnu : nu < 0 := by
    have h1 := congrArg (fun y => ⟪F.N 3, y⟫) hln
    simp only [inner_add_right, inner_smul_right] at h1
    have hne : ⟪F.N 3, e⟫ = 0 := by rw [real_inner_comm]; exact hen
    rw [hne, mul_zero, zero_add, ip, zD4] at h1
    by_contra h; push Not at h; linarith [mul_nonneg h hnn.le]
  have c0 : c0264 0 = 0 := rfl
  have c1 : c0264 1 = 2 := rfl
  have c2 : c0264 2 = 6 := rfl
  have c3 : c0264 3 = 4 := rfl
  have hpos : ∃ q ∈ diagPairs, 0 < ⟪x (c0264 q.1) - x (c0264 q.2), a⟫ := by
    have hDa : ⟪F.N 3, a⟫ < 0 := ha.2 3 (by simp [D0264])
    by_cases h04 : 0 < ⟪x 0 - x 4, a⟫
    · exact ⟨(0, 3), by decide, by simp only [c0, c3]; exact h04⟩
    · push Not at h04
      refine ⟨(2, 3), by decide, ?_⟩
      simp only [c2, c3]
      have h1 := congrArg (fun y => ⟪y, a⟫) hln
      simp only [inner_add_left, real_inner_smul_left] at h1
      have hea : 0 ≤ ⟪e, a⟫ := by
        rw [he_def, show x 4 - x 0 = -(x 0 - x 4) by abel, inner_neg_left]; linarith
      rw [h1]; linarith [mul_nonneg hlam hea, mul_pos_of_neg_of_neg hnu hDa]
  rcases hT with hT | h20
  · exact isRupert_of_closedCell_q4 F hx (by decide) cyc0264 ha hcl ha.cellLe
      ⟨(0, 1), by decide, by simp only [c0, c1]; exact hf1 hT⟩ hpos
  -- `X 2 = 0`: `N_C = aC e + bC N_D` with `bC = 0` (from `f_C 2 = 0`) and `aC < 0`, so `z 0 < z 4` on the cell
  obtain ⟨aC, bC, hCab⟩ := orth_decomp he0 hn3 hg0 hen heg hng hCg
  have eC : ∀ v, ⟪F.N 2, v⟫ = aC * ⟪e, v⟫ + bC * ⟪F.N 3, v⟫ := by
    intro v; rw [hCab, inner_add_left, real_inner_smul_left, real_inner_smul_left]
  have hbC : bC = 0 := by
    have h1 := eC (x 2 - x 0)
    rw [ip, ip, zC2, zC0, real_inner_comm (x 2 - x 0) e, h20, zD0] at h1
    have : bC * F.f 3 (x 2) = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · exact h
    · linarith
  have haC : aC < 0 := by
    have h1 := eC e
    have r1 : ⟪F.N 2, e⟫ = F.f 2 (x 4) := by rw [he_def, ip, zC0, sub_zero]
    rw [hbC, zero_mul, add_zero, r1] at h1
    by_contra h; push Not at h; linarith [mul_nonneg h hee.le]
  have hCa : ⟪F.N 2, a⟫ < 0 := ha.2 2 (by simp [D0264])
  rw [eC, hbC, zero_mul, add_zero] at hCa
  have hea : 0 < ⟪e, a⟫ := by
    by_contra h; push Not at h; linarith [mul_nonneg_of_nonpos_of_nonpos haC.le h]
  refine isRupert_of_closedCell_q4 F hx (by decide) cyc0264 ha ha.cellLe ha.cellLe
    ⟨(0, 3), by decide, ?_⟩ hpos
  simp only [c0, c3]
  rw [show x 0 - x 4 = -e by rw [he_def]; abel, inner_neg_left]; linarith

/-- **The box corner gives `C ∥ I`**: on `R` with `X 2 = 0` and `X 6 = |e|²`, `⟪N_C, x 6 - x 3⟫ = 0`
(`N_C = a e + b N_D` with `b = 0`, and `⟪e, x 6 - x 3⟫ = X 6 - |e|² = 0`). -/
theorem box_ci (F : S0xFac 9 s0x_S24 x) (hP : x 3 = x 4 + x 5 - x 0)
    (hE : ⟪F.N 4, x 2 - x 3⟫ = 0) (hw : ⟪x 5 - x 0, x 2 - x 3⟫ = 0)
    (hs : ⟪x 5 - x 0, x 6 - x 0⟫ = 0) (h2 : ⟪x 2 - x 0, x 4 - x 0⟫ = 0)
    (h6 : ⟪x 6 - x 0, x 4 - x 0⟫ = ⟪x 4 - x 0, x 4 - x 0⟫) :
    ⟪F.N 2, x 6 - x 3⟫ = 0 := by
  obtain ⟨heg, hen, hng, hCg, -⟩ := rect_frame F hP hE hw hs
  have IS := F.inner_sub
  have hx := Minimality.H24.SAT.inj_of_fac F
  have he : x 4 - x 0 ≠ 0 := fun h => absurd (hx (sub_eq_zero.1 h)) (by decide)
  have hg : x 5 - x 0 ≠ 0 := fun h => absurd (hx (sub_eq_zero.1 h)) (by decide)
  have hD2 := F.neg 3 2 (by decide)
  have hn : F.N 3 ≠ 0 := by
    intro h; have := IS 3 2 0; rw [h, inner_zero_left, F.zero 3 0 (by decide)] at this; linarith
  obtain ⟨a, b, hab⟩ := orth_decomp he hn hg hen heg hng hCg
  have e2 := congrArg (fun y => ⟪y, x 2 - x 0⟫) hab
  simp only [inner_add_left, real_inner_smul_left] at e2
  rw [IS 2 2 0, IS 3 2 0, F.zero 2 2 (by decide), F.zero 2 0 (by decide), F.zero 3 0 (by decide),
    real_inner_comm (x 2 - x 0) (x 4 - x 0), h2] at e2
  have hb : b = 0 := by
    have : b * F.f 3 (x 2) = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · exact h
    · linarith
  rw [hab, hb, zero_smul, add_zero, real_inner_smul_left,
    show x 6 - x 3 = (x 6 - x 0) - (x 4 - x 0) - (x 5 - x 0) by rw [hP]; abel,
    inner_sub_right, inner_sub_right, heg, real_inner_comm (x 6 - x 0) (x 4 - x 0), h6]; ring

/-- The stratum `D` parallelogram, `E ∥ G`, outside the box corner `R₄` (`R ∩ {X 2 = 0, X 6 = |e|²}`). -/
theorem isRupert_eg_par4 (F : S0xFac 9 s0x_S24 x) (hP : x 3 = x 4 + x 5 - x 0)
    (hE : ⟪F.N 4, x 2 - x 3⟫ = 0)
    (hR : ¬ (⟪x 5 - x 0, x 2 - x 3⟫ = 0 ∧ ⟪x 5 - x 0, x 6 - x 0⟫ = 0 ∧ 0 ≤ ⟪x 6 - x 0, x 2 - x 3⟫ ∧
      ⟪x 2 - x 0, x 4 - x 0⟫ = 0 ∧ ⟪x 6 - x 0, x 4 - x 0⟫ = ⟪x 4 - x 0, x 4 - x 0⟫)) :
    IsRupert (univ.image x) := by
  by_cases hR2 : ⟪x 5 - x 0, x 2 - x 3⟫ = 0 ∧ ⟪x 5 - x 0, x 6 - x 0⟫ = 0 ∧ 0 ≤ ⟪x 6 - x 0, x 2 - x 3⟫ ∧
      ⟪x 2 - x 0, x 4 - x 0⟫ ≤ 0 ∧ ⟪x 4 - x 0, x 4 - x 0⟫ ≤ ⟪x 6 - x 0, x 4 - x 0⟫
  swap
  · exact isRupert_eg_notR2 F hP hE hR2
  obtain ⟨hw, hs, hh, h2, h6⟩ := hR2
  rcases h2.lt_or_eq with h2 | h2
  · by_cases hT : 0 < ⟪x 3 - x 6, x 2 - x 0⟫
    · exact isRupert_eg_R2v F hP hE hw hs h2 h6 hT
    · exact isRupert_eg_R2c F hP hE hw hs h2.le h6 (Or.inl (not_lt.1 hT)) (Or.inl h2)
  · rcases h6.lt_or_eq with h6' | h6'
    · exact isRupert_eg_R2c F hP hE hw hs h2.le h6 (Or.inr h2) (Or.inr h6')
    · exact absurd ⟨hw, hs, hh, h2, h6'.symm⟩ hR

open Minimality.H24K.SAT in
/-- The image of `isRupert_eg_par4` under `σ = (2 6)(4 5)`. -/
theorem isRupert_ci_par4 (F : S0xFac 9 s0x_S24 x) (hP : x 3 = x 4 + x 5 - x 0)
    (hC : ⟪F.N 2, x 6 - x 3⟫ = 0)
    (hR : ¬ (⟪x 4 - x 0, x 6 - x 3⟫ = 0 ∧ ⟪x 4 - x 0, x 2 - x 0⟫ = 0 ∧ 0 ≤ ⟪x 2 - x 0, x 6 - x 3⟫ ∧
      ⟪x 6 - x 0, x 5 - x 0⟫ = 0 ∧ ⟪x 2 - x 0, x 5 - x 0⟫ = ⟪x 5 - x 0, x 5 - x 0⟫)) :
    IsRupert (univ.image x) := by
  have h := isRupert_eg_par4 (facSig F) (x := x ∘ wallSig)
    (by show x 3 = x 5 + x 4 - x 0; rw [hP]; abel) hC hR
  have e : Finset.univ.image (x ∘ wallSig) = Finset.univ.image x := by
    ext y
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Function.comp]
    constructor
    · rintro ⟨i, rfl⟩; exact ⟨_, rfl⟩
    · rintro ⟨i, rfl⟩; exact ⟨wallSig i, by rw [wallSig_invol]⟩
  rwa [e] at h

/-- **The stratum `D` parallelogram, `E ∥ G`**, every case except the box corner with `T ≤ 0`:
`R₄' = R ∩ {X 2 = 0, X 6 = |e|², T ≤ 0}` (`D` a rectangle, `C ∥ I` and `E ∥ G` both perpendicular to `D`).
On the box corner with `T > 0` the corner is `C ∥ I` (`box_ci`) outside that stratum's exclusion. -/
theorem isRupert_eg_par (F : S0xFac 9 s0x_S24 x) (hP : x 3 = x 4 + x 5 - x 0)
    (hE : ⟪F.N 4, x 2 - x 3⟫ = 0)
    (hR : ¬ (⟪x 5 - x 0, x 2 - x 3⟫ = 0 ∧ ⟪x 5 - x 0, x 6 - x 0⟫ = 0 ∧ 0 ≤ ⟪x 6 - x 0, x 2 - x 3⟫ ∧
      ⟪x 2 - x 0, x 4 - x 0⟫ = 0 ∧ ⟪x 6 - x 0, x 4 - x 0⟫ = ⟪x 4 - x 0, x 4 - x 0⟫ ∧
      ⟪x 3 - x 6, x 2 - x 0⟫ ≤ 0)) :
    IsRupert (univ.image x) := by
  by_cases h4 : ⟪x 5 - x 0, x 2 - x 3⟫ = 0 ∧ ⟪x 5 - x 0, x 6 - x 0⟫ = 0 ∧ 0 ≤ ⟪x 6 - x 0, x 2 - x 3⟫ ∧
      ⟪x 2 - x 0, x 4 - x 0⟫ = 0 ∧ ⟪x 6 - x 0, x 4 - x 0⟫ = ⟪x 4 - x 0, x 4 - x 0⟫
  swap
  · exact isRupert_eg_par4 F hP hE h4
  obtain ⟨hw, hs, hh, h2, h6⟩ := h4
  have hT : 0 < ⟪x 3 - x 6, x 2 - x 0⟫ := by
    by_contra hT; exact hR ⟨hw, hs, hh, h2, h6, not_lt.1 hT⟩
  refine isRupert_ci_par4 F hP (box_ci F hP hE hw hs h2 h6) fun h => ?_
  have : ⟪x 2 - x 0, x 6 - x 3⟫ = -⟪x 3 - x 6, x 2 - x 0⟫ := by
    rw [real_inner_comm, show x 6 - x 3 = -(x 3 - x 6) by abel, inner_neg_left]
  linarith [h.2.2.1]

/-- **The `E ∥ G` stratum from the SAT-level facts**: `KD0435 = KD0534 = 0` and `E:23 = 0`, outside `R₄'`. -/
theorem isRupert_parEG (F : S0xFac 9 s0x_S24 x)
    (hD : det3 (x 0 - x 4) (x 3 - x 5) (F.N 3) = 0 ∧ det3 (x 0 - x 5) (x 3 - x 4) (F.N 3) = 0)
    (hEG : ⟪F.N 4, x 2 - x 3⟫ = 0)
    (hR : ¬ (⟪x 5 - x 0, x 2 - x 3⟫ = 0 ∧ ⟪x 5 - x 0, x 6 - x 0⟫ = 0 ∧ 0 ≤ ⟪x 6 - x 0, x 2 - x 3⟫ ∧
      ⟪x 2 - x 0, x 4 - x 0⟫ = 0 ∧ ⟪x 6 - x 0, x 4 - x 0⟫ = ⟪x 4 - x 0, x 4 - x 0⟫ ∧
      ⟪x 3 - x 6, x 2 - x 0⟫ ≤ 0)) :
    IsRupert (univ.image x) :=
  isRupert_eg_par F (par_of_KD F hD) hEG hR

open Minimality.H24K.SAT in
/-- **The stratum `D` parallelogram, `C ∥ I`** (the image of `isRupert_eg_par` under `σ = (2 6)(4 5)`). -/
theorem isRupert_ci_par (F : S0xFac 9 s0x_S24 x) (hP : x 3 = x 4 + x 5 - x 0)
    (hC : ⟪F.N 2, x 6 - x 3⟫ = 0)
    (hR : ¬ (⟪x 4 - x 0, x 6 - x 3⟫ = 0 ∧ ⟪x 4 - x 0, x 2 - x 0⟫ = 0 ∧ 0 ≤ ⟪x 2 - x 0, x 6 - x 3⟫ ∧
      ⟪x 6 - x 0, x 5 - x 0⟫ = 0 ∧ ⟪x 2 - x 0, x 5 - x 0⟫ = ⟪x 5 - x 0, x 5 - x 0⟫ ∧
      ⟪x 3 - x 2, x 6 - x 0⟫ ≤ 0)) :
    IsRupert (univ.image x) := by
  have h := isRupert_eg_par (facSig F) (x := x ∘ wallSig)
    (by show x 3 = x 5 + x 4 - x 0; rw [hP]; abel) hC hR
  have e : Finset.univ.image (x ∘ wallSig) = Finset.univ.image x := by
    ext y
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Function.comp]
    constructor
    · rintro ⟨i, rfl⟩; exact ⟨_, rfl⟩
    · rintro ⟨i, rfl⟩; exact ⟨wallSig i, by rw [wallSig_invol]⟩
  rwa [e] at h

/-- **The `C ∥ I` stratum from the SAT-level facts**: `KD0435 = KD0534 = 0` and `C:36 = 0`, outside the image
of `R₄'`. -/
theorem isRupert_parCI (F : S0xFac 9 s0x_S24 x)
    (hD : det3 (x 0 - x 4) (x 3 - x 5) (F.N 3) = 0 ∧ det3 (x 0 - x 5) (x 3 - x 4) (F.N 3) = 0)
    (hCI : ⟪F.N 2, x 3 - x 6⟫ = 0)
    (hR : ¬ (⟪x 4 - x 0, x 6 - x 3⟫ = 0 ∧ ⟪x 4 - x 0, x 2 - x 0⟫ = 0 ∧ 0 ≤ ⟪x 2 - x 0, x 6 - x 3⟫ ∧
      ⟪x 6 - x 0, x 5 - x 0⟫ = 0 ∧ ⟪x 2 - x 0, x 5 - x 0⟫ = ⟪x 5 - x 0, x 5 - x 0⟫ ∧
      ⟪x 3 - x 2, x 6 - x 0⟫ ≤ 0)) :
    IsRupert (univ.image x) :=
  isRupert_ci_par F (par_of_KD F hD)
    (by rw [show x 6 - x 3 = -(x 3 - x 6) by abel, inner_neg_right, hCI, neg_zero]) hR

end Minimality.T24.Par
