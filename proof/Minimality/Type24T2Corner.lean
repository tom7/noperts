module

public import Minimality.Type24T2Cone
public import Minimality.Type24FootLex

/-!
# Corner rule `T2C` for the type-24 cone `T_2` (`cA2`)

`z_q = ⟪x q, ·⟫`.  Lemma Z (`z₀ < z₁`) and the former Lemma AH (`z₀ < z₅`, `z₀ < z₃`; pruned, a special case) are the two ends of one rule:

* `cA2_robUni_of_t2c`: every open `cA2` view `uT2 x β γ` with
  `z₀ < z₁  ∨  (z₀ < z₅ ∧ (z₀ ≤ z₆ ∨ z₀ ≤ z₃))` has `RobUni` depths on `cA2 = ![0, 5, 3, 6, 1]` under `OB1 x`
  (Fact 1 `uT2_depth_signs`, Fact 2 `cA2_not_back_03_56`).
* `rayRLex_of_t2c`: the rule at a corner ray `x v - x 2` of the closed cell (facets strict or vanishing with the sign
  of the push `dl = uT2 x β₀ γ₀`; the letters strict or tied with the sign of `dl`) gives `FootLex.RayRLex x F 2 v`.
  Facts 1 and 2 are not needed at the ray itself: they are used at the open view `ray + t • dl` (any `t > 0` small),
  and `RobUni` there gives the lexicographic `RobUniLex` at the ray with `d₁ = dl`, `d₂ = 0`.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace
open Filter Topology
open Finset
open Minimality Minimality.H21 Minimality.T24.SAT Minimality.T24.M4
open Minimality.T24.HC Minimality.T24.SF Minimality.T24.DeepC

namespace Minimality.T24.TwoCone

/-- **T2C letters** on the depths `z_q` (any four reals `z₀, z₁, z₃, z₅, z₆` standing for `⟪x q, ·⟫`). -/
def T2CLetter (z0 z1 z3 z5 z6 : ℝ) : Prop :=
  z0 < z1 ∨ (z0 < z5 ∧ (z0 ≤ z6 ∨ z0 ≤ z3))

/-- **Rule T2C (open cell):** under `OB1 x`, every open-cell view `uT2 x β γ` of `cA2` satisfying the T2C letter has
`RobUni` depths on `cA2 = ![0, 5, 3, 6, 1]`. -/
theorem cA2_robUni_of_t2c {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hO : H24K.SAT.OB1 x)
    {beta gamma : ℝ} (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (hcell : CellAt F U_A2 D_A2 (uT2 x beta gamma))
    (hlet : T2CLetter ⟪x 0, uT2 x beta gamma⟫ ⟪x 1, uT2 x beta gamma⟫ ⟪x 3, uT2 x beta gamma⟫
      ⟪x 5, uT2 x beta gamma⟫ ⟪x 6, uT2 x beta gamma⟫) :
    H21.RobUni (fun i => ⟪x (cA2 i), uT2 x beta gamma⟫) := by
  rcases hlet with hz | ⟨h05, h6⟩
  · have hz' : ⟪x 0 - x 1, uT2 x beta gamma⟫ < 0 := by rw [inner_sub_left]; linarith
    exact cA2_robUni_of_z0_lt F hO hbeta hgamma hcell hz'
  have hF1 : ⟪x 0, uT2 x beta gamma⟫ ≤ ⟪x 1, uT2 x beta gamma⟫ →
      ⟪x 1, uT2 x beta gamma⟫ < ⟪x 6, uT2 x beta gamma⟫ := by
    intro h
    have h0 : ⟪x 0 - x 1, uT2 x beta gamma⟫ ≤ 0 := by rw [inner_sub_left]; linarith
    have h6 := (uT2_depth_signs F hO hbeta hgamma).2 h0
    rw [inner_sub_left] at h6; linarith
  have hnb6 := cA2_not_back_03_56 F hcell
  intro B b c d hb hbc hcd hdk
  have hb5 : b < 5 := by omega
  have hc5 : c < 5 := by omega
  have hd5 : d < 5 := by omega
  have hB : B = 0 ∨ B = 1 ∨ B = 2 ∨ B = 3 ∨ B = 4 := by revert B; decide
  have hZ5 :
      ((0 : ZMod 5) + 1 = 1 ∧ (0 : ZMod 5) + 2 = 2 ∧ (0 : ZMod 5) + 3 = 3 ∧ (0 : ZMod 5) + 4 = 4) ∧
      ((1 : ZMod 5) + 1 = 2 ∧ (1 : ZMod 5) + 2 = 3 ∧ (1 : ZMod 5) + 3 = 4 ∧ (1 : ZMod 5) + 4 = 0) ∧
      ((2 : ZMod 5) + 1 = 3 ∧ (2 : ZMod 5) + 2 = 4 ∧ (2 : ZMod 5) + 3 = 0 ∧ (2 : ZMod 5) + 4 = 1) ∧
      ((3 : ZMod 5) + 1 = 4 ∧ (3 : ZMod 5) + 2 = 0 ∧ (3 : ZMod 5) + 3 = 1 ∧ (3 : ZMod 5) + 4 = 2) ∧
      ((4 : ZMod 5) + 1 = 0 ∧ (4 : ZMod 5) + 2 = 1 ∧ (4 : ZMod 5) + 3 = 2 ∧ (4 : ZMod 5) + 4 = 3) := by
    decide
  have hev : cA2 0 = 0 ∧ cA2 1 = 5 ∧ cA2 2 = 3 ∧ cA2 3 = 6 ∧ cA2 4 = 1 := by decide
  rcases hB with rfl | rfl | rfl | rfl | rfl <;>
  · interval_cases b <;> interval_cases c <;> interval_cases d <;>
    · simp only [Nat.cast_one, Nat.cast_ofNat, hZ5, hev]
      rintro ⟨h1, h2, h3, h4⟩
      rcases le_or_gt ⟪x 0, uT2 x beta gamma⟫ ⟪x 1, uT2 x beta gamma⟫ with hc | hc
      · have h6' := hF1 hc
        first
          | linarith
          | exact hnb6 (max_le (le_min (by linarith) (by linarith)) (le_min (by linarith) (by linarith)))
      · first
          | linarith
          | exact hnb6 (max_le (le_min (by linarith) (by linarith)) (le_min (by linarith) (by linarith)))
          | (rcases h6 with h6 | h6 <;>
              exact hnb6 (max_le (le_min (by linarith) (by linarith)) (le_min (by linarith) (by linarith))))


/-! ## The corner ray -/

/-- Lexicographic strict inequality at a ray with push `dl`: `⟪x p - x q, r⟫ < 0`, or tied with `⟪x p - x q, dl⟫ < 0`. -/
def LexLtAt (x : Fin 7 → ℝ³) (r dl : ℝ³) (p q : Fin 7) : Prop :=
  ⟪x p - x q, r⟫ < 0 ∨ (⟪x p - x q, r⟫ = 0 ∧ ⟪x p - x q, dl⟫ < 0)

/-- Lexicographic weak inequality at a ray with push `dl`. -/
def LexLeAt (x : Fin 7 → ℝ³) (r dl : ℝ³) (p q : Fin 7) : Prop :=
  ⟪x p - x q, r⟫ < 0 ∨ (⟪x p - x q, r⟫ = 0 ∧ ⟪x p - x q, dl⟫ ≤ 0)

/-- **T2C at a ray `r` with push `dl`** (the letters `z₀ < z₁`, or `z₀ < z₅` and (`z₀ ≤ z₆` or `z₀ ≤ z₃`) on
the depths `⟪x q, r⟫`, ties broken by `dl`). -/
def T2CAt (x : Fin 7 → ℝ³) (r dl : ℝ³) : Prop :=
  LexLtAt x r dl 0 1 ∨ (LexLtAt x r dl 0 5 ∧ (LexLeAt x r dl 0 6 ∨ LexLeAt x r dl 0 3))

private theorem ev_lt_lex {A B : ℝ} (h : A < 0 ∨ (A = 0 ∧ B < 0)) :
    ∀ᶠ t : ℝ in 𝓝[>] 0, A + t * B < 0 := by
  rcases h with h | ⟨rfl, h⟩
  · filter_upwards [Minimality.T24.Belt.ev_neg A B h] with t ht using by linarith [mul_comm B t]
  · filter_upwards [Minimality.T24.Belt.ev_gt0] with t ht
    nlinarith

private theorem ev_le_lex {A B : ℝ} (h : A < 0 ∨ (A = 0 ∧ B ≤ 0)) :
    ∀ᶠ t : ℝ in 𝓝[>] 0, A + t * B ≤ 0 := by
  rcases h with h | ⟨rfl, h⟩
  · filter_upwards [Minimality.T24.Belt.ev_neg A B h] with t ht using by linarith [mul_comm B t]
  · filter_upwards [Minimality.T24.Belt.ev_gt0] with t ht
    nlinarith

private theorem ev_pos_lex {A B : ℝ} (h : 0 < A ∨ (A = 0 ∧ 0 < B)) :
    ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < A + t * B := by
  rcases h with h | ⟨rfl, h⟩
  · filter_upwards [Minimality.T24.Belt.ev_pos A B h] with t ht using by linarith [mul_comm B t]
  · filter_upwards [Minimality.T24.Belt.ev_gt0] with t ht
    nlinarith

private theorem ev_notLexPos {A B : ℝ} (h : ¬ LexCell.LexPos3 A B 0) :
    ∀ᶠ t : ℝ in 𝓝[>] 0, A + t * B ≤ 0 := by
  apply ev_le_lex
  unfold LexCell.LexPos3 at h
  push Not at h
  rcases lt_or_eq_of_le h.1 with h1 | h1
  · exact Or.inl h1
  · exact Or.inr ⟨h1, h.2 h1 |>.1⟩

/-- **Open-view step:** at the ray `r = x v - x 2 = a e₀ + b e₂ + c e₆` (`e₀ = x 0 - x 1`, ...; `a, c ≥ 0`, `b ≤ 0`)
with push `dl = uT2 x β₀ γ₀`, facets strict or vanishing with the sign of `dl` and the T2C letters, the depths
`⟪x q, r⟫ + t ⟪x q, dl⟫` on `cA2` are `RobUni` for all small `t > 0`. -/
theorem cA2_eventually_robUni_of_t2c {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hO : H24K.SAT.OB1 x)
    {beta0 gamma0 : ℝ} (hb0 : 0 < beta0) (hg0 : 0 < gamma0) {r : ℝ³} {a b c : ℝ}
    (hr : r = a • (x 0 - x 1) + b • (x 2 - x 1) + c • (x 6 - x 1)) (ha : 0 ≤ a) (hb : b ≤ 0) (hc : 0 ≤ c)
    (hU : ∀ s ∈ U_A2, 0 < ⟪F.N s, r⟫ ∨ (⟪F.N s, r⟫ = 0 ∧ 0 < ⟪F.N s, uT2 x beta0 gamma0⟫))
    (hD : ∀ s ∈ D_A2, ⟪F.N s, r⟫ < 0 ∨ (⟪F.N s, r⟫ = 0 ∧ ⟪F.N s, uT2 x beta0 gamma0⟫ < 0))
    (hlet : T2CAt x r (uT2 x beta0 gamma0)) :
    ∀ᶠ t : ℝ in 𝓝[>] 0, H21.RobUni
      (fun i => ⟪x (cA2 i), r⟫ + t * ⟪x (cA2 i), uT2 x beta0 gamma0⟫) := by
  set dl := uT2 x beta0 gamma0 with hdl
  have hfU : ∀ᶠ t : ℝ in 𝓝[>] 0, ∀ s ∈ U_A2, 0 < ⟪F.N s, r⟫ + t * ⟪F.N s, dl⟫ :=
    (Filter.eventually_all_finset _).2 fun s hs => ev_pos_lex (hU s hs)
  have hfD : ∀ᶠ t : ℝ in 𝓝[>] 0, ∀ s ∈ D_A2, ⟪F.N s, r⟫ + t * ⟪F.N s, dl⟫ < 0 :=
    (Filter.eventually_all_finset _).2 fun s hs => ev_lt_lex (hD s hs)
  have hL : ∀ᶠ t : ℝ in 𝓝[>] 0, T2CLetter (⟪x 0, r⟫ + t * ⟪x 0, dl⟫) (⟪x 1, r⟫ + t * ⟪x 1, dl⟫)
      (⟪x 3, r⟫ + t * ⟪x 3, dl⟫) (⟪x 5, r⟫ + t * ⟪x 5, dl⟫) (⟪x 6, r⟫ + t * ⟪x 6, dl⟫) := by
    have lt' : ∀ p q, LexLtAt x r dl p q → ∀ᶠ t : ℝ in 𝓝[>] 0,
        ⟪x p, r⟫ + t * ⟪x p, dl⟫ < ⟪x q, r⟫ + t * ⟪x q, dl⟫ := by
      intro p q h
      filter_upwards [ev_lt_lex h] with t ht
      rw [inner_sub_left, inner_sub_left] at ht; linarith
    have le' : ∀ p q, LexLeAt x r dl p q → ∀ᶠ t : ℝ in 𝓝[>] 0,
        ⟪x p, r⟫ + t * ⟪x p, dl⟫ ≤ ⟪x q, r⟫ + t * ⟪x q, dl⟫ := by
      intro p q h
      filter_upwards [ev_le_lex h] with t ht
      rw [inner_sub_left, inner_sub_left] at ht; linarith
    rcases hlet with h | ⟨h5, h6 | h3⟩
    · filter_upwards [lt' _ _ h] with t ht using Or.inl ht
    · filter_upwards [lt' _ _ h5, le' _ _ h6] with t t5 t6 using Or.inr ⟨t5, Or.inl t6⟩
    · filter_upwards [lt' _ _ h5, le' _ _ h3] with t t5 t3 using Or.inr ⟨t5, Or.inr t3⟩
  filter_upwards [hfU, hfD, hL, Minimality.T24.Belt.ev_gt0] with t hu hd hl ht
  have hat : 0 < a + t := by linarith
  set beta := (-b + t * beta0) / (a + t) with hbeta_def
  set gamma := (c + t * gamma0) / (a + t) with hgamma_def
  have hbeta : 0 < beta := div_pos (by nlinarith) hat
  have hgamma : 0 < gamma := div_pos (by nlinarith) hat
  have hview : uT2 x beta gamma = (a + t)⁻¹ • (r + t • dl) := by
    have e1 : (a + t)⁻¹ * (b - t * beta0) = -beta := by
      rw [hbeta_def]; field_simp; ring
    have e2 : (a + t)⁻¹ * (c + t * gamma0) = gamma := by
      rw [hgamma_def]; field_simp
    have e0 : (a + t)⁻¹ * (a + t) = 1 := inv_mul_cancel₀ hat.ne'
    have : r + t • dl = (a + t) • (x 0 - x 1) + (b - t * beta0) • (x 2 - x 1) +
        (c + t * gamma0) • (x 6 - x 1) := by
      rw [hr, hdl, uT2, capView]; module
    rw [this, uT2, capView, smul_add, smul_add, smul_smul, smul_smul, smul_smul, e0, e1, e2, one_smul]
  have hz : ∀ q : Fin 7, ⟪x q, uT2 x beta gamma⟫ = (a + t)⁻¹ * (⟪x q, r⟫ + t * ⟪x q, dl⟫) := by
    intro q
    rw [hview, real_inner_smul_right, inner_add_right, real_inner_smul_right]
  have hN : ∀ s : Fin 9, ⟪F.N s, uT2 x beta gamma⟫ = (a + t)⁻¹ * (⟪F.N s, r⟫ + t * ⟪F.N s, dl⟫) := by
    intro s
    rw [hview, real_inner_smul_right, inner_add_right, real_inner_smul_right]
  have hia : 0 < (a + t)⁻¹ := inv_pos.mpr hat
  have hcell : CellAt F U_A2 D_A2 (uT2 x beta gamma) :=
    ⟨fun s hs => by rw [hN]; exact mul_pos hia (hu s hs),
     fun s hs => by rw [hN]; exact mul_neg_of_pos_of_neg hia (hd s hs)⟩
  have hlet' : T2CLetter ⟪x 0, uT2 x beta gamma⟫ ⟪x 1, uT2 x beta gamma⟫ ⟪x 3, uT2 x beta gamma⟫
      ⟪x 5, uT2 x beta gamma⟫ ⟪x 6, uT2 x beta gamma⟫ := by
    simp only [hz, T2CLetter] at hl ⊢
    rcases hl with h | ⟨h5, h6 | h3⟩
    · exact Or.inl (mul_lt_mul_of_pos_left h hia)
    · exact Or.inr ⟨mul_lt_mul_of_pos_left h5 hia, Or.inl (mul_le_mul_of_nonneg_left h6 hia.le)⟩
    · exact Or.inr ⟨mul_lt_mul_of_pos_left h5 hia, Or.inr (mul_le_mul_of_nonneg_left h3 hia.le)⟩
  have hR := cA2_robUni_of_t2c F hO hbeta hgamma hcell hlet'
  intro B b' c' d' h1 h2 h3 h4 hcr
  apply hR B b' c' d' h1 h2 h3 h4
  simp only [hz]
  obtain ⟨e1, e2, e3, e4⟩ := hcr
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply mul_le_mul_of_nonneg_left (by assumption) hia.le


/-- **Rule T2C at a corner ray (`RayRLex` form):** `r = x v - x 2 = a e₀ + b e₂ + c e₆` (`a, c ≥ 0`, `b ≤ 0`) with the
`cA2` facet pattern at the ray (strict, or vanishing with the sign of the push `dl = uT2 x β₀ γ₀`) and the T2C
letters on the depths at the ray (ties broken by `dl`).  Facts 1 and 2 are used at the open views `r + t • dl`;
`RobUni` there gives the lexicographic `RobUniLex` at the ray (`d₁ = dl`, `d₂ = 0`). -/
theorem rayRLex_of_t2c {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hO : H24K.SAT.OB1 x) (v : Fin 7)
    {beta0 gamma0 : ℝ} (hb0 : 0 < beta0) (hg0 : 0 < gamma0) {a b c : ℝ}
    (hr : x v - x 2 = a • (x 0 - x 1) + b • (x 2 - x 1) + c • (x 6 - x 1)) (ha : 0 ≤ a) (hb : b ≤ 0)
    (hc : 0 ≤ c)
    (hU : ∀ s ∈ U_A2, 0 < ⟪F.N s, x v - x 2⟫ ∨
      (⟪F.N s, x v - x 2⟫ = 0 ∧ 0 < ⟪F.N s, uT2 x beta0 gamma0⟫))
    (hD : ∀ s ∈ D_A2, ⟪F.N s, x v - x 2⟫ < 0 ∨
      (⟪F.N s, x v - x 2⟫ = 0 ∧ ⟪F.N s, uT2 x beta0 gamma0⟫ < 0))
    (hlet : T2CAt x (x v - x 2) (uT2 x beta0 gamma0)) :
    FootLex.RayRLex x F 2 v := by
  set dl := uT2 x beta0 gamma0 with hdl
  have hev := cA2_eventually_robUni_of_t2c F hO hb0 hg0 hr ha hb hc hU hD hlet
  have hD' : univ \ U_A2 = D_A2 := by decide
  refine ⟨5, inferInstance, cA2, U_A2, dl, 0, by norm_num, cA2_inj, hD' ▸ cA2_cyc, ?_, ?_, ?_⟩
  · intro s hs
    rcases hU s hs with h | ⟨h0, h1⟩
    · exact Or.inl h
    · exact Or.inr ⟨h0, Or.inl h1⟩
  · intro s hs
    rw [hD'] at hs
    rcases hD s hs with h | ⟨h0, h1⟩
    · exact Or.inl (neg_pos.2 h)
    · exact Or.inr ⟨by rw [h0, neg_zero], Or.inl (neg_pos.2 h1)⟩
  · intro B b' c' d' h1 h2 h3 h4
    by_contra hn
    simp only [LexCell.LexLt3, not_or] at hn
    obtain ⟨n1, n2, n3, n4⟩ := hn
    have f : ∀ p q : ZMod 5, ¬ LexCell.LexPos3 (⟪x (cA2 q), x v - x 2⟫ - ⟪x (cA2 p), x v - x 2⟫)
        (⟪x (cA2 q), dl⟫ - ⟪x (cA2 p), dl⟫) 0 → ∀ᶠ t : ℝ in 𝓝[>] 0,
        ⟪x (cA2 q), x v - x 2⟫ + t * ⟪x (cA2 q), dl⟫ ≤ ⟪x (cA2 p), x v - x 2⟫ + t * ⟪x (cA2 p), dl⟫ := by
      intro p q h
      filter_upwards [ev_notLexPos h] with t ht
      linarith
    have g : ∀ p q : ZMod 5, ¬ LexCell.LexPos3 (⟪x (cA2 q), x v - x 2⟫ - ⟪x (cA2 p), x v - x 2⟫)
        (⟪x (cA2 q), dl⟫ - ⟪x (cA2 p), dl⟫) (⟪x (cA2 q), (0 : ℝ³)⟫ - ⟪x (cA2 p), (0 : ℝ³)⟫) →
        ∀ᶠ t : ℝ in 𝓝[>] 0, ⟪x (cA2 q), x v - x 2⟫ + t * ⟪x (cA2 q), dl⟫ ≤
          ⟪x (cA2 p), x v - x 2⟫ + t * ⟪x (cA2 p), dl⟫ := by
      intro p q h
      simp only [inner_zero_right, sub_zero] at h
      exact f p q h
    obtain ⟨t, ht1, ht2⟩ := ((hev.and (((g _ _ n1).and (g _ _ n2)).and ((g _ _ n3).and (g _ _ n4))))).exists
    exact ht1 B b' c' d' h1 h2 h3 h4 ⟨ht2.1.1, ht2.1.2, ht2.2.1, ht2.2.2⟩

theorem lexAny_of_t2c {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hO : H24K.SAT.OB1 x) (v : Fin 7)
    {beta0 gamma0 : ℝ} (hb0 : 0 < beta0) (hg0 : 0 < gamma0) {a b c : ℝ}
    (hr : x v - x 2 = a • (x 0 - x 1) + b • (x 2 - x 1) + c • (x 6 - x 1)) (ha : 0 ≤ a) (hb : b ≤ 0)
    (hc : 0 ≤ c)
    (hU : ∀ s ∈ U_A2, 0 < ⟪F.N s, x v - x 2⟫ ∨
      (⟪F.N s, x v - x 2⟫ = 0 ∧ 0 < ⟪F.N s, uT2 x beta0 gamma0⟫))
    (hD : ∀ s ∈ D_A2, ⟪F.N s, x v - x 2⟫ < 0 ∨
      (⟪F.N s, x v - x 2⟫ = 0 ∧ ⟪F.N s, uT2 x beta0 gamma0⟫ < 0))
    (hlet : T2CAt x (x v - x 2) (uT2 x beta0 gamma0)) :
    Gen.LexAny F :=
  FootLex.lexAny_of_rayRLex (rayRLex_of_t2c F hO v hb0 hg0 hr ha hb hc hU hD hlet)


end Minimality.T24.TwoCone
