module

public import Minimality.Type24T2Corner

/-!
# Lemma P0 and the edge region `P0Edge025` for the type-24 cone `T_2` (`cA2`): vertex 0 the peak

`z_q = ⟪x q, ·⟫` on the rim `cA2 = ![0, 5, 3, 6, 1]`.  Lemma Z (`z₀ < z₁`), Lemma AH (`z₀ < z₅`, `z₀ < z₃`) and rule
T2C all need vertex 0 NOT to be the peak.  With `z₀` the largest depth the rim is unimodal iff the arc
`5 → 3 → 6 → 1` has a single valley, i.e. (strictly) `z₆ < z₃ < z₅` (valley at 6 or 1) or `z₃ < z₆ < z₁`
(valley at 3 or 5).  Neither chain needs `z₀` to be the peak:

* `cA2_robUni_of_p0`: every view `uT2 x β γ` (`β, γ > 0`) with `P0Letter` (`z₆ < z₃ < z₅` or `z₃ < z₆ < z₁`) has
  `RobUni` depths on `cA2` under `OB1 x`.  Only Fact 1 (`uT2_depth_signs`) is used; the cell sign pattern and
  Fact 2 are not needed (the `LexAny` form `cA2_lexAny_of_p0` needs the open cell for the cell certificate).
* `P0Edge025`: on the `025` edge line `r p = x₅ - x₂ + p (x₀ - x₂)` (facet `025` edge-on), some `p` with the other
  `cA2` facets strict (`012` is automatic) and `z₆ < z₃ < z₅` at `r p`.  The push `uT2 x 2 1` (`⟪N₀₂₅, ·⟫ = f₀₂₅(x₆) < 0`)
  enters the open cell (`cA2_exists_of_p0Edge025`), hence `Gen.LexAny F` (`lexAny_of_p0Edge025`, `π_24` twin, hole
  facts).  This is the vertex-0-peak region of the w1_7_3 lemma gap (nopert229 FACENORM24.md A2PEAK).
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

/-- **P0 letters** on the depths: `z₆ < z₃ < z₅` or `z₃ < z₆ < z₁` (the vertex-0-peak branches of `cA2`). -/
def P0Letter (z1 z3 z5 z6 : ℝ) : Prop :=
  (z6 < z3 ∧ z3 < z5) ∨ (z3 < z6 ∧ z6 < z1)

/-- **Lemma P0:** under `OB1 x`, every view `uT2 x β γ` (`β, γ > 0`; the `cA2` cell is not needed) satisfying the
P0 letter has `RobUni` depths on `cA2 = ![0, 5, 3, 6, 1]`.  Only Fact 1 (`uT2_depth_signs`) is used: a crown would
need `z₀ ≤ z₁` together with `z₆ ≤ z₁`, and Fact 1 turns `z₀ ≤ z₁` into `z₁ < z₆`. -/
theorem cA2_robUni_of_p0 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hO : H24K.SAT.OB1 x)
    {beta gamma : ℝ} (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (hlet : P0Letter ⟪x 1, uT2 x beta gamma⟫ ⟪x 3, uT2 x beta gamma⟫ ⟪x 5, uT2 x beta gamma⟫
      ⟪x 6, uT2 x beta gamma⟫) :
    H21.RobUni (fun i => ⟪x (cA2 i), uT2 x beta gamma⟫) := by
  have hF1 : ⟪x 0, uT2 x beta gamma⟫ ≤ ⟪x 1, uT2 x beta gamma⟫ →
      ⟪x 1, uT2 x beta gamma⟫ < ⟪x 6, uT2 x beta gamma⟫ := by
    intro h
    have h0 : ⟪x 0 - x 1, uT2 x beta gamma⟫ ≤ 0 := by rw [inner_sub_left]; linarith
    have h6 := (uT2_depth_signs F hO hbeta hgamma).2 h0
    rw [inner_sub_left] at h6; linarith
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
        rcases hlet with ⟨l1, l2⟩ | ⟨l1, l2⟩ <;> linarith
      · rcases hlet with ⟨l1, l2⟩ | ⟨l1, l2⟩ <;> linarith

/-- **Lemma P0 (`LexAny` form):** `cA2` open cell + `OB1` + the P0 letter gives `Gen.LexAny F`. -/
theorem cA2_lexAny_of_p0 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hO : H24K.SAT.OB1 x)
    {beta gamma : ℝ} (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (hcell : CellAt F U_A2 D_A2 (uT2 x beta gamma))
    (hlet : P0Letter ⟪x 1, uT2 x beta gamma⟫ ⟪x 3, uT2 x beta gamma⟫ ⟪x 5, uT2 x beta gamma⟫
      ⟪x 6, uT2 x beta gamma⟫) :
    Gen.LexAny F :=
  WC.lexAny_of_cellAt_robUni (by norm_num) F cA2_inj cA2_cyc hcell
    (cA2_robUni_of_p0 F hO hbeta hgamma hlet)

/-- **P0Edge025:** `OB1 x` and some `p` such that at the `025` edge view `r = x₅ - x₂ + p (x₀ - x₂)` the `cA2`
facets `U_A2 = {016, 0345, 046, 346}` are strictly positive, `{126, 235, 236}` strictly negative (`012` is automatic,
`025` vanishes), and `z₆ < z₃ < z₅`. -/
def P0Edge025 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  H24K.SAT.OB1 x ∧ ∃ p : ℝ,
    (∀ s ∈ U_A2, 0 < ⟪F.N s, x 5 - x 2 + p • (x 0 - x 2)⟫) ∧
    (∀ s ∈ ({5, 6, 7} : Finset (Fin 9)), ⟪F.N s, x 5 - x 2 + p • (x 0 - x 2)⟫ < 0) ∧
    ⟪x 3, x 5 - x 2 + p • (x 0 - x 2)⟫ < ⟪x 5, x 5 - x 2 + p • (x 0 - x 2)⟫ ∧
    ⟪x 6, x 5 - x 2 + p • (x 0 - x 2)⟫ < ⟪x 3, x 5 - x 2 + p • (x 0 - x 2)⟫

/-- **P0 edge view:** on `P0Edge025 x F` there are `β, γ > 0` with `uT2 x β γ` an open `cA2` view satisfying
`z₆ < z₃ < z₅` (the view `r + t • uT2 x 2 1`, `t > 0` small, rescaled). -/
theorem cA2_exists_of_p0Edge025 {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x} (hZ : P0Edge025 x F) :
    ∃ beta gamma : ℝ, 0 < beta ∧ 0 < gamma ∧ CellAt F U_A2 D_A2 (uT2 x beta gamma) ∧
      ⟪x 6, uT2 x beta gamma⟫ < ⟪x 3, uT2 x beta gamma⟫ ∧
      ⟪x 3, uT2 x beta gamma⟫ < ⟪x 5, uT2 x beta gamma⟫ := by
  obtain ⟨-, p, hU, hD, h35, h63⟩ := hZ
  have T := type24OfFac F
  set r := x 5 - x 2 + p • (x 0 - x 2) with hr_def
  set dl := uT2 x 2 1 with hdl
  set a := oblX0 x 5 + p with ha_def
  set b := oblX2 x 5 - 1 - p with hb_def
  set c := oblX6 x 5 with hc_def
  have hc : 0 < c := T.X6_pos (v := 5) (by decide)
  have hr : r = a • (x 0 - x 1) + b • (x 2 - x 1) + c • (x 6 - x 1) := by
    have h1' : x 5 - x 1 = oblX0 x 5 • (x 0 - x 1) + oblX2 x 5 • (x 2 - x 1) + oblX6 x 5 • (x 6 - x 1) := by
      conv_lhs => rw [T.rep 5]
      abel
    rw [hr_def, show x 5 - x 2 = (x 5 - x 1) - (x 2 - x 1) by abel,
      show x 0 - x 2 = (x 0 - x 1) - (x 2 - x 1) by abel, h1', ha_def, hb_def, hc_def]
    module
  have hNr : ∀ s : Fin 9, ⟪F.N s, r⟫ = a * (F.f s (x 0) - F.f s (x 1)) + b * (F.f s (x 2) - F.f s (x 1)) +
      c * (F.f s (x 6) - F.f s (x 1)) := by
    intro s
    rw [hr, inner_add_right, inner_add_right, real_inner_smul_right, real_inner_smul_right,
      real_inner_smul_right, F.inner_sub, F.inner_sub, F.inner_sub]
  -- `a > 0` from facet `126`, `b < 0` from facet `016`
  have ha : 0 < a := by
    have h5 := hD 5 (by decide)
    rw [hNr, F.zero 5 1 (by decide), F.zero 5 2 (by decide), F.zero 5 6 (by decide)] at h5
    have hf := F.neg 5 0 (by decide)
    nlinarith
  have hb : b < 0 := by
    have h1 := hU 1 (by decide)
    rw [hNr, F.zero 1 0 (by decide), F.zero 1 1 (by decide), F.zero 1 6 (by decide)] at h1
    have hf := F.neg 1 2 (by decide)
    nlinarith
  -- facets `012` (automatic) and `025` (zero, push negative)
  have h0r : ⟪F.N 0, r⟫ < 0 := by
    rw [hNr, F.zero 0 0 (by decide), F.zero 0 1 (by decide), F.zero 0 2 (by decide)]
    have hf := F.neg 0 6 (by decide)
    nlinarith
  have h2r : ⟪F.N 2, r⟫ = 0 := by
    rw [hr_def, inner_add_right, real_inner_smul_right, F.inner_sub, F.inner_sub,
      F.zero 2 0 (by decide), F.zero 2 2 (by decide), F.zero 2 5 (by decide)]
    ring
  have h2d : ⟪F.N 2, dl⟫ < 0 := by
    rw [hdl, uT2, inner_cap, F.zero 2 0 (by decide), F.zero 2 2 (by decide)]
    have hf := F.neg 2 6 (by decide)
    linarith
  have hD' : ∀ s ∈ D_A2, ⟪F.N s, r⟫ < 0 ∨ (⟪F.N s, r⟫ = 0 ∧ ⟪F.N s, dl⟫ < 0) := by
    intro s hs
    simp only [D_A2, Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl
    · exact Or.inl h0r
    · exact Or.inr ⟨h2r, h2d⟩
    · exact Or.inl (hD 5 (by decide))
    · exact Or.inl (hD 6 (by decide))
    · exact Or.inl (hD 7 (by decide))
  have hfU : ∀ᶠ t : ℝ in 𝓝[>] 0, ∀ s ∈ U_A2, 0 < ⟪F.N s, r⟫ + ⟪F.N s, dl⟫ * t :=
    (Filter.eventually_all_finset _).2 fun s hs => Minimality.T24.Belt.ev_pos _ _ (hU s hs)
  have hfD : ∀ᶠ t : ℝ in 𝓝[>] 0, ∀ s ∈ D_A2, ⟪F.N s, r⟫ + ⟪F.N s, dl⟫ * t < 0 := by
    refine (Filter.eventually_all_finset _).2 fun s hs => ?_
    rcases hD' s hs with h | ⟨h0, h1⟩
    · exact Minimality.T24.Belt.ev_neg _ _ h
    · filter_upwards [Minimality.T24.Belt.ev_gt0] with t ht
      rw [h0]; nlinarith
  have hl1 : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < (⟪x 3, r⟫ - ⟪x 6, r⟫) + (⟪x 3, dl⟫ - ⟪x 6, dl⟫) * t :=
    Minimality.T24.Belt.ev_pos _ _ (by linarith)
  have hl2 : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < (⟪x 5, r⟫ - ⟪x 3, r⟫) + (⟪x 5, dl⟫ - ⟪x 3, dl⟫) * t :=
    Minimality.T24.Belt.ev_pos _ _ (by linarith)
  obtain ⟨t, hu, hd, l1, l2, ht⟩ :=
    (hfU.and (hfD.and (hl1.and (hl2.and Minimality.T24.Belt.ev_gt0)))).exists
  have hat : 0 < a + t := by linarith
  have hbeta : 0 < (2 * t - b) / (a + t) := div_pos (by linarith) hat
  have hgamma : 0 < (c + t) / (a + t) := div_pos (by linarith) hat
  have hview : uT2 x ((2 * t - b) / (a + t)) ((c + t) / (a + t)) = (a + t)⁻¹ • (r + t • dl) := by
    have e1 : (a + t)⁻¹ * (b - 2 * t) = -((2 * t - b) / (a + t)) := by field_simp; ring
    have e2 : (a + t)⁻¹ * (c + t) = (c + t) / (a + t) := by rw [div_eq_inv_mul]
    have e0 : (a + t)⁻¹ * (a + t) = 1 := inv_mul_cancel₀ hat.ne'
    have : r + t • dl = (a + t) • (x 0 - x 1) + (b - 2 * t) • (x 2 - x 1) + (c + t) • (x 6 - x 1) := by
      rw [hr, hdl, uT2, capView]; module
    rw [this, uT2, capView, smul_add, smul_add, smul_smul, smul_smul, smul_smul, e0, e1, e2, one_smul]
  have hia : 0 < (a + t)⁻¹ := inv_pos.mpr hat
  have hz : ∀ v : ℝ³, ⟪v, uT2 x ((2 * t - b) / (a + t)) ((c + t) / (a + t))⟫ =
      (a + t)⁻¹ * (⟪v, r⟫ + ⟪v, dl⟫ * t) := by
    intro v
    rw [hview, real_inner_smul_right, inner_add_right, real_inner_smul_right, mul_comm t]
  refine ⟨_, _, hbeta, hgamma, ⟨fun s hs => ?_, fun s hs => ?_⟩, ?_, ?_⟩
  · rw [hz]; exact mul_pos hia (hu s hs)
  · rw [hz]; exact mul_neg_of_pos_of_neg hia (hd s hs)
  · rw [hz, hz]; apply mul_lt_mul_of_pos_left _ hia; linarith
  · rw [hz, hz]; apply mul_lt_mul_of_pos_left _ hia; linarith

/-- **Lemma P0 + edge 025:** `P0Edge025 x F` implies `Gen.LexAny F`. -/
theorem lexAny_of_p0Edge025 {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x} (hZ : P0Edge025 x F) :
    Gen.LexAny F := by
  obtain ⟨beta, gamma, hb, hg, hcell, h63, h35⟩ := cA2_exists_of_p0Edge025 hZ
  exact cA2_lexAny_of_p0 F hZ.1 hb hg hcell (Or.inl ⟨h63, h35⟩)

/-- **P0Edge025 (`π_24` mirror):** `P0Edge025 (x ∘ Sym.pi24) (Sym.sym24 F)` implies `Gen.LexAny F`. -/
theorem lexAny_of_p0Edge025_twin {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x}
    (hZ : P0Edge025 (x ∘ Sym.pi24) (Sym.sym24 F)) : Gen.LexAny F :=
  Sym.lexAny_sym F (lexAny_of_p0Edge025 hZ)

/-- **P0Edge025 hole fact:** `HoleLeaf x F` excludes `P0Edge025 x F`. -/
theorem holeLeaf_not_p0Edge025 {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F)
    (hZ : P0Edge025 x F) : False :=
  hF.2.2.2.1 (lexAny_of_p0Edge025 hZ)

/-- **P0Edge025 twin hole fact:** `HoleLeaf x F` excludes `P0Edge025 (x ∘ Sym.pi24) (Sym.sym24 F)`. -/
theorem holeLeaf_not_p0Edge025_twin {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F)
    (hZ : P0Edge025 (x ∘ Sym.pi24) (Sym.sym24 F)) : False :=
  hF.2.2.2.1 (lexAny_of_p0Edge025_twin hZ)

end Minimality.T24.TwoCone
