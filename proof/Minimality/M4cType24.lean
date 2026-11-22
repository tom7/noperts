module

public import Minimality.M4Sym24
public import Minimality.M4bType24
public import Minimality.M4Type24

/-!
# Type 24 — Refereed A8 Lemmas (Task CD)

Formalizes the referee-verified lemmas from `A8-REFEREE.md`:
- `splitAny24_of_lex3'` (lex-row version of `splitAny24_of_lex3`);
- `w26_bound` (`W26`, `F126xF236`) and its `Sym24` twin `w26'_bound`;
- `w26_diag_band` (`V31 + W26`) and its `Sym24` twin `w26'_diag_band`;
- `lexAny_or_split_E05P5U` and `isRupert_of_E05P5U` (generalizing `splitAny24_E05P5`);
- `e05q4_bound` (`E05-Q4` U-bound);
- `splitAny24_E0416` and `isRupert_of_E0416` (`E04-16`, tie-free and `a4 = 1`).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace
open Finset Filter
open scoped Topology

namespace Minimality.T24.A8

open Minimality Minimality.H21 Minimality.H24.SAT Minimality.T24.SAT Minimality.T24.RCell
  Minimality.LexCell Minimality.Split Minimality.T24.M4 Minimality.T24.A7 Minimality.T24.Sym

/-! ### Part 0: Lex-row `splitAny24_of_lex3'` -/

private theorem det3_add_smul_smul (u v b d1 d2 : ℝ³) (ε : ℝ) :
    det3 u v (b + ε • d1 + ε ^ 2 • d2) =
      det3 u v b + ε * det3 u v d1 + ε ^ 2 * det3 u v d2 := by
  simp only [det3_expand, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  ring

theorem splitAny24_of_lex3' {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    {k : ℕ} [NeZero k] (hk : 3 ≤ k) (c : ZMod k → Fin 7) (hc : Function.Injective c)
    (pat : Fin 9 → Bool) (hcyc : S0xCycOK s0x_S24 c pat)
    (b d1 d2 : ℝ³)
    (hfac : ∀ t : Fin 9,
      LexPos3 (if pat t then ⟪F.N t, b⟫ else -⟪F.N t, b⟫)
              (if pat t then ⟪F.N t, d1⟫ else -⟪F.N t, d1⟫)
              (if pat t then ⟪F.N t, d2⟫ else -⟪F.N t, d2⟫))
    (a cc : ZMod k) (hca : cc ≠ a) (hca1 : cc ≠ a + 1) (σ : ℝ)
    (hrows : ∀ i : ZMod k, i ≠ a → ∀ j : ZMod k, (j = i ∨ j = i + 1) → j ≠ cc →
      ∃ s : ℝ,
        LexPos3 (s * ⟪x (c j) - x (c cc), b⟫) (s * ⟪x (c j) - x (c cc), d1⟫)
                (s * ⟪x (c j) - x (c cc), d2⟫) ∧
        LexPos3 (σ * s * det3 (x (c (i + 1)) - x (c i)) (x (c (a + 1)) - x (c a)) b)
                (σ * s * det3 (x (c (i + 1)) - x (c i)) (x (c (a + 1)) - x (c a)) d1)
                (σ * s * det3 (x (c (i + 1)) - x (c i)) (x (c (a + 1)) - x (c a)) d2)) :
    SplitAny24 F := by
  have hev_fac : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ∀ t : Fin 9, 0 < (if pat t then ⟪F.N t, b + ε • d1 + ε ^ 2 • d2⟫ else
        -⟪F.N t, b + ε • d1 + ε ^ 2 • d2⟫) := by
    rw [eventually_all]
    intro t
    filter_upwards [ev_lexPos3 (hfac t)] with ε hε
    by_cases ht : pat t <;> simp only [ht, ↓reduceIte, Bool.false_eq_true] at hε ⊢ <;>
      simp only [inner_add_right, inner_smul_right] <;> linarith
  have hev_rows : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ∀ i j : ZMod k, i ≠ a → (j = i ∨ j = i + 1) → j ≠ cc →
        0 < σ * (⟪x (c j) - x (c cc), b + ε • d1 + ε ^ 2 • d2⟫ *
          det3 (x (c (i + 1)) - x (c i)) (x (c (a + 1)) - x (c a))
            (b + ε • d1 + ε ^ 2 • d2)) := by
    rw [eventually_all]; intro i
    rw [eventually_all]; intro j
    by_cases hia : i ≠ a
    · by_cases hj : j = i ∨ j = i + 1
      · by_cases hjc : j ≠ cc
        · obtain ⟨s, hlex, hdet⟩ := hrows i hia j hj hjc
          have hs_ne : s ≠ 0 := by
            rintro rfl
            simp only [zero_mul] at hlex
            rcases hlex with h | ⟨_, h | ⟨_, h⟩⟩ <;> linarith
          have h1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
              0 < s * ⟪x (c j) - x (c cc), b + ε • d1 + ε ^ 2 • d2⟫ := by
            filter_upwards [ev_lexPos3 hlex] with ε hε
            simp only [inner_add_right, inner_smul_right]
            linarith
          have h2 : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
              0 < σ * s * det3 (x (c (i + 1)) - x (c i)) (x (c (a + 1)) - x (c a))
                (b + ε • d1 + ε ^ 2 • d2) := by
            have hdet' : ∀ ε : ℝ,
                σ * s * det3 (x (c (i + 1)) - x (c i)) (x (c (a + 1)) - x (c a))
                  (b + ε • d1 + ε ^ 2 • d2) =
                (σ * s * det3 (x (c (i + 1)) - x (c i)) (x (c (a + 1)) - x (c a)) b) +
                ε * (σ * s * det3 (x (c (i + 1)) - x (c i)) (x (c (a + 1)) - x (c a)) d1) +
                ε ^ 2 * (σ * s * det3 (x (c (i + 1)) - x (c i)) (x (c (a + 1)) - x (c a)) d2) := by
              intro ε; rw [det3_add_smul_smul]; ring
            filter_upwards [ev_lexPos3 hdet] with ε hε
            rw [hdet']; exact hε
          filter_upwards [h1, h2] with ε hε1 hε2 _ _ _
          have hprod : 0 < (s * ⟪x (c j) - x (c cc), b + ε • d1 + ε ^ 2 • d2⟫) *
              (σ * s * det3 (x (c (i + 1)) - x (c i)) (x (c (a + 1)) - x (c a))
                (b + ε • d1 + ε ^ 2 • d2)) := mul_pos hε1 hε2
          have hs2 : 0 < s * s := mul_self_pos.mpr hs_ne
          nlinarith
        · exact Eventually.of_forall fun _ _ _ h => absurd h hjc
      · exact Eventually.of_forall fun _ _ h => absurd h hj
    · exact Eventually.of_forall fun _ h => absurd h hia
  obtain ⟨ε, ⟨hfac_ε, hrows_ε⟩, _⟩ := ((hev_fac.and hev_rows).and self_mem_nhdsWithin).exists
  have hdet_eq : ∀ u v w : ℝ³, Minimality.Split.det3 u v w = Minimality.det3 u v w := by
    intro u v w
    simp [Minimality.Split.det3, Minimality.det3_expand]
  refine ⟨k, inferInstance, c, pat, b + ε • d1 + ε ^ 2 • d2, 0, a, cc, σ, hk, hc, hcyc, ?_,
    hca, hca1, fun i j hia hj hjc => by
      simpa only [hdet_eq] using hrows_ε i j hia hj hjc⟩
  intro t
  have ht := hfac_ε t
  constructor
  · intro hpt; simp only [hpt, ↓reduceIte] at ht; exact Or.inl ht
  · intro hpt; simp only [hpt, Bool.false_eq_true, ↓reduceIte] at ht; exact Or.inl ht

/-! ### Part 1: `w26_bound`, `w26'_bound`, `w26_diag_band`, `w26'_diag_band` -/

theorem robUniLex_five_w26 (z : ZMod 5 → ℝ × ℝ × ℝ)
    (h10 : (z 1).1 < (z 0).1) (h04 : (z 0).1 < (z 4).1)
    (hdiag : ¬ (max (z 1).1 (z 3).1 ≤ min (z 4).1 (z 2).1)) :
    RobUniLex z := by
  intro B b c d hb hbc hcd hd
  have hB : B = 0 ∨ B = 1 ∨ B = 2 ∨ B = 3 ∨ B = 4 := by revert B; decide
  have hbcd : (b = 1 ∧ c = 2 ∧ d = 3) ∨ (b = 1 ∧ c = 2 ∧ d = 4) ∨
      (b = 1 ∧ c = 3 ∧ d = 4) ∨ (b = 2 ∧ c = 3 ∧ d = 4) := by omega
  have hcases : (z 2).1 < (z 1).1 ∨ (z 4).1 < (z 3).1 ∨ (z 2).1 < (z 3).1 := by
    by_cases h12 : (z 1).1 ≤ (z 2).1
    · by_cases h34 : (z 3).1 ≤ (z 4).1
      · by_cases h23 : (z 3).1 ≤ (z 2).1
        · exfalso; apply hdiag
          exact max_le (le_min (by linarith) h12) (le_min h34 h23)
        · exact Or.inr (Or.inr (not_le.mp h23))
      · exact Or.inr (Or.inl (not_le.mp h34))
    · exact Or.inl (not_le.mp h12)
  rcases hcases with h21 | h43 | h23
  all_goals rcases hB with rfl | rfl | rfl | rfl | rfl <;>
    rcases hbcd with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
    simp only [Nat.cast_one, Nat.cast_ofNat,
      show (0 : ZMod 5) + 1 = 1 from rfl, show (0 : ZMod 5) + 2 = 2 from rfl,
      show (0 : ZMod 5) + 3 = 3 from rfl, show (0 : ZMod 5) + 4 = 4 from rfl,
      show (1 : ZMod 5) + 1 = 2 from rfl, show (1 : ZMod 5) + 2 = 3 from rfl,
      show (1 : ZMod 5) + 3 = 4 from rfl, show (1 : ZMod 5) + 4 = 0 from rfl,
      show (2 : ZMod 5) + 1 = 3 from rfl, show (2 : ZMod 5) + 2 = 4 from rfl,
      show (2 : ZMod 5) + 3 = 0 from rfl, show (2 : ZMod 5) + 4 = 1 from rfl,
      show (3 : ZMod 5) + 1 = 4 from rfl, show (3 : ZMod 5) + 2 = 0 from rfl,
      show (3 : ZMod 5) + 3 = 1 from rfl, show (3 : ZMod 5) + 4 = 2 from rfl,
      show (4 : ZMod 5) + 1 = 0 from rfl, show (4 : ZMod 5) + 2 = 1 from rfl,
      show (4 : ZMod 5) + 3 = 2 from rfl, show (4 : ZMod 5) + 4 = 3 from rfl]
  all_goals first
    | exact Or.inl (Or.inl (by linarith))
    | exact Or.inr (Or.inl (Or.inl (by linarith)))
    | exact Or.inr (Or.inr (Or.inl (Or.inl (by linarith))))
    | exact Or.inr (Or.inr (Or.inr (Or.inl (by linarith))))

theorem w26_bound {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x)
    (hbc : ⟪x 2 - x 1, x 6 - x 1⟫ ≤ 0) (hn : F.f 3 (x 2) < F.f 3 (x 6))
    (hU : ¬ LexAny F) :
    ⟪x 0 - x 1, x 2 - x 6⟫ ≤ 0 := by
  by_contra hcon
  push Not at hcon
  have T := type24OfFac F
  have hom3 : 0 < omega3 x := hC.1
  have hom5 : 0 < omega5 x := hC.2.2.1
  have ha3 : 0 < oblX0 x 3 := T.X0_pos (v := 3) (by decide)
  have ha5 : 0 < oblX0 x 5 := T.X0_pos (v := 5) (by decide)
  have hc5 : 0 < oblX6 x 5 := T.X6_pos (v := 5) (by decide)
  let b : ℝ³ := x 2 - x 6
  let d1 : ℝ³ := x 1 - x 0
  have hb_ne : b ≠ 0 := sub_ne_zero.mpr fun h => absurd (T.inj h) (by decide)
  have h61 : x 6 - x 1 ≠ 0 := sub_ne_zero.mpr fun h => absurd (T.inj h) (by decide)
  have hz61 : ⟪x 6 - x 1, b⟫ < 0 := by
    dsimp [b]
    rw [show x 2 - x 6 = (x 2 - x 1) - (x 6 - x 1) by abel, inner_sub_right]
    have hbc' : ⟪x 6 - x 1, x 2 - x 1⟫ ≤ 0 := by rw [real_inner_comm]; exact hbc
    linarith [real_inner_self_pos.mpr h61]
  -- Facings at `(b, d1, 0)` on `U = {0, 2, 5, 6, 7}`, `Dn = {1, 3, 4, 8}`:
  have hf0 : 0 < ⟪F.N 0, b⟫ := by
    dsimp [b]; rw [← F.hN 0 (x 2) (x 6), F.zero 0 2 (by decide), zero_sub]
    linarith [F.neg 0 6 (by decide)]
  have hf1 : ⟪F.N 1, b⟫ < 0 := by
    dsimp [b]; rw [← F.hN 1 (x 2) (x 6), F.zero 1 6 (by decide), sub_zero]
    exact F.neg 1 2 (by decide)
  have hf2 : 0 < ⟪F.N 2, b⟫ := by
    dsimp [b]; rw [← F.hN 2 (x 2) (x 6), F.zero 2 2 (by decide), zero_sub]
    linarith [F.neg 2 6 (by decide)]
  have hf3 : ⟪F.N 3, b⟫ < 0 := by
    dsimp [b]; rw [← F.hN 3 (x 2) (x 6)]; linarith
  have hf4 : ⟪F.N 4, b⟫ < 0 := by
    dsimp [b]; rw [← F.hN 4 (x 2) (x 6), F.zero 4 6 (by decide), sub_zero]
    exact F.neg 4 2 (by decide)
  have hf5 : ⟪F.N 5, b⟫ = 0 := by
    dsimp [b]; rw [← F.hN 5 (x 2) (x 6), F.zero 5 2 (by decide), F.zero 5 6 (by decide), sub_self]
  have hd5 : 0 < ⟪F.N 5, d1⟫ := by
    dsimp [d1]; rw [← F.hN 5 (x 1) (x 0), F.zero 5 1 (by decide), zero_sub]
    linarith [F.neg 5 0 (by decide)]
  have hf6 : 0 < ⟪F.N 6, b⟫ := by
    dsimp [b]; rw [← F.hN 6 (x 2) (x 6), F.zero 6 2 (by decide), zero_sub]
    linarith [F.neg 6 6 (by decide)]
  have hf7 : ⟪F.N 7, b⟫ = 0 := by
    dsimp [b]; rw [← F.hN 7 (x 2) (x 6), F.zero 7 2 (by decide), F.zero 7 6 (by decide), sub_self]
  have hd7 : 0 < ⟪F.N 7, d1⟫ := by
    dsimp [d1]; rw [← F.hN 7 (x 1) (x 0)]
    have ev7 := fac_eval F 7 3
    rw [F.zero 7 3 (by decide), F.zero 7 2 (by decide), F.zero 7 6 (by decide)] at ev7
    have e3 := eq3 F
    have hprod : oblX0 x 3 * (F.f 7 (x 1) - F.f 7 (x 0) - (-omega3 x * F.f 7 (x 1))) = 0 := by
      linear_combination ev7 - F.f 7 (x 1) * e3
    have heq : F.f 7 (x 1) - F.f 7 (x 0) = -omega3 x * F.f 7 (x 1) :=
      sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_left ha3.ne')
    rw [heq]
    have : -omega3 x * F.f 7 (x 1) = omega3 x * (-F.f 7 (x 1)) := by ring
    rw [this]; exact mul_pos hom3 (neg_pos.mpr (F.neg 7 1 (by decide)))
  have hf8 : ⟪F.N 8, b⟫ < 0 := by
    dsimp [b]; rw [← F.hN 8 (x 2) (x 6), F.zero 8 6 (by decide), sub_zero]
    exact F.neg 8 2 (by decide)
  -- Front diagonal `[x 5, x 6]` in front of `[x 0, x 3]` along `b = x 2 - x 6`:
  have hfront : FrontDiag (x 5) (x 6) (x 0) (x 3) b := by
    have h75 : F.f 7 (x 5) < 0 := F.neg 7 5 (by decide)
    have hf7_0 : F.f 7 (x 0) = (1 + omega3 x) * F.f 7 (x 1) := by
      have ev7 := fac_eval F 7 3
      rw [F.zero 7 3 (by decide), F.zero 7 2 (by decide), F.zero 7 6 (by decide)] at ev7
      have e3 := eq3 F
      have hprod : oblX0 x 3 * (F.f 7 (x 0) - (1 + omega3 x) * F.f 7 (x 1)) = 0 := by
        linear_combination -ev7 + F.f 7 (x 1) * e3
      exact sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_left ha3.ne')
    have h75_ineq : (1 + omega5 x) * oblX6 x 5 < oblX0 x 5 * (1 + omega3 x) := by
      have ev75 := fac_eval F 7 5
      rw [F.zero 7 2 (by decide), F.zero 7 6 (by decide), hf7_0] at ev75
      have e5 := eq5 F
      have h71 : 0 < -F.f 7 (x 1) := by linarith [F.neg 7 1 (by decide)]
      have hprod : (-F.f 7 (x 1)) * ((1 + omega5 x) * oblX6 x 5 - oblX0 x 5 * (1 + omega3 x)) =
          F.f 7 (x 5) := by
        rw [ev75]; linear_combination F.f 7 (x 1) * e5
      nlinarith
    set num_l : ℝ := (1 + omega5 x) * oblX6 x 5
    set num_1l : ℝ := oblX0 x 3 * (oblX0 x 5 * (1 + omega3 x) - (1 + omega5 x) * oblX6 x 5)
    set den : ℝ := num_l + num_1l
    have hnl : 0 < num_l := mul_pos (by linarith) hc5
    have hn1l : 0 < num_1l := mul_pos ha3 (sub_pos.mpr h75_ineq)
    have hden : 0 < den := by linarith
    set l : ℝ := num_l / den
    have hl0 : 0 < l := div_pos hnl hden
    have hl1 : l < 1 := by rw [div_lt_one hden]; dsimp [den]; linarith
    set m : ℝ := 1 - (1 - l + l * oblX0 x 3) / oblX0 x 5
    set s : ℝ := l * oblX2 x 3 - (1 - m) * oblX2 x 5
    have h_ea : (1 - l) + l * oblX0 x 3 - (1 - m) * oblX0 x 5 = 0 := by
      dsimp [m]; field_simp [ha5.ne']; ring
    have h_eb : l * oblX2 x 3 - (1 - m) * oblX2 x 5 - s = 0 := by
      dsimp [s]; ring
    have h_ec : l * oblX6 x 3 - (1 - m) * oblX6 x 5 - m + s = 0 := by
      have hb3c3 : oblX2 x 3 + oblX6 x 3 = 1 + omega3 x * oblX0 x 3 := by linarith [eq3 F]
      have hb5c5 : oblX2 x 5 + oblX6 x 5 - 1 = (1 + omega5 x) * oblX6 x 5 - oblX0 x 5 := by
        linarith [eq5 F]
      have h_sum : l * (oblX2 x 3 + oblX6 x 3) - (1 - m) * (oblX2 x 5 + oblX6 x 5 - 1) - 1 =
          l * oblX6 x 3 - (1 - m) * oblX6 x 5 - m + s := by
        dsimp [s]; ring
      rw [← h_sum, hb3c3, hb5c5]
      dsimp [m, l]
      field_simp [hden.ne', ha5.ne']
      dsimp [den, num_l, num_1l]
      ring
    have hvec : (1 - l) • (x 0 - x 1) + l • (x 3 - x 1) =
        (1 - m) • (x 5 - x 1) + m • (x 6 - x 1) + s • (x 2 - x 6) := by
      have hrep3 : x 3 - x 1 = oblX0 x 3 • (x 0 - x 1) + oblX2 x 3 • (x 2 - x 1) +
          oblX6 x 3 • (x 6 - x 1) := by rw [T.rep 3]; abel
      have hrep5 : x 5 - x 1 = oblX0 x 5 • (x 0 - x 1) + oblX2 x 5 • (x 2 - x 1) +
          oblX6 x 5 • (x 6 - x 1) := by rw [T.rep 5]; abel
      have h26' : x 2 - x 6 = (x 2 - x 1) - (x 6 - x 1) := by abel
      rw [hrep3, hrep5, h26']
      calc (1 - l) • (x 0 - x 1) + l • (oblX0 x 3 • (x 0 - x 1) + oblX2 x 3 • (x 2 - x 1) +
            oblX6 x 3 • (x 6 - x 1))
          = ((1 - l) + l * oblX0 x 3) • (x 0 - x 1) + (l * oblX2 x 3) • (x 2 - x 1) +
            (l * oblX6 x 3) • (x 6 - x 1) := by
              simp only [smul_add, smul_smul, add_smul]; abel
        _ = ((1 - m) * oblX0 x 5) • (x 0 - x 1) + ((1 - m) * oblX2 x 5 + s) • (x 2 - x 1) +
            ((1 - m) * oblX6 x 5 + m - s) • (x 6 - x 1) := by
              rw [show (1 - l) + l * oblX0 x 3 = (1 - m) * oblX0 x 5 by linarith [h_ea],
                show l * oblX2 x 3 = (1 - m) * oblX2 x 5 + s by linarith [h_eb],
                show l * oblX6 x 3 = (1 - m) * oblX6 x 5 + m - s by linarith [h_ec]]
        _ = (1 - m) • (oblX0 x 5 • (x 0 - x 1) + oblX2 x 5 • (x 2 - x 1) +
              oblX6 x 5 • (x 6 - x 1)) + m • (x 6 - x 1) + s • ((x 2 - x 1) - (x 6 - x 1)) := by
              simp only [smul_add, smul_sub, smul_smul, add_smul, sub_smul]; abel
    have hf3_eq : 0 = m * F.f 3 (x 6) + s * (F.f 3 (x 2) - F.f 3 (x 6)) := by
      have hi := congrArg (fun v => ⟪F.N 3, v⟫) hvec
      simp only [inner_add_right, inner_smul_right, ← F.hN 3 _ (x 1), ← F.hN 3 (x 2) (x 6),
        F.zero 3 0 (by decide), F.zero 3 3 (by decide), F.zero 3 5 (by decide)] at hi
      linarith
    have hm_pos : 0 < m := by
      have h23 : F.f 2 (x 3) < 0 := F.neg 2 3 (by decide)
      have h26 : F.f 2 (x 6) < 0 := F.neg 2 6 (by decide)
      have h32 : F.f 3 (x 2) < 0 := F.neg 3 2 (by decide)
      have hf2_eq : l * F.f 2 (x 3) = (m - s) * F.f 2 (x 6) := by
        have hi := congrArg (fun v => ⟪F.N 2, v⟫) hvec
        simp only [inner_add_right, inner_smul_right, ← F.hN 2 _ (x 1), ← F.hN 2 (x 2) (x 6),
          F.zero 2 0 (by decide), F.zero 2 5 (by decide), F.zero 2 2 (by decide)] at hi
        linarith
      have hms_pos : 0 < m - s := by
        have hlt : l * F.f 2 (x 3) < 0 := mul_neg_of_pos_of_neg hl0 h23
        rw [hf2_eq] at hlt
        by_contra h; push Not at h
        have : 0 ≤ (m - s) * F.f 2 (x 6) := mul_nonneg_of_nonpos_of_nonpos h h26.le
        linarith
      have hm_rel : (m - s) * (F.f 3 (x 2) - F.f 3 (x 6)) = m * F.f 3 (x 2) := by linarith
      have hm_neg_prod : m * F.f 3 (x 2) < 0 := by
        rw [← hm_rel]
        exact mul_neg_of_pos_of_neg hms_pos (sub_neg.mpr hn)
      by_contra h; push Not at h
      have : 0 ≤ m * F.f 3 (x 2) := mul_nonneg_of_nonpos_of_nonpos h h32.le
      linarith
    have hm1 : m < 1 := by
      dsimp [m]
      have : 0 < (1 - l + l * oblX0 x 3) / oblX0 x 5 := div_pos (by nlinarith) ha5
      linarith
    have hs_neg : s < 0 := by
      have h36 : F.f 3 (x 6) < 0 := F.neg 3 6 (by decide)
      have hpos : 0 < s * (F.f 3 (x 2) - F.f 3 (x 6)) := by
        have : m * F.f 3 (x 6) < 0 := mul_neg_of_pos_of_neg hm_pos h36
        linarith
      by_contra h; push Not at h
      have : s * (F.f 3 (x 2) - F.f 3 (x 6)) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos h (sub_nonpos.mpr hn.le)
      linarith
    refine ⟨m, l, -s, hm_pos.le, hm1.le, hl0.le, hl1.le, neg_pos.mpr hs_neg, ?_⟩
    have hshift5 : x 5 + m • (x 6 - x 5) - (x 0 + l • (x 3 - x 0)) =
        ((1 - m) • (x 5 - x 1) + m • (x 6 - x 1)) - ((1 - l) • (x 0 - x 1) + l • (x 3 - x 1)) := by
      simp only [sub_smul, one_smul, smul_sub]; abel
    rw [hshift5, hvec]
    simp only [neg_smul]; abel
  have hnb := FrontDiag.not_back hfront hb_ne
  have hshift : ∀ v : Fin 7, ⟪x v, b⟫ = ⟪x v - x 1, b⟫ + ⟪x 1, b⟫ := by
    intro v; rw [inner_sub_left]; ring
  apply hU
  refine ⟨5, inferInstance, (![1, 6, 3, 5, 0] : ZMod 5 → Fin 7), {0, 2, 5, 6, 7}, {1, 3, 4, 8},
    b, d1, 0, by decide,
    (by intro i j h; fin_cases i <;> fin_cases j <;> first | rfl | exact absurd h (by decide)),
    (by unfold S0xCycUD; decide), ?_, ?_, ?_⟩
  · intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · exact Or.inl hf0
    · exact Or.inl hf2
    · exact Or.inr ⟨hf5, Or.inl hd5⟩
    · exact Or.inl hf6
    · exact Or.inr ⟨hf7, Or.inl hd7⟩
  · intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · exact Or.inl (by linarith)
    · exact Or.inl (by linarith)
    · exact Or.inl (by linarith)
    · exact Or.inl (by linarith)
  · refine robUniLex_five_w26 _ ?_ ?_ ?_
    · dsimp only [Matrix.cons_val]; rw [hshift 6, hshift 1]; simp only [sub_self, inner_zero_left]; linarith
    · dsimp only [Matrix.cons_val]; rw [hshift 1, hshift 0]; simp only [sub_self, inner_zero_left]; linarith
    · dsimp only [Matrix.cons_val]
      intro hle; apply hnb
      simp only [max_le_iff, le_min_iff] at hle ⊢
      exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

theorem w26'_bound {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x)
    (hbc : ⟪x 2 - x 1, x 6 - x 1⟫ ≤ 0) (hn : F.f 3 (x 6) < F.f 3 (x 2))
    (hU : ¬ LexAny F) :
    ⟪x 0 - x 1, x 6 - x 2⟫ ≤ 0 := by
  have hw := w26_bound (sym24 F) ((cbarIn_comp_pi24 x).2 hC)
    (by simpa [Function.comp_apply, real_inner_comm] using hbc)
    (by simpa [sym24_f_apply] using hn)
    (fun h => hU (lexAny_sym F h))
  simpa [Function.comp_apply] using hw

theorem w26_diag_band {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x)
    (_hab : ⟪x 0 - x 1, x 2 - x 1⟫ ≤ 0) (hac : ⟪x 0 - x 1, x 6 - x 1⟫ ≤ 0)
    (hbc : ⟪x 2 - x 1, x 6 - x 1⟫ ≤ 0)
    (hnc : F.f 3 (x 1) < F.f 3 (x 6)) (hnb : F.f 3 (x 2) < F.f 3 (x 1))
    (hb : oblX2 x 4 < oblX2 x 3) (hU : ¬ LexAny F) :
    0 ≤ -⟪x 0 - x 1, x 6 - x 1⟫ ∧
    -⟪x 0 - x 1, x 6 - x 1⟫ ≤ -⟪x 0 - x 1, x 2 - x 1⟫ ∧
    nC x * (-⟪x 0 - x 1, x 2 - x 1⟫) ≤ D45 x * (-⟪x 2 - x 1, x 6 - x 1⟫) := by
  have hw := w26_bound F hC hbc (lt_trans hnb hnc) hU
  have hv := v31_bound F hC hac hnc hb hU
  have h1 : 0 ≤ -⟪x 0 - x 1, x 6 - x 1⟫ := by linarith
  have h2 : -⟪x 0 - x 1, x 6 - x 1⟫ ≤ -⟪x 0 - x 1, x 2 - x 1⟫ := by
    rw [show x 2 - x 6 = (x 2 - x 1) - (x 6 - x 1) by abel, inner_sub_right] at hw
    linarith
  have h3 : nC x * (-⟪x 0 - x 1, x 2 - x 1⟫) ≤ D45 x * (-⟪x 2 - x 1, x 6 - x 1⟫) := by
    dsimp [v31] at hv
    simp only [inner_add_right, inner_smul_right] at hv
    have hcomm : ⟪x 2 - x 1, x 0 - x 1⟫ = ⟪x 0 - x 1, x 2 - x 1⟫ := real_inner_comm _ _
    rw [hcomm] at hv
    linarith
  exact ⟨h1, h2, h3⟩

theorem w26'_diag_band {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x)
    (hab : ⟪x 0 - x 1, x 2 - x 1⟫ ≤ 0) (hac : ⟪x 0 - x 1, x 6 - x 1⟫ ≤ 0)
    (hbc : ⟪x 2 - x 1, x 6 - x 1⟫ ≤ 0)
    (hnb : F.f 3 (x 1) < F.f 3 (x 2)) (hnc : F.f 3 (x 6) < F.f 3 (x 1))
    (hc : oblX6 x 5 < oblX6 x 3) (hU : ¬ LexAny F) :
    0 ≤ -⟪x 0 - x 1, x 2 - x 1⟫ ∧
    -⟪x 0 - x 1, x 2 - x 1⟫ ≤ -⟪x 0 - x 1, x 6 - x 1⟫ ∧
    nB x * (-⟪x 0 - x 1, x 6 - x 1⟫) ≤ D45 x * (-⟪x 2 - x 1, x 6 - x 1⟫) := by
  have hd := w26_diag_band (sym24 F) ((cbarIn_comp_pi24 x).2 hC)
    (by simpa [Function.comp_apply] using hac)
    (by simpa [Function.comp_apply] using hab)
    (by simpa [Function.comp_apply, real_inner_comm] using hbc)
    (by simpa [sym24_f_apply] using hnb)
    (by simpa [sym24_f_apply] using hnc)
    (by simpa [oblX2_comp_pi24] using hc)
    (fun h => hU (lexAny_sym F h))
  simpa [Function.comp_apply, nC_comp_pi24, d45_comp_pi24, real_inner_comm (x 6 - x 1) (x 2 - x 1)] using hd

/-! ### Part 2: `lexAny_or_split_E05P5U` and `isRupert_of_E05P5U` -/

theorem nC_pos_of {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (ha4 : oblX0 x 4 ≤ 1) (ha5 : 1 < oblX0 x 5) : 0 < nC x := by
  have T := type24OfFac F
  have hb4 : 0 < oblX2 x 4 := T.X2_pos (v := 4) (by decide)
  have hb5 : 0 < oblX2 x 5 := T.X2_pos (v := 5) (by decide)
  dsimp [nC]
  nlinarith

theorem R04_neg {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (ha4 : oblX0 x 4 ≤ 1) (ha5 : 1 < oblX0 x 5) : R04 x < 0 := by
  have T := type24OfFac F
  have hb4 : 0 < oblX2 x 4 := T.X2_pos (v := 4) (by decide)
  have hc4 : 0 < oblX6 x 4 := T.X6_pos (v := 4) (by decide)
  have hb5 : 0 < oblX2 x 5 := T.X2_pos (v := 5) (by decide)
  have hc5 : 0 < oblX6 x 5 := T.X6_pos (v := 5) (by decide)
  dsimp [R04]
  nlinarith

theorem R46_neg {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (ha5 : 1 < oblX0 x 5) (hL : 0 ≤ Lam5 x) : R46 x < 0 := by
  have T := type24OfFac F
  have ha3 : 0 < oblX0 x 3 := T.X0_pos (v := 3) (by decide)
  have ha4 : 0 < oblX0 x 4 := T.X0_pos (v := 4) (by decide)
  have hf7_0 : F.f 7 (x 0) = (1 + omega3 x) * F.f 7 (x 1) := by
    have ev7 := fac_eval F 7 3
    rw [F.zero 7 3 (by decide), F.zero 7 2 (by decide), F.zero 7 6 (by decide)] at ev7
    have e3 := eq3 F
    have hprod : oblX0 x 3 * (F.f 7 (x 0) - (1 + omega3 x) * F.f 7 (x 1)) = 0 := by
      linear_combination -ev7 + F.f 7 (x 1) * e3
    exact sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_left ha3.ne')
  have h236_4 : 0 < 1 + omega3 x * oblX0 x 4 - oblX2 x 4 - oblX6 x 4 := by
    have ev := fac_eval F 7 4
    rw [F.zero 7 2 (by decide), F.zero 7 6 (by decide), hf7_0] at ev
    have h71 : 0 < -F.f 7 (x 1) := by linarith [F.neg 7 1 (by decide)]
    have hprod : (-F.f 7 (x 1)) * (1 + omega3 x * oblX0 x 4 - oblX2 x 4 - oblX6 x 4) =
        -F.f 7 (x 4) := by
      rw [ev]; ring
    nlinarith [F.neg 7 4 (by decide)]
  have hR46_id : R46 x = -Lam5 x * oblX0 x 4 -
      (oblX0 x 5 - 1) * (1 + omega3 x * oblX0 x 4 - oblX2 x 4 - oblX6 x 4) := by
    dsimp [R46, Lam5]; ring
  rw [hR46_id]
  nlinarith

theorem robUniLex_five_twopeak (z : ZMod 5 → ℝ × ℝ × ℝ)
    (h04 : (z 0).1 < (z 4).1) (h14 : (z 1).1 < (z 4).1)
    (h43 : (z 4).1 < (z 3).1)
    (h42 : LexPos3 ((z 2).1 - (z 4).1) ((z 2).2.1 - (z 4).2.1) ((z 2).2.2 - (z 4).2.2)) :
    RobUniLex z := by
  intro B b c d hb hbc hcd hd
  have hB : B = 0 ∨ B = 1 ∨ B = 2 ∨ B = 3 ∨ B = 4 := by revert B; decide
  have hbcd : (b = 1 ∧ c = 2 ∧ d = 3) ∨ (b = 1 ∧ c = 2 ∧ d = 4) ∨
      (b = 1 ∧ c = 3 ∧ d = 4) ∨ (b = 2 ∧ c = 3 ∧ d = 4) := by omega
  rcases h42 with h42_0 | ⟨h42_0, h42_1 | ⟨h42_1, h42_2⟩⟩
  all_goals rcases hB with rfl | rfl | rfl | rfl | rfl <;>
    rcases hbcd with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
    simp only [Nat.cast_one, Nat.cast_ofNat,
      show (0 : ZMod 5) + 1 = 1 from rfl, show (0 : ZMod 5) + 2 = 2 from rfl,
      show (0 : ZMod 5) + 3 = 3 from rfl, show (0 : ZMod 5) + 4 = 4 from rfl,
      show (1 : ZMod 5) + 1 = 2 from rfl, show (1 : ZMod 5) + 2 = 3 from rfl,
      show (1 : ZMod 5) + 3 = 4 from rfl, show (1 : ZMod 5) + 4 = 0 from rfl,
      show (2 : ZMod 5) + 1 = 3 from rfl, show (2 : ZMod 5) + 2 = 4 from rfl,
      show (2 : ZMod 5) + 3 = 0 from rfl, show (2 : ZMod 5) + 4 = 1 from rfl,
      show (3 : ZMod 5) + 1 = 4 from rfl, show (3 : ZMod 5) + 2 = 0 from rfl,
      show (3 : ZMod 5) + 3 = 1 from rfl, show (3 : ZMod 5) + 4 = 2 from rfl,
      show (4 : ZMod 5) + 1 = 0 from rfl, show (4 : ZMod 5) + 2 = 1 from rfl,
      show (4 : ZMod 5) + 3 = 2 from rfl, show (4 : ZMod 5) + 4 = 3 from rfl]
  all_goals first
    | exact Or.inl (Or.inl (by linarith))
    | exact Or.inr (Or.inl (Or.inl (by linarith)))
    | exact Or.inr (Or.inr (Or.inl (Or.inl (by linarith))))
    | exact Or.inr (Or.inr (Or.inr (Or.inl (by linarith))))

private theorem e05p5u_split {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (ha5 : 1 < oblX0 x 5) (hR46 : R46 x < 0) (hR04 : R04 x < 0)
    (hfac_lex : ∀ t : Fin 9,
      LexPos3 (if decide (t = 3 ∨ t = 6 ∨ t = 7 ∨ t = 8) then ⟪F.N t, x 5 - x 0⟫ else -⟪F.N t, x 5 - x 0⟫)
              (if decide (t = 3 ∨ t = 6 ∨ t = 7 ∨ t = 8) then ⟪F.N t, x 6 - x 1⟫ else -⟪F.N t, x 6 - x 1⟫)
              (if decide (t = 3 ∨ t = 6 ∨ t = 7 ∨ t = 8) then ⟪F.N t, x 6 - x 5⟫ else -⟪F.N t, x 6 - x 5⟫))
    (hz : ⟪x 4, x 5 - x 0⟫ < ⟪x 5, x 5 - x 0⟫ ∧ ⟪x 5, x 5 - x 0⟫ < ⟪x 2, x 5 - x 0⟫)
    (h65 : LexPos3 (-⟪x 6 - x 5, x 5 - x 0⟫) (-⟪x 6 - x 5, x 6 - x 1⟫) (-⟪x 6 - x 5, x 6 - x 5⟫)) :
    SplitAny24 F := by
  have T := type24OfFac F
  have hb5 : 0 < oblX2 x 5 := T.X2_pos (v := 5) (by decide)
  have hc5 : 0 < oblX6 x 5 := T.X6_pos (v := 5) (by decide)
  have hrows := rows_P5 F
  have hd2 : 0 < det24 x * det24 x := mul_self_pos.mpr T.det_ne
  let w05 : ℝ³ := x 5 - x 0
  let d1 : ℝ³ := x 6 - x 1
  let d2 : ℝ³ := x 6 - x 5
  let c : ZMod 5 → Fin 7 := ![0, 4, 6, 2, 5]
  let pat : Fin 9 → Bool := fun t => decide (t = 3 ∨ t = 6 ∨ t = 7 ∨ t = 8)
  have hz05 : ⟪x 0 - x 5, w05⟫ < 0 := by
    dsimp [w05]; rw [← neg_sub, inner_neg_left]
    have hw_ne : w05 ≠ 0 := sub_ne_zero.mpr fun h => absurd (T.inj h) (by decide)
    exact neg_neg_of_pos (real_inner_self_pos.mpr hw_ne)
  have hz45 : ⟪x 4 - x 5, w05⟫ < 0 := by rw [inner_sub_left]; exact sub_lt_zero.mpr hz.1
  have hz25 : 0 < ⟪x 2 - x 5, w05⟫ := by rw [inner_sub_left]; exact sub_pos.mpr hz.2
  refine splitAny24_of_lex3' F (by decide) c
    (by intro i j h; fin_cases i <;> fin_cases j <;> first | rfl | exact absurd h (by decide))
    pat (by unfold S0xCycOK; decide) w05 d1 d2 hfac_lex 2 4 (by decide) (by decide) (det24 x) ?_
  intro i hia j hj hjc
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by decide +revert
  have hc0 : c 0 = 0 := rfl
  have hc1 : c 1 = 4 := rfl
  have hc2 : c 2 = 6 := rfl
  have hc3 : c 3 = 2 := rfl
  have hc4 : c 4 = 5 := rfl
  have he0 : (0 : ZMod 5) + 1 = 1 := rfl
  have he1 : (1 : ZMod 5) + 1 = 2 := rfl
  have he2 : (2 : ZMod 5) + 1 = 3 := rfl
  have he3 : (3 : ZMod 5) + 1 = 4 := rfl
  have he4 : (4 : ZMod 5) + 1 = 0 := rfl
  rcases hi with rfl | rfl | rfl | rfl | rfl
  · rcases hj with rfl | rfl
    · refine ⟨-1, Or.inl (by rw [hc0, hc4]; linarith [hz05]), Or.inl ?_⟩
      rw [he0, he2, hc0, hc1, hc2, hc3]; dsimp [w05]; rw [hrows.1]
      have h1 : det24 x * -1 * (det24 x * R04 x) = (det24 x * det24 x) * (-R04 x) := by ring
      rw [h1]; exact mul_pos hd2 (neg_pos.mpr hR04)
    · refine ⟨-1, Or.inl (by rw [he0, hc1, hc4]; linarith [hz45]), Or.inl ?_⟩
      rw [he0, he2, hc0, hc1, hc2, hc3]; dsimp [w05]; rw [hrows.1]
      have h1 : det24 x * -1 * (det24 x * R04 x) = (det24 x * det24 x) * (-R04 x) := by ring
      rw [h1]; exact mul_pos hd2 (neg_pos.mpr hR04)
  · rcases hj with rfl | rfl
    · refine ⟨-1, Or.inl (by rw [hc1, hc4]; linarith [hz45]), Or.inl ?_⟩
      rw [he1, he2, hc1, hc2, hc3]; dsimp [w05]; rw [hrows.2.1]
      have h1 : det24 x * -1 * (det24 x * R46 x) = (det24 x * det24 x) * (-R46 x) := by ring
      rw [h1]; exact mul_pos hd2 (neg_pos.mpr hR46)
    · refine ⟨-1, ?_, Or.inl ?_⟩
      · rw [he1, hc2, hc4]
        simpa only [neg_one_mul] using h65
      · rw [he1, he2, hc1, hc2, hc3]; dsimp [w05]; rw [hrows.2.1]
        have h1 : det24 x * -1 * (det24 x * R46 x) = (det24 x * det24 x) * (-R46 x) := by ring
        rw [h1]; exact mul_pos hd2 (neg_pos.mpr hR46)
  · exact absurd rfl hia
  · rcases hj with rfl | rfl
    · refine ⟨1, Or.inl (by rw [hc3, hc4]; linarith [hz25]), Or.inl ?_⟩
      rw [he3, he2, hc2, hc3, hc4]; dsimp [w05]; rw [hrows.2.2.1]
      have h5_pos : 0 < oblX0 x 5 + oblX2 x 5 + oblX6 x 5 - 1 := by linarith
      have h1 : det24 x * 1 * (det24 x * (oblX0 x 5 + oblX2 x 5 + oblX6 x 5 - 1)) =
          (det24 x * det24 x) * (oblX0 x 5 + oblX2 x 5 + oblX6 x 5 - 1) := by ring
      rw [h1]; exact mul_pos hd2 h5_pos
    · exact absurd rfl hjc
  · rcases hj with rfl | rfl
    · exact absurd rfl hjc
    · refine ⟨-1, Or.inl (by rw [he4, hc0, hc4]; linarith [hz05]), Or.inr ⟨?_, Or.inl ?_⟩⟩
      · rw [he4, he2, hc0, hc2, hc3, hc4]; dsimp [w05]
        have : det3 (x 0 - x 5) (x 2 - x 6) (x 5 - x 0) = 0 := by
          simp only [det3_expand, PiLp.sub_apply]; ring
        rw [this, mul_zero]
      · rw [he4, he2, hc0, hc2, hc3, hc4]; dsimp [d1]; rw [hrows.2.2.2]
        have h1 : det24 x * -1 * (det24 x * (1 - oblX0 x 5)) =
            (det24 x * det24 x) * (oblX0 x 5 - 1) := by ring
        rw [h1]; exact mul_pos hd2 (sub_pos.mpr ha5)

theorem lexAny_or_split_E05P5U {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hC : CbarIn x) (ha5 : 1 < oblX0 x 5) (ha4 : oblX0 x 4 ≤ 1)
    (hL : 0 ≤ Lam5 x) (h346 : F.f 8 (x 0) ≤ F.f 8 (x 5))
    (hz : ⟪x 4, x 5 - x 0⟫ < ⟪x 5, x 5 - x 0⟫ ∧
          ⟪x 5, x 5 - x 0⟫ < ⟪x 2, x 5 - x 0⟫) :
    LexAny F ∨ SplitAny24 F := by
  have T := type24OfFac F
  have hc5 : 0 < oblX6 x 5 := T.X6_pos (v := 5) (by decide)
  have hb5 : 0 < oblX2 x 5 := T.X2_pos (v := 5) (by decide)
  have hnc : F.f 3 (x 1) < F.f 3 (x 6) :=
    (nC_pos_iff F).mp (nC_pos_of F ha4 ha5)
  have hR46 : R46 x < 0 := R46_neg F ha5 hL
  have hR04 : R04 x < 0 := R04_neg F ha4 ha5
  let w05 : ℝ³ := x 5 - x 0
  let d1 : ℝ³ := x 6 - x 1
  let d2 : ℝ³ := x 6 - x 5
  let c : ZMod 5 → Fin 7 := ![0, 4, 6, 2, 5]
  let pat : Fin 9 → Bool := fun t => decide (t = 3 ∨ t = 6 ∨ t = 7 ∨ t = 8)
  have hc_inj : Function.Injective c := by
    intro i j h; fin_cases i <;> fin_cases j <;> first | rfl | exact absurd h (by decide)
  have hcyc_ok : S0xCycOK s0x_S24 c pat := by unfold S0xCycOK; decide
  -- Facings at `(w05, d1, d2)`:
  have hf0 : ⟪F.N 0, w05⟫ < 0 := by
    dsimp [w05]; rw [← F.hN 0 (x 5) (x 0), F.zero 0 0 (by decide), sub_zero]
    exact F.neg 0 5 (by decide)
  have hf1 : ⟪F.N 1, w05⟫ < 0 := by
    dsimp [w05]; rw [← F.hN 1 (x 5) (x 0), F.zero 1 0 (by decide), sub_zero]
    exact F.neg 1 5 (by decide)
  have hf2_0 : ⟪F.N 2, w05⟫ = 0 := by
    dsimp [w05]; rw [← F.hN 2 (x 5) (x 0), F.zero 2 5 (by decide), F.zero 2 0 (by decide), sub_self]
  have hd2_1 : 0 < -⟪F.N 2, d1⟫ := by
    dsimp [d1]; rw [← F.hN 2 (x 6) (x 1)]
    have ev25 := fac_eval F 2 5
    rw [F.zero 2 5 (by decide), F.zero 2 0 (by decide), F.zero 2 2 (by decide)] at ev25
    have e5 := eq5 F
    have h1' : F.f 2 (x 1) * (1 - oblX0 x 5 - oblX2 x 5) +
        oblX6 x 5 * (F.f 2 (x 6) - F.f 2 (x 1)) = 0 := by linear_combination -ev25
    have h2' : oblX6 x 5 * ((F.f 2 (x 6) - F.f 2 (x 1)) - F.f 2 (x 1) * omega5 x) = 0 := by
      linear_combination h1' + F.f 2 (x 1) * e5
    have h6_eq : F.f 2 (x 6) - F.f 2 (x 1) = F.f 2 (x 1) * omega5 x :=
      sub_eq_zero.mp ((mul_eq_zero.mp h2').resolve_left hc5.ne')
    rw [h6_eq, ← neg_mul]
    exact mul_pos (by linarith [F.neg 2 1 (by decide)]) hC.2.2.1
  have hf3_0 : ⟪F.N 3, w05⟫ = 0 := by
    dsimp [w05]; rw [← F.hN 3 (x 5) (x 0), F.zero 3 5 (by decide), F.zero 3 0 (by decide), sub_self]
  have hd3_1 : 0 < ⟪F.N 3, d1⟫ := by
    dsimp [d1]; rw [← F.hN 3 (x 6) (x 1)]; exact sub_pos.mpr hnc
  have hf4 : ⟪F.N 4, w05⟫ < 0 := by
    dsimp [w05]; rw [← F.hN 4 (x 5) (x 0), F.zero 4 0 (by decide), sub_zero]
    exact F.neg 4 5 (by decide)
  have hf5 : ⟪F.N 5, w05⟫ < 0 := by
    dsimp [w05]; rw [← F.hN 5 (x 5) (x 0)]
    have ev5 := fac_eval F 5 5
    rw [F.zero 5 1 (by decide), F.zero 5 2 (by decide), F.zero 5 6 (by decide)] at ev5
    rw [ev5]
    have hmul : (oblX0 x 5 - 1) * F.f 5 (x 0) =
        (0 + oblX0 x 5 * (F.f 5 (x 0) - 0) + oblX2 x 5 * (0 - 0) + oblX6 x 5 * (0 - 0)) -
          F.f 5 (x 0) := by ring
    rw [← hmul]
    exact mul_neg_of_pos_of_neg (sub_pos.mpr ha5) (F.neg 5 0 (by decide))
  have hf6 : 0 < ⟪F.N 6, w05⟫ := by
    dsimp [w05]; rw [← F.hN 6 (x 5) (x 0), F.zero 6 5 (by decide), zero_sub]
    linarith [F.neg 6 0 (by decide)]
  have hf7_lex : LexPos3 ⟪F.N 7, w05⟫ ⟪F.N 7, d1⟫ ⟪F.N 7, d2⟫ := by
    have ha3 : 0 < oblX0 x 3 := T.X0_pos (v := 3) (by decide)
    have hf7_0 : F.f 7 (x 0) = (1 + omega3 x) * F.f 7 (x 1) := by
      have ev7_3 := fac_eval F 7 3
      rw [F.zero 7 3 (by decide), F.zero 7 2 (by decide), F.zero 7 6 (by decide)] at ev7_3
      have e3 := eq3 F
      have h7_id : oblX0 x 3 * (F.f 7 (x 0) - (1 + omega3 x) * F.f 7 (x 1)) = 0 := by
        linear_combination -ev7_3 + F.f 7 (x 1) * e3
      exact sub_eq_zero.mp ((mul_eq_zero.mp h7_id).resolve_left ha3.ne')
    have hw7 : ⟪F.N 7, w05⟫ = (-F.f 7 (x 1)) * Lam5 x := by
      dsimp [w05, Lam5]; rw [← F.hN 7 (x 5) (x 0)]
      have ev7_5 := fac_eval F 7 5
      rw [F.zero 7 2 (by decide), F.zero 7 6 (by decide), hf7_0] at ev7_5
      rw [ev7_5, hf7_0]; ring
    have hd7_1 : 0 < ⟪F.N 7, d1⟫ := by
      dsimp [d1]; rw [← F.hN 7 (x 6) (x 1), F.zero 7 6 (by decide), zero_sub]
      linarith [F.neg 7 1 (by decide)]
    rcases eq_or_lt_of_le hL with hL0 | hLpos
    · exact Or.inr ⟨by rw [hw7, ← hL0, mul_zero], Or.inl hd7_1⟩
    · exact Or.inl (by rw [hw7]; exact mul_pos (by linarith [F.neg 7 1 (by decide)]) hLpos)
  have hf8_lex : LexPos3 ⟪F.N 8, w05⟫ ⟪F.N 8, d1⟫ ⟪F.N 8, d2⟫ := by
    have hw8 : ⟪F.N 8, w05⟫ = F.f 8 (x 5) - F.f 8 (x 0) := by
      dsimp [w05]; rw [← F.hN 8 (x 5) (x 0)]
    have hd8_1 : 0 < ⟪F.N 8, d1⟫ := by
      dsimp [d1]; rw [← F.hN 8 (x 6) (x 1), F.zero 8 6 (by decide), zero_sub]
      linarith [F.neg 8 1 (by decide)]
    rcases eq_or_lt_of_le h346 with heq | hlt
    · exact Or.inr ⟨by rw [hw8, heq, sub_self], Or.inl hd8_1⟩
    · exact Or.inl (by rw [hw8]; linarith)
  have hfac_lex : ∀ t : Fin 9,
      LexPos3 (if pat t then ⟪F.N t, w05⟫ else -⟪F.N t, w05⟫)
              (if pat t then ⟪F.N t, d1⟫ else -⟪F.N t, d1⟫)
              (if pat t then ⟪F.N t, d2⟫ else -⟪F.N t, d2⟫) := by
    intro t; fin_cases t <;> simp [pat]
    · exact Or.inl (by linarith)
    · exact Or.inl (by linarith)
    · exact Or.inr ⟨by rw [hf2_0, neg_zero], Or.inl hd2_1⟩
    · exact Or.inr ⟨hf3_0, Or.inl hd3_1⟩
    · exact Or.inl (by linarith)
    · exact Or.inl (by linarith)
    · exact Or.inl hf6
    · exact hf7_lex
    · exact hf8_lex
  -- Case split on the lex sign of `⟪x 6 - x 5, (w05, d1, d2)⟫`:
  have hd2_pos : 0 < ⟪x 6 - x 5, d2⟫ := by
    dsimp [d2]
    exact real_inner_self_pos.mpr (sub_ne_zero.mpr fun h => absurd (T.inj h) (by decide))
  by_cases hz65_0 : ⟪x 6 - x 5, w05⟫ = 0
  · by_cases hz65_1 : ⟪x 6 - x 5, d1⟫ < 0
    · -- Tie broken negatively at level 1 -> `SplitAny24 F`:
      exact Or.inr (e05p5u_split F ha5 hR46 hR04 hfac_lex hz
        (Or.inr ⟨by rw [neg_eq_zero]; exact hz65_0, Or.inl (neg_pos.mpr hz65_1)⟩))
    · -- Tie broken positively (`z5 <lex z6`) -> `LexAny F`:
      left
      have h65_lex : LexPos3 (⟪x 6, w05⟫ - ⟪x 5, w05⟫) (⟪x 6, d1⟫ - ⟪x 5, d1⟫)
          (⟪x 6, d2⟫ - ⟪x 5, d2⟫) := by
        rw [← inner_sub_left, ← inner_sub_left, ← inner_sub_left]
        rcases eq_or_lt_of_le (not_lt.mp hz65_1) with heq | hlt
        · exact Or.inr ⟨hz65_0, Or.inr ⟨heq.symm, hd2_pos⟩⟩
        · exact Or.inr ⟨hz65_0, Or.inl hlt⟩
      have hz05_lt : ⟪x 0, w05⟫ < ⟪x 5, w05⟫ := by
        refine sub_lt_zero.mp ?_
        have h_eq : ⟪x 0, w05⟫ - ⟪x 5, w05⟫ = -⟪w05, w05⟫ := by
          dsimp [w05]; rw [← inner_sub_left, ← neg_sub, inner_neg_left]
        have hw_ne : w05 ≠ 0 := sub_ne_zero.mpr fun h => absurd (T.inj h) (by decide)
        rw [h_eq]
        exact neg_neg_of_pos (real_inner_self_pos.mpr hw_ne)
      refine ⟨5, inferInstance, c, {3, 6, 7, 8}, {0, 1, 2, 4, 5}, w05, d1, d2, by decide,
        hc_inj, (by unfold S0xCycUD; decide), ?_, ?_, ?_⟩
      · intro t ht; simp only [Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl | rfl | rfl
        · exact Or.inr ⟨hf3_0, Or.inl hd3_1⟩
        · exact Or.inl hf6
        · exact hf7_lex
        · exact hf8_lex
      · intro t ht; simp only [Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl | rfl | rfl | rfl
        · exact Or.inl (by linarith)
        · exact Or.inl (by linarith)
        · exact Or.inr ⟨by rw [hf2_0, neg_zero], Or.inl hd2_1⟩
        · exact Or.inl (by linarith)
        · exact Or.inl (by linarith)
      · refine robUniLex_five_twopeak _ ?_ ?_ ?_ h65_lex
        · have hc0 : c 0 = 0 := rfl
          have hc4 : c 4 = 5 := rfl
          rw [hc0, hc4]; exact hz05_lt
        · have hc1 : c 1 = 4 := rfl
          have hc4 : c 4 = 5 := rfl
          rw [hc1, hc4]; exact hz.1
        · have hc4 : c 4 = 5 := rfl
          have hc3 : c 3 = 2 := rfl
          rw [hc4, hc3]; exact hz.2
  · rcases lt_or_gt_of_ne hz65_0 with hz65_neg | hz65_pos
    · -- Strict `z6 < z5` -> `SplitAny24 F`:
      exact Or.inr (e05p5u_split F ha5 hR46 hR04 hfac_lex hz (Or.inl (neg_pos.mpr hz65_neg)))
    · -- Strict `z5 < z6` -> `LexAny F`:
      left
      have h65_lex : LexPos3 (⟪x 6, w05⟫ - ⟪x 5, w05⟫) (⟪x 6, d1⟫ - ⟪x 5, d1⟫)
          (⟪x 6, d2⟫ - ⟪x 5, d2⟫) := by
        rw [← inner_sub_left]; exact Or.inl hz65_pos
      have hz05_lt : ⟪x 0, w05⟫ < ⟪x 5, w05⟫ := by
        refine sub_lt_zero.mp ?_
        have h_eq : ⟪x 0, w05⟫ - ⟪x 5, w05⟫ = -⟪w05, w05⟫ := by
          dsimp [w05]; rw [← inner_sub_left, ← neg_sub, inner_neg_left]
        have hw_ne : w05 ≠ 0 := sub_ne_zero.mpr fun h => absurd (T.inj h) (by decide)
        rw [h_eq]
        exact neg_neg_of_pos (real_inner_self_pos.mpr hw_ne)
      refine ⟨5, inferInstance, c, {3, 6, 7, 8}, {0, 1, 2, 4, 5}, w05, d1, d2, by decide,
        hc_inj, (by unfold S0xCycUD; decide), ?_, ?_, ?_⟩
      · intro t ht; simp only [Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl | rfl | rfl
        · exact Or.inr ⟨hf3_0, Or.inl hd3_1⟩
        · exact Or.inl hf6
        · exact hf7_lex
        · exact hf8_lex
      · intro t ht; simp only [Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl | rfl | rfl | rfl
        · exact Or.inl (by linarith)
        · exact Or.inl (by linarith)
        · exact Or.inr ⟨by rw [hf2_0, neg_zero], Or.inl hd2_1⟩
        · exact Or.inl (by linarith)
        · exact Or.inl (by linarith)
      · refine robUniLex_five_twopeak _ ?_ ?_ ?_ h65_lex
        · have hc0 : c 0 = 0 := rfl
          have hc4 : c 4 = 5 := rfl
          rw [hc0, hc4]; exact hz05_lt
        · have hc1 : c 1 = 4 := rfl
          have hc4 : c 4 = 5 := rfl
          rw [hc1, hc4]; exact hz.1
        · have hc4 : c 4 = 5 := rfl
          have hc3 : c 3 = 2 := rfl
          rw [hc4, hc3]; exact hz.2

theorem isRupert_of_E05P5U {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hC : CbarIn x) (ha5 : 1 < oblX0 x 5) (ha4 : oblX0 x 4 < 1)
    (hL : 0 ≤ Lam5 x) (h346 : F.f 8 (x 0) ≤ F.f 8 (x 5))
    (hz : ⟪x 4, x 5 - x 0⟫ < ⟪x 5, x 5 - x 0⟫ ∧
          ⟪x 5, x 5 - x 0⟫ < ⟪x 2, x 5 - x 0⟫) :
    IsRupert (univ.image x) := by
  rcases lexAny_or_split_E05P5U F hC ha5 ha4.le hL h346 hz with hL' | hS'
  · exact lexAny_isRupert F hL'
  · exact splitAny24_isRupert F hS'

/-! ### Part 3: `splitAny24_E0416` and `isRupert_of_E0416` -/

theorem splitAny24_E0416 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hC : CbarIn x) (ha4 : oblX0 x 4 ≤ 1) (hnc : F.f 3 (x 6) < F.f 3 (x 1))
    (htau : F.f 6 (x 0) < F.f 6 (x 4))
    (hrow : (1 - oblX0 x 4) * (1 - oblX2 x 5) < oblX0 x 5 * oblX2 x 4)
    (hz : max 0 (max ⟪x 2 - x 1, x 4 - x 0⟫ ⟪x 5 - x 1, x 4 - x 0⟫) < ⟪x 4 - x 1, x 4 - x 0⟫ ∧
          ⟪x 4 - x 1, x 4 - x 0⟫ < ⟪x 6 - x 1, x 4 - x 0⟫) :
    SplitAny24 F := by
  have T := type24OfFac F
  have hom3 : 0 < omega3 x := hC.1
  have hb4 : 0 < oblX2 x 4 := T.X2_pos (v := 4) (by decide)
  have ha3 : 0 < oblX0 x 3 := T.X0_pos (v := 3) (by decide)
  have hnC_neg : nC x < 0 := by
    by_contra h; push Not at h
    rcases eq_or_lt_of_le h with h0 | hpos
    · have ev4 := fac_eval F 3 4
      have ev5 := fac_eval F 3 5
      rw [F.zero 3 4 (by decide), F.zero 3 0 (by decide)] at ev4
      rw [F.zero 3 5 (by decide), F.zero 3 0 (by decide)] at ev5
      have h31 : F.f 3 (x 1) < 0 := F.neg 3 1 (by decide)
      have h32 : F.f 3 (x 2) < 0 := F.neg 3 2 (by decide)
      have hlin : D45 x * (F.f 3 (x 6) - F.f 3 (x 1)) = -nC x * F.f 3 (x 1) := by
        dsimp [D45, nC]
        linear_combination oblX2 x 4 * ev5 - oblX2 x 5 * ev4
      rw [← h0, neg_zero, zero_mul] at hlin
      have hd45 : 0 < D45 x := d45_pos F
      nlinarith
    · exact absurd ((nC_pos_iff F).mp hpos) (by linarith)
  have hd45 : 0 < D45 x := d45_pos F
  let b : ℝ³ := x 0 - x 4
  let d1 : ℝ³ := v31 x + (x 6 - x 1)
  let c : ZMod 6 → Fin 7 := ![0, 4, 6, 1, 2, 5]
  let pat : Fin 9 → Bool := fun t => decide (t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 4)
  -- Facings at `(b, d1, 0)`:
  have hf0 : 0 < ⟪F.N 0, b⟫ := by
    dsimp [b]; rw [← F.hN 0 (x 0) (x 4), F.zero 0 0 (by decide), zero_sub]
    linarith [F.neg 0 4 (by decide)]
  have hf1 : 0 < ⟪F.N 1, b⟫ := by
    dsimp [b]; rw [← F.hN 1 (x 0) (x 4), F.zero 1 0 (by decide), zero_sub]
    linarith [F.neg 1 4 (by decide)]
  have hf2 : 0 < ⟪F.N 2, b⟫ := by
    dsimp [b]; rw [← F.hN 2 (x 0) (x 4), F.zero 2 0 (by decide), zero_sub]
    linarith [F.neg 2 4 (by decide)]
  have hf3_0 : ⟪F.N 3, b⟫ = 0 := by
    dsimp [b]; rw [← F.hN 3 (x 0) (x 4), F.zero 3 0 (by decide), F.zero 3 4 (by decide), sub_self]
  have hd3_1 : 0 < -⟪F.N 3, d1⟫ := by
    dsimp [d1, v31]
    rw [inner_add_right, inner_add_right, inner_smul_right, inner_smul_right,
      ← F.hN 3 (x 0) (x 1), ← F.hN 3 (x 6) (x 1), F.zero 3 0 (by decide), zero_sub]
    have hv31_3 : -nC x * (-F.f 3 (x 1)) + D45 x * (F.f 3 (x 6) - F.f 3 (x 1)) = 0 := by
      have ev4 := fac_eval F 3 4
      have ev5 := fac_eval F 3 5
      rw [F.zero 3 4 (by decide), F.zero 3 0 (by decide)] at ev4
      rw [F.zero 3 5 (by decide), F.zero 3 0 (by decide)] at ev5
      dsimp [D45, nC]
      linear_combination oblX2 x 4 * ev5 - oblX2 x 5 * ev4
    linarith
  have hf4_0 : ⟪F.N 4, b⟫ = 0 := by
    dsimp [b]; rw [← F.hN 4 (x 0) (x 4), F.zero 4 0 (by decide), F.zero 4 4 (by decide), sub_self]
  have hd4_1 : 0 < ⟪F.N 4, d1⟫ := by
    dsimp [d1, v31]
    rw [inner_add_right, inner_add_right, inner_smul_right, inner_smul_right,
      ← F.hN 4 (x 0) (x 1), ← F.hN 4 (x 6) (x 1), F.zero 4 0 (by decide), F.zero 4 6 (by decide),
      zero_sub]
    have h41 : 0 < -F.f 4 (x 1) := by linarith [F.neg 4 1 (by decide)]
    nlinarith
  have hf5_lex : LexPos3 (-⟪F.N 5, b⟫) (-⟪F.N 5, d1⟫) 0 := by
    have hb5' : -⟪F.N 5, b⟫ = (1 - oblX0 x 4) * (-F.f 5 (x 0)) := by
      dsimp [b]; rw [← F.hN 5 (x 0) (x 4)]
      have ev4 := fac_eval F 5 4
      rw [F.zero 5 1 (by decide), F.zero 5 2 (by decide), F.zero 5 6 (by decide)] at ev4
      rw [ev4]; ring
    have hd5' : -⟪F.N 5, d1⟫ = nC x * F.f 5 (x 0) := by
      dsimp [d1, v31]
      rw [inner_add_right, inner_add_right, inner_smul_right, inner_smul_right,
        ← F.hN 5 (x 0) (x 1), ← F.hN 5 (x 6) (x 1), F.zero 5 1 (by decide), F.zero 5 6 (by decide)]
      ring
    have h50 : F.f 5 (x 0) < 0 := F.neg 5 0 (by decide)
    rcases eq_or_lt_of_le ha4 with heq | hlt
    · exact Or.inr ⟨by rw [hb5', heq, sub_self, zero_mul],
        Or.inl (by rw [hd5']; exact mul_pos_of_neg_of_neg hnC_neg h50)⟩
    · exact Or.inl (by rw [hb5']; exact mul_pos (sub_pos.mpr hlt) (by linarith))
  have hf6 : 0 < -⟪F.N 6, b⟫ := by
    dsimp [b]; rw [← F.hN 6 (x 0) (x 4)]; linarith
  have hf7 : 0 < -⟪F.N 7, b⟫ := by
    dsimp [b]; rw [← F.hN 7 (x 0) (x 4)]
    have hf7_0 : F.f 7 (x 0) = (1 + omega3 x) * F.f 7 (x 1) := by
      have ev7_3 := fac_eval F 7 3
      rw [F.zero 7 3 (by decide), F.zero 7 2 (by decide), F.zero 7 6 (by decide)] at ev7_3
      have e3 := eq3 F
      have h7_id : oblX0 x 3 * (F.f 7 (x 0) - (1 + omega3 x) * F.f 7 (x 1)) = 0 := by
        linear_combination -ev7_3 + F.f 7 (x 1) * e3
      exact sub_eq_zero.mp ((mul_eq_zero.mp h7_id).resolve_left ha3.ne')
    have ev7_4 := fac_eval F 7 4
    rw [F.zero 7 2 (by decide), F.zero 7 6 (by decide), hf7_0] at ev7_4
    have h71 : 0 < -F.f 7 (x 1) := by linarith [F.neg 7 1 (by decide)]
    have hdiff : -(F.f 7 (x 0) - F.f 7 (x 4)) =
        (-F.f 7 (x 1)) * (oblX2 x 4 + oblX6 x 4 + omega3 x * (1 - oblX0 x 4)) := by
      rw [ev7_4, hf7_0]; ring
    rw [hdiff]
    have hc4 : 0 < oblX6 x 4 := T.X6_pos (v := 4) (by decide)
    exact mul_pos h71 (by nlinarith)
  have hf8 : 0 < -⟪F.N 8, b⟫ := by
    dsimp [b]; rw [← F.hN 8 (x 0) (x 4), F.zero 8 4 (by decide), sub_zero]
    linarith [F.neg 8 0 (by decide)]
  have hfac_lex : ∀ t : Fin 9,
      LexPos3 (if pat t then ⟪F.N t, b⟫ else -⟪F.N t, b⟫)
              (if pat t then ⟪F.N t, d1⟫ else -⟪F.N t, d1⟫) 0 := by
    intro t; fin_cases t <;> simp [pat]
    · exact Or.inl hf0
    · exact Or.inl hf1
    · exact Or.inl hf2
    · exact Or.inr ⟨by rw [hf3_0, neg_zero], Or.inl hd3_1⟩
    · exact Or.inr ⟨hf4_0, Or.inl hd4_1⟩
    · exact hf5_lex
    · exact Or.inl hf6
    · exact Or.inl hf7
    · exact Or.inl hf8
  -- Depth signs at `b = x 0 - x 4`:
  have hz04 : 0 < ⟪x 0 - x 4, b⟫ := by
    dsimp [b]
    exact real_inner_self_pos.mpr (sub_ne_zero.mpr fun h => absurd (T.inj h) (by decide))
  have hz14 : 0 < ⟪x 1 - x 4, b⟫ := by
    have h4_pos : 0 < ⟪x 4 - x 1, x 4 - x 0⟫ := lt_of_le_of_lt (le_max_left _ _) hz.1
    dsimp [b]
    rw [show x 1 - x 4 = -(x 4 - x 1) by abel, show x 0 - x 4 = -(x 4 - x 0) by abel,
      inner_neg_left, inner_neg_right, neg_neg]
    exact h4_pos
  have hz24 : 0 < ⟪x 2 - x 4, b⟫ := by
    have h2_lt : ⟪x 2 - x 1, x 4 - x 0⟫ < ⟪x 4 - x 1, x 4 - x 0⟫ :=
      lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hz.1
    dsimp [b]
    rw [show x 2 - x 4 = (x 2 - x 1) - (x 4 - x 1) by abel, show x 0 - x 4 = -(x 4 - x 0) by abel,
      inner_neg_right, inner_sub_left]
    linarith
  have hz54 : 0 < ⟪x 5 - x 4, b⟫ := by
    have h5_lt : ⟪x 5 - x 1, x 4 - x 0⟫ < ⟪x 4 - x 1, x 4 - x 0⟫ :=
      lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hz.1
    dsimp [b]
    rw [show x 5 - x 4 = (x 5 - x 1) - (x 4 - x 1) by abel, show x 0 - x 4 = -(x 4 - x 0) by abel,
      inner_neg_right, inner_sub_left]
    linarith
  have hz64 : ⟪x 6 - x 4, b⟫ < 0 := by
    dsimp [b]
    rw [show x 6 - x 4 = (x 6 - x 1) - (x 4 - x 1) by abel, show x 0 - x 4 = -(x 4 - x 0) by abel,
      inner_neg_right, inner_sub_left]
    linarith [hz.2]
  -- Row determinant formulas with `x 1 - x 6 = -(x 6 - x 1)`:
  have hrep : ∀ v : Fin 7, x v - x 1 =
      oblX0 x v • (x 0 - x 1) + oblX2 x v • (x 2 - x 1) + oblX6 x v • (x 6 - x 1) := by
    intro v; rw [T.rep v]; abel
  have h16 : x 1 - x 6 = (0 : ℝ) • (x 0 - x 1) + (0 : ℝ) • (x 2 - x 1) + (-1 : ℝ) • (x 6 - x 1) := by
    module
  have hb_rep : b = (1 - oblX0 x 4) • (x 0 - x 1) + (-oblX2 x 4) • (x 2 - x 1) +
      (-oblX6 x 4) • (x 6 - x 1) := by
    dsimp [b]; rw [show x 0 - x 4 = (x 0 - x 1) - (x 4 - x 1) by abel, hrep 4]; module
  have hd1_rep : d1 = (-nC x) • (x 0 - x 1) + (0 : ℝ) • (x 2 - x 1) +
      (D45 x + 1) • (x 6 - x 1) := by
    dsimp [d1, v31]; module
  have hdet_b : ∀ (u : ℝ³) (α β γ : ℝ),
      u = α • (x 0 - x 1) + β • (x 2 - x 1) + γ • (x 6 - x 1) →
      det3 u (x 1 - x 6) b = det24 x * (-α * oblX2 x 4 - β * (1 - oblX0 x 4)) := by
    intro u α β γ hu
    rw [hu, h16, hb_rep, M4.det3_frame]
    ring
  have hdet_d1 : ∀ (u : ℝ³) (α β γ : ℝ),
      u = α • (x 0 - x 1) + β • (x 2 - x 1) + γ • (x 6 - x 1) →
      det3 u (x 1 - x 6) d1 = det24 x * (β * nC x) := by
    intro u α β γ hu
    rw [hu, h16, hd1_rep, M4.det3_frame]
    ring
  have hd2 : 0 < det24 x * det24 x := mul_self_pos.mpr T.det_ne
  refine splitAny24_of_lex3' F (by decide) c
    (by intro i j h; fin_cases i <;> fin_cases j <;> first | rfl | exact absurd h (by decide))
    pat (by unfold S0xCycOK; decide) b d1 0
    (by intro t; simpa only [inner_zero_right, neg_zero, ite_self] using hfac_lex t)
    2 1 (by decide) (by decide) (-det24 x) ?_
  intro i hia j hj hjc
  have hc0 : c 0 = 0 := rfl
  have hc1 : c 1 = 4 := rfl
  have hc2 : c 2 = 6 := rfl
  have hc3 : c 3 = 1 := rfl
  have hc4 : c 4 = 2 := rfl
  have hc5 : c 5 = 5 := rfl
  have he0 : (0 : ZMod 6) + 1 = 1 := rfl
  have he1 : (1 : ZMod 6) + 1 = 2 := rfl
  have he3 : (3 : ZMod 6) + 1 = 4 := rfl
  have he4 : (4 : ZMod 6) + 1 = 5 := rfl
  have he5 : (5 : ZMod 6) + 1 = 0 := rfl
  have he2 : (2 : ZMod 6) + 1 = 3 := rfl
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by decide +revert
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
  · rcases hj with rfl | rfl
    · refine ⟨1, Or.inl (by rw [hc0, hc1]; linarith [hz04]), Or.inr ⟨?_, Or.inl ?_⟩⟩
      · rw [he0, he2, hc0, hc1, hc2, hc3]
        rw [hdet_b _ (oblX0 x 4 - 1) (oblX2 x 4) (oblX6 x 4)
          (by rw [show x 4 - x 0 = (x 4 - x 1) - (x 0 - x 1) by abel, hrep 4]; module)]
        ring
      · rw [he0, he2, hc0, hc1, hc2, hc3]
        rw [hdet_d1 _ (oblX0 x 4 - 1) (oblX2 x 4) (oblX6 x 4)
          (by rw [show x 4 - x 0 = (x 4 - x 1) - (x 0 - x 1) by abel, hrep 4]; module)]
        nlinarith [mul_neg_of_pos_of_neg hb4 hnC_neg]
    · exact absurd rfl hjc
  · rcases hj with rfl | rfl
    · exact absurd rfl hjc
    · refine ⟨-1, Or.inl (by rw [he1, hc2, hc1]; linarith [hz64]), Or.inl ?_⟩
      rw [he1, he2, hc1, hc2, hc3]
      rw [hdet_b _ (-oblX0 x 4) (-oblX2 x 4) (1 - oblX6 x 4)
        (by rw [show x 6 - x 4 = (x 6 - x 1) - (x 4 - x 1) by abel, hrep 4]; module)]
      nlinarith
  · exact absurd rfl hia
  · rcases hj with rfl | rfl
    · refine ⟨1, Or.inl (by rw [hc3, hc1]; linarith [hz14]), ?_⟩
      rw [he3, he2, hc2, hc3, hc4]
      rw [hdet_b _ 0 1 0 (by module), hdet_d1 _ 0 1 0 (by module)]
      rcases eq_or_lt_of_le ha4 with heq | hlt
      · exact Or.inr ⟨by rw [heq]; ring, Or.inl (by
          have h1 : 0 < (-det24 x) * 1 * (det24 x * (1 * nC x)) := by
            have : (-det24 x) * 1 * (det24 x * (1 * nC x)) = (det24 x * det24 x) * (-nC x) := by ring
            rw [this]; exact mul_pos hd2 (neg_pos.mpr hnC_neg)
          exact h1)⟩
      · exact Or.inl (by
          have h1 : 0 < (-det24 x) * 1 * (det24 x * (-0 * oblX2 x 4 - 1 * (1 - oblX0 x 4))) := by
            have : (-det24 x) * 1 * (det24 x * (-0 * oblX2 x 4 - 1 * (1 - oblX0 x 4))) =
                (det24 x * det24 x) * (1 - oblX0 x 4) := by ring
            rw [this]; exact mul_pos hd2 (sub_pos.mpr hlt)
          exact h1)
    · refine ⟨1, Or.inl (by rw [he3, hc4, hc1]; linarith [hz24]), ?_⟩
      rw [he3, he2, hc2, hc3, hc4]
      rw [hdet_b _ 0 1 0 (by module), hdet_d1 _ 0 1 0 (by module)]
      rcases eq_or_lt_of_le ha4 with heq | hlt
      · exact Or.inr ⟨by rw [heq]; ring, Or.inl (by
          have h1 : 0 < (-det24 x) * 1 * (det24 x * (1 * nC x)) := by
            have : (-det24 x) * 1 * (det24 x * (1 * nC x)) = (det24 x * det24 x) * (-nC x) := by ring
            rw [this]; exact mul_pos hd2 (neg_pos.mpr hnC_neg)
          exact h1)⟩
      · exact Or.inl (by
          have h1 : 0 < (-det24 x) * 1 * (det24 x * (-0 * oblX2 x 4 - 1 * (1 - oblX0 x 4))) := by
            have : (-det24 x) * 1 * (det24 x * (-0 * oblX2 x 4 - 1 * (1 - oblX0 x 4))) =
                (det24 x * det24 x) * (1 - oblX0 x 4) := by ring
            rw [this]; exact mul_pos hd2 (sub_pos.mpr hlt)
          exact h1)
  · rcases hj with rfl | rfl
    · refine ⟨1, Or.inl (by rw [hc4, hc1]; linarith [hz24]), Or.inl ?_⟩
      rw [he4, he2, hc2, hc3, hc4, hc5]
      rw [hdet_b _ (oblX0 x 5) (oblX2 x 5 - 1) (oblX6 x 5)
        (by rw [show x 5 - x 2 = (x 5 - x 1) - (x 2 - x 1) by abel, hrep 5]; module)]
      have h1 : (-det24 x) * 1 * (det24 x * (-oblX0 x 5 * oblX2 x 4 - (oblX2 x 5 - 1) * (1 - oblX0 x 4))) =
          (det24 x * det24 x) * (oblX0 x 5 * oblX2 x 4 - (1 - oblX0 x 4) * (1 - oblX2 x 5)) := by ring
      rw [h1]; exact mul_pos hd2 (sub_pos.mpr hrow)
    · refine ⟨1, Or.inl (by rw [he4, hc5, hc1]; linarith [hz54]), Or.inl ?_⟩
      rw [he4, he2, hc2, hc3, hc4, hc5]
      rw [hdet_b _ (oblX0 x 5) (oblX2 x 5 - 1) (oblX6 x 5)
        (by rw [show x 5 - x 2 = (x 5 - x 1) - (x 2 - x 1) by abel, hrep 5]; module)]
      have h1 : (-det24 x) * 1 * (det24 x * (-oblX0 x 5 * oblX2 x 4 - (oblX2 x 5 - 1) * (1 - oblX0 x 4))) =
          (det24 x * det24 x) * (oblX0 x 5 * oblX2 x 4 - (1 - oblX0 x 4) * (1 - oblX2 x 5)) := by ring
      rw [h1]; exact mul_pos hd2 (sub_pos.mpr hrow)
  · rcases hj with rfl | rfl
    · refine ⟨1, Or.inl (by rw [hc5, hc1]; linarith [hz54]), Or.inl ?_⟩
      rw [he5, he2, hc0, hc2, hc3, hc5]
      rw [hdet_b _ (1 - oblX0 x 5) (-oblX2 x 5) (-oblX6 x 5)
        (by rw [show x 0 - x 5 = (x 0 - x 1) - (x 5 - x 1) by abel, hrep 5]; module)]
      have h1 : (-det24 x) * 1 * (det24 x * (-(1 - oblX0 x 5) * oblX2 x 4 - -oblX2 x 5 * (1 - oblX0 x 4))) =
          (det24 x * det24 x) * (-nC x) := by dsimp [nC]; ring
      rw [h1]; exact mul_pos hd2 (neg_pos.mpr hnC_neg)
    · refine ⟨1, Or.inl (by rw [he5, hc0, hc1]; linarith [hz04]), Or.inl ?_⟩
      rw [he5, he2, hc0, hc2, hc3, hc5]
      rw [hdet_b _ (1 - oblX0 x 5) (-oblX2 x 5) (-oblX6 x 5)
        (by rw [show x 0 - x 5 = (x 0 - x 1) - (x 5 - x 1) by abel, hrep 5]; module)]
      have h1 : (-det24 x) * 1 * (det24 x * (-(1 - oblX0 x 5) * oblX2 x 4 - -oblX2 x 5 * (1 - oblX0 x 4))) =
          (det24 x * det24 x) * (-nC x) := by dsimp [nC]; ring
      rw [h1]; exact mul_pos hd2 (neg_pos.mpr hnC_neg)

theorem isRupert_of_E0416 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hC : CbarIn x) (ha4 : oblX0 x 4 ≤ 1) (hnc : F.f 3 (x 6) < F.f 3 (x 1))
    (htau : F.f 6 (x 0) < F.f 6 (x 4))
    (hrow : (1 - oblX0 x 4) * (1 - oblX2 x 5) < oblX0 x 5 * oblX2 x 4)
    (hz : max 0 (max ⟪x 2 - x 1, x 4 - x 0⟫ ⟪x 5 - x 1, x 4 - x 0⟫) < ⟪x 4 - x 1, x 4 - x 0⟫ ∧
          ⟪x 4 - x 1, x 4 - x 0⟫ < ⟪x 6 - x 1, x 4 - x 0⟫) :
    IsRupert (univ.image x) :=
  splitAny24_isRupert F (splitAny24_E0416 F hC ha4 hnc htau hrow hz)

/-! ### Part 4: `e05q4_bound` -/

theorem e05q4_bound {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (ha5 : 1 < oblX0 x 5) (hL : 0 < Lam5 x) (h346 : F.f 8 (x 5) < F.f 8 (x 0))
    (hU : ¬ LexAny F) :
    max ⟪x 5, x 5 - x 0⟫ ⟪x 6, x 5 - x 0⟫ ≤ min ⟪x 2, x 5 - x 0⟫ ⟪x 3, x 5 - x 0⟫ := by
  by_contra hcon
  push Not at hcon
  have T := type24OfFac F
  have ha3 : 0 < oblX0 x 3 := T.X0_pos (v := 3) (by decide)
  have hc5 : 0 < oblX6 x 5 := T.X6_pos (v := 5) (by decide)
  let w05 : ℝ³ := x 5 - x 0
  let d1 : ℝ³ := x 1 - x 0
  have hw05_ne : w05 ≠ 0 := sub_ne_zero.mpr fun h => absurd (T.inj h) (by decide)
  -- Facings at `(w05, d1, 0)` on `U = {6, 7}`, `Dn = {0, 1, 2, 3, 4, 5, 8}`:
  have hf0 : ⟪F.N 0, w05⟫ < 0 := by
    dsimp [w05]; rw [← F.hN 0 (x 5) (x 0), F.zero 0 0 (by decide), sub_zero]
    exact F.neg 0 5 (by decide)
  have hf1 : ⟪F.N 1, w05⟫ < 0 := by
    dsimp [w05]; rw [← F.hN 1 (x 5) (x 0), F.zero 1 0 (by decide), sub_zero]
    exact F.neg 1 5 (by decide)
  have hf2_0 : ⟪F.N 2, w05⟫ = 0 := by
    dsimp [w05]; rw [← F.hN 2 (x 5) (x 0), F.zero 2 5 (by decide), F.zero 2 0 (by decide), sub_self]
  have hd2_1 : 0 < -⟪F.N 2, d1⟫ := by
    dsimp [d1]; rw [← F.hN 2 (x 1) (x 0), F.zero 2 0 (by decide), sub_zero]
    linarith [F.neg 2 1 (by decide)]
  have hf3_0 : ⟪F.N 3, w05⟫ = 0 := by
    dsimp [w05]; rw [← F.hN 3 (x 5) (x 0), F.zero 3 5 (by decide), F.zero 3 0 (by decide), sub_self]
  have hd3_1 : 0 < -⟪F.N 3, d1⟫ := by
    dsimp [d1]; rw [← F.hN 3 (x 1) (x 0), F.zero 3 0 (by decide), sub_zero]
    linarith [F.neg 3 1 (by decide)]
  have hf4 : ⟪F.N 4, w05⟫ < 0 := by
    dsimp [w05]; rw [← F.hN 4 (x 5) (x 0), F.zero 4 0 (by decide), sub_zero]
    exact F.neg 4 5 (by decide)
  have hf5 : ⟪F.N 5, w05⟫ < 0 := by
    dsimp [w05]; rw [← F.hN 5 (x 5) (x 0)]
    have ev5 := fac_eval F 5 5
    rw [F.zero 5 1 (by decide), F.zero 5 2 (by decide), F.zero 5 6 (by decide)] at ev5
    rw [ev5]
    have hmul : (oblX0 x 5 - 1) * F.f 5 (x 0) =
        (0 + oblX0 x 5 * (F.f 5 (x 0) - 0) + oblX2 x 5 * (0 - 0) + oblX6 x 5 * (0 - 0)) -
          F.f 5 (x 0) := by ring
    rw [← hmul]
    exact mul_neg_of_pos_of_neg (sub_pos.mpr ha5) (F.neg 5 0 (by decide))
  have hf6 : 0 < ⟪F.N 6, w05⟫ := by
    dsimp [w05]; rw [← F.hN 6 (x 5) (x 0), F.zero 6 5 (by decide), zero_sub]
    linarith [F.neg 6 0 (by decide)]
  have hf7_0 : F.f 7 (x 0) = (1 + omega3 x) * F.f 7 (x 1) := by
    have ev7_3 := fac_eval F 7 3
    rw [F.zero 7 3 (by decide), F.zero 7 2 (by decide), F.zero 7 6 (by decide)] at ev7_3
    have e3 := eq3 F
    have h7_id : oblX0 x 3 * (F.f 7 (x 0) - (1 + omega3 x) * F.f 7 (x 1)) = 0 := by
      linear_combination -ev7_3 + F.f 7 (x 1) * e3
    exact sub_eq_zero.mp ((mul_eq_zero.mp h7_id).resolve_left ha3.ne')
  have hf7 : 0 < ⟪F.N 7, w05⟫ := by
    dsimp [w05]; rw [← F.hN 7 (x 5) (x 0)]
    have ev7_5 := fac_eval F 7 5
    rw [F.zero 7 2 (by decide), F.zero 7 6 (by decide), hf7_0] at ev7_5
    have hdiff : F.f 7 (x 5) - (1 + omega3 x) * F.f 7 (x 1) = (-F.f 7 (x 1)) * Lam5 x := by
      dsimp [Lam5]; rw [ev7_5]; ring
    rw [hf7_0, hdiff]
    exact mul_pos (by linarith [F.neg 7 1 (by decide)]) hL
  have hf8 : ⟪F.N 8, w05⟫ < 0 := by
    dsimp [w05]; rw [← F.hN 8 (x 5) (x 0)]; linarith
  -- Front diagonal `[x 2, x 3]` in front of `[x 5, x 6]` along `w05 = x 5 - x 0`:
  have hfront : FrontDiag (x 2) (x 3) (x 5) (x 6) w05 := by
    have h75_ineq : 0 < oblX0 x 5 * (1 + omega3 x) - (1 + omega5 x) * oblX6 x 5 := by
      have ev75 := fac_eval F 7 5
      rw [F.zero 7 2 (by decide), F.zero 7 6 (by decide), hf7_0] at ev75
      have e5 := eq5 F
      have h71 : 0 < -F.f 7 (x 1) := by linarith [F.neg 7 1 (by decide)]
      have hprod : (-F.f 7 (x 1)) * ((1 + omega5 x) * oblX6 x 5 - oblX0 x 5 * (1 + omega3 x)) =
          F.f 7 (x 5) := by
        rw [ev75]; linear_combination F.f 7 (x 1) * e5
      have h75 : F.f 7 (x 5) < 0 := F.neg 7 5 (by decide)
      nlinarith
    set num_l : ℝ := oblX0 x 5 + oblX2 x 5 + oblX6 x 5 - 1
    set num_gam : ℝ := oblX0 x 3 * (oblX0 x 5 * (1 + omega3 x) - (1 + omega5 x) * oblX6 x 5)
    set num_m : ℝ := (oblX0 x 5 - 1) * oblX6 x 3 - (oblX0 x 3 - 1) * oblX6 x 5 +
        oblX2 x 5 * oblX6 x 3 - oblX2 x 3 * oblX6 x 5
    set detM : ℝ := oblX0 x 3 * oblX2 x 5 - oblX0 x 5 * oblX2 x 3 + oblX0 x 5 -
        oblX2 x 3 * oblX6 x 5 + oblX2 x 3 + oblX2 x 5 * oblX6 x 3 + oblX6 x 5 - 1
    have hnl_pos : 0 < num_l := by
      have e5 := eq5 F
      have h5 : num_l = (1 + omega5 x) * oblX6 x 5 := by dsimp [num_l]; linarith
      rw [h5]
      have h1om5 : 0 < 1 + omega5 x := by
        -- `1 + omega5 x = F.f 2 (x 6) / F.f 2 (x 1) > 0`
        have ev25 := fac_eval F 2 5
        rw [F.zero 2 5 (by decide), F.zero 2 0 (by decide), F.zero 2 2 (by decide)] at ev25
        have h21 : 0 < -F.f 2 (x 1) := by linarith [F.neg 2 1 (by decide)]
        have h26 : 0 < -F.f 2 (x 6) := by linarith [F.neg 2 6 (by decide)]
        have hprod' : (-F.f 2 (x 1)) * (1 + omega5 x) = -F.f 2 (x 6) := by
          have hb5_eq' : oblX2 x 5 = 1 - oblX0 x 5 + omega5 x * oblX6 x 5 := by linarith [e5]
          rw [hb5_eq'] at ev25
          have hmul : oblX6 x 5 * ((-F.f 2 (x 1)) * (1 + omega5 x) - (-F.f 2 (x 6))) = 0 := by
            linarith [ev25]
          exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left hc5.ne')
        nlinarith
      exact mul_pos h1om5 hc5
    have hngam_pos : 0 < num_gam := mul_pos ha3 h75_ineq
    have hb3_eq : oblX2 x 3 = 1 - oblX6 x 3 + omega3 x * oblX0 x 3 := by linarith [eq3 F]
    have hb5_eq : oblX2 x 5 = 1 - oblX0 x 5 + omega5 x * oblX6 x 5 := by linarith [eq5 F]
    have h_ea : num_l * oblX0 x 3 - (detM - num_m + num_gam) * oblX0 x 5 + num_gam = 0 := by
      dsimp [num_l, num_gam, num_m, detM]
      rw [hb3_eq, hb5_eq]; ring
    have h_eb : (detM - num_l) + num_l * oblX2 x 3 - (detM - num_m + num_gam) * oblX2 x 5 = 0 := by
      dsimp [num_l, num_gam, num_m, detM]
      rw [hb3_eq, hb5_eq]; ring
    have h_ec : num_l * oblX6 x 3 - (detM - num_m + num_gam) * oblX6 x 5 - num_m = 0 := by
      dsimp [num_l, num_gam, num_m, detM]
      rw [hb3_eq, hb5_eq]; ring
    have hvec : (detM - num_l) • (x 2 - x 1) + num_l • (x 3 - x 1) =
        (detM - num_m + num_gam) • (x 5 - x 1) + num_m • (x 6 - x 1) - num_gam • (x 0 - x 1) := by
      have hrep3 : x 3 - x 1 = oblX0 x 3 • (x 0 - x 1) + oblX2 x 3 • (x 2 - x 1) +
          oblX6 x 3 • (x 6 - x 1) := by rw [T.rep 3]; abel
      have hrep5 : x 5 - x 1 = oblX0 x 5 • (x 0 - x 1) + oblX2 x 5 • (x 2 - x 1) +
          oblX6 x 5 • (x 6 - x 1) := by rw [T.rep 5]; abel
      rw [hrep3, hrep5]
      calc (detM - num_l) • (x 2 - x 1) + num_l • (oblX0 x 3 • (x 0 - x 1) +
            oblX2 x 3 • (x 2 - x 1) + oblX6 x 3 • (x 6 - x 1))
          = (num_l * oblX0 x 3) • (x 0 - x 1) + ((detM - num_l) + num_l * oblX2 x 3) • (x 2 - x 1) +
            (num_l * oblX6 x 3) • (x 6 - x 1) := by
              simp only [smul_add, smul_smul, add_smul]; abel
        _ = ((detM - num_m + num_gam) * oblX0 x 5 - num_gam) • (x 0 - x 1) +
            ((detM - num_m + num_gam) * oblX2 x 5) • (x 2 - x 1) +
            ((detM - num_m + num_gam) * oblX6 x 5 + num_m) • (x 6 - x 1) := by
              rw [show num_l * oblX0 x 3 = (detM - num_m + num_gam) * oblX0 x 5 - num_gam by linarith [h_ea],
                show (detM - num_l) + num_l * oblX2 x 3 = (detM - num_m + num_gam) * oblX2 x 5 by linarith [h_eb],
                show num_l * oblX6 x 3 = (detM - num_m + num_gam) * oblX6 x 5 + num_m by linarith [h_ec]]
        _ = (detM - num_m + num_gam) • (oblX0 x 5 • (x 0 - x 1) + oblX2 x 5 • (x 2 - x 1) +
              oblX6 x 5 • (x 6 - x 1)) + num_m • (x 6 - x 1) - num_gam • (x 0 - x 1) := by
              simp only [smul_add, smul_sub, smul_smul, add_smul, sub_smul]; abel
    have hnm_pos : 0 < num_m := by
      have hi := congrArg (fun v => ⟪F.N 6, v⟫) hvec
      simp only [inner_add_right, inner_sub_right, inner_smul_right, ← F.hN 6 _ (x 1),
        F.zero 6 2 (by decide), F.zero 6 3 (by decide), F.zero 6 5 (by decide)] at hi
      have h60 : F.f 6 (x 0) < 0 := F.neg 6 0 (by decide)
      have h66 : F.f 6 (x 6) < 0 := F.neg 6 6 (by decide)
      have h6_eq : num_m * F.f 6 (x 6) = num_gam * F.f 6 (x 0) := by linarith
      have hneg : num_m * F.f 6 (x 6) < 0 := by rw [h6_eq]; exact mul_neg_of_pos_of_neg hngam_pos h60
      by_contra h; push Not at h
      have : 0 ≤ num_m * F.f 6 (x 6) := mul_nonneg_of_nonpos_of_nonpos h h66.le
      linarith
    have hn1l_pos : 0 < detM - num_l := by
      have hi := congrArg (fun v => ⟪F.N 3, v⟫) hvec
      simp only [inner_add_right, inner_sub_right, inner_smul_right, ← F.hN 3 _ (x 1),
        F.zero 3 0 (by decide), F.zero 3 3 (by decide), F.zero 3 5 (by decide)] at hi
      have h32 : F.f 3 (x 2) < 0 := F.neg 3 2 (by decide)
      have h36 : F.f 3 (x 6) < 0 := F.neg 3 6 (by decide)
      have h3_eq : (detM - num_l) * F.f 3 (x 2) = num_m * F.f 3 (x 6) := by linarith
      have hneg : (detM - num_l) * F.f 3 (x 2) < 0 := by
        rw [h3_eq]; exact mul_neg_of_pos_of_neg hnm_pos h36
      by_contra h; push Not at h
      have : 0 ≤ (detM - num_l) * F.f 3 (x 2) := mul_nonneg_of_nonpos_of_nonpos h h32.le
      linarith
    have hdet_pos : 0 < detM := by linarith
    have hn1m_pos : 0 < detM - num_m := by
      have e3 := eq3 F; have e5 := eq5 F
      have hid : detM - num_m = oblX0 x 3 * Lam5 x := by
        dsimp [detM, num_m, Lam5]
        rw [hb3_eq, hb5_eq]; ring
      rw [hid]
      exact mul_pos ha3 hL
    set l : ℝ := num_l / detM
    set m : ℝ := num_m / detM
    set γ : ℝ := num_gam / detM
    refine ⟨l, m, γ, (div_pos hnl_pos hdet_pos).le, (by rw [div_le_one hdet_pos]; linarith),
      (div_pos hnm_pos hdet_pos).le, (by rw [div_le_one hdet_pos]; linarith),
      div_pos hngam_pos hdet_pos, ?_⟩
    have hvec_div : (1 - l) • (x 2 - x 1) + l • (x 3 - x 1) =
        (1 - m + γ) • (x 5 - x 1) + m • (x 6 - x 1) - γ • (x 0 - x 1) := by
      have h1 : (1 - l) = (detM - num_l) / detM := by dsimp [l]; field_simp [hdet_pos.ne']
      have h2 : (1 - m + γ) = (detM - num_m + num_gam) / detM := by
        dsimp [m, γ]; field_simp [hdet_pos.ne']
      rw [h1, h2]
      dsimp [l, m, γ]
      simp only [div_eq_inv_mul, ← smul_smul]
      rw [← smul_add, ← smul_add, ← smul_sub, hvec]
    have hshift : (x 2 + l • (x 3 - x 2)) - (x 5 + m • (x 6 - x 5)) =
        ((1 - l) • (x 2 - x 1) + l • (x 3 - x 1)) - ((1 - m) • (x 5 - x 1) + m • (x 6 - x 1)) := by
      simp only [sub_smul, one_smul, smul_sub]; abel
    rw [hshift, hvec_div]
    dsimp [w05]
    rw [show (x 5 - x 0) = (x 5 - x 1) - (x 0 - x 1) by abel]
    simp only [add_smul, sub_smul, smul_sub]; abel
  have hnb := FrontDiag.not_back hfront hw05_ne
  let c : ZMod 4 → Fin 7 := ![5, 2, 6, 3]
  apply hU
  refine ⟨4, inferInstance, c, {6, 7}, {0, 1, 2, 3, 4, 5, 8}, w05, d1, 0, by decide,
    (by intro i j h; fin_cases i <;> fin_cases j <;> first | rfl | exact absurd h (by decide)),
    (by unfold S0xCycUD; decide), ?_, ?_, ?_⟩
  · intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl
    · exact Or.inl hf6
    · exact Or.inl hf7
  · intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl (by linarith)
    · exact Or.inl (by linarith)
    · exact Or.inr ⟨by rw [hf2_0, neg_zero], Or.inl hd2_1⟩
    · exact Or.inr ⟨by rw [hf3_0, neg_zero], Or.inl hd3_1⟩
    · exact Or.inl (by linarith)
    · exact Or.inl (by linarith)
    · exact Or.inl (by linarith)
  · have hc0 : c 0 = 5 := rfl
    have hc1 : c 1 = 2 := rfl
    have hc2 : c 2 = 6 := rfl
    have hc3 : c 3 = 3 := rfl
    refine robUniLex_four_of_mixed ?_ ?_
    · by_cases h52 : ⟪x 5, w05⟫ < ⟪x 2, w05⟫
      · exact ⟨(0, 1), by decide, Or.inl (by rw [hc0, hc1]; exact sub_pos.mpr h52)⟩
      · by_cases h53 : ⟪x 5, w05⟫ < ⟪x 3, w05⟫
        · exact ⟨(0, 3), by decide, Or.inl (by rw [hc0, hc3]; exact sub_pos.mpr h53)⟩
        · by_cases h62 : ⟪x 6, w05⟫ < ⟪x 2, w05⟫
          · exact ⟨(2, 1), by decide, Or.inl (by rw [hc2, hc1]; exact sub_pos.mpr h62)⟩
          · refine ⟨(2, 3), by decide, Or.inl (by
              rw [hc2, hc3]; refine sub_pos.mpr ?_; by_contra h63; apply hnb
              exact max_le (le_min (not_lt.mp h52) (not_lt.mp h62)) (le_min (not_lt.mp h53) (not_lt.mp h63)))⟩
    · by_cases h25 : ⟪x 2, w05⟫ < ⟪x 5, w05⟫
      · exact ⟨(0, 1), by decide, Or.inl (by rw [hc0, hc1]; exact sub_pos.mpr h25)⟩
      · by_cases h26 : ⟪x 2, w05⟫ < ⟪x 6, w05⟫
        · exact ⟨(2, 1), by decide, Or.inl (by rw [hc2, hc1]; exact sub_pos.mpr h26)⟩
        · by_cases h35 : ⟪x 3, w05⟫ < ⟪x 5, w05⟫
          · exact ⟨(0, 3), by decide, Or.inl (by rw [hc0, hc3]; exact sub_pos.mpr h35)⟩
          · refine ⟨(2, 3), by decide, Or.inl (by
              rw [hc2, hc3]; refine sub_pos.mpr ?_; by_contra h36
              have hle : max ⟪x 5, w05⟫ ⟪x 6, w05⟫ ≤ min ⟪x 2, w05⟫ ⟪x 3, w05⟫ :=
                max_le (le_min (not_lt.mp h25) (not_lt.mp h35)) (le_min (not_lt.mp h26) (not_lt.mp h36))
              exact absurd (lt_of_lt_of_le hcon hle) (lt_irrefl _))⟩

end Minimality.T24.A8
