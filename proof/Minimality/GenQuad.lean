module

public import Minimality.GenericLeaves
public import Minimality.SameView

@[expose] public section

/-!
# Quadruple-clause form of `RobUniLex`

From nopert229 out/bottleneck/p29/sat/k1c/GEN29-REVIEW.md (R1). On a `k`-rim at a view `b`, every alternating
quadruple of rim vertices has two crossing diagonals; the diagonal in front along `b` (`FrontOf`, a sign check of four
`det3` values: `frontOf_of_det`) can never carry a double peak (`lexClause_of_frontOf`), and the other one fails only
on the metric set `M_Q` (`lexClause_of_notM`). `clauses_of_sorted` (all `k`) and `clauses_four` / `clauses_five` /
`clauses_six` turn one clause per (4-subset, pairing) into `RobUniLex`; `lexAny_of_clauses` is the generic leaf.
-/

set_option autoImplicit false

open scoped RealInnerProductSpace
open Minimality Minimality.LexCell Minimality.H21

namespace Minimality.GenQuad

/-- Segment `p q` lies in front of segment `r s` along `b`. -/
def FrontOf (p q r s b : ℝ³) : Prop :=
  ∃ lam mu eta : ℝ, 0 ≤ lam ∧ lam ≤ 1 ∧ 0 ≤ mu ∧ mu ≤ 1 ∧ 0 < eta ∧
    lam • p + (1 - lam) • q = mu • r + (1 - mu) • s + eta • b

theorem frontOf_iff_frontDiag (p q r s b : ℝ³) :
    FrontOf p q r s b ↔ FrontDiag q p s r b := by
  constructor
  · rintro ⟨lam, mu, eta, hl0, hl1, hm0, hm1, he, hv⟩
    refine ⟨lam, mu, eta, hl0, hl1, hm0, hm1, he, ?_⟩
    rw [← sub_eq_iff_eq_add'] at hv
    rw [← hv]; module
  · rintro ⟨lam, mu, eta, hl0, hl1, hm0, hm1, he, hv⟩
    refine ⟨lam, mu, eta, hl0, hl1, hm0, hm1, he, ?_⟩
    have : lam • p + (1 - lam) • q - (mu • r + (1 - mu) • s) = eta • b := by
      rw [← hv]; module
    rw [← this]; abel

/-- Obtuse frame guard: at an obtuse corner (`⟪e0, e2⟫ ≤ 0`, `⟪e0, e6⟫ ≤ 0`), a view with frame
coordinates of sign pattern `(-, +, +)` has `⟪e0, A0 • e0 + A2 • e2 + A6 • e6⟫ ≤ 0`. -/
theorem obtuse_frame {e0 e2 e6 : ℝ³} {A0 A2 A6 : ℝ} (h02 : ⟪e0, e2⟫ ≤ 0) (h06 : ⟪e0, e6⟫ ≤ 0)
    (hA0 : A0 ≤ 0) (hA2 : 0 ≤ A2) (hA6 : 0 ≤ A6) :
    ⟪e0, A0 • e0 + A2 • e2 + A6 • e6⟫ ≤ 0 := by
  simp only [inner_add_right, real_inner_smul_right]
  have := real_inner_self_nonneg (x := e0)
  nlinarith [mul_nonpos_of_nonneg_of_nonpos hA2 h02, mul_nonpos_of_nonneg_of_nonpos hA6 h06,
    mul_nonpos_of_nonpos_of_nonneg hA0 this]

/-- The RobUniLex clause of one alternating quadruple: peaks `r s`, valleys `p q`. -/
def LexClause (p q r s b d1 d2 : ℝ³) : Prop :=
  LexLt3 (⟪r, b⟫, ⟪r, d1⟫, ⟪r, d2⟫) (⟪p, b⟫, ⟪p, d1⟫, ⟪p, d2⟫) ∨
  LexLt3 (⟪s, b⟫, ⟪s, d1⟫, ⟪s, d2⟫) (⟪p, b⟫, ⟪p, d1⟫, ⟪p, d2⟫) ∨
  LexLt3 (⟪r, b⟫, ⟪r, d1⟫, ⟪r, d2⟫) (⟪q, b⟫, ⟪q, d1⟫, ⟪q, d2⟫) ∨
  LexLt3 (⟪s, b⟫, ⟪s, d1⟫, ⟪s, d2⟫) (⟪q, b⟫, ⟪q, d1⟫, ⟪q, d2⟫)

/-- First-level form of the clause (the metric region `¬ M`). -/
theorem lexClause_of_notM {p q r s b d1 d2 : ℝ³}
    (h : ¬ (⟪p, b⟫ ≤ ⟪r, b⟫ ∧ ⟪p, b⟫ ≤ ⟪s, b⟫ ∧ ⟪q, b⟫ ≤ ⟪r, b⟫ ∧ ⟪q, b⟫ ≤ ⟪s, b⟫)) :
    LexClause p q r s b d1 d2 := by
  unfold LexClause LexLt3 LexPos3
  by_contra hn
  simp only [not_or] at hn
  apply h
  refine ⟨?_, ?_, ?_, ?_⟩
  · by_contra hc; push Not at hc; exact hn.1.1 (by linarith)
  · by_contra hc; push Not at hc; exact hn.2.1.1 (by linarith)
  · by_contra hc; push Not at hc; exact hn.2.2.1.1 (by linarith)
  · by_contra hc; push Not at hc; exact hn.2.2.2.1 (by linarith)

/-- A valley pair in front of the peak pair: the clause holds for every metric. -/
theorem lexClause_of_frontOf {p q r s b d1 d2 : ℝ³} (hb : b ≠ 0) (h : FrontOf p q r s b) :
    LexClause p q r s b d1 d2 := by
  obtain ⟨lam, mu, eta, hl0, hl1, hm0, hm1, he, hv⟩ := h
  apply lexClause_of_notM
  rintro ⟨h1, h2, h3, h4⟩
  have hbb : 0 < ⟪b, b⟫ := real_inner_self_pos.mpr hb
  have hz := congrArg (fun v => ⟪v, b⟫) hv
  simp only [inner_add_left, inner_smul_left, conj_trivial] at hz
  nlinarith [mul_pos he hbb, mul_nonneg hl0 hm0, mul_nonneg (sub_nonneg.2 hl1) hm0,
    mul_nonneg hl0 (sub_nonneg.2 hm1), mul_nonneg (sub_nonneg.2 hl1) (sub_nonneg.2 hm1)]

/-- **Quadruple form of RobUniLex**: it suffices to give each alternating quadruple's clause. -/
theorem robUniLex_of_clauses {k : ℕ} {p : ZMod k → ℝ³} {b d1 d2 : ℝ³}
    (h : ∀ (B : ZMod k) (b' c' d' : ℕ), 0 < b' → b' < c' → c' < d' → d' < k →
      LexClause (p (B + b')) (p (B + d')) (p B) (p (B + c')) b d1 d2) :
    RobUniLex (fun i => (⟪p i, b⟫, ⟪p i, d1⟫, ⟪p i, d2⟫)) := by
  intro B b' c' d' h1 h2 h3 h4
  rcases h B b' c' d' h1 h2 h3 h4 with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))

/-- Generic line-view leaf: cycle + lex facet signs + one clause per alternating quadruple. -/
theorem lexAny_of_clauses {m n : ℕ} {S : Fin m → Finset (Fin n)} {x : Fin n → ℝ³}
    (F : S0xFac m S x) {k : ℕ} [NeZero k] (hk : 4 ≤ k) {c : ZMod k → Fin n}
    (hc : Function.Injective c) {U Dn : Finset (Fin m)} (hcyc : S0xCycUD S c U Dn) (b d1 d2 : ℝ³)
    (hU : ∀ t ∈ U, LexPos3 ⟪F.N t, b⟫ ⟪F.N t, d1⟫ ⟪F.N t, d2⟫)
    (hD : ∀ t ∈ Dn, LexPos3 (-⟪F.N t, b⟫) (-⟪F.N t, d1⟫) (-⟪F.N t, d2⟫))
    (h : ∀ (B : ZMod k) (b' c' d' : ℕ), 0 < b' → b' < c' → c' < d' → d' < k →
      LexClause (x (c (B + b'))) (x (c (B + d'))) (x (c B)) (x (c (B + c'))) b d1 d2) :
    Minimality.Gen.LexAny F :=
  ⟨k, inferInstance, c, U, Dn, b, d1, d2, hk, hc, hcyc, hU, hD,
    robUniLex_of_clauses (p := fun i => x (c i)) h⟩

/-- Cramer identity in ℝ³ (makes `FrontOf` a sign check of four determinants). -/
theorem cramer3 (A C b w : ℝ³) :
    (Minimality.Split.det3 A C b) • w =
      (Minimality.Split.det3 w C b) • A + (Minimality.Split.det3 A w b) • C +
        (Minimality.Split.det3 A C w) • b := by
  ext i; fin_cases i <;> simp [Minimality.Split.det3] <;> ring



/-- Core of `frontOf_of_det`: Cramer coefficients as quotients. -/
theorem frontOf_of_cramer {p q r s b : ℝ³} (hΔ : Split.det3 (p - q) (r - s) b ≠ 0)
    (hl0 : 0 ≤ Split.det3 (s - q) (r - s) b / Split.det3 (p - q) (r - s) b)
    (hl1 : Split.det3 (s - q) (r - s) b / Split.det3 (p - q) (r - s) b ≤ 1)
    (hm0 : 0 ≤ -Split.det3 (p - q) (s - q) b / Split.det3 (p - q) (r - s) b)
    (hm1 : -Split.det3 (p - q) (s - q) b / Split.det3 (p - q) (r - s) b ≤ 1)
    (he : 0 < -Split.det3 (p - q) (r - s) (s - q) / Split.det3 (p - q) (r - s) b) :
    FrontOf p q r s b := by
  refine ⟨Split.det3 (s - q) (r - s) b / Split.det3 (p - q) (r - s) b,
    -Split.det3 (p - q) (s - q) b / Split.det3 (p - q) (r - s) b,
    -Split.det3 (p - q) (r - s) (s - q) / Split.det3 (p - q) (r - s) b, hl0, hl1, hm0, hm1, he, ?_⟩
  have hc := cramer3 (p - q) (r - s) b (s - q)
  have hw : s - q = (Split.det3 (s - q) (r - s) b / Split.det3 (p - q) (r - s) b) • (p - q) +
      (Split.det3 (p - q) (s - q) b / Split.det3 (p - q) (r - s) b) • (r - s) +
      (Split.det3 (p - q) (r - s) (s - q) / Split.det3 (p - q) (r - s) b) • b := by
    have := congrArg (fun v => (Split.det3 (p - q) (r - s) b)⁻¹ • v) hc
    simp only [smul_add, smul_smul] at this
    rw [inv_mul_cancel₀ hΔ, one_smul] at this
    simpa only [div_eq_inv_mul] using this
  simp only [neg_div]
  generalize Split.det3 (s - q) (r - s) b / Split.det3 (p - q) (r - s) b = X at hw ⊢
  generalize Split.det3 (p - q) (s - q) b / Split.det3 (p - q) (r - s) b = Y at hw ⊢
  generalize Split.det3 (p - q) (r - s) (s - q) / Split.det3 (p - q) (r - s) b = Z at hw ⊢
  linear_combination (norm := module) (-1 : ℝ) • hw

/-- Front pair `p q` over `r s` along `b`, from determinant signs (orientation `Δ > 0`). -/
theorem frontOf_of_det {p q r s b : ℝ³} (hΔ : 0 < Split.det3 (p - q) (r - s) b)
    (hl0 : 0 ≤ Split.det3 (s - q) (r - s) b) (hl1 : Split.det3 (s - q) (r - s) b ≤ Split.det3 (p - q) (r - s) b)
    (hm0 : 0 ≤ -Split.det3 (p - q) (s - q) b) (hm1 : -Split.det3 (p - q) (s - q) b ≤ Split.det3 (p - q) (r - s) b)
    (he : Split.det3 (p - q) (r - s) (s - q) < 0) : FrontOf p q r s b :=
  frontOf_of_cramer hΔ.ne' (div_nonneg hl0 hΔ.le) ((div_le_one hΔ).2 hl1)
    (div_nonneg hm0 hΔ.le) ((div_le_one hΔ).2 hm1) (div_pos (by linarith) hΔ)

/-- Mirror of `frontOf_of_det` for `Δ < 0`. -/
theorem frontOf_of_det_neg {p q r s b : ℝ³} (hΔ : Split.det3 (p - q) (r - s) b < 0)
    (hl0 : Split.det3 (s - q) (r - s) b ≤ 0) (hl1 : Split.det3 (p - q) (r - s) b ≤ Split.det3 (s - q) (r - s) b)
    (hm0 : -Split.det3 (p - q) (s - q) b ≤ 0) (hm1 : Split.det3 (p - q) (r - s) b ≤ -Split.det3 (p - q) (s - q) b)
    (he : 0 < Split.det3 (p - q) (r - s) (s - q)) : FrontOf p q r s b :=
  frontOf_of_cramer hΔ.ne (div_nonneg_of_nonpos hl0 hΔ.le) ((div_le_one_of_neg hΔ).2 hl1)
    (div_nonneg_of_nonpos hm0 hΔ.le) ((div_le_one_of_neg hΔ).2 hm1)
    (div_pos_of_neg_of_neg (by linarith) hΔ)

theorem lexClause_swap_left {p q r s b d1 d2 : ℝ³} :
    LexClause p q r s b d1 d2 ↔ LexClause q p r s b d1 d2 := by
  unfold LexClause; tauto

theorem lexClause_swap_right {p q r s b d1 d2 : ℝ³} :
    LexClause p q r s b d1 d2 ↔ LexClause p q s r b d1 d2 := by
  unfold LexClause; tauto

/-- **All `k`**: it suffices to give the clause of every increasing quadruple `i < j < l < m`
(values in `0..k-1`) for both pairings: `hA` has peaks `i, l` and valleys `j, m`; `hB` has
peaks `j, m` and valleys `i, l`. -/
theorem clauses_of_sorted {k : ℕ} [NeZero k] {p : ZMod k → ℝ³} {b d1 d2 : ℝ³}
    (hA : ∀ i j l m : ZMod k, i.val < j.val → j.val < l.val → l.val < m.val →
      LexClause (p j) (p m) (p i) (p l) b d1 d2)
    (hB : ∀ i j l m : ZMod k, i.val < j.val → j.val < l.val → l.val < m.val →
      LexClause (p i) (p l) (p j) (p m) b d1 d2) :
    ∀ (B : ZMod k) (b' c' d' : ℕ), 0 < b' → b' < c' → c' < d' → d' < k →
      LexClause (p (B + b')) (p (B + d')) (p B) (p (B + c')) b d1 d2 := by
  intro B b' c' d' h1 h2 h3 h4
  have hv : ∀ t : ℕ, t < k →
      ((B.val + t < k → (B + (t : ZMod k)).val = B.val + t) ∧
       (k ≤ B.val + t → (B + (t : ZMod k)).val = B.val + t - k)) := by
    intro t ht
    have h0 := ZMod.val_lt B
    have e : (B + (t : ZMod k)).val = (B.val + t) % k := by
      rw [ZMod.val_add, ZMod.val_natCast, Nat.mod_eq_of_lt ht]
    refine ⟨fun h => by rw [e, Nat.mod_eq_of_lt h], fun h => ?_⟩
    rw [e, Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]
  have hB0 := ZMod.val_lt B
  have e1 := hv b' (by omega)
  have e2 := hv c' (by omega)
  have e3 := hv d' (by omega)
  by_cases w1 : B.val + b' < k <;> by_cases w2 : B.val + c' < k <;>
    by_cases w3 : B.val + d' < k
  · exact hA B _ _ _ (by omega) (by omega) (by omega)
  · exact lexClause_swap_left.1 (hB (B + d') B (B + b') (B + c') (by omega) (by omega) (by omega))
  · omega
  · exact lexClause_swap_left.1 (lexClause_swap_right.1 (hA (B + c') (B + d') B (B + b')
      (by omega) (by omega) (by omega)))
  · omega
  · omega
  · omega
  · exact lexClause_swap_right.1 (hB (B + b') (B + c') (B + d') B (by omega) (by omega) (by omega))

/-- Reduction of increasing quadruples in `ZMod k` to natural-number ones. -/
theorem sorted_cases {k : ℕ} [NeZero k] (P : ZMod k → ZMod k → ZMod k → ZMod k → Prop)
    (h : ∀ a b c d : ℕ, a < b → b < c → c < d → d < k → P a b c d) :
    ∀ i j l m : ZMod k, i.val < j.val → j.val < l.val → l.val < m.val → P i j l m := by
  intro i j l m h1 h2 h3
  have := h i.val j.val l.val m.val h1 h2 h3 (ZMod.val_lt m)
  simpa only [ZMod.natCast_zmod_val] using this

/-- `k = 4`: `LexClause` for every alternating quadruple of a 4-cycle, in canonical form.
For each 4-subset `{i<j<l<m}` of `0..3` (written `ijlm`): `hAijlm` has valleys `j, m` and peaks `i, l`
(`LexClause (p j) (p m) (p i) (p l)`); `hBijlm` has valleys `i, l` and peaks `j, m`
(`LexClause (p i) (p l) (p j) (p m)`). That is 1 subsets x 2 pairings = 2 hypotheses.
Conclusion: the hypothesis of `robUniLex_of_clauses` / `lexAny_of_clauses`. -/
theorem clauses_four {p : ZMod 4 → ℝ³} {b d1 d2 : ℝ³}
    (hA0123 : LexClause (p 1) (p 3) (p 0) (p 2) b d1 d2)
    (hB0123 : LexClause (p 0) (p 2) (p 1) (p 3) b d1 d2)
    : ∀ (B : ZMod 4) (b' c' d' : ℕ), 0 < b' → b' < c' → c' < d' → d' < 4 →
      LexClause (p (B + b')) (p (B + d')) (p B) (p (B + c')) b d1 d2 := by
  refine clauses_of_sorted ?_ ?_ <;>
  · refine sorted_cases _ ?_
    intro a b c d h1 h2 h3 h4
    have ha : a < 4 := by omega
    have hb : b < 4 := by omega
    have hc : c < 4 := by omega
    interval_cases a <;> interval_cases b <;> interval_cases c <;> interval_cases d <;>
      first | omega | (simpa using hA0123) | (simpa using hB0123)
/-- `k = 5`: `LexClause` for every alternating quadruple of a 5-cycle, in canonical form.
For each 4-subset `{i<j<l<m}` of `0..4` (written `ijlm`): `hAijlm` has valleys `j, m` and peaks `i, l`
(`LexClause (p j) (p m) (p i) (p l)`); `hBijlm` has valleys `i, l` and peaks `j, m`
(`LexClause (p i) (p l) (p j) (p m)`). That is 5 subsets x 2 pairings = 10 hypotheses.
Conclusion: the hypothesis of `robUniLex_of_clauses` / `lexAny_of_clauses`. -/
theorem clauses_five {p : ZMod 5 → ℝ³} {b d1 d2 : ℝ³}
    (hA0123 : LexClause (p 1) (p 3) (p 0) (p 2) b d1 d2)
    (hB0123 : LexClause (p 0) (p 2) (p 1) (p 3) b d1 d2)
    (hA0124 : LexClause (p 1) (p 4) (p 0) (p 2) b d1 d2)
    (hB0124 : LexClause (p 0) (p 2) (p 1) (p 4) b d1 d2)
    (hA0134 : LexClause (p 1) (p 4) (p 0) (p 3) b d1 d2)
    (hB0134 : LexClause (p 0) (p 3) (p 1) (p 4) b d1 d2)
    (hA0234 : LexClause (p 2) (p 4) (p 0) (p 3) b d1 d2)
    (hB0234 : LexClause (p 0) (p 3) (p 2) (p 4) b d1 d2)
    (hA1234 : LexClause (p 2) (p 4) (p 1) (p 3) b d1 d2)
    (hB1234 : LexClause (p 1) (p 3) (p 2) (p 4) b d1 d2)
    : ∀ (B : ZMod 5) (b' c' d' : ℕ), 0 < b' → b' < c' → c' < d' → d' < 5 →
      LexClause (p (B + b')) (p (B + d')) (p B) (p (B + c')) b d1 d2 := by
  refine clauses_of_sorted ?_ ?_ <;>
  · refine sorted_cases _ ?_
    intro a b c d h1 h2 h3 h4
    have ha : a < 5 := by omega
    have hb : b < 5 := by omega
    have hc : c < 5 := by omega
    interval_cases a <;> interval_cases b <;> interval_cases c <;> interval_cases d <;>
      first | omega | (simpa using hA0123) | (simpa using hB0123) | (simpa using hA0124) | (simpa using hB0124) | (simpa using hA0134) | (simpa using hB0134) | (simpa using hA0234) | (simpa using hB0234) | (simpa using hA1234) | (simpa using hB1234)
/-- `k = 6`: `LexClause` for every alternating quadruple of a 6-cycle, in canonical form.
For each 4-subset `{i<j<l<m}` of `0..5` (written `ijlm`): `hAijlm` has valleys `j, m` and peaks `i, l`
(`LexClause (p j) (p m) (p i) (p l)`); `hBijlm` has valleys `i, l` and peaks `j, m`
(`LexClause (p i) (p l) (p j) (p m)`). That is 15 subsets x 2 pairings = 30 hypotheses.
Conclusion: the hypothesis of `robUniLex_of_clauses` / `lexAny_of_clauses`. -/
theorem clauses_six {p : ZMod 6 → ℝ³} {b d1 d2 : ℝ³}
    (hA0123 : LexClause (p 1) (p 3) (p 0) (p 2) b d1 d2)
    (hB0123 : LexClause (p 0) (p 2) (p 1) (p 3) b d1 d2)
    (hA0124 : LexClause (p 1) (p 4) (p 0) (p 2) b d1 d2)
    (hB0124 : LexClause (p 0) (p 2) (p 1) (p 4) b d1 d2)
    (hA0125 : LexClause (p 1) (p 5) (p 0) (p 2) b d1 d2)
    (hB0125 : LexClause (p 0) (p 2) (p 1) (p 5) b d1 d2)
    (hA0134 : LexClause (p 1) (p 4) (p 0) (p 3) b d1 d2)
    (hB0134 : LexClause (p 0) (p 3) (p 1) (p 4) b d1 d2)
    (hA0135 : LexClause (p 1) (p 5) (p 0) (p 3) b d1 d2)
    (hB0135 : LexClause (p 0) (p 3) (p 1) (p 5) b d1 d2)
    (hA0145 : LexClause (p 1) (p 5) (p 0) (p 4) b d1 d2)
    (hB0145 : LexClause (p 0) (p 4) (p 1) (p 5) b d1 d2)
    (hA0234 : LexClause (p 2) (p 4) (p 0) (p 3) b d1 d2)
    (hB0234 : LexClause (p 0) (p 3) (p 2) (p 4) b d1 d2)
    (hA0235 : LexClause (p 2) (p 5) (p 0) (p 3) b d1 d2)
    (hB0235 : LexClause (p 0) (p 3) (p 2) (p 5) b d1 d2)
    (hA0245 : LexClause (p 2) (p 5) (p 0) (p 4) b d1 d2)
    (hB0245 : LexClause (p 0) (p 4) (p 2) (p 5) b d1 d2)
    (hA0345 : LexClause (p 3) (p 5) (p 0) (p 4) b d1 d2)
    (hB0345 : LexClause (p 0) (p 4) (p 3) (p 5) b d1 d2)
    (hA1234 : LexClause (p 2) (p 4) (p 1) (p 3) b d1 d2)
    (hB1234 : LexClause (p 1) (p 3) (p 2) (p 4) b d1 d2)
    (hA1235 : LexClause (p 2) (p 5) (p 1) (p 3) b d1 d2)
    (hB1235 : LexClause (p 1) (p 3) (p 2) (p 5) b d1 d2)
    (hA1245 : LexClause (p 2) (p 5) (p 1) (p 4) b d1 d2)
    (hB1245 : LexClause (p 1) (p 4) (p 2) (p 5) b d1 d2)
    (hA1345 : LexClause (p 3) (p 5) (p 1) (p 4) b d1 d2)
    (hB1345 : LexClause (p 1) (p 4) (p 3) (p 5) b d1 d2)
    (hA2345 : LexClause (p 3) (p 5) (p 2) (p 4) b d1 d2)
    (hB2345 : LexClause (p 2) (p 4) (p 3) (p 5) b d1 d2)
    : ∀ (B : ZMod 6) (b' c' d' : ℕ), 0 < b' → b' < c' → c' < d' → d' < 6 →
      LexClause (p (B + b')) (p (B + d')) (p B) (p (B + c')) b d1 d2 := by
  refine clauses_of_sorted ?_ ?_ <;>
  · refine sorted_cases _ ?_
    intro a b c d h1 h2 h3 h4
    have ha : a < 6 := by omega
    have hb : b < 6 := by omega
    have hc : c < 6 := by omega
    interval_cases a <;> interval_cases b <;> interval_cases c <;> interval_cases d <;>
      first | omega | (simpa using hA0123) | (simpa using hB0123) | (simpa using hA0124) | (simpa using hB0124) | (simpa using hA0125) | (simpa using hB0125) | (simpa using hA0134) | (simpa using hB0134) | (simpa using hA0135) | (simpa using hB0135) | (simpa using hA0145) | (simpa using hB0145) | (simpa using hA0234) | (simpa using hB0234) | (simpa using hA0235) | (simpa using hB0235) | (simpa using hA0245) | (simpa using hB0245) | (simpa using hA0345) | (simpa using hB0345) | (simpa using hA1234) | (simpa using hB1234) | (simpa using hA1235) | (simpa using hB1235) | (simpa using hA1245) | (simpa using hB1245) | (simpa using hA1345) | (simpa using hB1345) | (simpa using hA2345) | (simpa using hB2345)

/-- `p q` in front of `r s` along `b`, as sign conditions on four `det3` values (either orientation). -/
def FrontDet (p q r s b : ℝ³) : Prop :=
  (0 < Split.det3 (p - q) (r - s) b ∧ 0 ≤ Split.det3 (s - q) (r - s) b ∧
    Split.det3 (s - q) (r - s) b ≤ Split.det3 (p - q) (r - s) b ∧
    0 ≤ -Split.det3 (p - q) (s - q) b ∧ -Split.det3 (p - q) (s - q) b ≤ Split.det3 (p - q) (r - s) b ∧
    Split.det3 (p - q) (r - s) (s - q) < 0) ∨
  (Split.det3 (p - q) (r - s) b < 0 ∧ Split.det3 (s - q) (r - s) b ≤ 0 ∧
    Split.det3 (p - q) (r - s) b ≤ Split.det3 (s - q) (r - s) b ∧
    -Split.det3 (p - q) (s - q) b ≤ 0 ∧ Split.det3 (p - q) (r - s) b ≤ -Split.det3 (p - q) (s - q) b ∧
    0 < Split.det3 (p - q) (r - s) (s - q))

theorem FrontDet.frontOf {p q r s b : ℝ³} (h : FrontDet p q r s b) : FrontOf p q r s b := by
  rcases h with ⟨h1, h2, h3, h4, h5, h6⟩ | ⟨h1, h2, h3, h4, h5, h6⟩
  · exact frontOf_of_det h1 h2 h3 h4 h5 h6
  · exact frontOf_of_det_neg h1 h2 h3 h4 h5 h6

end Minimality.GenQuad
