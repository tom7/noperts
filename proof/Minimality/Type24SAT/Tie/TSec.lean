module

public import Minimality.Type24SAT.Tie.TSem
public import Minimality.Type24SAT.Geo.Row
public import Minimality.Type21SAT.Lex2

@[expose] public section

/-!
# L24T, T4: the lex sign `lexS`, `lex_z3`, and the clause families 34 and 35

* `lexSW a b` is the encoder's `lexS`; `lexS_sound`: it is the two-level lex sign (`LexSg`) of the reals of `a` and `b`.
* `lex_z3`: lex signs of pairs whose components both sum to 0 satisfy the three-term zsum.
* Family 34 (row3 at the tie view `u'`), `chk34`, `fam34_sound`.
* Family 35 (Z0 rows, RH rows, KA rows, exclusions of RH and KA), `chk35`, `fam35_sound`.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
open scoped RealInnerProductSpace Topology
open Classical Filter

namespace Minimality.H24T.SAT
open Minimality Minimality.H21 Minimality.H24.SAT Minimality.H29.SAT

/-! ### The lex sign -/

/-- The two literals of `t` say exactly "`(a, b)` is lex positive" and "`(a, b)` is lex negative"
(`= Lex2Sg (evalW ρ t.1) (evalW ρ t.2) a b` of `TPar`). -/
def LexSg (ρ : W → Bool) (t : S3W) (a b : ℝ) : Prop :=
  (evalW ρ t.1 = true ↔ h21b_LP a b) ∧ (evalW ρ t.2 = true ↔ h21b_LP (-a) (-b))

/-- The encoder's `lexS(a, b) = (a.p or (z and b.p), a.q or (z and b.q))`, `z = (a = 0)`. -/
def lexSW (a b : S3W) : S3W :=
  (orW a.1 (andW (andW a.1.neg a.2.neg) b.1), orW a.2 (andW (andW a.1.neg a.2.neg) b.2))

/-- **`lexS_sound`.** -/
theorem lexS_sound {ρ : W → Bool} (hP : ProperW ρ) (hG : GateOKW ρ) {a b : S3W} {ra rb : ℝ}
    (ha : SgW ρ a ra) (hb : SgW ρ b rb) : LexSg ρ (lexSW a b) ra rb := by
  obtain ⟨a1, a2⟩ := ha
  obtain ⟨b1, b2⟩ := hb
  simp only [LexSg, lexSW, h21b_LP, evalW_orW hP hG, evalW_andW hP hG, evalW_neg, Bool.or_eq_true,
    Bool.and_eq_true, Bool.not_eq_true', ← Bool.not_eq_true, a1, a2, b1, b2]
  rcases lt_trichotomy ra 0 with h | h | h <;> rcases lt_trichotomy rb 0 with h' | h' | h'
  all_goals first
    | (subst h; subst h'; simp)
    | (subst h; simp [h'])
    | (subst h'; simp [h, not_lt.mpr h.le])
    | simp [h, h', h.ne, h.ne', not_lt.mpr h.le, not_lt.mpr h'.le]

theorem LexSg_neg {ρ : W → Bool} {t : S3W} {a b : ℝ} (h : LexSg ρ t a b) : LexSg ρ (negSW t) (-a) (-b) := by
  refine ⟨h.2, ?_⟩
  simpa [negSW] using h.1

theorem LexSg_congr {ρ : W → Bool} {t : S3W} {a b a' b' : ℝ} (h : LexSg ρ t a b) (ha : a = a') (hb : b = b') :
    LexSg ρ t a' b' := by subst ha; subst hb; exact h

theorem lp_excl {a b : ℝ} (h : h21b_LP a b) : ¬ h21b_LP (-a) (-b) := by
  unfold h21b_LP at *
  rintro h'
  rcases h with h | ⟨h1, h2⟩ <;> rcases h' with h' | ⟨h3, h4⟩ <;> linarith

theorem lp_none {a b : ℝ} (h1 : ¬ h21b_LP a b) (h2 : ¬ h21b_LP (-a) (-b)) : a = 0 ∧ b = 0 := by
  unfold h21b_LP at *
  rcases lt_trichotomy a 0 with ha | ha | ha
  · exact absurd (Or.inl (by linarith)) h2
  · subst ha
    rcases lt_trichotomy b 0 with hb | hb | hb
    · exact absurd (Or.inr ⟨by simp, by linarith⟩) h2
    · exact ⟨rfl, hb⟩
    · exact absurd (Or.inr ⟨rfl, hb⟩) h1
  · exact absurd (Or.inl ha) h1

/-- The lex sign is the real sign of `a + eps * b` for all small `eps > 0`. -/
theorem lex_eps {ρ : W → Bool} {t : S3W} {a b : ℝ} (h : LexSg ρ t a b) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), SgW ρ t (a + ε * b) := by
  by_cases h1 : h21b_LP a b
  · filter_upwards [eventually_pos_affine h1] with ε hε
    exact ⟨⟨fun _ => hε, fun _ => h.1.mpr h1⟩,
      ⟨fun e => absurd (h.2.mp e) (lp_excl h1), fun e => absurd e (not_lt.mpr hε.le)⟩⟩
  · by_cases h2 : h21b_LP (-a) (-b)
    · filter_upwards [eventually_pos_affine h2] with ε hε
      have hn : a + ε * b < 0 := by linarith
      exact ⟨⟨fun e => absurd (h.1.mp e) h1, fun e => absurd e (not_lt.mpr hn.le)⟩,
        ⟨fun _ => hn, fun _ => h.2.mpr h2⟩⟩
    · obtain ⟨ha, hb⟩ := lp_none h1 h2
      refine Eventually.of_forall fun ε => ?_
      have e0 : a + ε * b = 0 := by rw [ha, hb]; ring
      refine ⟨⟨fun e => absurd (h.1.mp e) h1, fun e => ?_⟩, ⟨fun e => absurd (h.2.mp e) h2, fun e => ?_⟩⟩
      · rw [e0] at e; exact absurd e (lt_irrefl _)
      · rw [e0] at e; exact absurd e (lt_irrefl _)

/-- **`lex_z3`.**  If three lex signs have first components and second components each summing to 0, the
three-term zsum clauses hold (`z4W` with the zero sign as fourth term). -/
theorem lex_z3 {ρ : W → Bool} (hP : ProperW ρ) {t1 t2 t3 : S3W} {a1 b1 a2 b2 a3 b3 : ℝ}
    (h1 : LexSg ρ t1 a1 b1) (h2 : LexSg ρ t2 a2 b2) (h3 : LexSg ρ t3 a3 b3)
    (ha : a1 + a2 + a3 = 0) (hb : b1 + b2 + b3 = 0) :
    ∀ cl ∈ z4W t1 t2 t3 zeroSW, HoldsW ρ cl := by
  have ev := (lex_eps h1).and ((lex_eps h2).and (lex_eps h3))
  obtain ⟨ε, e1, e2, e3⟩ := ev.exists
  exact z4W_sound e1 e2 e3 (SgW_zero hP) (by linear_combination ha + ε * hb)

/-! ### Family 34: row3 at the tie view -/

/-- `kS(side, x)`: `x` for side `+` (`sd = 1`), else its negation. -/
def kSW (sd : Nat) (x : S3W) : S3W := if sd = 1 then x else negSW x

theorem kSW_sg {ρ : W → Bool} {x : S3W} {r : ℝ} (sd : Nat) (h : SgW ρ x r) : SgW ρ (kSW sd x) (sdR sd * r) := by
  unfold kSW sdR
  by_cases hs : sd = 1
  · simpa [hs] using h
  · simpa [hs] using h.neg

/-- The encoder's `Dp(q)` for the leaf `(t, f, side)`: the constant `side` for `q = f`, else `lexS(P(f,q), side RH(t,f,q))`. -/
def DpW (t f sd q : Nat) : S3W :=
  if q = f then (if sd = 1 then (ltrueW, lfalseW) else (lfalseW, ltrueW))
  else lexSW (liftS (PS t f q)) (kSW sd (RS t f q))

/-- `ordD(a,b)`: `Dp` of the edge `a < b`, or its negation for `b < a`. -/
def ordDW (t f sd a b : Nat) : S3W := if a < b then DpW t f sd (EI a b) else negSW (DpW t f sd (EI b a))

/-- The vector whose inner product with `D_q` is the second order depth `R(f,q)` (`Rtie`). -/
noncomputable def Gv (g : Geo) (t f : Nat) : ℝ³ := if Z0 g t f then g.dv f else dplus g t f

theorem Rtie_eq (g : Geo) (t f q : Nat) : Rtie g t f q = ⟪Gv g t f, g.dv q⟫ := by
  unfold Rtie Gv
  by_cases hz : Z0 g t f <;> simp [hz, Rr]

theorem dv_EI (g : Geo) {a b : Nat} (ha : a < 7) (hb : b < 7) (hab : a < b) :
    g.dv (EI a b) = g.x a - g.x b := by
  have h := vv_EI g hab hb
  have h21 := EI_lt21 a ha b hb hab
  simpa [Geo.vv, h21] using h

theorem dv_ne {g : Geo} (hG : GeoOK g) {f : Nat} (hf : f < 21) : g.dv f ≠ 0 := by
  have := hG.hv f hf
  simpa [Geo.vv, hf] using this

theorem Rff_pos {g : Geo} {t f : Nat} (hv : g.dv f ≠ 0) : 0 < Rtie g t f f := by
  unfold Rtie
  by_cases hz : Z0 g t f
  · simp only [hz, ite_true]; exact real_inner_self_pos.mpr hv
  · simp only [hz, ite_false]; rw [R_self]; exact wf_pos hz

theorem evalW_ltrueW (g : Geo) : evalW (rhoW g) ltrueW = true := by
  simp [evalW, ltrueW, rhoW, rho]
theorem evalW_lfalseW (g : Geo) : evalW (rhoW g) lfalseW = false := by
  simp [evalW, lfalseW, rhoW, rho]

/-- `Dp(q)` is the lex sign of `(P(f,q), side R(f,q) / R(f,f))`. -/
theorem DpW_lex {g : Geo} {t f : Nat} (hv : g.dv f ≠ 0) (sd q : Nat) :
    LexSg (rhoW g) (DpW t f sd q) (Pp g t f q) ((Rtie g t f f)⁻¹ * (sdR sd * Rtie g t f q)) := by
  have hR := Rff_pos (t := t) hv
  by_cases hq : q = f
  · subst hq
    have e1 : Pp g t q q = 0 := P_self g t q
    have e2 : (Rtie g t q q)⁻¹ * (sdR sd * Rtie g t q q) = sdR sd := by field_simp
    rw [e1, e2]
    unfold DpW sdR
    by_cases hs : sd = 1
    · simp [LexSg, hs, h21b_LP, evalW_ltrueW g, evalW_lfalseW g]
    · simp [LexSg, hs, h21b_LP, evalW_ltrueW g, evalW_lfalseW g]
  · unfold DpW
    rw [ite_eq_right hq]
    have hb := (kSW_sg sd (SgW_RH g t f q)).scale (c := (Rtie g t f f)⁻¹) (inv_pos.mpr hR)
    exact lexS_sound (rhoW_proper g) (rhoW_gateOK g) (SgW_P g t f q) hb

theorem ordDW_lex {g : Geo} {t f : Nat} (hv : g.dv f ≠ 0) (sd : Nat) {a b : Nat} (ha : a < 7) (hb : b < 7)
    (hab : a ≠ b) :
    LexSg (rhoW g) (ordDW t f sd a b) ⟪wf g t f, g.x a - g.x b⟫
      ((Rtie g t f f)⁻¹ * (sdR sd * ⟪Gv g t f, g.x a - g.x b⟫)) := by
  unfold ordDW
  by_cases h : a < b
  · rw [ite_eq_left h]
    have := DpW_lex (t := t) hv sd (EI a b)
    rw [P_eq, Rtie_eq g t f (EI a b), dv_EI g ha hb h] at this
    exact this
  · rw [ite_eq_right h]
    have hba : b < a := by omega
    have := LexSg_neg (DpW_lex (t := t) hv sd (EI b a))
    rw [P_eq, Rtie_eq g t f (EI b a), dv_EI g hb ha hba] at this
    refine LexSg_congr this ?_ ?_
    · rw [inner_sub_right, inner_sub_right]; ring
    · rw [inner_sub_right, inner_sub_right]; ring

/-- Family 34, real form: the three-term zsum of `ordD` at the tie view. -/
theorem fam34_core {g : Geo} (hG : GeoOK g) {t f : Nat} (hf : f < 21) (sd : Nat) {a b c : Nat}
    (ha : a < 7) (hb : b < 7) (hc : c < 7) (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a) :
    ∀ cl ∈ z4W (ordDW t f sd a b) (ordDW t f sd b c) (ordDW t f sd c a) zeroSW, HoldsW (rhoW g) cl := by
  have hv := dv_ne hG hf
  refine lex_z3 (rhoW_proper g) (ordDW_lex hv sd ha hb hab) (ordDW_lex hv sd hb hc hbc)
    (ordDW_lex hv sd hc ha hca) ?_ ?_
  · simp only [inner_sub_right]; ring
  · simp only [inner_sub_right]; ring

/-- `cl` covers one of the clauses of `S`. -/
def anyCovW (cl : List LitW) (S : List (List LitW)) : Bool := S.any (coversW cl)

theorem anyCovW_holds {ρ : W → Bool} (hP : ProperW ρ) {cl : List LitW} {S : List (List LitW)}
    (h : anyCovW cl S = true) (hS : ∀ s ∈ S, HoldsW ρ s) : HoldsW ρ cl := by
  obtain ⟨s, hs, hc⟩ := List.any_eq_true.mp h
  exact HoldsW.of_covers hP hc (hS s hs)

/-- The checker of a family 34 row (tag `34 t f sd a b c`; `sd = 1` for side `+`). -/
def chk34 (t f sd a b c : Nat) (cl : List LitW) : Bool :=
  decide (f < 21 ∧ (sd = 0 ∨ sd = 1) ∧ a < b ∧ b < c ∧ c < 7) &&
    anyCovW cl (z4W (ordDW t f sd a b) (ordDW t f sd b c) (ordDW t f sd c a) zeroSW)

/-- **Family 34 soundness.** -/
theorem fam34_sound {g : Geo} (hG : GeoOK g) {t f sd a b c : Nat} {cl : List LitW}
    (h : chk34 t f sd a b c cl = true) : HoldsW (rhoW g) cl := by
  unfold chk34 at h
  rw [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hf, -, hab, hbc, hc⟩, hcov⟩ := h
  exact anyCovW_holds (rhoW_proper g) hcov
    (fam34_core hG hf sd (by omega) (by omega) hc (by omega) (by omega) (by omega))

/-! ### Family 35: second order axioms -/

theorem HoldsW_append {ρ : W → Bool} {a b : List LitW} : HoldsW ρ (a ++ b) ↔ HoldsW ρ a ∨ HoldsW ρ b := by
  unfold HoldsW
  constructor
  · rintro ⟨l, h, e⟩
    rcases List.mem_append.mp h with h | h
    · exact Or.inl ⟨l, h, e⟩
    · exact Or.inr ⟨l, h, e⟩
  · rintro (⟨l, h, e⟩ | ⟨l, h, e⟩)
    · exact ⟨l, List.mem_append.mpr (Or.inl h), e⟩
    · exact ⟨l, List.mem_append.mpr (Or.inr h), e⟩

theorem not_holds_append {ρ : W → Bool} {a b : List LitW} (h : ¬ HoldsW ρ (a ++ b)) :
    ¬ HoldsW ρ a ∧ ¬ HoldsW ρ b := by
  rw [HoldsW_append] at h; exact not_or.mp h

/-- `not [x = sg]` as literals (the encoder's `eqN`). -/
def eqNL (x : S3W) (sg : Int) : List LitW :=
  if 0 < sg then [x.1.neg] else if sg < 0 then [x.2.neg] else [x.1, x.2]

/-- The encoder's `force(b, x, sg)`: the clause(s) `b or [x = sg]`. -/
def forceL (b : List LitW) (x : S3W) (sg : Int) : List (List LitW) :=
  if 0 < sg then [b ++ [x.1]] else if sg < 0 then [b ++ [x.2]] else [b ++ [x.1.neg], b ++ [x.2.neg]]

theorem single_neg_false {ρ : W → Bool} {l : LitW} (hn : ¬ HoldsW ρ [l.neg]) : evalW ρ l = true := by
  by_contra e
  apply hn
  refine ⟨l.neg, by simp, ?_⟩
  rw [evalW_neg]; simpa using e

theorem pair_zero {ρ : W → Bool} {x : S3W} {r : ℝ} (h : SgW ρ x r) (hn : ¬ HoldsW ρ [x.1, x.2]) : r = 0 := by
  have e1 : evalW ρ x.1 ≠ true := fun e => hn ⟨x.1, by simp, e⟩
  have e2 : evalW ρ x.2 ≠ true := fun e => hn ⟨x.2, by simp, e⟩
  have a1 : ¬ 0 < r := fun hr => e1 (h.1.mpr hr)
  have a2 : ¬ r < 0 := fun hr => e2 (h.2.mpr hr)
  exact le_antisymm (not_lt.mp a1) (not_lt.mp a2)

theorem eqNL_sem {ρ : W → Bool} {x : S3W} {r : ℝ} (h : SgW ρ x r) (sg : Int)
    (hn : ¬ HoldsW ρ (eqNL x sg)) : (0 < sg → 0 < r) ∧ (sg < 0 → r < 0) ∧ (sg = 0 → r = 0) := by
  rcases lt_trichotomy sg 0 with hs | hs | hs
  · have : eqNL x sg = [x.2.neg] := by simp [eqNL, not_lt.mpr hs.le, hs]
    rw [this] at hn
    exact ⟨fun h' => absurd h' (not_lt.mpr hs.le), fun _ => h.2.mp (single_neg_false hn),
      fun h' => absurd h' hs.ne⟩
  · subst hs
    have : eqNL x 0 = [x.1, x.2] := by simp [eqNL]
    rw [this] at hn
    exact ⟨fun h' => absurd h' (lt_irrefl _), fun h' => absurd h' (lt_irrefl _), fun _ => pair_zero h hn⟩
  · have : eqNL x sg = [x.1.neg] := by simp [eqNL, hs]
    rw [this] at hn
    exact ⟨fun _ => h.1.mp (single_neg_false hn), fun h' => absurd h' (not_lt.mpr hs.le),
      fun h' => absurd h' hs.ne'⟩

theorem forceL_sound {ρ : W → Bool} {b : List LitW} {x : S3W} {r : ℝ} (sg : Int) (hx : SgW ρ x r)
    (hb : ¬ HoldsW ρ b → (0 < sg → 0 < r) ∧ (sg < 0 → r < 0) ∧ (sg = 0 → r = 0)) :
    ∀ c ∈ forceL b x sg, HoldsW ρ c := by
  intro c hc
  by_cases hh : HoldsW ρ b
  · have hb' : ∀ l, HoldsW ρ (b ++ [l]) := fun l => HoldsW_append.mpr (Or.inl hh)
    simp only [forceL] at hc
    split_ifs at hc <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    · subst hc; exact hb' _
    · subst hc; exact hb' _
    · rcases hc with rfl | rfl <;> exact hb' _
  · obtain ⟨p1, p2, p3⟩ := hb hh
    have mk : ∀ l, evalW ρ l = true → HoldsW ρ (b ++ [l]) := fun l e =>
      HoldsW_append.mpr (Or.inr ⟨l, by simp, e⟩)
    simp only [forceL] at hc
    split_ifs at hc with h1 h2 <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    · subst hc; exact mk _ (hx.1.mpr (p1 h1))
    · subst hc; exact mk _ (hx.2.mpr (p2 h2))
    · have h0 : sg = 0 := by omega
      have hr := p3 h0
      rcases hc with rfl | rfl
      · refine mk _ ?_
        rw [evalW_neg]
        have : evalW ρ x.1 ≠ true := fun e => absurd (hx.1.mp e) (by rw [hr]; exact lt_irrefl _)
        simpa using this
      · refine mk _ ?_
        rw [evalW_neg]
        have : evalW ρ x.2 ≠ true := fun e => absurd (hx.2.mp e) (by rw [hr]; exact lt_irrefl _)
        simpa using this

/-- The sign algebra of the master identity: `B W = A R`, `W > 0`, `A` of sign `s1`, `B` of sign `s2`,
so `R` has the sign `s1 s2`. -/
theorem sign_core {W A R B : ℝ} (hW : 0 < W) (e : B * W = A * R) {s1 s2 : Int}
    (hs1 : s1 = 1 ∨ s1 = -1) (hs2 : s2 = -1 ∨ s2 = 0 ∨ s2 = 1)
    (hA1 : 0 < s1 → 0 < A) (hA2 : s1 < 0 → A < 0)
    (hB1 : 0 < s2 → 0 < B) (hB2 : s2 < 0 → B < 0) (hB3 : s2 = 0 → B = 0) :
    (0 < s1 * s2 → 0 < R) ∧ (s1 * s2 < 0 → R < 0) ∧ (s1 * s2 = 0 → R = 0) := by
  have z0 : A ≠ 0 → B = 0 → R = 0 := by
    intro hA hB
    rw [hB] at e
    have : A * R = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_left hA
  rcases hs1 with rfl | rfl <;> rcases hs2 with rfl | rfl | rfl
  · -- A > 0, B < 0
    have hA := hA1 (by norm_num); have hB := hB2 (by norm_num)
    refine ⟨by norm_num, fun _ => ?_, by norm_num⟩
    by_contra hR; have h' : 0 ≤ R := not_lt.mp hR
    nlinarith [mul_nonneg hA.le h', mul_neg_of_neg_of_pos hB hW]
  · have hA := hA1 (by norm_num); have hB := hB3 rfl
    exact ⟨by norm_num, by norm_num, fun _ => z0 hA.ne' hB⟩
  · have hA := hA1 (by norm_num); have hB := hB1 (by norm_num)
    refine ⟨fun _ => ?_, by norm_num, by norm_num⟩
    by_contra hR; have h' : R ≤ 0 := not_lt.mp hR
    nlinarith [mul_pos hB hW, mul_nonneg hA.le (neg_nonneg.mpr h')]
  · have hA := hA2 (by norm_num); have hB := hB2 (by norm_num)
    refine ⟨fun _ => ?_, by norm_num, by norm_num⟩
    by_contra hR; have h' : R ≤ 0 := not_lt.mp hR
    nlinarith [mul_nonneg_of_nonpos_of_nonpos hA.le h', mul_neg_of_neg_of_pos hB hW]
  · have hA := hA2 (by norm_num); have hB := hB3 rfl
    exact ⟨by norm_num, by norm_num, fun _ => z0 hA.ne hB⟩
  · have hA := hA2 (by norm_num); have hB := hB1 (by norm_num)
    refine ⟨by norm_num, fun _ => ?_, by norm_num⟩
    by_contra hR; have h' : 0 ≤ R := not_lt.mp hR
    nlinarith [mul_pos hB hW, mul_nonneg (neg_nonneg.mpr hA.le) h']

/-- Family 35 kind 0: `Z0 -> P(f,b) = 0`, as the clauses `{-z, -P.p}`, `{-z, -P.q}`. -/
theorem z0_rows (g : Geo) (t f b : Nat) :
    ∀ c ∈ [[(Z0L t f).neg, (liftS (PS t f b)).1.neg], [(Z0L t f).neg, (liftS (PS t f b)).2.neg]],
      HoldsW (rhoW g) c := by
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  by_cases hz : Z0 g t f
  · have h0 := P_of_Z0 hz b
    have hP := SgW_P g t f b
    rw [h0] at hP
    rcases hc with rfl | rfl
    · refine ⟨(liftS (PS t f b)).1.neg, by simp, ?_⟩
      rw [evalW_neg]
      have : ¬ evalW (rhoW g) (liftS (PS t f b)).1 = true := fun e => lt_irrefl _ (hP.1.mp e)
      simpa using this
    · refine ⟨(liftS (PS t f b)).2.neg, by simp, ?_⟩
      rw [evalW_neg]
      have : ¬ evalW (rhoW g) (liftS (PS t f b)).2 = true := fun e => lt_irrefl _ (hP.2.mp e)
      simpa using this
  · have hl : evalW (rhoW g) (Z0L t f).neg = true := by
      rw [evalW_neg]
      have : ¬ evalW (rhoW g) (Z0L t f) = true := fun e => hz ((evalW_Z0L g t f).mp e)
      simpa using this
    rcases hc with rfl | rfl
    · exact ⟨_, by simp, hl⟩
    · exact ⟨_, by simp, hl⟩

/-- Family 35 kind 1 (RH rows). -/
theorem rh_rows {g : Geo} (t f x b : Nat) {s1 s2 : Int} (hs1 : s1 = 1 ∨ s1 = -1)
    (hs2 : s2 = -1 ∨ s2 = 0 ∨ s2 = 1) :
    ∀ c ∈ forceL ([(liftS (PS t f x)).1, (liftS (PS t f x)).2] ++ eqNL (liftS (PS t b f)) s1 ++
      eqNL (liftS (PS t b x)) s2) (RS t f x) (s1 * s2), HoldsW (rhoW g) c := by
  refine forceL_sound (s1 * s2) (SgW_RH g t f x) fun hn => ?_
  obtain ⟨h12, h3⟩ := not_holds_append hn
  obtain ⟨h1, h2⟩ := not_holds_append h12
  have e0 := pair_zero (SgW_P g t f x) h1
  have sA := eqNL_sem (SgW_P g t b f) s1 h2
  have sB := eqNL_sem (SgW_P g t b x) s2 h3
  have hz : ¬ Z0 g t f := by
    intro hz
    have h0 : Pp g t b f = 0 := by rw [P_swap, P_of_Z0 hz b]; simp
    rcases hs1 with rfl | rfl
    · exact (sA.1 (by norm_num)).ne' h0
    · exact (sA.2.1 (by norm_num)).ne h0
  have hm := master_P g t f b x
  rw [e0] at hm
  have hW := wf_pos hz
  have key := sign_core (R := Rr g t f x) hW (by linarith) hs1 hs2 sA.1 sA.2.1 sB.1 sB.2.1 sB.2.2
  simpa [Rtie, hz] using key

/-- Family 35 kind 2 (KA rows). -/
theorem ka_rows {g : Geo} (hG : GeoOK g) {t f s b : Nat} (hf : f < 21) (hb : b < 21) {view : Nat} {k : Int}
    (hl : lsOK t s view k = true) {s1 s2 : Int} (hs1 : s1 = 1 ∨ s1 = -1)
    (hs2 : s2 = -1 ∨ s2 = 0 ∨ s2 = 1) :
    ∀ c ∈ forceL ([(liftS (lsS view k f)).1, (liftS (lsS view k f)).2] ++ eqNL (liftS (PS t f b)) s1 ++
      eqNL (liftS (lsS view k b)) s2) (KS t f s) (s1 * s2), HoldsW (rhoW g) c := by
  refine forceL_sound (s1 * s2) (SgW_KA g t f s) fun hn => ?_
  obtain ⟨h12, h3⟩ := not_holds_append hn
  obtain ⟨h1, h2⟩ := not_holds_append h12
  have e0 := pair_zero (ls_sound hG.hF hG.hO hl hf) h1
  have sA := eqNL_sem (SgW_P g t f b) s1 h2
  have sB := eqNL_sem (ls_sound hG.hF hG.hO hl hb) s2 h3
  have hz : ¬ Z0 g t f := by
    intro hz
    have h0 : Pp g t f b = 0 := P_of_Z0 hz b
    rcases hs1 with rfl | rfl
    · exact (sA.1 (by norm_num)).ne' h0
    · exact (sA.2.1 (by norm_num)).ne h0
  have hm := master_K g t f s b
  rw [e0] at hm
  have hW := wf_pos hz
  have key := sign_core (R := Kk g t f s) hW (by linarith) hs1 hs2 sA.1 sA.2.1 sB.1 sB.2.1 sB.2.2
  simpa [Ktie, hz] using key

/-- The clauses (up to the dumper's dropping of constant literals) of a family 35 row
`35 kind t f x b s1 s2`; `view, k` are the `LS t x view k` line of the vmap (kind 2 only). -/
def cands35 (kind t f x b : Nat) (s1 s2 : Int) (view : Nat) (k : Int) : List (List LitW) :=
  if kind = 0 then
    [[(Z0L t f).neg, (liftS (PS t f b)).1.neg], [(Z0L t f).neg, (liftS (PS t f b)).2.neg]]
  else if kind = 1 then
    forceL ([(liftS (PS t f x)).1, (liftS (PS t f x)).2] ++ eqNL (liftS (PS t b f)) s1 ++
      eqNL (liftS (PS t b x)) s2) (RS t f x) (s1 * s2)
  else if kind = 2 then
    forceL ([(liftS (lsS view k f)).1, (liftS (lsS view k f)).2] ++ eqNL (liftS (PS t f b)) s1 ++
      eqNL (liftS (lsS view k b)) s2) (KS t f x) (s1 * s2)
  else if kind = 3 then [[(false, W.rh t f x true), (false, W.rh t f x false)]]
  else [[(false, W.ka t f x true), (false, W.ka t f x false)]]

/-- Side conditions of a family 35 row. -/
def ok35 (kind t f x b : Nat) (s1 s2 : Int) (view : Nat) (k : Int) : Bool :=
  if kind = 0 then true
  else if kind = 1 then (s1 == 1 || s1 == -1) && (s2 == -1 || s2 == 0 || s2 == 1)
  else if kind = 2 then decide (f < 21 ∧ b < 21) && (s1 == 1 || s1 == -1) &&
    (s2 == -1 || s2 == 0 || s2 == 1) && lsOK t x view k
  else decide (kind = 3 ∨ kind = 4)

/-- The checker of a family 35 row. -/
def chk35 (kind t f x b : Nat) (s1 s2 : Int) (view : Nat) (k : Int) (cl : List LitW) : Bool :=
  ok35 kind t f x b s1 s2 view k && anyCovW cl (cands35 kind t f x b s1 s2 view k)

/-- **Family 35 soundness** (all kinds, both `Z0` branches). -/
theorem fam35_sound {g : Geo} (hG : GeoOK g) {kind t f x b : Nat} {s1 s2 : Int} {view : Nat} {k : Int}
    {cl : List LitW} (h : chk35 kind t f x b s1 s2 view k cl = true) : HoldsW (rhoW g) cl := by
  unfold chk35 at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hok, hcov⟩ := h
  refine anyCovW_holds (rhoW_proper g) hcov fun c hc => ?_
  unfold cands35 at hc
  unfold ok35 at hok
  by_cases k0 : kind = 0
  · rw [ite_eq_left k0] at hc
    exact z0_rows g t f b c hc
  rw [ite_eq_right k0] at hc hok
  by_cases k1 : kind = 1
  · rw [ite_eq_left k1] at hc hok
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hok
    exact rh_rows t f x b hok.1 (by rcases hok.2 with (h | h) | h <;> simp [h]) c hc
  rw [ite_eq_right k1] at hc hok
  by_cases k2 : kind = 2
  · rw [ite_eq_left k2] at hc hok
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hok
    obtain ⟨⟨⟨⟨hf, hb⟩, hs1⟩, hs2⟩, hl⟩ := hok
    exact ka_rows hG hf hb hl hs1 (by rcases hs2 with (h | h) | h <;> simp [h]) c hc
  rw [ite_eq_right k2] at hc hok
  by_cases k3 : kind = 3
  · rw [ite_eq_left k3] at hc
    simp only [List.mem_singleton] at hc
    subst hc; exact rh_excl g t f x
  · rw [ite_eq_right k3] at hc
    have k4 : kind = 4 := by
      simp only [decide_eq_true_eq] at hok
      omega
    simp only [List.mem_singleton] at hc
    subst hc; exact ka_excl g t f x

/-! ### The facing sign `Fp(s)` at the tie view (for the tie rules, T6) -/

/-- `Fp(s) = lexS(-lineS(t,s,f), side KA(t,f,s))`, `lineS(t,s,f) = k T(view, f)`. -/
def FpW (t f sd view : Nat) (k : Int) (s : Nat) : S3W :=
  lexSW (negSW (liftS (lsS view k f))) (kSW sd (KS t f s))

/-- `Fp(s)` is the lex sign of `(-L(s,f), sigma K(s))`, with the `Z0` convention `K = 1` (`Ktie`). -/
theorem FpW_lex {g : Geo} (hG : GeoOK g) {t s view : Nat} {k : Int} (hl : lsOK t s view k = true)
    {f : Nat} (hf : f < 21) (sd : Nat) :
    LexSg (rhoW g) (FpW t f sd view k s) (-Ls g t s f) (sdR sd * Ktie g t f s) :=
  lexS_sound (rhoW_proper g) (rhoW_gateOK g) (ls_sound hG.hF hG.hO hl hf).neg (kSW_sg sd (SgW_KA g t f s))

end Minimality.H24T.SAT
