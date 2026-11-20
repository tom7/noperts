module

public import Minimality.R012
public import Minimality.Q45Leaf
public import Minimality.CornerU
public import Minimality.DiagCross
public import Minimality.FaceChordFac
public import Minimality.SplitTie
public import Minimality.FiveRim
public import Minimality.Q45J0
public import Minimality.Q45Signs
public import Minimality.Q45Orient
public import Minimality.RimFromSigns
public import Minimality.Type24SAT.K24.Wire24
public import Minimality.Type24SAT.Facets24
public import Minimality.ZModLemmas
public import Minimality.Q45Tie

@[expose] public section

set_option autoImplicit true
set_option relaxedAutoImplicit true
open scoped RealInnerProductSpace Topology
open Filter Finset
open Minimality Minimality.H21 Minimality.FaceChord Minimality.T24.SAT Minimality.RimFromSigns
open Minimality.T24.Q45
open Minimality.T24.R012

namespace Minimality.T24.Q45

/-- Lexicographic depth order at the base view `b` with tilt `c` (ties at `b` broken by `c`). -/
def LexLt (b c a a' : ℝ³) : Prop :=
  ⟪a, b⟫ < ⟪a', b⟫ ∨ (⟪a, b⟫ = ⟪a', b⟫ ∧ ⟪a, c⟫ < ⟪a', c⟫)

theorem ev_lexLt (b c a a' : ℝ³) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), (⟪a, b + ε • c⟫ < ⟪a', b + ε • c⟫ ↔ LexLt b c a a') := by
  have e : ∀ ε : ℝ, ⟪a', b + ε • c⟫ - ⟪a, b + ε • c⟫ = (⟪a', b⟫ - ⟪a, b⟫) + ε * (⟪a', c⟫ - ⟪a, c⟫) := by
    intro ε; simp only [inner_add_right, real_inner_smul_right]; ring
  have e' : ∀ ε : ℝ, ⟪a, b + ε • c⟫ - ⟪a', b + ε • c⟫ = (⟪a, b⟫ - ⟪a', b⟫) + ε * (⟪a, c⟫ - ⟪a', c⟫) := by
    intro ε; simp only [inner_add_right, real_inner_smul_right]; ring
  rcases lt_trichotomy (⟪a, b⟫) (⟪a', b⟫) with h | h | h
  · have := eventually_pos_affine (A := ⟪a', b⟫ - ⟪a, b⟫) (B := ⟪a', c⟫ - ⟪a, c⟫) (Or.inl (by linarith))
    filter_upwards [this] with ε hε
    rw [← e] at hε
    exact ⟨fun _ => Or.inl h, fun _ => by linarith⟩
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε : (0 : ℝ) < ε := hε
    constructor
    · intro hlt
      right
      refine ⟨h, ?_⟩
      have := e' ε
      rw [h, sub_self, zero_add] at this
      have h2 : ε * (⟪a, c⟫ - ⟪a', c⟫) < 0 := by rw [← this]; linarith
      by_contra hn; push Not at hn
      nlinarith
    · rintro (h' | ⟨_, h'⟩)
      · linarith
      · have := e' ε
        rw [h, sub_self, zero_add] at this
        have : ε * (⟪a, c⟫ - ⟪a', c⟫) < 0 := mul_neg_of_pos_of_neg hε (by linarith)
        linarith [e' ε]
  · have := eventually_pos_affine (A := ⟪a, b⟫ - ⟪a', b⟫) (B := ⟪a, c⟫ - ⟪a', c⟫) (Or.inl (by linarith))
    filter_upwards [this] with ε hε
    rw [← e'] at hε
    constructor
    · intro hlt; linarith
    · rintro (h' | ⟨h', _⟩) <;> linarith

variable {p : ZMod 5 → ℝ³}

/-- Lexicographic version of the increasing alternation at corner `m`. -/
def LexAltIncr (p : ZMod 5 → ℝ³) (b c : ℝ³) (m : ZMod 5) : Prop :=
  LexLt b c (p (m - 1)) (p m) ∧ LexLt b c (p m) (p (m + 1)) ∧
  LexLt b c (subquad p m 1) (subquad p m 0) ∧ LexLt b c (subquad p m 1) (subquad p m 2) ∧
  LexLt b c (subquad p m 3) (subquad p m 0) ∧ LexLt b c (subquad p m 3) (subquad p m 2)

/-- Lexicographic version of the decreasing alternation at corner `m`. -/
def LexAltDecr (p : ZMod 5 → ℝ³) (b c : ℝ³) (m : ZMod 5) : Prop :=
  LexLt b c (p (m + 1)) (p m) ∧ LexLt b c (p m) (p (m - 1)) ∧
  LexLt b c (subquad p m 0) (subquad p m 1) ∧ LexLt b c (subquad p m 0) (subquad p m 3) ∧
  LexLt b c (subquad p m 2) (subquad p m 1) ∧ LexLt b c (subquad p m 2) (subquad p m 3)

theorem quadOdd_iff (q : ZMod 4 → ℝ³) (u : ℝ³) :
    QuadOddBelowEven q u ↔ (⟪q 1, u⟫ < ⟪q 0, u⟫ ∧ ⟪q 1, u⟫ < ⟪q 2, u⟫ ∧
      ⟪q 3, u⟫ < ⟪q 0, u⟫ ∧ ⟪q 3, u⟫ < ⟪q 2, u⟫) := by
  unfold QuadOddBelowEven
  rw [max_lt_iff, lt_min_iff, lt_min_iff]; tauto

theorem quadEven_iff (q : ZMod 4 → ℝ³) (u : ℝ³) :
    QuadEvenBelowOdd q u ↔ (⟪q 0, u⟫ < ⟪q 1, u⟫ ∧ ⟪q 0, u⟫ < ⟪q 3, u⟫ ∧
      ⟪q 2, u⟫ < ⟪q 1, u⟫ ∧ ⟪q 2, u⟫ < ⟪q 3, u⟫) := by
  unfold QuadEvenBelowOdd
  rw [max_lt_iff, lt_min_iff, lt_min_iff]; tauto

/-- Corner `m` with `ρ κ < 0`: the increasing alternation is ruled out by DiagCross, the decreasing one
eventually by the lexicographic depth condition. -/
theorem ev_rulesOut_neg (b c : ℝ³) (ρ : ℝ) (m : ZMod 5)
    (hcvx : ∀ᶠ ε in 𝓝[>] (0 : ℝ), StrictConvex5 p (b + ε • c) ρ)
    (hk : ρ * quadKappa (subquad p m) < 0) (hD : ¬ LexAltDecr p b c m) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), SubquadRulesOut p (b + ε • c) m := by
  have e1 := ev_lexLt b c (p (m + 1)) (p m)
  have e2 := ev_lexLt b c (p m) (p (m - 1))
  have e3 := ev_lexLt b c (subquad p m 0) (subquad p m 1)
  have e4 := ev_lexLt b c (subquad p m 0) (subquad p m 3)
  have e5 := ev_lexLt b c (subquad p m 2) (subquad p m 1)
  have e6 := ev_lexLt b c (subquad p m 2) (subquad p m 3)
  filter_upwards [hcvx, e1, e2, e3, e4, e5, e6] with ε hc h1 h2 h3 h4 h5 h6
  refine ⟨ruleOut_incr_of_kappa_neg p _ ρ hc m hk, ?_⟩
  rintro ⟨d1, d2⟩ hq
  rw [quadEven_iff] at hq
  exact hD ⟨h1.mp d1, h2.mp d2, h3.mp hq.1, h4.mp hq.2.1, h5.mp hq.2.2.1, h6.mp hq.2.2.2⟩

theorem ev_rulesOut_pos (b c : ℝ³) (ρ : ℝ) (m : ZMod 5)
    (hcvx : ∀ᶠ ε in 𝓝[>] (0 : ℝ), StrictConvex5 p (b + ε • c) ρ)
    (hk : 0 < ρ * quadKappa (subquad p m)) (hI : ¬ LexAltIncr p b c m) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), SubquadRulesOut p (b + ε • c) m := by
  have e1 := ev_lexLt b c (p (m - 1)) (p m)
  have e2 := ev_lexLt b c (p m) (p (m + 1))
  have e3 := ev_lexLt b c (subquad p m 1) (subquad p m 0)
  have e4 := ev_lexLt b c (subquad p m 1) (subquad p m 2)
  have e5 := ev_lexLt b c (subquad p m 3) (subquad p m 0)
  have e6 := ev_lexLt b c (subquad p m 3) (subquad p m 2)
  filter_upwards [hcvx, e1, e2, e3, e4, e5, e6] with ε hc h1 h2 h3 h4 h5 h6
  refine ⟨?_, ruleOut_decr_of_kappa_pos p _ ρ hc m hk⟩
  rintro ⟨d1, d2⟩ hq
  rw [quadOdd_iff] at hq
  exact hI ⟨h1.mp d1, h2.mp d2, h3.mp hq.1, h4.mp hq.2.1, h5.mp hq.2.2.1, h6.mp hq.2.2.2⟩

/-- Either-sign rule-out at corner `m`: `ρ κ` negative with no decreasing lex alternation, or positive with
no increasing one. -/
theorem ev_rulesOut (b c : ℝ³) (ρ : ℝ) (m : ZMod 5)
    (hcvx : ∀ᶠ ε in 𝓝[>] (0 : ℝ), StrictConvex5 p (b + ε • c) ρ)
    (h : (ρ * quadKappa (subquad p m) < 0 ∧ ¬ LexAltDecr p b c m) ∨
         (0 < ρ * quadKappa (subquad p m) ∧ ¬ LexAltIncr p b c m)) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), SubquadRulesOut p (b + ε • c) m := by
  rcases h with ⟨hk, hD⟩ | ⟨hk, hI⟩
  · exact ev_rulesOut_neg b c ρ m hcvx hk hD
  · exact ev_rulesOut_pos b c ρ m hcvx hk hI

/-- **K5 in lexicographic form**: strictly convex 5-rim, injective depths, every corner's sub-quad rules out
the alternation not forbidden by its DiagCross sign: eventually unimodal. -/
theorem ev_unimodal_five (b c : ℝ³) (ρ : ℝ)
    (hcvx : ∀ᶠ ε in 𝓝[>] (0 : ℝ), StrictConvex5 p (b + ε • c) ρ)
    (hinj : ∀ᶠ ε in 𝓝[>] (0 : ℝ), Function.Injective (fun i => ⟪p i, b + ε • c⟫))
    (h : ∀ m : ZMod 5, (ρ * quadKappa (subquad p m) < 0 ∧ ¬ LexAltDecr p b c m) ∨
         (0 < ρ * quadKappa (subquad p m) ∧ ¬ LexAltIncr p b c m)) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), Function.Injective (fun i => ⟪p i, b + ε • c⟫) ∧
      IsCyclicUnimodal (fun i => ⟪p i, b + ε • c⟫) := by
  have h0 := ev_rulesOut b c ρ 0 hcvx (h 0)
  have h1 := ev_rulesOut b c ρ 1 hcvx (h 1)
  have h2 := ev_rulesOut b c ρ 2 hcvx (h 2)
  have h3 := ev_rulesOut b c ρ 3 hcvx (h 3)
  have h4 := ev_rulesOut b c ρ 4 hcvx (h 4)
  filter_upwards [hcvx, hinj, h0, h1, h2, h3, h4] with ε hc hi r0 r1 r2 r3 r4
  refine ⟨hi, fiveRim_unimodal_of_subquads p _ ρ hc hi ?_⟩
  intro m
  rcases zmod5_cases m with rfl | rfl | rfl | rfl | rfl <;> assumption

variable {x : Fin 7 → ℝ³}
theorem ev_injective (b c : ℝ³) (p : ZMod 5 → ℝ³)
    (hgen : ∀ i j : ZMod 5, i ≠ j → ⟪p i - p j, b⟫ ≠ 0 ∨ ⟪p i - p j, c⟫ ≠ 0) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), Function.Injective (fun i => ⟪p i, b + ε • c⟫) := by
  have h : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ i j : ZMod 5, i ≠ j → ⟪p i - p j, b + ε • c⟫ ≠ 0 := by
    rw [Filter.eventually_all]; intro i
    rw [Filter.eventually_all]; intro j
    by_cases hij : i = j
    · exact Filter.Eventually.of_forall fun _ h => absurd hij h
    · have := eventually_ne_affine_or (hgen i j hij)
      filter_upwards [this] with ε hε _
      rw [inner_add_right, real_inner_smul_right]; exact hε
  filter_upwards [h] with ε hε i j hij
  by_contra hne
  apply hε i j hne
  rw [inner_sub_left]; simp only at hij; linarith

lemma cramer_facet_eq (F : S0xFac 9 s0x_S24 x)
    (t : Fin 9) (o a b c d : Fin 7)
    (ho : o ∈ s0x_S24 t) (ha : a ∈ s0x_S24 t) (hb : b ∈ s0x_S24 t) :
    det3 (x a - x o) (x b - x o) (x c - x o) * F.f t (x d) =
    det3 (x a - x o) (x b - x o) (x d - x o) * F.f t (x c) := by
  have zo : F.f t (x o) = 0 := F.zero t o ho
  have za : F.f t (x a) = 0 := F.zero t a ha
  have zb : F.f t (x b) = 0 := F.zero t b hb
  have ha' : ⟪F.N t, x a - x o⟫ = 0 := by rw [F.inner_sub t a o, za, zo, sub_self]
  have hb' : ⟪F.N t, x b - x o⟫ = 0 := by rw [F.inner_sub t b o, zb, zo, sub_self]
  have hc' : ⟪F.N t, x c - x o⟫ = F.f t (x c) := by rw [F.inner_sub t c o, zo, sub_zero]
  have hd' : ⟪F.N t, x d - x o⟫ = F.f t (x d) := by rw [F.inner_sub t d o, zo, sub_zero]
  have hc := vol3_smul_cramer (x a - x o) (x b - x o) (x c - x o) (x d - x o)
  have h_inner := congr_arg (fun v => ⟪F.N t, v⟫) hc
  rw [real_inner_smul_right, inner_add_right, inner_add_right,
      real_inner_smul_right, real_inner_smul_right, real_inner_smul_right,
      ha', hb', mul_zero, mul_zero, zero_add, zero_add] at h_inner
  have hv1 : vol3 (x a - x o) (x b - x o) (x c - x o) = det3 (x a - x o) (x b - x o) (x c - x o) := by
    simp only [det3_expand, vol3, PiLp.sub_apply]; ring
  have hv2 : vol3 (x a - x o) (x b - x o) (x d - x o) = det3 (x a - x o) (x b - x o) (x d - x o) := by
    simp only [det3_expand, vol3, PiLp.sub_apply]; ring
  rw [hv1, hv2, hc', hd'] at h_inner
  exact h_inner

lemma pos_of_mul_neg_of_neg' {a b : ℝ} (hb : b < 0) (h : a * b < 0) : 0 < a := by
  by_contra h'; push Not at h'
  nlinarith [mul_nonneg_of_nonpos_of_nonpos h' hb.le]

lemma neg_of_mul_pos_of_neg' {a b : ℝ} (hb : b < 0) (h : 0 < a * b) : a < 0 := by
  by_contra h'; push Not at h'
  nlinarith [mul_nonpos_of_nonneg_of_nonpos h' hb.le]

/-- The exposed 5-rim `(4, 5, 2, 1, 6)` of the 0345 circle (cyclically Carbon's `(6, 4, 5, 2, 1)`). -/
abbrev rimJ0 (x : Fin 7 → ℝ³) : ZMod 5 → ℝ³ := quint (x 4) (x 5) (x 2) (x 1) (x 6)

private theorem ev_inner_pos (n b d : ℝ³) (h : 0 < ⟪n, b⟫) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ⟪n, b + ε • d⟫ := by
  have := eventually_pos_affine (A := ⟪n, b⟫) (B := ⟪n, d⟫) (Or.inl h)
  filter_upwards [this] with ε hε
  rw [inner_add_right, real_inner_smul_right]; linarith

theorem omega_kappa0 (F : S0xFac 9 s0x_S24 x) :
    det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) * det3 (x 1 - x 5) (x 6 - x 2) (x 5 - x 2) < 0 := by
  have hΩ := omega_ne_zero F
  obtain ⟨p, q, r, h⟩ := exists_coords (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) (x 5 - x 1) hΩ
  have h5 : x 5 = x 1 + (p • (x 0 - x 1) + q • (x 2 - x 1) + r • (x 6 - x 1)) := by
    rw [← h]; abel
  have hid : det3 (x 1 - x 5) (x 6 - x 2) (x 5 - x 2) =
      - p * det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) := by
    rw [h5]
    simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  have hp : 0 < p := by
    have e1 : ⟪F.N 5, x 5 - x 1⟫ = F.f 5 (x 5) - F.f 5 (x 1) := (F.hN 5 _ _).symm
    have e2 : ⟪F.N 5, x 5 - x 1⟫ = p * (F.f 5 (x 0) - F.f 5 (x 1)) + q * (F.f 5 (x 2) - F.f 5 (x 1)) +
        r * (F.f 5 (x 6) - F.f 5 (x 1)) := by
      rw [h, inner_add_right, inner_add_right, real_inner_smul_right, real_inner_smul_right,
        real_inner_smul_right, F.inner_sub, F.inner_sub, F.inner_sub]
    rw [F.zero 5 1 (by decide), F.zero 5 2 (by decide), F.zero 5 6 (by decide)] at e2
    rw [F.zero 5 1 (by decide)] at e1
    have hf5 := F.neg 5 5 (by decide); have hf0 := F.neg 5 0 (by decide)
    by_contra hn; push Not at hn
    nlinarith [mul_nonneg (neg_nonneg.mpr hn) (neg_nonneg.mpr hf0.le)]
  rw [hid]
  nlinarith [mul_pos hp (sq_pos_of_ne_zero hΩ)]

/-- `Ω κ > 0` for the sub-quad `(x2, x1, x6, x4)` (drop `x5`), for every Type-24 solid. -/
theorem omega_kappa1 (F : S0xFac 9 s0x_S24 x) :
    0 < det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) * det3 (x 6 - x 2) (x 4 - x 1) (x 2 - x 1) := by
  have hΩ := omega_ne_zero F
  have hc := cramer_facet_eq F 5 1 2 6 4 0 (by decide) (by decide) (by decide)
  have e1 : det3 (x 2 - x 1) (x 6 - x 1) (x 0 - x 1) = det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have e2 : det3 (x 6 - x 2) (x 4 - x 1) (x 2 - x 1) = det3 (x 2 - x 1) (x 6 - x 1) (x 4 - x 1) := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  rw [e1] at hc
  rw [e2]
  set Ω := det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1)
  set K := det3 (x 2 - x 1) (x 6 - x 1) (x 4 - x 1)
  have f0 := F.neg 5 0 (by decide)
  have f4 := F.neg 5 4 (by decide)
  have h1 : (Ω * K) * F.f 5 (x 0) = Ω ^ 2 * F.f 5 (x 4) := by linear_combination Ω * hc
  have h2 : (Ω * K) * F.f 5 (x 0) < 0 := by
    rw [h1]; exact mul_neg_of_pos_of_neg (sq_pos_of_ne_zero hΩ) f4
  by_contra hn; push Not at hn
  nlinarith [mul_nonneg_of_nonpos_of_nonpos hn f0.le]

/-- Orientation of the 5-rim relative to `Ω` when vertex 1 is exposed (`N5 u > 0`). -/
theorem rho_omega_pos (F : S0xFac 9 s0x_S24 x) {u : ℝ³} {ρ : ℝ}
    (hρ : 0 < ρ * det3 (x 1 - x 2) (x 6 - x 2) u) (hN5 : 0 < ⟪F.N 5, u⟫) :
    0 < ρ * det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) := by
  have hsw : det3 (x 6 - x 2) (x 1 - x 2) u = - det3 (x 1 - x 2) (x 6 - x 2) u := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have hor := rimOrient F u (-ρ) (by rw [hsw]; linarith)
  by_contra hn; push Not at hn
  nlinarith [mul_nonneg (neg_nonneg.mpr hn) hN5.le]

theorem strictConvex5_of_rho' {p : ZMod 5 → ℝ³} {u : ℝ³} {ρ Ω : ℝ} (hρΩ : 0 < ρ * Ω)
    (hc : StrictConvex5 p u ρ) : StrictConvex5 p u Ω := by
  intro i j h1 h2
  have h := hc i j h1 h2
  have hT : 0 < (ρ * Ω) * (ρ * det3 (p (i + 1) - p i) (p j - p i) u) := mul_pos hρΩ h
  have e : (ρ * Ω) * (ρ * det3 (p (i + 1) - p i) (p j - p i) u) =
      ρ ^ 2 * (Ω * det3 (p (i + 1) - p i) (p j - p i) u) := by ring
  rw [e] at hT
  exact pos_of_mul_pos_right hT (sq_nonneg ρ)

/-! ### Depth-separated branch (Theorem K5-DS in lexicographic form) -/

/-- Lexicographic sign test for a determinant against the base view `b` and tilt `c`:
`Ω det3 e v (b + ε c) < 0` for small `ε > 0`. -/
def LexNegDet (Ω : ℝ) (e v b c : ℝ³) : Prop :=
  Ω * det3 e v b < 0 ∨ (Ω * det3 e v b = 0 ∧ Ω * det3 e v c < 0)

theorem ev_lexNegDet (Ω : ℝ) (e v b c : ℝ³) (h : LexNegDet Ω e v b c) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), Ω * det3 e v (b + ε • c) < 0 := by
  have hl : ∀ ε : ℝ, Ω * det3 e v (b + ε • c) = Ω * det3 e v b + ε * (Ω * det3 e v c) := by
    intro ε; simp only [det3_expand, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
  have hh : 0 < -(Ω * det3 e v b) ∨ (-(Ω * det3 e v b) = 0 ∧ 0 < -(Ω * det3 e v c)) := by
    rcases h with h | ⟨h1, h2⟩
    · exact Or.inl (by linarith)
    · exact Or.inr ⟨by linarith, by linarith⟩
  filter_upwards [eventually_pos_affine hh] with ε hε
  rw [hl]; linarith

/-- Corner `m` of the 5-rim `p` is the monotone corner `M` of a two-peaked cycle and is depth-separated from
the other four (K5-DS, lexicographic form): `z (m+1) < z m < z (m-1)`, `z (m+3) < z (m+2)`, and either
`M` below `V1 = p (m+3)` with `M` the farthest corner from the edge `[V2, P1]`, or `P1 = p (m+2)` below
`M` with `M` the farthest corner from `[V1, P2]`. -/
def DSd (p : ZMod 5 → ℝ³) (Ω : ℝ) (b c : ℝ³) (m : ZMod 5) : Prop :=
  LexLt b c (p (m + 1)) (p m) ∧ LexLt b c (p m) (p (m - 1)) ∧ LexLt b c (p (m + 3)) (p (m + 2)) ∧
  ((LexLt b c (p m) (p (m + 3)) ∧
      LexNegDet Ω (p (m + 2) - p (m + 1)) (p (m + 3) - p m) b c ∧
      LexNegDet Ω (p (m + 2) - p (m + 1)) (p (m - 1) - p m) b c) ∨
   (LexLt b c (p (m + 2)) (p m) ∧
      LexNegDet Ω (p (m - 1) - p (m + 3)) (p (m + 2) - p m) b c ∧
      LexNegDet Ω (p (m - 1) - p (m + 3)) (p (m + 1) - p m) b c))

theorem prod_neg_of {Ω D X : ℝ} (hD : 0 < Ω * D) (hX : Ω * X < 0) : X * D < 0 := by
  have h1 : (Ω * X) * (Ω * D) < 0 := mul_neg_of_neg_of_pos hX hD
  have e : (Ω * X) * (Ω * D) = Ω ^ 2 * (X * D) := by ring
  by_contra h; push Not at h
  have := mul_nonneg (sq_nonneg Ω) h
  linarith

theorem neg_sq_neg {Ω D : ℝ} (hD : 0 < Ω * D) : (-D) * D < 0 := by
  have : D ≠ 0 := by rintro rfl; simp at hD
  nlinarith [sq_pos_of_ne_zero this]

theorem ds_canon (q : ZMod 5 → ℝ³) (u : ℝ³) (Ω : ℝ) (hc : StrictConvex5 q u Ω)
    (hV2M : ⟪q 4, u⟫ < ⟪q 3, u⟫) (hMP2 : ⟪q 3, u⟫ < ⟪q 2, u⟫) (hV1P1 : ⟪q 1, u⟫ < ⟪q 0, u⟫)
    (h : (⟪q 3, u⟫ < ⟪q 1, u⟫ ∧ Ω * det3 (q 0 - q 4) (q 1 - q 3) u < 0 ∧
          Ω * det3 (q 0 - q 4) (q 2 - q 3) u < 0) ∨
        (⟪q 0, u⟫ < ⟪q 3, u⟫ ∧ Ω * det3 (q 2 - q 1) (q 0 - q 3) u < 0 ∧
          Ω * det3 (q 2 - q 1) (q 4 - q 3) u < 0)) :
    ∃ a c : ZMod 5, DepthSepAt q u a c := by
  obtain ⟨a, ha⟩ := (depthSepAt_k5_iff q u hV2M hMP2 hV1P1).mpr (by
    rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · left
      have hD : 0 < Ω * det3 (q 0 - q 4) (q 3 - q 4) u := hc 4 3 (by decide) (by decide)
      refine ⟨h1, fun j hj => ?_⟩
      rcases zmod5_cases j with rfl | rfl | rfl | rfl | rfl
      · have : det3 (q 0 - q 4) (q 0 - q 3) u = - det3 (q 0 - q 4) (q 3 - q 4) u := by
          simp only [det3_expand, PiLp.sub_apply]; ring
        rw [this]; exact neg_sq_neg hD
      · exact prod_neg_of hD h2
      · exact prod_neg_of hD h3
      · exact absurd rfl hj
      · have : det3 (q 0 - q 4) (q 4 - q 3) u = - det3 (q 0 - q 4) (q 3 - q 4) u := by
          simp only [det3_expand, PiLp.sub_apply]; ring
        rw [this]; exact neg_sq_neg hD
    · right
      have hD : 0 < Ω * det3 (q 2 - q 1) (q 3 - q 1) u := hc 1 3 (by decide) (by decide)
      refine ⟨h1, fun j hj => ?_⟩
      rcases zmod5_cases j with rfl | rfl | rfl | rfl | rfl
      · exact prod_neg_of hD h2
      · have : det3 (q 2 - q 1) (q 1 - q 3) u = - det3 (q 2 - q 1) (q 3 - q 1) u := by
          simp only [det3_expand, PiLp.sub_apply]; ring
        rw [this]; exact neg_sq_neg hD
      · have : det3 (q 2 - q 1) (q 2 - q 3) u = - det3 (q 2 - q 1) (q 3 - q 1) u := by
          simp only [det3_expand, PiLp.sub_apply]; ring
        rw [this]; exact neg_sq_neg hD
      · exact absurd rfl hj
      · exact prod_neg_of hD h3)
  exact ⟨a, 3, ha⟩

theorem strictConvex5_rot {p : ZMod 5 → ℝ³} {u : ℝ³} {Ω : ℝ} (d : ZMod 5) (hc : StrictConvex5 p u Ω) :
    StrictConvex5 (fun i => p (i + d)) u Ω := by
  intro i j h1 h2
  have h := hc (i + d) (j + d) (fun h => h1 (add_right_cancel h)) (by
    intro h; apply h2
    have : j + d = (i + 1) + d := by rw [h]; ring
    exact add_right_cancel this)
  have e : i + 1 + d = i + d + 1 := by ring
  show 0 < Ω * det3 (p (i + 1 + d) - p (i + d)) (p (j + d) - p (i + d)) u
  rw [e]; exact h

theorem strictConvex5_neg {p : ZMod 5 → ℝ³} {u : ℝ³} {Ω : ℝ} (hc : StrictConvex5 p u Ω) :
    StrictConvex5 p (-u) (-Ω) := by
  intro i j h1 h2
  have := hc i j h1 h2
  rw [det3_neg_right', neg_mul_neg]; exact this

theorem depthSepAt_rot {k : ℕ} {p : ZMod k → ℝ³} {u : ℝ³} {a c : ZMod k} (d : ZMod k)
    (h : DepthSepAt (fun i => p (i + d)) u a c) : DepthSepAt p u (a + d) (c + d) := by
  obtain ⟨hn, hz⟩ := h
  have ev : a + d - (c + d) = a - c := by ring
  have e1 : a + 1 + d = a + d + 1 := by ring
  have e4 : ∀ s : ℕ, c + d + (s : ZMod k) = c + (s : ZMod k) + d := fun s => by ring
  refine ⟨fun j hj => ?_, ?_⟩
  · have := hn (j - d) (by intro h; apply hj; rw [← h]; ring)
    have e2 : j - d + d = j := by ring
    simp only [e1, e2] at this
    exact this
  · rw [ev]; simp only [e4]; exact hz

/-- Eventual depth-separated pair from `DSd` (all inequalities are lexicographic). -/
theorem ev_ds (p : ZMod 5 → ℝ³) (Ω : ℝ) (b c : ℝ³) (m : ZMod 5)
    (hcvx : ∀ᶠ ε in 𝓝[>] (0 : ℝ), StrictConvex5 p (b + ε • c) Ω) (hm : DSd p Ω b c m) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ a c' : ZMod 5, DepthSepAt p (b + ε • c) a c' := by
  have h5 : (5 : ZMod 5) = 0 := by decide
  have r0 : (0 : ZMod 5) + (m - 3) = m + 2 := by linear_combination (-1 : ZMod 5) * h5
  have r1 : (1 : ZMod 5) + (m - 3) = m + 3 := by linear_combination (-1 : ZMod 5) * h5
  have r2 : (2 : ZMod 5) + (m - 3) = m - 1 := by ring
  have r3 : (3 : ZMod 5) + (m - 3) = m := by ring
  have r4 : (4 : ZMod 5) + (m - 3) = m + 1 := by ring
  obtain ⟨hl1, hl2, hl3, hopt⟩ := hm
  have e1 := ev_lexLt b c (p (m + 1)) (p m)
  have e2 := ev_lexLt b c (p m) (p (m - 1))
  have e3 := ev_lexLt b c (p (m + 3)) (p (m + 2))
  have hcq := hcvx.mono fun ε h => strictConvex5_rot (m - 3) h
  rcases hopt with ⟨h4, d1, d2⟩ | ⟨h4, d1, d2⟩
  · have e4 := ev_lexLt b c (p m) (p (m + 3))
    have f1 := ev_lexNegDet Ω _ _ b c d1
    have f2 := ev_lexNegDet Ω _ _ b c d2
    filter_upwards [hcq, e1, e2, e3, e4, f1, f2] with ε hc g1 g2 g3 g4 k1 k2
    obtain ⟨a, c', h⟩ := ds_canon (fun i => p (i + (m - 3))) (b + ε • c) Ω hc
      (by simpa only [r3, r4] using g1.mpr hl1) (by simpa only [r2, r3] using g2.mpr hl2)
      (by simpa only [r0, r1] using g3.mpr hl3)
      (Or.inl ⟨by simpa only [r1, r3] using g4.mpr h4, by simpa only [r0, r1, r3, r4] using k1,
        by simpa only [r0, r2, r3, r4] using k2⟩)
    exact ⟨_, _, depthSepAt_rot (m - 3) h⟩
  · have e4 := ev_lexLt b c (p (m + 2)) (p m)
    have f1 := ev_lexNegDet Ω _ _ b c d1
    have f2 := ev_lexNegDet Ω _ _ b c d2
    filter_upwards [hcq, e1, e2, e3, e4, f1, f2] with ε hc g1 g2 g3 g4 k1 k2
    obtain ⟨a, c', h⟩ := ds_canon (fun i => p (i + (m - 3))) (b + ε • c) Ω hc
      (by simpa only [r3, r4] using g1.mpr hl1) (by simpa only [r2, r3] using g2.mpr hl2)
      (by simpa only [r0, r1] using g3.mpr hl3)
      (Or.inr ⟨by simpa only [r0, r3] using g4.mpr h4, by simpa only [r0, r1, r2, r3] using k1,
        by simpa only [r0, r1, r2, r3, r4] using k2⟩)
    exact ⟨_, _, depthSepAt_rot (m - 3) h⟩


/-- The orientation determinant `Ω` of the 5-rim data. -/
noncomputable def Om (x : Fin 7 → ℝ³) : ℝ := det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1)

/-- Unimodal branch: the five lexicographic rule-out conditions (K5 in lex form) at base `b`, tilt `c`. -/
def UniLex (x : Fin 7 → ℝ³) (b c : ℝ³) : Prop :=
  ¬ LexAltDecr (rimJ0 x) b c 0 ∧ ¬ LexAltIncr (rimJ0 x) b c 1 ∧
  ((Om x * det3 (x 4 - x 1) (x 5 - x 6) (x 1 - x 6) < 0 ∧ ¬ LexAltDecr (rimJ0 x) b c 2) ∨
   (0 < Om x * det3 (x 4 - x 1) (x 5 - x 6) (x 1 - x 6) ∧ ¬ LexAltIncr (rimJ0 x) b c 2)) ∧
  ((Om x * det3 (x 5 - x 6) (x 2 - x 4) (x 6 - x 4) < 0 ∧ ¬ LexAltDecr (rimJ0 x) b c 3) ∨
   (0 < Om x * det3 (x 5 - x 6) (x 2 - x 4) (x 6 - x 4) ∧ ¬ LexAltIncr (rimJ0 x) b c 3)) ∧
  ((Om x * det3 (x 2 - x 4) (x 1 - x 5) (x 4 - x 5) < 0 ∧ ¬ LexAltDecr (rimJ0 x) b c 4) ∨
   (0 < Om x * det3 (x 2 - x 4) (x 1 - x 5) (x 4 - x 5) ∧ ¬ LexAltIncr (rimJ0 x) b c 4))

/-- Depth-separated branch: some corner `m` is the monotone corner of a two-peaked rim and is depth-separated
(increasing sense: the same condition at `-u`). -/
def DSany (x : Fin 7 → ℝ³) (b c : ℝ³) : Prop :=
  ∃ m : ZMod 5, DSd (rimJ0 x) (Om x) b c m ∨ DSd (rimJ0 x) (-Om x) (-b) (-c) m

/-- **Core of the J0-Exposed end leaf** at the view family `b + ε c = u_Pi x (α ε) (β ε)`: the rim is unimodal
(`UniLex`) or two-peaked with a depth-separated pair (`DSany`). -/
theorem core_J0_exp (F : S0xFac 9 s0x_S24 x) (s t : ℝ) (hs0 : 0 < s) (ht : 0 < t) (hst : 1 < s + t)
    (hdecomp : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0)) (b c : ℝ³) (α β : ℝ → ℝ)
    (hu : ∀ ε : ℝ, b + ε • c = u_Pi x (α ε) (β ε))
    (hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < α ε ∧ 0 < β ε ∧ 0 < α ε * (1 - s) + β ε * t ∧
      0 < α ε * s + β ε * (1 - t) ∧ 0 < ⟪F.N 5, b + ε • c⟫)
    (hU : UniLex x b c ∨ DSany x b c)
    (hgen : ∀ i j : ZMod 5, i ≠ j → ⟪rimJ0 x i - rimJ0 x j, b⟫ ≠ 0 ∨ ⟪rimJ0 x i - rimJ0 x j, c⟫ ≠ 0)
    (w : Fin 7) (hw : w = 1 ∨ w = 2 ∨ w = 6)
    (hmin : ∀ m : Fin 7, m ≠ w → (m = 1 ∨ m = 2 ∨ m = 6) → F.f 3 (x w) < F.f 3 (x m))
    (hoff : ⟪F.N 3, cross (x 5 - x 4) (x w - x 4)⟫ ≠ 0 ∨ ⟪x w - x 4, x 5 - x 4⟫ < 0 ∨
      ⟪x w - x 5, x 4 - x 5⟫ < 0) :
    FaceChordView F 3 := by
  set Ω := Om x with hΩ
  have hcvx : ∀ᶠ ε in 𝓝[>] (0 : ℝ), StrictConvex5 (rimJ0 x) (b + ε • c) Ω := by
    filter_upwards [hev] with ε ⟨hα, hβ, h8, h6, hN5'⟩
    rw [hu] at hN5' ⊢
    obtain ⟨hN3, bN0, bN1, bN2, bN4, bN6, bN8⟩ := signs_pos F s t (α ε) (β ε) hs0 ht hdecomp hα hβ h8 h6
    obtain ⟨ρ, -, hconv⟩ := rim5J0 F hN3 bN0 bN1 bN2 bN4 hN5' bN6 bN8
    have hρΩ := rho_omega_pos F (hconv 2 4 (by decide) (by decide)) hN5'
    exact strictConvex5_of_rho' hρΩ hconv
  have hinj := ev_injective b c (rimJ0 x) hgen
  have hZ : ∀ᶠ ε in 𝓝[>] (0 : ℝ), Function.Injective (fun i => ⟪rimJ0 x i, b + ε • c⟫) ∧
      UniOrSep (rimJ0 x) (b + ε • c) := by
    rcases hU with hUL | ⟨m, hm | hm⟩
    · obtain ⟨u0, u1, u2, u3, u4⟩ := hUL
      have hk0 := omega_kappa0 F
      have hk1 := omega_kappa1 F
      have hrules : ∀ m : ZMod 5, (Ω * quadKappa (subquad (rimJ0 x) m) < 0 ∧
            ¬ LexAltDecr (rimJ0 x) b c m) ∨
          (0 < Ω * quadKappa (subquad (rimJ0 x) m) ∧ ¬ LexAltIncr (rimJ0 x) b c m) := by
        intro m
        rcases zmod5_cases m with rfl | rfl | rfl | rfl | rfl
        · exact Or.inl ⟨hk0, u0⟩
        · exact Or.inr ⟨hk1, u1⟩
        · exact u2
        · exact u3
        · exact u4
      filter_upwards [ev_unimodal_five b c Ω hcvx hinj hrules] with ε ⟨hi, hcu⟩
      exact ⟨hi, Or.inl (Minimality.strictUnimodal_of_cyclic (by decide) hcu)⟩
    · filter_upwards [ev_ds (rimJ0 x) Ω b c m hcvx hm, hinj] with ε ⟨a, c', h⟩ hi
      exact ⟨hi, Or.inr ⟨a, c', h⟩⟩
    · have hcn : ∀ᶠ ε in 𝓝[>] (0 : ℝ), StrictConvex5 (rimJ0 x) (-b + ε • -c) (-Ω) := by
        filter_upwards [hcvx] with ε h
        have := strictConvex5_neg h
        rwa [show -(b + ε • c) = -b + ε • -c by rw [smul_neg, neg_add]] at this
      filter_upwards [ev_ds (rimJ0 x) (-Ω) (-b) (-c) m hcn hm, hinj] with ε ⟨a, c', h⟩ hi
      refine ⟨hi, Or.inr ⟨a, c', ?_⟩⟩
      have := h.neg
      rwa [show -(-b + ε • -c) = b + ε • c by rw [smul_neg, neg_add, neg_neg, neg_neg]] at this
  obtain ⟨ε, ⟨hα, hε0, h8, h6, hN5'⟩, hinj', hz⟩ := (hev.and hZ).exists
  rw [hu] at hN5'
  have hcu := hz
  rw [hu] at hinj' hcu
  obtain ⟨hN3', cN0, cN1, cN2, cN4, cN6, cN8⟩ := signs_pos F s t (α ε) (β ε) hs0 ht hdecomp hα hε0 h8 h6
  obtain ⟨ρ, hρ, hconv⟩ := rim5J0 F hN3' cN0 cN1 cN2 cN4 hN5' cN6 cN8
  set r : ZMod 5 → Fin 7 := quint (4 : Fin 7) 5 2 1 6 with hr
  have hrx : ∀ i, x (r i) = rimJ0 x i := quint_eq_J0t
  obtain ⟨wi, hrw⟩ : ∃ wi : ZMod 5, r wi = w := by
    rcases hw with rfl | rfl | rfl
    exacts [⟨3, rfl⟩, ⟨2, rfl⟩, ⟨4, rfl⟩]
  have hsum : α ε + β ε ≠ 0 := by positivity
  have hmb := middle_bounds_J0 s t (α ε) (β ε) hst hα hε0 h8 h6
  refine ⟨u_Pi x (α ε) (β ε), 5, inferInstance, r, 0, wi, ρ, hN3', by decide, ?_, ?_, hρ, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show quint (4 : Fin 7) 5 2 1 6 0 ∈ s0x_S24 3; decide
  · show quint (4 : Fin 7) 5 2 1 6 (0 + 1) ∈ s0x_S24 3; decide
  · intro i j hj1 hj2
    simp_rw [hrx]
    exact hconv i j hj1 hj2
  · intro q' hqS hqr i
    exact (ext_vertices_J0t q' hqS hqr).elim
  · intro q' hqS hqr
    have hra : x (r 0) = x 4 := rfl
    have hra1 : x (r (0 + 1)) = x 5 := rfl
    rw [hra, hra1]
    rcases mid_vertices_J0t q' hqS hqr with rfl | rfl
    · exact ⟨α ε / (α ε + β ε), -(1 / (α ε + β ε)), hmb.1.1, hmb.1.2.1, hmb.1.2.2,
        middle_quad_x0 x (α ε) (β ε) hsum⟩
    · exact ⟨((1 - s) * α ε + t * β ε) / (α ε + β ε), (s + t - 1) / (α ε + β ε), hmb.2.1, hmb.2.2.1,
        hmb.2.2.2, middle_quad_x3 x s t (α ε) (β ε) hdecomp hsum⟩
  · simp_rw [hrx]; exact hinj'
  · simp_rw [hrx]; exact hcu
  · rw [hrw]
    rcases hw with rfl | rfl | rfl <;> decide
  · intro m hmw hmS
    rw [hrw]
    exact hmin (r m) (fun h => hmw (rinj_J0t _ _ (h.trans hrw.symm))) (far_cand_J0t m hmS)
  · have hra : x (r 0) = x 4 := rfl
    have hra1 : x (r (0 + 1)) = x 5 := rfl
    rw [hra, hra1, hrw]
    exact hoff

/-- **J0-Exposed end leaf, `s ≤ 1`** (`E5 = e5`, view `e5 + ε (x4 - x5)`), unimodal or depth-separated. -/
theorem q45_J0_exp_end_ds (F : S0xFac 9 s0x_S24 x) (s t : ℝ) (hs0 : 0 < s) (ht : 0 < t) (hst : 1 < s + t)
    (hdecomp : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0)) (hs : s ≤ 1)
    (hN5 : 0 < ⟪F.N 5, x 5 - x 0⟫)
    (hU : UniLex x (x 5 - x 0) (x 4 - x 5) ∨ DSany x (x 5 - x 0) (x 4 - x 5))
    (hgen : ∀ i j : ZMod 5, i ≠ j →
      ⟪rimJ0 x i - rimJ0 x j, x 5 - x 0⟫ ≠ 0 ∨ ⟪rimJ0 x i - rimJ0 x j, x 4 - x 5⟫ ≠ 0)
    (w : Fin 7) (hw : w = 1 ∨ w = 2 ∨ w = 6)
    (hmin : ∀ m : Fin 7, m ≠ w → (m = 1 ∨ m = 2 ∨ m = 6) → F.f 3 (x w) < F.f 3 (x m))
    (hoff : ⟪F.N 3, cross (x 5 - x 4) (x w - x 4)⟫ ≠ 0 ∨ ⟪x w - x 4, x 5 - x 4⟫ < 0 ∨
      ⟪x w - x 5, x 4 - x 5⟫ < 0) :
    FaceChordView F 3 := by
  refine core_J0_exp F s t hs0 ht hst hdecomp (x 5 - x 0) (x 4 - x 5) (fun ε => 1 - ε) (fun ε => ε)
    (fun ε => ?_) ?_ hU hgen w hw hmin hoff
  · ext j
    simp only [u_Pi, e4, e5, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]; ring
  · have ev0 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
    have eα : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < 1 - ε := by
      filter_upwards [eventually_pos_affine (A := (1 : ℝ)) (B := -1) (Or.inl one_pos)] with ε h
      linarith
    have e8 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < (1 - ε) * (1 - s) + ε * t := by
      have hh : 0 < 1 - s ∨ (1 - s = 0 ∧ 0 < t + s - 1) := by
        rcases hs.lt_or_eq with h | h
        · exact Or.inl (by linarith)
        · exact Or.inr ⟨by linarith, by linarith⟩
      filter_upwards [eventually_pos_affine (A := 1 - s) (B := t + s - 1) hh] with ε h
      have : (1 - ε) * (1 - s) + ε * t = (1 - s) + ε * (t + s - 1) := by ring
      linarith
    have e6 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < (1 - ε) * s + ε * (1 - t) := by
      filter_upwards [eventually_pos_affine (A := s) (B := 1 - t - s) (Or.inl hs0)] with ε h
      have : (1 - ε) * s + ε * (1 - t) = s + ε * (1 - t - s) := by ring
      linarith
    filter_upwards [eα, ev0, e8, e6, ev_inner_pos (F.N 5) (x 5 - x 0) (x 4 - x 5) hN5] with ε a b c d e
    exact ⟨a, b, c, d, e⟩

/-- **J0-Exposed end leaf, `1 < s`** (`E5 = e34 = x3 - x4`, view `e34 + ε (x4 - x0)`), unimodal or
depth-separated. -/
theorem q45_J0_exp_end_ds_gt (F : S0xFac 9 s0x_S24 x) (s t : ℝ) (hs0 : 0 < s) (ht : 0 < t) (hst : 1 < s + t)
    (hdecomp : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0)) (hs : 1 < s)
    (hN5 : 0 < ⟪F.N 5, x 3 - x 4⟫)
    (hU : UniLex x (x 3 - x 4) (x 4 - x 0) ∨ DSany x (x 3 - x 4) (x 4 - x 0))
    (hgen : ∀ i j : ZMod 5, i ≠ j →
      ⟪rimJ0 x i - rimJ0 x j, x 3 - x 4⟫ ≠ 0 ∨ ⟪rimJ0 x i - rimJ0 x j, x 4 - x 0⟫ ≠ 0)
    (w : Fin 7) (hw : w = 1 ∨ w = 2 ∨ w = 6)
    (hmin : ∀ m : Fin 7, m ≠ w → (m = 1 ∨ m = 2 ∨ m = 6) → F.f 3 (x w) < F.f 3 (x m))
    (hoff : ⟪F.N 3, cross (x 5 - x 4) (x w - x 4)⟫ ≠ 0 ∨ ⟪x w - x 4, x 5 - x 4⟫ < 0 ∨
      ⟪x w - x 5, x 4 - x 5⟫ < 0) :
    FaceChordView F 3 := by
  refine core_J0_exp F s t hs0 ht hst hdecomp (x 3 - x 4) (x 4 - x 0) (fun _ => t) (fun ε => s - 1 + ε)
    (fun ε => ?_) ?_ hU hgen w hw hmin hoff
  · have hdj := fun j => congr_arg (fun (v : ℝ³) => v j) hdecomp
    ext j
    have := hdj j
    simp only [u_Pi, e4, e5, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul] at this ⊢
    linear_combination this
  · have e6 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < t * s + (s - 1 + ε) * (1 - t) := by
      have hA : 0 < t * s + (s - 1) * (1 - t) := by linarith
      filter_upwards [eventually_pos_affine (A := t * s + (s - 1) * (1 - t)) (B := 1 - t) (Or.inl hA)] with ε h
      linarith
    filter_upwards [(self_mem_nhdsWithin : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε), e6,
      ev_inner_pos (F.N 5) (x 3 - x 4) (x 4 - x 0)  hN5] with ε hε h6 hn
    have hε : (0 : ℝ) < ε := hε
    refine ⟨ht, by linarith, ?_, h6, hn⟩
    have : t * (1 - s) + (s - 1 + ε) * t = ε * t := by ring
    rw [this]; exact mul_pos hε ht


end Minimality.T24.Q45
