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

@[expose] public section

set_option autoImplicit true
set_option relaxedAutoImplicit true
open scoped RealInnerProductSpace Topology
open Filter Finset
open Minimality Minimality.H21 Minimality.FaceChord Minimality.T24.SAT Minimality.RimFromSigns
open Minimality.T24.Q45 Minimality.T24.R012

namespace Minimality.T24.R012

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

/-- The rim `(1, 6, 3, 5, 0)`; the chord `0 → 1` of facet 012 is the edge from index `4` to index `0`. -/
def rimM1 : ZMod 5 → Fin 7
  | 0 => 1
  | 1 => 6
  | 2 => 3
  | 3 => 5
  | 4 => 0

private lemma view_inner (F : S0xFac 9 s0x_S24 x) (t : Fin 9) (b c : ℝ³) (ε : ℝ) :
    ⟪F.N t, b + ε • c⟫ = ⟪F.N t, b⟫ + ε * ⟪F.N t, c⟫ := by
  rw [inner_add_right, real_inner_smul_right]

lemma evp' (N b c : ℝ³) (h : 0 < ⟪N, b⟫ ∨ (⟪N, b⟫ = 0 ∧ 0 < ⟪N, c⟫)) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ⟪N, b + ε • c⟫ := by
  filter_upwards [eventually_pos_affine h] with ε hε
  rwa [inner_add_right, real_inner_smul_right]

lemma evn' (N b c : ℝ³) (h : ⟪N, b⟫ < 0 ∨ (⟪N, b⟫ = 0 ∧ ⟪N, c⟫ < 0)) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ⟪N, b + ε • c⟫ < 0 := by
  have h' : 0 < -⟪N, b⟫ ∨ (-⟪N, b⟫ = 0 ∧ 0 < -⟪N, c⟫) := by
    rcases h with h | ⟨h1, h2⟩
    · left; linarith
    · right; constructor <;> linarith
  filter_upwards [eventually_pos_affine h'] with ε hε
  rw [inner_add_right, real_inner_smul_right]; linarith

theorem ev_signs (F : S0xFac 9 s0x_S24 x) (hN8 : 0 < ⟪F.N 8, x 0 - x 2⟫) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      0 < ⟪F.N 1, (x 0 - x 2) + ε • (x 1 - x 2)⟫ ∧ ⟪F.N 5, (x 0 - x 2) + ε • (x 1 - x 2)⟫ < 0 ∧
      ⟪F.N 7, (x 0 - x 2) + ε • (x 1 - x 2)⟫ < 0 ∧ 0 < ⟪F.N 8, (x 0 - x 2) + ε • (x 1 - x 2)⟫ ∧
      ⟪F.N 6, (x 0 - x 2) + ε • (x 1 - x 2)⟫ < 0 ∧ 0 < ⟪F.N 3, (x 0 - x 2) + ε • (x 1 - x 2)⟫ ∧
      ⟪F.N 2, (x 0 - x 2) + ε • (x 1 - x 2)⟫ < 0 := by
  have z := fun (t : Fin 9) (i : Fin 7) (h : i ∈ s0x_S24 t) => F.zero t i h
  have s := fun (t : Fin 9) (a b : Fin 7) => F.inner_sub t a b
  have e1 := evp' (F.N 1) (x 0 - x 2) (x 1 - x 2) (Or.inl (by
    rw [s 1 0 2, z 1 0 (by decide)]; linarith [F.neg 1 2 (by decide)]))
  have e5 := evn' (F.N 5) (x 0 - x 2) (x 1 - x 2) (Or.inl (by
    rw [s 5 0 2, z 5 2 (by decide)]; linarith [F.neg 5 0 (by decide)]))
  have e7 := evn' (F.N 7) (x 0 - x 2) (x 1 - x 2) (Or.inl (by
    rw [s 7 0 2, z 7 2 (by decide)]; linarith [F.neg 7 0 (by decide)]))
  have e8 := evp' (F.N 8) (x 0 - x 2) (x 1 - x 2) (Or.inl hN8)
  have e6 := evn' (F.N 6) (x 0 - x 2) (x 1 - x 2) (Or.inl (by
    rw [s 6 0 2, z 6 2 (by decide)]; linarith [F.neg 6 0 (by decide)]))
  have e3 := evp' (F.N 3) (x 0 - x 2) (x 1 - x 2) (Or.inl (by
    rw [s 3 0 2, z 3 0 (by decide)]; linarith [F.neg 3 2 (by decide)]))
  have e2 := evn' (F.N 2) (x 0 - x 2) (x 1 - x 2) (Or.inr ⟨by
    rw [s 2 0 2, z 2 0 (by decide), z 2 2 (by decide)]; ring, by
    rw [s 2 1 2, z 2 2 (by decide)]; linarith [F.neg 2 1 (by decide)]⟩)
  filter_upwards [e1, e5, e7, e8, e6, e3, e2] with ε h1 h5 h7 h8 h6 h3 h2
  exact ⟨h1, h5, h7, h8, h6, h3, h2⟩

lemma inner_N0_u (F : S0xFac 9 s0x_S24 x) (ε : ℝ) :
    ⟪F.N 0, (x 0 - x 2) + ε • (x 1 - x 2)⟫ = 0 := by
  rw [view_inner, F.inner_sub, F.inner_sub, F.zero 0 0 (by decide), F.zero 0 2 (by decide),
    F.zero 0 1 (by decide)]; ring

/-- Rim data on the view `u_ε`: orientation `ρ`, strict convexity of `(1,6,3,5,0)`, vertex `4` inside. -/
theorem rim_data (F : S0xFac 9 s0x_S24 x) {u : ℝ³}
    (hN0 : ⟪F.N 0, u⟫ = 0) (h1 : 0 < ⟪F.N 1, u⟫) (h5 : ⟪F.N 5, u⟫ < 0) (h7 : ⟪F.N 7, u⟫ < 0)
    (h8 : 0 < ⟪F.N 8, u⟫) (h6 : ⟪F.N 6, u⟫ < 0) (h3 : 0 < ⟪F.N 3, u⟫) (h2 : ⟪F.N 2, u⟫ < 0) :
    ∃ ρ : ℝ, ρ ≠ 0 ∧ StrictConvex5 (fun i => x (rimM1 i)) u ρ ∧
      (∀ i : ZMod 5, 0 < ρ * det3 (x (rimM1 (i + 1)) - x (rimM1 i)) (x 4 - x (rimM1 i)) u) := by
  have hne_01 : cross u (x 6 - x 1) ≠ 0 :=
    cross_ne_zero_of_facet_sign F 1 1 6 (by decide) (by decide) h1.ne' 0 (by decide) (by decide)
  have hne_12 : cross u (x 3 - x 6) ≠ 0 :=
    cross_ne_zero_of_facet_sign F 8 6 3 (by decide) (by decide) h8.ne' 1 (by decide) (by decide)
  have hne_23 : cross u (x 5 - x 3) ≠ 0 :=
    cross_ne_zero_of_facet_sign F 3 3 5 (by decide) (by decide) h3.ne' 7 (by decide) (by decide)
  have hne_34 : cross u (x 0 - x 5) ≠ 0 :=
    cross_ne_zero_of_facet_sign F 3 5 0 (by decide) (by decide) h3.ne' 6 (by decide) (by decide)
  have hne_40 : cross u (x 1 - x 0) ≠ 0 :=
    cross_ne_zero_of_facet_sign F 1 0 1 (by decide) (by decide) h1.ne' 3 (by decide) (by decide)
  exact fiveRim_of_signs F (u := u) rimM1 4 5 1 7 8 6 3 2 3 0
    (by decide) (by decide) hN0
    ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ ⟨h5, h1⟩
    ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ ⟨h7, h8⟩
    ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ ⟨h6, h3⟩
    ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ ⟨h2, h3⟩
    hne_01 hne_12 hne_23 hne_34 hne_40
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

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

/-- `Ω · det3 (x1-x0, x6-x0, x_d - x0) > 0` for `d = 3, 5` (facet 016 sees `d` and `2` on the same side). -/
lemma omega_V1d (F : S0xFac 9 s0x_S24 x) (d : Fin 7) (hd : d ∉ s0x_S24 1) :
    0 < det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) * det3 (x 1 - x 0) (x 6 - x 0) (x d - x 0) := by
  have hc := cramer_facet_eq F 1 0 1 6 2 d (by decide) (by decide) (by decide)
  have hid : det3 (x 1 - x 0) (x 6 - x 0) (x 2 - x 0) = det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  rw [hid] at hc
  set Ω := det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1)
  have hΩ : Ω ≠ 0 := omega_ne_zero F
  have f2 := F.neg 1 2 (by decide)
  have fd := F.neg 1 d hd
  have h1 : (Ω * det3 (x 1 - x 0) (x 6 - x 0) (x d - x 0)) * F.f 1 (x 2) = Ω ^ 2 * F.f 1 (x d) := by
    linear_combination (-Ω) * hc
  have h2 : (Ω * det3 (x 1 - x 0) (x 6 - x 0) (x d - x 0)) * F.f 1 (x 2) < 0 := by
    rw [h1]; exact mul_neg_of_pos_of_neg (sq_pos_of_ne_zero hΩ) fd
  by_contra hn; push Not at hn
  nlinarith [mul_nonneg_of_nonpos_of_nonpos hn f2.le]

/-- `Ω · det3 (x3-x0, x5-x0, x6-x0) > 0`: orientation of facet 0345 relative to `Ω`. -/
lemma omega_W0356 (F : S0xFac 9 s0x_S24 x) :
    0 < det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) * det3 (x 3 - x 0) (x 5 - x 0) (x 6 - x 0) := by
  have hA := omega_mul_det3_0256_pos_unconditional F
  have hB := cramer_facet_eq F 2 0 2 5 3 6 (by decide) (by decide) (by decide)
  have hC := cramer_facet_eq F 3 0 3 5 6 2 (by decide) (by decide) (by decide)
  set Ω := det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1)
  have hΩ : Ω ≠ 0 := omega_ne_zero F
  have e1 : det3 (x 0 - x 6) (x 2 - x 6) (x 5 - x 6) = - det3 (x 2 - x 0) (x 5 - x 0) (x 6 - x 0) := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have e2 : det3 (x 3 - x 0) (x 5 - x 0) (x 2 - x 0) = - det3 (x 2 - x 0) (x 5 - x 0) (x 3 - x 0) := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  rw [e1] at hA
  rw [e2] at hC
  set E1 := det3 (x 2 - x 0) (x 5 - x 0) (x 3 - x 0)
  set E2 := det3 (x 2 - x 0) (x 5 - x 0) (x 6 - x 0)
  set W := det3 (x 3 - x 0) (x 5 - x 0) (x 6 - x 0)
  have f26 := F.neg 2 6 (by decide)
  have f23 := F.neg 2 3 (by decide)
  have f36 := F.neg 3 6 (by decide)
  have f32 := F.neg 3 2 (by decide)
  have hE2 : Ω * E2 < 0 := by nlinarith
  have h1 : (Ω * E1) * F.f 2 (x 6) = (Ω * E2) * F.f 2 (x 3) := by linear_combination Ω * hB
  have h1' : 0 < (Ω * E1) * F.f 2 (x 6) := by
    rw [h1]; exact mul_pos_of_neg_of_neg hE2 f23
  have hE1 : Ω * E1 < 0 := neg_of_mul_pos_of_neg' f26 h1'
  have h2 : (Ω * W) * F.f 3 (x 2) = -(Ω * E1) * F.f 3 (x 6) := by linear_combination Ω * hC
  have h2' : (Ω * W) * F.f 3 (x 2) < 0 := by
    rw [h2]; exact mul_neg_of_pos_of_neg (by linarith) f36
  exact pos_of_mul_neg_of_neg' f32 h2'

/-- `Ω · det3 (x3-x0, x5-x0, x1-x0) > 0`. -/
lemma omega_W0351 (F : S0xFac 9 s0x_S24 x) :
    0 < det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) * det3 (x 3 - x 0) (x 5 - x 0) (x 1 - x 0) := by
  have hW := omega_W0356 F
  have hC := cramer_facet_eq F 3 0 3 5 6 1 (by decide) (by decide) (by decide)
  set Ω := det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1)
  set W := det3 (x 3 - x 0) (x 5 - x 0) (x 6 - x 0)
  set W1 := det3 (x 3 - x 0) (x 5 - x 0) (x 1 - x 0)
  have f36 := F.neg 3 6 (by decide)
  have f31 := F.neg 3 1 (by decide)
  have h1 : (Ω * W) * F.f 3 (x 1) = (Ω * W1) * F.f 3 (x 6) := by linear_combination Ω * hC
  have h2 : (Ω * W1) * F.f 3 (x 6) < 0 := by
    rw [← h1]; exact mul_neg_of_pos_of_neg hW f31
  exact pos_of_mul_neg_of_neg' f36 h2

/-- `Ω κ < 0` for the sub-quad of the rim `(1,6,3,5,0)` after deleting corner index 3 (`x 5`). -/
theorem omega_kappa_m3 (F : S0xFac 9 s0x_S24 x) :
    det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) * det3 (x 6 - x 0) (x 3 - x 1) (x 0 - x 1) < 0 := by
  have h := omega_V1d F 3 (by decide)
  have e : det3 (x 6 - x 0) (x 3 - x 1) (x 0 - x 1) = - det3 (x 1 - x 0) (x 6 - x 0) (x 3 - x 0) := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  rw [e]; linarith

/-- `Ω κ > 0`, deleting corner index 2 (`x 3`). -/
theorem omega_kappa_m2 (F : S0xFac 9 s0x_S24 x) :
    0 < det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) * det3 (x 1 - x 5) (x 6 - x 0) (x 5 - x 0) := by
  have h := omega_V1d F 5 (by decide)
  have e : det3 (x 1 - x 5) (x 6 - x 0) (x 5 - x 0) = det3 (x 1 - x 0) (x 6 - x 0) (x 5 - x 0) := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  rw [e]; exact h

/-- `Ω κ > 0`, deleting corner index 0 (`x 1`). -/
theorem omega_kappa_m0 (F : S0xFac 9 s0x_S24 x) :
    0 < det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) * det3 (x 5 - x 6) (x 0 - x 3) (x 6 - x 3) := by
  have h := omega_W0356 F
  have e : det3 (x 5 - x 6) (x 0 - x 3) (x 6 - x 3) = det3 (x 3 - x 0) (x 5 - x 0) (x 6 - x 0) := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  rw [e]; exact h

/-- `Ω κ < 0`, deleting corner index 1 (`x 6`). -/
theorem omega_kappa_m1 (F : S0xFac 9 s0x_S24 x) :
    det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) * det3 (x 0 - x 3) (x 1 - x 5) (x 3 - x 5) < 0 := by
  have h := omega_W0351 F
  have e : det3 (x 0 - x 3) (x 1 - x 5) (x 3 - x 5) = - det3 (x 3 - x 0) (x 5 - x 0) (x 1 - x 0) := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  rw [e]; linarith


/-- Depth of vertex `i` is lexicographically below that of `j` at the base view `x0 - x2`
(ties broken by the tilt `x1 - x2`). -/
def lexD (x : Fin 7 → ℝ³) (i j : Fin 7) : Prop := LexLt (x 0 - x 2) (x 1 - x 2) (x i) (x j)

theorem strictConvex5_of_rho {p : ZMod 5 → ℝ³} {u : ℝ³} {ρ Ω : ℝ} (hρΩ : ρ * Ω < 0)
    (hc : StrictConvex5 p u ρ) : StrictConvex5 p u (-Ω) := by
  intro i j h1 h2
  have h := hc i j h1 h2
  have hT : 0 < (-(ρ * Ω)) * (ρ * det3 (p (i + 1) - p i) (p j - p i) u) := mul_pos (by linarith) h
  have e : (-(ρ * Ω)) * (ρ * det3 (p (i + 1) - p i) (p j - p i) u) =
      ρ ^ 2 * ((-Ω) * det3 (p (i + 1) - p i) (p j - p i) u) := by ring
  rw [e] at hT
  exact pos_of_mul_pos_right hT (sq_nonneg ρ)

theorem rho_omega_neg (ε : ℝ) (hε : 0 < ε) {ρ : ℝ}
    (hc : StrictConvex5 (fun i => x (rimM1 i)) ((x 0 - x 2) + ε • (x 1 - x 2)) ρ) :
    ρ * det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) < 0 := by
  have h := hc 4 1 (by decide) (by decide)
  have e : det3 (x (rimM1 (4 + 1)) - x (rimM1 4)) (x (rimM1 1) - x (rimM1 4)) ((x 0 - x 2) + ε • (x 1 - x 2)) =
      -(1 + ε) * det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) := by
    change det3 (x 1 - x 0) (x 6 - x 0) ((x 0 - x 2) + ε • (x 1 - x 2)) = _
    simp only [det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
  rw [e] at h
  have h1 : 0 < ρ * (-(1 + ε) * det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1)) := h
  have : 0 < (1 + ε) := by linarith
  by_contra hn; push Not at hn
  nlinarith [mul_nonneg this.le hn]

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

theorem sub_kappa_sign (F : S0xFac 9 s0x_S24 x) :
    let p : ZMod 5 → ℝ³ := fun i => x (rimM1 i)
    let Ω := det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1)
    (-Ω) * quadKappa (subquad p 0) < 0 ∧ 0 < (-Ω) * quadKappa (subquad p 1) ∧
    (-Ω) * quadKappa (subquad p 2) < 0 ∧ 0 < (-Ω) * quadKappa (subquad p 3) := by
  intro p Ω
  have h0 := omega_kappa_m0 F
  have h1 := omega_kappa_m1 F
  have h2 := omega_kappa_m2 F
  have h3 := omega_kappa_m3 F
  refine ⟨?_, ?_, ?_, ?_⟩
  · change (-Ω) * det3 (x 5 - x 6) (x 0 - x 3) (x 6 - x 3) < 0; linarith
  · change 0 < (-Ω) * det3 (x 0 - x 3) (x 1 - x 5) (x 3 - x 5); linarith
  · change (-Ω) * det3 (x 1 - x 5) (x 6 - x 0) (x 5 - x 0) < 0; linarith
  · change 0 < (-Ω) * det3 (x 6 - x 0) (x 3 - x 1) (x 0 - x 1); linarith


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



/-- Unimodal branch of the m1 leaf: the five lexicographic rule-out conditions (K5 in lex form) plus the
sign of the unforced sub-quad `(x1, x6, x3, x5)` (sense `h4`). -/
def UniM1 (x : Fin 7 → ℝ³) : Prop :=
  ¬ (lexD x 6 1 ∧ lexD x 1 0 ∧ lexD x 6 3 ∧ lexD x 6 0 ∧ lexD x 5 3 ∧ lexD x 5 0) ∧
  ¬ (lexD x 1 6 ∧ lexD x 6 3 ∧ lexD x 5 3 ∧ lexD x 5 0 ∧ lexD x 1 3 ∧ lexD x 1 0) ∧
  ¬ (lexD x 5 3 ∧ lexD x 3 6 ∧ lexD x 5 0 ∧ lexD x 5 6 ∧ lexD x 1 0 ∧ lexD x 1 6) ∧
  ¬ (lexD x 3 5 ∧ lexD x 5 0 ∧ lexD x 1 0 ∧ lexD x 1 6 ∧ lexD x 3 0 ∧ lexD x 3 6) ∧
  ((0 < det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) * det3 (x 3 - x 1) (x 5 - x 6) (x 1 - x 6) ∧
        ¬ (lexD x 1 0 ∧ lexD x 0 5 ∧ lexD x 1 6 ∧ lexD x 1 5 ∧ lexD x 3 6 ∧ lexD x 3 5)) ∨
      (det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) * det3 (x 3 - x 1) (x 5 - x 6) (x 1 - x 6) < 0 ∧
        ¬ (lexD x 5 0 ∧ lexD x 0 1 ∧ lexD x 6 1 ∧ lexD x 6 3 ∧ lexD x 5 1 ∧ lexD x 5 3)))

/-- Depth-separated (two-peaked) branch of the m1 leaf: some corner of the rim `(1,6,3,5,0)` is the monotone
corner of a K5-DS pattern (decreasing sense with orientation `-Ω`, increasing sense at `-u`). -/
def DSm1 (x : Fin 7 → ℝ³) : Prop :=
  ∃ m : ZMod 5,
    DSd (fun i => x (rimM1 i)) (-det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1)) (x 0 - x 2) (x 1 - x 2) m ∨
    DSd (fun i => x (rimM1 i)) (det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1)) (-(x 0 - x 2)) (-(x 1 - x 2)) m

/-- **m1 leaf, core** (unimodal or depth-separated): facet 012, rim `(1, 6, 3, 5, 0)` with middle `2` over the
chord `0 → 1`, view `u_ε = (x0 - x2) + ε (x1 - x2)`, `ε → 0+`. Case conditions: `⟪N8, x0-x2⟫ > 0`, lexicographic
depth conditions at the base view (`UniM1`) or a K5-DS pattern (`DSm1`), tie genericity `hgen`, and the foot data
`hfar`/`hoff` of the Lemma H vertex `w`. -/
theorem m1_core (F : S0xFac 9 s0x_S24 x)
    (hN8 : 0 < ⟪F.N 8, x 0 - x 2⟫)
    (hU : UniM1 x ∨ DSm1 x)
    (hgen : ∀ i j : ZMod 5, i ≠ j →
      ⟪x (rimM1 i) - x (rimM1 j), x 0 - x 2⟫ ≠ 0 ∨ ⟪x (rimM1 i) - x (rimM1 j), x 1 - x 2⟫ ≠ 0)
    (w : ZMod 5) (hw : w = 1 ∨ w = 2 ∨ w = 3)
    (hfar : ∀ m : ZMod 5, m ≠ w → rimM1 m ∉ s0x_S24 0 → F.f 0 (x (rimM1 w)) < F.f 0 (x (rimM1 m)))
    (hoff : ⟪F.N 0, cross (x 1 - x 0) (x (rimM1 w) - x 0)⟫ ≠ 0 ∨
      ⟪x (rimM1 w) - x 0, x 1 - x 0⟫ < 0 ∨ ⟪x (rimM1 w) - x 1, x 0 - x 1⟫ < 0) :
    FaceChordView F 0 := by
  set b : ℝ³ := x 0 - x 2 with hb
  set c : ℝ³ := x 1 - x 2 with hc
  set Ω := det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) with hΩ
  set p : ZMod 5 → ℝ³ := fun i => x (rimM1 i) with hp
  have ev0 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  have evs := ev_signs F hN8
  have hcvx : ∀ᶠ ε in 𝓝[>] (0 : ℝ), StrictConvex5 p (b + ε • c) (-Ω) := by
    filter_upwards [evs, ev0] with ε ⟨h1, h5, h7, h8, h6, h3, h2⟩ hε
    obtain ⟨ρ, -, hcv, -⟩ := rim_data F (inner_N0_u F ε) h1 h5 h7 h8 h6 h3 h2
    exact strictConvex5_of_rho (rho_omega_neg ε hε hcv) hcv
  obtain ⟨k0, k1, k2, k3⟩ := sub_kappa_sign F
  have hinj := ev_injective b c p hgen
  have hZ : ∀ᶠ ε in 𝓝[>] (0 : ℝ), Function.Injective (fun i => ⟪p i, b + ε • c⟫) ∧
      UniOrSep p (b + ε • c) := by
    rcases hU with ⟨hD0, hI1, hD2, hI3, h4⟩ | ⟨m, hm | hm⟩
    · have hrules : ∀ m : ZMod 5, ((-Ω) * quadKappa (subquad p m) < 0 ∧ ¬ LexAltDecr p b c m) ∨
          (0 < (-Ω) * quadKappa (subquad p m) ∧ ¬ LexAltIncr p b c m) := by
        intro m
        rcases zmod5_cases m with rfl | rfl | rfl | rfl | rfl
        · exact Or.inl ⟨k0, fun h => hD0 h⟩
        · exact Or.inr ⟨k1, fun h => hI1 h⟩
        · exact Or.inl ⟨k2, fun h => hD2 h⟩
        · exact Or.inr ⟨k3, fun h => hI3 h⟩
        · rcases h4 with ⟨hk, hn⟩ | ⟨hk, hn⟩
          · refine Or.inl ⟨?_, fun h => hn h⟩
            change (-Ω) * det3 (x 3 - x 1) (x 5 - x 6) (x 1 - x 6) < 0; linarith
          · refine Or.inr ⟨?_, fun h => hn h⟩
            change 0 < (-Ω) * det3 (x 3 - x 1) (x 5 - x 6) (x 1 - x 6); linarith
      filter_upwards [ev_unimodal_five b c (-Ω) hcvx hinj hrules] with ε ⟨hi, hcu⟩
      exact ⟨hi, Or.inl (strictUnimodal_of_cyclic (by decide) hcu)⟩
    · filter_upwards [ev_ds p (-Ω) b c m hcvx hm, hinj] with ε ⟨a, c', h⟩ hi
      exact ⟨hi, Or.inr ⟨a, c', h⟩⟩
    · have hcn : ∀ᶠ ε in 𝓝[>] (0 : ℝ), StrictConvex5 p (-b + ε • -c) (-(-Ω)) := by
        filter_upwards [hcvx] with ε h
        have := strictConvex5_neg h
        rwa [show -(b + ε • c) = -b + ε • -c by rw [smul_neg, neg_add]] at this
      rw [neg_neg] at hcn
      filter_upwards [ev_ds p Ω (-b) (-c) m hcn hm, hinj] with ε ⟨a, c', h⟩ hi
      refine ⟨hi, Or.inr ⟨a, c', ?_⟩⟩
      have := h.neg
      rwa [show -(-b + ε • -c) = b + ε • c by rw [smul_neg, neg_add, neg_neg, neg_neg]] at this
  obtain ⟨ε, ⟨h1, h5, h7, h8, h6, h3, h2⟩, hε, hinj', hz⟩ := (evs.and (ev0.and hZ)).exists
  have hN0 := inner_N0_u F ε
  obtain ⟨ρ, hρ, hcv, hin4⟩ := rim_data F hN0 h1 h5 h7 h8 h6 h3 h2
  have hε' : (0 : ℝ) < ε := hε
  have hw' : rimM1 w ∉ s0x_S24 0 := by rcases hw with rfl | rfl | rfl <;> decide
  refine ⟨b + ε • c, 5, inferInstance, rimM1, 4, w, ρ, hN0, by decide, by decide, by decide, hρ,
    hcv, ?_, ?_, hinj', hz, hw', hfar, hoff⟩
  · intro q hq0 hqr i
    have hq4 : q = 4 := by
      fin_cases q
      · exfalso; exact hqr 4 rfl
      · exfalso; exact hqr 0 rfl
      · exfalso; revert hq0; decide
      · exfalso; exact hqr 2 rfl
      · rfl
      · exfalso; exact hqr 3 rfl
      · exfalso; exact hqr 1 rfl
    subst hq4
    exact hin4 i
  · intro q hq0 hqr
    have hq2 : q = 2 := by
      fin_cases q
      · exfalso; exact hqr 4 rfl
      · exfalso; exact hqr 0 rfl
      · rfl
      · exfalso; exact hqr 2 rfl
      · exfalso; revert hq0; decide
      · exfalso; exact hqr 3 rfl
      · exfalso; exact hqr 1 rfl
    subst hq2
    refine ⟨ε / (1 + ε), -1 / (1 + ε), by positivity, ?_, ?_, ?_⟩
    · rw [div_lt_one (by linarith)]; linarith
    · exact div_ne_zero (by norm_num) (by linarith)
    · change x 2 = x 0 + (ε / (1 + ε)) • (x 1 - x 0) + (-1 / (1 + ε)) • ((x 0 - x 2) + ε • (x 1 - x 2))
      have hne : (1 + ε) ≠ 0 := by linarith
      ext j
      simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
      field_simp
      ring




/-! ### The 6-rim `(0, 1, 6, 4, 3, 5)` for `⟪N8, x0 - x2⟫ < 0` -/

/-- The rim `(0, 1, 6, 4, 3, 5)`; the chord `0 → 1` of facet 012 is the edge from index `0` to index `1`. -/
def rimM6 : ZMod 6 → Fin 7
  | 0 => 0
  | 1 => 1
  | 2 => 6
  | 3 => 4
  | 4 => 3
  | 5 => 5

/-- Strict convexity of a rim of any length in the orientation `ρ`. -/
def StrictConvexK {k : ℕ} [NeZero k] (p : ZMod k → ℝ³) (u : ℝ³) (ρ : ℝ) : Prop :=
  ∀ i j : ZMod k, j ≠ i → j ≠ i + 1 → 0 < ρ * det3 (p (i + 1) - p i) (p j - p i) u

theorem strictConvexK_of_rho {k : ℕ} [NeZero k] {p : ZMod k → ℝ³} {u : ℝ³} {ρ Ω : ℝ} (hρΩ : ρ * Ω < 0)
    (hc : StrictConvexK p u ρ) : StrictConvexK p u (-Ω) := by
  intro i j h1 h2
  have h := hc i j h1 h2
  have hT : 0 < (-(ρ * Ω)) * (ρ * det3 (p (i + 1) - p i) (p j - p i) u) := mul_pos (by linarith) h
  have e : (-(ρ * Ω)) * (ρ * det3 (p (i + 1) - p i) (p j - p i) u) =
      ρ ^ 2 * ((-Ω) * det3 (p (i + 1) - p i) (p j - p i) u) := by ring
  rw [e] at hT
  exact pos_of_mul_pos_right hT (sq_nonneg ρ)

variable {x : Fin 7 → ℝ³}

theorem ev_signs6 (F : S0xFac 9 s0x_S24 x) (hN8 : ⟪F.N 8, x 0 - x 2⟫ < 0) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      0 < ⟪F.N 1, (x 0 - x 2) + ε • (x 1 - x 2)⟫ ∧ ⟪F.N 5, (x 0 - x 2) + ε • (x 1 - x 2)⟫ < 0 ∧
      0 < ⟪F.N 4, (x 0 - x 2) + ε • (x 1 - x 2)⟫ ∧ ⟪F.N 8, (x 0 - x 2) + ε • (x 1 - x 2)⟫ < 0 ∧
      ⟪F.N 6, (x 0 - x 2) + ε • (x 1 - x 2)⟫ < 0 ∧ 0 < ⟪F.N 3, (x 0 - x 2) + ε • (x 1 - x 2)⟫ ∧
      ⟪F.N 2, (x 0 - x 2) + ε • (x 1 - x 2)⟫ < 0 := by
  have z := fun (t : Fin 9) (i : Fin 7) (h : i ∈ s0x_S24 t) => F.zero t i h
  have s := fun (t : Fin 9) (a b : Fin 7) => F.inner_sub t a b
  have e1 := evp' (F.N 1) (x 0 - x 2) (x 1 - x 2) (Or.inl (by
    rw [s 1 0 2, z 1 0 (by decide)]; linarith [F.neg 1 2 (by decide)]))
  have e5 := evn' (F.N 5) (x 0 - x 2) (x 1 - x 2) (Or.inl (by
    rw [s 5 0 2, z 5 2 (by decide)]; linarith [F.neg 5 0 (by decide)]))
  have e4 := evp' (F.N 4) (x 0 - x 2) (x 1 - x 2) (Or.inl (by
    rw [s 4 0 2, z 4 0 (by decide)]; linarith [F.neg 4 2 (by decide)]))
  have e8 := evn' (F.N 8) (x 0 - x 2) (x 1 - x 2) (Or.inl hN8)
  have e6 := evn' (F.N 6) (x 0 - x 2) (x 1 - x 2) (Or.inl (by
    rw [s 6 0 2, z 6 2 (by decide)]; linarith [F.neg 6 0 (by decide)]))
  have e3 := evp' (F.N 3) (x 0 - x 2) (x 1 - x 2) (Or.inl (by
    rw [s 3 0 2, z 3 0 (by decide)]; linarith [F.neg 3 2 (by decide)]))
  have e2 := evn' (F.N 2) (x 0 - x 2) (x 1 - x 2) (Or.inr ⟨by
    rw [s 2 0 2, z 2 0 (by decide), z 2 2 (by decide)]; ring, by
    rw [s 2 1 2, z 2 2 (by decide)]; linarith [F.neg 2 1 (by decide)]⟩)
  filter_upwards [e1, e5, e4, e8, e6, e3, e2] with ε h1 h5 h4 h8 h6 h3 h2
  exact ⟨h1, h5, h4, h8, h6, h3, h2⟩

/-- Rim data for the 6-rim `(0,1,6,4,3,5)` at a view `u` on the circle of facet 012: strict convexity in some
orientation `ρ`, from the facet signs (every edge is a ridge between a facet seen from above and one from below,
or lies on facet 012 itself). -/
theorem rim_data6 (F : S0xFac 9 s0x_S24 x) {u : ℝ³}
    (hN0 : ⟪F.N 0, u⟫ = 0) (h1 : 0 < ⟪F.N 1, u⟫) (h5 : ⟪F.N 5, u⟫ < 0) (h4 : 0 < ⟪F.N 4, u⟫)
    (h8 : ⟪F.N 8, u⟫ < 0) (h6 : ⟪F.N 6, u⟫ < 0) (h3 : 0 < ⟪F.N 3, u⟫) (h2 : ⟪F.N 2, u⟫ < 0) :
    ∃ ρ : ℝ, ρ ≠ 0 ∧ StrictConvexK (fun i => x (rimM6 i)) u ρ := by
  have n01 : cross u (x 1 - x 0) ≠ 0 :=
    cross_ne_zero_of_facet_sign F 1 0 1 (by decide) (by decide) h1.ne' 3 (by decide) (by decide)
  have n12 : cross u (x 6 - x 1) ≠ 0 :=
    cross_ne_zero_of_facet_sign F 1 1 6 (by decide) (by decide) h1.ne' 0 (by decide) (by decide)
  have n23 : cross u (x 4 - x 6) ≠ 0 :=
    cross_ne_zero_of_facet_sign F 4 6 4 (by decide) (by decide) h4.ne' 1 (by decide) (by decide)
  have n34 : cross u (x 3 - x 4) ≠ 0 :=
    cross_ne_zero_of_facet_sign F 3 4 3 (by decide) (by decide) h3.ne' 4 (by decide) (by decide)
  have n45 : cross u (x 5 - x 3) ≠ 0 :=
    cross_ne_zero_of_facet_sign F 3 3 5 (by decide) (by decide) h3.ne' 8 (by decide) (by decide)
  have n50 : cross u (x 0 - x 5) ≠ 0 :=
    cross_ne_zero_of_facet_sign F 3 5 0 (by decide) (by decide) h3.ne' 6 (by decide) (by decide)
  obtain ⟨σ0, hσ0n, hσ0⟩ := det3_sign_edgeOn F 0 0 1 (by decide) (by decide) u hN0 n01
  obtain ⟨σ1, -, hσ1⟩ := det3_sign_ridge F 5 1 1 6 ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ u ⟨h5, h1⟩ n12
  obtain ⟨σ2, -, hσ2⟩ := det3_sign_ridge F 8 4 6 4 ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ u ⟨h8, h4⟩ n23
  obtain ⟨σ3, -, hσ3⟩ := det3_sign_ridge F 8 3 4 3 ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ u ⟨h8, h3⟩ n34
  obtain ⟨σ4, -, hσ4⟩ := det3_sign_ridge F 6 3 3 5 ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ u ⟨h6, h3⟩ n45
  obtain ⟨σ5, -, hσ5⟩ := det3_sign_ridge F 2 3 5 0 ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ u ⟨h2, h3⟩ n50
  have c0 := Minimality.det3_cycle_triangle (x 0) (x 1) (x 6) u
  have c1 := Minimality.det3_cycle_triangle (x 1) (x 6) (x 4) u
  have c2 := Minimality.det3_cycle_triangle (x 6) (x 4) (x 3) u
  have c3 := Minimality.det3_cycle_triangle (x 4) (x 3) (x 5) u
  have c4 := Minimality.det3_cycle_triangle (x 3) (x 5) (x 0) u
  have p01 : 0 < σ0 * σ1 := sign_prod (hσ0 6 (by decide)) (by rw [c0]; exact hσ1 0 (by decide))
  have p12 : 0 < σ1 * σ2 := sign_prod (hσ1 4 (by decide)) (by rw [c1]; exact hσ2 1 (by decide))
  have p23 : 0 < σ2 * σ3 := sign_prod (hσ2 3 (by decide)) (by rw [c2]; exact hσ3 6 (by decide))
  have p34 : 0 < σ3 * σ4 := sign_prod (hσ3 5 (by decide)) (by rw [c3]; exact hσ4 4 (by decide))
  have p45 : 0 < σ4 * σ5 := sign_prod (hσ4 0 (by decide)) (by rw [c4]; exact hσ5 3 (by decide))
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
  · exact sign_transfer s01 (hσ1 0 (by decide))
  · exact False.elim (hj1 rfl)
  · exact False.elim (hj2 rfl)
  · exact sign_transfer s01 (hσ1 4 (by decide))
  · exact sign_transfer s01 (hσ1 3 (by decide))
  · exact sign_transfer s01 (hσ1 5 (by decide))
  · exact sign_transfer s02 (hσ2 0 (by decide))
  · exact sign_transfer s02 (hσ2 1 (by decide))
  · exact False.elim (hj1 rfl)
  · exact False.elim (hj2 rfl)
  · exact sign_transfer s02 (hσ2 3 (by decide))
  · exact sign_transfer s02 (hσ2 5 (by decide))
  · exact sign_transfer s03 (hσ3 0 (by decide))
  · exact sign_transfer s03 (hσ3 1 (by decide))
  · exact sign_transfer s03 (hσ3 6 (by decide))
  · exact False.elim (hj1 rfl)
  · exact False.elim (hj2 rfl)
  · exact sign_transfer s03 (hσ3 5 (by decide))
  · exact sign_transfer s04 (hσ4 0 (by decide))
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

/-- Lexicographic form of `DepthSepAt p u a c` at `u = b + ε c'`, `ε → 0+`, for a rim of any length `k`: the
other corners are on the side of the edge `[a, a+1]` given by a lexicographic sign test (`LexNegDet`, relative to
the orientation `Ω` of the rim), and the depths of the other corners relative to `c` are lexicographic. -/
def LexDS {k : ℕ} [NeZero k] (p : ZMod k → ℝ³) (Ω : ℝ) (b c' : ℝ³) (a c : ZMod k) : Prop :=
  (∀ j, j ≠ c → j ≠ a → j ≠ a + 1 → LexNegDet Ω (p (a + 1) - p a) (p j - p c) b c') ∧
  (((∀ s : ℕ, 0 < s → s ≤ (a - c).val → LexLt b c' (p c) (p (c + s))) ∧
      ∀ s : ℕ, (a - c).val < s → s < k → LexLt b c' (p (c + s)) (p c)) ∨
   ((∀ s : ℕ, 0 < s → s ≤ (a - c).val → LexLt b c' (p (c + s)) (p c)) ∧
      ∀ s : ℕ, (a - c).val < s → s < k → LexLt b c' (p c) (p (c + s))))

/-- Lexicographic unimodality test: every corner but `t` has a lexicographically higher neighbour. -/
def LexTop {k : ℕ} [NeZero k] (p : ZMod k → ℝ³) (b c' : ℝ³) (t : ZMod k) : Prop :=
  ∀ i, i ≠ t → LexLt b c' (p i) (p (i - 1)) ∨ LexLt b c' (p i) (p (i + 1))

theorem ev_forall_nat (K : ℕ) (P : ℕ → ℝ → Prop) (h : ∀ s, s < K → ∀ᶠ ε in 𝓝[>] (0 : ℝ), P s ε) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ s, s < K → P s ε := by
  have := (Filter.eventually_all_finset (Finset.range K)).2 (fun s hs => h s (Finset.mem_range.1 hs))
  filter_upwards [this] with ε hε s hs using hε s (Finset.mem_range.2 hs)

theorem ev_depthSepAt {k : ℕ} [NeZero k] (p : ZMod k → ℝ³) (Ω : ℝ) (b c' : ℝ³) (a c : ZMod k)
    (hca : c ≠ a) (hca1 : c ≠ a + 1)
    (hcvx : ∀ᶠ ε in 𝓝[>] (0 : ℝ), StrictConvexK p (b + ε • c') Ω)
    (h : LexDS p Ω b c' a c) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), DepthSepAt p (b + ε • c') a c := by
  obtain ⟨hdet, hdep⟩ := h
  have e1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ j, j ≠ c → j ≠ a → j ≠ a + 1 →
      Ω * det3 (p (a + 1) - p a) (p j - p c) (b + ε • c') < 0 := by
    rw [Filter.eventually_all]; intro j
    by_cases hj : j ≠ c ∧ j ≠ a ∧ j ≠ a + 1
    · filter_upwards [ev_lexNegDet Ω _ _ b c' (hdet j hj.1 hj.2.1 hj.2.2)] with ε hε _ _ _
      exact hε
    · exact Filter.Eventually.of_forall (fun ε h1 h2 h3 => absurd ⟨h1, h2, h3⟩ hj)
  have hn : (a - c).val < k := ZMod.val_lt _
  have key : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ j, j ≠ c →
      det3 (p (a + 1) - p a) (p j - p c) (b + ε • c') * det3 (p (a + 1) - p a) (p c - p a) (b + ε • c') < 0 := by
    filter_upwards [hcvx, e1] with ε hc g
    have hD := hc a c hca hca1
    intro j hjc
    by_cases hja : j = a
    · subst hja
      have : det3 (p (j + 1) - p j) (p j - p c) (b + ε • c') = - det3 (p (j + 1) - p j) (p c - p j) (b + ε • c') := by
        simp only [det3_expand, PiLp.sub_apply]; ring
      rw [this]; exact neg_sq_neg hD
    by_cases hja1 : j = a + 1
    · subst hja1
      have : det3 (p (a + 1) - p a) (p (a + 1) - p c) (b + ε • c') = - det3 (p (a + 1) - p a) (p c - p a) (b + ε • c') := by
        simp only [det3_expand, PiLp.sub_apply]; ring
      rw [this]; exact neg_sq_neg hD
    · exact prod_neg_of hD (g j hjc hja hja1)
  have lexr : ∀ (K : ℕ) (P : ℕ → Prop) (A B : ℕ → ℝ³), (∀ s, P s → s < K) →
      (∀ s, P s → LexLt b c' (A s) (B s)) →
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ s, P s → ⟪A s, b + ε • c'⟫ < ⟪B s, b + ε • c'⟫ := by
    intro K P A B hK hl
    have := ev_forall_nat K (fun s ε => P s → ⟪A s, b + ε • c'⟫ < ⟪B s, b + ε • c'⟫) (fun s _ => by
      by_cases hp : P s
      · filter_upwards [ev_lexLt b c' (A s) (B s)] with ε hε _
        exact hε.mpr (hl s hp)
      · exact Filter.Eventually.of_forall (fun ε h => absurd h hp))
    filter_upwards [this] with ε hε s hp using hε s (hK s hp) hp
  rcases hdep with ⟨d1, d2⟩ | ⟨d1, d2⟩
  · have f1 := lexr k (fun s => 0 < s ∧ s ≤ (a - c).val) (fun _ => p c) (fun s => p (c + s))
      (fun s hs => lt_of_le_of_lt hs.2 hn) (fun s hs => d1 s hs.1 hs.2)
    have f2 := lexr k (fun s => (a - c).val < s ∧ s < k) (fun s => p (c + s)) (fun _ => p c)
      (fun s hs => hs.2) (fun s hs => d2 s hs.1 hs.2)
    filter_upwards [key, f1, f2] with ε g1 g2 g3
    exact ⟨g1, Or.inl ⟨fun s h1 h2 => g2 s ⟨h1, h2⟩, fun s h1 h2 => g3 s ⟨h1, h2⟩⟩⟩
  · have f1 := lexr k (fun s => 0 < s ∧ s ≤ (a - c).val) (fun s => p (c + s)) (fun _ => p c)
      (fun s hs => lt_of_le_of_lt hs.2 hn) (fun s hs => d1 s hs.1 hs.2)
    have f2 := lexr k (fun s => (a - c).val < s ∧ s < k) (fun _ => p c) (fun s => p (c + s))
      (fun s hs => hs.2) (fun s hs => d2 s hs.1 hs.2)
    filter_upwards [key, f1, f2] with ε g1 g2 g3
    exact ⟨g1, Or.inr ⟨fun s h1 h2 => g2 s ⟨h1, h2⟩, fun s h1 h2 => g3 s ⟨h1, h2⟩⟩⟩

theorem ev_lexTop {k : ℕ} [NeZero k] (p : ZMod k → ℝ³) (b c' : ℝ³) (t : ZMod k) (h : LexTop p b c' t) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ i, i ≠ t →
      ⟪p i, b + ε • c'⟫ < ⟪p (i - 1), b + ε • c'⟫ ∨ ⟪p i, b + ε • c'⟫ < ⟪p (i + 1), b + ε • c'⟫ := by
  rw [Filter.eventually_all]; intro i
  by_cases hi : i = t
  · exact Filter.Eventually.of_forall (fun ε h => absurd hi h)
  · filter_upwards [ev_lexLt b c' (p i) (p (i - 1)), ev_lexLt b c' (p i) (p (i + 1))] with ε h1 h2 _
    rcases h i hi with h | h
    · exact Or.inl (h1.mpr h)
    · exact Or.inr (h2.mpr h)

theorem ev_injective_k {k : ℕ} [NeZero k] (b c : ℝ³) (p : ZMod k → ℝ³)
    (hgen : ∀ i j : ZMod k, i ≠ j → ⟪p i - p j, b⟫ ≠ 0 ∨ ⟪p i - p j, c⟫ ≠ 0) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), Function.Injective (fun i => ⟪p i, b + ε • c⟫) := by
  have h : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ i j : ZMod k, i ≠ j → ⟪p i - p j, b + ε • c⟫ ≠ 0 := by
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

theorem rho_omega_neg6 (ε : ℝ) (hε : 0 < ε) {ρ : ℝ}
    (hc : StrictConvexK (fun i => x (rimM6 i)) ((x 0 - x 2) + ε • (x 1 - x 2)) ρ) :
    ρ * det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) < 0 := by
  have h := hc 0 2 (by decide) (by decide)
  have e : det3 (x (rimM6 (0 + 1)) - x (rimM6 0)) (x (rimM6 2) - x (rimM6 0)) ((x 0 - x 2) + ε • (x 1 - x 2)) =
      -(1 + ε) * det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) := by
    change det3 (x 1 - x 0) (x 6 - x 0) ((x 0 - x 2) + ε • (x 1 - x 2)) = _
    simp only [det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
  rw [e] at h
  have h1 : 0 < ρ * (-(1 + ε) * det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1)) := h
  have : 0 < (1 + ε) := by linarith
  by_contra hn; push Not at hn
  nlinarith [mul_nonneg this.le hn]

/-- **m1 leaf, 6-rim case** (`⟪N8, x0 - x2⟫ < 0`): facet 012, rim `(0, 1, 6, 4, 3, 5)` with middle `2` over the
chord `0 → 1`, view `u_ε = (x0 - x2) + ε (x1 - x2)`, `ε → 0+`. The rim is unimodal (`LexTop`: some corner `t`,
every other corner has a lexicographically higher neighbour at the base view) or has a depth-separated pair
(`LexDS`, edge `[a, a+1]`, corner `c`), plus tie genericity and the Lemma H foot data of `w`. -/

theorem q012_m1_neg_pos (F : S0xFac 9 s0x_S24 x)
    (hN8 : 0 < ⟪F.N 8, x 0 - x 2⟫)
    (hk4 : 0 < det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) * det3 (x 3 - x 1) (x 5 - x 6) (x 1 - x 6))
    (hD0 : ¬ (lexD x 6 1 ∧ lexD x 1 0 ∧ lexD x 6 3 ∧ lexD x 6 0 ∧ lexD x 5 3 ∧ lexD x 5 0))
    (hI1 : ¬ (lexD x 1 6 ∧ lexD x 6 3 ∧ lexD x 5 3 ∧ lexD x 5 0 ∧ lexD x 1 3 ∧ lexD x 1 0))
    (hD2 : ¬ (lexD x 5 3 ∧ lexD x 3 6 ∧ lexD x 5 0 ∧ lexD x 5 6 ∧ lexD x 1 0 ∧ lexD x 1 6))
    (hI3 : ¬ (lexD x 3 5 ∧ lexD x 5 0 ∧ lexD x 1 0 ∧ lexD x 1 6 ∧ lexD x 3 0 ∧ lexD x 3 6))
    (hD4 : ¬ (lexD x 1 0 ∧ lexD x 0 5 ∧ lexD x 1 6 ∧ lexD x 1 5 ∧ lexD x 3 6 ∧ lexD x 3 5))
    (hgen : ∀ i j : ZMod 5, i ≠ j →
      ⟪x (rimM1 i) - x (rimM1 j), x 0 - x 2⟫ ≠ 0 ∨ ⟪x (rimM1 i) - x (rimM1 j), x 1 - x 2⟫ ≠ 0)
    (w : ZMod 5) (hw : w = 1 ∨ w = 2 ∨ w = 3)
    (hfar : ∀ m : ZMod 5, m ≠ w → rimM1 m ∉ s0x_S24 0 → F.f 0 (x (rimM1 w)) < F.f 0 (x (rimM1 m)))
    (hoff : ⟪F.N 0, cross (x 1 - x 0) (x (rimM1 w) - x 0)⟫ ≠ 0 ∨
      ⟪x (rimM1 w) - x 0, x 1 - x 0⟫ < 0 ∨ ⟪x (rimM1 w) - x 1, x 0 - x 1⟫ < 0) :
    FaceChordView F 0 :=
  m1_core F hN8 (Or.inl ⟨hD0, hI1, hD2, hI3, Or.inl ⟨hk4, hD4⟩⟩) hgen w hw hfar hoff

theorem q012_m1_neg_neg (F : S0xFac 9 s0x_S24 x)
    (hN8 : 0 < ⟪F.N 8, x 0 - x 2⟫)
    (hk4 : det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) * det3 (x 3 - x 1) (x 5 - x 6) (x 1 - x 6) < 0)
    (hD0 : ¬ (lexD x 6 1 ∧ lexD x 1 0 ∧ lexD x 6 3 ∧ lexD x 6 0 ∧ lexD x 5 3 ∧ lexD x 5 0))
    (hI1 : ¬ (lexD x 1 6 ∧ lexD x 6 3 ∧ lexD x 5 3 ∧ lexD x 5 0 ∧ lexD x 1 3 ∧ lexD x 1 0))
    (hD2 : ¬ (lexD x 5 3 ∧ lexD x 3 6 ∧ lexD x 5 0 ∧ lexD x 5 6 ∧ lexD x 1 0 ∧ lexD x 1 6))
    (hI3 : ¬ (lexD x 3 5 ∧ lexD x 5 0 ∧ lexD x 1 0 ∧ lexD x 1 6 ∧ lexD x 3 0 ∧ lexD x 3 6))
    (hI4 : ¬ (lexD x 5 0 ∧ lexD x 0 1 ∧ lexD x 6 1 ∧ lexD x 6 3 ∧ lexD x 5 1 ∧ lexD x 5 3))
    (hgen : ∀ i j : ZMod 5, i ≠ j →
      ⟪x (rimM1 i) - x (rimM1 j), x 0 - x 2⟫ ≠ 0 ∨ ⟪x (rimM1 i) - x (rimM1 j), x 1 - x 2⟫ ≠ 0)
    (w : ZMod 5) (hw : w = 1 ∨ w = 2 ∨ w = 3)
    (hfar : ∀ m : ZMod 5, m ≠ w → rimM1 m ∉ s0x_S24 0 → F.f 0 (x (rimM1 w)) < F.f 0 (x (rimM1 m)))
    (hoff : ⟪F.N 0, cross (x 1 - x 0) (x (rimM1 w) - x 0)⟫ ≠ 0 ∨
      ⟪x (rimM1 w) - x 0, x 1 - x 0⟫ < 0 ∨ ⟪x (rimM1 w) - x 1, x 0 - x 1⟫ < 0) :
    FaceChordView F 0 :=
  m1_core F hN8 (Or.inl ⟨hD0, hI1, hD2, hI3, Or.inr ⟨hk4, hI4⟩⟩) hgen w hw hfar hoff

theorem m6_core (F : S0xFac 9 s0x_S24 x)
    (hN8 : ⟪F.N 8, x 0 - x 2⟫ < 0)
    (hU : (∃ t : ZMod 6, LexTop (fun i => x (rimM6 i)) (x 0 - x 2) (x 1 - x 2) t) ∨
      ∃ a c : ZMod 6, c ≠ a ∧ c ≠ a + 1 ∧
        LexDS (fun i => x (rimM6 i)) (-det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1)) (x 0 - x 2) (x 1 - x 2) a c)
    (hgen : ∀ i j : ZMod 6, i ≠ j →
      ⟪x (rimM6 i) - x (rimM6 j), x 0 - x 2⟫ ≠ 0 ∨ ⟪x (rimM6 i) - x (rimM6 j), x 1 - x 2⟫ ≠ 0)
    (w : ZMod 6) (hw : w = 2 ∨ w = 3 ∨ w = 4 ∨ w = 5)
    (hfar : ∀ m : ZMod 6, m ≠ w → rimM6 m ∉ s0x_S24 0 → F.f 0 (x (rimM6 w)) < F.f 0 (x (rimM6 m)))
    (hoff : ⟪F.N 0, cross (x 1 - x 0) (x (rimM6 w) - x 0)⟫ ≠ 0 ∨
      ⟪x (rimM6 w) - x 0, x 1 - x 0⟫ < 0 ∨ ⟪x (rimM6 w) - x 1, x 0 - x 1⟫ < 0) :
    FaceChordView F 0 := by
  set b : ℝ³ := x 0 - x 2 with hb
  set c : ℝ³ := x 1 - x 2 with hc
  set Ω := det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) with hΩ
  set p : ZMod 6 → ℝ³ := fun i => x (rimM6 i) with hp
  have ev0 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  have evs := ev_signs6 F hN8
  have hcvx : ∀ᶠ ε in 𝓝[>] (0 : ℝ), StrictConvexK p (b + ε • c) (-Ω) := by
    filter_upwards [evs, ev0] with ε ⟨h1, h5, h4, h8, h6, h3, h2⟩ hε
    obtain ⟨ρ, -, hcv⟩ := rim_data6 F (inner_N0_u F ε) h1 h5 h4 h8 h6 h3 h2
    exact strictConvexK_of_rho (rho_omega_neg6 ε hε hcv) hcv
  have hinj := ev_injective_k b c p hgen
  have hZ : ∀ᶠ ε in 𝓝[>] (0 : ℝ), Function.Injective (fun i => ⟪p i, b + ε • c⟫) ∧
      UniOrSep p (b + ε • c) := by
    rcases hU with ⟨t, ht⟩ | ⟨a, c', hca, hca1, hd⟩
    · filter_upwards [ev_lexTop p b c t ht, hinj] with ε h hi
      exact ⟨hi, Or.inl (strictUnimodal_of_cyclic (by decide) (isCyclicUnimodal_of_top (by norm_num) hi t h))⟩
    · filter_upwards [ev_depthSepAt p (-Ω) b c a c' hca hca1 hcvx hd, hinj] with ε h hi
      exact ⟨hi, Or.inr ⟨a, c', h⟩⟩
  obtain ⟨ε, ⟨h1, h5, h4, h8, h6, h3, h2⟩, hε, hinj', hz⟩ := (evs.and (ev0.and hZ)).exists
  have hN0 := inner_N0_u F ε
  obtain ⟨ρ, hρ, hcv⟩ := rim_data6 F hN0 h1 h5 h4 h8 h6 h3 h2
  have hε' : (0 : ℝ) < ε := hε
  have hw' : rimM6 w ∉ s0x_S24 0 := by rcases hw with rfl | rfl | rfl | rfl <;> decide
  refine ⟨b + ε • c, 6, inferInstance, rimM6, 0, w, ρ, hN0, by decide, by decide, by decide, hρ,
    hcv, ?_, ?_, hinj', hz, hw', hfar, hoff⟩
  · intro q hq0 hqr i
    exfalso
    fin_cases q
    · exact hqr 0 rfl
    · exact hqr 1 rfl
    · revert hq0; decide
    · exact hqr 4 rfl
    · exact hqr 3 rfl
    · exact hqr 5 rfl
    · exact hqr 2 rfl
  · intro q hq0 hqr
    have hq2 : q = 2 := by
      fin_cases q
      · exfalso; exact hqr 0 rfl
      · exfalso; exact hqr 1 rfl
      · rfl
      · exfalso; exact hqr 4 rfl
      · exfalso; exact hqr 3 rfl
      · exfalso; exact hqr 5 rfl
      · exfalso; exact hqr 2 rfl
    subst hq2
    refine ⟨ε / (1 + ε), -1 / (1 + ε), by positivity, ?_, ?_, ?_⟩
    · rw [div_lt_one (by linarith)]; linarith
    · exact div_ne_zero (by norm_num) (by linarith)
    · change x 2 = x 0 + (ε / (1 + ε)) • (x 1 - x 0) + (-1 / (1 + ε)) • ((x 0 - x 2) + ε • (x 1 - x 2))
      have hne : (1 + ε) ≠ 0 := by linarith
      ext j
      simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
      field_simp
      ring



end Minimality.T24.R012
