module

public import Minimality.Q45J0Edge
public import Minimality.MonoCorner
public import Minimality.ClosedCellLex
public import Minimality.Tilt

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace Topology
open Filter Finset
open Minimality Minimality.H21 Minimality.FaceChord Minimality.T24.SAT

/-!
# The J0 view tilted off the 0345 circle: a lex cell (job OSPEC4, nopert229 notes/OPENSPECIAL-STRATEGY.md)

At a J0 view `u` (on the face circle of `0345`, rim `6 4 5 2`, chord `4 → 5`, middles `0`, `3` on opposite sides of
the chord) tilt off the circle: `w = u + η σ N3` with `η > 0` small.  The face `0345` turns up (`σ = 1`) or down
(`σ = -1`); the middle on the outer side pops onto the rim: rim `6 4 0 5 2` for `σ = 1`, `6 4 3 5 2` for `σ = -1`
(`rimP0`, `rimP3`, facings `UP0 / DnP0`, `UP3 / DnP3`, every rim edge in an up and a down facet: `decide`).  The rim is
robustly unimodal at `w` as soon as two of its corners are strictly monotone at `u` (`robUni_of_monoCorners`, `k = 5`),
so the tilted view is a lex cell (`lexAny_of_j0Tilt0`, `lexAny_of_j0Tilt3`) with no far-vertex, double-normal or
injectivity hypothesis.

Which middle pops: if the rim depths at `u` are strictly unimodal and the chord `4 5` carries the maximum, the middle
`3` (depth offset `δ > 0`, so `min z4 z5 < z3`) keeps the old monotone corners; if it carries the minimum, the middle
`0` (`z0 < max z4 z5`).  The only bad case is the chord inside a monotone chain (`6 → 4 → 5 → 2` monotone,
`j0Tilt_corners`).  On the S4J0 locus the farther vertex has its foot on the chord, so its depth lies between `z4`
and `z5` at every view of the circle (`depth_between_of_s4`): the chord is not inside a monotone chain, and every J0
point of S4J0 is a lex cell (`lexAny_of_j0S4`).  On the S2 locus with an OPPOSITE pair only (`4 2` or `6 5` orthogonal
to the face plane) the tied corners rule out the monotone chain (`lexAny_of_j0_tie`, `lexAny_of_j0_s2opp`, with the
weak cores `q45_*_j0w`); off both, unless the lex order at the core's base is a monotone chain (`J0MidLex`,
`lexAny_of_j0_lexNoMid`; the S3 crossing part).  General form: `lexAny_of_j0_noMid`.
-/

namespace Minimality.T24.Q45

variable {x : Fin 7 → ℝ³}

/-- The tilted J0 rim with middle `0` popped (`σ = 1`, face `0345` up). -/
def rimP0 : ZMod 5 → Fin 7 := ![6, 4, 0, 5, 2]
/-- The tilted J0 rim with middle `3` popped (`σ = -1`, face `0345` down). -/
def rimP3 : ZMod 5 → Fin 7 := ![6, 4, 3, 5, 2]
def UP0 : Finset (Fin 9) := {3, 6, 7, 8}
def DnP0 : Finset (Fin 9) := {2, 4, 5}
def UP3 : Finset (Fin 9) := {6, 7, 8}
def DnP3 : Finset (Fin 9) := {2, 3, 4, 5}

theorem rimP0_cyc : S0xCycUD s0x_S24 rimP0 UP0 DnP0 := by decide
theorem rimP3_cyc : S0xCycUD s0x_S24 rimP3 UP3 DnP3 := by decide
theorem rimP0_inj : Function.Injective rimP0 := by decide
theorem rimP3_inj : Function.Injective rimP3 := by decide

/-- A strictly monotone corner `v` of a 5-cycle of reals (both incident edges with the same strict sign). -/
def Mono5 (z : ZMod 5 → ℝ) (v : ZMod 5) : Prop := 0 < (z v - z (v - 1)) * (z (v + 1) - z v)

theorem n3_ne_zero (F : S0xFac 9 s0x_S24 x) : F.N 3 ≠ 0 := by
  intro h
  have h1 := F.inner_sub 3 1 0
  rw [h, inner_zero_left, F.zero 3 0 (by decide)] at h1
  have := F.neg 3 1 (by decide)
  linarith

/-- **The tilt is a lex cell** (generic in the rim): facings at `u` strict except `N3` (which `σ N3` decides), two
strictly monotone rim corners at `u`. -/
theorem lexAny_of_tilt (F : S0xFac 9 s0x_S24 x) {u : ℝ³} (c : ZMod 5 → Fin 7) (hc : Function.Injective c)
    {U Dn : Finset (Fin 9)} (hcyc : S0xCycUD s0x_S24 c U Dn) (σ : ℝ)
    (hU : ∀ t ∈ U, 0 < ⟪F.N t, u⟫ ∨ (⟪F.N t, u⟫ = 0 ∧ 0 < σ * ⟪F.N t, F.N 3⟫))
    (hD : ∀ t ∈ Dn, ⟪F.N t, u⟫ < 0 ∨ (⟪F.N t, u⟫ = 0 ∧ σ * ⟪F.N t, F.N 3⟫ < 0))
    (v₁ v₂ : ZMod 5) (hv : v₁ ≠ v₂)
    (h₁ : Mono5 (fun i => ⟪x (c i), u⟫) v₁) (h₂ : Mono5 (fun i => ⟪x (c i), u⟫) v₂) :
    Gen.LexAny F := by
  set w : ℝ → ℝ³ := fun η => u + (η * σ) • F.N 3 with hw
  have hlin : ∀ (l : ℝ³) (η : ℝ), ⟪l, w η⟫ = ⟪l, u⟫ + η * (σ * ⟪l, F.N 3⟫) := by
    intro l η; simp only [hw, inner_add_right, real_inner_smul_right]; ring
  have evU : ∀ᶠ η in 𝓝[>] (0 : ℝ), ∀ t ∈ U, 0 < ⟪F.N t, w η⟫ := by
    refine (eventually_all_finset U).mpr fun t ht => ?_
    filter_upwards [eventually_pos_affine (hU t ht)] with η hη
    rw [hlin]; exact hη
  have evD : ∀ᶠ η in 𝓝[>] (0 : ℝ), ∀ t ∈ Dn, ⟪F.N t, w η⟫ < 0 := by
    refine (eventually_all_finset Dn).mpr fun t ht => ?_
    have h' : 0 < -⟪F.N t, u⟫ ∨ (-⟪F.N t, u⟫ = 0 ∧ 0 < -(σ * ⟪F.N t, F.N 3⟫)) := by
      rcases hD t ht with h | ⟨h0, h1⟩
      · exact Or.inl (by linarith)
      · exact Or.inr ⟨by rw [h0, neg_zero], by linarith⟩
    filter_upwards [eventually_pos_affine h'] with η hη
    rw [hlin]; linarith
  have evM : ∀ v, Mono5 (fun i => ⟪x (c i), u⟫) v →
      ∀ᶠ η in 𝓝[>] (0 : ℝ), Mono5 (fun i => ⟪x (c i), w η⟫) v := by
    intro v hv0
    have hcont : Continuous fun η : ℝ =>
        ((⟪x (c v), u⟫ + η * (σ * ⟪x (c v), F.N 3⟫)) -
            (⟪x (c (v - 1)), u⟫ + η * (σ * ⟪x (c (v - 1)), F.N 3⟫))) *
          ((⟪x (c (v + 1)), u⟫ + η * (σ * ⟪x (c (v + 1)), F.N 3⟫)) -
            (⟪x (c v), u⟫ + η * (σ * ⟪x (c v), F.N 3⟫))) := by fun_prop
    have h0 : 0 < ((⟪x (c v), u⟫ + (0 : ℝ) * (σ * ⟪x (c v), F.N 3⟫)) -
            (⟪x (c (v - 1)), u⟫ + (0 : ℝ) * (σ * ⟪x (c (v - 1)), F.N 3⟫))) *
          ((⟪x (c (v + 1)), u⟫ + (0 : ℝ) * (σ * ⟪x (c (v + 1)), F.N 3⟫)) -
            (⟪x (c v), u⟫ + (0 : ℝ) * (σ * ⟪x (c v), F.N 3⟫))) := by
      simp only [zero_mul, add_zero]; exact hv0
    filter_upwards [(hcont.continuousAt.eventually (lt_mem_nhds h0)).filter_mono nhdsWithin_le_nhds]
      with η hη
    simp only [Mono5, hlin]; exact hη
  obtain ⟨η, hU', hD', hm₁, hm₂⟩ := (evU.and (evD.and ((evM v₁ h₁).and (evM v₂ h₂)))).exists
  refine Minimality.H21.lexAny_of_cellAt_robUni (k := 5) (by norm_num) F hc hcyc (u := w η) ⟨hU', hD'⟩ ?_
  refine GenPlus.robUni_of_monoCorners (by norm_num) {v₁, v₂} (by rw [Finset.card_pair hv]) ?_
  intro v hv'
  rcases Finset.mem_insert.mp hv' with rfl | hv'
  · exact hm₁
  · rw [Finset.mem_singleton.mp hv']; exact hm₂

theorem lexAny_of_j0Tilt0 (F : S0xFac 9 s0x_S24 x) {u : ℝ³} (h3 : ⟪F.N 3, u⟫ = 0) (hs : J0Signs F u)
    (v₁ v₂ : ZMod 5) (hv : v₁ ≠ v₂)
    (h₁ : Mono5 (fun i => ⟪x (rimP0 i), u⟫) v₁) (h₂ : Mono5 (fun i => ⟪x (rimP0 i), u⟫) v₂) :
    Gen.LexAny F := by
  obtain ⟨h2, h4, h5, h6, h7, h8⟩ := hs
  have hNN : 0 < ⟪F.N 3, F.N 3⟫ := real_inner_self_pos.mpr (n3_ne_zero F)
  refine lexAny_of_tilt F rimP0 rimP0_inj rimP0_cyc 1 ?_ ?_ v₁ v₂ hv h₁ h₂
  · intro t ht
    simp only [UP0, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · exact Or.inr ⟨h3, by linarith⟩
    exacts [Or.inl h6, Or.inl h7, Or.inl h8]
  · intro t ht
    simp only [DnP0, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl
    exacts [Or.inl h2, Or.inl h4, Or.inl h5]

theorem lexAny_of_j0Tilt3 (F : S0xFac 9 s0x_S24 x) {u : ℝ³} (h3 : ⟪F.N 3, u⟫ = 0) (hs : J0Signs F u)
    (v₁ v₂ : ZMod 5) (hv : v₁ ≠ v₂)
    (h₁ : Mono5 (fun i => ⟪x (rimP3 i), u⟫) v₁) (h₂ : Mono5 (fun i => ⟪x (rimP3 i), u⟫) v₂) :
    Gen.LexAny F := by
  obtain ⟨h2, h4, h5, h6, h7, h8⟩ := hs
  have hNN : 0 < ⟪F.N 3, F.N 3⟫ := real_inner_self_pos.mpr (n3_ne_zero F)
  refine lexAny_of_tilt F rimP3 rimP3_inj rimP3_cyc (-1) ?_ ?_ v₁ v₂ hv h₁ h₂
  · intro t ht
    simp only [UP3, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl
    exacts [Or.inl h6, Or.inl h7, Or.inl h8]
  · intro t ht
    simp only [DnP3, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · exact Or.inl h2
    · exact Or.inr ⟨h3, by linarith⟩
    exacts [Or.inl h4, Or.inl h5]

/-! ### Which middle pops -/

private theorem mono5_0 (a b m c d : ℝ) : Mono5 ![a, b, m, c, d] 0 ↔ 0 < (a - d) * (b - a) := Iff.rfl
private theorem mono5_1 (a b m c d : ℝ) : Mono5 ![a, b, m, c, d] 1 ↔ 0 < (b - a) * (m - b) := Iff.rfl
private theorem mono5_3 (a b m c d : ℝ) : Mono5 ![a, b, m, c, d] 3 ↔ 0 < (c - m) * (d - c) := Iff.rfl
private theorem mono5_4 (a b m c d : ℝ) : Mono5 ![a, b, m, c, d] 4 ↔ 0 < (d - c) * (a - d) := Iff.rfl

/-- **The popped middle** (combinatorics of the depths `a b c d = z6 z4 z5 z2`, `p = z0`, `q = z3`): a strictly
unimodal 4-cycle (adjacent distinct, no double peak) whose chord `b c` is not inside a monotone chain gets two strictly
monotone corners after inserting `q` (if `min b c < q`, used when the chord carries the maximum) or `p` (if
`p < max b c`, when it carries the minimum) between `b` and `c`. -/
theorem j0Tilt_corners (a b c d p q : ℝ) (hab : a ≠ b) (hbc : b ≠ c) (hcd : c ≠ d) (hda : d ≠ a)
    (hn : a < b ∨ a < d ∨ c < b ∨ c < d) (hp : b < a ∨ b < c ∨ d < a ∨ d < c)
    (hmid : ¬ (a < b ∧ b < c ∧ c < d)) (hmid' : ¬ (d < c ∧ c < b ∧ b < a))
    (hp0 : p < max b c) (hq3 : min b c < q) :
    (∃ v₁ v₂ : ZMod 5, v₁ ≠ v₂ ∧ Mono5 ![a, b, q, c, d] v₁ ∧ Mono5 ![a, b, q, c, d] v₂) ∨
    (∃ v₁ v₂ : ZMod 5, v₁ ≠ v₂ ∧ Mono5 ![a, b, p, c, d] v₁ ∧ Mono5 ![a, b, p, c, d] v₂) := by
  rcases lt_or_gt_of_ne hab with h1 | h1 <;> rcases lt_or_gt_of_ne hbc with h2 | h2 <;>
    rcases lt_or_gt_of_ne hcd with h3 | h3 <;> rcases lt_or_gt_of_ne hda with h4 | h4
  -- sign patterns (sgn (b - a), sgn (c - b), sgn (d - c), sgn (a - d))
  · linarith                                                          -- + + + +
  · exact absurd ⟨h1, h2, h3⟩ hmid                                    -- + + + -
  · have hq : b < q := by rwa [min_eq_left h2.le] at hq3            -- + + - + : c max, d min
    left; exact ⟨0, 1, by decide, (mono5_0 ..).2 (mul_pos (by linarith) (by linarith)),
      (mono5_1 ..).2 (mul_pos (by linarith) (by linarith))⟩
  · have hq : b < q := by rwa [min_eq_left h2.le] at hq3            -- + + - - : c max, a min
    left; exact ⟨1, 4, by decide, (mono5_1 ..).2 (mul_pos (by linarith) (by linarith)),
      (mono5_4 ..).2 (mul_pos_of_neg_of_neg (by linarith) (by linarith))⟩
  · left; exact ⟨0, 4, by decide, (mono5_0 ..).2 (mul_pos (by linarith) (by linarith)),   -- + - + + : b max, c min
      (mono5_4 ..).2 (mul_pos (by linarith) (by linarith))⟩
  · rcases hp with h | h | h | h <;> linarith                         -- + - + - : double peak
  · have hq : c < q := by rwa [min_eq_right h2.le] at hq3           -- + - - + : b max, d min
    left; exact ⟨0, 3, by decide, (mono5_0 ..).2 (mul_pos (by linarith) (by linarith)),
      (mono5_3 ..).2 (mul_pos_of_neg_of_neg (by linarith) (by linarith))⟩
  · have hq : c < q := by rwa [min_eq_right h2.le] at hq3           -- + - - - : b max, a min
    left; exact ⟨3, 4, by decide, (mono5_3 ..).2 (mul_pos_of_neg_of_neg (by linarith) (by linarith)),
      (mono5_4 ..).2 (mul_pos_of_neg_of_neg (by linarith) (by linarith))⟩
  · have hp' : p < c := by rwa [max_eq_right h2.le] at hp0          -- - + + + : a max, b min
    right; exact ⟨3, 4, by decide, (mono5_3 ..).2 (mul_pos (by linarith) (by linarith)),
      (mono5_4 ..).2 (mul_pos (by linarith) (by linarith))⟩
  · have hp' : p < c := by rwa [max_eq_right h2.le] at hp0          -- - + + - : d max, b min
    right; exact ⟨0, 3, by decide, (mono5_0 ..).2 (mul_pos_of_neg_of_neg (by linarith) (by linarith)),
      (mono5_3 ..).2 (mul_pos (by linarith) (by linarith))⟩
  · rcases hn with h | h | h | h <;> linarith                         -- - + - + : double peak
  · left; exact ⟨0, 4, by decide, (mono5_0 ..).2 (mul_pos_of_neg_of_neg (by linarith) (by linarith)),  -- - + - - : c max, b min
      (mono5_4 ..).2 (mul_pos_of_neg_of_neg (by linarith) (by linarith))⟩
  · have hp' : p < b := by rwa [max_eq_left h2.le] at hp0           -- - - + + : a max, c min
    right; exact ⟨1, 4, by decide, (mono5_1 ..).2 (mul_pos_of_neg_of_neg (by linarith) (by linarith)),
      (mono5_4 ..).2 (mul_pos (by linarith) (by linarith))⟩
  · have hp' : p < b := by rwa [max_eq_left h2.le] at hp0           -- - - + - : d max, c min
    right; exact ⟨0, 1, by decide, (mono5_0 ..).2 (mul_pos_of_neg_of_neg (by linarith) (by linarith)),
      (mono5_1 ..).2 (mul_pos_of_neg_of_neg (by linarith) (by linarith))⟩
  · exact absurd ⟨h3, h2, h1⟩ hmid'                                   -- - - - +
  · linarith                                                          -- - - - -


/-! ### The S4J0 locus: the farther vertex's depth lies between the chord ends -/

theorem perp_id (N a b u : ℝ³) :
    ⟪N, N⟫ * (⟪b, u⟫ * ⟪a, a⟫ - ⟪b, a⟫ * ⟪a, u⟫) =
      ⟪N, cross a b⟫ * ⟪N, cross a u⟫ + ⟪cross N (cross a b), a⟫ * ⟪N, u⟫ -
        ⟪cross N (cross a b), u⟫ * ⟪N, a⟫ := by
  simp only [fcip, cross_apply_zero, cross_apply_one, cross_apply_two]; ring

/-- On `Q45S4LocusJ0` (foot of the farther vertex `v` on the chord `[x 4, x 5]` along `N3`), at every view `u` of the
`0345` circle the depth of `v` lies between the depths of `4` and `5` (projection along `N3` keeps the depth). -/
theorem depth_between_of_s4 (F : S0xFac 9 s0x_S24 x) {u : ℝ³} (h3 : ⟪F.N 3, u⟫ = 0)
    (hS4 : Q45S4LocusJ0 F) :
    min ⟪x 4, u⟫ ⟪x 5, u⟫ ≤ ⟪x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6), u⟫ ∧
      ⟪x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6), u⟫ ≤ max ⟪x 4, u⟫ ⟪x 5, u⟫ := by
  generalize hv : (if F.f 3 (x 2) < F.f 3 (x 6) then (2 : Fin 7) else 6) = v at hS4 ⊢
  simp only [Q45S4LocusJ0, hv, not_or, not_not, not_lt] at hS4
  obtain ⟨hc, hb, hb'⟩ := hS4
  have hNa : ⟪F.N 3, x 5 - x 4⟫ = 0 := by
    rw [F.inner_sub, F.zero 3 5 (by decide), F.zero 3 4 (by decide), sub_self]
  have hNN : 0 < ⟪F.N 3, F.N 3⟫ := real_inner_self_pos.mpr (n3_ne_zero F)
  have hid := perp_id (F.N 3) (x 5 - x 4) (x v - x 4) u
  rw [hc, h3, hNa] at hid
  simp only [zero_mul, mul_zero, add_zero, sub_zero] at hid
  have key : ⟪x v - x 4, u⟫ * ⟪x 5 - x 4, x 5 - x 4⟫ = ⟪x v - x 4, x 5 - x 4⟫ * ⟪x 5 - x 4, u⟫ := by
    rcases mul_eq_zero.mp hid with h | h
    · exact absurd h hNN.ne'
    · linarith
  have h45 : x 5 - x 4 ≠ 0 := by
    intro h0
    have h1 := F.inner_sub 4 5 4
    rw [h0, inner_zero_right, F.zero 4 4 (by decide), sub_zero] at h1
    have := F.neg 4 5 (by decide)
    linarith
  have hA : 0 < ⟪x 5 - x 4, x 5 - x 4⟫ := real_inner_self_pos.mpr h45
  have hb2 : ⟪x v - x 5, x 4 - x 5⟫ = ⟪x 5 - x 4, x 5 - x 4⟫ - ⟪x v - x 4, x 5 - x 4⟫ := by
    simp only [fcip, PiLp.sub_apply]; ring
  rw [hb2] at hb'
  rw [show ⟪x v - x 4, u⟫ = ⟪x v, u⟫ - ⟪x 4, u⟫ from inner_sub_left _ _ _,
    show ⟪x 5 - x 4, u⟫ = ⟪x 5, u⟫ - ⟪x 4, u⟫ from inner_sub_left _ _ _] at key
  rcases le_total ⟪x 4, u⟫ ⟪x 5, u⟫ with hle | hle
  · rw [min_eq_left hle, max_eq_right hle]
    constructor
    · by_contra hlt; push Not at hlt
      nlinarith [mul_nonneg hb (sub_nonneg.2 hle), mul_pos (sub_pos.2 hlt) hA]
    · by_contra hlt; push Not at hlt
      nlinarith [mul_nonneg hb' (sub_nonneg.2 hle), mul_pos (sub_pos.2 hlt) hA]
  · rw [min_eq_right hle, max_eq_left hle]
    constructor
    · by_contra hlt; push Not at hlt
      nlinarith [mul_nonneg hb' (sub_nonneg.2 hle), mul_pos (sub_pos.2 hlt) hA]
    · by_contra hlt; push Not at hlt
      nlinarith [mul_nonneg hb (sub_nonneg.2 hle), mul_pos (sub_pos.2 hlt) hA]

/-- A strictly unimodal 4-cycle: adjacent values distinct and no double peak (each diagonal pair is beaten once). -/
theorem su4_facts {z : ZMod 4 → ℝ} (h : StrictUnimodal z) :
    z 0 ≠ z 1 ∧ z 1 ≠ z 2 ∧ z 2 ≠ z 3 ∧ z 3 ≠ z 0 ∧
      (z 0 < z 1 ∨ z 0 < z 3 ∨ z 2 < z 1 ∨ z 2 < z 3) ∧ (z 1 < z 0 ∨ z 1 < z 2 ∨ z 3 < z 0 ∨ z 3 < z 2) := by
  obtain ⟨hne, hcard⟩ := h
  have e0 : z 0 ≠ z 1 := hne 0
  have e1 : z 1 ≠ z 2 := hne 1
  have e2 : z 2 ≠ z 3 := hne 2
  have e3 : z 3 ≠ z 0 := hne 3
  have two : ∀ i j : ZMod 4, i ≠ j → (z (i - 1) < z i ∧ z (i + 1) < z i) → (z (j - 1) < z j ∧ z (j + 1) < z j) →
      False := by
    intro i j hij hi hj
    have hsub : ({i, j} : Finset (ZMod 4)) ⊆ univ.filter fun k => z (k - 1) < z k ∧ z (k + 1) < z k := by
      intro k hk
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl <;> simp only [Finset.mem_filter, Finset.mem_univ, true_and] <;> assumption
    have := Finset.card_le_card hsub
    rw [hcard, Finset.card_pair hij] at this
    omega
  refine ⟨e0, e1, e2, e3, ?_, ?_⟩
  · by_contra hc; push Not at hc
    obtain ⟨c1, c2, c3, c4⟩ := hc
    exact two 0 2 (by decide) ⟨lt_of_le_of_ne c2 e3, lt_of_le_of_ne c1 e0.symm⟩
      ⟨lt_of_le_of_ne c3 e1, lt_of_le_of_ne c4 e2.symm⟩
  · by_contra hc; push Not at hc
    obtain ⟨c1, c2, c3, c4⟩ := hc
    exact two 1 3 (by decide) ⟨lt_of_le_of_ne c1 e0, lt_of_le_of_ne c2 e1.symm⟩
      ⟨lt_of_le_of_ne c4 e2, lt_of_le_of_ne c3 e3.symm⟩

/-- **A J0 view whose chord is not inside a monotone chain tilts to a lex cell.**  `u` a J0 view (on the `0345`
circle, `J0Extra`: the J0 facet signs, strictly unimodal rim depths, middle `0` below `max z4 z5`, middle `3` above
`min z4 z5`); `hmid`, `hmid'`: the rim `6 → 4 → 5 → 2` is not monotone; `j0Tilt_corners` picks the middle to pop. -/
theorem lexAny_of_j0_noMid (F : S0xFac 9 s0x_S24 x) {u : ℝ³} (h3 : ⟪F.N 3, u⟫ = 0) (hx : J0Extra F u)
    (hmid : ¬ (⟪x 6, u⟫ < ⟪x 4, u⟫ ∧ ⟪x 4, u⟫ < ⟪x 5, u⟫ ∧ ⟪x 5, u⟫ < ⟪x 2, u⟫))
    (hmid' : ¬ (⟪x 2, u⟫ < ⟪x 5, u⟫ ∧ ⟪x 5, u⟫ < ⟪x 4, u⟫ ∧ ⟪x 4, u⟫ < ⟪x 6, u⟫)) : Gen.LexAny F := by
  obtain ⟨hs, huni, h0, h3'⟩ := hx
  obtain ⟨e0, e1, e2, e3, hn, hp⟩ := su4_facts huni
  simp only [quad] at e0 e1 e2 e3 hn hp
  change ⟪x 6, u⟫ ≠ ⟪x 4, u⟫ at e0
  change ⟪x 4, u⟫ ≠ ⟪x 5, u⟫ at e1
  change ⟪x 5, u⟫ ≠ ⟪x 2, u⟫ at e2
  change ⟪x 2, u⟫ ≠ ⟪x 6, u⟫ at e3
  change ⟪x 6, u⟫ < ⟪x 4, u⟫ ∨ ⟪x 6, u⟫ < ⟪x 2, u⟫ ∨ ⟪x 5, u⟫ < ⟪x 4, u⟫ ∨ ⟪x 5, u⟫ < ⟪x 2, u⟫ at hn
  change ⟪x 4, u⟫ < ⟪x 6, u⟫ ∨ ⟪x 4, u⟫ < ⟪x 5, u⟫ ∨ ⟪x 2, u⟫ < ⟪x 6, u⟫ ∨ ⟪x 2, u⟫ < ⟪x 5, u⟫ at hp
  have hz3 : (fun i => ⟪x (rimP3 i), u⟫) = ![⟪x 6, u⟫, ⟪x 4, u⟫, ⟪x 3, u⟫, ⟪x 5, u⟫, ⟪x 2, u⟫] := by
    funext i; fin_cases i <;> rfl
  have hz0 : (fun i => ⟪x (rimP0 i), u⟫) = ![⟪x 6, u⟫, ⟪x 4, u⟫, ⟪x 0, u⟫, ⟪x 5, u⟫, ⟪x 2, u⟫] := by
    funext i; fin_cases i <;> rfl
  rcases j0Tilt_corners _ _ _ _ _ _ e0 e1 e2 e3 hn hp hmid hmid' h0 h3' with
    ⟨v₁, v₂, hv, m₁, m₂⟩ | ⟨v₁, v₂, hv, m₁, m₂⟩
  · exact lexAny_of_j0Tilt3 F h3 hs v₁ v₂ hv (by rw [hz3]; exact m₁) (by rw [hz3]; exact m₂)
  · exact lexAny_of_j0Tilt0 F h3 hs v₁ v₂ hv (by rw [hz0]; exact m₁) (by rw [hz0]; exact m₂)

/-- **Every J0 view on the S4J0 locus tilts to a lex cell**: the farther vertex's depth lies between `z4` and `z5`
(`depth_between_of_s4`), so the chord is not inside a monotone chain. -/
theorem lexAny_of_j0S4 (F : S0xFac 9 s0x_S24 x) {u : ℝ³} (h3 : ⟪F.N 3, u⟫ = 0) (hx : J0Extra F u)
    (hS4 : Q45S4LocusJ0 F) : Gen.LexAny F := by
  have hb := depth_between_of_s4 F h3 hS4
  refine lexAny_of_j0_noMid F h3 hx ?_ ?_
  · rintro ⟨c1, c2, c3⟩
    rw [min_eq_left c2.le, max_eq_right c2.le] at hb
    split_ifs at hb <;> linarith [hb.1, hb.2]
  · rintro ⟨c1, c2, c3⟩
    rw [min_eq_right c2.le, max_eq_left c2.le] at hb
    split_ifs at hb <;> linarith [hb.1, hb.2]

/-- **A J0 view with an opposite depth tie tilts to a lex cell** (`z4 = z2` or `z6 = z5`: the S2 pairs `4 2`, `6 5`
of the rim `6 4 5 2`): a monotone chain through the chord would separate the tied corners. -/
theorem lexAny_of_j0_tie (F : S0xFac 9 s0x_S24 x) {u : ℝ³} (h3 : ⟪F.N 3, u⟫ = 0) (hx : J0Extra F u)
    (htie : ⟪x 4, u⟫ = ⟪x 2, u⟫ ∨ ⟪x 6, u⟫ = ⟪x 5, u⟫) : Gen.LexAny F := by
  refine lexAny_of_j0_noMid F h3 hx ?_ ?_
  · rintro ⟨c1, c2, c3⟩; rcases htie with h | h <;> linarith
  · rintro ⟨c1, c2, c3⟩; rcases htie with h | h <;> linarith

/-- **The S2J0 locus with no adjacent S2 pair** (a weak J0 core's view `u = B + ε D`, `hS2a`, the full S2 condition
failing): an opposite pair is orthogonal to `B` and `D`, hence tied at `u`, and the tilt is a lex cell. -/
theorem lexAny_of_j0_s2opp (F : S0xFac 9 s0x_S24 x) {u B D : ℝ³} (h3 : ⟪F.N 3, u⟫ = 0) (hx : J0Extra F u)
    (hu : ∃ ε : ℝ, u = B + ε • D)
    (hS2a : ∀ i : ZMod 4,
      ⟪quad (x 6) (x 4) (x 5) (x 2) i - quad (x 6) (x 4) (x 5) (x 2) (i + 1), B⟫ ≠ 0 ∨
      ⟪quad (x 6) (x 4) (x 5) (x 2) i - quad (x 6) (x 4) (x 5) (x 2) (i + 1), D⟫ ≠ 0)
    (hS2 : ¬ ∀ i j : ZMod 4, i ≠ j →
      ⟪quad (x 6) (x 4) (x 5) (x 2) i - quad (x 6) (x 4) (x 5) (x 2) j, B⟫ ≠ 0 ∨
      ⟪quad (x 6) (x 4) (x 5) (x 2) i - quad (x 6) (x 4) (x 5) (x 2) j, D⟫ ≠ 0) : Gen.LexAny F := by
  obtain ⟨ε, rfl⟩ := hu
  refine lexAny_of_j0_tie F h3 hx ?_
  have hlin : ∀ a c : ℝ³, ⟪a, B + ε • D⟫ - ⟪c, B + ε • D⟫ = ⟪a - c, B⟫ + ε * ⟪a - c, D⟫ := by
    intro a c; rw [← inner_sub_left, inner_add_right, real_inner_smul_right]
  rcases s2_opp_of _ B D hS2a hS2 with ⟨hb, hd⟩ | ⟨hb, hd⟩
  · left
    have := hlin (x 4) (x 2)
    simp only [quad] at hb hd
    change ⟪x 4 - x 2, B⟫ = 0 at hb
    change ⟪x 4 - x 2, D⟫ = 0 at hd
    rw [hb, hd, mul_zero, add_zero] at this; linarith
  · right
    have := hlin (x 6) (x 5)
    simp only [quad] at hb hd
    change ⟪x 6 - x 5, B⟫ = 0 at hb
    change ⟪x 6 - x 5, D⟫ = 0 at hd
    rw [hb, hd, mul_zero, add_zero] at this; linarith

/-- `z a < z c` in the lex order of the views `B + ε D` (`ε → 0⁺`). -/
def LexLt2 (x : Fin 7 → ℝ³) (B D : ℝ³) (a c : Fin 7) : Prop :=
  0 < ⟪x c - x a, B⟫ ∨ (⟪x c - x a, B⟫ = 0 ∧ 0 < ⟪x c - x a, D⟫)

/-- The J0 rim depths in lex order at `(B, D)` with the chord inside a monotone chain (`6 → 4 → 5 → 2`). -/
def J0MidLex (x : Fin 7 → ℝ³) (B D : ℝ³) : Prop :=
  (LexLt2 x B D 6 4 ∧ LexLt2 x B D 4 5 ∧ LexLt2 x B D 5 2) ∨
    (LexLt2 x B D 2 5 ∧ LexLt2 x B D 5 4 ∧ LexLt2 x B D 4 6)

/-- A strict depth order at a view `u = B + ε D` that reads the lex order (`hlex`) is a lex order. -/
theorem lexLt2_of_lt {B D u : ℝ³} (hu : ∃ ε : ℝ, u = B + ε • D)
    (hlex : ∀ a c : Fin 7, (0 < ⟪x a - x c, B⟫ ∨ (⟪x a - x c, B⟫ = 0 ∧ 0 < ⟪x a - x c, D⟫)) →
      ⟪x c, u⟫ < ⟪x a, u⟫) {a c : Fin 7} (h : ⟪x a, u⟫ < ⟪x c, u⟫) : LexLt2 x B D a c := by
  obtain ⟨ε, rfl⟩ := hu
  have hl : ⟪x c, B + ε • D⟫ - ⟪x a, B + ε • D⟫ = ⟪x c - x a, B⟫ + ε * ⟪x c - x a, D⟫ := by
    rw [← inner_sub_left, inner_add_right, real_inner_smul_right]
  have nB : ⟪x a - x c, B⟫ = -⟪x c - x a, B⟫ := by rw [← inner_neg_left, neg_sub]
  have nD : ⟪x a - x c, D⟫ = -⟪x c - x a, D⟫ := by rw [← inner_neg_left, neg_sub]
  by_contra hn
  simp only [LexLt2, not_or, not_and, not_lt] at hn
  obtain ⟨h1, h2⟩ := hn
  rcases lt_or_eq_of_le h1 with h1 | h1
  · have := hlex a c (Or.inl (by rw [nB]; linarith)); linarith
  · rcases lt_or_eq_of_le (h2 h1) with h3 | h3
    · have := hlex a c (Or.inr ⟨by rw [nB, h1, neg_zero], by rw [nD]; linarith⟩); linarith
    · rw [h1, h3, mul_zero, add_zero] at hl; linarith

/-- **The tilt off the lex monotone chain**: a weak J0 core's view (`u = B + ε D` reading the lex order at `(B, D)`)
with the rim not in a lex monotone chain through the chord is a lex cell. -/
theorem lexAny_of_j0_lexNoMid (F : S0xFac 9 s0x_S24 x) {u B D : ℝ³} (h3 : ⟪F.N 3, u⟫ = 0) (hx : J0Extra F u)
    (hu : ∃ ε : ℝ, u = B + ε • D)
    (hlex : ∀ a c : Fin 7, (0 < ⟪x a - x c, B⟫ ∨ (⟪x a - x c, B⟫ = 0 ∧ 0 < ⟪x a - x c, D⟫)) →
      ⟪x c, u⟫ < ⟪x a, u⟫)
    (hnm : ¬ J0MidLex x B D) : Gen.LexAny F := by
  refine lexAny_of_j0_noMid F h3 hx ?_ ?_
  · rintro ⟨c1, c2, c3⟩
    exact hnm (Or.inl ⟨lexLt2_of_lt hu hlex c1, lexLt2_of_lt hu hlex c2, lexLt2_of_lt hu hlex c3⟩)
  · rintro ⟨c1, c2, c3⟩
    exact hnm (Or.inr ⟨lexLt2_of_lt hu hlex c1, lexLt2_of_lt hu hlex c2, lexLt2_of_lt hu hlex c3⟩)

/-- **A J0 core's view on S4J0 is a lex cell** (`J0Chord` gives `⟪N3, u⟫ = 0`). -/
theorem lexAny_of_j0Chord_s4 (F : S0xFac 9 s0x_S24 x) {u : ℝ³} {ρ : ℝ} (hc : J0Chord F u ρ) (hx : J0Extra F u)
    (hS4 : Q45S4LocusJ0 F) : Gen.LexAny F :=
  lexAny_of_j0S4 F hc.1 hx hS4

/-! ### The tilt in the 3-level lex order (job OSPEC5): no S2 hypothesis

At a weak core's view `u = B + ε D` (reading the lex order at `(B, D)`; adjacent rim pairs may TIE at `u` when they
are orthogonal to `B` and `D`) tilt by `η σ N3`.  For small `η` the rim depths at `u + η σ N3` are ordered by the
3-level lex order `(B, D, σ N3)`; a tied pair is separated by `σ (h_i - h_j)`, `h = ⟪x, N3⟫`.  The tilted view is a lex
cell (base `u`, `d1 = σ N3`, `d2 = 0`) whenever the popped rim (`rimP0` for `σ = 1`, `rimP3` for `σ = -1`) is
`RobUniLex` in that order (`J0TiltOK`).  This subsumes `lexAny_of_j0_noMid` and its corollaries: at `u` the depth
order IS the `(B, D)` lex order (`hlex`; lex-zero pairs are tied at `u`). -/

open Minimality.LexCell in
/-- The 3-level lex tilt: the popped rim `rimP0` (face `0345` up, `σ = 1`) or `rimP3` (down, `σ = -1`) is robustly
unimodal in the lex order `(B, D, σ N3)`. -/
def J0TiltOK {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (B D : ℝ³) : Prop :=
  RobUniLex (fun i => (⟪x (rimP0 i), B⟫, ⟪x (rimP0 i), D⟫, ⟪x (rimP0 i), F.N 3⟫)) ∨
    RobUniLex (fun i => (⟪x (rimP3 i), B⟫, ⟪x (rimP3 i), D⟫, ⟪x (rimP3 i), -F.N 3⟫))

open Minimality.LexCell in
/-- A `(B, D, N)` lex comparison becomes a `(u, N, 0)` lex comparison at a view `u = B + ε D` reading the `(B, D)`
lex order. -/
theorem lexLt3_tilt {B D u N : ℝ³} (hu : ∃ ε : ℝ, u = B + ε • D)
    (hlex : ∀ a c : Fin 7, (0 < ⟪x a - x c, B⟫ ∨ (⟪x a - x c, B⟫ = 0 ∧ 0 < ⟪x a - x c, D⟫)) →
      ⟪x c, u⟫ < ⟪x a, u⟫) (a c : Fin 7)
    (h : LexLt3 (⟪x a, B⟫, ⟪x a, D⟫, ⟪x a, N⟫) (⟪x c, B⟫, ⟪x c, D⟫, ⟪x c, N⟫)) :
    LexLt3 (⟪x a, u⟫, ⟪x a, N⟫, ⟪x a, (0 : ℝ³)⟫) (⟪x c, u⟫, ⟪x c, N⟫, ⟪x c, (0 : ℝ³)⟫) := by
  obtain ⟨ε, rfl⟩ := hu
  simp only [LexLt3, LexPos3] at h ⊢
  have eB : ⟪x c - x a, B⟫ = ⟪x c, B⟫ - ⟪x a, B⟫ := inner_sub_left _ _ _
  have eD : ⟪x c - x a, D⟫ = ⟪x c, D⟫ - ⟪x a, D⟫ := inner_sub_left _ _ _
  have eu : ⟪x c, B + ε • D⟫ - ⟪x a, B + ε • D⟫ = (⟪x c, B⟫ - ⟪x a, B⟫) + ε * (⟪x c, D⟫ - ⟪x a, D⟫) := by
    simp only [inner_add_right, real_inner_smul_right]; ring
  rcases h with h | ⟨h0, h | ⟨h1, h⟩⟩
  · exact Or.inl (sub_pos.2 (hlex c a (Or.inl (by rw [eB]; exact h))))
  · exact Or.inl (sub_pos.2 (hlex c a (Or.inr ⟨by rw [eB]; exact h0, by rw [eD]; exact h⟩)))
  · right; refine ⟨by rw [eu, h0, h1]; ring, Or.inl h⟩

open Minimality.LexCell in
/-- **The lex tilt is a lex cell** (generic rim): facings at `u` strict except those decided by `N`, the rim
`RobUniLex` in the lex order `(B, D, N)`, `u = B + ε D` reading the `(B, D)` lex order. -/
theorem lexAny_of_tiltLex {k : ℕ} [NeZero k] (hk : 4 ≤ k) (F : S0xFac 9 s0x_S24 x) {u B D N : ℝ³}
    (c : ZMod k → Fin 7) (hc : Function.Injective c) {U Dn : Finset (Fin 9)} (hcyc : S0xCycUD s0x_S24 c U Dn)
    (hU : ∀ t ∈ U, 0 < ⟪F.N t, u⟫ ∨ (⟪F.N t, u⟫ = 0 ∧ 0 < ⟪F.N t, N⟫))
    (hD : ∀ t ∈ Dn, ⟪F.N t, u⟫ < 0 ∨ (⟪F.N t, u⟫ = 0 ∧ ⟪F.N t, N⟫ < 0))
    (hu : ∃ ε : ℝ, u = B + ε • D)
    (hlex : ∀ a c : Fin 7, (0 < ⟪x a - x c, B⟫ ∨ (⟪x a - x c, B⟫ = 0 ∧ 0 < ⟪x a - x c, D⟫)) →
      ⟪x c, u⟫ < ⟪x a, u⟫)
    (hR : RobUniLex (fun i => (⟪x (c i), B⟫, ⟪x (c i), D⟫, ⟪x (c i), N⟫))) : Gen.LexAny F := by
  refine ⟨k, inferInstance, c, U, Dn, u, N, 0, hk, hc, hcyc, ?_, ?_, ?_⟩
  · intro t ht
    rcases hU t ht with h | ⟨h0, h1⟩
    · exact Or.inl h
    · exact Or.inr ⟨h0, Or.inl h1⟩
  · intro t ht
    rcases hD t ht with h | ⟨h0, h1⟩
    · exact Or.inl (by linarith)
    · exact Or.inr ⟨by rw [h0, neg_zero], Or.inl (by linarith)⟩
  · intro B' b c' d hb hbc hcd hd
    rcases hR B' b c' d hb hbc hcd hd with h | h | h | h
    · exact Or.inl (lexLt3_tilt hu hlex _ _ h)
    · exact Or.inr (Or.inl (lexLt3_tilt hu hlex _ _ h))
    · exact Or.inr (Or.inr (Or.inl (lexLt3_tilt hu hlex _ _ h)))
    · exact Or.inr (Or.inr (Or.inr (lexLt3_tilt hu hlex _ _ h)))

/-- **The J0 lex tilt** (no S2, S3, S4 or unimodality hypothesis): a weak core's view `u = B + ε D` with the J0 facet
signs, on the `0345` circle, reading the `(B, D)` lex order, and `J0TiltOK F B D` give a lex cell. -/
theorem lexAny_of_j0TiltLex (F : S0xFac 9 s0x_S24 x) {u B D : ℝ³} (h3 : ⟪F.N 3, u⟫ = 0) (hs : J0Signs F u)
    (hu : ∃ ε : ℝ, u = B + ε • D)
    (hlex : ∀ a c : Fin 7, (0 < ⟪x a - x c, B⟫ ∨ (⟪x a - x c, B⟫ = 0 ∧ 0 < ⟪x a - x c, D⟫)) →
      ⟪x c, u⟫ < ⟪x a, u⟫)
    (hT : J0TiltOK F B D) : Gen.LexAny F := by
  obtain ⟨h2, h4, h5, h6, h7, h8⟩ := hs
  have hNN : 0 < ⟪F.N 3, F.N 3⟫ := real_inner_self_pos.mpr (n3_ne_zero F)
  rcases hT with hR | hR
  · refine lexAny_of_tiltLex (by norm_num) F rimP0 rimP0_inj rimP0_cyc ?_ ?_ hu hlex hR
    · intro t ht
      simp only [UP0, Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl | rfl
      · exact Or.inr ⟨h3, hNN⟩
      exacts [Or.inl h6, Or.inl h7, Or.inl h8]
    · intro t ht
      simp only [DnP0, Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl
      exacts [Or.inl h2, Or.inl h4, Or.inl h5]
  · refine lexAny_of_tiltLex (by norm_num) F rimP3 rimP3_inj rimP3_cyc ?_ ?_ hu hlex hR
    · intro t ht
      simp only [UP3, Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl
      exacts [Or.inl h6, Or.inl h7, Or.inl h8]
    · intro t ht
      simp only [DnP3, Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl | rfl
      · exact Or.inl h2
      · exact Or.inr ⟨h3, by rw [inner_neg_right]; linarith⟩
      exacts [Or.inl h4, Or.inl h5]

end Minimality.T24.Q45
