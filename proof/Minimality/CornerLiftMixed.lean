module

public import Mathlib
public import Minimality.CornerLiftMax

/-!
# The pattern lift: constraint region, maximal points, the mixed lift and the K1 / K2 classification

Source: `CORNER-OFFOB1.md` sections 1-4 and 7 (steps 2 and 3), `CORNER-GENERALIZE.md` item 3.  Namespace
`Minimality.CornerEQ`, `Fin 3`.  `Q G ν = (liftM ν)ᵀ G (liftM ν)` is the Gram matrix of the lifted apex
(`lift_gram_apply`); the lift order is `N = ∑ ν`, as in `CornerLiftMax`.

* `liftSetPat G P`: `{ν ≥ 0 | P a b → (Q G ν)_ab ≤ 0 for a ≠ b}`; `liftSetP G = liftSetPat G (G a b ≤ 0)`:
  the entries that start `≤ 0` stay `≤ 0` (no obtuseness hypothesis).
  `zero_mem_liftSetPat`, `liftSetPat_isClosed`, `liftSetPat_isCompact` (`G` positive definite and some
  constrained pair `a ≠ b`; for `liftSetP` an entry `G_ab ≤ 0`), `exists_maximal_liftSetP`.
* `maximal_no_further_liftPat`: at a maximizer of `N` there is no further feasible lift (constraints of
  the original pattern, on the lifted matrix).
* `lift_single_apply`, `lift_one_mixed`: `G_ab ≤ 0`, `G_ac < 0`, `G_ac + G_bc < 0` give `ε > 0` with
  `(Q G (ε e_c))_ab < 0` and `(Q G (ε e_c))_ac < 0` (it contains `lift_one_nonpos` for these two entries).
* `exists_K_of_maximal`: classification at `H` for the pattern `{ab, ac}` (OB1x, vertex `a`):
  K2: `H_ab = H_ac = 0`; K1: `H_ab = 0 > H_ac`, `0 ≤ H_ac + H_bc`; or the same with `b`, `c` swapped.
  Only symmetry of `H` and the two constrained entries are used (no definiteness, no obtuseness, no `bc`
  hypothesis).
* `exists_lift_K` (combined): `G` positive definite, `G_ab, G_ac ≤ 0 < G_bc`: a maximizer `ν` of `N` on
  `liftSetP G` exists, `Q G ν` is positive definite and of the form K2 or K1.
-/

set_option autoImplicit false

namespace Minimality.CornerEQ

open Finset Matrix

@[expose] public section

/-- Feasible lifts for a pattern `P` of constrained entries. -/
def liftSetPat (G : Matrix (Fin 3) (Fin 3) ℝ) (P : Fin 3 → Fin 3 → Prop) : Set (Fin 3 → ℝ) :=
  {ν | 0 ≤ ν ∧ ∀ a b, a ≠ b → P a b → ((liftM ν)ᵀ * G * liftM ν) a b ≤ 0}

/-- The entries of `G` that start `≤ 0` stay `≤ 0` (the pattern lift). -/
def liftSetP (G : Matrix (Fin 3) (Fin 3) ℝ) : Set (Fin 3 → ℝ) :=
  liftSetPat G fun a b => G a b ≤ 0

theorem zero_mem_liftSetPat (G : Matrix (Fin 3) (Fin 3) ℝ) (P : Fin 3 → Fin 3 → Prop)
    (hP : ∀ a b, a ≠ b → P a b → G a b ≤ 0) : (0 : Fin 3 → ℝ) ∈ liftSetPat G P := by
  refine ⟨le_rfl, fun a b hab hp => ?_⟩
  have : liftM (0 : Fin 3 → ℝ) = 1 := by simp [liftM]
  simpa [this] using hP a b hab hp

theorem zero_mem_liftSetP (G : Matrix (Fin 3) (Fin 3) ℝ) : (0 : Fin 3 → ℝ) ∈ liftSetP G :=
  zero_mem_liftSetPat G _ fun _ _ _ h => h

theorem liftSetPat_isClosed (G : Matrix (Fin 3) (Fin 3) ℝ) (P : Fin 3 → Fin 3 → Prop) :
    IsClosed (liftSetPat G P) := by
  have : liftSetPat G P = Set.Ici 0 ∩ ⋂ a, ⋂ b, ⋂ (_ : a ≠ b), ⋂ (_ : P a b),
      {ν : Fin 3 → ℝ | ((liftM ν)ᵀ * G * liftM ν) a b ≤ 0} := by
    ext ν; simp [liftSetPat]
  rw [this]
  exact isClosed_Ici.inter (isClosed_iInter fun a => isClosed_iInter fun b =>
    isClosed_iInter fun _ => isClosed_iInter fun _ =>
      isClosed_le (continuous_liftGram G a b) continuous_const)

theorem liftSetPat_isBounded (G : Matrix (Fin 3) (Fin 3) ℝ) (hpd : G.PosDef)
    (P : Fin 3 → Fin 3 → Prop) (hex : ∃ a b, a ≠ b ∧ P a b) :
    Bornology.IsBounded (liftSetPat G P) := by
  have hG : G.IsSymm := by
    have := hpd.isHermitian
    simpa [Matrix.IsHermitian, Matrix.IsSymm] using this
  obtain ⟨a, b, hab, hPab⟩ := hex
  obtain ⟨m, hm, hq⟩ := exists_quad_lower G hpd
  set B : ℝ := ∑ a, ∑ j, |G a j| with hB
  set D : ℝ := |G a b| + 2 * B with hD
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  have key : ∀ ν ∈ liftSetPat G P, ‖ν‖ ≤ D / m + 1 := by
    rintro ν ⟨hν0, hν⟩
    set r := ‖ν‖ with hr
    have hr0 : 0 ≤ r := norm_nonneg _
    have hterm : ∀ i j, -(|G i j| * r) ≤ G i j * ν j := by
      intro i j
      have h1 : |ν j| ≤ r := by simpa [Real.norm_eq_abs] using norm_le_pi_norm ν j
      have : |G i j * ν j| ≤ |G i j| * r := by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      linarith [neg_abs_le (G i j * ν j)]
    have hrow : ∀ i, -(B * r) ≤ (G *ᵥ ν) i := by
      intro i
      have h1 : ∑ j, -(|G i j| * r) ≤ (G *ᵥ ν) i := by
        simp only [Matrix.mulVec, dotProduct]
        exact Finset.sum_le_sum fun j _ => hterm i j
      have h2 : ∑ j, |G i j| ≤ B :=
        Finset.single_le_sum (f := fun i => ∑ j, |G i j|)
          (fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _) (Finset.mem_univ i)
      have h3 : ∑ j, -(|G i j| * r) = -((∑ j, |G i j|) * r) := by
        simp [Finset.sum_neg_distrib, Finset.sum_mul]
      rw [h3] at h1
      nlinarith
    have h01 := hν a b hab hPab
    rw [lift_gram_apply G hG] at h01
    have hq3 := hq ν
    rw [← hr] at hq3
    have ha := hrow a
    have hb := hrow b
    have hC := neg_abs_le (G a b)
    have hmain : m * r ^ 2 ≤ -(G a b) + 2 * B * r := by linarith
    have hDnn : 0 ≤ D / m := by positivity
    by_cases hr1 : r ≤ 1
    · linarith
    · push Not at hr1
      have hab' : -(G a b) ≤ |G a b| * r := by
        nlinarith [neg_abs_le (G a b), abs_nonneg (G a b)]
      have h3 : m * r * r ≤ D * r := by rw [hD]; nlinarith
      have h4 : m * r ≤ D := le_of_mul_le_mul_right h3 (by linarith)
      have : r ≤ D / m := by rw [le_div_iff₀ hm]; linarith
      linarith
  refine (Metric.isBounded_iff_subset_closedBall 0).2 ⟨D / m + 1, fun ν hν => ?_⟩
  simpa using key ν hν

/-- Compactness: `G` positive definite and at least one constrained pair. -/
theorem liftSetPat_isCompact (G : Matrix (Fin 3) (Fin 3) ℝ) (hpd : G.PosDef)
    (P : Fin 3 → Fin 3 → Prop) (hex : ∃ a b, a ≠ b ∧ P a b) : IsCompact (liftSetPat G P) :=
  Metric.isCompact_of_isClosed_isBounded (liftSetPat_isClosed G P)
    (liftSetPat_isBounded G hpd P hex)

/-- `liftSetP G` is compact when `G` is positive definite and some entry `G_ab ≤ 0` (`a ≠ b`). -/
theorem liftSetP_isCompact (G : Matrix (Fin 3) (Fin 3) ℝ) (hpd : G.PosDef)
    (hex : ∃ a b, a ≠ b ∧ G a b ≤ 0) : IsCompact (liftSetP G) :=
  liftSetPat_isCompact G hpd _ hex

theorem exists_maximal_liftSetPat (G : Matrix (Fin 3) (Fin 3) ℝ) (hpd : G.PosDef)
    (P : Fin 3 → Fin 3 → Prop) (hP : ∀ a b, a ≠ b → P a b → G a b ≤ 0)
    (hex : ∃ a b, a ≠ b ∧ P a b) :
    ∃ ν ∈ liftSetPat G P, ∀ ν' ∈ liftSetPat G P, ∑ i, ν' i ≤ ∑ i, ν i := by
  obtain ⟨ν, hν, hmax⟩ := (liftSetPat_isCompact G hpd P hex).exists_isMaxOn
    ⟨0, zero_mem_liftSetPat G P hP⟩
    (continuous_finsetSum _ fun i _ => continuous_apply i).continuousOn
  exact ⟨ν, hν, fun ν' hν' => hmax hν'⟩

theorem exists_maximal_liftSetP (G : Matrix (Fin 3) (Fin 3) ℝ) (hpd : G.PosDef)
    (hex : ∃ a b, a ≠ b ∧ G a b ≤ 0) :
    ∃ ν ∈ liftSetP G, ∀ ν' ∈ liftSetP G, ∑ i, ν' i ≤ ∑ i, ν i :=
  exists_maximal_liftSetPat G hpd _ (fun _ _ _ h => h) hex

/-- At a maximizer of `N` on `liftSetPat G P` there is no further lift keeping the constrained entries
`≤ 0`. -/
theorem maximal_no_further_liftPat (G : Matrix (Fin 3) (Fin 3) ℝ) {P : Fin 3 → Fin 3 → Prop}
    {ν : Fin 3 → ℝ} (hν : ν ∈ liftSetPat G P)
    (hmax : ∀ ν' ∈ liftSetPat G P, ∑ i, ν' i ≤ ∑ i, ν i) {ν' : Fin 3 → ℝ} (hν' : 0 ≤ ν')
    (hf : ∀ a b, a ≠ b → P a b →
      ((liftM ν')ᵀ * ((liftM ν)ᵀ * G * liftM ν) * liftM ν') a b ≤ 0) : ν' = 0 := by
  have hmem : ν + liftM ν *ᵥ ν' ∈ liftSetPat G P :=
    ⟨add_nonneg hν.1 (liftM_mulVec_nonneg ν ν' hν.1 hν'), fun a b hab hp => by
      rw [← gram_comp]; exact hf a b hab hp⟩
  have h := hmax _ hmem
  rw [sum_liftTotal] at h
  have hN : 0 ≤ ∑ i, ν i := Finset.sum_nonneg fun i _ => hν.1 i
  have hN' : 0 ≤ ∑ i, ν' i := Finset.sum_nonneg fun i _ => hν' i
  have h0 : ∑ i, ν' i = 0 := by nlinarith
  ext i
  exact (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hν' i).1 h0 i (Finset.mem_univ i)

/-! ### The mixed lift -/

theorem lift_single_apply (G : Matrix (Fin 3) (Fin 3) ℝ) (hG : G.IsSymm) (d i j : Fin 3) (ε : ℝ) :
    ((liftM (Pi.single d ε))ᵀ * G * liftM (Pi.single d ε)) i j
      = G i j + ε * G i d + ε * G j d + ε * ε * G d d := by
  rw [lift_gram_apply G hG]
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  ring

theorem single_nonneg (d : Fin 3) {ε : ℝ} (hε : 0 ≤ ε) : 0 ≤ (Pi.single d ε : Fin 3 → ℝ) :=
  fun i => by
    by_cases h : i = d
    · subst h; simpa using hε
    · simp [h]

/-- Two strictly negative entries stay negative under a small lift along any axis `d`. -/
theorem lift_two_strict (G : Matrix (Fin 3) (Fin 3) ℝ) (hG : G.IsSymm) (d i j k l : Fin 3)
    (h1 : G i j < 0) (h2 : G k l < 0) :
    ∃ ε : ℝ, 0 < ε ∧ ((liftM (Pi.single d ε))ᵀ * G * liftM (Pi.single d ε)) i j < 0
      ∧ ((liftM (Pi.single d ε))ᵀ * G * liftM (Pi.single d ε)) k l < 0 := by
  have hc : ∀ i j : Fin 3, Continuous fun ε : ℝ => G i j + ε * G i d + ε * G j d + ε * ε * G d d :=
    fun i j => by fun_prop
  have e1 : ∀ᶠ ε in nhds (0 : ℝ), G i j + ε * G i d + ε * G j d + ε * ε * G d d < 0 :=
    (hc i j).continuousAt.eventually_lt continuousAt_const (by simpa using h1)
  have e2 : ∀ᶠ ε in nhds (0 : ℝ), G k l + ε * G k d + ε * G l d + ε * ε * G d d < 0 :=
    (hc k l).continuousAt.eventually_lt continuousAt_const (by simpa using h2)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 (e1.and e2)
  obtain ⟨r1, r2⟩ := hball (y := δ / 2)
    (by rw [Real.dist_eq, sub_zero, abs_of_pos (half_pos hδ)]; linarith)
  exact ⟨δ / 2, half_pos hδ, by rw [lift_single_apply G hG]; exact r1,
    by rw [lift_single_apply G hG]; exact r2⟩

/-- **The mixed lift.**  `G_ab ≤ 0`, `G_ac < 0` and `G_ac + G_bc < 0` (`G_bc` of either sign): lifting by
`ε e_c` makes both `(ab)` and `(ac)` strictly negative.  (`lift_one_nonpos` is the case `G_bc < 0`.) -/
theorem lift_one_mixed (G : Matrix (Fin 3) (Fin 3) ℝ) (hG : G.IsSymm) {a b c : Fin 3}
    (h0 : G a b ≤ 0) (h1 : G a c < 0) (h2 : G a c + G b c < 0) :
    ∃ ε : ℝ, 0 < ε ∧ ((liftM (Pi.single c ε))ᵀ * G * liftM (Pi.single c ε)) a b < 0
      ∧ ((liftM (Pi.single c ε))ᵀ * G * liftM (Pi.single c ε)) a c < 0 := by
  set m := min (-(G a c + G b c)) (-(G a c)) with hm
  have hm0 : 0 < m := lt_min (by linarith) (by linarith)
  have hm1 : m ≤ -(G a c + G b c) := min_le_left _ _
  have hm2 : m ≤ -(G a c) := min_le_right _ _
  set ε := m / (|G c c| + 1) with hε
  have hpos : 0 < |G c c| + 1 := by positivity
  have he0 : 0 < ε := by positivity
  have hcc : ε * |G c c| < m := by
    rw [hε, div_mul_eq_mul_div, div_lt_iff₀ hpos]; nlinarith [abs_nonneg (G c c)]
  have hcc' : ε * G c c < m := by have := le_abs_self (G c c); nlinarith
  refine ⟨ε, he0, ?_, ?_⟩
  · rw [lift_single_apply G hG]
    have : G a c + G b c + ε * G c c < 0 := by linarith
    nlinarith [mul_neg_of_pos_of_neg he0 this]
  · rw [lift_single_apply G hG]
    have : G a c + ε * G c c < 0 := by linarith
    nlinarith [mul_neg_of_pos_of_neg (by linarith : 0 < 1 + ε) this]

/-! ### Classification at a maximal point -/

/-- **K1 / K2 classification** (pattern `{ab, ac}`, vertex `a`).  `H` symmetric with `H_ab, H_ac ≤ 0`
admitting no nonzero further lift that keeps `(ab)` and `(ac)` nonpositive.  Then
K2: `H_ab = H_ac = 0`; or K1: `H_ab = 0 > H_ac` and `0 ≤ H_ac + H_bc`; or K1 with `b`, `c` swapped. -/
theorem exists_K_of_maximal (H : Matrix (Fin 3) (Fin 3) ℝ) (hH : H.IsSymm) {a b c : Fin 3}
    (h1 : H a b ≤ 0) (h2 : H a c ≤ 0)
    (hmax : ∀ ν' : Fin 3 → ℝ, 0 ≤ ν' → ((liftM ν')ᵀ * H * liftM ν') a b ≤ 0 →
      ((liftM ν')ᵀ * H * liftM ν') a c ≤ 0 → ν' = 0) :
    (H a b = 0 ∧ H a c = 0) ∨ (H a b = 0 ∧ H a c < 0 ∧ 0 ≤ H a c + H b c)
      ∨ (H a c = 0 ∧ H a b < 0 ∧ 0 ≤ H a b + H b c) := by
  have hs : ∀ i j, H i j = H j i := fun i j => hH.apply j i
  have nolift : ∀ (d : Fin 3) (ε : ℝ), 0 < ε →
      ((liftM (Pi.single d ε))ᵀ * H * liftM (Pi.single d ε)) a b ≤ 0 →
      ((liftM (Pi.single d ε))ᵀ * H * liftM (Pi.single d ε)) a c ≤ 0 → False := by
    intro d ε hε e1 e2
    have := congrFun (hmax _ (single_nonneg d hε.le) e1 e2) d
    simp at this
    exact hε.ne' this
  rcases h1.lt_or_eq with x | x <;> rcases h2.lt_or_eq with y | y
  · obtain ⟨ε, hε, e1, e2⟩ := lift_two_strict H hH a a b a c x y
    exact (nolift a ε hε e1.le e2.le).elim
  · right; right
    refine ⟨y, x, ?_⟩
    by_contra hneg
    push Not at hneg
    obtain ⟨ε, hε, e1, e2⟩ := lift_one_mixed H hH (a := a) (b := c) (c := b) h2 x
      (by rw [hs c b]; exact hneg)
    exact nolift b ε hε e2.le e1.le
  · right; left
    refine ⟨x, y, ?_⟩
    by_contra hneg
    push Not at hneg
    obtain ⟨ε, hε, e1, e2⟩ := lift_one_mixed H hH (a := a) (b := b) (c := c) h1 y hneg
    exact nolift c ε hε e1.le e2.le
  · left; exact ⟨x, y⟩

/-! ### Combined statement -/

theorem exists_lift_K (G : Matrix (Fin 3) (Fin 3) ℝ) (hpd : G.PosDef) {a b c : Fin 3}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (h1 : G a b ≤ 0) (h2 : G a c ≤ 0)
    (h3 : 0 < G b c) :
    ∃ ν ∈ liftSetP G, (∀ ν' ∈ liftSetP G, ∑ i, ν' i ≤ ∑ i, ν i) ∧
      ((liftM ν)ᵀ * G * liftM ν).PosDef ∧
      (let H := (liftM ν)ᵀ * G * liftM ν
       (H a b = 0 ∧ H a c = 0) ∨ (H a b = 0 ∧ H a c < 0 ∧ 0 ≤ H a c + H b c)
        ∨ (H a c = 0 ∧ H a b < 0 ∧ 0 ≤ H a b + H b c)) := by
  have hG : G.IsSymm := by
    have := hpd.isHermitian
    simpa [Matrix.IsHermitian, Matrix.IsSymm] using this
  obtain ⟨ν, hν, hmax⟩ := exists_maximal_liftSetP G hpd ⟨a, b, hab, h1⟩
  have hN : 0 ≤ ∑ i, ν i := Finset.sum_nonneg fun i _ => hν.1 i
  have hs : ((liftM ν)ᵀ * G * liftM ν).IsSymm := by
    simp [Matrix.IsSymm, Matrix.transpose_mul, hG.eq, Matrix.mul_assoc]
  refine ⟨ν, hν, hmax, lift_posDef G hpd ν hN, ?_⟩
  have hab' := hν.2 a b hab h1
  have hac' := hν.2 a c hac h2
  refine exists_K_of_maximal _ hs hab' hac' fun ν' hν' e1 e2 => ?_
  refine maximal_no_further_liftPat G hν hmax hν' fun x y hxy hp => ?_
  have hsy := lift_gram_symm _ hs ν'
  have hx : x = a ∨ x = b ∨ x = c := by omega
  have hy : y = a ∨ y = b ∨ y = c := by omega
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
    first
    | exact absurd rfl hxy
    | assumption
    | rwa [hsy]
    | exact absurd hp (by rw [hG.apply]; linarith)

end

end Minimality.CornerEQ
