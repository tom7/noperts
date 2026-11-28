module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination

/-!
# SupportStep: Theorem M (support differences are not monotone round the circle)

Mathlib-only formalization of the planar support-difference step identity and cyclic
contradiction lemma:
* `cr`, `dot2`, `len2`, `supportD`: 2D cross product, inner product, Euclidean length,
  and signed support-difference quotient `D(p, m) = cr(p, m) / |m|`.
* `supportStep_identity` (GD1): for `m ≠ 0` and `m' ≠ 0`,
  `cr(m, m') * (D(p, m') - D(p, m)) = (|m| |m'| - ⟨m, m'⟩) * (⟨p, m⟩ / |m| + ⟨p, m'⟩ / |m'|)`.
* `supportStep_mono`, `supportStep_strict` (GD1): monotonicity and strictness when `cr(m, m') > 0`.
* `supportD_add_smul` (GD2): `D(p + c • m, m) = D(p, m)`.
* `supportStep_chain`, `supportStep_chain_contradiction`, `supportStep_chain_halfTurn` (GD3):
  around any counterclockwise cycle (in particular, a half-turn `u₀, …, uₙ₋₁` extended by
  antipodes), nonnegativity of `⟨pₖ, mₖ⟩` and `⟨pₖ, mₖ₊₁⟩` forces all inner products to vanish.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Minimality.SupportStep

/-- 2D cross product `m.1 * m'.2 - m.2 * m'.1`. -/
def cr (m m' : ℝ × ℝ) : ℝ :=
  m.1 * m'.2 - m.2 * m'.1

/-- 2D dot product `m.1 * m'.1 + m.2 * m'.2`. -/
def dot2 (m m' : ℝ × ℝ) : ℝ :=
  m.1 * m'.1 + m.2 * m'.2

/-- 2D Euclidean length `√(m.1² + m.2²)`. -/
noncomputable def len2 (m : ℝ × ℝ) : ℝ :=
  Real.sqrt (m.1 ^ 2 + m.2 ^ 2)

/-- Support-difference quotient `D(p, m) = cr(p, m) / |m|`. -/
noncomputable def supportD (p m : ℝ × ℝ) : ℝ :=
  cr p m / len2 m

@[simp] theorem cr_self (m : ℝ × ℝ) : cr m m = 0 := by
  simp only [cr]; ring

theorem cr_antisymm (m m' : ℝ × ℝ) : cr m m' = -cr m' m := by
  simp only [cr]; ring

theorem cr_add_left (a b m : ℝ × ℝ) : cr (a + b) m = cr a m + cr b m := by
  simp only [cr, Prod.fst_add, Prod.snd_add]; ring

theorem cr_smul_left (c : ℝ) (a m : ℝ × ℝ) : cr (c • a) m = c * cr a m := by
  simp only [cr, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

theorem ne_zero_of_cr_pos {m m' : ℝ × ℝ} (h : 0 < cr m m') : m ≠ 0 ∧ m' ≠ 0 := by
  constructor <;> rintro rfl <;> simp only [cr, Prod.fst_zero, Prod.snd_zero, zero_mul, mul_zero,
    sub_self] at h <;> exact lt_irrefl 0 h

theorem len2_pos {m : ℝ × ℝ} (hm : m ≠ 0) : 0 < len2 m := by
  rw [len2, Real.sqrt_pos]
  by_contra h
  push Not at h
  have h1 : m.1 ^ 2 ≤ 0 := by nlinarith [sq_nonneg m.2]
  have h2 : m.2 ^ 2 ≤ 0 := by nlinarith [sq_nonneg m.1]
  have hm1 : m.1 = 0 := sq_eq_zero_iff.mp (le_antisymm h1 (sq_nonneg m.1))
  have hm2 : m.2 = 0 := sq_eq_zero_iff.mp (le_antisymm h2 (sq_nonneg m.2))
  exact hm (Prod.ext hm1 hm2)

theorem len2_sq {m : ℝ × ℝ} : len2 m ^ 2 = m.1 ^ 2 + m.2 ^ 2 :=
  Real.sq_sqrt (by positivity)

theorem len2_mul_sq_sub_dot2_sq (m m' : ℝ × ℝ) :
    (len2 m * len2 m') ^ 2 - dot2 m m' ^ 2 = cr m m' ^ 2 := by
  rw [mul_pow, len2_sq, len2_sq]
  simp only [dot2, cr]
  ring

theorem len2_mul_sub_dot2_pos {m m' : ℝ × ℝ} (hcr : cr m m' ≠ 0) :
    0 < len2 m * len2 m' - dot2 m m' := by
  have hsq : dot2 m m' ^ 2 < (len2 m * len2 m') ^ 2 := by
    have hp : 0 < cr m m' ^ 2 := sq_pos_of_ne_zero hcr
    linarith [len2_mul_sq_sub_dot2_sq m m']
  have hnonneg : 0 ≤ len2 m * len2 m' := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hlt : dot2 m m' < len2 m * len2 m' := by
    by_contra hle
    push Not at hle
    nlinarith [sq_nonneg (len2 m * len2 m' - dot2 m m')]
  linarith

/-! ## GD1: STEP identity, monotonicity, and strictness -/

/-- **STEP identity (GD1):** for nonzero `m, m' : ℝ × ℝ`,
`cr(m, m') * (D(p, m') - D(p, m)) = (|m| |m'| - ⟨m, m'⟩) * (⟨p, m⟩ / |m| + ⟨p, m'⟩ / |m'|)`. -/
theorem supportStep_identity (p m m' : ℝ × ℝ) (hm : m ≠ 0) (hm' : m' ≠ 0) :
    cr m m' * (supportD p m' - supportD p m) =
      (len2 m * len2 m' - dot2 m m') * (dot2 p m / len2 m + dot2 p m' / len2 m') := by
  have h1 : len2 m ≠ 0 := (len2_pos hm).ne'
  have h2 : len2 m' ≠ 0 := (len2_pos hm').ne'
  simp only [supportD]
  field_simp
  have hs1 : len2 m ^ 2 = m.1 ^ 2 + m.2 ^ 2 := len2_sq
  have hs2 : len2 m' ^ 2 = m'.1 ^ 2 + m'.2 ^ 2 := len2_sq
  simp only [cr, dot2]
  linear_combination
    -((p.1 * m.1 + p.2 * m.2) * len2 m * hs2 + (p.1 * m'.1 + p.2 * m'.2) * len2 m' * hs1)

/-- **STEP monotonicity (GD1):** if `cr(m, m') > 0` and `⟨p, m⟩ ≥ 0`, `⟨p, m'⟩ ≥ 0`,
then `D(p, m) ≤ D(p, m')`. -/
theorem supportStep_mono {p m m' : ℝ × ℝ} (hcr : 0 < cr m m')
    (hpm : 0 ≤ dot2 p m) (hpm' : 0 ≤ dot2 p m') :
    supportD p m ≤ supportD p m' := by
  obtain ⟨hm, hm'⟩ := ne_zero_of_cr_pos hcr
  have hid := supportStep_identity p m m' hm hm'
  have hdiff : 0 ≤ len2 m * len2 m' - dot2 m m' := (len2_mul_sub_dot2_pos hcr.ne').le
  have hsum : 0 ≤ dot2 p m / len2 m + dot2 p m' / len2 m' :=
    add_nonneg (div_nonneg hpm (len2_pos hm).le) (div_nonneg hpm' (len2_pos hm').le)
  have hprod : 0 ≤ cr m m' * (supportD p m' - supportD p m) := by
    rw [hid]
    exact mul_nonneg hdiff hsum
  have hsub : 0 ≤ supportD p m' - supportD p m := nonneg_of_mul_nonneg_right hprod hcr
  linarith

/-- **STEP strictness (GD1):** if `cr(m, m') > 0`, `⟨p, m⟩ ≥ 0`, `⟨p, m'⟩ ≥ 0`, and one of
the two inner products is strictly positive, then `D(p, m) < D(p, m')`. -/
theorem supportStep_strict {p m m' : ℝ × ℝ} (hcr : 0 < cr m m')
    (hpm : 0 ≤ dot2 p m) (hpm' : 0 ≤ dot2 p m') (hpos : 0 < dot2 p m ∨ 0 < dot2 p m') :
    supportD p m < supportD p m' := by
  obtain ⟨hm, hm'⟩ := ne_zero_of_cr_pos hcr
  have hid := supportStep_identity p m m' hm hm'
  have hdiff : 0 < len2 m * len2 m' - dot2 m m' := len2_mul_sub_dot2_pos hcr.ne'
  have hsum : 0 < dot2 p m / len2 m + dot2 p m' / len2 m' := by
    rcases hpos with h | h
    · exact add_pos_of_pos_of_nonneg (div_pos h (len2_pos hm)) (div_nonneg hpm' (len2_pos hm').le)
    · exact add_pos_of_nonneg_of_pos (div_nonneg hpm (len2_pos hm).le) (div_pos h (len2_pos hm'))
  have hprod : 0 < cr m m' * (supportD p m' - supportD p m) := by
    rw [hid]
    exact mul_pos hdiff hsum
  have hsub : 0 < supportD p m' - supportD p m := pos_of_mul_pos_right hprod hcr.le
  linarith

/-- **STEP equality converse:** if `cr(m, m') > 0`, `⟨p, m⟩ ≥ 0`, `⟨p, m'⟩ ≥ 0`, and
`D(p, m) = D(p, m')`, then `⟨p, m⟩ = 0` and `⟨p, m'⟩ = 0`. -/
theorem supportStep_eq_zero {p m m' : ℝ × ℝ} (hcr : 0 < cr m m')
    (hpm : 0 ≤ dot2 p m) (hpm' : 0 ≤ dot2 p m') (heq : supportD p m = supportD p m') :
    dot2 p m = 0 ∧ dot2 p m' = 0 := by
  by_contra h
  rw [not_and_or] at h
  have hpos : 0 < dot2 p m ∨ 0 < dot2 p m' := by
    rcases h with h1 | h2
    · exact Or.inl (lt_of_le_of_ne hpm (Ne.symm h1))
    · exact Or.inr (lt_of_le_of_ne hpm' (Ne.symm h2))
  exact (supportStep_strict hcr hpm hpm' hpos).ne heq

/-! ## GD2: Continuity along the generator -/

/-- **Continuity (GD2):** `D(p + c • m, m) = D(p, m)` for any scalar `c`. -/
theorem supportD_add_smul (p m : ℝ × ℝ) (c : ℝ) :
    supportD (p + c • m) m = supportD p m := by
  simp only [supportD, cr_add_left, cr_smul_left, cr_self, mul_zero, add_zero]

/-! ## GD3: Cyclic chain theorem (Theorem M) -/

private theorem zmod_sum_shift {N : ℕ} [NeZero N] (f : ZMod N → ℝ) :
    ∑ k : ZMod N, f (k + 1) = ∑ k : ZMod N, f k :=
  Equiv.sum_comp (Equiv.addRight (1 : ZMod N)) f

/-- **Theorem M (general cyclic form, GD3):** around any counterclockwise cycle
`m : ZMod N → ℝ × ℝ` (`cr(m k, m (k + 1)) > 0`) with `p (k + 1) - p k = c • m (k + 1)`,
nonnegativity of `⟨p k, m k⟩` and `⟨p k, m (k + 1)⟩` forces every step to be an equality and
all these inner products to vanish. -/
theorem supportStep_chain {N : ℕ} [NeZero N]
    (m p : ZMod N → ℝ × ℝ)
    (hccw : ∀ k : ZMod N, 0 < cr (m k) (m (k + 1)))
    (hcont : ∀ k : ZMod N, ∃ c : ℝ, p (k + 1) - p k = c • m (k + 1))
    (hge : ∀ k : ZMod N, 0 ≤ dot2 (p k) (m k) ∧ 0 ≤ dot2 (p k) (m (k + 1))) :
    ∀ k : ZMod N, dot2 (p k) (m k) = 0 ∧ dot2 (p k) (m (k + 1)) = 0 := by
  have hstep : ∀ k : ZMod N, supportD (p k) (m k) ≤ supportD (p (k + 1)) (m (k + 1)) := by
    intro k
    obtain ⟨c, hc⟩ := hcont k
    have hp : p (k + 1) = p k + c • m (k + 1) := by rw [← hc]; ext <;> simp
    rw [hp, supportD_add_smul]
    exact supportStep_mono (hccw k) (hge k).1 (hge k).2
  have hsum_zero : ∑ k : ZMod N, (supportD (p (k + 1)) (m (k + 1)) - supportD (p k) (m k)) = 0 := by
    rw [Finset.sum_sub_distrib, zmod_sum_shift (fun k => supportD (p k) (m k)), sub_self]
  have heach : ∀ k ∈ (Finset.univ : Finset (ZMod N)),
      supportD (p (k + 1)) (m (k + 1)) - supportD (p k) (m k) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => sub_nonneg.mpr (hstep k))).mp hsum_zero
  intro k
  obtain ⟨c, hc⟩ := hcont k
  have hp : p (k + 1) = p k + c • m (k + 1) := by rw [← hc]; ext <;> simp
  have heq : supportD (p k) (m k) = supportD (p k) (m (k + 1)) := by
    have hk := heach k (Finset.mem_univ k)
    rw [hp, supportD_add_smul] at hk
    linarith
  exact supportStep_eq_zero (hccw k) (hge k).1 (hge k).2 heq

/-- **Corollary (GD3):** if in addition at least one inner product `⟨p k, m k⟩` or
`⟨p k, m (k + 1)⟩` is strictly positive, we obtain a contradiction. -/
theorem supportStep_chain_contradiction {N : ℕ} [NeZero N]
    (m p : ZMod N → ℝ × ℝ)
    (hccw : ∀ k : ZMod N, 0 < cr (m k) (m (k + 1)))
    (hcont : ∀ k : ZMod N, ∃ c : ℝ, p (k + 1) - p k = c • m (k + 1))
    (hge : ∀ k : ZMod N, 0 ≤ dot2 (p k) (m k) ∧ 0 ≤ dot2 (p k) (m (k + 1)))
    (hpos : ∃ k : ZMod N, 0 < dot2 (p k) (m k) ∨ 0 < dot2 (p k) (m (k + 1))) :
    False := by
  have hall := supportStep_chain m p hccw hcont hge
  obtain ⟨k, hk | hk⟩ := hpos
  · exact hk.ne' (hall k).1
  · exact hk.ne' (hall k).2

/-- Half-turn extension of `u : Fin n → ℝ × ℝ` to `2n` directions `m : ZMod (2 * n) → ℝ × ℝ`
given by `m i = u i` for `i < n` and `m (n + i) = -u i` for `i < n`. -/
def halfTurnExt {n : ℕ} [NeZero n] (u : Fin n → ℝ × ℝ) (k : ZMod (2 * n)) : ℝ × ℝ :=
  haveI : NeZero (2 * n) := ⟨Nat.mul_ne_zero two_ne_zero (NeZero.ne n)⟩
  if h : ZMod.val k < n then u ⟨ZMod.val k, h⟩
  else -u ⟨ZMod.val k - n, by have hk := ZMod.val_lt k; omega⟩

theorem halfTurnExt_ccw {n : ℕ} [NeZero n] (u : Fin n → ℝ × ℝ)
    (hstep : ∀ i : ℕ, (hi : i + 1 < n) → 0 < cr (u ⟨i, by omega⟩) (u ⟨i + 1, hi⟩))
    (hwrap : 0 < cr (u ⟨0, NeZero.pos n⟩) (u ⟨n - 1, Nat.sub_lt (NeZero.pos n) Nat.one_pos⟩)) :
    ∀ k : ZMod (2 * n), 0 < cr (halfTurnExt u k) (halfTurnExt u (k + 1)) := by
  intro k
  have : NeZero (2 * n) := ⟨Nat.mul_ne_zero two_ne_zero (NeZero.ne n)⟩
  have hval : ZMod.val (k + 1) = (ZMod.val k + 1) % (2 * n) := by
    rw [ZMod.val_add, ZMod.val_one_eq_one_mod]
    simp [Nat.add_mod]
  have hk := ZMod.val_lt k
  by_cases h1 : ZMod.val k + 1 < n
  · have hk0 : ZMod.val k < n := by omega
    have hk1val : ZMod.val (k + 1) = ZMod.val k + 1 := by rw [hval, Nat.mod_eq_of_lt (by omega)]
    have hk1 : ZMod.val (k + 1) < n := by omega
    simp only [halfTurnExt, hk0, ↓reduceDIte, hk1]
    have heq : (⟨ZMod.val (k + 1), hk1⟩ : Fin n) = ⟨ZMod.val k + 1, h1⟩ := Fin.ext hk1val
    rw [heq]
    exact hstep (ZMod.val k) h1
  · by_cases h2 : ZMod.val k < n
    · have hkn : ZMod.val k = n - 1 := by omega
      have hk1val : ZMod.val (k + 1) = n := by rw [hval, Nat.mod_eq_of_lt (by omega)]; omega
      have hk1 : ¬ ZMod.val (k + 1) < n := by omega
      simp only [halfTurnExt, h2, ↓reduceDIte, hk1]
      have heq1 : (⟨ZMod.val k, h2⟩ : Fin n) = ⟨n - 1, Nat.sub_lt (NeZero.pos n) Nat.one_pos⟩ :=
        Fin.ext hkn
      have heq2 : (⟨ZMod.val (k + 1) - n, by have := ZMod.val_lt (k + 1); omega⟩ : Fin n) =
          ⟨0, NeZero.pos n⟩ := Fin.ext (by dsimp; omega)
      rw [heq1, heq2]
      have hcr : cr (u ⟨n - 1, Nat.sub_lt (NeZero.pos n) Nat.one_pos⟩) (-u ⟨0, NeZero.pos n⟩) =
          cr (u ⟨0, NeZero.pos n⟩) (u ⟨n - 1, Nat.sub_lt (NeZero.pos n) Nat.one_pos⟩) := by
        simp only [cr, Prod.fst_neg, Prod.snd_neg]; ring
      rw [hcr]; exact hwrap
    · by_cases h3 : ZMod.val k + 1 < 2 * n
      · have hk1val : ZMod.val (k + 1) = ZMod.val k + 1 := by rw [hval, Nat.mod_eq_of_lt h3]
        have hk1 : ¬ ZMod.val (k + 1) < n := by omega
        simp only [halfTurnExt, h2, ↓reduceDIte, hk1]
        have heq : (⟨ZMod.val (k + 1) - n, by have := ZMod.val_lt (k + 1); omega⟩ : Fin n) =
            ⟨(ZMod.val k - n) + 1, by omega⟩ := Fin.ext (by dsimp; omega)
        rw [heq]
        have hneg : cr (-u ⟨ZMod.val k - n, by omega⟩) (-u ⟨(ZMod.val k - n) + 1, by omega⟩) =
            cr (u ⟨ZMod.val k - n, by omega⟩) (u ⟨(ZMod.val k - n) + 1, by omega⟩) := by
          simp only [cr, Prod.fst_neg, Prod.snd_neg]; ring
        rw [hneg]
        exact hstep (ZMod.val k - n) (by omega)
      · have hkn : ZMod.val k = 2 * n - 1 := by omega
        have hk1val : ZMod.val (k + 1) = 0 := by
          have : ZMod.val k + 1 = 2 * n := by omega
          rw [hval, this, Nat.mod_self]
        have hk1 : ZMod.val (k + 1) < n := by rw [hk1val]; exact NeZero.pos n
        simp only [halfTurnExt, h2, ↓reduceDIte, hk1]
        have heq1 : (⟨ZMod.val k - n, by omega⟩ : Fin n) =
            ⟨n - 1, Nat.sub_lt (NeZero.pos n) Nat.one_pos⟩ := Fin.ext (by dsimp; omega)
        have heq2 : (⟨ZMod.val (k + 1), hk1⟩ : Fin n) = ⟨0, NeZero.pos n⟩ := Fin.ext hk1val
        rw [heq1, heq2]
        have hcr : cr (-u ⟨n - 1, Nat.sub_lt (NeZero.pos n) Nat.one_pos⟩) (u ⟨0, NeZero.pos n⟩) =
            cr (u ⟨0, NeZero.pos n⟩) (u ⟨n - 1, Nat.sub_lt (NeZero.pos n) Nat.one_pos⟩) := by
          simp only [cr, Prod.fst_neg, Prod.snd_neg]; ring
        rw [hcr]; exact hwrap

/-- **Theorem M (half-turn `2n` form, GD3):** if `u₀, …, uₙ₋₁` span less than a half turn in
strict counterclockwise order (`cr(uᵢ, uᵢ₊₁) > 0` and `cr(u₀, uₙ₋₁) > 0`) and `p` satisfies
continuity + nonnegativity around the `2n`-cycle `halfTurnExt u`, all inner products vanish. -/
theorem supportStep_chain_halfTurn {n : ℕ} [NeZero n]
    (u : Fin n → ℝ × ℝ)
    (hstep : ∀ i : ℕ, (hi : i + 1 < n) → 0 < cr (u ⟨i, by omega⟩) (u ⟨i + 1, hi⟩))
    (hwrap : 0 < cr (u ⟨0, NeZero.pos n⟩) (u ⟨n - 1, Nat.sub_lt (NeZero.pos n) Nat.one_pos⟩))
    (p : ZMod (2 * n) → ℝ × ℝ)
    (hcont : ∀ k : ZMod (2 * n), ∃ c : ℝ, p (k + 1) - p k = c • halfTurnExt u (k + 1))
    (hge : ∀ k : ZMod (2 * n),
      0 ≤ dot2 (p k) (halfTurnExt u k) ∧ 0 ≤ dot2 (p k) (halfTurnExt u (k + 1))) :
    ∀ k : ZMod (2 * n),
      dot2 (p k) (halfTurnExt u k) = 0 ∧ dot2 (p k) (halfTurnExt u (k + 1)) = 0 :=
  have : NeZero (2 * n) := ⟨Nat.mul_ne_zero two_ne_zero (NeZero.ne n)⟩
  supportStep_chain (halfTurnExt u) p (halfTurnExt_ccw u hstep hwrap) hcont hge

end Minimality.SupportStep
