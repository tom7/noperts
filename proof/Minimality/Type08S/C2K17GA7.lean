module

public import Minimality.Type08S.C2K17GA6

@[expose] public section


/-!
# K17GA / GA7: S1.3a lex lemma (cycle `(a,d,b,a',b')`, `α4 = 1`)
-/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

theorem lexLt_fst_le' {p q : ℝ × ℝ} (h : LexLt p q) : p.1 ≤ q.1 := by
  rcases h with h | ⟨h, _⟩
  · exact h.le
  · exact h.le

set_option maxHeartbeats 3200000 in
/-- Cycle `(a,d,b,a',b') = 0..4`: `z4 < z0`, `a (z0 - z1) + b (z2 - z1) < 0` (`a,b > 0`) and `z2 ≤ z1 → z3 < z2`. -/
theorem k17ga_lexUni5_A41 (z w : ZMod 5 → ℝ) (hinj : ∀ i j, z i = z j → w i = w j → i = j) {α β : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (H0 : z 4 < z 0) (HU : α * (z 0 - z 1) + β * (z 2 - z 1) < 0)
    (Hz : z 2 ≤ z 1 → z 3 < z 2) : LexUni z w := by
  have tot : ∀ i j : ZMod 5, i ≠ j → LexLt (z i, w i) (z j, w j) ∨ LexLt (z j, w j) (z i, w i) := by
    intro i j hij
    apply lexLt_total
    intro h; exact hij (hinj i j (congrArg Prod.fst h) (congrArg Prod.snd h))
  have le : ∀ i j, LexLt (z i, w i) (z j, w j) → z i ≤ z j := fun i j h => lexLt_fst_le' h
  obtain ⟨s0, s1, s2, s3, s4⟩ := z5_add
  obtain ⟨t0, t1, t2, t3, t4⟩ := k17f_zsub
  have L40 : LexLt (z 4, w 4) (z 0, w 0) := Or.inl H0
  rcases tot 1 0 (by decide) with h10 | h01
  · refine k17f_lexUni5_of_peak z w hinj 0 ?_ ?_
    · simp only [t0, s0]; exact ⟨L40, h10⟩
    · intro i hi
      rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
      · exact absurd rfl hi
      · simp only [t1, s1]; rintro ⟨h, -⟩; exact lexLt_asymm h10 h
      · simp only [t2, s2]; rintro ⟨h, -⟩
        have := le _ _ h10; have := le _ _ h
        nlinarith
      · simp only [t3, s3]; rintro ⟨h, -⟩
        have := le _ _ h10; have := le _ _ h
        by_cases hc : z 2 ≤ z 1
        · have := Hz hc; linarith
        · push Not at hc; nlinarith
      · simp only [t4, s4]; rintro ⟨-, h⟩; have := le _ _ h; linarith
  · rcases tot 2 1 (by decide) with h21 | h12
    · refine k17f_lexUni5_of_peak z w hinj 1 ?_ ?_
      · simp only [t1, s1]; exact ⟨h01, h21⟩
      · intro i hi
        rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
        · simp only [t0, s0]; rintro ⟨-, h⟩; exact lexLt_asymm h01 h
        · exact absurd rfl hi
        · simp only [t2, s2]; rintro ⟨h, -⟩; exact lexLt_asymm h21 h
        · simp only [t3, s3]; rintro ⟨h, -⟩
          have := le _ _ h; have := le _ _ h01; have := le _ _ h21
          have := Hz this; linarith
        · simp only [t4, s4]; rintro ⟨-, h⟩; have := le _ _ h; linarith
    · rcases tot 3 2 (by decide) with h32 | h23
      · refine k17f_lexUni5_of_peak z w hinj 2 ?_ ?_
        · simp only [t2, s2]; exact ⟨h12, h32⟩
        · intro i hi
          rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
          · simp only [t0, s0]; rintro ⟨-, h⟩; exact lexLt_asymm h01 h
          · simp only [t1, s1]; rintro ⟨-, h⟩; exact lexLt_asymm h12 h
          · exact absurd rfl hi
          · simp only [t3, s3]; rintro ⟨h, -⟩; exact lexLt_asymm h32 h
          · simp only [t4, s4]; rintro ⟨-, h⟩; have := le _ _ h; linarith
      · rcases tot 4 3 (by decide) with h43 | h34
        · refine k17f_lexUni5_of_peak z w hinj 3 ?_ ?_
          · simp only [t3, s3]; exact ⟨h23, h43⟩
          · intro i hi
            rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
            · simp only [t0, s0]; rintro ⟨-, h⟩; exact lexLt_asymm h01 h
            · simp only [t1, s1]; rintro ⟨-, h⟩; exact lexLt_asymm h12 h
            · simp only [t2, s2]; rintro ⟨-, h⟩; exact lexLt_asymm h23 h
            · exact absurd rfl hi
            · simp only [t4, s4]; rintro ⟨-, h⟩; have := le _ _ h; linarith
        · exfalso
          have := le _ _ h01; have := le _ _ h12; have := le _ _ h23; have := le _ _ h34
          linarith


set_option maxHeartbeats 3200000 in
/-- **The S1.3a cell** (`α4 = 1`): pentagon `(a,d,b,a',b')` at `a - c'`, frame `(b-d, c-d, a-c')`, tilt `(1, λ)`.
Facts (depth at `a - c'`): `d > b`, `b > a'`, `a > b'`. -/
theorem k17ga_a41_cell {a a' b b' c c' d : ℝ³} {α1 α4 β1 γ4 β6 : ℝ} (hdet : det3 (a - d) (b - d) (c - d) ≠ 0)
    (hc' : c' = d + α1 • (a - d) + β1 • (b - d)) (hb' : b' = d + α4 • (a - d) + γ4 • (c - d))
    (ha' : a' = d + β6 • (b - d) + (1 : ℝ) • (c - d)) (hα1 : 1 < α1) (hβ1 : 0 < β1) (hα4 : 1 ≤ α4)
    (hγ4 : 1 < γ4) (hb6 : 1 ≤ β6)
    (hα41 : α4 = 1) (hz : ⟪c - d, a - c'⟫ < 0)
    (hU : (α1 - 1) * ⟪a - d, a - c'⟫ + β1 * ⟪b - d, a - c'⟫ < 0)
    (hzz : ⟪b - d, a - c'⟫ ≤ 0 → ⟪c - d, a - c'⟫ < (1 - β6) * ⟪b - d, a - c'⟫) :
    HasLexCell (V8 a a' b b' c c' d) := by
  obtain ⟨τ, hτdef⟩ : ∃ τ, τ = 1 / (α1 - 1) := ⟨_, rfl⟩
  have hα1' : 0 < α1 - 1 := by linarith
  have hτ : 0 < τ := by rw [hτdef]; positivity
  have hτα : τ * (α1 - 1) = 1 := by rw [hτdef]; field_simp
  set P := b - d with hP
  set Q := c - d with hQ
  set R := a - c' with hR
  have hRv : R = (1 - α1) • (a - d) - β1 • (b - d) := by rw [hR, hc']; module
  have hpR : a - d = (-τ) • R + (-(β1 * τ)) • P := by
    rw [hRv, hP]
    have : a - d = (a - d) := rfl
    match_scalars <;> nlinarith
  have hΔ : det3 P Q R ≠ 0 := by
    have e : det3 P Q R = (1 - α1) * det3 (a - d) (b - d) (c - d) := by
      rw [hRv, hP, hQ]
      simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; ring
    rw [e]; exact mul_ne_zero (by linarith) hdet
  have Ea : fpoint P Q R d (-(β1 * τ), 0, -τ) = a := by
    rw [k17ga_fp]; have h := hpR
    linear_combination (norm := module) (-1 : ℝ) • h
  have Ed : fpoint P Q R d (0, 0, 0) = d := by rw [k17ga_fp]; module
  have Eb : fpoint P Q R d (1, 0, 0) = b := by rw [k17ga_fp, hP]; module
  have Ec : fpoint P Q R d (0, 1, 0) = c := by rw [k17ga_fp, hQ]; module
  have Ea' : fpoint P Q R d (β6, 1, 0) = a' := by rw [k17ga_fp, ha', hP, hQ]; module
  have Eb' : fpoint P Q R d (-(α4 * β1 * τ), γ4, -(α4 * τ)) = b' := by
    rw [k17ga_fp, hb', hQ]; have h := hpR
    linear_combination (norm := module) (-α4) • h
  have Ec' : fpoint P Q R d (-(β1 * τ), 0, -(τ + 1)) = c' := by
    rw [k17ga_fp]; have h := hpR
    have : c' = a - R := by rw [hR]; abel
    rw [this]
    linear_combination (norm := module) (-1 : ℝ) • h
  have hz' : ∀ t : ℝ × ℝ × ℝ, ⟪fpoint P Q R d t, R⟫ = ⟪d, R⟫ + t.1 * ⟪P, R⟫ + t.2.1 * ⟪Q, R⟫ + t.2.2 * ⟪R, R⟫ :=
    fun t => inner_fpoint _ _ _ _ _ _
  have hpRR : ⟪a - d, R⟫ = -τ * ⟪R, R⟫ + (-(β1 * τ)) * ⟪P, R⟫ := by
    rw [hpR, inner_add_left, real_inner_smul_left, real_inner_smul_left]
  have hRR : 0 < ⟪R, R⟫ := real_inner_self_pos.2 (k17ga_r0 hΔ)
  have hR0 : R ≠ 0 := k17ga_r0 hΔ
  refine ⟨R, hR0, ?_⟩
  refine k3_cell_gen (V8 a a' b b' c c' d) P Q R d hΔ (k := 5) (by norm_num) (k17gaR3 τ β1 α4 γ4 β6)
    (k17gaR3_inj hτ hβ1 hα4 (by linarith)) (u1 := 1) (u2 := 0) (t1 := 0) (t2 := 1) (by norm_num) ?_ ?_ ?_ ?_
  · intro i
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
    · simp only [k17gaR3, pc5_0, Ea]; simp [V8]
    · simp only [k17gaR3, pc5_1, Ed]; simp [V8]
    · simp only [k17gaR3, pc5_2, Eb]; simp [V8]
    · simp only [k17gaR3, pc5_3, Ea']; simp [V8]
    · simp only [k17gaR3, pc5_4, Eb']; simp [V8]
  · intro lam h0 h1 D hD
    refine k17ga_r3_tsc hD hτ hβ1 hα4 hγ4 hb6 (by norm_num) (by simpa using h0) ?_
    simp only [mul_zero, add_zero, zero_add, mul_one]
    have : 0 ≤ (α4 - 1) * β1 * τ * lam := by
      have := mul_nonneg (mul_nonneg (sub_nonneg.2 hα4) hβ1.le) hτ.le
      exact mul_nonneg this h0.le
    nlinarith
  · intro y hy hyx
    have hV : y = fpoint P Q R d (-(β1 * τ), 0, -τ) ∨ y = fpoint P Q R d (0, 0, 0) ∨ y = fpoint P Q R d (1, 0, 0) ∨
        y = fpoint P Q R d (β6, 1, 0) ∨ y = fpoint P Q R d (-(α4 * β1 * τ), γ4, -(α4 * τ)) ∨
        y = fpoint P Q R d (0, 1, 0) ∨ y = fpoint P Q R d (-(β1 * τ), 0, -(τ + 1)) := by
      rw [Ea, Ed, Eb, Ea', Eb', Ec, Ec']
      simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
      tauto
    have hc1 : ∀ lam : ℝ, 0 < lam → lam < 1 → 0 < γ4 * (1 + lam * 0) + (α4 - 1) * β1 * τ * (0 + lam * 1) := by
      intro lam h0 h1
      have := mul_nonneg (mul_nonneg (sub_nonneg.2 hα4) hβ1.le) hτ.le
      nlinarith [mul_nonneg this h0.le]
    rcases hV with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hyx 0 (by simp only [k17gaR3, pc5_0])).elim
    · exact (hyx 1 (by simp only [k17gaR3, pc5_1])).elim
    · exact (hyx 2 (by simp only [k17gaR3, pc5_2])).elim
    · exact (hyx 3 (by simp only [k17gaR3, pc5_3])).elim
    · exact (hyx 4 (by simp only [k17gaR3, pc5_4])).elim
    · refine ⟨_, rfl, fun lam h0 h1 D hD i => ?_⟩
      exact (k17ga_r3_rest hD hτ hβ1 hα4 hγ4 hb6 (by norm_num) (by simpa using h0) (by
        simpa using hc1 lam h0 h1)).1 i
    · refine ⟨_, rfl, fun lam h0 h1 D hD i => ?_⟩
      exact (k17ga_r3_rest hD hτ hβ1 hα4 hγ4 hb6 (by norm_num) (by simpa using h0) (by
        simpa using hc1 lam h0 h1)).2 i
  · intro w hw
    refine k17ga_lexUni5_A41 _ w hw (α := α1 - 1) (β := β1) (by linarith) hβ1 ?_ ?_ ?_
    · simp only [k17gaR3, pc5_4, pc5_0, hz']
      subst hα41; nlinarith
    · simp only [k17gaR3, pc5_0, pc5_1, pc5_2, hz']
      rw [hpRR] at hU; nlinarith
    · simp only [k17gaR3, pc5_1, pc5_2, pc5_3, hz']
      intro h; have := hzz (by nlinarith); nlinarith

end C2
end Type08Sp
end Minimality
