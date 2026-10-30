module

public import Minimality.Type08S.P2TDefs

@[expose] public section

set_option relaxedAutoImplicit true
set_option autoImplicit true
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

private theorem det3_mid' {p q u : ℝ³} (x y : ℝ) :
    det3 p (x • q + y • u) u = x * det3 p q u := by
  simp only [det3_expand, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring

theorem tie_conv_T_L {a a' b b' c c' d : ℝ³} {F : OctFacets a a' b b' c c'} (hd : IsCap F d)
    (h : ∃ r : ℝ, c - a' = r • (b - d)) : F.abc'.f a' = F.abc'.f c := by
  obtain ⟨r, hr⟩ := h
  have hnd := F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  have hFc := F.abc'.neg c (by simp) (Ne.symm hnd.1.2.2.2.1) (Ne.symm hnd.2.2.1.2.1) hnd.2.2.2.2.1
  obtain ⟨-, -, -, ha'⟩ : 0 < F.ab'c.f a' / F.ab'c.f b ∧ 0 < F.abc'.f a' / F.abc'.f c ∧
      1 < F.ab'c.f a' / F.ab'c.f b + F.abc'.f a' / F.abc'.f c ∧
      a' = d + (F.ab'c.f a' / F.ab'c.f b) • (b - d) + (F.abc'.f a' / F.abc'.f c) • (c - d) :=
    hd.perm₁₂.Qac_coords'
  generalize F.ab'c.f a' / F.ab'c.f b = k at ha'
  generalize hq : F.abc'.f a' / F.abc'.f c = q at ha'
  have hv : (1 - q) • (c - d) + (-(r + k)) • (b - d) = 0 := by
    have : c - a' = r • (b - d) := hr
    rw [ha'] at this
    rw [← sub_eq_zero] at this
    rw [← this]; module
  have h0 := det3_mid' (p := a - d) (q := c - d) (u := b - d) (1 - q) (-(r + k))
  rw [hv] at h0
  have hz : det3 (a - d) 0 (b - d) = 0 := by simp [det3_expand]
  rw [hz] at h0
  have hq1 : q = 1 := by
    have := hd.det_Qac_ne
    rcases mul_eq_zero.mp h0.symm with h | h
    · linarith
    · exact absurd h this
  rw [hq1, div_eq_one_iff_eq hFc.ne] at hq
  exact hq

/-- At `T` the shape is on the closure of the T4 region: `γ6 = 1 < α1` (tree: `type08_T_far`). -/
theorem T_closure_T4 {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) (hT : IsT a' b c d) :
    N.F.abc'.f a' = N.F.abc'.f c ∧ N.F.a'bc.f c' < N.F.a'bc.f a :=
  have e := tie_conv_T_L N.hd hT
  ⟨e, type08_T_far N.F N.G N.hκb N.hκc N.hU e⟩

/-- Generic approximants on the T4 side: `θ_n → θ`, `genPoly08 (θ_n) ≠ 0`, `θ_n 5 < 1`. -/
theorem exists_seq_T4side (θ : Fin 6 → ℝ) :
    ∃ θs : ℕ → Fin 6 → ℝ, Tendsto θs atTop (𝓝 θ) ∧ (∀ n, MvPolynomial.eval (θs n) genPoly08 ≠ 0) ∧
      ∀ n, θs n 5 < θ 5 := by
  set c : ℕ → Fin 6 → ℝ := fun n => θ - (1 / ((n : ℝ) + 1)) • (Pi.single 5 1 : Fin 6 → ℝ) with hc
  have box : ∀ n : ℕ, ∃ θ' : Fin 6 → ℝ, (∀ i, |θ' i - c n i| < 1 / (2 * ((n : ℝ) + 1))) ∧
      MvPolynomial.eval θ' genPoly08 ≠ 0 := by
    intro n
    have hε : (0 : ℝ) < 1 / (2 * ((n : ℝ) + 1)) := by positivity
    by_contra hcon
    push Not at hcon
    apply genPoly08_ne_zero
    refine MvPolynomial.funext_set (R := ℝ) (σ := Fin 6) (p := genPoly08) (q := 0)
      (fun i => Set.Ioo (c n i - 1 / (2 * ((n : ℝ) + 1))) (c n i + 1 / (2 * ((n : ℝ) + 1))))
      (fun i => Set.Ioo_infinite (α := ℝ) (by linarith)) fun y hy => ?_
    rw [map_zero]
    refine hcon y fun i => ?_
    have := hy i (Set.mem_univ i)
    rw [abs_sub_lt_iff]; constructor <;> linarith [this.1, this.2]
  choose θs hθs hne using box
  refine ⟨θs, tendsto_pi_nhds.mpr fun i => ?_, hne, fun n => ?_⟩
  · rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨M, hM⟩ := exists_nat_one_div_lt (half_pos hε)
    refine ⟨M, fun n hn => ?_⟩
    rw [Real.dist_eq]
    have h1 := hθs n i
    have h2 : 1 / ((n : ℝ) + 1) ≤ 1 / ((M : ℝ) + 1) := by
      apply one_div_le_one_div_of_le (by positivity)
      exact_mod_cast Nat.add_le_add_right hn 1
    have h3 : |c n i - θ i| ≤ 1 / ((n : ℝ) + 1) := by
      simp only [hc, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      by_cases hi : i = 5
      · subst hi; simp [abs_of_nonneg (show (0:ℝ) ≤ ((n:ℝ)+1) by positivity)]
      · simp [Pi.single_apply, hi]; positivity
    have h4 : 1 / (2 * ((n : ℝ) + 1)) ≤ 1 / ((n : ℝ) + 1) := by
      apply one_div_le_one_div_of_le (by positivity); nlinarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
    have := abs_sub_le (θs n i) (c n i) (θ i)
    linarith
  · have h1 := hθs n 5
    have h3 : c n 5 = θ 5 - 1 / ((n : ℝ) + 1) := by simp [hc]
    have h4 : 1 / (2 * ((n : ℝ) + 1)) < 1 / ((n : ℝ) + 1) := by
      apply one_div_lt_one_div_of_lt (by positivity); nlinarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
    rw [abs_sub_lt_iff] at h1
    linarith [h1.1]

end Type08Sp
end Minimality
