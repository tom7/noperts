module

public import Minimality.Type08S.C2K17GA10

@[expose] public section


/-!
# K17GA / GA11: S1.2a (Zdb(ii), `ζ_{a-c'}(a,d) > 0`): cell `(a,b',c,a',c')@a-b'`, frame `(b-d, c-d, a-b')`
ccw cycle `(c', a', c, b', a)`; tilt cone `v1 < 0 ∧ κ(α1-1) v1 < β1 v2`, tilt `(-λ η, 1)`.
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

def k17gaA (κ σ α1 β1 β6 : ℝ) : ZMod 5 → ℝ × ℝ × ℝ :=
  pc5 (β1, κ * α1, α1 * σ) (β6, 1, 0) (0, 1, 0) (0, κ, σ - 1) (0, κ, σ)

set_option maxHeartbeats 3200000 in
theorem k17ga_s12a_tsc {κ σ α1 β1 β6 v1 v2 : ℝ} (hκ : κ < 0) (hσ : σ < 0) (hα1 : 1 < α1) (hβ1 : 0 < β1)
    (hb6 : 1 ≤ β6) (hbc : 1 < β1 + κ * α1 * (1 - β6)) (hE : (σ - 1) * (1 - β1) ≤ α1 * (σ - κ))
    (hv1 : v1 < 0) (hcone : κ * (α1 - 1) * v1 < β1 * v2) :
    (∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      TSc 1 (k17gaA κ σ α1 β1 β6 (i + 1) - k17gaA κ σ α1 β1 β6 i)
        (k17gaA κ σ α1 β1 β6 j - k17gaA κ σ α1 β1 β6 i) (v1, v2, 0)) ∧
    (∀ t ∈ [((1 : ℝ), (0 : ℝ), (0 : ℝ)), (0, 0, 0)], ∀ i : ZMod 5,
      TSc 1 (k17gaA κ σ α1 β1 β6 (i + 1) - k17gaA κ σ α1 β1 β6 i) (t - k17gaA κ σ α1 β1 β6 i) (v1, v2, 0)) := by
  obtain ⟨f0, f1, f2, f3, f4⟩ := z5_add
  have nk : 0 < -κ := by linarith
  have ns : 0 < -σ := by linarith
  have a1 : 0 < α1 - 1 := by linarith
  have b6 : 0 ≤ β6 - 1 := by linarith
  have nv : 0 < -v1 := by linarith
  have h1 := mul_pos nk nv
  have h2 := mul_pos ns nv
  have h3 := mul_pos hβ1 nk
  have h4 := mul_pos (mul_pos nk a1) nv
  have h5 := mul_nonneg (le_of_lt nk) b6
  have h6 := mul_nonneg (le_of_lt hβ1) b6
  have h7 := mul_nonneg (le_of_lt (mul_pos hβ1 nk)) b6
  have h8 := mul_nonneg (le_of_lt (mul_pos nk a1)) b6
  have h9 := mul_pos ns a1
  have h10 := mul_pos (mul_pos ns a1) nv
  have h11 := mul_pos ns (sub_pos.2 hcone)
  have h12 := mul_pos hβ1 ns
  have h13 := mul_nonneg (le_of_lt (mul_pos hβ1 ns)) b6
  have h14 := mul_pos nk (sub_pos.2 hcone)
  have h15 := mul_nonneg b6 (sub_pos.2 hcone).le
  have h16 := mul_pos (mul_pos nk a1) (sub_pos.2 hcone)
  constructor
  · intro i j h1 h2
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl h1
      | exact (h2 (by decide)).elim
      | (simp only [TSc, d3, k17gaA, f0, f1, f2, f3, f4, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4,
          Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
         first | (left; nlinarith) | (right; refine ⟨by ring, by nlinarith⟩))
  · intro t ht i
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl <;>
      rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      (simp only [TSc, d3, k17gaA, f0, f1, f2, f3, f4, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4,
          Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
       first | (left; nlinarith) | (right; refine ⟨by ring, by nlinarith⟩))

set_option maxHeartbeats 3200000 in
/-- Cycle `0..4 = (c', a', c, b', a)`: `c' = a` (z-tie, top), `a' = c`, `a'` below the top, `b'` below `a`,
and `w(c) < w(a')`.  Exactly one of `c'`, `a` is the peak. -/
theorem k17ga_lex_A (z w : ZMod 5 → ℝ) (hinj : ∀ i j, z i = z j → w i = w j → i = j)
    (h12 : z 1 = z 2) (h40 : z 4 = z 0) (h10 : z 1 < z 0) (h34 : z 3 < z 4) (hw : w 2 < w 1) : LexUni z w := by
  have tot : LexLt (z 4, w 4) (z 0, w 0) ∨ LexLt (z 0, w 0) (z 4, w 4) := by
    apply lexLt_total
    intro h; have := hinj 4 0 (congrArg Prod.fst h) (congrArg Prod.snd h); exact absurd this (by decide)
  have le : ∀ i j, LexLt (z i, w i) (z j, w j) → z i ≤ z j := fun i j h => lexLt_fst_le' h
  obtain ⟨s0, s1, s2, s3, s4⟩ := z5_add
  obtain ⟨t0, t1, t2, t3, t4⟩ := k17f_zsub
  have L21 : LexLt (z 2, w 2) (z 1, w 1) := Or.inr ⟨h12.symm, hw⟩
  have L10 : LexLt (z 1, w 1) (z 0, w 0) := Or.inl h10
  have L34 : LexLt (z 3, w 3) (z 4, w 4) := Or.inl h34
  rcases tot with h40' | h04
  · refine k17f_lexUni5_of_peak z w hinj 0 ?_ ?_
    · simp only [t0, s0]; exact ⟨h40', L10⟩
    · intro i hi
      rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
      · exact absurd rfl hi
      · simp only [t1, s1]; rintro ⟨h, -⟩; have := le _ _ h; linarith
      · simp only [t2, s2]; rintro ⟨h, -⟩; exact lexLt_asymm L21 h
      · simp only [t3, s3]; rintro ⟨-, h⟩; have := le _ _ h; linarith
      · simp only [t4, s4]; rintro ⟨-, h⟩; exact lexLt_asymm h40' h
  · refine k17f_lexUni5_of_peak z w hinj 4 ?_ ?_
    · simp only [t4, s4]; exact ⟨L34, h04⟩
    · intro i hi
      rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
      · simp only [t0, s0]; rintro ⟨h, -⟩; exact lexLt_asymm h04 h
      · simp only [t1, s1]; rintro ⟨h, -⟩; have := le _ _ h; linarith
      · simp only [t2, s2]; rintro ⟨h, -⟩; exact lexLt_asymm L21 h
      · simp only [t3, s3]; rintro ⟨-, h⟩; have := le _ _ h; linarith
      · exact absurd rfl hi

theorem k17gaA_inj {κ σ α1 β1 β6 : ℝ} (hκ : κ < 0) (hα1 : 1 < α1) (hβ1 : 0 < β1) (hb6 : 1 ≤ β6) :
    ∀ i j : ZMod 5, k17gaA κ σ α1 β1 β6 i = k17gaA κ σ α1 β1 β6 j → i = j := by
  intro i j h
  have e1 := congrArg Prod.fst h
  have e2 := congrArg (fun t => t.2.1) h
  have e3 := congrArg (fun t => t.2.2) h
  have m1 : κ * α1 < 0 := by nlinarith
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;> rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    first | rfl | (exfalso; simp only [k17gaA, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4] at e1 e2 e3; nlinarith)

set_option maxHeartbeats 3200000 in
/-- **S1.2a frame cell** `(a, b', c, a', c')` at `R = a - b'` on the Zdb(ii) tie, given `⟪P,Q⟫ > 0`. -/
theorem k17ga_s12a_frame (V : Finset ℝ³) (P Q R d : ℝ³) (hΔ : det3 P Q R ≠ 0) {κ σ α1 β1 β6 : ℝ}
    (hκ : κ < 0) (hσ : σ < 0) (hα1 : 1 < α1) (hβ1 : 0 < β1) (hb6 : 1 ≤ β6) (hbc : 1 < β1 + κ * α1 * (1 - β6))
    (hE : (σ - 1) * (1 - β1) ≤ α1 * (σ - κ)) (hBz : ⟪P, R⟫ = 0) (hZa : κ * ⟪Q, R⟫ + σ * ⟪R, R⟫ = 0)
    (hL : 0 < ⟪P, Q⟫)
    (hmem : ∀ i, fpoint P Q R d (k17gaA κ σ α1 β1 β6 i) ∈ V)
    (hVall : ∀ y ∈ V, y = fpoint P Q R d (0, κ, σ) ∨ y = fpoint P Q R d (β1, κ * α1, α1 * σ) ∨
      y = fpoint P Q R d (β6, 1, 0) ∨ y = fpoint P Q R d (0, 1, 0) ∨ y = fpoint P Q R d (0, 0, 0) ∨
      y = fpoint P Q R d (1, 0, 0) ∨ y = fpoint P Q R d (0, κ, σ - 1)) :
    HasLexCellAt V R := by
  have hR0 : R ≠ 0 := by intro h; apply hΔ; rw [h]; simp [det3_expand]
  have hA : 0 < ⟪R, R⟫ := real_inner_self_pos.2 hR0
  have nk : 0 < -κ := by linarith
  have a1 : 0 < α1 - 1 := by linarith
  have hy : ⟪Q, R⟫ < 0 := by nlinarith [mul_pos (neg_pos.2 hσ) hA]
  have hz : ∀ t : ℝ × ℝ × ℝ, ⟪fpoint P Q R d t, R⟫ = ⟪d, R⟫ + t.1 * ⟪P, R⟫ + t.2.1 * ⟪Q, R⟫ + t.2.2 * ⟪R, R⟫ :=
    fun t => inner_fpoint _ _ _ _ _ _
  obtain ⟨η0, hη0, hηx0⟩ := k8_eta (x := ⟪P, P⟫) (y := ⟪P, Q⟫) hL.ne'
  have hnka : 0 < (-κ) * (α1 - 1) + 1 := by nlinarith [mul_pos nk a1]
  obtain ⟨η, hηdef⟩ : ∃ η, η = min η0 (β1 / ((-κ) * (α1 - 1) + 1)) := ⟨_, rfl⟩
  have hη : 0 < η := by rw [hηdef]; exact lt_min hη0 (by positivity)
  have hη1 : η ≤ η0 := by rw [hηdef]; exact min_le_left _ _
  have hη2 : η ≤ β1 / ((-κ) * (α1 - 1) + 1) := by rw [hηdef]; exact min_le_right _ _
  have hηx : 2 * η * |⟪P, P⟫| < |⟪P, Q⟫| := by
    nlinarith [mul_le_mul_of_nonneg_right hη1 (abs_nonneg ⟪P, P⟫)]
  have hη3 : η * ((-κ) * (α1 - 1)) < β1 := by
    have := (le_div_iff₀ hnka).1 hη2
    nlinarith [mul_pos nk a1]
  have hXabs : |⟪P, Q⟫| = ⟪P, Q⟫ := abs_of_pos hL
  have hlexC : ∀ v1 v2 : ℝ, 0 < v1 * ⟪P, P⟫ + v2 * ⟪P, Q⟫ →
      (∀ i j, ⟪fpoint P Q R d (k17gaA κ σ α1 β1 β6 i), R⟫ = ⟪fpoint P Q R d (k17gaA κ σ α1 β1 β6 j), R⟫ →
        ⟪fpoint P Q R d (k17gaA κ σ α1 β1 β6 i), fcomb P Q R v1 v2 0⟫ =
          ⟪fpoint P Q R d (k17gaA κ σ α1 β1 β6 j), fcomb P Q R v1 v2 0⟫ → i = j) →
      LexUni (fun i => ⟪fpoint P Q R d (k17gaA κ σ α1 β1 β6 i), R⟫)
        (fun i => ⟪fpoint P Q R d (k17gaA κ σ α1 β1 β6 i), fcomb P Q R v1 v2 0⟫) := by
    intro v1 v2 hw hinj
    refine k17ga_lex_A _ _ hinj ?_ ?_ ?_ ?_ ?_
    · simp only [k17gaA, pc5_1, pc5_2, hz, hBz]; ring
    · simp only [k17gaA, pc5_4, pc5_0, hz, hBz]; nlinarith
    · simp only [k17gaA, pc5_1, pc5_0, hz, hBz]; nlinarith
    · simp only [k17gaA, pc5_3, pc5_4, hz, hBz]; nlinarith
    · simp only [k17gaA, pc5_2, pc5_1, k17f_wexp, hBz]; nlinarith [mul_pos (by linarith : (0:ℝ) < β6) hw]
  refine cyc_cell V P Q R d hΔ (k := 5) (by norm_num) (k17gaA κ σ α1 β1 β6)
    (k17gaA_inj hκ hα1 hβ1 hb6) hmem [((1 : ℝ), (0 : ℝ), (0 : ℝ)), (0, 0, 0)] ?_
    (u1 := 0) (u2 := 1) (t1 := -η) (t2 := 0) (lo := 0) (hi := 1) (by nlinarith) (by norm_num)
    (fun v1 v2 => v1 < 0 ∧ κ * (α1 - 1) * v1 < β1 * v2 ∧ 0 < v1 * ⟪P, P⟫ + v2 * ⟪P, Q⟫) ?_ ?_ ?_
  · intro y hy
    rcases hVall y hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨4, rfl⟩
    · exact Or.inl ⟨0, rfl⟩
    · exact Or.inl ⟨1, rfl⟩
    · exact Or.inl ⟨2, rfl⟩
    · exact Or.inr ⟨_, by simp, rfl⟩
    · exact Or.inr ⟨_, by simp, rfl⟩
    · exact Or.inl ⟨3, rfl⟩
  · intro lam h0 h1
    refine ⟨by nlinarith [mul_pos h0 hη], by nlinarith [mul_lt_mul_of_pos_left hη3 h0, mul_pos h0 hη], ?_⟩
    have hle : lam * η * ⟪P, P⟫ ≤ η * |⟪P, P⟫| := by
      have h2 : lam * ⟪P, P⟫ ≤ |⟪P, P⟫| := by
        rcases le_total 0 ⟪P, P⟫ with hx | hx
        · rw [abs_of_nonneg hx]; nlinarith
        · rw [abs_of_nonpos hx]; nlinarith
      nlinarith [mul_le_mul_of_nonneg_left h2 hη.le]
    have e : (0 + lam * -η) * ⟪P, P⟫ + (1 + lam * 0) * ⟪P, Q⟫ = -(lam * η * ⟪P, P⟫) + ⟪P, Q⟫ := by ring
    rw [e]; rw [hXabs] at hηx
    nlinarith [abs_nonneg ⟪P, P⟫]
  · rintro v1 v2 ⟨hv1, hc, -⟩
    exact k17ga_s12a_tsc hκ hσ hα1 hβ1 hb6 hbc hE hv1 hc
  · rintro v1 v2 ⟨-, -, hw⟩ hinj
    exact hlexC v1 v2 hw hinj

end C2
end Type08Sp
end Minimality
