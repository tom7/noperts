module

public import Minimality.Type08S.C2K17F2A

@[expose] public section


/-!
# K17GA / GA2: the cell (a,d,b,a',b') at a - c' (frame (b-d, c-d, a-c')): R3 (S1.1c) and S1.3a
Frame coordinates: `a = (-β1 τ, 0, -τ)`, `d = 0`, `b = (1,0,0)`, `a' = (β6,1,0)`, `b' = (-α4 β1 τ, γ4, -α4 τ)`, `c = (0,1,0)`,
`c' = (-β1 τ, 0, -(τ+1))`, `τ = 1/(α1-1)`.  Tilt cone `v2 > 0 ∧ γ4 v1 + (α4-1) β1 τ v2 > 0`.
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

theorem k17ga_fp (P Q R d : ℝ³) (x y z : ℝ) : fpoint P Q R d (x, y, z) = d + x • P + y • Q + z • R := by
  simp only [fpoint, fcomb]; module

theorem k17ga_r0 {P Q R : ℝ³} (h : det3 P Q R ≠ 0) : R ≠ 0 := by
  intro h0; rw [h0] at h; simp [det3_expand] at h

/-- ccw pentagon `a, d, b, a', b'` at `a - c'`. -/
def k17gaR3 (τ β1 α4 γ4 β6 : ℝ) : ZMod 5 → ℝ × ℝ × ℝ :=
  pc5 (-(β1 * τ), 0, -τ) (0, 0, 0) (1, 0, 0) (β6, 1, 0) (-(α4 * β1 * τ), γ4, -(α4 * τ))

set_option maxHeartbeats 3200000 in
theorem k17ga_r3_tsc {D τ β1 α4 γ4 β6 v1 v2 : ℝ} (hD : 0 < D) (hτ : 0 < τ) (hβ1 : 0 < β1) (hα4 : 1 ≤ α4)
    (hγ4 : 1 < γ4) (hb6 : 1 ≤ β6) (hv1 : 0 < v1) (hv2 : 0 < v2) (hc : 0 < γ4 * v1 + (α4 - 1) * β1 * τ * v2) :
    ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      TSc D (k17gaR3 τ β1 α4 γ4 β6 (i + 1) - k17gaR3 τ β1 α4 γ4 β6 i)
        (k17gaR3 τ β1 α4 γ4 β6 j - k17gaR3 τ β1 α4 γ4 β6 i) (v1, v2, 0) := by
  obtain ⟨s0, s1, s2, s3, s4⟩ := z5_add
  have a1 : 0 ≤ α4 - 1 := by linarith
  have b6 : 0 ≤ β6 - 1 := by linarith
  have k1 := hD
  have kt := mul_pos hD hτ
  have kb := mul_pos hD hβ1
  have kg := mul_pos hD (by linarith : (0 : ℝ) < γ4)
  have kg1 := mul_pos hD (sub_pos.2 hγ4)
  have ktb := mul_pos kt hβ1
  have kv1 := mul_pos hD hv1
  have kv2 := mul_pos hD hv2
  have kc := mul_pos hD hc
  have ktv2 := mul_pos kt hv2
  have ktbv2 := mul_pos ktb hv2
  have ka := mul_nonneg hD.le a1
  have kb6 := mul_nonneg hD.le b6
  intro i j h1 h2'
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl h1
    | exact (h2' (by decide)).elim
    | (simp only [TSc, d3, k17gaR3, s0, s1, s2, s3, s4, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4,
        Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
       first
       | (left; nlinarith)
       | (right; refine ⟨by ring, by nlinarith⟩))

set_option maxHeartbeats 3200000 in
theorem k17ga_r3_rest {D τ β1 α4 γ4 β6 v1 v2 : ℝ} (hD : 0 < D) (hτ : 0 < τ) (hβ1 : 0 < β1) (hα4 : 1 ≤ α4)
    (hγ4 : 1 < γ4) (hb6 : 1 ≤ β6) (hv1 : 0 < v1) (hv2 : 0 < v2) (hc : 0 < γ4 * v1 + (α4 - 1) * β1 * τ * v2) :
    (∀ i : ZMod 5, TSc D (k17gaR3 τ β1 α4 γ4 β6 (i + 1) - k17gaR3 τ β1 α4 γ4 β6 i)
        ((0, 1, 0) - k17gaR3 τ β1 α4 γ4 β6 i) (v1, v2, 0)) ∧
    (∀ i : ZMod 5, TSc D (k17gaR3 τ β1 α4 γ4 β6 (i + 1) - k17gaR3 τ β1 α4 γ4 β6 i)
        ((-(β1 * τ), 0, -(τ + 1)) - k17gaR3 τ β1 α4 γ4 β6 i) (v1, v2, 0)) := by
  obtain ⟨s0, s1, s2, s3, s4⟩ := z5_add
  have a1 : 0 ≤ α4 - 1 := by linarith
  have b6 : 0 ≤ β6 - 1 := by linarith
  have k1 := hD
  have kt := mul_pos hD hτ
  have kb := mul_pos hD hβ1
  have kg := mul_pos hD (by linarith : (0 : ℝ) < γ4)
  have kg1 := mul_pos hD (sub_pos.2 hγ4)
  have ktb := mul_pos kt hβ1
  have kv1 := mul_pos hD hv1
  have kv2 := mul_pos hD hv2
  have kc := mul_pos hD hc
  have ktv2 := mul_pos kt hv2
  have ktbv2 := mul_pos ktb hv2
  have ka := mul_nonneg hD.le a1
  have kb6 := mul_nonneg hD.le b6
  constructor <;> intro i <;>
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    (simp only [TSc, d3, k17gaR3, s0, s1, s2, s3, s4, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4,
        Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
     first
     | (left; nlinarith)
     | (right; refine ⟨by ring, by nlinarith⟩))

theorem k17gaR3_inj {τ β1 α4 γ4 β6 : ℝ} (hτ : 0 < τ) (hβ1 : 0 < β1) (hα4 : 1 ≤ α4) (hγ4 : 0 < γ4) :
    ∀ i j, k17gaR3 τ β1 α4 γ4 β6 i = k17gaR3 τ β1 α4 γ4 β6 j → i = j := by
  intro i j h
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    simp only [k17gaR3, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4, Prod.mk.injEq] at h <;>
    first | rfl | (exfalso; nlinarith [h.1, h.2.1, h.2.2, mul_pos hτ hβ1]) | (exfalso; norm_num at h) |
      (exfalso; obtain ⟨h1, h2, h3⟩ := h; nlinarith [mul_pos hτ hβ1])

/-- Reversed `lexUni5_top`: `z2 < z1`, `z3 < z2`, `z4 < z0` (lex), cycle `0..4`. -/
theorem k17ga_lexUni5_R3 (z w : ZMod 5 → ℝ) (hinj : ∀ i j, z i = z j → w i = w j → i = j)
    (h21 : LexLt (z 2, w 2) (z 1, w 1)) (h32 : LexLt (z 3, w 3) (z 2, w 2))
    (h40 : LexLt (z 4, w 4) (z 0, w 0)) : LexUni z w := by
  have e4 : (-1 : ZMod 5) = 4 := by decide
  have e3 : (-2 : ZMod 5) = 3 := by decide
  have e2 : (-3 : ZMod 5) = 2 := by decide
  have e1 : (-4 : ZMod 5) = 1 := by decide
  have := lexUni_neg (lexUni5_top (fun i => z (-i)) (fun i => w (-i))
    (fun i j h1 h2 => neg_injective (hinj _ _ h1 h2)) (by simpa [e4] using h40) (by simpa [e3, e2] using h32)
    (by simpa [e2, e1] using h21))
  simpa using this

set_option maxHeartbeats 3200000 in
/-- **The R3 / S1.1c / S1.3a cell**: pentagon `(a,d,b,a',b')` at `a - c'`, frame `(b-d, c-d, a-c')`, tilt `(1, λ)`.
Facts (depth at `a - c'`): `d > b`, `b > a'`, `a > b'`. -/
theorem k17ga_r3_cell {a a' b b' c c' d : ℝ³} {α1 α4 β1 γ4 β6 : ℝ} (hdet : det3 (a - d) (b - d) (c - d) ≠ 0)
    (hc' : c' = d + α1 • (a - d) + β1 • (b - d)) (hb' : b' = d + α4 • (a - d) + γ4 • (c - d))
    (ha' : a' = d + β6 • (b - d) + (1 : ℝ) • (c - d)) (hα1 : 1 < α1) (hβ1 : 0 < β1) (hα4 : 1 ≤ α4)
    (hγ4 : 1 < γ4) (hb6 : 1 ≤ β6)
    (hx : ⟪b - d, a - c'⟫ < 0) (hy : ⟪c - d, a - c'⟫ < (1 - β6) * ⟪b - d, a - c'⟫)
    (hz : γ4 * ⟪c - d, a - c'⟫ < (1 - α4) * ⟪a - d, a - c'⟫) :
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
    refine k17ga_lexUni5_R3 _ w hw ?_ ?_ ?_
    · left; simp only [k17gaR3, pc5_1, pc5_2, hz']; nlinarith
    · left; simp only [k17gaR3, pc5_2, pc5_3, hz']; nlinarith
    · left; simp only [k17gaR3, pc5_4, pc5_0, hz']; nlinarith

end C2
end Type08Sp
end Minimality
