module

public import Minimality.Type08S.C2K22ZA
public import Minimality.Type08S.C2K19G
public import Minimality.Type08S.C2K18A
public import Minimality.Type08S.C2K16E
public import Minimality.Type08S.C2K14D
public import Minimality.Type08S.C2K6HF

@[expose] public section


set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

/-- Quadrilateral `b', c', a', c` in the frame `(a-d, b-d, R)`, `R = -s (a-d) - (c-d)` (`α1 = 1 + β1 s`). -/
def k24h1b0Y (b1 s h6 g : ℝ) : ZMod 4 → ℝ × ℝ × ℝ :=
  ![(1, 0, -b1), (1 + b1 * s, b1, 0), (-(g * s), h6, -g), (-s, 0, -1)]

theorem k24h1b0Y_0 : k24h1b0Y b1 s h6 g 0 = (1, 0, -b1) := rfl
theorem k24h1b0Y_1 : k24h1b0Y b1 s h6 g 1 = (1 + b1 * s, b1, 0) := rfl
theorem k24h1b0Y_2 : k24h1b0Y b1 s h6 g 2 = (-(g * s), h6, -g) := rfl
theorem k24h1b0Y_3 : k24h1b0Y b1 s h6 g 3 = (-s, 0, -1) := rfl

theorem k24h1b0Y_inj {b1 s h6 g : ℝ} (hb1 : 1 < b1) (hs : 0 < s) (hg : 0 < g) (hh6 : 1 < h6) :
    ∀ i j, k24h1b0Y b1 s h6 g i = k24h1b0Y b1 s h6 g j → i = j := by
  intro i j h
  rcases k19_z4_cases i with rfl | rfl | rfl | rfl <;>
    rcases k19_z4_cases j with rfl | rfl | rfl | rfl <;>
    simp only [k24h1b0Y_0, k24h1b0Y_1, k24h1b0Y_2, k24h1b0Y_3, Prod.mk.injEq] at h <;>
    first | rfl | (exfalso; linarith) | (exfalso; linarith [h.1, h.2.1, h.2.2]) |
      (exfalso; obtain ⟨h1, h2, h3⟩ := h; nlinarith) |
      (exfalso; obtain ⟨h1, h2, h3⟩ := h; nlinarith [mul_pos hb1.le hs])

set_option maxHeartbeats 12800000 in
theorem k24h1b0_tsc {D b1 s h6 g v1 v2 : ℝ} (hD : 0 < D) (hb1 : 1 < b1) (hs : 0 < s) (hg : 0 < g)
    (hh6 : 1 < h6) (hv2 : v2 < 0) (hv : 0 < v1 - s * v2) :
    (∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
      TSc D (k24h1b0Y b1 s h6 g (i + 1) - k24h1b0Y b1 s h6 g i) (k24h1b0Y b1 s h6 g j - k24h1b0Y b1 s h6 g i) (v1, v2, 0)) ∧
    (∀ t ∈ [((0 : ℝ), (0 : ℝ), (0 : ℝ)), (1, 0, 0), (0, 1, 0)], ∀ i : ZMod 4,
      TSc D (k24h1b0Y b1 s h6 g (i + 1) - k24h1b0Y b1 s h6 g i) (t - k24h1b0Y b1 s h6 g i) (v1, v2, 0)) := by
  obtain ⟨e0, e1, e2, e3, f0, f1, f2, f3⟩ := k19_z4
  obtain ⟨x, hx, rfl⟩ : ∃ x : ℝ, 0 < x ∧ b1 = 1 + x := ⟨b1 - 1, by linarith, by ring⟩
  obtain ⟨y, hy, rfl⟩ : ∃ y : ℝ, 0 < y ∧ h6 = 1 + y := ⟨h6 - 1, by linarith, by ring⟩
  have n2 : 0 < -v2 := by linarith
  have hb : 0 < 1 + x := by linarith
  have q1 := mul_pos hD hb
  have q2 := mul_pos (mul_pos hD hb) hb
  have q3 := mul_pos hD hv
  have q4 := mul_pos (mul_pos hD hb) hv
  have q5 := mul_pos (mul_pos hD hb) (mul_pos hb hv)
  have q6 := mul_pos hD n2
  have q7 := mul_pos (mul_pos hD hb) n2
  have q8 := mul_pos (mul_pos hD hs) n2
  have q9 := mul_pos (mul_pos hD hb) (mul_pos hs n2)
  refine ⟨?_, ?_⟩
  · intro i j h1 h2'
    rcases k19_z4_cases i with rfl | rfl | rfl | rfl <;>
      rcases k19_z4_cases j with rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl h1
      | exact (h2' (by decide)).elim
      | (simp only [TSc, d3, e0, e1, e2, e3, f0, f1, f2, f3, k24h1b0Y_0, k24h1b0Y_1, k24h1b0Y_2, k24h1b0Y_3,
            Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
         first
         | (left; ring_nf; positivity)
         | (left; nlinarith)
         | (right; refine ⟨by ring, by nlinarith⟩))
  · intro t ht i
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl <;>
    rcases k19_z4_cases i with rfl | rfl | rfl | rfl <;>
      (simp only [TSc, d3, e0, e1, e2, e3, f0, f1, f2, f3, k24h1b0Y_0, k24h1b0Y_1, k24h1b0Y_2, k24h1b0Y_3,
            Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
       first
       | (left; ring_nf; positivity)
       | (left; nlinarith)
       | (right; refine ⟨by ring, by nlinarith⟩))

theorem k24h1b0_cs {P Q R : ℝ³} (hΔ : det3 P Q R ≠ 0) : ⟪Q, R⟫ ^ 2 < ⟪Q, Q⟫ * ⟪R, R⟫ := by
  have hR0 : R ≠ 0 := k17f_r0 hΔ
  have hRR : 0 < ⟪R, R⟫ := real_inner_self_pos.2 hR0
  set u : ℝ³ := ⟪R, R⟫ • Q - ⟪Q, R⟫ • R with hu
  have hu0 : u ≠ 0 := by
    intro h0
    apply hΔ
    have hQ : Q = (⟪Q, R⟫ / ⟪R, R⟫) • R := by
      have : ⟪R, R⟫ • Q = ⟪Q, R⟫ • R := sub_eq_zero.1 h0
      rw [div_eq_inv_mul, mul_smul, ← this, smul_smul, inv_mul_cancel₀ hRR.ne', one_smul]
    rw [hQ]; simp [det3_expand]; ring
  have huu : 0 < ⟪u, u⟫ := real_inner_self_pos.2 hu0
  have e : ⟪u, u⟫ = ⟪R, R⟫ * (⟪Q, Q⟫ * ⟪R, R⟫ - ⟪Q, R⟫ ^ 2) := by
    simp only [hu, inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
      real_inner_comm R Q]; ring
  rw [e] at huu
  nlinarith [(mul_pos_iff_of_pos_left hRR).1 huu]


theorem k24h1c0_gram (A N E : ℝ³) : det3 A N E ^ 2 = ⟪A, A⟫ * ⟪N, N⟫ * ⟪E, E⟫ +
    2 * ⟪A, N⟫ * ⟪N, E⟫ * ⟪E, A⟫ - ⟪A, A⟫ * ⟪N, E⟫ ^ 2 - ⟪N, N⟫ * ⟪E, A⟫ ^ 2 -
    ⟪E, E⟫ * ⟪A, N⟫ ^ 2 := by
  simp only [det3, cross, PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, conj_trivial]
  simp
  ring


set_option maxHeartbeats 3200000 in
/-- `⟪c-a',c-b⟫ > 0` on the tie. -/
theorem k24h1b0_T {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ}
    (hC : K6mCoords a a' b b' c c' d α1 β1 β6 γ6) (hM : K6sM a a' b b' c c' d)
    (hrel : K16Rel a b c d α1 β1) (hH : K6mH1 α1 β1 β6 γ6)
    (ht1 : ⟪c - a', a - b'⟫ = 0) :
    0 < ⟪c - a', c - b⟫ := by
  obtain ⟨hdet, hc', hb', ha', -, -, -, -, hγ6, -⟩ := hC
  obtain ⟨hm0, hm1, hm2⟩ := hM
  obtain ⟨hr1, hr2⟩ := hrel
  obtain ⟨hα1, hβ1, -, hβ6, hγ61⟩ := hH
  set P := a - d with hP
  set Q := b - d with hQ
  set R := c - d with hR
  have e1 : c - a' = (1 - γ6) • R - β6 • Q := by rw [ha', hQ, hR]; module
  have e3 : a - b' = (1 - α1) • P - β1 • R := by rw [hb', hP, hR]; module
  have e4 : b - c = Q - R := by rw [hQ, hR]; module
  have e5 : c' - d = α1 • P + β1 • Q := by rw [hc']; module
  have e6 : b' - d = α1 • P + β1 • R := by rw [hb']; module
  have e9 : c - b' = (1 - β1) • R - α1 • P := by rw [hb', hP, hR]; module
  have hg := k24h1c0_gram P Q R
  rw [e1, e3] at ht1
  rw [e4] at hm0
  rw [e4, e5] at hm1
  rw [e6, e4] at hm2
  have e10 : c - b = R - Q := by rw [hQ, hR]; module
  rw [e10, e1]
  have hRP : ⟪R, P⟫ = ⟪P, R⟫ := real_inner_comm _ _
  have hRQ : ⟪R, Q⟫ = ⟪Q, R⟫ := real_inner_comm _ _
  have hPQ : ⟪Q, P⟫ = ⟪P, Q⟫ := real_inner_comm _ _
  simp only [inner_smul_right, inner_sub_right, inner_add_right, inner_smul_left,
    inner_sub_left, inner_add_left, conj_trivial, hRP, hRQ, hPQ] at ht1 hm0 hm1 hm2 ⊢
  have hr1' : α1 * ⟪P, Q⟫ * (⟪Q, Q⟫ + ⟪R, R⟫ - 2 * ⟪Q, R⟫) =
      -(β1 - 1) * (⟪Q, Q⟫ * ⟪R, R⟫ - ⟪Q, R⟫ ^ 2) := hr1
  have hPR : ⟪P, R⟫ = ⟪P, Q⟫ := by linarith
  simp only [hPR, hRP] at ht1 hm1 hm2 hg ⊢
  have hdet2 : 0 < det3 P Q R ^ 2 := by positivity
  have hee : 0 < ⟪Q, Q⟫ + ⟪R, R⟫ - 2 * ⟪Q, R⟫ := by
    by_contra hn; push Not at hn
    nlinarith [sq_nonneg (⟪Q, Q⟫ - ⟪R, R⟫), real_inner_self_nonneg (x := Q), real_inner_self_nonneg (x := R)]
  have hm : ⟪P, Q⟫ < 0 := by
    by_contra hn; push Not at hn
    have := mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ α1) hn) hee.le
    nlinarith [mul_pos (sub_pos.2 hβ1) hr2]
  have hα : 0 < α1 - 1 := by linarith
  have hT : β1 * ((1 - γ6) * ⟪R, R⟫ - β6 * ⟪Q, R⟫) = (1 - α1) * ⟪P, Q⟫ * (1 - γ6 - β6) := by
    linear_combination (-1 : ℝ) * ht1
  have hkp : 0 < (1 - α1) * ⟪P, Q⟫ := by nlinarith
  have hrk : (1 - α1) * ⟪P, Q⟫ < β1 * ⟪R, R⟫ := by
    by_contra hn; push Not at hn
    have h1 : 0 < γ6 + β6 - 1 := by linarith
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ γ6 - 1) (by linarith : (0:ℝ) ≤ (1 - α1) * ⟪P, Q⟫ - β1 * ⟪R, R⟫), mul_pos (by linarith : (0:ℝ) < β6) (by nlinarith : (0:ℝ) < (1 - α1) * ⟪P, Q⟫ - β1 * ⟪Q, R⟫)]
  have hD : 0 < ⟪Q, Q⟫ * ⟪R, R⟫ - ⟪Q, R⟫ ^ 2 := by nlinarith
  have hid : ((1 - γ6) * (⟪R, R⟫ - ⟪Q, R⟫) + β6 * (⟪Q, Q⟫ - ⟪Q, R⟫)) * (β1 * ⟪R, R⟫ - (1 - α1) * ⟪P, Q⟫) =
      β6 * (⟪Q, Q⟫ * ⟪R, R⟫ - ⟪Q, R⟫ ^ 2 - ⟪P, Q⟫ * (⟪Q, Q⟫ + ⟪R, R⟫ - 2 * ⟪Q, R⟫)) := by
    linear_combination (⟪R, R⟫ - ⟪Q, R⟫) * hT + β6 * hr1'
  have hpos : 0 < β6 * (⟪Q, Q⟫ * ⟪R, R⟫ - ⟪Q, R⟫ ^ 2 - ⟪P, Q⟫ * (⟪Q, Q⟫ + ⟪R, R⟫ - 2 * ⟪Q, R⟫)) :=
    mul_pos (by linarith) (by nlinarith)
  rw [← hid] at hpos
  exact pos_of_mul_pos_left hpos (by linarith) |> fun h => by nlinarith

end C2
end Type08Sp
end Minimality
