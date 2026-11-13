module

public import Minimality.Type08S.C2K22ZA
public import Minimality.Type08S.C2K19G
public import Minimality.Type08S.C2K18A
public import Minimality.Type08S.C2K16E

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
def k24h1bY (b1 s h6 g : ℝ) : ZMod 4 → ℝ × ℝ × ℝ :=
  ![(1, 0, -b1), (1 + b1 * s, b1, 0), (-(g * s), h6, -g), (-s, 0, -1)]

theorem k24h1bY_0 : k24h1bY b1 s h6 g 0 = (1, 0, -b1) := rfl
theorem k24h1bY_1 : k24h1bY b1 s h6 g 1 = (1 + b1 * s, b1, 0) := rfl
theorem k24h1bY_2 : k24h1bY b1 s h6 g 2 = (-(g * s), h6, -g) := rfl
theorem k24h1bY_3 : k24h1bY b1 s h6 g 3 = (-s, 0, -1) := rfl

theorem k24h1bY_inj {b1 s h6 g : ℝ} (hb1 : 1 < b1) (hs : 0 < s) (hg : 0 < g) (hh6 : 1 < h6) :
    ∀ i j, k24h1bY b1 s h6 g i = k24h1bY b1 s h6 g j → i = j := by
  intro i j h
  rcases k19_z4_cases i with rfl | rfl | rfl | rfl <;>
    rcases k19_z4_cases j with rfl | rfl | rfl | rfl <;>
    simp only [k24h1bY_0, k24h1bY_1, k24h1bY_2, k24h1bY_3, Prod.mk.injEq] at h <;>
    first | rfl | (exfalso; linarith)

set_option maxHeartbeats 12800000 in
theorem k24h1b_tsc {D b1 s h6 g v1 v2 : ℝ} (hD : 0 < D) (hb1 : 1 < b1) (hs : 0 < s) (hg : 0 < g)
    (hh6 : 1 < h6) (hv2 : v2 < 0) (hv : 0 < v1 - s * v2) :
    (∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
      TSc D (k24h1bY b1 s h6 g (i + 1) - k24h1bY b1 s h6 g i) (k24h1bY b1 s h6 g j - k24h1bY b1 s h6 g i) (v1, v2, 0)) ∧
    (∀ t ∈ [((0 : ℝ), (0 : ℝ), (0 : ℝ)), (1, 0, 0), (0, 1, 0)], ∀ i : ZMod 4,
      TSc D (k24h1bY b1 s h6 g (i + 1) - k24h1bY b1 s h6 g i) (t - k24h1bY b1 s h6 g i) (v1, v2, 0)) := by
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
      | (simp only [TSc, d3, e0, e1, e2, e3, f0, f1, f2, f3, k24h1bY_0, k24h1bY_1, k24h1bY_2, k24h1bY_3,
            Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
         first
         | (left; ring_nf; positivity)
         | (right; refine ⟨by ring, by nlinarith⟩))
  · intro t ht i
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl <;>
    rcases k19_z4_cases i with rfl | rfl | rfl | rfl <;>
      (simp only [TSc, d3, e0, e1, e2, e3, f0, f1, f2, f3, k24h1bY_0, k24h1bY_1, k24h1bY_2, k24h1bY_3,
            Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
       first
       | (left; ring_nf; positivity)
       | (left; nlinarith)
       | (right; refine ⟨by ring, by nlinarith⟩))

theorem k24h1b_cs {P Q R : ℝ³} (hΔ : det3 P Q R ≠ 0) : ⟪Q, R⟫ ^ 2 < ⟪Q, Q⟫ * ⟪R, R⟫ := by
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

end C2
end Type08Sp
end Minimality
