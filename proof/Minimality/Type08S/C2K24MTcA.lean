module

public import Minimality.Type08S.C2K14D
public import Minimality.Type08S.C2K16E
public import Minimality.Type08S.C2K22ZA
public import Minimality.Type08S.C2K19G
public import Minimality.Type08S.C2K18A

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

/-- Strict Cauchy-Schwarz for `Q, R` from `det3 P Q R ≠ 0`. -/
theorem k24mtc_cs {P Q R : ℝ³} (hΔ : det3 P Q R ≠ 0) : ⟪Q, R⟫ ^ 2 < ⟪Q, Q⟫ * ⟪R, R⟫ := by
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

/-- Quadrilateral `a', c, b', c'` in the frame `(a-d, (b-d)/γ6, (b-a')/γ6)`. -/
def k24mtcY (α1 β1 β6 γ6 : ℝ) : ZMod 4 → ℝ × ℝ × ℝ :=
  ![(0, γ6, -γ6), (0, 1 - β6, -1), (α1, β1 * (1 - β6), -β1), (α1, β1 * γ6, 0)]

theorem k24mtcY_0 : k24mtcY α1 β1 β6 γ6 0 = (0, γ6, -γ6) := rfl
theorem k24mtcY_1 : k24mtcY α1 β1 β6 γ6 1 = (0, 1 - β6, -1) := rfl
theorem k24mtcY_2 : k24mtcY α1 β1 β6 γ6 2 = (α1, β1 * (1 - β6), -β1) := rfl
theorem k24mtcY_3 : k24mtcY α1 β1 β6 γ6 3 = (α1, β1 * γ6, 0) := rfl

theorem k24mtcY_inj {α1 β1 β6 γ6 : ℝ} (hα1 : 1 < α1) (hβ1 : 0 < β1) (hβ6 : 1 < β6) (hγ6 : 0 < γ6) :
    ∀ i j, k24mtcY α1 β1 β6 γ6 i = k24mtcY α1 β1 β6 γ6 j → i = j := by
  intro i j h
  rcases k19_z4_cases i with rfl | rfl | rfl | rfl <;>
    rcases k19_z4_cases j with rfl | rfl | rfl | rfl <;>
    simp only [k24mtcY_0, k24mtcY_1, k24mtcY_2, k24mtcY_3, Prod.mk.injEq] at h <;>
    first | rfl | (exfalso; linarith)

set_option maxHeartbeats 12800000 in
theorem k24mtc_tsc {D α1 β1 β6 γ6 v1 v2 : ℝ} (hD : 0 < D) (hα1 : 1 < α1) (hβ1 : 1 < β1) (hβ6 : 1 < β6)
    (hγ6 : 0 < γ6) (hγ61 : γ6 < 1) (hv1 : v1 < 0) (hv2 : v2 < 0)
    (hv3 : 0 < α1 * v2 - γ6 * (β1 - 1) * v1) :
    (∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
      TSc D (k24mtcY α1 β1 β6 γ6 (i + 1) - k24mtcY α1 β1 β6 γ6 i) (k24mtcY α1 β1 β6 γ6 j - k24mtcY α1 β1 β6 γ6 i) (v1, v2, 0)) ∧
    (∀ t ∈ [((0 : ℝ), (0 : ℝ), (0 : ℝ)), (1, 0, 0), (0, γ6, 0)], ∀ i : ZMod 4,
      TSc D (k24mtcY α1 β1 β6 γ6 (i + 1) - k24mtcY α1 β1 β6 γ6 i) (t - k24mtcY α1 β1 β6 γ6 i) (v1, v2, 0)) := by
  obtain ⟨e0, e1, e2, e3, f0, f1, f2, f3⟩ := k19_z4
  have a1 := sub_pos.2 hα1
  have b1 := sub_pos.2 hβ1
  have B1 := sub_pos.2 hβ6
  have g1 := sub_pos.2 hγ61
  have n1 : 0 < -v1 := by linarith
  have n2 : 0 < -v2 := by linarith
  have k0 := mul_pos hD hγ6
  have k1 := mul_pos (mul_pos hD hγ6) a1
  have k2 := mul_pos (mul_pos hD a1) B1
  have k3 := mul_pos (mul_pos hD a1) hγ6
  have k4 := mul_pos (mul_pos hD (by linarith : (0:ℝ) < β1)) B1
  have k5 := mul_pos (mul_pos hD (by linarith : (0:ℝ) < α1)) B1
  have k6 := mul_pos (mul_pos hD (by linarith : (0:ℝ) < α1)) hγ6
  have k7 := mul_pos (mul_pos hD (by linarith : (0:ℝ) < β1)) hγ6
  have k8 := mul_pos (mul_pos hD (by linarith : (0:ℝ) < α1)) (mul_pos (by linarith : (0:ℝ) < β1) hγ6)
  have k9 := mul_pos (mul_pos hD hγ6) b1
  have k10 := mul_pos (mul_pos hD hγ6) g1
  have k11 := mul_pos (mul_pos hD (by linarith : (0:ℝ) < α1)) b1
  have k12 := mul_pos (mul_pos hD hγ6) n1
  have k13 := mul_pos hD n1
  have k14 := mul_pos (mul_pos hD hγ6) hv3
  have k15 := mul_pos hD hv3
  have k16 := mul_pos (mul_pos hD (by linarith : (0:ℝ) < α1)) n1
  have k17 := mul_pos (mul_pos hD (by linarith : (0:ℝ) < β1)) n1
  have k18 := mul_pos (mul_pos hD (by linarith : (0:ℝ) < α1)) (mul_pos (by linarith : (0:ℝ) < β1) hγ6)
  have k19 := mul_pos (mul_pos hD (by linarith : (0:ℝ) < α1)) (mul_pos (by linarith : (0:ℝ) < β1) B1)
  refine ⟨?_, ?_⟩
  · intro i j h1 h2'
    rcases k19_z4_cases i with rfl | rfl | rfl | rfl <;>
      rcases k19_z4_cases j with rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl h1
      | exact (h2' (by decide)).elim
      | (simp only [TSc, d3, e0, e1, e2, e3, f0, f1, f2, f3, k24mtcY_0, k24mtcY_1, k24mtcY_2, k24mtcY_3,
            Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
         first
         | (left; nlinarith)
         | (right; refine ⟨by ring, by nlinarith⟩))
  · intro t ht i
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl <;>
    rcases k19_z4_cases i with rfl | rfl | rfl | rfl <;>
      (simp only [TSc, d3, e0, e1, e2, e3, f0, f1, f2, f3, k24mtcY_0, k24mtcY_1, k24mtcY_2, k24mtcY_3,
            Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
       first
       | (left; nlinarith)
       | (right; refine ⟨by ring, by nlinarith⟩))

set_option maxHeartbeats 3200000 in
/-- Metric facts of the side-1 L<=0 cell. -/
theorem k24mtc_keys {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ}
    (hC : K6mCoords a a' b b' c c' d α1 β1 β6 γ6) (hM : K6sM a a' b b' c c' d)
    (hrel : K16Rel a b c d α1 β1)
    (hα1 : 1 < α1) (hβ1 : 1 < β1) (hβ6 : 1 < β6) (hγ61 : γ6 < 1)
    (ht1 : ⟪c - a', a - b'⟫ = 0) :
    0 < ⟪c - a', b - a'⟫ ∧ ⟪c - b, b - d⟫ < 0 ∧ ⟪c - b, a - d⟫ = 0 ∧
      ⟪b' - c', b - a'⟫ = -β1 * ⟪b - c, b - a'⟫ := by
  obtain ⟨hdet, hc', hb', ha', -, -, -, -, hγ6, -⟩ := hC
  obtain ⟨hm0, hm1, hm2⟩ := hM
  obtain ⟨hr1, hr2⟩ := hrel
  set P := a - d with hP
  set Q := b - d with hQ
  set R := c - d with hR
  have e1 : c - a' = (1 - γ6) • R - β6 • Q := by rw [ha', hQ, hR]; module
  have e2 : b - a' = (1 - β6) • Q - γ6 • R := by rw [ha', hQ, hR]; module
  have e3 : a - b' = (1 - α1) • P - β1 • R := by rw [hb', hP, hR]; module
  have e4 : b - c = Q - R := by rw [hQ, hR]; module
  have e5 : c' - d = α1 • P + β1 • Q := by rw [hc']; module
  have e6 : b' - d = α1 • P + β1 • R := by rw [hb']; module
  have e7 : b' - c' = β1 • (R - Q) := by rw [hb', hc', hQ, hR]; module
  have e8 : c - b = R - Q := by rw [hQ, hR]; module
  rw [e1, e3] at ht1
  rw [e4] at hm0 ⊢
  rw [e4, e5] at hm1
  rw [e6, e4] at hm2
  rw [e1, e7, e2, e8]
  have hRP : ⟪R, P⟫ = ⟪P, R⟫ := real_inner_comm _ _
  have hRQ : ⟪R, Q⟫ = ⟪Q, R⟫ := real_inner_comm _ _
  have hPQ : ⟪Q, P⟫ = ⟪P, Q⟫ := real_inner_comm _ _
  have hcs := k24mtc_cs hdet
  simp only [inner_smul_right, inner_sub_right, inner_add_right, inner_smul_left,
    inner_sub_left, inner_add_left, conj_trivial, hRP, hRQ, hPQ] at ht1 hm0 hm1 hm2 ⊢
  have hr1' : α1 * ⟪P, Q⟫ * (⟪Q, Q⟫ + ⟪R, R⟫ - 2 * ⟪Q, R⟫) =
      -(β1 - 1) * (⟪Q, Q⟫ * ⟪R, R⟫ - ⟪Q, R⟫ ^ 2) := hr1
  have hPR : ⟪P, R⟫ = ⟪P, Q⟫ := by linarith
  rw [hPR] at ht1 hm1 hm2 ⊢
  have hqq : ⟪Q, R⟫ < ⟪Q, Q⟫ := by nlinarith
  have hrr : ⟪Q, R⟫ < ⟪R, R⟫ := by nlinarith
  have hD : 0 < ⟪Q, Q⟫ * ⟪R, R⟫ - ⟪Q, R⟫ ^ 2 := by linarith
  have hW : 0 < ⟪Q, Q⟫ + ⟪R, R⟫ - 2 * ⟪Q, R⟫ := by linarith
  have hs : ⟪P, Q⟫ < 0 := by
    by_contra hn; push Not at hn
    have := mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ α1) hn) hW.le
    nlinarith [mul_pos (sub_pos.2 hβ1) hD]
  have hα : 0 < α1 - 1 := by linarith
  have hσ : 0 < β6 + γ6 - 1 := by linarith
  have hg : 0 < 1 - γ6 := by linarith
  have hps : 0 < (α1 - 1) * (β6 + γ6 - 1) * (-⟪P, Q⟫) := mul_pos (mul_pos hα hσ) (by linarith)
  have hkey : 0 < β6 * ⟪Q, R⟫ - (1 - γ6) * ⟪R, R⟫ := by
    have h1 : β1 * (β6 * ⟪Q, R⟫ - (1 - γ6) * ⟪R, R⟫) > 0 := by nlinarith
    exact pos_of_mul_pos_right h1 (by linarith) |> fun h => by nlinarith
  refine ⟨?_, by linarith, by linarith, by ring⟩
  have hq0 : 0 < ⟪Q, R⟫ := by nlinarith
  have hB : 0 < β6 - 1 := by linarith
  nlinarith [mul_pos hB (by nlinarith : 0 < β6 * ⟪Q, Q⟫ - (1 - γ6) * ⟪Q, R⟫), mul_pos hγ6 hkey]

end C2
end Type08Sp
end Minimality
