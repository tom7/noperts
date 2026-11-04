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

/-- Gram expansion of an inner product of two combinations of `P, Q, R` with `⟪P,Q⟫ = ⟪P,R⟫`. -/
theorem k24h1l_ex (P Q R : ℝ³) (hPR : ⟪P, R⟫ = ⟪P, Q⟫) (x1 x2 x3 y1 y2 y3 : ℝ) :
    ⟪x1 • P + x2 • Q + x3 • R, y1 • P + y2 • Q + y3 • R⟫ =
      x1 * y1 * ⟪P, P⟫ + (x1 * y2 + x2 * y1 + x1 * y3 + x3 * y1) * ⟪P, Q⟫ + x2 * y2 * ⟪Q, Q⟫ +
        (x2 * y3 + x3 * y2) * ⟪Q, R⟫ + x3 * y3 * ⟪R, R⟫ := by
  have hQP : ⟪Q, P⟫ = ⟪P, Q⟫ := real_inner_comm P Q
  have hRP : ⟪R, P⟫ = ⟪P, R⟫ := real_inner_comm P R
  have hRQ : ⟪R, Q⟫ = ⟪Q, R⟫ := real_inner_comm Q R
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, conj_trivial, hQP, hRP, hRQ, hPR]
  ring

/-- Strict Cauchy-Schwarz for `Q, R`. -/
theorem k24h1l_cs {P Q R : ℝ³} (hΔ : det3 P Q R ≠ 0) : ⟪Q, R⟫ ^ 2 < ⟪Q, Q⟫ * ⟪R, R⟫ := by
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

/-- Positive definiteness: `σ² W < pp D` where `σ = ⟪P,Q⟫ = ⟪P,R⟫`. -/
theorem k24h1l_pd {P Q R : ℝ³} (hΔ : det3 P Q R ≠ 0) (hPR : ⟪P, R⟫ = ⟪P, Q⟫) :
    ⟪P, Q⟫ ^ 2 * (⟪Q, Q⟫ + ⟪R, R⟫ - 2 * ⟪Q, R⟫) <
      ⟪P, P⟫ * (⟪Q, Q⟫ * ⟪R, R⟫ - ⟪Q, R⟫ ^ 2) := by
  have hD := sub_pos.2 (k24h1l_cs hΔ)
  obtain ⟨D, hDd⟩ : ∃ D, D = ⟪Q, Q⟫ * ⟪R, R⟫ - ⟪Q, R⟫ ^ 2 := ⟨_, rfl⟩
  rw [← hDd] at hD ⊢
  obtain ⟨x, hx⟩ : ∃ x, x = ⟪P, Q⟫ * (⟪R, R⟫ - ⟪Q, R⟫) := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y, y = ⟪P, Q⟫ * (⟪Q, Q⟫ - ⟪Q, R⟫) := ⟨_, rfl⟩
  have hu0 : D • P + (-x) • Q + (-y) • R ≠ 0 := by
    intro h0; apply hΔ
    have hP : D • P = x • Q + y • R := by
      have h1 : D • P + (-x) • Q + (-y) • R = D • P - x • Q - y • R := by module
      rw [h1, sub_sub, sub_eq_zero] at h0; exact h0
    have h1 : det3 (D • P) Q R = 0 := by rw [hP]; simp [det3_expand]; ring
    have h2 : det3 (D • P) Q R = D * det3 P Q R := by simp [det3_expand]; ring
    rw [h2] at h1; exact (mul_eq_zero.1 h1).resolve_left hD.ne'
  have huu := real_inner_self_pos.2 hu0
  rw [show D • P + (-x) • Q + (-y) • R = D • P + (-x) • Q + (-y) • R from rfl,
    k24h1l_ex P Q R hPR D (-x) (-y) D (-x) (-y)] at huu
  have e : D * D * ⟪P, P⟫ + (D * (-x) + (-x) * D + D * (-y) + (-y) * D) * ⟪P, Q⟫ + (-x) * (-x) * ⟪Q, Q⟫ +
      ((-x) * (-y) + (-y) * (-x)) * ⟪Q, R⟫ + (-y) * (-y) * ⟪R, R⟫ =
      D * (⟪P, P⟫ * D - ⟪P, Q⟫ ^ 2 * (⟪Q, Q⟫ + ⟪R, R⟫ - 2 * ⟪Q, R⟫)) := by
    rw [hx, hy, hDd]; ring
  rw [e] at huu
  nlinarith [(mul_pos_iff_of_pos_left hD).1 huu]

/-- Real-variable core of the metric facts.  `σ = ⟪P,Q⟫ = ⟪P,R⟫`. -/
theorem k24h1l_real {pp σ qq qr rr α β B g : ℝ} (hα : 1 < α) (hβ : 1 < β) (hB : 1 < B) (hg : 1 < g)
    (hD : 0 < qq * rr - qr ^ 2) (hqq : qr < qq) (hrr : qr < rr)
    (hpd : σ ^ 2 * (qq + rr - 2 * qr) < pp * (qq * rr - qr ^ 2))
    (hrel : α * σ * (qq + rr - 2 * qr) = -(β - 1) * (qq * rr - qr ^ 2))
    (ht : (1 - α) * σ * (1 - g - B) - (1 - g) * β * rr + B * β * qr = 0) :
    0 < α * σ * (1 - g - B) + (β - 1) * ((1 - g) * rr - B * qr) ∧
    0 < α * (α - 1) * pp + ((α - 1) * (β - 1) + α * β) * σ + β * (β - 1) * rr ∧
    (α * (1 - α) * pp + ((1 - α) * (β - 1) - α * β) * σ - β * (β - 1) * qr = 0 →
      0 < (α - 1) * pp + β * σ) := by
  have hW : 0 < qq + rr - 2 * qr := by linarith
  have hs : 0 < β - 1 := by linarith
  have hα0 : 0 < α := by linarith
  have hrr0 : 0 < rr := by
    by_contra hn; push Not at hn
    rcases le_or_gt 0 qq with h | h
    · nlinarith [mul_nonneg h (neg_nonneg.2 hn), sq_nonneg qr]
    · nlinarith [mul_pos (sub_pos.2 hqq) (sub_pos.2 hrr), mul_pos (neg_pos.2 h) (neg_pos.2 (lt_of_lt_of_le hrr hn)), sq_nonneg qr]
  have hσ : σ < 0 := by
    by_contra hn; push Not at hn
    have := mul_nonneg (mul_nonneg hα0.le hn) hW.le
    nlinarith [mul_pos hs hD]
  have hR : 0 < α * σ + (β - 1) * rr := by
    have e : (α * σ + (β - 1) * rr) * (qq + rr - 2 * qr) = (β - 1) * (rr - qr) ^ 2 := by
      linear_combination hrel
    have : 0 < (α * σ + (β - 1) * rr) * (qq + rr - 2 * qr) := by
      rw [e]; exact mul_pos hs (by nlinarith)
    exact (pos_iff_pos_of_mul_pos this).2 hW
  refine ⟨?_, ?_, ?_⟩
  · have e : β * (α * σ * (1 - g - B) + (β - 1) * ((1 - g) * rr - B * qr)) =
        (g + B - 1) * (-σ) * (α + β - 1) := by linear_combination (-(β - 1)) * ht
    have hp : 0 < (g + B - 1) * (-σ) * (α + β - 1) :=
      mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)
    rw [← e] at hp
    exact pos_of_mul_pos_right hp (by linarith) |> fun h => by nlinarith
  · have e : (α * (α - 1) * pp + ((α - 1) * (β - 1) + α * β) * σ + β * (β - 1) * rr) * (qq * rr - qr ^ 2) =
        β * (qq * rr - qr ^ 2) * (α * σ + (β - 1) * rr) +
          α * (α - 1) * (pp * (qq * rr - qr ^ 2) - σ ^ 2 * (qq + rr - 2 * qr)) := by
      linear_combination ((α - 1) * σ) * hrel
    have hp : 0 < β * (qq * rr - qr ^ 2) * (α * σ + (β - 1) * rr) +
          α * (α - 1) * (pp * (qq * rr - qr ^ 2) - σ ^ 2 * (qq + rr - 2 * qr)) :=
      add_pos (mul_pos (mul_pos (by linarith) hD) hR)
        (mul_pos (mul_pos hα0 (by linarith)) (by linarith))
    rw [← e] at hp
    exact (pos_iff_pos_of_mul_pos hp).2 hD
  · intro hL1
    have e1 : α * ((α - 1) * pp + β * σ) = (β - 1) * ((1 - α) * σ - β * qr) := by
      linear_combination (-1) * hL1
    have e2 : B * ((1 - α) * σ - β * qr) = (g - 1) * (β * rr - (α - 1) * (-σ)) := by
      linear_combination (-1) * ht
    have e3 : (α - 1) * (-σ) * (α * (qq + rr - 2 * qr)) = (α - 1) * (β - 1) * (qq * rr - qr ^ 2) := by
      linear_combination (-(α - 1)) * hrel
    have hlt : (α - 1) * (-σ) < β * rr := by
      have hDr : qq * rr - qr ^ 2 < rr * (qq + rr - 2 * qr) := by nlinarith
      have h1 : (α - 1) * (β - 1) * (qq * rr - qr ^ 2) < β * rr * (α * (qq + rr - 2 * qr)) := by
        have := mul_lt_mul_of_pos_left hDr (mul_pos (by linarith : (0:ℝ) < α - 1) hs)
        have hk : (α - 1) * (β - 1) < α * β := by nlinarith
        have hk2 := mul_lt_mul_of_pos_right hk (mul_pos hrr0 hW)
        nlinarith [this, hk2]
      rw [← e3] at h1
      have h2 : (α - 1) * (-σ) * (α * (qq + rr - 2 * qr)) < β * rr * (α * (qq + rr - 2 * qr)) := h1
      exact lt_of_mul_lt_mul_right h2 (mul_pos hα0 hW).le
    have hC : 0 < (1 - α) * σ - β * qr := by
      have : 0 < B * ((1 - α) * σ - β * qr) := by
        rw [e2]; exact mul_pos (by linarith) (by linarith)
      exact pos_of_mul_pos_right this (by linarith) |> fun h => by nlinarith
    have : 0 < α * ((α - 1) * pp + β * σ) := by rw [e1]; exact mul_pos hs hC
    exact (pos_iff_pos_of_mul_pos this).1 hα0

/-- Pentagon `b', a, c', a', c` in the frame `((a-d)/(β1-1), b-d, (b'-c)/(β1-1))`. -/
def k24h1lY (α β B g : ℝ) : ZMod 5 → ℝ × ℝ × ℝ :=
  ![(-α, 0, β), (β - 1, 0, 0), (α * (β - 1), β, 0), (-α * g, B, g), (-α, 0, 1)]

theorem k24h1lY_0 : k24h1lY α β B g 0 = (-α, 0, β) := rfl
theorem k24h1lY_1 : k24h1lY α β B g 1 = (β - 1, 0, 0) := rfl
theorem k24h1lY_2 : k24h1lY α β B g 2 = (α * (β - 1), β, 0) := rfl
theorem k24h1lY_3 : k24h1lY α β B g 3 = (-α * g, B, g) := rfl
theorem k24h1lY_4 : k24h1lY α β B g 4 = (-α, 0, 1) := rfl

theorem k24h1lY_inj {α β B g : ℝ} (hα : 1 < α) (hβ : 1 < β) (hB : 1 < B) (hg : 1 < g) :
    ∀ i j, k24h1lY α β B g i = k24h1lY α β B g j → i = j := by
  intro i j h
  have h1 : 0 < α * (g - 1) := mul_pos (by linarith) (by linarith)
  have h2 : 0 < α * (β - 1) := mul_pos (by linarith) (by linarith)
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    simp only [k24h1lY_0, k24h1lY_1, k24h1lY_2, k24h1lY_3, k24h1lY_4, Prod.mk.injEq] at h <;>
    first | rfl | (exfalso; linarith) | (exfalso; obtain ⟨h1', h2', h3'⟩ := h; linarith) |
      (exfalso; obtain ⟨h1', h2', h3'⟩ := h; nlinarith)

set_option maxHeartbeats 12800000 in
theorem k24h1l_tsc {D α β B g v1 v2 : ℝ} (hD : 0 < D) (hα : 1 < α) (hβ : 1 < β) (hB : 1 < B) (hg : 1 < g)
    (hβB : β < B + g) (hv2 : 0 < v2) (hw : 0 < -B * v1 - α * (g - 1) * v2) :
    (∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      TSc D (k24h1lY α β B g (i + 1) - k24h1lY α β B g i) (k24h1lY α β B g j - k24h1lY α β B g i) (v1, v2, 0)) ∧
    (∀ t ∈ [((0 : ℝ), (0 : ℝ), (0 : ℝ)), (0, 1, 0)], ∀ i : ZMod 5,
      TSc D (k24h1lY α β B g (i + 1) - k24h1lY α β B g i) (t - k24h1lY α β B g i) (v1, v2, 0)) := by
  obtain ⟨e0, e1, e2, e3, e4, f0, f1, f2, f3, f4⟩ := k19_z5
  have hs : 0 < β - 1 := by linarith
  have ha1 : 0 < α - 1 := by linarith
  have hα0 : 0 < α := by linarith
  have hβ0 : 0 < β := by linarith
  have hB0 : 0 < B := by linarith
  have hg0 : 0 < g := by linarith
  have hg1 : 0 < g - 1 := by linarith
  have ht : 0 < g + B - 1 := by linarith
  have hu : 0 < B + g - β := by linarith
  have hsα : 0 < β - 1 + α := by linarith
  have hnv1 : 0 < -v1 := by nlinarith [mul_pos hα0 (mul_pos hg1 hv2), mul_pos hB0 hB0]
  have hav : 0 < α * v2 - v1 := by nlinarith [mul_pos hα0 hv2]
  have x1 := mul_pos hD (mul_pos hβ0 hsα)
  have x2 := mul_pos hD (mul_pos hsα hB0)
  have x3 := mul_pos hD (mul_pos (mul_pos hsα hs) hv2)
  have x4 := mul_pos hD (add_pos (mul_pos (mul_pos hs ha1) hB0) (mul_pos hβ0 (add_pos (mul_pos hα0 hg0) hs)))
  have x5 := mul_pos hD (mul_pos hβ0 (add_pos hα0 hs))
  have x6 := mul_pos hD (mul_pos (mul_pos hα0 hβ0) ht)
  have x7 := mul_pos hD (add_pos (add_pos (mul_pos hg0 hsα) (mul_pos (mul_pos hα0 hβ0) hs))
    (mul_pos hu (mul_pos hs ha1)))
  have x8 := mul_pos hD (mul_pos hs hw)
  have x9 := mul_pos hD (mul_pos (mul_pos hβ0 hs) hv2)
  have x10 := mul_pos hD (mul_pos hβ0 hs)
  have x11 := mul_pos hD (mul_pos hα0 (add_pos (mul_pos hβ0 hg0) (mul_pos hB0 hs)))
  have x12 := mul_pos hD (mul_pos hα0 hB0)
  have x13 := mul_pos hD (mul_pos (mul_pos hs hα0) hv2)
  have x14 := mul_pos hD hsα
  have x15 := mul_pos hD (mul_pos hs (by linarith : 0 < α - 1 + β))
  have x16 := mul_pos hD (mul_pos (mul_pos hα0 hs) ht)
  have x17 := mul_pos hD (mul_pos hα0 ht)
  have x18 := mul_pos hD (mul_pos hs hav)
  have x19 := mul_pos hD (mul_pos (mul_pos hs hβ0) hav)
  refine ⟨?_, ?_⟩
  · intro i j h1 h2'
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl h1
      | exact (h2' (by decide)).elim
      | (simp only [TSc, d3, e0, e1, e2, e3, e4, f0, f1, f2, f3, f4, k24h1lY_0, k24h1lY_1, k24h1lY_2, k24h1lY_3,
          k24h1lY_4, Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
         first
         | (left; first | linarith | nlinarith)
         | (right; refine ⟨by ring, ?_⟩; first | linarith | nlinarith))
  · intro t ht' i
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht'
    rcases ht' with rfl | rfl <;>
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      (simp only [TSc, d3, e0, e1, e2, e3, e4, f0, f1, f2, f3, f4, k24h1lY_0, k24h1lY_1, k24h1lY_2, k24h1lY_3,
          k24h1lY_4, Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
       first
       | (left; first | linarith | nlinarith)
       | (right; refine ⟨by ring, ?_⟩; first | linarith | nlinarith))

set_option maxHeartbeats 3200000 in
/-- Metric facts of the cell. -/
theorem k24h1l_keys {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ}
    (hC : K6mCoords a a' b b' c c' d α1 β1 β6 γ6) (hM : K6sM a a' b b' c c' d)
    (hrel : K16Rel a b c d α1 β1)
    (hα1 : 1 < α1) (hβ1 : 1 < β1) (hβ6 : 1 < β6) (hγ6 : 1 < γ6)
    (ht : ⟪c - a', a - b'⟫ = 0) :
    0 < ⟪c - a', b' - c⟫ ∧ 0 < ⟪b' - a, b' - c⟫ ∧
      (⟪a - c', b' - c⟫ = 0 → 0 < ⟪c' - a, a - d⟫) := by
  obtain ⟨hdet, hc', hb', ha', -, -, -, -, -, -⟩ := hC
  obtain ⟨hm0, hm1, hm2⟩ := hM
  obtain ⟨hr1, hr2⟩ := hrel
  obtain ⟨P, hP⟩ : ∃ P : ℝ³, P = a - d := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ³, Q = b - d := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R : ℝ³, R = c - d := ⟨_, rfl⟩
  have hPd : a - d = P := hP.symm
  have hQd : b - d = Q := hQ.symm
  have hRd : c - d = R := hR.symm
  rw [hPd, hQd, hRd] at hr1
  rw [hQd, hRd] at hr2
  rw [hPd, hQd, hRd] at hdet
  have eE1 : c - a' = (0:ℝ) • P + (-β6) • Q + (1 - γ6) • R := by rw [ha', hP, hQ, hR]; module
  have eE2 : b' - c = α1 • P + (0:ℝ) • Q + (β1 - 1) • R := by rw [hb', hP, hR]; module
  have eE3 : b' - a = (α1 - 1) • P + (0:ℝ) • Q + β1 • R := by rw [hb', hP, hR]; module
  have eE4 : a - c' = (1 - α1) • P + (-β1) • Q + (0:ℝ) • R := by rw [hc', hP, hQ]; module
  have eE5 : c' - a = (α1 - 1) • P + β1 • Q + (0:ℝ) • R := by rw [hc', hP, hQ]; module
  have eE6 : a - b' = (1 - α1) • P + (0:ℝ) • Q + (-β1) • R := by rw [hb', hP, hR]; module
  have eE7 : a - d = (1:ℝ) • P + (0:ℝ) • Q + (0:ℝ) • R := by rw [hP]; module
  have eE8 : b - c = (0:ℝ) • P + (1:ℝ) • Q + (-1:ℝ) • R := by rw [hQ, hR]; module
  have eE9 : c' - d = α1 • P + β1 • Q + (0:ℝ) • R := by rw [hc', hP, hQ]; module
  have eE10 : b' - d = α1 • P + (0:ℝ) • Q + β1 • R := by rw [hb', hP, hR]; module
  have hPR : ⟪P, R⟫ = ⟪P, Q⟫ := by
    have e8 : b - c = Q - R := by rw [hQ, hR]; abel
    rw [hPd, e8, inner_sub_right] at hm0; linarith
  have hex := k24h1l_ex P Q R hPR
  have hqq : ⟪Q, R⟫ < ⟪Q, Q⟫ := by
    rw [eE9, eE8, hex] at hm1
    have : 0 < β1 * (⟪Q, Q⟫ - ⟪Q, R⟫) := by linarith
    have := (pos_iff_pos_of_mul_pos this).1 (by linarith)
    linarith
  have hrr : ⟪Q, R⟫ < ⟪R, R⟫ := by
    rw [eE10, eE8, hex] at hm2
    have : 0 < β1 * (⟪R, R⟫ - ⟪Q, R⟫) := by linarith
    have := (pos_iff_pos_of_mul_pos this).1 (by linarith)
    linarith
  have hpd := k24h1l_pd hdet hPR
  rw [eE1, eE6, hex] at ht
  obtain ⟨r1, r2, r3⟩ := k24h1l_real hα1 hβ1 hβ6 hγ6 hr2 hqq hrr hpd hr1 (by linarith [ht])
  refine ⟨?_, ?_, ?_⟩
  · rw [eE1, eE2, hex]; linarith [r1]
  · rw [eE3, eE2, hex]; linarith [r2]
  · intro hL
    rw [eE4, eE2, hex] at hL
    rw [eE5, eE7, hex]
    linarith [r3 (by linarith [hL])]

end C2
end Type08Sp
end Minimality
