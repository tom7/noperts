module

public import Minimality.Type08S.C2K17GA2

@[expose] public section


/-!
# K17GA / GA3: R3 (S1.1c) depth facts and wrappers
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


/-- Scalar core of the R3 depth facts.  `K = (α1-1)γ4`, `m = w + γ4 α1`. -/
theorem k17ga_r3_scalar {α1 β1 β6 w γ4 A Zq ZZ YY : ℝ} (hα1 : 1 < α1) (hβ1 : 0 < β1) (hw : 0 < w) (hγ4 : 0 < γ4)
    (hb6 : 1 ≤ β6) (hbr : w * (1 - β1) ≤ γ4 * α1 * (β6 - 1)) (hA : 0 < A) (hZZ : 0 ≤ ZZ) (hYY : 0 ≤ YY)
    (hcs : Zq ^ 2 ≤ A * ZZ)
    (hL : 0 < (β6 - β1) * (((α1 - 1) * γ4) * Zq + (w + γ4 * α1) * β1 * A) - ((α1 - 1) * γ4) * ZZ -
      (w + γ4 * α1) * β1 * Zq) :
    0 < ((α1 - 1) * γ4) * Zq + (w + γ4 * α1) * β1 * A ∧
    0 < (β6 - 1) * (w + γ4 * α1) * (((α1 - 1) * γ4) * Zq + (w + γ4 * α1) * β1 * A) + α1 * (α1 - 1) * YY -
      w * (α1 - 1) * γ4 * ZZ - w * β1 * (w + γ4 * α1) * Zq := by
  obtain ⟨m, hm⟩ : ∃ m, m = w + γ4 * α1 := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K, K = (α1 - 1) * γ4 := ⟨_, rfl⟩
  rw [← hm, ← hK] at hL ⊢
  have hKp : 0 < K := by rw [hK]; exact mul_pos (by linarith) hγ4
  have hmp : 0 < m := by rw [hm]; have := mul_pos hγ4 (by linarith : (0:ℝ) < α1); linarith
  have hmK : K < m := by rw [hK, hm]; nlinarith
  have hM1 : 0 < K * Zq + m * β1 * A := by
    by_contra hh; push Not at hh
    -- u = -Zq, m β1 A ≤ K u
    have hu : m * β1 * A ≤ K * (-Zq) := by linarith
    have hupos : 0 < -Zq := by
      by_contra h2; push Not at h2
      nlinarith [mul_pos (mul_pos hmp hβ1) hA, mul_nonneg hKp.le (by linarith : 0 ≤ Zq)]
    -- K ZZ A ≥ K u^2 ; form ≥ 0
    have h1 : K * (Zq ^ 2) ≤ K * (A * ZZ) := mul_le_mul_of_nonneg_left hcs hKp.le
    have h2 : 0 ≤ K * ZZ + β1 * (K + m) * Zq + m * β1 ^ 2 * A := by
      have h3 : 0 ≤ (K * (-Zq) - m * β1 * A) * ((-Zq) - β1 * A) := by
        apply mul_nonneg (by linarith)
        nlinarith [mul_pos hβ1 hA, mul_pos hmp hβ1, mul_pos (sub_pos.2 hmK) hβ1]
      nlinarith [mul_pos hA hA, mul_pos hA hβ1]
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ β6) (by linarith : 0 ≤ -(K * Zq + m * β1 * A))]
  refine ⟨hM1, ?_⟩
  have hb : 0 ≤ γ4 * α1 * (β6 - 1) - w * (1 - β1) := by linarith
  subst hm hK
  nlinarith [mul_pos hw hL, mul_nonneg hb hM1.le, mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ α1) (by linarith : (0:ℝ) ≤ α1 - 1)) hYY]

/-- Gram form of the R3 facts: `F1 = ⟪q,U⟫ > 0`, `F2 = ⟪a'-b,U⟫ > 0`, `⟪Y,U⟫ > 0` from `L2 = ⟪a'-c',U⟫ > 0`.
`U = (α1-1)p + β1 q`, `Y = w p + γ4 r`, ties `⟪Y,q⟫ = 0`, `⟪Y, α1 p + β1 q - r⟫ = 0`. -/
theorem k17ga_r3_gram {α1 β1 β6 w γ4 pp pq pr qq qr rr : ℝ} (hα1 : 1 < α1) (hβ1 : 0 < β1) (hw : 0 < w)
    (hγ4 : 0 < γ4) (hb6 : 1 ≤ β6) (hbr : w * (1 - β1) ≤ γ4 * α1 * (β6 - 1)) (hA : 0 < qq)
    (hZZ : 0 ≤ α1 ^ 2 * pp - 2 * α1 * pr + rr) (hYY : 0 < w ^ 2 * pp + 2 * w * γ4 * pr + γ4 ^ 2 * rr)
    (hcs : (α1 * pq - qr) ^ 2 ≤ qq * (α1 ^ 2 * pp - 2 * α1 * pr + rr))
    (E1 : w * pq + γ4 * qr = 0)
    (E2 : α1 * (w * pp + γ4 * pr) + β1 * (w * pq + γ4 * qr) - (w * pr + γ4 * rr) = 0)
    (hL : 0 < (β6 - β1) * ((α1 - 1) * pq + β1 * qq) -
      (α1 * (α1 - 1) * pp + α1 * β1 * pq - (α1 - 1) * pr - β1 * qr)) :
    0 < (α1 - 1) * pq + β1 * qq ∧
    0 < (β6 - 1) * ((α1 - 1) * pq + β1 * qq) + ((α1 - 1) * pr + β1 * qr) ∧
    0 < (α1 - 1) * (w * pp + γ4 * pr) + β1 * (w * pq + γ4 * qr) := by
  obtain ⟨m, hm⟩ : ∃ m, m = w + γ4 * α1 := ⟨_, rfl⟩
  have hmp : 0 < m := by rw [hm]; have := mul_pos hγ4 (by linarith : (0:ℝ) < α1); linarith
  have hF1 : m * ((α1 - 1) * pq + β1 * qq) = ((α1 - 1) * γ4) * (α1 * pq - qr) + m * β1 * qq := by
    rw [hm]; linear_combination (α1 - 1) * E1
  have hL2 : m * ((β6 - β1) * ((α1 - 1) * pq + β1 * qq) -
      (α1 * (α1 - 1) * pp + α1 * β1 * pq - (α1 - 1) * pr - β1 * qr)) =
      (β6 - β1) * (((α1 - 1) * γ4) * (α1 * pq - qr) + m * β1 * qq) - ((α1 - 1) * γ4) * (α1 ^ 2 * pp - 2 * α1 * pr + rr) -
      m * β1 * (α1 * pq - qr) := by
    rw [hm]; linear_combination (β6 - β1) * (α1 - 1) * E1 - (α1 - 1) * E2 + (α1 - 1) * β1 * E1 + (α1-1) * 0
  have hqr : qr = -(w * pq) / γ4 := by field_simp; linarith
  have hrr : rr = (α1 * (w * pp + γ4 * pr) + β1 * (w * pq + γ4 * qr) - w * pr) / γ4 := by
    field_simp; linarith
  have hF2 : m ^ 2 * ((β6 - 1) * ((α1 - 1) * pq + β1 * qq) + ((α1 - 1) * pr + β1 * qr)) =
      (β6 - 1) * m * (((α1 - 1) * γ4) * (α1 * pq - qr) + m * β1 * qq) +
        α1 * (α1 - 1) * (w ^ 2 * pp + 2 * w * γ4 * pr + γ4 ^ 2 * rr) -
        w * (α1 - 1) * γ4 * (α1 ^ 2 * pp - 2 * α1 * pr + rr) - w * β1 * m * (α1 * pq - qr) := by
    rw [hm, hrr, hqr]; field_simp; ring
  have hX : m * ((α1 - 1) * (w * pp + γ4 * pr) + β1 * (w * pq + γ4 * qr)) = (α1 - 1) * (w ^ 2 * pp + 2 * w * γ4 * pr + γ4 ^ 2 * rr) := by
    rw [hm, hrr, hqr]; field_simp; ring
  have hLm : 0 < (β6 - β1) * (((α1 - 1) * γ4) * (α1 * pq - qr) + (w + γ4 * α1) * β1 * qq) -
      ((α1 - 1) * γ4) * (α1 ^ 2 * pp - 2 * α1 * pr + rr) - (w + γ4 * α1) * β1 * (α1 * pq - qr) := by
    rw [← hm, ← hL2]; exact mul_pos hmp hL
  obtain ⟨h1, h2⟩ := k17ga_r3_scalar hα1 hβ1 hw hγ4 hb6 hbr hA hZZ hYY.le hcs hLm
  rw [← hm] at h1 h2
  refine ⟨?_, ?_, ?_⟩
  · rw [← hF1] at h1; exact pos_of_mul_pos_right h1 hmp.le
  · have : 0 < m ^ 2 * ((β6 - 1) * ((α1 - 1) * pq + β1 * qq) + ((α1 - 1) * pr + β1 * qr)) := by
      rw [hF2]; convert h2 using 1
    exact pos_of_mul_pos_right this (by positivity)
  · have : 0 < m * ((α1 - 1) * (w * pp + γ4 * pr) + β1 * (w * pq + γ4 * qr)) := by
      rw [hX]; exact mul_pos (by linarith) hYY
    exact pos_of_mul_pos_right this hmp.le

theorem k17ga_ip3 (p q r : ℝ³) (x1 x2 x3 y1 y2 y3 : ℝ) :
    ⟪x1 • p + x2 • q + x3 • r, y1 • p + y2 • q + y3 • r⟫ =
      x1 * y1 * ⟪p, p⟫ + (x1 * y2 + x2 * y1) * ⟪p, q⟫ + (x1 * y3 + x3 * y1) * ⟪p, r⟫ + x2 * y2 * ⟪q, q⟫ +
        (x2 * y3 + x3 * y2) * ⟪q, r⟫ + x3 * y3 * ⟪r, r⟫ := by
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
  rw [real_inner_comm q p, real_inner_comm r p, real_inner_comm r q]
  ring

theorem k17ga_ipc (p q r u v : ℝ³) (x1 x2 x3 y1 y2 y3 : ℝ) (hu : u = x1 • p + x2 • q + x3 • r)
    (hv : v = y1 • p + y2 • q + y3 • r) :
    ⟪u, v⟫ = x1 * y1 * ⟪p, p⟫ + (x1 * y2 + x2 * y1) * ⟪p, q⟫ + (x1 * y3 + x3 * y1) * ⟪p, r⟫ + x2 * y2 * ⟪q, q⟫ +
        (x2 * y3 + x3 * y2) * ⟪q, r⟫ + x3 * y3 * ⟪r, r⟫ := by
  subst hu hv; exact k17ga_ip3 _ _ _ _ _ _ _ _ _

set_option maxHeartbeats 3200000 in
/-- **R3 core** (both regimes): from the Zdb(i) ties and `ζ_{a-c'}(c',a') > 0` the cell `(a,d,b,a',b')@a-c'`. -/
theorem k17ga_r3_core {a a' b b' c c' d : ℝ³} {α1 α4 β1 γ4 β6 : ℝ} (hdet : det3 (a - d) (b - d) (c - d) ≠ 0)
    (hc' : c' = d + α1 • (a - d) + β1 • (b - d)) (hb' : b' = d + α4 • (a - d) + γ4 • (c - d))
    (ha' : a' = d + β6 • (b - d) + (1 : ℝ) • (c - d)) (hα1 : 1 < α1) (hβ1 : 0 < β1) (hα4 : 1 < α4)
    (hγ4 : 1 < γ4) (hb6 : 1 ≤ β6) (hbr : (α4 - 1) * (1 - β1) ≤ γ4 * α1 * (β6 - 1))
    (E1 : ⟪d - b, a - b'⟫ = 0) (E2 : ⟪c' - c, a - b'⟫ = 0) (hL : 0 < ⟪c' - a', a - c'⟫) :
    HasLexCell (V8 a a' b b' c c' d) := by
  obtain ⟨w, hwdef⟩ : ∃ w, w = α4 - 1 := ⟨_, rfl⟩
  have hw : 0 < w := by linarith
  have hdet' := hdet
  obtain ⟨p, hp⟩ : ∃ p, p = a - d := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q, q = b - d := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r, r = c - d := ⟨_, rfl⟩
  have v1 : a - c' = (-(α1 - 1)) • p + (-β1) • q + (0 : ℝ) • r := by rw [hc', hp, hq]; module
  have v2 : a - b' = (-w) • p + (0 : ℝ) • q + (-γ4) • r := by rw [hb', hwdef, hp, hr]; module
  have v3 : d - b = (0 : ℝ) • p + (-1 : ℝ) • q + (0 : ℝ) • r := by rw [hq]; module
  have v4 : c' - c = α1 • p + β1 • q + (-1 : ℝ) • r := by rw [hc', hr, hp, hq]; module
  have v5 : c' - a' = α1 • p + (β1 - β6) • q + (-1 : ℝ) • r := by rw [hc', ha', hp, hq, hr]; module
  have E1' := E1
  have E2' := E2
  have hL' := hL
  rw [k17ga_ipc p q r _ _ _ _ _ _ _ _ v3 v2] at E1'
  rw [k17ga_ipc p q r _ _ _ _ _ _ _ _ v4 v2] at E2'
  rw [k17ga_ipc p q r _ _ _ _ _ _ _ _ v5 v1] at hL'
  rw [← hp, ← hq, ← hr] at hdet'
  have hqne : q ≠ 0 := by
    intro h; apply hdet'; rw [h]; simp [det3_expand]
  have hYne : w • p + γ4 • r ≠ 0 := by
    intro h
    have e : det3 p q (w • p + γ4 • r) = γ4 * det3 p q r := by
      simp only [det3_expand, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
    rw [h] at e
    have : γ4 * det3 p q r = 0 := by rw [← e]; simp [det3_expand]
    exact hdet' ((mul_eq_zero.1 this).resolve_left (by linarith))
  have hzz := k17ga_ipc p q r (α1 • p + (0 : ℝ) • q + (-1 : ℝ) • r) (α1 • p + (0 : ℝ) • q + (-1 : ℝ) • r)
    α1 0 (-1) α1 0 (-1) rfl rfl
  have hyy := k17ga_ipc p q r (w • p + (0 : ℝ) • q + γ4 • r) (w • p + (0 : ℝ) • q + γ4 • r) w 0 γ4 w 0 γ4 rfl rfl
  have hzq := k17ga_ipc p q r (α1 • p + (0 : ℝ) • q + (-1 : ℝ) • r) ((0 : ℝ) • p + (1 : ℝ) • q + (0 : ℝ) • r)
    α1 0 (-1) 0 1 0 rfl rfl
  have hZZ := real_inner_self_nonneg (x := α1 • p + (0 : ℝ) • q + (-1 : ℝ) • r)
  have hYY : 0 < ⟪w • p + (0 : ℝ) • q + γ4 • r, w • p + (0 : ℝ) • q + γ4 • r⟫ :=
    real_inner_self_pos.2 (by simpa using hYne)
  have hcs := real_inner_mul_inner_self_le (α1 • p + (0 : ℝ) • q + (-1 : ℝ) • r) q
  have hqq := real_inner_self_pos.2 hqne
  have hqq' : ⟪q, q⟫ = ⟪q, q⟫ := rfl
  have hzq' : ⟪α1 • p + (0 : ℝ) • q + (-1 : ℝ) • r, q⟫ = α1 * ⟪p, q⟫ - ⟪q, r⟫ := by
    have := hzq
    rw [show (0 : ℝ) • p + (1 : ℝ) • q + (0 : ℝ) • r = q by module] at this
    rw [this]; ring
  rw [hzq'] at hcs
  rw [hzz] at hZZ hcs
  rw [hyy] at hYY
  obtain ⟨F1, F2, F3⟩ := k17ga_r3_gram (α1 := α1) (β1 := β1) (β6 := β6) (w := w) (γ4 := γ4) (pp := ⟪p, p⟫) (pq := ⟪p, q⟫) (pr := ⟪p, r⟫) (qq := ⟪q, q⟫)
    (qr := ⟪q, r⟫) (rr := ⟪r, r⟫) hα1 hβ1 hw (by linarith) hb6 (by rw [hwdef] at *; linarith) hqq
    (by linarith) (by linarith) (by nlinarith [hcs]) (by nlinarith [E1']) (by nlinarith [E2']) (by nlinarith [hL'])
  have c1 := k17ga_ipc p q r q (a - c') 0 1 0 (-(α1 - 1)) (-β1) 0 (by module) v1
  have c2 := k17ga_ipc p q r r (a - c') 0 0 1 (-(α1 - 1)) (-β1) 0 (by module) v1
  have c3 := k17ga_ipc p q r p (a - c') 1 0 0 (-(α1 - 1)) (-β1) 0 (by module) v1
  refine k17ga_r3_cell (a := a) (a' := a') (b := b) (b' := b') (c := c) (c' := c') (d := d) hdet hc' hb' ha'
    hα1 hβ1 hα4.le hγ4 hb6 ?_ ?_ ?_
  · rw [← hq, c1]; nlinarith [F1]
  · rw [← hq, ← hr, c1, c2]; nlinarith [F2]
  · rw [← hr, ← hp, c2, c3]; rw [hwdef] at *; nlinarith [F3]

end C2
end Type08Sp
end Minimality
