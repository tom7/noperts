module

public import Minimality.Type08S.C2K17GA12
public import Minimality.Type08S.C2K18A

@[expose] public section


/-!
# K18 / B: S1.1 R3 on the closed side (`ζ_{a-c'}(c',a') ≥ 0`), closing the S1.1 ties (L1, L2)

K17GA's R3 (`k17ga_r3_core`) needs `ζ_{a-c'}(c',a') > 0` only to make three Gram forms positive.  With the strict
Cauchy-Schwarz inequality for `Z = α1 p - r` and `q` (strict because `det3 p q r ≠ 0`) and `⟪Y,Y⟫ > 0`, the same forms
are positive for `ζ ≥ 0`: the tie `ζ = 0` is not a cycle tie of R3 (`c'` is not on R3's cycle).
-/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

/-- `k17ga_r3_scalar` with `hL ≥ 0`, strict Cauchy-Schwarz and `YY > 0`. -/
theorem k18_r3_scalar {α1 β1 β6 w γ4 A Zq ZZ YY : ℝ} (hα1 : 1 < α1) (hβ1 : 0 < β1) (hw : 0 < w) (hγ4 : 0 < γ4)
    (hb6 : 1 ≤ β6) (hbr : w * (1 - β1) ≤ γ4 * α1 * (β6 - 1)) (hA : 0 < A) (hZZ : 0 ≤ ZZ) (hYY : 0 < YY)
    (hcs : Zq ^ 2 < A * ZZ)
    (hL : 0 ≤ (β6 - β1) * (((α1 - 1) * γ4) * Zq + (w + γ4 * α1) * β1 * A) - ((α1 - 1) * γ4) * ZZ -
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
    have hu : m * β1 * A ≤ K * (-Zq) := by linarith
    have hupos : 0 < -Zq := by
      by_contra h2; push Not at h2
      nlinarith [mul_pos (mul_pos hmp hβ1) hA, mul_nonneg hKp.le (by linarith : 0 ≤ Zq)]
    have h1 : K * (Zq ^ 2) < K * (A * ZZ) := mul_lt_mul_of_pos_left hcs hKp
    have h3 : 0 ≤ (K * (-Zq) - m * β1 * A) * ((-Zq) - β1 * A) := by
      apply mul_nonneg (by linarith)
      nlinarith [mul_pos hβ1 hA, mul_pos hmp hβ1, mul_pos (sub_pos.2 hmK) hβ1]
    have h2 : 0 < A * (K * ZZ + β1 * (K + m) * Zq + m * β1 ^ 2 * A) := by nlinarith
    have h2' : 0 < K * ZZ + β1 * (K + m) * Zq + m * β1 ^ 2 * A := pos_of_mul_pos_right h2 hA.le
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ β6) (by linarith : 0 ≤ -(K * Zq + m * β1 * A))]
  refine ⟨hM1, ?_⟩
  have hb : 0 ≤ γ4 * α1 * (β6 - 1) - w * (1 - β1) := by linarith
  subst hm hK
  nlinarith [mul_nonneg hw.le hL, mul_nonneg hb hM1.le,
    mul_pos (mul_pos (by linarith : (0:ℝ) < α1) (by linarith : (0:ℝ) < α1 - 1)) hYY]

/-- `k17ga_r3_gram` with `hL ≥ 0` and strict Cauchy-Schwarz. -/
theorem k18_r3_gram {α1 β1 β6 w γ4 pp pq pr qq qr rr : ℝ} (hα1 : 1 < α1) (hβ1 : 0 < β1) (hw : 0 < w)
    (hγ4 : 0 < γ4) (hb6 : 1 ≤ β6) (hbr : w * (1 - β1) ≤ γ4 * α1 * (β6 - 1)) (hA : 0 < qq)
    (hZZ : 0 ≤ α1 ^ 2 * pp - 2 * α1 * pr + rr) (hYY : 0 < w ^ 2 * pp + 2 * w * γ4 * pr + γ4 ^ 2 * rr)
    (hcs : (α1 * pq - qr) ^ 2 < qq * (α1 ^ 2 * pp - 2 * α1 * pr + rr))
    (E1 : w * pq + γ4 * qr = 0)
    (E2 : α1 * (w * pp + γ4 * pr) + β1 * (w * pq + γ4 * qr) - (w * pr + γ4 * rr) = 0)
    (hL : 0 ≤ (β6 - β1) * ((α1 - 1) * pq + β1 * qq) -
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
  have hX : m * ((α1 - 1) * (w * pp + γ4 * pr) + β1 * (w * pq + γ4 * qr)) =
      (α1 - 1) * (w ^ 2 * pp + 2 * w * γ4 * pr + γ4 ^ 2 * rr) := by
    rw [hm, hrr, hqr]; field_simp; ring
  have hLm : 0 ≤ (β6 - β1) * (((α1 - 1) * γ4) * (α1 * pq - qr) + (w + γ4 * α1) * β1 * qq) -
      ((α1 - 1) * γ4) * (α1 ^ 2 * pp - 2 * α1 * pr + rr) - (w + γ4 * α1) * β1 * (α1 * pq - qr) := by
    rw [← hm, ← hL2]; exact mul_nonneg hmp.le hL
  obtain ⟨h1, h2⟩ := k18_r3_scalar hα1 hβ1 hw hγ4 hb6 hbr hA hZZ hYY hcs hLm
  rw [← hm] at h1 h2
  refine ⟨?_, ?_, ?_⟩
  · rw [← hF1] at h1; exact pos_of_mul_pos_right h1 hmp.le
  · have : 0 < m ^ 2 * ((β6 - 1) * ((α1 - 1) * pq + β1 * qq) + ((α1 - 1) * pr + β1 * qr)) := by
      rw [hF2]; convert h2 using 1
    exact pos_of_mul_pos_right this (by positivity)
  · have : 0 < m * ((α1 - 1) * (w * pp + γ4 * pr) + β1 * (w * pq + γ4 * qr)) := by
      rw [hX]; exact mul_pos (by linarith) hYY
    exact pos_of_mul_pos_right this hmp.le

/-- Strict Cauchy-Schwarz for `x` and `y` when `x - t y ≠ 0` for every `t`. -/
theorem k18_cs_strict (x y : ℝ³) (hy : y ≠ 0) (hxy : ∀ t : ℝ, x - t • y ≠ 0) :
    ⟪x, y⟫ ^ 2 < ⟪y, y⟫ * ⟪x, x⟫ := by
  have hyy : 0 < ⟪y, y⟫ := real_inner_self_pos.2 hy
  set t := ⟪x, y⟫ / ⟪y, y⟫ with ht
  have h := real_inner_self_pos.2 (hxy t)
  have e : ⟪x - t • y, x - t • y⟫ = ⟪x, x⟫ - 2 * t * ⟪x, y⟫ + t ^ 2 * ⟪y, y⟫ := by
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right]
    rw [real_inner_comm x y]; ring
  rw [e] at h
  have e2 : t * ⟪y, y⟫ = ⟪x, y⟫ := by rw [ht]; field_simp
  nlinarith [mul_pos hyy h]

set_option maxHeartbeats 3200000 in
/-- **R3 core, closed side**: as `k17ga_r3_core` with `0 ≤ ζ_{a-c'}(c',a')`. -/
theorem k18_r3_core {a a' b b' c c' d : ℝ³} {α1 α4 β1 γ4 β6 : ℝ} (hdet : det3 (a - d) (b - d) (c - d) ≠ 0)
    (hc' : c' = d + α1 • (a - d) + β1 • (b - d)) (hb' : b' = d + α4 • (a - d) + γ4 • (c - d))
    (ha' : a' = d + β6 • (b - d) + (1 : ℝ) • (c - d)) (hα1 : 1 < α1) (hβ1 : 0 < β1) (hα4 : 1 < α4)
    (hγ4 : 1 < γ4) (hb6 : 1 ≤ β6) (hbr : (α4 - 1) * (1 - β1) ≤ γ4 * α1 * (β6 - 1))
    (E1 : ⟪d - b, a - b'⟫ = 0) (E2 : ⟪c' - c, a - b'⟫ = 0) (hL : 0 ≤ ⟪c' - a', a - c'⟫) :
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
  have hZt : ∀ t : ℝ, (α1 • p + (0 : ℝ) • q + (-1 : ℝ) • r) - t • q ≠ 0 := by
    intro t h
    have e : det3 p q ((α1 • p + (0 : ℝ) • q + (-1 : ℝ) • r) - t • q) = -det3 p q r := by
      simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; ring
    rw [h] at e
    have : det3 p q r = 0 := by
      have h0 : det3 p q (0 : ℝ³) = 0 := by simp [det3_expand]
      linarith
    exact hdet' this
  have hzz := k17ga_ipc p q r (α1 • p + (0 : ℝ) • q + (-1 : ℝ) • r) (α1 • p + (0 : ℝ) • q + (-1 : ℝ) • r)
    α1 0 (-1) α1 0 (-1) rfl rfl
  have hyy := k17ga_ipc p q r (w • p + (0 : ℝ) • q + γ4 • r) (w • p + (0 : ℝ) • q + γ4 • r) w 0 γ4 w 0 γ4 rfl rfl
  have hzq := k17ga_ipc p q r (α1 • p + (0 : ℝ) • q + (-1 : ℝ) • r) ((0 : ℝ) • p + (1 : ℝ) • q + (0 : ℝ) • r)
    α1 0 (-1) 0 1 0 rfl rfl
  have hZZ := real_inner_self_nonneg (x := α1 • p + (0 : ℝ) • q + (-1 : ℝ) • r)
  have hYY : 0 < ⟪w • p + (0 : ℝ) • q + γ4 • r, w • p + (0 : ℝ) • q + γ4 • r⟫ :=
    real_inner_self_pos.2 (by simpa using hYne)
  have hcs := k18_cs_strict (α1 • p + (0 : ℝ) • q + (-1 : ℝ) • r) q hqne hZt
  have hqq := real_inner_self_pos.2 hqne
  have hzq' : ⟪α1 • p + (0 : ℝ) • q + (-1 : ℝ) • r, q⟫ = α1 * ⟪p, q⟫ - ⟪q, r⟫ := by
    have := hzq
    rw [show (0 : ℝ) • p + (1 : ℝ) • q + (0 : ℝ) • r = q by module] at this
    rw [this]; ring
  rw [hzq'] at hcs
  rw [hzz] at hZZ hcs
  rw [hyy] at hYY
  obtain ⟨F1, F2, F3⟩ := k18_r3_gram (α1 := α1) (β1 := β1) (β6 := β6) (w := w) (γ4 := γ4) (pp := ⟪p, p⟫)
    (pq := ⟪p, q⟫) (pr := ⟪p, r⟫) (qq := ⟪q, q⟫) (qr := ⟪q, r⟫) (rr := ⟪r, r⟫) hα1 hβ1 hw (by linarith) hb6
    (by rw [hwdef] at *; linarith) hqq (by linarith) (by linarith) (by nlinarith [hcs]) (by nlinarith [E1'])
    (by nlinarith [E2']) (by nlinarith [hL'])
  have c1 := k17ga_ipc p q r q (a - c') 0 1 0 (-(α1 - 1)) (-β1) 0 (by module) v1
  have c2 := k17ga_ipc p q r r (a - c') 0 0 1 (-(α1 - 1)) (-β1) 0 (by module) v1
  have c3 := k17ga_ipc p q r p (a - c') 1 0 0 (-(α1 - 1)) (-β1) 0 (by module) v1
  refine k17ga_r3_cell (a := a) (a' := a') (b := b) (b' := b') (c := c) (c' := c') (d := d) hdet hc' hb' ha'
    hα1 hβ1 hα4.le hγ4 hb6 ?_ ?_ ?_
  · rw [← hq, c1]; nlinarith [F1]
  · rw [← hq, ← hr, c1, c2]; nlinarith [F2]
  · rw [← hr, ← hp, c2, c3]; rw [hwdef] at *; nlinarith [F3]

/-- **S1.1 R3, Ta, closed side** (`ζ_{a-c'}(c',a') ≥ 0`). -/
theorem k18_s11_r3_ta {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (h : K17fZdbTa a a' b b' c c' d)
    (hz1 : ⟪c' - c, a - b'⟫ = 0) (hL : 0 ≤ ⟪c' - a', a - c'⟫) : HasLexCell (V8 a a' b b' c c' d) := by
  have hζ0 : ⟪d - b, a - b'⟫ = 0 := h.2.2.2.2.1
  obtain ⟨α1, α4, β1, γ4, β6, hdet, hc', hb', ha', hα11, hα41, hβ1, hγ4, hb6, hbc0, hE0⟩ :=
    k17ga_ta_coords W h
  have hg : 1 < γ4 := by
    by_contra hh; push Not at hh
    nlinarith [mul_pos (by linarith : (0:ℝ) < α4) (sub_pos.2 hβ1), mul_nonneg (by linarith : (0:ℝ) ≤ α1) (sub_nonneg.2 hh)]
  exact k18_r3_core hdet hc' hb' ha' hα11 (by linarith) hα41 hg hb6
    (by nlinarith [mul_nonneg (mul_pos hγ4 (by linarith : (0:ℝ) < α1)).le (sub_nonneg.2 hb6), mul_pos (sub_pos.2 hα41) (sub_pos.2 hβ1)])
    hζ0 hz1 hL

/-- **S1.1, Ta: closed.**  `K17fZdbTa` with the Zdb(i) tie `⟪c'-c, a-b'⟫ = 0` has a lex cell. -/
theorem k18_s11_ta {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (h : K17fZdbTa a a' b b' c c' d)
    (hz1 : ⟪c' - c, a - b'⟫ = 0) : HasLexCell (V8 a a' b b' c c' d) := by
  rcases k17ga_s11_ta W h hz1 with h1 | ⟨-, hL⟩
  · exact h1
  · exact k18_s11_r3_ta W h hz1 hL

set_option maxHeartbeats 3200000 in
/-- **S1.1 R3, Tc, closed side**: `qr ≥ 0`, `ζ_{c'-b}(d,b) ≤ 0`, `ζ_{a-c'}(c',a') ≥ 0`; leftover only
`ζ_{c'-b}(d,b) = 0 ∧ ⟪a-d,b-d⟫ = 0` (then `β1 = 1`). -/
theorem k18_s11_r3_tc {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (h : K17fZdbTc a a' b b' c c' d)
    (hz1 : ⟪c' - c, a - b'⟫ = 0) (hq : 0 ≤ ⟪b - d, c - d⟫) (h3 : ⟪d - b, c' - b⟫ ≤ 0)
    (hL : 0 ≤ ⟪c' - a', a - c'⟫) :
    HasLexCell (V8 a a' b b' c c' d) ∨ (⟪d - b, c' - b⟫ = 0 ∧ ⟪a - d, b - d⟫ = 0) := by
  have hζ0 : ⟪d - b, a - b'⟫ = 0 := h.2.2.1
  obtain ⟨α1, α4, β1, γ4, β6, hdet, hc', hb', ha', hα11, hα41, hβ1, hγ4, hb6, hpl, hE0⟩ :=
    k17ga_tc_coords W h
  have hqq : 0 < ⟪b - d, b - d⟫ := real_inner_self_pos.2 (by
    intro h0; apply hdet
    have : b - d = 0 := h0
    rw [this]; simp [det3_expand])
  have v3 : d - b = (0 : ℝ) • (a - d) + (-1 : ℝ) • (b - d) + (0 : ℝ) • (c - d) := by module
  have v2 : a - b' = (-(α4 - 1)) • (a - d) + (0 : ℝ) • (b - d) + (-γ4) • (c - d) := by rw [hb']; module
  have v6 : c' - b = α1 • (a - d) + (β1 - 1) • (b - d) + (0 : ℝ) • (c - d) := by rw [hc']; module
  have E1' := k17ga_ipc (a - d) (b - d) (c - d) _ _ _ _ _ _ _ _ v3 v2
  have h3' := k17ga_ipc (a - d) (b - d) (c - d) _ _ _ _ _ _ _ _ v3 v6
  have hζ0' := hζ0
  rw [E1'] at hζ0'
  have h3e := h3
  rw [h3'] at h3e
  have hpq : ⟪a - d, b - d⟫ ≤ 0 := by
    have hqr : ⟪b - d, c - d⟫ = -((α4 - 1) * ⟪a - d, b - d⟫) / γ4 := by
      field_simp; rw [real_inner_comm (b - d) (a - d)] at *; nlinarith [hζ0']
    rw [hqr] at hq
    have : 0 ≤ -((α4 - 1) * ⟪a - d, b - d⟫) := by
      by_contra hh; push Not at hh
      have := div_neg_of_neg_of_pos hh hγ4; linarith
    nlinarith
  rcases hpq.lt_or_eq with hpq | hpq
  · left
    have hβ : 1 < β1 := by
      by_contra hh; push Not at hh
      nlinarith [mul_pos (by linarith : (0:ℝ) < α1) (neg_pos.2 hpq), mul_nonneg (sub_nonneg.2 hh) hqq.le]
    have hg : 1 < γ4 := by
      by_contra hh; push Not at hh
      nlinarith [mul_pos (by linarith : (0:ℝ) < α4) (sub_pos.2 hβ), mul_nonneg (by linarith : (0:ℝ) ≤ α1) (sub_nonneg.2 hh)]
    exact k18_r3_core hdet hc' hb' ha' hα11 (by linarith) hα41 hg hb6
      (by nlinarith [mul_nonneg (mul_pos hγ4 (by linarith : (0:ℝ) < α1)).le (sub_nonneg.2 hb6), mul_pos (sub_pos.2 hα41) (sub_pos.2 hβ)])
      hζ0 hz1 hL
  · rcases h3.lt_or_eq with h3l | h3e0
    · left
      have hβ : 1 < β1 := by
        by_contra hh; push Not at hh
        rw [h3'] at h3l
        nlinarith [mul_nonneg (sub_nonneg.2 hh) hqq.le]
      have hg : 1 < γ4 := by
        by_contra hh; push Not at hh
        nlinarith [mul_pos (by linarith : (0:ℝ) < α4) (sub_pos.2 hβ), mul_nonneg (by linarith : (0:ℝ) ≤ α1) (sub_nonneg.2 hh)]
      exact k18_r3_core hdet hc' hb' ha' hα11 (by linarith) hα41 hg hb6
        (by nlinarith [mul_nonneg (mul_pos hγ4 (by linarith : (0:ℝ) < α1)).le (sub_nonneg.2 hb6), mul_pos (sub_pos.2 hα41) (sub_pos.2 hβ)])
        hζ0 hz1 hL
    · exact Or.inr ⟨h3e0, hpq⟩

/-- **S1.1, Tc**: `K17fZdbTc` with the Zdb(i) tie has a lex cell unless `ζ_{c'-b}(d,b) = 0 ∧ ⟪a-d,b-d⟫ = 0`. -/
theorem k18_s11_tc {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (h : K17fZdbTc a a' b b' c c' d)
    (hz1 : ⟪c' - c, a - b'⟫ = 0) :
    HasLexCell (V8 a a' b b' c c' d) ∨ (⟪d - b, c' - b⟫ = 0 ∧ ⟪a - d, b - d⟫ = 0) := by
  rcases k17f_s11_tc W h hz1 with h1 | ⟨hq, hL⟩
  · exact Or.inl h1
  · rcases lt_or_ge 0 ⟪d - b, c' - b⟫ with hl | hl
    · exact Or.inl (k17ga_s11_r2_tc W h hz1 hl)
    · exact k18_s11_r3_tc W h hz1 hq hl hL

end C2
end Type08Sp
end Minimality
