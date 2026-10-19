module

public import Minimality.Forces

@[expose] public section

/-!
# Lemma T at the tie, robust form: the scalar core

The force argument of "Lemma T at the tie, robust form"
(`FEWER-FACES-PROOFS.md` §7) after every force is written on its corner's
generators (`force_mem_cone`) and the equilibrium equations are dotted with
fixed test vectors. Weights `l j ≥ 0` sit on the generators `j ∈ J` of the
corners above the tie (the shared vertex and the chain corners), and
`π1, π3, κ3, κ2 ≥ 0` on the far ends `a` (generators `Ga`, `G3`) and `b`
(`G3`, `Gb`; `G3`, the generator of the edge `a b`, is shared). The numbers
are the generators' inner products with the test vectors `m`, `p`, two screen
axes, and their torques. `δ = z(b) - z(a) > 0` at the view is of order `ε`.

* E2·m bounds the mass on `J` by `δ K ν / (η κ)` (`ν` the far mass);
* E2·p and E1·p make `π3 = O(δ ν)` (the far end `a` loses its edge force);
* the far ends' generators with their torques form a nonsingular `3 × 3`
  system (the survivor's torque is nonzero), so Cramer bounds `π1, κ3, κ2`
  by `O(δ ν)`; hence `ν ≤ δ S ν`, and `ν = 0` once `δ S < 1`.
-/

namespace Minimality

open Finset

/-- Cramer's rule for three columns in `ℝ³`, as scalars. -/
theorem cramer3 {a1 a2 a3 b1 b2 b3 d1 d2 d3 x y z r1 r2 r3 : ℝ}
    (e1 : x * a1 + y * b1 + z * d1 = r1) (e2 : x * a2 + y * b2 + z * d2 = r2)
    (e3 : x * a3 + y * b3 + z * d3 = r3) :
    x * (a1 * (b2 * d3 - b3 * d2) - a2 * (b1 * d3 - b3 * d1) + a3 * (b1 * d2 - b2 * d1)) =
      r1 * (b2 * d3 - b3 * d2) - r2 * (b1 * d3 - b3 * d1) + r3 * (b1 * d2 - b2 * d1) := by
  subst e1 e2 e3; ring

/-- `|u * v - w * t| ≤ 2 K²` for entries bounded by `K`. -/
theorem abs_sub_mul_le {u v w t K : ℝ} (hu : |u| ≤ K) (hv : |v| ≤ K) (hw : |w| ≤ K)
    (ht : |t| ≤ K) : |u * v - w * t| ≤ 2 * K ^ 2 := by
  have hK : 0 ≤ K := (abs_nonneg u).trans hu
  calc |u * v - w * t| ≤ |u * v| + |w * t| := abs_sub _ _
    _ = |u| * |v| + |w| * |t| := by rw [abs_mul, abs_mul]
    _ ≤ K * K + K * K := add_le_add (mul_le_mul hu hv (abs_nonneg _) hK)
        (mul_le_mul hw ht (abs_nonneg _) hK)
    _ = 2 * K ^ 2 := by ring

/-- Cramer's bound: with entries of the last two columns bounded by `K`, the
right side bounded by `r`, and `|det| ≥ c`, the first unknown is at most
`6 r K² / c`. -/
theorem cramer3_bound {a1 a2 a3 b1 b2 b3 d1 d2 d3 x y z r1 r2 r3 K r c : ℝ}
    (e1 : x * a1 + y * b1 + z * d1 = r1) (e2 : x * a2 + y * b2 + z * d2 = r2)
    (e3 : x * a3 + y * b3 + z * d3 = r3)
    (hb1 : |b1| ≤ K) (hb2 : |b2| ≤ K) (hb3 : |b3| ≤ K)
    (hd1 : |d1| ≤ K) (hd2 : |d2| ≤ K) (hd3 : |d3| ≤ K)
    (hr1 : |r1| ≤ r) (hr2 : |r2| ≤ r) (hr3 : |r3| ≤ r) (hc : 0 < c)
    (hdet : c ≤ |a1 * (b2 * d3 - b3 * d2) - a2 * (b1 * d3 - b3 * d1) + a3 * (b1 * d2 - b2 * d1)|) :
    |x| ≤ 6 * r * K ^ 2 / c := by
  have key := cramer3 e1 e2 e3
  set Δ := a1 * (b2 * d3 - b3 * d2) - a2 * (b1 * d3 - b3 * d1) + a3 * (b1 * d2 - b2 * d1)
  have m1 := abs_sub_mul_le hb2 hd3 hb3 hd2
  have m2 := abs_sub_mul_le hb1 hd3 hb3 hd1
  have m3 := abs_sub_mul_le hb1 hd2 hb2 hd1
  have hr : 0 ≤ r := (abs_nonneg _).trans hr1
  have bound : |x| * |Δ| ≤ 6 * r * K ^ 2 := by
    rw [← abs_mul, key]
    calc _ ≤ |r1 * (b2 * d3 - b3 * d2)| + |r2 * (b1 * d3 - b3 * d1)| + |r3 * (b1 * d2 - b2 * d1)| :=
          (abs_add_le _ _).trans (by gcongr; exact abs_sub _ _)
      _ = |r1| * |b2 * d3 - b3 * d2| + |r2| * |b1 * d3 - b3 * d1| + |r3| * |b1 * d2 - b2 * d1| := by
          rw [abs_mul, abs_mul, abs_mul]
      _ ≤ r * (2 * K ^ 2) + r * (2 * K ^ 2) + r * (2 * K ^ 2) := by
          gcongr
      _ = 6 * r * K ^ 2 := by ring
  rw [le_div_iff₀ hc]
  calc |x| * c ≤ |x| * |Δ| := mul_le_mul_of_nonneg_left hdet (abs_nonneg _)
    _ ≤ _ := bound

set_option maxHeartbeats 2000000 in
/-- **The scalar core.** With the bounds below and `δ S < 1`, all weights
vanish. -/
theorem tie_core {ι : Type*} (J : Finset ι) (l ζ M P X1 X2 T : ι → ℝ)
    (π1 π3 κ3 κ2 δ : ℝ) (M3 Mb Pa P3 Pb X1a X13 X1b X2a X23 X2b Ta T3a T3b Tb : ℝ)
    (κ η Z K L c3 c : ℝ)
    (hl : ∀ j ∈ J, 0 ≤ l j) (h1 : 0 ≤ π1) (h3 : 0 ≤ π3) (k3 : 0 ≤ κ3) (k2 : 0 ≤ κ2)
    (hκ : 0 < κ) (hη : 0 < η) (hc3 : 0 < c3) (hc : 0 < c) (hδ : 0 < δ) (hL : 0 ≤ L)
    (hZ : 0 ≤ Z)
    (hM : ∀ j ∈ J, κ ≤ M j) (hζ : ∀ j ∈ J, η ≤ ζ j) (hζZ : ∀ j ∈ J, ζ j ≤ Z)
    (hP : ∀ j ∈ J, -(L * δ) ≤ P j) (hPK : ∀ j ∈ J, |P j| ≤ K)
    (hX1 : ∀ j ∈ J, |X1 j| ≤ K) (hX2 : ∀ j ∈ J, |X2 j| ≤ K) (hT : ∀ j ∈ J, |T j| ≤ K)
    (hM3 : |M3| ≤ K) (hMb : |Mb| ≤ K) (hPa : |Pa| ≤ L * δ) (hP3 : P3 ≤ -c3)
    (hX13 : |X13| ≤ K) (hX23 : |X23| ≤ K) (hT3a : |T3a| ≤ K)
    (hX1a : |X1a| ≤ K) (hX2a : |X2a| ≤ K) (hTa : |Ta| ≤ K) (hT3b : |T3b| ≤ K)
    (hX1b : |X1b| ≤ K) (hX2b : |X2b| ≤ K) (hTb : |Tb| ≤ K)
    (hdet : c ≤ |X1a * (X23 * Tb - T3b * X2b) - X2a * (X13 * Tb - T3b * X1b) +
      Ta * (X13 * X2b - X23 * X1b)|)
    (E1x : ∑ j ∈ J, l j * X1 j + π1 * X1a + (π3 + κ3) * X13 + κ2 * X1b = 0)
    (E1y : ∑ j ∈ J, l j * X2 j + π1 * X2a + (π3 + κ3) * X23 + κ2 * X2b = 0)
    (E1p : ∑ j ∈ J, l j * P j + π1 * Pa + (π3 + κ3) * P3 + κ2 * Pb = 0)
    (E2m : ∑ j ∈ J, l j * ζ j * M j + δ * (κ3 * M3 + κ2 * Mb) = 0)
    (E2p : ∑ j ∈ J, l j * ζ j * P j + δ * (κ3 * P3 + κ2 * Pb) = 0)
    (E3 : ∑ j ∈ J, l j * T j + π1 * Ta + π3 * T3a + κ3 * T3b + κ2 * Tb = 0)
    (hsmall : δ * (18 * K ^ 3 * (K / (η * κ) + ((K + L * Z) * K / (η * κ) + L) / c3) / c +
      ((K + L * Z) * K / (η * κ) + L) / c3) < 1) :
    (∀ j ∈ J, l j = 0) ∧ π1 = 0 ∧ π3 = 0 ∧ κ3 = 0 ∧ κ2 = 0 := by
  have hK : 0 ≤ K := (abs_nonneg _).trans hM3
  set μ := ∑ j ∈ J, l j with hμdef
  set ν := π1 + π3 + κ3 + κ2 with hνdef
  have hμ0 : 0 ≤ μ := sum_nonneg hl
  have hν0 : 0 ≤ ν := by positivity
  have hηκ : 0 < η * κ := mul_pos hη hκ
  -- (A) the mass on `J`
  have sA : η * κ * μ ≤ ∑ j ∈ J, l j * ζ j * M j := by
    rw [hμdef, mul_sum]
    refine sum_le_sum fun j hj => ?_
    have : η * κ ≤ ζ j * M j := mul_le_mul (hζ j hj) (hM j hj) hκ.le (hη.le.trans (hζ j hj))
    nlinarith [hl j hj]
  have hA : η * κ * μ ≤ δ * K * ν := by
    have e3 : -M3 ≤ K := (neg_le_abs M3).trans hM3
    have eb : -Mb ≤ K := (neg_le_abs Mb).trans hMb
    have p3 : δ * κ3 * (-M3) ≤ δ * κ3 * K := mul_le_mul_of_nonneg_left e3 (by positivity)
    have pb : δ * κ2 * (-Mb) ≤ δ * κ2 * K := mul_le_mul_of_nonneg_left eb (by positivity)
    have pν : δ * K * (κ3 + κ2) ≤ δ * K * ν :=
      mul_le_mul_of_nonneg_left (by rw [hνdef]; linarith) (by positivity)
    have e : ∑ j ∈ J, l j * ζ j * M j = δ * κ3 * (-M3) + δ * κ2 * (-Mb) := by linarith
    have e2 : δ * κ3 * K + δ * κ2 * K = δ * K * (κ3 + κ2) := by ring
    linarith only [sA, e, p3, pb, pν, e2]
  have hμ : μ ≤ δ * K * ν / (η * κ) := by rw [le_div_iff₀ hηκ]; linarith
  -- (B) E2 dotted with `p`
  have sB : -(L * δ * Z * μ) ≤ ∑ j ∈ J, l j * ζ j * P j := by
    rw [hμdef, mul_sum, ← sum_neg_distrib]
    refine sum_le_sum fun j hj => ?_
    have hz : 0 ≤ ζ j := hη.le.trans (hζ j hj)
    have h1 : l j * ζ j * (P j + L * δ) ≥ 0 := mul_nonneg (mul_nonneg (hl j hj) hz) (by linarith [hP j hj])
    have h2 : l j * (L * δ) * ζ j ≤ l j * (L * δ) * Z :=
      mul_le_mul_of_nonneg_left (hζZ j hj) (mul_nonneg (hl j hj) (mul_nonneg hL hδ.le))
    nlinarith
  have hB : κ3 * P3 + κ2 * Pb ≤ L * Z * μ := by
    have : δ * (κ3 * P3 + κ2 * Pb) ≤ δ * (L * Z * μ) := by
      have e : δ * (κ3 * P3 + κ2 * Pb) = -(∑ j ∈ J, l j * ζ j * P j) := by linarith
      rw [e]; linarith
    exact le_of_mul_le_mul_left this hδ
  -- (C) E1 dotted with `p`
  have sC : |∑ j ∈ J, l j * P j| ≤ K * μ := by
    rw [hμdef, mul_sum]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j hj => ?_)
    rw [abs_mul, abs_of_nonneg (hl j hj), mul_comm]
    exact mul_le_mul_of_nonneg_right (hPK j hj) (hl j hj)
  have hC : -(K * μ) - L * δ * ν ≤ (π3 + κ3) * P3 + κ2 * Pb := by
    have e1 := le_abs_self (∑ j ∈ J, l j * P j)
    have e2 : π1 * Pa ≤ π1 * (L * δ) := mul_le_mul_of_nonneg_left ((le_abs_self Pa).trans hPa) h1
    have e3 : π1 * (L * δ) ≤ ν * (L * δ) := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have e4 : ν * (L * δ) = L * δ * ν := by ring
    linarith only [E1p, e1, e2, e3, e4, sC]
  -- (D) `π3 = O(δ ν)`
  have hD : π3 * c3 ≤ (K + L * Z) * μ + L * δ * ν := by
    have : π3 * P3 ≤ π3 * (-c3) := mul_le_mul_of_nonneg_left hP3 h3
    nlinarith
  set Q := ((K + L * Z) * K / (η * κ) + L) / c3 with hQ
  have hπ3 : π3 ≤ δ * ν * Q := by
    have hKL : 0 ≤ K + L * Z := by positivity
    have e1 : (K + L * Z) * μ ≤ (K + L * Z) * (δ * K * ν / (η * κ)) :=
      mul_le_mul_of_nonneg_left hμ hKL
    have e2 : π3 ≤ ((K + L * Z) * μ + L * δ * ν) / c3 := by rw [le_div_iff₀ hc3]; linarith
    calc π3 ≤ ((K + L * Z) * (δ * K * ν / (η * κ)) + L * δ * ν) / c3 := by
          refine e2.trans ?_; gcongr
      _ = δ * ν * Q := by rw [hQ]; field_simp
  -- (E) Cramer on the far ends
  set r := K * μ + K * π3 with hr
  have hR : ∀ (U : ι → ℝ) (u3 : ℝ), (∀ j ∈ J, |U j| ≤ K) → |u3| ≤ K →
      |-(∑ j ∈ J, l j * U j) - π3 * u3| ≤ r := by
    intro U u3 hU hu3
    have s : |∑ j ∈ J, l j * U j| ≤ K * μ := by
      rw [hμdef, mul_sum]
      refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j hj => ?_)
      rw [abs_mul, abs_of_nonneg (hl j hj), mul_comm]
      exact mul_le_mul_of_nonneg_right (hU j hj) (hl j hj)
    have t : |π3 * u3| ≤ K * π3 := by
      rw [abs_mul, abs_of_nonneg h3, mul_comm]; exact mul_le_mul_of_nonneg_right hu3 h3
    calc _ ≤ |∑ j ∈ J, l j * U j| + |π3 * u3| := by
          rw [show -(∑ j ∈ J, l j * U j) - π3 * u3 = -(∑ j ∈ J, l j * U j) + -(π3 * u3) by ring]
          refine (abs_add_le _ _).trans ?_; rw [abs_neg, abs_neg]
      _ ≤ _ := add_le_add s t
  have r1 := hR X1 X13 hX1 hX13
  have r2 := hR X2 X23 hX2 hX23
  have r3 := hR T T3a hT hT3a
  have q1 : π1 * X1a + κ3 * X13 + κ2 * X1b = -(∑ j ∈ J, l j * X1 j) - π3 * X13 := by linarith
  have q2 : π1 * X2a + κ3 * X23 + κ2 * X2b = -(∑ j ∈ J, l j * X2 j) - π3 * X23 := by linarith
  have q3 : π1 * Ta + κ3 * T3b + κ2 * Tb = -(∑ j ∈ J, l j * T j) - π3 * T3a := by linarith
  have b1 := cramer3_bound q1 q2 q3 hX13 hX23 hT3b hX1b hX2b hTb r1 r2 r3 hc hdet
  have q1' : κ3 * X13 + π1 * X1a + κ2 * X1b = -(∑ j ∈ J, l j * X1 j) - π3 * X13 := by linarith
  have q2' : κ3 * X23 + π1 * X2a + κ2 * X2b = -(∑ j ∈ J, l j * X2 j) - π3 * X23 := by linarith
  have q3' : κ3 * T3b + π1 * Ta + κ2 * Tb = -(∑ j ∈ J, l j * T j) - π3 * T3a := by linarith
  have b2 := cramer3_bound q1' q2' q3' hX1a hX2a hTa hX1b hX2b hTb r1 r2 r3 hc (by
      refine hdet.trans (le_of_eq ?_)
      rw [← abs_neg]; congr 1; ring)
  have q1'' : κ2 * X1b + π1 * X1a + κ3 * X13 = -(∑ j ∈ J, l j * X1 j) - π3 * X13 := by linarith
  have q2'' : κ2 * X2b + π1 * X2a + κ3 * X23 = -(∑ j ∈ J, l j * X2 j) - π3 * X23 := by linarith
  have q3'' : κ2 * Tb + π1 * Ta + κ3 * T3b = -(∑ j ∈ J, l j * T j) - π3 * T3a := by linarith
  have b3 := cramer3_bound q1'' q2'' q3'' hX1a hX2a hTa hX13 hX23 hT3b r1 r2 r3 hc (by
      refine hdet.trans (le_of_eq ?_)
      congr 1; ring)
  rw [abs_of_nonneg h1] at b1; rw [abs_of_nonneg k3] at b2; rw [abs_of_nonneg k2] at b3
  -- (F) conclude
  set S := 18 * K ^ 3 * (K / (η * κ) + Q) / c + Q with hS
  have hνS : ν ≤ δ * ν * S := by
    have e : ν ≤ 18 * r * K ^ 2 / c + π3 := by
      have : π1 + κ3 + κ2 ≤ 18 * r * K ^ 2 / c := by
        have := add_le_add (add_le_add b1 b2) b3
        calc π1 + κ3 + κ2 ≤ _ := this
          _ = 18 * r * K ^ 2 / c := by ring
      linarith
    have hr' : r ≤ K * (δ * K * ν / (η * κ)) + K * (δ * ν * Q) := by
      rw [hr]; exact add_le_add (mul_le_mul_of_nonneg_left hμ hK) (mul_le_mul_of_nonneg_left hπ3 hK)
    calc ν ≤ 18 * r * K ^ 2 / c + π3 := e
      _ ≤ 18 * (K * (δ * K * ν / (η * κ)) + K * (δ * ν * Q)) * K ^ 2 / c + δ * ν * Q := by
          gcongr
      _ = δ * ν * S := by rw [hS]; field_simp
  have hν : ν = 0 := by
    have : ν * (1 - δ * S) ≤ 0 := by nlinarith
    have hpos : 0 < 1 - δ * S := by rw [hS, hQ]; linarith
    exact le_antisymm (nonpos_of_mul_nonpos_left (by linarith) hpos) hν0
  have hμ' : μ = 0 := le_antisymm (hμ.trans (by rw [hν]; simp)) hμ0
  refine ⟨fun j hj => (sum_eq_zero_iff_of_nonneg hl).mp hμ' j hj, ?_, ?_, ?_, ?_⟩ <;> linarith

end Minimality

end
