module

public import Minimality.TieRobust

@[expose] public section

/-!
# Lemma T at the tie, robust form, at a right angle: the scalar core

At a right angle of the far triangle at `a` the far system's determinant
(`hdet` of `tie_core`) vanishes at the untilted view, so Cramer's rule on the
far ends fails. The force argument (`FEWER-FACES-PROOFS.md`, "Addendum: right
angles") instead takes torques about `b`, which removes `κ3, κ2`:

* steps (A)-(D) of `tie_core` are unchanged: the mass `μ` on `J` and `π3`
  are `O(δ ν)`;
* every generator of `J` either is near `n2` (`c2 ≤ P j`; then E2·p and E1·p
  make its mass `O(δ² ν)`) or has torque about `b` at least `-L δ`; so the
  torque of `J` about `b` is at least `-O(δ² ν)`;
* the generator `Ga` at `a` (the last chain edge, rotated by `O(δ)`) has
  torque about `b` at least `c1 δ`, and `G3` at `a` a nonnegative one; so
  the torque equation about `b` gives `π1 = O(δ ν)`;
* E1 on the two remaining generators `G3`, `Gb` at `b` (independent) gives
  `κ3, κ2 = O(δ ν)`; hence `ν ≤ δ S ν`, and `ν = 0` once `δ S < 1`.
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

/-- Cramer's bound for two columns in `ℝ²`: with `|det| ≥ c` and right sides
bounded by `r`, entries by `K`, both unknowns are at most `2 r K / c`. -/
theorem cramer2_bound {a1 a2 b1 b2 x y r1 r2 K r c : ℝ}
    (e1 : x * a1 + y * b1 = r1) (e2 : x * a2 + y * b2 = r2)
    (ha1 : |a1| ≤ K) (ha2 : |a2| ≤ K) (hb1 : |b1| ≤ K) (hb2 : |b2| ≤ K)
    (hr1 : |r1| ≤ r) (hr2 : |r2| ≤ r) (hc : 0 < c) (hdet : c ≤ |a1 * b2 - a2 * b1|) :
    |x| ≤ 2 * r * K / c ∧ |y| ≤ 2 * r * K / c := by
  have hK : 0 ≤ K := (abs_nonneg _).trans ha1
  have hr : 0 ≤ r := (abs_nonneg _).trans hr1
  have kx : x * (a1 * b2 - a2 * b1) = r1 * b2 - r2 * b1 := by subst e1 e2; ring
  have ky : y * (a1 * b2 - a2 * b1) = a1 * r2 - a2 * r1 := by subst e1 e2; ring
  have bnd : ∀ u v s t : ℝ, |u| ≤ r → |v| ≤ r → |s| ≤ K → |t| ≤ K → |u * s - v * t| ≤ 2 * r * K := by
    intro u v s t hu hv hs ht
    calc |u * s - v * t| ≤ |u| * |s| + |v| * |t| := by
          rw [← abs_mul, ← abs_mul]; exact abs_sub _ _
      _ ≤ r * K + r * K := add_le_add (mul_le_mul hu hs (abs_nonneg _) hr)
          (mul_le_mul hv ht (abs_nonneg _) hr)
      _ = 2 * r * K := by ring
  have fin : ∀ z D : ℝ, z * (a1 * b2 - a2 * b1) = D → |D| ≤ 2 * r * K → |z| ≤ 2 * r * K / c := by
    intro z D hz hD
    rw [le_div_iff₀ hc]
    calc |z| * c ≤ |z| * |a1 * b2 - a2 * b1| := mul_le_mul_of_nonneg_left hdet (abs_nonneg _)
      _ = |D| := by rw [← abs_mul, hz]
      _ ≤ _ := hD
  refine ⟨fin x _ kx (bnd _ _ _ _ hr1 hr2 hb2 hb1), fin y _ ky ?_⟩
  have := bnd _ _ _ _ hr2 hr1 ha1 ha2
  rwa [show r2 * a1 - r1 * a2 = a1 * r2 - a2 * r1 by ring] at this

set_option maxHeartbeats 2000000 in
/-- **The scalar core at a right angle.** As `tie_core`, with the torques `T`,
`Ta`, `T3a` taken about `b` (so `κ3, κ2` drop out of E3), the far determinant
replaced by the `2 × 2` determinant of `G3, Gb`, and the generators of `J`
split into those near `n2` (`c2 ≤ P j`) and those with torque about `b` at
least `-L δ`. With `δ S < 1` all weights vanish. -/
theorem tie_core_right {ι : Type*} (J : Finset ι) (l ζ M P X1 X2 T : ι → ℝ)
    (π1 π3 κ3 κ2 δ : ℝ) (M3 Mb Pa P3 Pb X1a X13 X1b X2a X23 X2b Ta T3a : ℝ)
    (κ η Z K L c3 c c1 c2 : ℝ)
    (hl : ∀ j ∈ J, 0 ≤ l j) (h1 : 0 ≤ π1) (h3 : 0 ≤ π3) (k3 : 0 ≤ κ3) (k2 : 0 ≤ κ2)
    (hκ : 0 < κ) (hη : 0 < η) (hc3 : 0 < c3) (hc : 0 < c) (hc1 : 0 < c1) (hc2 : 0 < c2)
    (hδ : 0 < δ) (hL : 0 ≤ L) (hZ : 0 ≤ Z)
    (hM : ∀ j ∈ J, κ ≤ M j) (hζ : ∀ j ∈ J, η ≤ ζ j) (hζZ : ∀ j ∈ J, ζ j ≤ Z)
    (hP : ∀ j ∈ J, -(L * δ) ≤ P j) (hPK : ∀ j ∈ J, |P j| ≤ K)
    (hX1 : ∀ j ∈ J, |X1 j| ≤ K) (hX2 : ∀ j ∈ J, |X2 j| ≤ K) (hT : ∀ j ∈ J, |T j| ≤ K)
    (hsplit : ∀ j ∈ J, c2 ≤ P j ∨ -(L * δ) ≤ T j)
    (hM3 : |M3| ≤ K) (hMb : |Mb| ≤ K) (hPa : |Pa| ≤ L * δ) (hP3 : P3 ≤ -c3)
    (hX1a : |X1a| ≤ K) (hX2a : |X2a| ≤ K) (hX13 : |X13| ≤ K) (hX23 : |X23| ≤ K)
    (hX1b : |X1b| ≤ K) (hX2b : |X2b| ≤ K)
    (hTa : c1 * δ ≤ Ta) (hT3a : 0 ≤ T3a)
    (hdet : c ≤ |X13 * X2b - X23 * X1b|)
    (E1x : ∑ j ∈ J, l j * X1 j + π1 * X1a + (π3 + κ3) * X13 + κ2 * X1b = 0)
    (E1y : ∑ j ∈ J, l j * X2 j + π1 * X2a + (π3 + κ3) * X23 + κ2 * X2b = 0)
    (E1p : ∑ j ∈ J, l j * P j + π1 * Pa + (π3 + κ3) * P3 + κ2 * Pb = 0)
    (E2m : ∑ j ∈ J, l j * ζ j * M j + δ * (κ3 * M3 + κ2 * Mb) = 0)
    (E2p : ∑ j ∈ J, l j * ζ j * P j + δ * (κ3 * P3 + κ2 * Pb) = 0)
    (E3 : ∑ j ∈ J, l j * T j + π1 * Ta + π3 * T3a = 0)
    (hsmall : δ * ((1 + 4 * K ^ 2 / c) * (K / (η * κ) + ((K + L * Z) * K / (η * κ) + L) / c3 +
      ((L + K / (η * c2) * K + K / (η * c2) * L * Z) * (K / (η * κ)) + K / (η * c2) * L) / c1)) < 1) :
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
  set a := K / (η * κ) with ha
  have hμ : μ ≤ δ * ν * a := by
    rw [ha, show δ * ν * (K / (η * κ)) = δ * K * ν / (η * κ) by ring, le_div_iff₀ hηκ]
    linarith
  -- (B) E2 dotted with `p`
  have hζsum : ∑ j ∈ J, l j * ζ j ≤ Z * μ := by
    rw [hμdef, mul_sum]
    exact sum_le_sum fun j hj => by nlinarith [hl j hj, hζZ j hj]
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
  have hπ1Pa : π1 * Pa ≤ L * δ * ν := by
    have e2 : π1 * Pa ≤ π1 * (L * δ) := mul_le_mul_of_nonneg_left ((le_abs_self Pa).trans hPa) h1
    have e3 : π1 * (L * δ) ≤ ν * (L * δ) := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    linarith
  have hC : -(K * μ) - L * δ * ν ≤ (π3 + κ3) * P3 + κ2 * Pb := by
    have e1 := le_abs_self (∑ j ∈ J, l j * P j)
    linarith only [E1p, e1, hπ1Pa, sC]
  -- (D) `π3 = O(δ ν)`
  have hD : π3 * c3 ≤ (K + L * Z) * μ + L * δ * ν := by
    have : π3 * P3 ≤ π3 * (-c3) := mul_le_mul_of_nonneg_left hP3 h3
    nlinarith
  set Q := ((K + L * Z) * a + L) / c3 with hQ
  have hπ3 : π3 ≤ δ * ν * Q := by
    have hKL : 0 ≤ K + L * Z := by positivity
    have e1 : (K + L * Z) * μ ≤ (K + L * Z) * (δ * ν * a) := mul_le_mul_of_nonneg_left hμ hKL
    have e2 : π3 ≤ ((K + L * Z) * μ + L * δ * ν) / c3 := by rw [le_div_iff₀ hc3]; linarith
    calc π3 ≤ ((K + L * Z) * (δ * ν * a) + L * δ * ν) / c3 := by
          refine e2.trans ?_; gcongr
      _ = δ * ν * Q := by rw [hQ]; ring
  -- (E) the torque of `J` about `b`
  set W := K / (η * c2) with hW
  have hW0 : 0 ≤ W := by positivity
  have pt : ∀ j ∈ J, -(L * δ) * l j - W * (l j * ζ j * (P j + L * δ)) ≤ l j * T j := by
    intro j hj
    have hlj := hl j hj
    have hz : 0 ≤ ζ j := hη.le.trans (hζ j hj)
    have hq : 0 ≤ l j * ζ j * (P j + L * δ) :=
      mul_nonneg (mul_nonneg hlj hz) (by linarith [hP j hj])
    have hLl : 0 ≤ L * δ * l j := by positivity
    rcases hsplit j hj with h2 | h2
    · have hTj : -K ≤ T j := by have := neg_abs_le (T j); linarith [hT j hj]
      have hPL : c2 ≤ P j + L * δ := by have := mul_nonneg hL hδ.le; linarith
      have e1 : l j * (η * c2) ≤ l j * (ζ j * (P j + L * δ)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul (hζ j hj) hPL hc2.le hz) hlj
      have e2 : W * (l j * (η * c2)) = K * l j := by
        rw [hW]; field_simp
      have e3 : W * (l j * (η * c2)) ≤ W * (l j * ζ j * (P j + L * δ)) := by
        rw [show l j * ζ j * (P j + L * δ) = l j * (ζ j * (P j + L * δ)) by ring]
        exact mul_le_mul_of_nonneg_left e1 hW0
      have e4 : l j * (-K) ≤ l j * T j := mul_le_mul_of_nonneg_left hTj hlj
      nlinarith
    · have e4 : l j * (-(L * δ)) ≤ l j * T j := mul_le_mul_of_nonneg_left h2 hlj
      have : 0 ≤ W * (l j * ζ j * (P j + L * δ)) := mul_nonneg hW0 hq
      nlinarith
  have sT : -(L * δ) * μ - W * (∑ j ∈ J, l j * ζ j * P j + L * δ * ∑ j ∈ J, l j * ζ j) ≤
      ∑ j ∈ J, l j * T j := by
    have e : ∑ j ∈ J, (-(L * δ) * l j - W * (l j * ζ j * (P j + L * δ))) =
        -(L * δ) * μ - W * (∑ j ∈ J, l j * ζ j * P j + L * δ * ∑ j ∈ J, l j * ζ j) := by
      rw [sum_sub_distrib, ← mul_sum, ← mul_sum, hμdef]
      congr 2
      rw [mul_sum, ← sum_add_distrib]
      exact sum_congr rfl fun j _ => by ring
    rw [← e]; exact sum_le_sum pt
  -- E2·p with E1·p: `Σ l ζ P = δ (Σ l P + π1 Pa + π3 P3) ≤ δ (K μ + L δ ν)`
  have hζP : ∑ j ∈ J, l j * ζ j * P j ≤ δ * (K * μ + L * δ * ν) := by
    have e : ∑ j ∈ J, l j * ζ j * P j = δ * (∑ j ∈ J, l j * P j + π1 * Pa + π3 * P3) := by
      linear_combination E2p - δ * E1p
    have h3P : π3 * P3 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos h3 (by linarith)
    rw [e]
    exact mul_le_mul_of_nonneg_left (by linarith [le_abs_self (∑ j ∈ J, l j * P j)]) hδ.le
  -- (F) `π1 = O(δ ν)` from the torque about `b`
  set R := ((L + W * K + W * L * Z) * a + W * L) / c1 with hR
  have hπ1 : π1 ≤ δ * ν * R := by
    have t1 : π1 * (c1 * δ) ≤ π1 * Ta := mul_le_mul_of_nonneg_left hTa h1
    have t3 : 0 ≤ π3 * T3a := mul_nonneg h3 hT3a
    have hz : L * δ * ∑ j ∈ J, l j * ζ j ≤ L * δ * (Z * μ) :=
      mul_le_mul_of_nonneg_left hζsum (by positivity)
    have hw : W * (∑ j ∈ J, l j * ζ j * P j + L * δ * ∑ j ∈ J, l j * ζ j) ≤
        W * (δ * (K * μ + L * δ * ν) + L * δ * (Z * μ)) :=
      mul_le_mul_of_nonneg_left (by linarith) hW0
    have key : δ * (c1 * π1) ≤ δ * ((L + W * K + W * L * Z) * μ + W * L * δ * ν) := by
      have e1 : δ * ((L + W * K + W * L * Z) * μ + W * L * δ * ν) =
          L * δ * μ + W * (δ * (K * μ + L * δ * ν) + L * δ * (Z * μ)) := by ring
      have e2 : δ * (c1 * π1) = π1 * (c1 * δ) := by ring
      have e3 : π1 * Ta = -(∑ j ∈ J, l j * T j) - π3 * T3a := by linarith
      have e4 : -(L * δ) * μ = -(L * δ * μ) := by ring
      rw [e1, e2]; linarith
    have k2' := le_of_mul_le_mul_left key hδ
    have hm : (L + W * K + W * L * Z) * μ ≤ (L + W * K + W * L * Z) * (δ * ν * a) :=
      mul_le_mul_of_nonneg_left hμ (by positivity)
    have hcR : c1 * (δ * ν * R) = (L + W * K + W * L * Z) * (δ * ν * a) + W * L * δ * ν := by
      rw [hR]; field_simp
    exact le_of_mul_le_mul_left (by rw [hcR]; linarith) hc1
  -- (G) `κ3, κ2` by Cramer on `G3, Gb`
  set s := μ + π1 + π3 with hs
  have hR' : ∀ (U : ι → ℝ) (ua u3 : ℝ), (∀ j ∈ J, |U j| ≤ K) → |ua| ≤ K → |u3| ≤ K →
      |-(∑ j ∈ J, l j * U j) - π1 * ua - π3 * u3| ≤ K * s := by
    intro U ua u3 hU hua hu3
    have s1 : |∑ j ∈ J, l j * U j| ≤ K * μ := by
      rw [hμdef, mul_sum]
      refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j hj => ?_)
      rw [abs_mul, abs_of_nonneg (hl j hj), mul_comm]
      exact mul_le_mul_of_nonneg_right (hU j hj) (hl j hj)
    have s2 : |π1 * ua| ≤ K * π1 := by
      rw [abs_mul, abs_of_nonneg h1, mul_comm]; exact mul_le_mul_of_nonneg_right hua h1
    have s3 : |π3 * u3| ≤ K * π3 := by
      rw [abs_mul, abs_of_nonneg h3, mul_comm]; exact mul_le_mul_of_nonneg_right hu3 h3
    calc _ ≤ |∑ j ∈ J, l j * U j| + |π1 * ua| + |π3 * u3| := by
          rw [show -(∑ j ∈ J, l j * U j) - π1 * ua - π3 * u3 =
            -(∑ j ∈ J, l j * U j) + -(π1 * ua) + -(π3 * u3) by ring]
          refine (abs_add_le _ _).trans ?_
          rw [abs_neg]; gcongr
          refine (abs_add_le _ _).trans ?_; rw [abs_neg, abs_neg]
      _ ≤ K * μ + K * π1 + K * π3 := by gcongr
      _ = K * s := by rw [hs]; ring
  have q1 : κ3 * X13 + κ2 * X1b = -(∑ j ∈ J, l j * X1 j) - π1 * X1a - π3 * X13 := by linarith
  have q2 : κ3 * X23 + κ2 * X2b = -(∑ j ∈ J, l j * X2 j) - π1 * X2a - π3 * X23 := by linarith
  obtain ⟨b3, b2⟩ := cramer2_bound q1 q2 hX13 hX23 hX1b hX2b (hR' X1 X1a X13 hX1 hX1a hX13)
    (hR' X2 X2a X23 hX2 hX2a hX23) hc hdet
  rw [abs_of_nonneg k3] at b3; rw [abs_of_nonneg k2] at b2
  -- (H) conclude
  set S := (1 + 4 * K ^ 2 / c) * (a + Q + R) with hS
  have hνS : ν ≤ δ * ν * S := by
    have e : ν ≤ (1 + 4 * K ^ 2 / c) * s := by
      have : κ3 + κ2 ≤ 4 * K ^ 2 / c * s := by
        have := add_le_add b3 b2
        calc κ3 + κ2 ≤ _ := this
          _ = 4 * K ^ 2 / c * s := by ring
      have e' : (1 + 4 * K ^ 2 / c) * s = s + 4 * K ^ 2 / c * s := by ring
      linarith
    have hs' : s ≤ δ * ν * (a + Q + R) := by
      have e' : δ * ν * (a + Q + R) = δ * ν * a + δ * ν * Q + δ * ν * R := by ring
      linarith
    calc ν ≤ (1 + 4 * K ^ 2 / c) * s := e
      _ ≤ (1 + 4 * K ^ 2 / c) * (δ * ν * (a + Q + R)) :=
          mul_le_mul_of_nonneg_left hs' (by positivity)
      _ = δ * ν * S := by rw [hS]; ring
  have hν : ν = 0 := by
    have e : ν * (1 - δ * S) = ν - δ * ν * S := by ring
    have : ν * (1 - δ * S) ≤ 0 := by linarith
    have hpos : 0 < 1 - δ * S := by
      convert sub_pos.mpr hsmall using 2
      rw [hS, hQ, ha]; ring
    exact le_antisymm (nonpos_of_mul_nonpos_left (by linarith) hpos) hν0
  have hμ' : μ = 0 := le_antisymm (hμ.trans (by rw [hν]; simp)) hμ0
  refine ⟨fun j hj => (sum_eq_zero_iff_of_nonneg hl).mp hμ' j hj, ?_, ?_, ?_, ?_⟩ <;> linarith

theorem inner_cross_swap (b F w : ℝ³) : ⟪cross b F, w⟫ = ⟪F, cross w b⟫ := by
  simp only [cross, PiLp.inner_apply, Fin.sum_univ_three]; simp; ring

/-- The torque about `b` of the edge generator `(b - a) × w` placed at `a` is
`|(b - a) × w|² ≥ 0`. -/
theorem torque_edge_nonneg (a b w : ℝ³) : 0 ≤ ⟪cross (a - b) (cross (b - a) w), w⟫ := by
  have e : ⟪cross (a - b) (cross (b - a) w), w⟫ = ⟪cross (b - a) w, cross (b - a) w⟫ := by
    simp only [cross, PiLp.inner_apply, Fin.sum_univ_three]; simp; ring
  rw [e]; exact real_inner_self_nonneg

/-- E3 about `b`: the torques of a force system about any point balance. -/
theorem torque_about {V : Finset ℝ³} {w : ℝ³} {F : ℝ³ → ℝ³} (hF : IsForceSys V w F) (b : ℝ³) :
    ∑ y ∈ V, ⟪cross (y - b) (F y), w⟫ = 0 := by
  obtain ⟨-, -, hE1, -, hE3⟩ := hF
  have e : ∀ y, ⟪cross (y - b) (F y), w⟫ = ⟪cross y (F y), w⟫ - ⟪F y, cross w b⟫ := by
    intro y; rw [← inner_cross_swap]
    simp only [cross, PiLp.inner_apply, Fin.sum_univ_three]; simp; ring
  simp only [e, sum_sub_distrib, hE3, ← sum_inner, hE1, inner_zero_left, sub_zero]

set_option maxHeartbeats 8000000 in
/-- **The robust tie at one view, right angle.** As `tie_no_forces_at`, with
the scalar bounds of `tie_core_right`: torques about `b`, the generators of
`X` near `n2` (`c2 ≤ ⟪G j, p⟫`) or with torque about `b` at least `-L δ`,
`a`'s side generator with torque about `b` at least `c1 δ`, and the
generators at `b` independent. Then every force system at `w` vanishes. -/
theorem tie_no_forces_at_right (V X : Finset ℝ³) (w a b a0 b1 m p : ℝ³) (nb0 nb1 : ℝ³ → ℝ³)
    (hXV : X ⊆ V) (ha : a ∈ V) (hb : b ∈ V) (hab : a ≠ b) (haX : a ∉ X) (hbX : b ∉ X)
    (ha0 : a0 ∈ V) (hb1 : b1 ∈ V) (hnb0 : ∀ y ∈ X, nb0 y ∈ V) (hnb1 : ∀ y ∈ X, nb1 y ∈ V)
    (hconvX : ∀ y ∈ X, 0 < det3 (nb1 y - y) (nb0 y - y) w)
    (hconva : 0 < det3 (b - a) (a0 - a) w) (hconvb : 0 < det3 (b1 - b) (a - b) w)
    (hin : ∀ y ∈ V, y ∉ X → y ≠ a → y ≠ b → ∀ G : ℝ³, ⟪G, w⟫ = 0 →
      (∀ q ∈ V, ⟪G, q - y⟫ ≤ 0) → G = 0)
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) (κ η Z K L c3 c c1 c2 : ℝ)
    (hκ : 0 < κ) (hη : 0 < η) (hc3 : 0 < c3) (hc : 0 < c) (hc1 : 0 < c1) (hc2 : 0 < c2)
    (hL : 0 ≤ L) (hZ : 0 ≤ Z)
    (hδ : 0 < σ * ⟪b - a, w⟫)
    (hM : ∀ j ∈ X ×ˢ (univ : Finset Bool), κ ≤ ⟪tgen nb0 nb1 w j, m⟫)
    (hζ : ∀ y ∈ X, η ≤ σ * ⟪y - a, w⟫) (hζZ : ∀ y ∈ X, σ * ⟪y - a, w⟫ ≤ Z)
    (hP : ∀ j ∈ X ×ˢ (univ : Finset Bool), -(L * (σ * ⟪b - a, w⟫)) ≤ ⟪tgen nb0 nb1 w j, p⟫)
    (hPK : ∀ j ∈ X ×ˢ (univ : Finset Bool), |⟪tgen nb0 nb1 w j, p⟫| ≤ K)
    (hX1 : ∀ j ∈ X ×ˢ (univ : Finset Bool), |tgen nb0 nb1 w j 0| ≤ K)
    (hX2 : ∀ j ∈ X ×ˢ (univ : Finset Bool), |tgen nb0 nb1 w j 1| ≤ K)
    (hT : ∀ j ∈ X ×ˢ (univ : Finset Bool), |⟪cross (j.1 - b) (tgen nb0 nb1 w j), w⟫| ≤ K)
    (hsplit : ∀ j ∈ X ×ˢ (univ : Finset Bool), c2 ≤ ⟪tgen nb0 nb1 w j, p⟫ ∨
      -(L * (σ * ⟪b - a, w⟫)) ≤ ⟪cross (j.1 - b) (tgen nb0 nb1 w j), w⟫)
    (hM3 : |⟪cross (b - a) w, m⟫| ≤ K) (hMb : |⟪cross (b1 - b) w, m⟫| ≤ K)
    (hPa : |⟪cross w (a0 - a), p⟫| ≤ L * (σ * ⟪b - a, w⟫)) (hP3 : ⟪cross (b - a) w, p⟫ ≤ -c3)
    (hX13 : |cross (b - a) w 0| ≤ K) (hX23 : |cross (b - a) w 1| ≤ K)
    (hX1a : |cross w (a0 - a) 0| ≤ K) (hX2a : |cross w (a0 - a) 1| ≤ K)
    (hX1b : |cross (b1 - b) w 0| ≤ K) (hX2b : |cross (b1 - b) w 1| ≤ K)
    (hTa : c1 * (σ * ⟪b - a, w⟫) ≤ ⟪cross (a - b) (cross w (a0 - a)), w⟫)
    (hdet : c ≤ |cross (b - a) w 0 * cross (b1 - b) w 1 - cross (b - a) w 1 * cross (b1 - b) w 0|)
    (hsmall : σ * ⟪b - a, w⟫ * ((1 + 4 * K ^ 2 / c) * (K / (η * κ) +
      ((K + L * Z) * K / (η * κ) + L) / c3 + ((L + K / (η * c2) * K + K / (η * c2) * L * Z) *
        (K / (η * κ)) + K / (η * c2) * L) / c1)) < 1)
    (F : ℝ³ → ℝ³) (hF : IsForceSys V w F) : ∀ y ∈ V, F y = 0 := by
  classical
  have hE3b := torque_about hF b
  obtain ⟨hFw, hFn, hE1, hE2, -⟩ := hF
  set J := X ×ˢ (univ : Finset Bool) with hJ
  set G := tgen nb0 nb1 w
  have hzero : ∀ y ∈ V, y ∉ X → y ≠ a → y ≠ b → F y = 0 := by
    intro y hy hyX hya hyb
    exact hin y hy hyX hya hyb (F y) (hFw y hy) (hFn y hy)
  have hcone : ∀ y ∈ X, ∃ s t : ℝ, 0 ≤ s ∧ 0 ≤ t ∧ F y = s • G (y, false) + t • G (y, true) := by
    intro y hy
    obtain ⟨s, t, hs, ht, e⟩ := force_mem_cone (hconvX y hy) (hFw y (hXV hy))
      (hFn y (hXV hy) _ (hnb1 y hy)) (hFn y (hXV hy) _ (hnb0 y hy))
    exact ⟨s, t, hs, ht, by simp only [G, tgen, ite_false, ite_true]; exact e⟩
  choose! s t hs ht hst using hcone
  obtain ⟨π1, π3, h1, h3, hFa⟩ := force_mem_cone hconva (hFw a ha) (hFn a ha b hb) (hFn a ha a0 ha0)
  obtain ⟨κ3, κ2, k3, k2, hFb⟩ := force_mem_cone hconvb (hFw b hb) (hFn b hb b1 hb1) (hFn b hb a ha)
  rw [cross_neg_sub] at hFb
  set Ga := cross w (a0 - a); set G3 := cross (b - a) w; set Gb := cross (b1 - b) w
  set δ := σ * ⟪b - a, w⟫ with hδdef
  let l : ℝ³ × Bool → ℝ := fun j => if j.2 then t j.1 else s j.1
  have hFX : ∀ y ∈ X, F y = l (y, false) • G (y, false) + l (y, true) • G (y, true) := by
    intro y hy; simp only [l, ite_false, ite_true]; exact hst y hy
  have split : ∀ {M : Type} [AddCommMonoid M] (φ : ℝ³ → M), (∀ y, F y = 0 → φ y = 0) →
      ∑ y ∈ V, φ y = ∑ y ∈ X, φ y + φ a + φ b := fun φ hφ =>
    sum_split V X φ hXV ha hb hab haX hbX fun y hy h1 h2 h3 => hφ y (hzero y hy h1 h2 h3)
  have lin : ∀ x : ℝ³, ∑ y ∈ X, ⟪F y, x⟫ = ∑ j ∈ J, l j * ⟪G j, x⟫ := by
    intro x
    rw [hJ, sum_gen]
    refine sum_congr rfl fun y hy => ?_
    rw [hFX y hy, inner_add_left, real_inner_smul_left, real_inner_smul_left]
  have E1d : ∀ x : ℝ³, ∑ j ∈ J, l j * ⟪G j, x⟫ + π1 * ⟪Ga, x⟫ + (π3 + κ3) * ⟪G3, x⟫ +
      κ2 * ⟪Gb, x⟫ = 0 := by
    intro x
    have h := congrArg (fun z => ⟪z, x⟫) hE1
    simp only [sum_inner, inner_zero_left] at h
    rw [split (fun y => ⟪F y, x⟫) (fun y hy => by rw [hy, inner_zero_left]), lin, hFa, hFb] at h
    simp only [inner_add_left, real_inner_smul_left] at h
    linarith
  have E2r : ∑ y ∈ V, ⟪y - a, w⟫ • F y = 0 := by
    have : ∑ y ∈ V, ⟪y - a, w⟫ • F y = ∑ y ∈ V, ⟪y, w⟫ • F y - ⟪a, w⟫ • ∑ y ∈ V, F y := by
      rw [smul_sum, ← sum_sub_distrib]
      exact sum_congr rfl fun y _ => by rw [inner_sub_left, sub_smul]
    rw [this, hE2, hE1, smul_zero, sub_zero]
  have E2d0 : ∀ x : ℝ³, ∑ j ∈ J, l j * ⟪j.1 - a, w⟫ * ⟪G j, x⟫ + ⟪b - a, w⟫ * (κ3 * ⟪G3, x⟫ + κ2 * ⟪Gb, x⟫) = 0 := by
    intro x
    have h := congrArg (fun z => ⟪z, x⟫) E2r
    simp only [sum_inner, inner_zero_left, real_inner_smul_left] at h
    rw [split (fun y => ⟪y - a, w⟫ * ⟪F y, x⟫) (fun y hy => by rw [hy, inner_zero_left, mul_zero]),
      sub_self, inner_zero_left, zero_mul, add_zero, hFb] at h
    have hX : ∑ y ∈ X, ⟪y - a, w⟫ * ⟪F y, x⟫ = ∑ j ∈ J, l j * ⟪j.1 - a, w⟫ * ⟪G j, x⟫ := by
      rw [hJ, sum_gen]
      refine sum_congr rfl fun y hy => ?_
      rw [hFX y hy, inner_add_left, real_inner_smul_left, real_inner_smul_left]; ring
    rw [hX] at h
    simp only [inner_add_left, real_inner_smul_left] at h
    linarith
  have E2d : ∀ x : ℝ³, ∑ j ∈ J, l j * (σ * ⟪j.1 - a, w⟫) * ⟪G j, x⟫ + δ * (κ3 * ⟪G3, x⟫ + κ2 * ⟪Gb, x⟫) = 0 := by
    intro x
    have h := E2d0 x
    have e : ∑ j ∈ J, l j * (σ * ⟪j.1 - a, w⟫) * ⟪G j, x⟫ = σ * ∑ j ∈ J, l j * ⟪j.1 - a, w⟫ * ⟪G j, x⟫ := by
      rw [mul_sum]; exact sum_congr rfl fun j _ => by ring
    rw [e, hδdef]
    have : σ * (∑ j ∈ J, l j * ⟪j.1 - a, w⟫ * ⟪G j, x⟫ + ⟪b - a, w⟫ * (κ3 * ⟪G3, x⟫ + κ2 * ⟪Gb, x⟫)) = 0 := by rw [h, mul_zero]
    linarith
  have E3d : ∑ j ∈ J, l j * ⟪cross (j.1 - b) (G j), w⟫ + π1 * ⟪cross (a - b) Ga, w⟫ +
      π3 * ⟪cross (a - b) G3, w⟫ = 0 := by
    rw [split (fun y => ⟪cross (y - b) (F y), w⟫) (fun y hy => by
      rw [hy]; simp [cross, PiLp.inner_apply, Fin.sum_univ_three])] at hE3b
    have hX : ∑ y ∈ X, ⟪cross (y - b) (F y), w⟫ = ∑ j ∈ J, l j * ⟪cross (j.1 - b) (G j), w⟫ := by
      rw [hJ, sum_gen]
      refine sum_congr rfl fun y hy => ?_
      rw [hFX y hy, cross_add_smul_right, inner_add_left, real_inner_smul_left,
        real_inner_smul_left]
    have hb0 : ⟪cross (b - b) (F b), w⟫ = 0 := by
      rw [sub_self]; simp [cross, PiLp.inner_apply, Fin.sum_univ_three]
    rw [hX, hb0, hFa, cross_add_smul_right] at hE3b
    simp only [inner_add_left, real_inner_smul_left] at hE3b
    linarith
  have hl : ∀ j ∈ J, 0 ≤ l j := by
    intro j hj
    obtain ⟨hy, -⟩ := mem_product.mp hj
    simp only [l]; split_ifs
    exacts [ht j.1 hy, hs j.1 hy]
  have core := tie_core_right J l (fun j => σ * ⟪j.1 - a, w⟫) (fun j => ⟪G j, m⟫)
    (fun j => ⟪G j, p⟫) (fun j => G j 0) (fun j => G j 1) (fun j => ⟪cross (j.1 - b) (G j), w⟫)
    π1 π3 κ3 κ2 δ ⟪G3, m⟫ ⟪Gb, m⟫ ⟪Ga, p⟫ ⟪G3, p⟫ ⟪Gb, p⟫ (Ga 0) (G3 0) (Gb 0) (Ga 1) (G3 1)
    (Gb 1) ⟪cross (a - b) Ga, w⟫ ⟪cross (a - b) G3, w⟫ κ η Z K L c3 c c1 c2
    hl h1 h3 k3 k2 hκ hη hc3 hc hc1 hc2 hδ hL hZ hM
    (fun j hj => hζ j.1 (mem_product.mp hj).1) (fun j hj => hζZ j.1 (mem_product.mp hj).1)
    hP hPK hX1 hX2 hT hsplit hM3 hMb hPa hP3 hX1a hX2a hX13 hX23 hX1b hX2b hTa
    (torque_edge_nonneg a b w) hdet
    (by have := E1d (EuclideanSpace.single 0 1); simpa [inner_single0] using this)
    (by have := E1d (EuclideanSpace.single 1 1); simpa [inner_single1] using this)
    (E1d p) (E2d m) (E2d p) E3d hsmall
  obtain ⟨hl0, hπ1, hπ3, hκ3, hκ2⟩ := core
  intro y hy
  by_cases hyX : y ∈ X
  · rw [hFX y hyX, hl0 _ (mem_product.mpr ⟨hyX, mem_univ _⟩),
      hl0 _ (mem_product.mpr ⟨hyX, mem_univ _⟩), zero_smul, zero_smul, add_zero]
  by_cases hya : y = a
  · rw [hya, hFa, hπ1, hπ3, zero_smul, zero_smul, add_zero]
  by_cases hyb : y = b
  · rw [hyb, hFb, hκ3, hκ2, zero_smul, zero_smul, add_zero]
  exact hzero y hy hyX hya hyb

theorem inner_cross_sub_swap (b y G w : ℝ³) : ⟪cross (b - y) G, w⟫ = -⟪cross (y - b) G, w⟫ := by
  simp only [cross, PiLp.inner_apply, Fin.sum_univ_three]; simp; ring

/-- E3 about `b`, with the opposite orientation. -/
theorem torque_about' {V : Finset ℝ³} {w : ℝ³} {F : ℝ³ → ℝ³} (hF : IsForceSys V w F) (b : ℝ³) :
    ∑ y ∈ V, ⟪cross (b - y) (F y), w⟫ = 0 := by
  simp only [inner_cross_sub_swap b, sum_neg_distrib, torque_about hF b, neg_zero]

/-- At a right angle at `b` (`⟪a - b, b1 - b⟫ = 0`) the torque about `a`
(opposite orientation) of `b`'s side generator is `⟪b1 - b, w⟫ ⟪a - b, w⟫`. -/
theorem torque_side_right_b (a b b1 w : ℝ³) (h : ⟪a - b, b1 - b⟫ = 0) :
    ⟪cross (a - b) (cross (b1 - b) w), w⟫ = ⟪b1 - b, w⟫ * ⟪a - b, w⟫ := by
  have e : ⟪cross (a - b) (cross (b1 - b) w), w⟫ =
      ⟪b1 - b, w⟫ * ⟪a - b, w⟫ - ⟪a - b, b1 - b⟫ * ⟪w, w⟫ := by
    simp only [cross, PiLp.inner_apply, Fin.sum_univ_three]; simp; ring
  rw [e, h, zero_mul, sub_zero]

set_option maxHeartbeats 8000000 in
/-- **The robust tie at one view, right angle, mirrored** (the far end `b`
loses its edge force; `δ = σ ⟪a - b, w⟫`, reference `b`; torques about `a`
with the opposite orientation). Then every force system at `w` vanishes. -/
theorem tie_no_forces_at_right_neg (V X : Finset ℝ³) (w a b a0 b1 m p : ℝ³) (nb0 nb1 : ℝ³ → ℝ³)
    (hXV : X ⊆ V) (ha : a ∈ V) (hb : b ∈ V) (hab : a ≠ b) (haX : a ∉ X) (hbX : b ∉ X)
    (ha0 : a0 ∈ V) (hb1 : b1 ∈ V) (hnb0 : ∀ y ∈ X, nb0 y ∈ V) (hnb1 : ∀ y ∈ X, nb1 y ∈ V)
    (hconvX : ∀ y ∈ X, 0 < det3 (nb1 y - y) (nb0 y - y) w)
    (hconva : 0 < det3 (b - a) (a0 - a) w) (hconvb : 0 < det3 (b1 - b) (a - b) w)
    (hin : ∀ y ∈ V, y ∉ X → y ≠ a → y ≠ b → ∀ G : ℝ³, ⟪G, w⟫ = 0 →
      (∀ q ∈ V, ⟪G, q - y⟫ ≤ 0) → G = 0)
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) (κ η Z K L c3 c c1 c2 : ℝ)
    (hκ : 0 < κ) (hη : 0 < η) (hc3 : 0 < c3) (hc : 0 < c) (hc1 : 0 < c1) (hc2 : 0 < c2)
    (hL : 0 ≤ L) (hZ : 0 ≤ Z)
    (hδ : 0 < σ * ⟪a - b, w⟫)
    (hM : ∀ j ∈ X ×ˢ (univ : Finset Bool), κ ≤ ⟪tgen nb0 nb1 w j, m⟫)
    (hζ : ∀ y ∈ X, η ≤ σ * ⟪y - b, w⟫) (hζZ : ∀ y ∈ X, σ * ⟪y - b, w⟫ ≤ Z)
    (hP : ∀ j ∈ X ×ˢ (univ : Finset Bool), -(L * (σ * ⟪a - b, w⟫)) ≤ ⟪tgen nb0 nb1 w j, p⟫)
    (hPK : ∀ j ∈ X ×ˢ (univ : Finset Bool), |⟪tgen nb0 nb1 w j, p⟫| ≤ K)
    (hX1 : ∀ j ∈ X ×ˢ (univ : Finset Bool), |tgen nb0 nb1 w j 0| ≤ K)
    (hX2 : ∀ j ∈ X ×ˢ (univ : Finset Bool), |tgen nb0 nb1 w j 1| ≤ K)
    (hT : ∀ j ∈ X ×ˢ (univ : Finset Bool), |⟪cross (a - j.1) (tgen nb0 nb1 w j), w⟫| ≤ K)
    (hsplit : ∀ j ∈ X ×ˢ (univ : Finset Bool), c2 ≤ ⟪tgen nb0 nb1 w j, p⟫ ∨
      -(L * (σ * ⟪a - b, w⟫)) ≤ ⟪cross (a - j.1) (tgen nb0 nb1 w j), w⟫)
    (hM3 : |⟪cross (b - a) w, m⟫| ≤ K) (hMa : |⟪cross w (a0 - a), m⟫| ≤ K)
    (hPb : |⟪cross (b1 - b) w, p⟫| ≤ L * (σ * ⟪a - b, w⟫)) (hP3 : ⟪cross (b - a) w, p⟫ ≤ -c3)
    (hX13 : |cross (b - a) w 0| ≤ K) (hX23 : |cross (b - a) w 1| ≤ K)
    (hX1a : |cross w (a0 - a) 0| ≤ K) (hX2a : |cross w (a0 - a) 1| ≤ K)
    (hX1b : |cross (b1 - b) w 0| ≤ K) (hX2b : |cross (b1 - b) w 1| ≤ K)
    (hTb : c1 * (σ * ⟪a - b, w⟫) ≤ ⟪cross (a - b) (cross (b1 - b) w), w⟫)
    (hdet : c ≤ |cross (b - a) w 0 * cross w (a0 - a) 1 - cross (b - a) w 1 * cross w (a0 - a) 0|)
    (hsmall : σ * ⟪a - b, w⟫ * ((1 + 4 * K ^ 2 / c) * (K / (η * κ) +
      ((K + L * Z) * K / (η * κ) + L) / c3 + ((L + K / (η * c2) * K + K / (η * c2) * L * Z) *
        (K / (η * κ)) + K / (η * c2) * L) / c1)) < 1)
    (F : ℝ³ → ℝ³) (hF : IsForceSys V w F) : ∀ y ∈ V, F y = 0 := by
  classical
  have hE3a := torque_about' hF a
  obtain ⟨hFw, hFn, hE1, hE2, -⟩ := hF
  set J := X ×ˢ (univ : Finset Bool) with hJ
  set G := tgen nb0 nb1 w
  have hzero : ∀ y ∈ V, y ∉ X → y ≠ a → y ≠ b → F y = 0 := by
    intro y hy hyX hya hyb
    exact hin y hy hyX hya hyb (F y) (hFw y hy) (hFn y hy)
  have hcone : ∀ y ∈ X, ∃ s t : ℝ, 0 ≤ s ∧ 0 ≤ t ∧ F y = s • G (y, false) + t • G (y, true) := by
    intro y hy
    obtain ⟨s, t, hs, ht, e⟩ := force_mem_cone (hconvX y hy) (hFw y (hXV hy))
      (hFn y (hXV hy) _ (hnb1 y hy)) (hFn y (hXV hy) _ (hnb0 y hy))
    exact ⟨s, t, hs, ht, by simp only [G, tgen, ite_false, ite_true]; exact e⟩
  choose! s t hs ht hst using hcone
  obtain ⟨π1, π3, h1, h3, hFa⟩ := force_mem_cone hconva (hFw a ha) (hFn a ha b hb) (hFn a ha a0 ha0)
  obtain ⟨κ3, κ2, k3, k2, hFb⟩ := force_mem_cone hconvb (hFw b hb) (hFn b hb b1 hb1) (hFn b hb a ha)
  rw [cross_neg_sub] at hFb
  set Ga := cross w (a0 - a); set G3 := cross (b - a) w; set Gb := cross (b1 - b) w
  set δ := σ * ⟪a - b, w⟫ with hδdef
  let l : ℝ³ × Bool → ℝ := fun j => if j.2 then t j.1 else s j.1
  have hFX : ∀ y ∈ X, F y = l (y, false) • G (y, false) + l (y, true) • G (y, true) := by
    intro y hy; simp only [l, ite_false, ite_true]; exact hst y hy
  have split : ∀ {M : Type} [AddCommMonoid M] (φ : ℝ³ → M), (∀ y, F y = 0 → φ y = 0) →
      ∑ y ∈ V, φ y = ∑ y ∈ X, φ y + φ a + φ b := fun φ hφ =>
    sum_split V X φ hXV ha hb hab haX hbX fun y hy h1 h2 h3 => hφ y (hzero y hy h1 h2 h3)
  have lin : ∀ x : ℝ³, ∑ y ∈ X, ⟪F y, x⟫ = ∑ j ∈ J, l j * ⟪G j, x⟫ := by
    intro x
    rw [hJ, sum_gen]
    refine sum_congr rfl fun y hy => ?_
    rw [hFX y hy, inner_add_left, real_inner_smul_left, real_inner_smul_left]
  have E1d : ∀ x : ℝ³, ∑ j ∈ J, l j * ⟪G j, x⟫ + π1 * ⟪Ga, x⟫ + (π3 + κ3) * ⟪G3, x⟫ +
      κ2 * ⟪Gb, x⟫ = 0 := by
    intro x
    have h := congrArg (fun z => ⟪z, x⟫) hE1
    simp only [sum_inner, inner_zero_left] at h
    rw [split (fun y => ⟪F y, x⟫) (fun y hy => by rw [hy, inner_zero_left]), lin, hFa, hFb] at h
    simp only [inner_add_left, real_inner_smul_left] at h
    linarith
  have E2r : ∑ y ∈ V, ⟪y - b, w⟫ • F y = 0 := by
    have : ∑ y ∈ V, ⟪y - b, w⟫ • F y = ∑ y ∈ V, ⟪y, w⟫ • F y - ⟪b, w⟫ • ∑ y ∈ V, F y := by
      rw [smul_sum, ← sum_sub_distrib]
      exact sum_congr rfl fun y _ => by rw [inner_sub_left, sub_smul]
    rw [this, hE2, hE1, smul_zero, sub_zero]
  have E2d0 : ∀ x : ℝ³, ∑ j ∈ J, l j * ⟪j.1 - b, w⟫ * ⟪G j, x⟫ + ⟪a - b, w⟫ * (π3 * ⟪G3, x⟫ + π1 * ⟪Ga, x⟫) = 0 := by
    intro x
    have h := congrArg (fun z => ⟪z, x⟫) E2r
    simp only [sum_inner, inner_zero_left, real_inner_smul_left] at h
    rw [split (fun y => ⟪y - b, w⟫ * ⟪F y, x⟫) (fun y hy => by rw [hy, inner_zero_left, mul_zero]),
      sub_self, inner_zero_left, zero_mul, add_zero, hFa] at h
    have hX : ∑ y ∈ X, ⟪y - b, w⟫ * ⟪F y, x⟫ = ∑ j ∈ J, l j * ⟪j.1 - b, w⟫ * ⟪G j, x⟫ := by
      rw [hJ, sum_gen]
      refine sum_congr rfl fun y hy => ?_
      rw [hFX y hy, inner_add_left, real_inner_smul_left, real_inner_smul_left]; ring
    rw [hX] at h
    simp only [inner_add_left, real_inner_smul_left] at h
    linarith
  have E2d : ∀ x : ℝ³, ∑ j ∈ J, l j * (σ * ⟪j.1 - b, w⟫) * ⟪G j, x⟫ + δ * (π3 * ⟪G3, x⟫ + π1 * ⟪Ga, x⟫) = 0 := by
    intro x
    have h := E2d0 x
    have e : ∑ j ∈ J, l j * (σ * ⟪j.1 - b, w⟫) * ⟪G j, x⟫ = σ * ∑ j ∈ J, l j * ⟪j.1 - b, w⟫ * ⟪G j, x⟫ := by
      rw [mul_sum]; exact sum_congr rfl fun j _ => by ring
    rw [e, hδdef]
    have : σ * (∑ j ∈ J, l j * ⟪j.1 - b, w⟫ * ⟪G j, x⟫ + ⟪a - b, w⟫ * (π3 * ⟪G3, x⟫ + π1 * ⟪Ga, x⟫)) = 0 := by rw [h, mul_zero]
    linarith
  have E3d : ∑ j ∈ J, l j * ⟪cross (a - j.1) (G j), w⟫ + κ2 * ⟪cross (a - b) Gb, w⟫ +
      κ3 * ⟪cross (a - b) G3, w⟫ = 0 := by
    rw [split (fun y => ⟪cross (a - y) (F y), w⟫) (fun y hy => by
      rw [hy]; simp [cross, PiLp.inner_apply, Fin.sum_univ_three])] at hE3a
    have hX : ∑ y ∈ X, ⟪cross (a - y) (F y), w⟫ = ∑ j ∈ J, l j * ⟪cross (a - j.1) (G j), w⟫ := by
      rw [hJ, sum_gen]
      refine sum_congr rfl fun y hy => ?_
      rw [hFX y hy, cross_add_smul_right, inner_add_left, real_inner_smul_left,
        real_inner_smul_left]
    have ha0' : ⟪cross (a - a) (F a), w⟫ = 0 := by
      rw [sub_self]; simp [cross, PiLp.inner_apply, Fin.sum_univ_three]
    rw [hX, ha0', hFb, cross_add_smul_right] at hE3a
    simp only [inner_add_left, real_inner_smul_left] at hE3a
    linarith
  have hl : ∀ j ∈ J, 0 ≤ l j := by
    intro j hj
    obtain ⟨hy, -⟩ := mem_product.mp hj
    simp only [l]; split_ifs
    exacts [ht j.1 hy, hs j.1 hy]
  have core := tie_core_right J l (fun j => σ * ⟪j.1 - b, w⟫) (fun j => ⟪G j, m⟫)
    (fun j => ⟪G j, p⟫) (fun j => G j 0) (fun j => G j 1) (fun j => ⟪cross (a - j.1) (G j), w⟫)
    κ2 κ3 π3 π1 δ ⟪G3, m⟫ ⟪Ga, m⟫ ⟪Gb, p⟫ ⟪G3, p⟫ ⟪Ga, p⟫ (Gb 0) (G3 0) (Ga 0) (Gb 1) (G3 1)
    (Ga 1) ⟪cross (a - b) Gb, w⟫ ⟪cross (a - b) G3, w⟫ κ η Z K L c3 c c1 c2
    hl k2 k3 h3 h1 hκ hη hc3 hc hc1 hc2 hδ hL hZ hM
    (fun j hj => hζ j.1 (mem_product.mp hj).1) (fun j hj => hζZ j.1 (mem_product.mp hj).1)
    hP hPK hX1 hX2 hT hsplit hM3 hMa hPb hP3 hX1b hX2b hX13 hX23 hX1a hX2a hTb
    (torque_edge_nonneg a b w) hdet
    (by have := E1d (EuclideanSpace.single 0 1); simp only [inner_single0] at this; linarith)
    (by have := E1d (EuclideanSpace.single 1 1); simp only [inner_single1] at this; linarith)
    (by have := E1d p; linarith) (by have := E2d m; linarith) (by have := E2d p; linarith)
    E3d hsmall
  obtain ⟨hl0, hκ2, hκ3, hπ3, hπ1⟩ := core
  intro y hy
  by_cases hyX : y ∈ X
  · rw [hFX y hyX, hl0 _ (mem_product.mpr ⟨hyX, mem_univ _⟩),
      hl0 _ (mem_product.mpr ⟨hyX, mem_univ _⟩), zero_smul, zero_smul, add_zero]
  by_cases hya : y = a
  · rw [hya, hFa, hπ1, hπ3, zero_smul, zero_smul, add_zero]
  by_cases hyb : y = b
  · rw [hyb, hFb, hκ3, hκ2, zero_smul, zero_smul, add_zero]
  exact hzero y hy hyX hya hyb

/-- At a right angle at `a` (`⟪a - b, a0 - a⟫ = 0`) the torque about `b` of
`a`'s side generator is `⟪a0 - a, w⟫ ⟪b - a, w⟫`. -/
theorem torque_side_right (a b a0 w : ℝ³) (h : ⟪a - b, a0 - a⟫ = 0) :
    ⟪cross (a - b) (cross w (a0 - a)), w⟫ = ⟪a0 - a, w⟫ * ⟪b - a, w⟫ := by
  have e : ⟪cross (a - b) (cross w (a0 - a)), w⟫ =
      ⟪a - b, a0 - a⟫ * ⟪w, w⟫ - ⟪a0 - a, w⟫ * ⟪a - b, w⟫ := by
    simp only [cross, PiLp.inner_apply, Fin.sum_univ_three]; simp; ring
  rw [e, h, zero_mul, zero_sub, show a - b = -(b - a) by abel, inner_neg_left]
  ring

theorem continuous_tgen_torque_at (nb0 nb1 : ℝ³ → ℝ³) (v b : ℝ³) (j : ℝ³ × Bool) :
    Continuous fun ε : ℝ => ⟪cross (j.1 - b) (tgen nb0 nb1 (tw v ε) j), tw v ε⟫ := by
  unfold tgen; split_ifs <;> (simp only [cross, tw, PiLp.inner_apply, Fin.sum_univ_three]; fun_prop)

/-- Eventual bounds for the corner generators' torques about `b`. -/
theorem ev_gen_torque_bounds (J : Finset (ℝ³ × Bool)) (nb0 nb1 : ℝ³ → ℝ³) (v b : ℝ³) :
    ∃ K0 : ℝ, 0 ≤ K0 ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ j ∈ J,
      |⟪cross (j.1 - b) (tgen nb0 nb1 (tw v ε) j), tw v ε⟫| ≤ K0 := by
  classical
  refine ⟨∑ j ∈ J, (|⟪cross (j.1 - b) (tgen nb0 nb1 (tw v 0) j), tw v 0⟫| + 1),
    sum_nonneg fun _ _ => by positivity, ?_⟩
  refine (eventually_all_finset J).2 fun j hj =>
    (ev_abs_le (continuous_tgen_torque_at nb0 nb1 v b j)).mono fun ε h => h.trans ?_
  exact single_le_sum (f := fun j => |⟪cross (j.1 - b) (tgen nb0 nb1 (tw v 0) j), tw v 0⟫| + 1)
    (fun _ _ => by positivity) hj

theorem continuous_det2 (v a b b1 : ℝ³) :
    Continuous fun ε : ℝ => cross (b - a) (tw v ε) 0 * cross (b1 - b) (tw v ε) 1 -
      cross (b - a) (tw v ε) 1 * cross (b1 - b) (tw v ε) 0 := by
  simp only [cross, tw]; simp; fun_prop

set_option maxHeartbeats 16000000 in
/-- **Lemma T at the tie, robust form, forces, right angle at `a`.** As
`tie_no_forces`, with the far determinant replaced by: a right angle at `a`
(`⟪a - b, a0 - a⟫ = 0`), `a0` strictly on the corners' side of the tie,
every corner generator positive on `p` or with positive torque about `b` at
`ε = 0`, and the generators at `b` independent. Then for all small `ε > 0`
every force system vanishes. -/
theorem tie_no_forces_right (V X : Finset ℝ³) (v a b a0 b1 m p : ℝ³) (nb0 nb1 : ℝ³ → ℝ³)
    (hXV : X ⊆ V) (ha : a ∈ V) (hb : b ∈ V) (hab : a ≠ b) (haX : a ∉ X) (hbX : b ∉ X)
    (ha0 : a0 ∈ V) (hb1 : b1 ∈ V) (hnb0 : ∀ y ∈ X, nb0 y ∈ V) (hnb1 : ∀ y ∈ X, nb1 y ∈ V)
    (htie : a 2 = b 2) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) (hD : 0 < σ * ⟪b - a, v⟫)
    (hXz : ∀ y ∈ X, 0 < σ * (y 2 - a 2))
    (hconvX : ∀ y ∈ X, ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < det3 (nb1 y - y) (nb0 y - y) (tw v ε))
    (hconva : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < det3 (b - a) (a0 - a) (tw v ε))
    (hconvb : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < det3 (b1 - b) (a - b) (tw v ε))
    (hin : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y ∈ V, y ∉ X → y ≠ a → y ≠ b → ∀ G : ℝ³,
      ⟪G, tw v ε⟫ = 0 → (∀ q ∈ V, ⟪G, q - y⟫ ≤ 0) → G = 0)
    (hm : ∀ j ∈ X ×ˢ (univ : Finset Bool), 0 < ⟪tgen nb0 nb1 ez j, m⟫)
    (hp : ∀ j ∈ X ×ˢ (univ : Finset Bool), 0 ≤ ⟪tgen nb0 nb1 ez j, p⟫)
    (hpa : ⟪cross ez (a0 - a), p⟫ = 0) (hp3 : ⟪cross (b - a) ez, p⟫ < 0)
    (hright : ⟪a - b, a0 - a⟫ = 0) (ha0z : 0 < σ * (a0 2 - a 2))
    (hsplit : ∀ j ∈ X ×ˢ (univ : Finset Bool), 0 < ⟪tgen nb0 nb1 ez j, p⟫ ∨
      0 < ⟪cross (j.1 - b) (tgen nb0 nb1 ez j), ez⟫)
    (hdet : cross (b - a) ez 0 * cross (b1 - b) ez 1 - cross (b - a) ez 1 * cross (b1 - b) ez 0 ≠ 0) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ F : ℝ³ → ℝ³, IsForceSys V (tw v ε) F → ∀ y ∈ V, F y = 0 := by
  classical
  set J := X ×ˢ (univ : Finset Bool) with hJ
  set D := σ * ⟪b - a, v⟫ with hDdef
  have hσ2 : σ * σ = 1 := by rcases hσ with h | h <;> rw [h] <;> norm_num
  have hδε : ∀ ε, σ * ⟪b - a, tw v ε⟫ = ε * D := fun ε => by
    rw [inner_tw, PiLp.sub_apply, htie, sub_self, zero_add, hDdef]; ring
  have hζε : ∀ y ε, σ * ⟪y - a, tw v ε⟫ = σ * (y 2 - a 2) + ε * (σ * ⟪y - a, v⟫) :=
    fun y ε => by rw [inner_tw, PiLp.sub_apply]; ring
  have hgenε : ∀ (j : ℝ³ × Bool) (x : ℝ³) (ε : ℝ), ⟪tgen nb0 nb1 (tw v ε) j, x⟫ =
      ⟪tgen nb0 nb1 ez j, x⟫ + ε * ⟪tgen' nb0 nb1 v j, x⟫ := fun j x ε => by
    rw [tgen_tw, inner_add_left, real_inner_smul_left]
  -- constants
  obtain ⟨κ, hκ, hκle⟩ := exists_pos_lower J (fun j => ⟪tgen nb0 nb1 ez j, m⟫ / 2)
    (fun j hj => by have := hm j hj; positivity)
  obtain ⟨η, hη, hηle⟩ := exists_pos_lower X (fun y => σ * (y 2 - a 2) / 2)
    (fun y hy => by have := hXz y hy; linarith)
  obtain ⟨c2, hc2, hc2le⟩ := exists_pos_lower J
    (fun j => if 0 < ⟪tgen nb0 nb1 ez j, p⟫ then ⟪tgen nb0 nb1 ez j, p⟫ / 2 else 1)
    (fun j _ => by split_ifs with h <;> [positivity; norm_num])
  set Z := ∑ y ∈ X, (|σ * (y 2 - a 2)| + |σ * ⟪y - a, v⟫|) with hZdef
  have hZ : 0 ≤ Z := sum_nonneg fun _ _ => by positivity
  obtain ⟨K1, hK1, evJ⟩ := ev_gen_bounds J nb0 nb1 v p
  obtain ⟨K2, hK2, evFar⟩ := ev_far_bounds v a b a0 b1 m
  obtain ⟨K3, hK3, evT⟩ := ev_gen_torque_bounds J nb0 nb1 v b
  set K := K1 + K2 + K3 with hKdef
  set sp := ∑ j ∈ J, |⟪tgen' nb0 nb1 v j, p⟫| + |⟪cross v (a0 - a), p⟫| with hsp
  have hsp0 : 0 ≤ sp := by positivity
  set L := sp / D with hLdef
  have hL : 0 ≤ L := div_nonneg hsp0 hD.le
  have hLδ : ∀ ε, L * (ε * D) = ε * sp := fun ε => by rw [hLdef]; field_simp
  set c3 := -⟪cross (b - a) ez, p⟫ / 2 with hc3def
  have hc3 : 0 < c3 := by rw [hc3def]; linarith
  set det0 := cross (b - a) ez 0 * cross (b1 - b) ez 1 - cross (b - a) ez 1 * cross (b1 - b) ez 0
  set c := |det0| / 2 with hcdef
  have hc : 0 < c := by rw [hcdef]; have := abs_pos.mpr hdet; linarith
  set c1 := σ * (a0 2 - a 2) / 2 with hc1def
  have hc1 : 0 < c1 := by rw [hc1def]; linarith
  set S := (1 + 4 * K ^ 2 / c) * (K / (η * κ) + ((K + L * Z) * K / (η * κ) + L) / c3 +
    ((L + K / (η * c2) * K + K / (η * c2) * L * Z) * (K / (η * κ)) + K / (η * c2) * L) / c1)
  -- eventual facts
  have evM : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ j ∈ J, κ ≤ ⟪tgen nb0 nb1 (tw v ε) j, m⟫ :=
    (eventually_all_finset J).2 fun j hj =>
      (ev_half (B := ⟪tgen' nb0 nb1 v j, m⟫) (hm j hj)).mono fun ε h => by
        rw [hgenε]; exact (hκle j hj).trans h
  have evζ : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y ∈ X, η ≤ σ * ⟪y - a, tw v ε⟫ ∧
      σ * ⟪y - a, tw v ε⟫ ≤ Z :=
    (eventually_all_finset X).2 fun y hy =>
      ((ev_half (B := σ * ⟪y - a, v⟫) (hXz y hy)).and
        (ev_abs_quad (σ * (y 2 - a 2)) (σ * ⟪y - a, v⟫) 0)).mono fun ε ⟨h1, h2⟩ => by
        rw [hζε]
        refine ⟨(hηle y hy).trans h1, ?_⟩
        have hsum : |σ * (y 2 - a 2)| + |σ * ⟪y - a, v⟫| ≤ Z :=
          single_le_sum (f := fun y => |σ * (y 2 - a 2)| + |σ * ⟪y - a, v⟫|)
            (fun _ _ => by positivity) hy
        simp only [mul_zero, add_zero, abs_zero] at h2
        exact (le_abs_self _).trans (h2.trans hsum)
  have evP3 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ⟪cross (b - a) (tw v ε), p⟫ ≤ -c3 :=
    (ev_half (B := -⟪cross (b - a) v, p⟫) (show 0 < -⟪cross (b - a) ez, p⟫ by linarith)).mono
      fun ε h => by
        rw [inner_gen_right]; rw [hc3def]; linarith
  have evDet : ∀ᶠ ε in 𝓝[>] (0 : ℝ), c ≤ |cross (b - a) (tw v ε) 0 * cross (b1 - b) (tw v ε) 1 -
      cross (b - a) (tw v ε) 1 * cross (b1 - b) (tw v ε) 0| := by
    have hcont := (continuous_det2 v a b b1).abs.continuousAt (x := 0)
    have : ∀ᶠ ε in 𝓝 (0 : ℝ), c < |cross (b - a) (tw v ε) 0 * cross (b1 - b) (tw v ε) 1 -
        cross (b - a) (tw v ε) 1 * cross (b1 - b) (tw v ε) 0| := by
      refine hcont.eventually (lt_mem_nhds ?_)
      have e : tw v 0 = ez := by simp [tw]
      simp only [e]; rw [hcdef]; have := abs_pos.mpr hdet; linarith
    exact (this.filter_mono nhdsWithin_le_nhds).mono fun _ h => h.le
  have evTa : ∀ᶠ ε in 𝓝[>] (0 : ℝ), c1 * (ε * D) ≤
      ⟪cross (a - b) (cross (tw v ε) (a0 - a)), tw v ε⟫ :=
    ((ev_half (B := σ * ⟪a0 - a, v⟫) ha0z).and ev_le_one).mono fun ε hh => by
      obtain ⟨h, hε, -⟩ := hh
      rw [torque_side_right a b a0 _ hright]
      have e1 : ⟪a0 - a, tw v ε⟫ * ⟪b - a, tw v ε⟫ =
          (σ * ⟪a0 - a, tw v ε⟫) * (σ * ⟪b - a, tw v ε⟫) := by
        rw [show (σ * ⟪a0 - a, tw v ε⟫) * (σ * ⟪b - a, tw v ε⟫) =
          (σ * σ) * (⟪a0 - a, tw v ε⟫ * ⟪b - a, tw v ε⟫) by ring, hσ2, one_mul]
      have e2 : σ * ⟪a0 - a, tw v ε⟫ = σ * (a0 2 - a 2) + ε * (σ * ⟪a0 - a, v⟫) := hζε a0 ε
      rw [e1, e2, hδε, hc1def]
      have hεD : 0 ≤ ε * D := mul_nonneg hε.le hD.le
      nlinarith
  have evSplit : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ j ∈ J, c2 ≤ ⟪tgen nb0 nb1 (tw v ε) j, p⟫ ∨
      0 < ⟪cross (j.1 - b) (tgen nb0 nb1 (tw v ε) j), tw v ε⟫ := by
    refine (eventually_all_finset J).2 fun j hj => ?_
    by_cases h0 : 0 < ⟪tgen nb0 nb1 ez j, p⟫
    · refine (ev_half (B := ⟪tgen' nb0 nb1 v j, p⟫) h0).mono fun ε h => Or.inl ?_
      have := hc2le j hj; simp only [h0, if_true] at this
      rw [hgenε]; linarith
    · have hT0 := (hsplit j hj).resolve_left h0
      have hcont := (continuous_tgen_torque_at nb0 nb1 v b j).continuousAt (x := 0)
      have : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < ⟪cross (j.1 - b) (tgen nb0 nb1 (tw v ε) j), tw v ε⟫ := by
        refine hcont.eventually (lt_mem_nhds ?_)
        have e : tw v 0 = ez := by simp [tw]
        simp only [e]; exact hT0
      exact (this.filter_mono nhdsWithin_le_nhds).mono fun _ h => Or.inr h
  filter_upwards [ev_le_one, (eventually_all_finset X).2 hconvX, hconva, hconvb, hin, evM, evζ,
    evJ, evFar, evT, evP3, evDet, evTa, evSplit, ev_small (k := D * S)] with ε hε01 hcX hca hcb
    hIn hMε hζε' hJε hfar hTε hP3ε hdetε hTaε hsplitε hsmallε
  obtain ⟨hε0, -⟩ := hε01
  obtain ⟨f1, f2, f3, f4, -, f6, f7, -, -, f10, f11, -, -⟩ := hfar
  have wK2 : ∀ {x : ℝ}, x ≤ K2 → x ≤ K := fun h => by rw [hKdef]; linarith
  have wK1 : ∀ {x : ℝ}, x ≤ K1 → x ≤ K := fun h => by rw [hKdef]; linarith
  have wK3 : ∀ {x : ℝ}, x ≤ K3 → x ≤ K := fun h => by rw [hKdef]; linarith
  have hδpos : 0 < σ * ⟪b - a, tw v ε⟫ := by rw [hδε]; positivity
  intro F hF
  refine tie_no_forces_at_right V X (tw v ε) a b a0 b1 m p nb0 nb1 hXV ha hb hab haX hbX ha0 hb1
    hnb0 hnb1 hcX hca hcb hIn σ hσ κ η Z K L c3 c c1 c2 hκ hη hc3 hc hc1 hc2 hL hZ hδpos hMε
    (fun y hy => (hζε' y hy).1) (fun y hy => (hζε' y hy).2) ?_ (fun j hj => wK1 (hJε j hj).1)
    (fun j hj => wK1 (hJε j hj).2.1) (fun j hj => wK1 (hJε j hj).2.2.1)
    (fun j hj => wK3 (hTε j hj)) ?_
    (wK2 f1) (wK2 f2) ?_ hP3ε (wK2 f3) (wK2 f4) (wK2 f6) (wK2 f7) (wK2 f10) (wK2 f11)
    (by rw [hδε]; exact hTaε) hdetε ?_ F hF
  · intro j hj
    rw [hgenε, hδε, hLδ]
    have h1 : -|⟪tgen' nb0 nb1 v j, p⟫| ≤ ⟪tgen' nb0 nb1 v j, p⟫ := neg_abs_le _
    have h2 : |⟪tgen' nb0 nb1 v j, p⟫| ≤ sp := by
      have := single_le_sum (f := fun j => |⟪tgen' nb0 nb1 v j, p⟫|) (fun _ _ => abs_nonneg _) hj
      rw [hsp]; have := abs_nonneg ⟪cross v (a0 - a), p⟫; linarith
    have h0 := hp j hj
    have h3 : ε * (-|⟪tgen' nb0 nb1 v j, p⟫|) ≤ ε * ⟪tgen' nb0 nb1 v j, p⟫ :=
      mul_le_mul_of_nonneg_left h1 hε0.le
    have h4 : ε * |⟪tgen' nb0 nb1 v j, p⟫| ≤ ε * sp := mul_le_mul_of_nonneg_left h2 hε0.le
    nlinarith
  · intro j hj
    rcases hsplitε j hj with h | h
    · exact Or.inl h
    · refine Or.inr (le_trans ?_ h.le)
      have : 0 ≤ L * (σ * ⟪b - a, tw v ε⟫) := mul_nonneg hL hδpos.le
      linarith
  · rw [inner_gen_left, hpa, zero_add, hδε, hLδ, abs_mul, abs_of_pos hε0]
    have : |⟪cross v (a0 - a), p⟫| ≤ sp := by
      rw [hsp]; have := sum_nonneg fun j (_ : j ∈ J) => abs_nonneg ⟪tgen' nb0 nb1 v j, p⟫; linarith
    exact mul_le_mul_of_nonneg_left this hε0.le
  · rw [hδε]; nlinarith

theorem continuous_det2' (v a b a0 : ℝ³) :
    Continuous fun ε : ℝ => cross (b - a) (tw v ε) 0 * cross (tw v ε) (a0 - a) 1 -
      cross (b - a) (tw v ε) 1 * cross (tw v ε) (a0 - a) 0 := by
  simp only [cross, tw]; simp; fun_prop

set_option maxHeartbeats 16000000 in
/-- **Lemma T at the tie, robust form, forces, right angle at `b`** (mirrored:
`⟪a - b, v⟫ > 0`, the far end `b` loses its edge force). As
`tie_no_forces_neg`, with the far determinant replaced by: a right angle at
`b` (`⟪a - b, b1 - b⟫ = 0`), `b1` strictly on the corners' side of the tie,
every corner generator positive on `p` or with positive torque about `a`
(opposite orientation) at `ε = 0`, and the generators at `a` independent. Then for all small `ε > 0`
every force system vanishes. -/
theorem tie_no_forces_right_neg (V X : Finset ℝ³) (v a b a0 b1 m p : ℝ³) (nb0 nb1 : ℝ³ → ℝ³)
    (hXV : X ⊆ V) (ha : a ∈ V) (hb : b ∈ V) (hab : a ≠ b) (haX : a ∉ X) (hbX : b ∉ X)
    (ha0 : a0 ∈ V) (hb1 : b1 ∈ V) (hnb0 : ∀ y ∈ X, nb0 y ∈ V) (hnb1 : ∀ y ∈ X, nb1 y ∈ V)
    (htie : a 2 = b 2) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) (hD : 0 < σ * ⟪a - b, v⟫)
    (hXz : ∀ y ∈ X, 0 < σ * (y 2 - b 2))
    (hconvX : ∀ y ∈ X, ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < det3 (nb1 y - y) (nb0 y - y) (tw v ε))
    (hconva : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < det3 (b - a) (a0 - a) (tw v ε))
    (hconvb : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < det3 (b1 - b) (a - b) (tw v ε))
    (hin : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y ∈ V, y ∉ X → y ≠ a → y ≠ b → ∀ G : ℝ³,
      ⟪G, tw v ε⟫ = 0 → (∀ q ∈ V, ⟪G, q - y⟫ ≤ 0) → G = 0)
    (hm : ∀ j ∈ X ×ˢ (univ : Finset Bool), 0 < ⟪tgen nb0 nb1 ez j, m⟫)
    (hp : ∀ j ∈ X ×ˢ (univ : Finset Bool), 0 ≤ ⟪tgen nb0 nb1 ez j, p⟫)
    (hpb : ⟪cross (b1 - b) ez, p⟫ = 0) (hp3 : ⟪cross (b - a) ez, p⟫ < 0)
    (hright : ⟪a - b, b1 - b⟫ = 0) (hb1z : 0 < σ * (b1 2 - b 2))
    (hsplit : ∀ j ∈ X ×ˢ (univ : Finset Bool), 0 < ⟪tgen nb0 nb1 ez j, p⟫ ∨
      0 < ⟪cross (a - j.1) (tgen nb0 nb1 ez j), ez⟫)
    (hdet : cross (b - a) ez 0 * cross ez (a0 - a) 1 - cross (b - a) ez 1 * cross ez (a0 - a) 0 ≠ 0) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ F : ℝ³ → ℝ³, IsForceSys V (tw v ε) F → ∀ y ∈ V, F y = 0 := by
  classical
  set J := X ×ˢ (univ : Finset Bool) with hJ
  set D := σ * ⟪a - b, v⟫ with hDdef
  have hσ2 : σ * σ = 1 := by rcases hσ with h | h <;> rw [h] <;> norm_num
  have hδε : ∀ ε, σ * ⟪a - b, tw v ε⟫ = ε * D := fun ε => by
    rw [inner_tw, PiLp.sub_apply, htie, sub_self, zero_add, hDdef]; ring
  have hζε : ∀ y ε, σ * ⟪y - b, tw v ε⟫ = σ * (y 2 - b 2) + ε * (σ * ⟪y - b, v⟫) :=
    fun y ε => by rw [inner_tw, PiLp.sub_apply]; ring
  have hgenε : ∀ (j : ℝ³ × Bool) (x : ℝ³) (ε : ℝ), ⟪tgen nb0 nb1 (tw v ε) j, x⟫ =
      ⟪tgen nb0 nb1 ez j, x⟫ + ε * ⟪tgen' nb0 nb1 v j, x⟫ := fun j x ε => by
    rw [tgen_tw, inner_add_left, real_inner_smul_left]
  -- constants
  obtain ⟨κ, hκ, hκle⟩ := exists_pos_lower J (fun j => ⟪tgen nb0 nb1 ez j, m⟫ / 2)
    (fun j hj => by have := hm j hj; positivity)
  obtain ⟨η, hη, hηle⟩ := exists_pos_lower X (fun y => σ * (y 2 - b 2) / 2)
    (fun y hy => by have := hXz y hy; linarith)
  obtain ⟨c2, hc2, hc2le⟩ := exists_pos_lower J
    (fun j => if 0 < ⟪tgen nb0 nb1 ez j, p⟫ then ⟪tgen nb0 nb1 ez j, p⟫ / 2 else 1)
    (fun j _ => by split_ifs with h <;> [positivity; norm_num])
  set Z := ∑ y ∈ X, (|σ * (y 2 - b 2)| + |σ * ⟪y - b, v⟫|) with hZdef
  have hZ : 0 ≤ Z := sum_nonneg fun _ _ => by positivity
  obtain ⟨K1, hK1, evJ⟩ := ev_gen_bounds J nb0 nb1 v p
  obtain ⟨K2, hK2, evFar⟩ := ev_far_bounds v a b a0 b1 m
  obtain ⟨K3, hK3, evT⟩ := ev_gen_torque_bounds J nb0 nb1 v a
  set K := K1 + K2 + K3 with hKdef
  set sp := ∑ j ∈ J, |⟪tgen' nb0 nb1 v j, p⟫| + |⟪cross (b1 - b) v, p⟫| with hsp
  have hsp0 : 0 ≤ sp := by positivity
  set L := sp / D with hLdef
  have hL : 0 ≤ L := div_nonneg hsp0 hD.le
  have hLδ : ∀ ε, L * (ε * D) = ε * sp := fun ε => by rw [hLdef]; field_simp
  set c3 := -⟪cross (b - a) ez, p⟫ / 2 with hc3def
  have hc3 : 0 < c3 := by rw [hc3def]; linarith
  set det0 := cross (b - a) ez 0 * cross ez (a0 - a) 1 - cross (b - a) ez 1 * cross ez (a0 - a) 0
  set c := |det0| / 2 with hcdef
  have hc : 0 < c := by rw [hcdef]; have := abs_pos.mpr hdet; linarith
  set c1 := σ * (b1 2 - b 2) / 2 with hc1def
  have hc1 : 0 < c1 := by rw [hc1def]; linarith
  set S := (1 + 4 * K ^ 2 / c) * (K / (η * κ) + ((K + L * Z) * K / (η * κ) + L) / c3 +
    ((L + K / (η * c2) * K + K / (η * c2) * L * Z) * (K / (η * κ)) + K / (η * c2) * L) / c1)
  -- eventual facts
  have evM : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ j ∈ J, κ ≤ ⟪tgen nb0 nb1 (tw v ε) j, m⟫ :=
    (eventually_all_finset J).2 fun j hj =>
      (ev_half (B := ⟪tgen' nb0 nb1 v j, m⟫) (hm j hj)).mono fun ε h => by
        rw [hgenε]; exact (hκle j hj).trans h
  have evζ : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y ∈ X, η ≤ σ * ⟪y - b, tw v ε⟫ ∧
      σ * ⟪y - b, tw v ε⟫ ≤ Z :=
    (eventually_all_finset X).2 fun y hy =>
      ((ev_half (B := σ * ⟪y - b, v⟫) (hXz y hy)).and
        (ev_abs_quad (σ * (y 2 - b 2)) (σ * ⟪y - b, v⟫) 0)).mono fun ε ⟨h1, h2⟩ => by
        rw [hζε]
        refine ⟨(hηle y hy).trans h1, ?_⟩
        have hsum : |σ * (y 2 - b 2)| + |σ * ⟪y - b, v⟫| ≤ Z :=
          single_le_sum (f := fun y => |σ * (y 2 - b 2)| + |σ * ⟪y - b, v⟫|)
            (fun _ _ => by positivity) hy
        simp only [mul_zero, add_zero, abs_zero] at h2
        exact (le_abs_self _).trans (h2.trans hsum)
  have evP3 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ⟪cross (b - a) (tw v ε), p⟫ ≤ -c3 :=
    (ev_half (B := -⟪cross (b - a) v, p⟫) (show 0 < -⟪cross (b - a) ez, p⟫ by linarith)).mono
      fun ε h => by
        rw [inner_gen_right]; rw [hc3def]; linarith
  have evDet : ∀ᶠ ε in 𝓝[>] (0 : ℝ), c ≤ |cross (b - a) (tw v ε) 0 * cross (tw v ε) (a0 - a) 1 -
      cross (b - a) (tw v ε) 1 * cross (tw v ε) (a0 - a) 0| := by
    have hcont := (continuous_det2' v a b a0).abs.continuousAt (x := 0)
    have : ∀ᶠ ε in 𝓝 (0 : ℝ), c < |cross (b - a) (tw v ε) 0 * cross (tw v ε) (a0 - a) 1 -
        cross (b - a) (tw v ε) 1 * cross (tw v ε) (a0 - a) 0| := by
      refine hcont.eventually (lt_mem_nhds ?_)
      have e : tw v 0 = ez := by simp [tw]
      simp only [e]; rw [hcdef]; have := abs_pos.mpr hdet; linarith
    exact (this.filter_mono nhdsWithin_le_nhds).mono fun _ h => h.le
  have evTa : ∀ᶠ ε in 𝓝[>] (0 : ℝ), c1 * (ε * D) ≤
      ⟪cross (a - b) (cross (b1 - b) (tw v ε)), tw v ε⟫ :=
    ((ev_half (B := σ * ⟪b1 - b, v⟫) hb1z).and ev_le_one).mono fun ε hh => by
      obtain ⟨h, hε, -⟩ := hh
      rw [torque_side_right_b a b b1 _ hright]
      have e1 : ⟪b1 - b, tw v ε⟫ * ⟪a - b, tw v ε⟫ =
          (σ * ⟪b1 - b, tw v ε⟫) * (σ * ⟪a - b, tw v ε⟫) := by
        rw [show (σ * ⟪b1 - b, tw v ε⟫) * (σ * ⟪a - b, tw v ε⟫) =
          (σ * σ) * (⟪b1 - b, tw v ε⟫ * ⟪a - b, tw v ε⟫) by ring, hσ2, one_mul]
      have e2 : σ * ⟪b1 - b, tw v ε⟫ = σ * (b1 2 - b 2) + ε * (σ * ⟪b1 - b, v⟫) := hζε b1 ε
      rw [e1, e2, hδε, hc1def]
      have hεD : 0 ≤ ε * D := mul_nonneg hε.le hD.le
      nlinarith
  have evSplit : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ j ∈ J, c2 ≤ ⟪tgen nb0 nb1 (tw v ε) j, p⟫ ∨
      0 < ⟪cross (a - j.1) (tgen nb0 nb1 (tw v ε) j), tw v ε⟫ := by
    refine (eventually_all_finset J).2 fun j hj => ?_
    by_cases h0 : 0 < ⟪tgen nb0 nb1 ez j, p⟫
    · refine (ev_half (B := ⟪tgen' nb0 nb1 v j, p⟫) h0).mono fun ε h => Or.inl ?_
      have := hc2le j hj; simp only [h0, if_true] at this
      rw [hgenε]; linarith
    · have hT0 := (hsplit j hj).resolve_left h0
      have hcont := (continuous_tgen_torque_at nb0 nb1 v a j).neg.continuousAt (x := 0)
      have : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < -⟪cross (j.1 - a) (tgen nb0 nb1 (tw v ε) j), tw v ε⟫ := by
        refine hcont.eventually (lt_mem_nhds ?_)
        have e : tw v 0 = ez := by simp [tw]
        show 0 < -⟪cross (j.1 - a) (tgen nb0 nb1 (tw v 0) j), tw v 0⟫
        rw [e, ← inner_cross_sub_swap]; exact hT0
      exact (this.filter_mono nhdsWithin_le_nhds).mono fun _ h => Or.inr (by rwa [inner_cross_sub_swap])
  filter_upwards [ev_le_one, (eventually_all_finset X).2 hconvX, hconva, hconvb, hin, evM, evζ,
    evJ, evFar, evT, evP3, evDet, evTa, evSplit, ev_small (k := D * S)] with ε hε01 hcX hca hcb
    hIn hMε hζε' hJε hfar hTε hP3ε hdetε hTaε hsplitε hsmallε
  obtain ⟨hε0, -⟩ := hε01
  obtain ⟨f1, -, f3, f4, -, f6, f7, -, -, f10, f11, -, f13⟩ := hfar
  have wK2 : ∀ {x : ℝ}, x ≤ K2 → x ≤ K := fun h => by rw [hKdef]; linarith
  have wK1 : ∀ {x : ℝ}, x ≤ K1 → x ≤ K := fun h => by rw [hKdef]; linarith
  have wK3 : ∀ {x : ℝ}, x ≤ K3 → x ≤ K := fun h => by rw [hKdef]; linarith
  have hδpos : 0 < σ * ⟪a - b, tw v ε⟫ := by rw [hδε]; positivity
  intro F hF
  refine tie_no_forces_at_right_neg V X (tw v ε) a b a0 b1 m p nb0 nb1 hXV ha hb hab haX hbX ha0 hb1
    hnb0 hnb1 hcX hca hcb hIn σ hσ κ η Z K L c3 c c1 c2 hκ hη hc3 hc hc1 hc2 hL hZ hδpos hMε
    (fun y hy => (hζε' y hy).1) (fun y hy => (hζε' y hy).2) ?_ (fun j hj => wK1 (hJε j hj).1)
    (fun j hj => wK1 (hJε j hj).2.1) (fun j hj => wK1 (hJε j hj).2.2.1)
    (fun j hj => wK3 (by rw [inner_cross_sub_swap, abs_neg]; exact hTε j hj)) ?_
    (wK2 f1) (wK2 f13) ?_ hP3ε (wK2 f3) (wK2 f4) (wK2 f6) (wK2 f7) (wK2 f10) (wK2 f11)
    (by rw [hδε]; exact hTaε) hdetε ?_ F hF
  · intro j hj
    rw [hgenε, hδε, hLδ]
    have h1 : -|⟪tgen' nb0 nb1 v j, p⟫| ≤ ⟪tgen' nb0 nb1 v j, p⟫ := neg_abs_le _
    have h2 : |⟪tgen' nb0 nb1 v j, p⟫| ≤ sp := by
      have := single_le_sum (f := fun j => |⟪tgen' nb0 nb1 v j, p⟫|) (fun _ _ => abs_nonneg _) hj
      rw [hsp]; have := abs_nonneg ⟪cross (b1 - b) v, p⟫; linarith
    have h0 := hp j hj
    have h3 : ε * (-|⟪tgen' nb0 nb1 v j, p⟫|) ≤ ε * ⟪tgen' nb0 nb1 v j, p⟫ :=
      mul_le_mul_of_nonneg_left h1 hε0.le
    have h4 : ε * |⟪tgen' nb0 nb1 v j, p⟫| ≤ ε * sp := mul_le_mul_of_nonneg_left h2 hε0.le
    nlinarith
  · intro j hj
    rcases hsplitε j hj with h | h
    · exact Or.inl h
    · refine Or.inr (le_trans ?_ h.le)
      have : 0 ≤ L * (σ * ⟪a - b, tw v ε⟫) := mul_nonneg hL hδpos.le
      linarith
  · rw [inner_gen_right, hpb, zero_add, hδε, hLδ, abs_mul, abs_of_pos hε0]
    have : |⟪cross (b1 - b) v, p⟫| ≤ sp := by
      rw [hsp]; have := sum_nonneg fun j (_ : j ∈ J) => abs_nonneg ⟪tgen' nb0 nb1 v j, p⟫; linarith
    exact mul_le_mul_of_nonneg_left this hε0.le
  · rw [hδε]; nlinarith

theorem isRupert_of_tie_right (V X : Finset ℝ³) (v a b a0 b1 m p : ℝ³) (nb0 nb1 : ℝ³ → ℝ³)
    (hsol : (interior (convexHull ℝ (V : Set ℝ³))).Nonempty) (hv : v 2 = 0)
    (hXV : X ⊆ V) (ha : a ∈ V) (hb : b ∈ V) (hab : a ≠ b) (haX : a ∉ X) (hbX : b ∉ X)
    (ha0 : a0 ∈ V) (hb1 : b1 ∈ V) (hnb0 : ∀ y ∈ X, nb0 y ∈ V) (hnb1 : ∀ y ∈ X, nb1 y ∈ V)
    (htie : a 2 = b 2) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) (hD : 0 < σ * ⟪b - a, v⟫)
    (hXz : ∀ y ∈ X, 0 < σ * (y 2 - a 2))
    (hconvX : ∀ y ∈ X, ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < det3 (nb1 y - y) (nb0 y - y) (tw v ε))
    (hconva : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < det3 (b - a) (a0 - a) (tw v ε))
    (hconvb : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < det3 (b1 - b) (a - b) (tw v ε))
    (hin : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y ∈ V, y ∉ X → y ≠ a → y ≠ b → ∀ G : ℝ³,
      ⟪G, tw v ε⟫ = 0 → (∀ q ∈ V, ⟪G, q - y⟫ ≤ 0) → G = 0)
    (hm : ∀ j ∈ X ×ˢ (univ : Finset Bool), 0 < ⟪tgen nb0 nb1 ez j, m⟫)
    (hp : ∀ j ∈ X ×ˢ (univ : Finset Bool), 0 ≤ ⟪tgen nb0 nb1 ez j, p⟫)
    (hpa : ⟪cross ez (a0 - a), p⟫ = 0) (hp3 : ⟪cross (b - a) ez, p⟫ < 0)
    (hright : ⟪a - b, a0 - a⟫ = 0) (ha0z : 0 < σ * (a0 2 - a 2))
    (hsplit : ∀ j ∈ X ×ˢ (univ : Finset Bool), 0 < ⟪tgen nb0 nb1 ez j, p⟫ ∨
      0 < ⟪cross (j.1 - b) (tgen nb0 nb1 ez j), ez⟫)
    (hdet : cross (b - a) ez 0 * cross (b1 - b) ez 1 - cross (b - a) ez 1 * cross (b1 - b) ez 0 ≠ 0) :
    IsRupert V := by
  obtain ⟨ε, hε⟩ := (tie_no_forces_right V X v a b a0 b1 m p nb0 nb1 hXV ha hb hab haX hbX ha0 hb1
    hnb0 hnb1 htie σ hσ hD hXz hconvX hconva hconvb hin hm hp hpa hp3 hright ha0z hsplit hdet).exists
  exact isRupert_of_no_forces V hsol (tw v ε) (tw_ne_zero v ε hv)
    fun F h1 h2 h3 h4 h5 => hε F ⟨h1, h2, h3, h4, h5⟩

theorem isRupert_of_tie_right_neg (V X : Finset ℝ³) (v a b a0 b1 m p : ℝ³) (nb0 nb1 : ℝ³ → ℝ³)
    (hsol : (interior (convexHull ℝ (V : Set ℝ³))).Nonempty) (hv : v 2 = 0)
    (hXV : X ⊆ V) (ha : a ∈ V) (hb : b ∈ V) (hab : a ≠ b) (haX : a ∉ X) (hbX : b ∉ X)
    (ha0 : a0 ∈ V) (hb1 : b1 ∈ V) (hnb0 : ∀ y ∈ X, nb0 y ∈ V) (hnb1 : ∀ y ∈ X, nb1 y ∈ V)
    (htie : a 2 = b 2) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) (hD : 0 < σ * ⟪a - b, v⟫)
    (hXz : ∀ y ∈ X, 0 < σ * (y 2 - b 2))
    (hconvX : ∀ y ∈ X, ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < det3 (nb1 y - y) (nb0 y - y) (tw v ε))
    (hconva : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < det3 (b - a) (a0 - a) (tw v ε))
    (hconvb : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < det3 (b1 - b) (a - b) (tw v ε))
    (hin : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y ∈ V, y ∉ X → y ≠ a → y ≠ b → ∀ G : ℝ³,
      ⟪G, tw v ε⟫ = 0 → (∀ q ∈ V, ⟪G, q - y⟫ ≤ 0) → G = 0)
    (hm : ∀ j ∈ X ×ˢ (univ : Finset Bool), 0 < ⟪tgen nb0 nb1 ez j, m⟫)
    (hp : ∀ j ∈ X ×ˢ (univ : Finset Bool), 0 ≤ ⟪tgen nb0 nb1 ez j, p⟫)
    (hpb : ⟪cross (b1 - b) ez, p⟫ = 0) (hp3 : ⟪cross (b - a) ez, p⟫ < 0)
    (hright : ⟪a - b, b1 - b⟫ = 0) (hb1z : 0 < σ * (b1 2 - b 2))
    (hsplit : ∀ j ∈ X ×ˢ (univ : Finset Bool), 0 < ⟪tgen nb0 nb1 ez j, p⟫ ∨
      0 < ⟪cross (a - j.1) (tgen nb0 nb1 ez j), ez⟫)
    (hdet : cross (b - a) ez 0 * cross ez (a0 - a) 1 - cross (b - a) ez 1 * cross ez (a0 - a) 0 ≠ 0) :
    IsRupert V := by
  obtain ⟨ε, hε⟩ := (tie_no_forces_right_neg V X v a b a0 b1 m p nb0 nb1 hXV ha hb hab haX hbX ha0
    hb1 hnb0 hnb1 htie σ hσ hD hXz hconvX hconva hconvb hin hm hp hpb hp3 hright hb1z hsplit
    hdet).exists
  exact isRupert_of_no_forces V hsol (tw v ε) (tw_ne_zero v ε hv)
    fun F h1 h2 h3 h4 h5 => hε F ⟨h1, h2, h3, h4, h5⟩

end Minimality

end
