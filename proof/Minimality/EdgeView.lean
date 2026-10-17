module

public import Minimality.Thm73
public import Minimality.FaceFive

@[expose] public section

/-!
# The view along an edge between two quadrilaterals (Theorems B and B′)

Tools for Theorems B and B′ of `FEWER-FACES-PROOFS.md` §4–5 (types 02 and 05:
the view along an edge shared by two quadrilaterals, tilted into the dihedral
wedge `W` or into `-W`).

This first part is about cyclic sequences only: local maxima and minima
alternate, so a cyclic sequence of distinct reals with a unique local minimum
is unimodal (`isCyclicUnimodal_of_localMin_unique`).  The proofs bound the
local minima of the cycle seen in `W` and the local maxima of the cycle seen
in `-W`, and this converts the first bound into unimodality.
-/

namespace Minimality

open Finset Filter Topology
open scoped RealInnerProductSpace

/-- A window whose ends descend into it contains a strict local minimum. -/
theorem exists_localMin_window {k : ℕ} (z : ZMod k → ℝ) (hz : Function.Injective z)
    (B : ZMod k) (L : ℕ) (hL : L < k) (h2 : 2 ≤ L)
    (h0 : z (B + (1 : ℕ)) < z B) (h1 : z (B + (L - 1 : ℕ)) < z (B + L)) :
    ∃ p : ℕ, 0 < p ∧ p < L ∧ z (B + p) < z (B + p - 1) ∧ z (B + p) < z (B + p + 1) := by
  obtain ⟨u, hu, hmin⟩ := (Finset.Ioo 0 L).exists_min_image (fun q : ℕ => z (B + q))
    ⟨1, Finset.mem_Ioo.mpr ⟨by omega, by omega⟩⟩
  rw [Finset.mem_Ioo] at hu
  have hu1 := hmin 1 (Finset.mem_Ioo.mpr ⟨by omega, by omega⟩)
  have huL := hmin (L - 1) (Finset.mem_Ioo.mpr ⟨by omega, by omega⟩)
  obtain ⟨p, hp0, hpL, hp1, hp2⟩ := exists_localMax_window (fun i => -z i)
    (fun a b h => hz (neg_injective h)) B L hL u hu.1 hu.2
    (by show -z B < -z (B + (u : ZMod k)); linarith)
    (by show -z (B + (L : ZMod k)) < -z (B + (u : ZMod k)); linarith)
  exact ⟨p, hp0, hpL, by simpa using hp1, by simpa using hp2⟩

/-- At most one local minimum forces at most one local maximum: between two
local maxima (either way round the cycle) there is a local minimum. -/
theorem localMax_unique_of_localMin_unique {k : ℕ} [NeZero k] (z : ZMod k → ℝ)
    (hz : Function.Injective z)
    (hmin : ∀ a b : ZMod k, z a < z (a - 1) → z a < z (a + 1) →
      z b < z (b - 1) → z b < z (b + 1) → a = b)
    (a b : ZMod k) (ha1 : z (a - 1) < z a) (ha2 : z (a + 1) < z a)
    (hb1 : z (b - 1) < z b) (hb2 : z (b + 1) < z b) : a = b := by
  by_contra hab
  have hk : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
  set d : ℕ := (b - a).val with hd
  have hdk : d < k := ZMod.val_lt (b - a)
  have hbd : b = a + (d : ZMod k) := by rw [hd, ZMod.natCast_zmod_val]; ring
  have hd0 : d ≠ 0 := by
    intro h0; apply hab; rw [hbd, h0]; simp
  -- neither arc between them is a single step
  have hd1 : d ≠ 1 := by
    intro h1
    rw [h1, Nat.cast_one] at hbd
    rw [hbd, add_sub_cancel_right] at hb1
    linarith
  have hba : a = b + ((k - d : ℕ) : ZMod k) := by
    rw [hbd, add_assoc, ← Nat.cast_add, Nat.add_sub_cancel' hdk.le, ZMod.natCast_self, add_zero]
  have hd1' : k - d ≠ 1 := by
    intro h1
    rw [h1, Nat.cast_one] at hba
    rw [hba, add_sub_cancel_right] at ha1
    linarith
  -- a local minimum strictly inside each arc
  obtain ⟨p, hp0, hpd, hp1, hp2⟩ := exists_localMin_window z hz a d hdk (by omega)
    (by rw [Nat.cast_one]; exact ha2)
    (by rw [Nat.cast_sub (by omega), Nat.cast_one, ← add_sub_assoc, ← hbd]; exact hb1)
  obtain ⟨q, hq0, hqd, hq1, hq2⟩ := exists_localMin_window z hz b (k - d) (by omega) (by omega)
    (by rw [Nat.cast_one]; exact hb2)
    (by rw [Nat.cast_sub (by omega), Nat.cast_one, ← add_sub_assoc, ← hba]; exact ha1)
  have heq := hmin _ _ hp1 hp2 hq1 hq2
  rw [hbd, add_assoc, ← Nat.cast_add] at heq
  exact zmod_add_ne (k := k) (a := p) (b := d + q) (by omega) (by omega) (by omega) a heq

/-- A cyclic sequence of distinct reals (at least two terms) with at most one
local minimum is unimodal. -/
theorem isCyclicUnimodal_of_localMin_unique {k : ℕ} [NeZero k] (hk : 2 ≤ k) (z : ZMod k → ℝ)
    (hz : Function.Injective z)
    (hmin : ∀ a b : ZMod k, z a < z (a - 1) → z a < z (a + 1) →
      z b < z (b - 1) → z b < z (b + 1) → a = b) : IsCyclicUnimodal z := by
  classical
  refine ⟨hz, Finset.card_eq_one.mpr ?_⟩
  -- the global maximum is a local maximum
  obtain ⟨m, -, hm⟩ := (Finset.univ : Finset (ZMod k)).exists_max_image z ⟨0, Finset.mem_univ _⟩
  have hne : ∀ c : ZMod k, c ≠ 0 → m + c ≠ m := fun c hc h => hc (by simpa using h)
  have h1 : (1 : ZMod k) ≠ 0 := by
    have : Fact (1 < k) := ⟨by omega⟩
    exact one_ne_zero
  have hmax1 : z (m - 1) < z m := lt_of_le_of_ne (hm _ (Finset.mem_univ _)) fun h =>
    (hne (-1) (neg_ne_zero.mpr h1)) (by rw [← sub_eq_add_neg]; exact hz h)
  have hmax2 : z (m + 1) < z m := lt_of_le_of_ne (hm _ (Finset.mem_univ _)) fun h =>
    (hne 1 h1) (hz h)
  refine ⟨m, Finset.eq_singleton_iff_unique_mem.mpr ⟨by simp [hmax1, hmax2], fun b hb => ?_⟩⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
  exact localMax_unique_of_localMin_unique z hz hmin b m hb.1 hb.2 hmax1 hmax2

/-! ### The real-number facts behind Theorem B

A plane through a vertex `b` (depth `zb`) and points at oblique coordinates
`(T1, 0)` and `(0, T2)` (depths `x`, `y`) gives the depth `c` of a point at
`(S, U)` by `T1 T2 (c - zb) = S T2 (x - zb) + U T1 (y - zb)`; this is (Q3)
or (Q4) of `FEWER-FACES-PROOFS.md` §4 with denominators cleared. -/

/-- Both coefficients negative: the point is below `zb`. -/
theorem plane_below {T1 T2 S U zb x y c : ℝ} (hT1 : 0 < T1) (hT2 : 0 < T2) (hS : 0 < S)
    (hU : 0 < U) (hpl : T1 * T2 * (c - zb) = S * T2 * (x - zb) + U * T1 * (y - zb))
    (hx : x < zb) (hy : y < zb) : c < zb := by
  have h1 : S * T2 * (x - zb) < 0 := mul_neg_of_pos_of_neg (mul_pos hS hT2) (by linarith)
  have h2 : U * T1 * (y - zb) < 0 := mul_neg_of_pos_of_neg (mul_pos hU hT1) (by linarith)
  by_contra h
  have : 0 ≤ T1 * T2 * (c - zb) := mul_nonneg (mul_pos hT1 hT2).le (by linarith)
  linarith

/-- The far chord: if the point lies beyond the chord between the two points
(`S/T1 + U/T2 > 1`) and both coefficients are negative, it is below one of
them. -/
theorem plane_far {T1 T2 S U zb x y c : ℝ} (hT1 : 0 < T1) (hT2 : 0 < T2) (hS : 0 < S)
    (hU : 0 < U) (hpl : T1 * T2 * (c - zb) = S * T2 * (x - zb) + U * T1 * (y - zb))
    (hch : T1 * T2 < S * T2 + U * T1) (hx : x < zb) (hy : y < zb) (hcx : x < c) (hcy : y < c) :
    False := by
  have hc := plane_below hT1 hT2 hS hU hpl hx hy
  have h1 : S * T2 * (x - zb) < S * T2 * (c - zb) :=
    mul_lt_mul_of_pos_left (by linarith) (mul_pos hS hT2)
  have h2 : U * T1 * (y - zb) < U * T1 * (c - zb) :=
    mul_lt_mul_of_pos_left (by linarith) (mul_pos hU hT1)
  have h3 : (S * T2 + U * T1) * (c - zb) < T1 * T2 * (c - zb) :=
    mul_lt_mul_of_neg_right hch (by linarith)
  nlinarith

/-- The mixed case ((A, B) = (1, 5) in §4): the plane through `b`, `x` (at
`(T0, 0)`) and `y` (at `(0, T5)`), the far vertex `w` of the first side at
`(T1, 0)` with `T0 < T1` on a strictly convex lower chain `b, x, w`, and the
point `c` beyond the chord from `w` to `y`. Then `c` is not above both `w`
and `y`. -/
theorem plane_mixed {T0 T1 T5 S U zb x y w c : ℝ} (hT0 : 0 < T0) (hT5 : 0 < T5) (hS : 0 < S)
    (hU : 0 < U) (hT01 : T0 < T1)
    (hpl : T0 * T5 * (c - zb) = S * T5 * (x - zb) + U * T0 * (y - zb))
    (hconv : (x - zb) * (T1 - T0) < (w - x) * T0)
    (hch : T1 * T5 < S * T5 + U * T1) (hx : x < zb) (hy : y < zb) (hcw : w < c) (hcy : y < c) :
    False := by
  -- p = zb - x, q = zb - y
  obtain ⟨p, rfl⟩ : ∃ p, x = zb - p := ⟨zb - x, by ring⟩
  obtain ⟨q, rfl⟩ : ∃ q, y = zb - q := ⟨zb - y, by ring⟩
  have hp0 : 0 < p := by linarith
  have hq0 : 0 < q := by linarith
  have hT1 : 0 < T1 := by linarith
  have hpl' : T0 * T5 * (c - zb) = -(S * T5 * p) - U * T0 * q := by linear_combination hpl
  -- the convex chain: T0 (w - zb) > -T1 p
  have hw : -(T1 * p) < T0 * (w - zb) := by linear_combination hconv
  have hTT : 0 < T0 * T5 := mul_pos hT0 hT5
  -- (∗) from c > w
  have hcw' : T0 * T5 * (w - zb) < T0 * T5 * (c - zb) := mul_lt_mul_of_pos_left (by linarith) hTT
  have hw5 : T5 * -(T1 * p) < T5 * (T0 * (w - zb)) := mul_lt_mul_of_pos_left hw hT5
  have hstar : U * T0 * q < (T1 - S) * T5 * p := by linear_combination hcw' + hw5 + hpl'
  -- (∗∗) from c > y
  have hcy' : T0 * T5 * (-q) < T0 * T5 * (c - zb) := mul_lt_mul_of_pos_left (by linarith) hTT
  have hstar2 : S * T5 * p < (T5 - U) * T0 * q := by linear_combination hcy' + hpl'
  have hUT0q : 0 < U * T0 * q := mul_pos (mul_pos hU hT0) hq0
  have hST5p : 0 < S * T5 * p := mul_pos (mul_pos hS hT5) hp0
  by_cases hS1 : T1 ≤ S
  · have : (T1 - S) * T5 * p ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (by linarith) hT5.le) hp0.le
    linarith
  rw [not_le] at hS1
  by_cases hU5 : T5 ≤ U
  · have : (T5 - U) * T0 * q ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (by linarith) hT0.le) hq0.le
    linarith
  rw [not_le] at hU5
  -- T0 q < T1 p: (T1 - S) T5 < U T1 (chord) and (∗)
  have hA : (T1 - S) * T5 * p < U * T1 * p := mul_lt_mul_of_pos_right (by linarith) hp0
  have e1 : U * (T0 * q) < U * (T1 * p) := by linear_combination hstar + hA
  have e1' : T0 * q < T1 * p := lt_of_mul_lt_mul_left e1 hU.le
  -- T1 p < T0 q: (T5 - U) T1 < S T5 (chord) and (∗∗)
  have hB : (T5 - U) * T1 * (T0 * q) < S * T5 * (T0 * q) :=
    mul_lt_mul_of_pos_right (by linarith) (mul_pos hT0 hq0)
  have hstar2' : S * T5 * p * T1 < (T5 - U) * T0 * q * T1 := mul_lt_mul_of_pos_right hstar2 hT1
  have e2 : (S * T5) * (T1 * p) < (S * T5) * (T0 * q) := by linear_combination hstar2' + hB
  have e2' : T1 * p < T0 * q := lt_of_mul_lt_mul_left e2 (mul_pos hS hT5).le
  linarith

/-! ### The cycle core of Theorem B (type 02)

Labels as in §4: the edge 34 (`z3 < z4`), the quads 0134 and 3456 seen edge-on
with oblique coordinates `t0, t1` (on the first ray) and `t5, t6` (on the
second), vertex 2 at `(s2, u2)`; (Q3) and (Q4) with denominators cleared. The
far vertices are `A ∈ {0, 1}` and `B ∈ {5, 6}`. In `W` the cycle is
`(U2 reversed, U1, 2)` and in `-W` it is `(L2 reversed, L1, 2)`; each theorem
below says: the `W` cycle has a unique local minimum, or the `-W` cycle has a
unique local maximum. Indices are `Fin k` (definitionally `ZMod k`). -/

set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in
theorem cycles02_A1B6 {z0 z1 z2 z3 z4 z5 z6 t0 t1 t5 t6 s2 u2 : ℝ} (h34 : z3 < z4)
    (ht0 : 0 < t0) (ht1 : 0 < t1) (ht5 : 0 < t5) (ht6 : 0 < t6) (hs2 : 0 < s2) (hu2 : 0 < u2)
    (hQ3 : t0 * t5 * (z2 - z3) = s2 * t5 * (z0 - z3) + u2 * t0 * (z5 - z3))
    (hQ4 : t1 * t6 * (z2 - z4) = s2 * t6 * (z1 - z4) + u2 * t1 * (z6 - z4))
        (ht01 : t0 < t1) (ht56 : t5 < t6)
    (hch1 : (z0 - z3) * (t1 - t0) < (z1 - z0) * t0)
    (hch2 : (z5 - z3) * (t6 - t5) < (z6 - z5) * t5)
    (hchord : t1 * t6 < s2 * t6 + u2 * t1) :
    (∀ a b : Fin 4, (![z6, z4, z1, z2] : Fin 4 → ℝ) a < (![z6, z4, z1, z2] : Fin 4 → ℝ) (a - 1) → (![z6, z4, z1, z2] : Fin 4 → ℝ) a < (![z6, z4, z1, z2] : Fin 4 → ℝ) (a + 1) →
      (![z6, z4, z1, z2] : Fin 4 → ℝ) b < (![z6, z4, z1, z2] : Fin 4 → ℝ) (b - 1) → (![z6, z4, z1, z2] : Fin 4 → ℝ) b < (![z6, z4, z1, z2] : Fin 4 → ℝ) (b + 1) → a = b) ∨
    (∀ c d : Fin 6, (![z6, z5, z3, z0, z1, z2] : Fin 6 → ℝ) (c - 1) < (![z6, z5, z3, z0, z1, z2] : Fin 6 → ℝ) c → (![z6, z5, z3, z0, z1, z2] : Fin 6 → ℝ) (c + 1) < (![z6, z5, z3, z0, z1, z2] : Fin 6 → ℝ) c →
      (![z6, z5, z3, z0, z1, z2] : Fin 6 → ℝ) (d - 1) < (![z6, z5, z3, z0, z1, z2] : Fin 6 → ℝ) d → (![z6, z5, z3, z0, z1, z2] : Fin 6 → ℝ) (d + 1) < (![z6, z5, z3, z0, z1, z2] : Fin 6 → ℝ) d → c = d) := by
  have hneg4 : t1 * t6 * (-z2 - -z4) = s2 * t6 * (-z1 - -z4) + u2 * t1 * (-z6 - -z4) := by
    linear_combination -hQ4
  have hneg3 : t0 * t5 * (-z2 - -z3) = s2 * t5 * (-z0 - -z3) + u2 * t0 * (-z5 - -z3) := by
    linear_combination -hQ3
  have Fclaim : z4 < z1 → z4 < z6 → z0 < z3 → z5 < z3 → False := fun h1 h6 h0 h5 => by
    have := plane_below ht0 ht5 hs2 hu2 hQ3 h0 h5
    have := plane_below ht1 ht6 hs2 hu2 hneg4 (by linarith) (by linarith)
    linarith
  have Fi : z1 < z2 → z6 < z2 → z1 < z4 → z6 < z4 → False := fun ha hb h1 h6 =>
    plane_far ht1 ht6 hs2 hu2 hQ4 hchord h1 h6 ha hb
  have Fii : z2 < z1 → z2 < z6 → z4 < z1 → z4 < z6 → False := fun ha hb h1 h6 =>
    plane_far ht1 ht6 hs2 hu2 hneg4 hchord (by linarith) (by linarith) (by linarith) (by linarith)
  have Fc1 : z3 < z0 → z0 < z1 := fun h => by
    by_contra h'
    have : 0 < (z0 - z3) * (t1 - t0) := mul_pos (by linarith) (by linarith)
    have : (z1 - z0) * t0 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) ht0.le
    linarith
  have Fc2 : z3 < z5 → z5 < z6 := fun h => by
    by_contra h'
    have : 0 < (z5 - z3) * (t6 - t5) := mul_pos (by linarith) (by linarith)
    have : (z6 - z5) * t5 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) ht5.le
    linarith
  clear hQ3 hQ4 hneg3 hneg4 hch1 hch2 hchord ht0 ht1 ht5 ht6 hs2 hu2 ht01 ht56
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hW, hM⟩ := hcon
  push Not at hW hM
  obtain ⟨a, b, ha1, ha2, hb1, hb2, hab⟩ := hW
  obtain ⟨c, d, hc1, hc2, hd1, hd2, hcd⟩ := hM
  fin_cases a <;> fin_cases b <;> simp at ha1 ha2 hb1 hb2 hab <;>
    fin_cases c <;> fin_cases d <;> simp at hc1 hc2 hd1 hd2 hcd <;>
    first
    | linarith
    | exact Fclaim (by linarith) (by linarith) (by linarith) (by linarith)
    | exact Fi (by linarith) (by linarith) (by linarith) (by linarith)
    | exact Fii (by linarith) (by linarith) (by linarith) (by linarith)
    | linarith [Fc1 (by linarith)]
    | linarith [Fc2 (by linarith)]
    | linarith [Fc1 (by linarith), Fc2 (by linarith)]

set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in
theorem cycles02_A0B6 {z0 z1 z2 z3 z4 z5 z6 t0 t1 t5 t6 s2 u2 : ℝ} (h34 : z3 < z4)
    (ht0 : 0 < t0) (ht1 : 0 < t1) (ht5 : 0 < t5) (ht6 : 0 < t6) (hs2 : 0 < s2) (hu2 : 0 < u2)
    (hQ3 : t0 * t5 * (z2 - z3) = s2 * t5 * (z0 - z3) + u2 * t0 * (z5 - z3))
    (hQ4 : t1 * t6 * (z2 - z4) = s2 * t6 * (z1 - z4) + u2 * t1 * (z6 - z4))
        (ht01 : t1 < t0) (ht56 : t5 < t6)
    (hch1 : (z0 - z1) * t1 < (z1 - z4) * (t0 - t1))
    (hch2 : (z5 - z3) * (t6 - t5) < (z6 - z5) * t5)
    (hchord : t0 * t6 < s2 * t6 + u2 * t0) :
    (∀ a b : Fin 5, (![z6, z4, z1, z0, z2] : Fin 5 → ℝ) a < (![z6, z4, z1, z0, z2] : Fin 5 → ℝ) (a - 1) → (![z6, z4, z1, z0, z2] : Fin 5 → ℝ) a < (![z6, z4, z1, z0, z2] : Fin 5 → ℝ) (a + 1) →
      (![z6, z4, z1, z0, z2] : Fin 5 → ℝ) b < (![z6, z4, z1, z0, z2] : Fin 5 → ℝ) (b - 1) → (![z6, z4, z1, z0, z2] : Fin 5 → ℝ) b < (![z6, z4, z1, z0, z2] : Fin 5 → ℝ) (b + 1) → a = b) ∨
    (∀ c d : Fin 5, (![z6, z5, z3, z0, z2] : Fin 5 → ℝ) (c - 1) < (![z6, z5, z3, z0, z2] : Fin 5 → ℝ) c → (![z6, z5, z3, z0, z2] : Fin 5 → ℝ) (c + 1) < (![z6, z5, z3, z0, z2] : Fin 5 → ℝ) c →
      (![z6, z5, z3, z0, z2] : Fin 5 → ℝ) (d - 1) < (![z6, z5, z3, z0, z2] : Fin 5 → ℝ) d → (![z6, z5, z3, z0, z2] : Fin 5 → ℝ) (d + 1) < (![z6, z5, z3, z0, z2] : Fin 5 → ℝ) d → c = d) := by
  have hneg4 : t1 * t6 * (-z2 - -z4) = s2 * t6 * (-z1 - -z4) + u2 * t1 * (-z6 - -z4) := by
    linear_combination -hQ4
  have hneg3 : t0 * t5 * (-z2 - -z3) = s2 * t5 * (-z0 - -z3) + u2 * t0 * (-z5 - -z3) := by
    linear_combination -hQ3
  have Fclaim : z4 < z1 → z4 < z6 → z0 < z3 → z5 < z3 → False := fun h1 h6 h0 h5 => by
    have := plane_below ht0 ht5 hs2 hu2 hQ3 h0 h5
    have := plane_below ht1 ht6 hs2 hu2 hneg4 (by linarith) (by linarith)
    linarith
  have Fi : z6 < z2 → z0 < z2 → z0 < z3 → z5 < z3 → False := fun ha hb h0 h5 =>
    plane_mixed (T0 := t5) (T1 := t6) (T5 := t0) (S := u2) (U := s2) (zb := z3) (x := z5)
      (y := z0) (w := z6) (c := z2) ht5 ht0 hu2 hs2 ht56 (by linear_combination hQ3) hch2
      (by linarith) h5 h0 ha hb
  have Fii : z2 < z0 → z2 < z6 → z4 < z1 → z4 < z6 → False := fun ha hb h1 h6 =>
    plane_mixed (T0 := t1) (T1 := t0) (T5 := t6) (S := s2) (U := u2) (zb := -z4) (x := -z1)
      (y := -z6) (w := -z0) (c := -z2) ht1 ht6 hs2 hu2 ht01 hneg4
      (by linear_combination hch1) (by linarith) (by linarith) (by linarith) (by linarith)
      (by linarith)
  have Fc1 : z1 < z4 → z0 < z1 := fun h => by
    by_contra h'
    have : (z1 - z4) * (t0 - t1) < 0 := mul_neg_of_neg_of_pos (by linarith) (by linarith)
    have : 0 ≤ (z0 - z1) * t1 := mul_nonneg (by linarith) ht1.le
    linarith
  have Fc2 : z3 < z5 → z5 < z6 := fun h => by
    by_contra h'
    have : 0 < (z5 - z3) * (t6 - t5) := mul_pos (by linarith) (by linarith)
    have : (z6 - z5) * t5 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) ht5.le
    linarith
  clear hQ3 hQ4 hneg3 hneg4 hch1 hch2 hchord ht0 ht1 ht5 ht6 hs2 hu2 ht01 ht56
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hW, hM⟩ := hcon
  push Not at hW hM
  obtain ⟨a, b, ha1, ha2, hb1, hb2, hab⟩ := hW
  obtain ⟨c, d, hc1, hc2, hd1, hd2, hcd⟩ := hM
  fin_cases a <;> fin_cases b <;> simp at ha1 ha2 hb1 hb2 hab <;>
    fin_cases c <;> fin_cases d <;> simp at hc1 hc2 hd1 hd2 hcd <;>
    first
    | linarith
    | exact Fclaim (by linarith) (by linarith) (by linarith) (by linarith)
    | exact Fi (by linarith) (by linarith) (by linarith) (by linarith)
    | exact Fii (by linarith) (by linarith) (by linarith) (by linarith)
    | linarith [Fc1 (by linarith)]
    | linarith [Fc2 (by linarith)]
    | linarith [Fc1 (by linarith), Fc2 (by linarith)]

set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in
theorem cycles02_A1B5 {z0 z1 z2 z3 z4 z5 z6 t0 t1 t5 t6 s2 u2 : ℝ} (h34 : z3 < z4)
    (ht0 : 0 < t0) (ht1 : 0 < t1) (ht5 : 0 < t5) (ht6 : 0 < t6) (hs2 : 0 < s2) (hu2 : 0 < u2)
    (hQ3 : t0 * t5 * (z2 - z3) = s2 * t5 * (z0 - z3) + u2 * t0 * (z5 - z3))
    (hQ4 : t1 * t6 * (z2 - z4) = s2 * t6 * (z1 - z4) + u2 * t1 * (z6 - z4))
        (ht01 : t0 < t1) (ht56 : t6 < t5)
    (hch1 : (z0 - z3) * (t1 - t0) < (z1 - z0) * t0)
    (hch2 : (z5 - z6) * t6 < (z6 - z4) * (t5 - t6))
    (hchord : t1 * t5 < s2 * t5 + u2 * t1) :
    (∀ a b : Fin 5, (![z5, z6, z4, z1, z2] : Fin 5 → ℝ) a < (![z5, z6, z4, z1, z2] : Fin 5 → ℝ) (a - 1) → (![z5, z6, z4, z1, z2] : Fin 5 → ℝ) a < (![z5, z6, z4, z1, z2] : Fin 5 → ℝ) (a + 1) →
      (![z5, z6, z4, z1, z2] : Fin 5 → ℝ) b < (![z5, z6, z4, z1, z2] : Fin 5 → ℝ) (b - 1) → (![z5, z6, z4, z1, z2] : Fin 5 → ℝ) b < (![z5, z6, z4, z1, z2] : Fin 5 → ℝ) (b + 1) → a = b) ∨
    (∀ c d : Fin 5, (![z5, z3, z0, z1, z2] : Fin 5 → ℝ) (c - 1) < (![z5, z3, z0, z1, z2] : Fin 5 → ℝ) c → (![z5, z3, z0, z1, z2] : Fin 5 → ℝ) (c + 1) < (![z5, z3, z0, z1, z2] : Fin 5 → ℝ) c →
      (![z5, z3, z0, z1, z2] : Fin 5 → ℝ) (d - 1) < (![z5, z3, z0, z1, z2] : Fin 5 → ℝ) d → (![z5, z3, z0, z1, z2] : Fin 5 → ℝ) (d + 1) < (![z5, z3, z0, z1, z2] : Fin 5 → ℝ) d → c = d) := by
  have hneg4 : t1 * t6 * (-z2 - -z4) = s2 * t6 * (-z1 - -z4) + u2 * t1 * (-z6 - -z4) := by
    linear_combination -hQ4
  have hneg3 : t0 * t5 * (-z2 - -z3) = s2 * t5 * (-z0 - -z3) + u2 * t0 * (-z5 - -z3) := by
    linear_combination -hQ3
  have Fclaim : z4 < z1 → z4 < z6 → z0 < z3 → z5 < z3 → False := fun h1 h6 h0 h5 => by
    have := plane_below ht0 ht5 hs2 hu2 hQ3 h0 h5
    have := plane_below ht1 ht6 hs2 hu2 hneg4 (by linarith) (by linarith)
    linarith
  have Fi : z1 < z2 → z5 < z2 → z0 < z3 → z5 < z3 → False := fun ha hb h0 h5 =>
    plane_mixed ht0 ht5 hs2 hu2 ht01 hQ3 hch1 hchord h0 h5 ha hb
  have Fii : z2 < z1 → z2 < z5 → z4 < z1 → z4 < z6 → False := fun ha hb h1 h6 =>
    plane_mixed (T0 := t6) (T1 := t5) (T5 := t1) (S := u2) (U := s2) (zb := -z4) (x := -z6)
      (y := -z1) (w := -z5) (c := -z2) ht6 ht1 hu2 hs2 ht56 (by linear_combination hneg4)
      (by linear_combination hch2) (by linarith) (by linarith) (by linarith) (by linarith)
      (by linarith)
  have Fc1 : z3 < z0 → z0 < z1 := fun h => by
    by_contra h'
    have : 0 < (z0 - z3) * (t1 - t0) := mul_pos (by linarith) (by linarith)
    have : (z1 - z0) * t0 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) ht0.le
    linarith
  have Fc2 : z6 < z4 → z5 < z6 := fun h => by
    by_contra h'
    have : (z6 - z4) * (t5 - t6) < 0 := mul_neg_of_neg_of_pos (by linarith) (by linarith)
    have : 0 ≤ (z5 - z6) * t6 := mul_nonneg (by linarith) ht6.le
    linarith
  clear hQ3 hQ4 hneg3 hneg4 hch1 hch2 hchord ht0 ht1 ht5 ht6 hs2 hu2 ht01 ht56
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hW, hM⟩ := hcon
  push Not at hW hM
  obtain ⟨a, b, ha1, ha2, hb1, hb2, hab⟩ := hW
  obtain ⟨c, d, hc1, hc2, hd1, hd2, hcd⟩ := hM
  fin_cases a <;> fin_cases b <;> simp at ha1 ha2 hb1 hb2 hab <;>
    fin_cases c <;> fin_cases d <;> simp at hc1 hc2 hd1 hd2 hcd <;>
    first
    | linarith
    | exact Fclaim (by linarith) (by linarith) (by linarith) (by linarith)
    | exact Fi (by linarith) (by linarith) (by linarith) (by linarith)
    | exact Fii (by linarith) (by linarith) (by linarith) (by linarith)
    | linarith [Fc1 (by linarith)]
    | linarith [Fc2 (by linarith)]
    | linarith [Fc1 (by linarith), Fc2 (by linarith)]

set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in
theorem cycles02_A0B5 {z0 z1 z2 z3 z4 z5 z6 t0 t1 t5 t6 s2 u2 : ℝ} (h34 : z3 < z4)
    (ht0 : 0 < t0) (ht1 : 0 < t1) (ht5 : 0 < t5) (ht6 : 0 < t6) (hs2 : 0 < s2) (hu2 : 0 < u2)
    (hQ3 : t0 * t5 * (z2 - z3) = s2 * t5 * (z0 - z3) + u2 * t0 * (z5 - z3))
    (hQ4 : t1 * t6 * (z2 - z4) = s2 * t6 * (z1 - z4) + u2 * t1 * (z6 - z4))
        (ht01 : t1 < t0) (ht56 : t6 < t5)
    (hch1 : (z0 - z1) * t1 < (z1 - z4) * (t0 - t1))
    (hch2 : (z5 - z6) * t6 < (z6 - z4) * (t5 - t6))
    (hchord : t0 * t5 < s2 * t5 + u2 * t0) :
    (∀ a b : Fin 6, (![z5, z6, z4, z1, z0, z2] : Fin 6 → ℝ) a < (![z5, z6, z4, z1, z0, z2] : Fin 6 → ℝ) (a - 1) → (![z5, z6, z4, z1, z0, z2] : Fin 6 → ℝ) a < (![z5, z6, z4, z1, z0, z2] : Fin 6 → ℝ) (a + 1) →
      (![z5, z6, z4, z1, z0, z2] : Fin 6 → ℝ) b < (![z5, z6, z4, z1, z0, z2] : Fin 6 → ℝ) (b - 1) → (![z5, z6, z4, z1, z0, z2] : Fin 6 → ℝ) b < (![z5, z6, z4, z1, z0, z2] : Fin 6 → ℝ) (b + 1) → a = b) ∨
    (∀ c d : Fin 4, (![z5, z3, z0, z2] : Fin 4 → ℝ) (c - 1) < (![z5, z3, z0, z2] : Fin 4 → ℝ) c → (![z5, z3, z0, z2] : Fin 4 → ℝ) (c + 1) < (![z5, z3, z0, z2] : Fin 4 → ℝ) c →
      (![z5, z3, z0, z2] : Fin 4 → ℝ) (d - 1) < (![z5, z3, z0, z2] : Fin 4 → ℝ) d → (![z5, z3, z0, z2] : Fin 4 → ℝ) (d + 1) < (![z5, z3, z0, z2] : Fin 4 → ℝ) d → c = d) := by
  have hneg4 : t1 * t6 * (-z2 - -z4) = s2 * t6 * (-z1 - -z4) + u2 * t1 * (-z6 - -z4) := by
    linear_combination -hQ4
  have hneg3 : t0 * t5 * (-z2 - -z3) = s2 * t5 * (-z0 - -z3) + u2 * t0 * (-z5 - -z3) := by
    linear_combination -hQ3
  have Fclaim : z4 < z1 → z4 < z6 → z0 < z3 → z5 < z3 → False := fun h1 h6 h0 h5 => by
    have := plane_below ht0 ht5 hs2 hu2 hQ3 h0 h5
    have := plane_below ht1 ht6 hs2 hu2 hneg4 (by linarith) (by linarith)
    linarith
  have Fi : z0 < z2 → z5 < z2 → z0 < z3 → z5 < z3 → False := fun ha hb h0 h5 =>
    plane_far ht0 ht5 hs2 hu2 hQ3 hchord h0 h5 ha hb
  have Fii : z2 < z0 → z2 < z5 → z3 < z0 → z3 < z5 → False := fun ha hb h0 h5 =>
    plane_far ht0 ht5 hs2 hu2 hneg3 hchord (by linarith) (by linarith) (by linarith) (by linarith)
  have Fc1 : z1 < z4 → z0 < z1 := fun h => by
    by_contra h'
    have : (z1 - z4) * (t0 - t1) < 0 := mul_neg_of_neg_of_pos (by linarith) (by linarith)
    have : 0 ≤ (z0 - z1) * t1 := mul_nonneg (by linarith) ht1.le
    linarith
  have Fc2 : z6 < z4 → z5 < z6 := fun h => by
    by_contra h'
    have : (z6 - z4) * (t5 - t6) < 0 := mul_neg_of_neg_of_pos (by linarith) (by linarith)
    have : 0 ≤ (z5 - z6) * t6 := mul_nonneg (by linarith) ht6.le
    linarith
  clear hQ3 hQ4 hneg3 hneg4 hch1 hch2 hchord ht0 ht1 ht5 ht6 hs2 hu2 ht01 ht56
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hW, hM⟩ := hcon
  push Not at hW hM
  obtain ⟨a, b, ha1, ha2, hb1, hb2, hab⟩ := hW
  obtain ⟨c, d, hc1, hc2, hd1, hd2, hcd⟩ := hM
  fin_cases a <;> fin_cases b <;> simp at ha1 ha2 hb1 hb2 hab <;>
    fin_cases c <;> fin_cases d <;> simp at hc1 hc2 hd1 hd2 hcd <;>
    first
    | linarith
    | exact Fclaim (by linarith) (by linarith) (by linarith) (by linarith)
    | exact Fi (by linarith) (by linarith) (by linarith) (by linarith)
    | exact Fii (by linarith) (by linarith) (by linarith) (by linarith)
    | linarith [Fc1 (by linarith)]
    | linarith [Fc2 (by linarith)]
    | linarith [Fc1 (by linarith), Fc2 (by linarith)]

/-! ### The frame: the edge vertical, oblique coordinates in the shadow

The view is `ez`; the shadow of a point is `O + a r1 + b r2` in oblique
coordinates on the two rays `r1`, `r2` (with `cross2 r1 r2 > 0`), and its depth
is `z`. The tilt is `v = α r1 + β r2` (horizontal). Then the determinant tests
of Lemma 8.0 are explicit polynomials in `(a, b, z)`. -/

/-- The point with oblique shadow coordinates `(a, b)` and depth `z`. -/
noncomputable def oblPt (O r1 r2 : ℝ²) (a b z : ℝ) : ℝ³ :=
  !₂[O 0 + a * r1 0 + b * r2 0, O 1 + a * r1 1 + b * r2 1, z]

/-- **The determinant tests in oblique coordinates.** -/
theorem tiltSign_obl (O r1 r2 : ℝ²) (hρ : 0 < cross2 r1 r2) (α β : ℝ)
    {ap bp zp aq bq zq ay by' zy : ℝ}
    (h : 0 < (aq - ap) * (by' - bp) - (bq - bp) * (ay - ap) ∨
      ((aq - ap) * (by' - bp) - (bq - bp) * (ay - ap) = 0 ∧
        0 < (zq - zp) * ((ay - ap) * β - (by' - bp) * α) -
          (zy - zp) * ((aq - ap) * β - (bq - bp) * α))) :
    TiltSign (oblPt O r1 r2 aq bq zq - oblPt O r1 r2 ap bp zp)
      (oblPt O r1 r2 ay by' zy - oblPt O r1 r2 ap bp zp) ez (oblPt 0 r1 r2 α β 0) := by
  have e0 : det3 (oblPt O r1 r2 aq bq zq - oblPt O r1 r2 ap bp zp)
      (oblPt O r1 r2 ay by' zy - oblPt O r1 r2 ap bp zp) ez =
      ((aq - ap) * (by' - bp) - (bq - bp) * (ay - ap)) * cross2 r1 r2 := by
    rw [det3_ez]; simp [oblPt, cross2]; ring
  have e1 : det3 (oblPt O r1 r2 aq bq zq - oblPt O r1 r2 ap bp zp)
      (oblPt O r1 r2 ay by' zy - oblPt O r1 r2 ap bp zp) (oblPt 0 r1 r2 α β 0) =
      ((zq - zp) * ((ay - ap) * β - (by' - bp) * α) -
          (zy - zp) * ((aq - ap) * β - (bq - bp) * α)) * cross2 r1 r2 := by
    rw [det3_gen]; simp [oblPt, cross2]; ring
  unfold TiltSign
  rw [e0, e1]
  rcases h with h | ⟨h0, h1⟩
  · exact Or.inl (mul_pos h hρ)
  · exact Or.inr ⟨by rw [h0, zero_mul], mul_pos h1 hρ⟩

/-! The six kinds of determinant test along the cycles of Theorem B. `D` below
is the hypothesis of `tiltSign_obl`. -/

/-- The disjunction of `tiltSign_obl`. -/
def TiltOK (ap bp zp aq bq zq ay by' zy α β : ℝ) : Prop :=
  0 < (aq - ap) * (by' - bp) - (bq - bp) * (ay - ap) ∨
    ((aq - ap) * (by' - bp) - (bq - bp) * (ay - ap) = 0 ∧
      0 < (zq - zp) * ((ay - ap) * β - (by' - bp) * α) -
        (zy - zp) * ((aq - ap) * β - (bq - bp) * α))

/-- Side 1 (`b = 0`), outward, the test point off the quad's plane. -/
theorem tiltOK_side1_off {ap aq zp zq ay by' zy α β : ℝ} (hpq : ap < aq) (hy : 0 < by') :
    TiltOK ap 0 zp aq 0 zq ay by' zy α β :=
  Or.inl (by nlinarith [mul_pos (sub_pos.mpr hpq) hy])

/-- Side 1, the test point on the quad (`b = 0`): the sign of `β` and the
orientation of `(p, q, y)` in the `(a, z)`-plane. -/
theorem tiltOK_side1_on {ap aq zp zq ay zy α β : ℝ}
    (h : (0 < β ∧ (aq - ap) * (zy - zp) - (zq - zp) * (ay - ap) < 0) ∨
      (β < 0 ∧ 0 < (aq - ap) * (zy - zp) - (zq - zp) * (ay - ap))) :
    TiltOK ap 0 zp aq 0 zq ay 0 zy α β := by
  right; refine ⟨by ring, ?_⟩
  rcases h with ⟨hb, hc⟩ | ⟨hb, hc⟩
  · nlinarith [mul_pos hb (neg_pos.mpr hc)]
  · nlinarith [mul_pos (neg_pos.mpr hb) hc]

/-- Side 2 (`a = 0`), inward (`b` decreasing), the test point off the quad. -/
theorem tiltOK_side2_off {bp bq zp zq ay by' zy α β : ℝ} (hpq : bq < bp) (hy : 0 < ay) :
    TiltOK 0 bp zp 0 bq zq ay by' zy α β :=
  Or.inl (by nlinarith [mul_pos (sub_pos.mpr hpq) hy])

/-- Side 2, the test point on the quad (`a = 0`). -/
theorem tiltOK_side2_on {bp bq zp zq by' zy α β : ℝ}
    (h : (0 < α ∧ 0 < (bq - bp) * (zy - zp) - (zq - zp) * (by' - bp)) ∨
      (α < 0 ∧ (bq - bp) * (zy - zp) - (zq - zp) * (by' - bp) < 0)) :
    TiltOK 0 bp zp 0 bq zq 0 by' zy α β := by
  right; refine ⟨by ring, ?_⟩
  rcases h with ⟨ha, hc⟩ | ⟨ha, hc⟩
  · nlinarith [mul_pos ha hc]
  · nlinarith [mul_pos (neg_pos.mpr ha) (neg_pos.mpr hc)]

/-- The far edge from `A = (tA, 0)` to `2 = (s2, u2)`, beyond the chord to
`B = (0, tB)`. -/
theorem tiltOK_farA {tA tB s2 u2 zp zq ay by' zy α β : ℝ} (hA : 0 < tA)
    (hu2 : 0 < u2) (hch : tA * tB < s2 * tB + u2 * tA)
    (hy : (by' = 0 ∧ ay < tA) ∨ (ay = 0 ∧ 0 ≤ by' ∧ by' ≤ tB)) :
    TiltOK tA 0 zp s2 u2 zq ay by' zy α β := by
  left
  rcases hy with ⟨h0, h1⟩ | ⟨h0, h1, h2⟩
  · subst h0; nlinarith [mul_pos hu2 (sub_pos.mpr h1)]
  · subst h0
    rcases le_or_gt tA s2 with hs | hs
    · nlinarith [mul_nonneg (sub_nonneg.mpr hs) h1, mul_pos hu2 hA]
    · nlinarith [mul_nonneg (sub_nonneg.mpr h2) (sub_pos.mpr hs).le]

/-- The far edge from `2 = (s2, u2)` to `B = (0, tB)`. -/
theorem tiltOK_farB {tA tB s2 u2 zp zq ay by' zy α β : ℝ} (hB : 0 < tB)
    (hs2 : 0 < s2) (hch : tA * tB < s2 * tB + u2 * tA)
    (hy : (ay = 0 ∧ by' < tB) ∨ (by' = 0 ∧ 0 ≤ ay ∧ ay ≤ tA)) :
    TiltOK s2 u2 zp 0 tB zq ay by' zy α β := by
  left
  rcases hy with ⟨h0, h1⟩ | ⟨h0, h1, h2⟩
  · subst h0; nlinarith [mul_pos hs2 (sub_pos.mpr h1)]
  · subst h0
    rcases le_or_gt tB u2 with hu | hu
    · nlinarith [mul_nonneg (sub_nonneg.mpr hu) h1, mul_pos hs2 hB]
    · nlinarith [mul_nonneg (sub_nonneg.mpr h2) (sub_pos.mpr hu).le]

/-- A cyclic sequence of distinct reals (at least two terms) with at most one
local maximum is unimodal. -/
theorem isCyclicUnimodal_of_localMax_unique {k : ℕ} [NeZero k] (hk : 2 ≤ k) (z : ZMod k → ℝ)
    (hz : Function.Injective z)
    (hmax : ∀ a b : ZMod k, z (a - 1) < z a → z (a + 1) < z a →
      z (b - 1) < z b → z (b + 1) < z b → a = b) : IsCyclicUnimodal z := by
  have h := isCyclicUnimodal_of_localMin_unique hk (fun i => -z i)
    (fun a b e => hz (neg_injective e))
    (fun a b h1 h2 h3 h4 => hmax a b (by linarith) (by linarith) (by linarith) (by linarith))
  refine ⟨hz, ?_⟩
  -- the local maxima of `z` are the local minima of `-z`
  obtain ⟨-, hc⟩ := h
  classical
  have hmin : (Finset.univ.filter fun i : ZMod k => -z i < -z (i - 1) ∧ -z i < -z (i + 1)).card
      = 1 := by
    -- `-z` has a unique local minimum as well (alternation, applied to `z`)
    refine Finset.card_eq_one.mpr ?_
    obtain ⟨m, -, hm⟩ := (Finset.univ : Finset (ZMod k)).exists_max_image z ⟨0, Finset.mem_univ _⟩
    have h1 : (1 : ZMod k) ≠ 0 := by
      have : Fact (1 < k) := ⟨by omega⟩
      exact one_ne_zero
    have hne : ∀ c : ZMod k, c ≠ 0 → m + c ≠ m := fun c hc h => hc (by simpa using h)
    have hmax1 : z (m - 1) < z m := lt_of_le_of_ne (hm _ (Finset.mem_univ _)) fun h =>
      (hne (-1) (neg_ne_zero.mpr h1)) (by rw [← sub_eq_add_neg]; exact hz h)
    have hmax2 : z (m + 1) < z m := lt_of_le_of_ne (hm _ (Finset.mem_univ _)) fun h =>
      (hne 1 h1) (hz h)
    refine ⟨m, Finset.eq_singleton_iff_unique_mem.mpr ⟨by simp [hmax1, hmax2], fun b hb => ?_⟩⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, neg_lt_neg_iff] at hb
    exact hmax b m hb.1 hb.2 hmax1 hmax2
  simpa only [neg_lt_neg_iff] using hmin

/-- Unimodal limit depths stay unimodal under small tilts. -/
theorem eventually_unimodal_tilt {k : ℕ} [NeZero k] (x : ZMod k → ℝ³) (u₀ v : ℝ³)
    (hu : IsCyclicUnimodal fun i => ⟪x i, u₀⟫) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), IsCyclicUnimodal fun i => ⟪x i, u₀ + ε • v⟫ := by
  have hc : Continuous fun ε : ℝ => fun i => ⟪x i, u₀ + ε • v⟫ := by fun_prop
  have := hc.continuousAt (x := 0) |>.preimage_mem_nhds (isOpen_isCyclicUnimodal.mem_nhds
    (by simpa using hu))
  exact nhdsWithin_le_nhds this

/-- A convex quadrilateral `p0 p1 p2 p3`, counterclockwise in the `(a, z)`-plane:
every vertex is strictly left of every edge it is not on. -/
def ConvQuad (a0 z0 a1 z1 a2 z2 a3 z3 : ℝ) : Prop :=
  (0 < (a1 - a0) * (z2 - z0) - (z1 - z0) * (a2 - a0) ∧
    0 < (a1 - a0) * (z3 - z0) - (z1 - z0) * (a3 - a0)) ∧
  (0 < (a2 - a1) * (z3 - z1) - (z2 - z1) * (a3 - a1) ∧
    0 < (a2 - a1) * (z0 - z1) - (z2 - z1) * (a0 - a1)) ∧
  (0 < (a3 - a2) * (z0 - z2) - (z3 - z2) * (a0 - a2) ∧
    0 < (a3 - a2) * (z1 - z2) - (z3 - z2) * (a1 - a2)) ∧
  (0 < (a0 - a3) * (z1 - z3) - (z0 - z3) * (a1 - a3) ∧
    0 < (a0 - a3) * (z2 - z3) - (z0 - z3) * (a2 - a3))

/-! ### The frame theorem for type 02, one shape and wedge at a time

The cycle is listed counterclockwise (`cross2 r1 r2 > 0`); in `W` the tilt is
`r1 + r2`, in `-W` it is `-(r1 + r2)`. Each test of Lemma 8.0 is one of the six
kinds above. -/

set_option maxHeartbeats 4000000 in
set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in
theorem rupert02_W_A1B6 (O r1 r2 : ℝ²) (hρ : 0 < cross2 r1 r2)
    {t0 t1 t5 t6 s2 u2 z0 z1 z2 z3 z4 z5 z6 : ℝ} (ht0 : 0 < t0) (ht1 : 0 < t1) (ht5 : 0 < t5)
    (ht6 : 0 < t6) (hs2 : 0 < s2) (hu2 : 0 < u2)
    (hQ1 : ConvQuad 0 z3 t0 z0 t1 z1 0 z4) (hQ2 : ConvQuad 0 z3 t5 z5 t6 z6 0 z4)
    (ht01 : t0 < t1) (ht56 : t5 < t6) (hch : t1 * t6 < s2 * t6 + u2 * t1)
    (hinj : Function.Injective (![z6, z4, z1, z2] : Fin 4 → ℝ))
    (hext : ∀ a b : Fin 4, (![z6, z4, z1, z2] : Fin 4 → ℝ) a < (![z6, z4, z1, z2] : Fin 4 → ℝ) (a - 1) →
      (![z6, z4, z1, z2] : Fin 4 → ℝ) a < (![z6, z4, z1, z2] : Fin 4 → ℝ) (a + 1) →
      (![z6, z4, z1, z2] : Fin 4 → ℝ) b < (![z6, z4, z1, z2] : Fin 4 → ℝ) (b - 1) →
      (![z6, z4, z1, z2] : Fin 4 → ℝ) b < (![z6, z4, z1, z2] : Fin 4 → ℝ) (b + 1) → a = b) :
    IsRupert ({oblPt O r1 r2 t0 0 z0, oblPt O r1 r2 t1 0 z1, oblPt O r1 r2 s2 u2 z2, oblPt O r1 r2 0 0 z3, oblPt O r1 r2 0 0 z4, oblPt O r1 r2 0 t5 z5, oblPt O r1 r2 0 t6 z6} : Finset ℝ³) := by
  obtain ⟨⟨q1a, q1b⟩, ⟨q1c, q1d⟩, ⟨q1e, q1f⟩, ⟨q1g, q1h⟩⟩ := hQ1
  obtain ⟨⟨q2a, q2b⟩, ⟨q2c, q2d⟩, ⟨q2e, q2f⟩, ⟨q2g, q2h⟩⟩ := hQ2
  have key : ∀ {ap bp zp aq bq zq ay by' zy : ℝ}, TiltOK ap bp zp aq bq zq ay by' zy (1) (1) →
      TiltSign (oblPt O r1 r2 aq bq zq - oblPt O r1 r2 ap bp zp)
        (oblPt O r1 r2 ay by' zy - oblPt O r1 r2 ap bp zp) ez (oblPt 0 r1 r2 (1) (1) 0) :=
    fun h => tiltSign_obl O r1 r2 hρ (1) (1) h
  have hez : (ez : ℝ³) ≠ 0 := by
    intro h; have := congrArg (fun x : ℝ³ => x 2) h; simp [ez] at this
  set x : Fin 4 → ℝ³ := ![oblPt O r1 r2 0 t6 z6, oblPt O r1 r2 0 0 z4, oblPt O r1 r2 t1 0 z1, oblPt O r1 r2 s2 u2 z2] with hx
  have hxV : ∀ i : Fin 4, x i ∈ ({oblPt O r1 r2 t0 0 z0, oblPt O r1 r2 t1 0 z1, oblPt O r1 r2 s2 u2 z2, oblPt O r1 r2 0 0 z3, oblPt O r1 r2 0 0 z4, oblPt O r1 r2 0 t5 z5, oblPt O r1 r2 0 t6 z6} : Finset ℝ³) := by
    intro i; fin_cases i <;> simp [hx]
  have hcyc : ∀ i j : Fin 4, j ≠ i → j ≠ i + 1 →
      TiltSign (x (i + 1) - x i) (x j - x i) ez (oblPt 0 r1 r2 (1) (1) 0) := by
    intro i j hji hji1
    fin_cases i <;> fin_cases j <;> simp [hx] at hji hji1 ⊢ <;> apply key
    all_goals first
      | (refine tiltOK_side1_off ?_ ?_ <;> linarith)
      | (refine tiltOK_side2_off ?_ ?_ <;> linarith)
      | (refine tiltOK_side1_on (Or.inl ⟨?_, ?_⟩) <;> linarith)
      | (refine tiltOK_side1_on (Or.inr ⟨?_, ?_⟩) <;> linarith)
      | (refine tiltOK_side2_on (Or.inl ⟨?_, ?_⟩) <;> linarith)
      | (refine tiltOK_side2_on (Or.inr ⟨?_, ?_⟩) <;> linarith)
      | (refine tiltOK_farA ht1 hu2 hch ?_
         first | (left; constructor <;> linarith) | (right; refine ⟨?_, ?_, ?_⟩ <;> linarith))
      | (refine tiltOK_farB ht6 hs2 hch ?_
         first | (left; constructor <;> linarith) | (right; refine ⟨?_, ?_, ?_⟩ <;> linarith))
  have hrest : ∀ y ∈ ({oblPt O r1 r2 t0 0 z0, oblPt O r1 r2 t1 0 z1, oblPt O r1 r2 s2 u2 z2, oblPt O r1 r2 0 0 z3, oblPt O r1 r2 0 0 z4, oblPt O r1 r2 0 t5 z5, oblPt O r1 r2 0 t6 z6} : Finset ℝ³), (∀ j : Fin 4, y ≠ x j) → ∀ i : Fin 4,
      TiltSign (x (i + 1) - x i) (y - x i) ez (oblPt 0 r1 r2 (1) (1) 0) := by
    intro y hy hyx i
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | (exfalso; apply hyx 0; simp [hx]; done)
      | (exfalso; apply hyx 1; simp [hx]; done)
      | (exfalso; apply hyx 2; simp [hx]; done)
      | (exfalso; apply hyx 3; simp [hx]; done)
      | (fin_cases i <;> simp [hx] <;> apply key <;> first
          | (refine tiltOK_side1_off ?_ ?_ <;> linarith)
          | (refine tiltOK_side2_off ?_ ?_ <;> linarith)
          | (refine tiltOK_side1_on (Or.inl ⟨?_, ?_⟩) <;> linarith)
          | (refine tiltOK_side1_on (Or.inr ⟨?_, ?_⟩) <;> linarith)
          | (refine tiltOK_side2_on (Or.inl ⟨?_, ?_⟩) <;> linarith)
          | (refine tiltOK_side2_on (Or.inr ⟨?_, ?_⟩) <;> linarith)
          | (refine tiltOK_farA ht1 hu2 hch ?_
             first | (left; constructor <;> linarith) | (right; refine ⟨?_, ?_, ?_⟩ <;> linarith))
          | (refine tiltOK_farB ht6 hs2 hch ?_
             first | (left; constructor <;> linarith) | (right; refine ⟨?_, ?_, ?_⟩ <;> linarith)))
  have hz : (fun i : Fin 4 => ⟪x i, ez⟫) = ![z6, z4, z1, z2] := by
    funext i; fin_cases i <;> simp [hx, oblPt, inner_ez]
  have hu0 : IsCyclicUnimodal (k := 4) fun i => ⟪x i, ez⟫ := by
    have := isCyclicUnimodal_of_localMin_unique (k := 4) (by norm_num) ![z6, z4, z1, z2] hinj hext
    rw [show (fun i : ZMod 4 => ⟪x i, ez⟫) = ![z6, z4, z1, z2] from hz]; exact this
  exact isRupert_of_tilted_unimodal' _ ez (oblPt 0 r1 r2 (1) (1) 0) hez (k := 4) (by norm_num)
    x hxV hcyc hrest IsCyclicUnimodal isOpen_isCyclicUnimodal
    (fun z c hc hz => isCyclicUnimodal_smul hc hz)
    (eventually_unimodal_tilt (k := 4) x ez (oblPt 0 r1 r2 (1) (1) 0) hu0) (fun z _ h => h)

set_option maxHeartbeats 4000000 in
set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in
theorem rupert02_W_A0B6 (O r1 r2 : ℝ²) (hρ : 0 < cross2 r1 r2)
    {t0 t1 t5 t6 s2 u2 z0 z1 z2 z3 z4 z5 z6 : ℝ} (ht0 : 0 < t0) (ht1 : 0 < t1) (ht5 : 0 < t5)
    (ht6 : 0 < t6) (hs2 : 0 < s2) (hu2 : 0 < u2)
    (hQ1 : ConvQuad 0 z3 t0 z0 t1 z1 0 z4) (hQ2 : ConvQuad 0 z3 t5 z5 t6 z6 0 z4)
    (ht01 : t1 < t0) (ht56 : t5 < t6) (hch : t0 * t6 < s2 * t6 + u2 * t0)
    (hinj : Function.Injective (![z6, z4, z1, z0, z2] : Fin 5 → ℝ))
    (hext : ∀ a b : Fin 5, (![z6, z4, z1, z0, z2] : Fin 5 → ℝ) a < (![z6, z4, z1, z0, z2] : Fin 5 → ℝ) (a - 1) →
      (![z6, z4, z1, z0, z2] : Fin 5 → ℝ) a < (![z6, z4, z1, z0, z2] : Fin 5 → ℝ) (a + 1) →
      (![z6, z4, z1, z0, z2] : Fin 5 → ℝ) b < (![z6, z4, z1, z0, z2] : Fin 5 → ℝ) (b - 1) →
      (![z6, z4, z1, z0, z2] : Fin 5 → ℝ) b < (![z6, z4, z1, z0, z2] : Fin 5 → ℝ) (b + 1) → a = b) :
    IsRupert ({oblPt O r1 r2 t0 0 z0, oblPt O r1 r2 t1 0 z1, oblPt O r1 r2 s2 u2 z2, oblPt O r1 r2 0 0 z3, oblPt O r1 r2 0 0 z4, oblPt O r1 r2 0 t5 z5, oblPt O r1 r2 0 t6 z6} : Finset ℝ³) := by
  obtain ⟨⟨q1a, q1b⟩, ⟨q1c, q1d⟩, ⟨q1e, q1f⟩, ⟨q1g, q1h⟩⟩ := hQ1
  obtain ⟨⟨q2a, q2b⟩, ⟨q2c, q2d⟩, ⟨q2e, q2f⟩, ⟨q2g, q2h⟩⟩ := hQ2
  have key : ∀ {ap bp zp aq bq zq ay by' zy : ℝ}, TiltOK ap bp zp aq bq zq ay by' zy (1) (1) →
      TiltSign (oblPt O r1 r2 aq bq zq - oblPt O r1 r2 ap bp zp)
        (oblPt O r1 r2 ay by' zy - oblPt O r1 r2 ap bp zp) ez (oblPt 0 r1 r2 (1) (1) 0) :=
    fun h => tiltSign_obl O r1 r2 hρ (1) (1) h
  have hez : (ez : ℝ³) ≠ 0 := by
    intro h; have := congrArg (fun x : ℝ³ => x 2) h; simp [ez] at this
  set x : Fin 5 → ℝ³ := ![oblPt O r1 r2 0 t6 z6, oblPt O r1 r2 0 0 z4, oblPt O r1 r2 t1 0 z1, oblPt O r1 r2 t0 0 z0, oblPt O r1 r2 s2 u2 z2] with hx
  have hxV : ∀ i : Fin 5, x i ∈ ({oblPt O r1 r2 t0 0 z0, oblPt O r1 r2 t1 0 z1, oblPt O r1 r2 s2 u2 z2, oblPt O r1 r2 0 0 z3, oblPt O r1 r2 0 0 z4, oblPt O r1 r2 0 t5 z5, oblPt O r1 r2 0 t6 z6} : Finset ℝ³) := by
    intro i; fin_cases i <;> simp [hx]
  have hcyc : ∀ i j : Fin 5, j ≠ i → j ≠ i + 1 →
      TiltSign (x (i + 1) - x i) (x j - x i) ez (oblPt 0 r1 r2 (1) (1) 0) := by
    intro i j hji hji1
    fin_cases i <;> fin_cases j <;> simp [hx] at hji hji1 ⊢ <;> apply key
    all_goals first
      | (refine tiltOK_side1_off ?_ ?_ <;> linarith)
      | (refine tiltOK_side2_off ?_ ?_ <;> linarith)
      | (refine tiltOK_side1_on (Or.inl ⟨?_, ?_⟩) <;> linarith)
      | (refine tiltOK_side1_on (Or.inr ⟨?_, ?_⟩) <;> linarith)
      | (refine tiltOK_side2_on (Or.inl ⟨?_, ?_⟩) <;> linarith)
      | (refine tiltOK_side2_on (Or.inr ⟨?_, ?_⟩) <;> linarith)
      | (refine tiltOK_farA ht0 hu2 hch ?_
         first | (left; constructor <;> linarith) | (right; refine ⟨?_, ?_, ?_⟩ <;> linarith))
      | (refine tiltOK_farB ht6 hs2 hch ?_
         first | (left; constructor <;> linarith) | (right; refine ⟨?_, ?_, ?_⟩ <;> linarith))
  have hrest : ∀ y ∈ ({oblPt O r1 r2 t0 0 z0, oblPt O r1 r2 t1 0 z1, oblPt O r1 r2 s2 u2 z2, oblPt O r1 r2 0 0 z3, oblPt O r1 r2 0 0 z4, oblPt O r1 r2 0 t5 z5, oblPt O r1 r2 0 t6 z6} : Finset ℝ³), (∀ j : Fin 5, y ≠ x j) → ∀ i : Fin 5,
      TiltSign (x (i + 1) - x i) (y - x i) ez (oblPt 0 r1 r2 (1) (1) 0) := by
    intro y hy hyx i
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | (exfalso; apply hyx 0; simp [hx]; done)
      | (exfalso; apply hyx 1; simp [hx]; done)
      | (exfalso; apply hyx 2; simp [hx]; done)
      | (exfalso; apply hyx 3; simp [hx]; done)
      | (exfalso; apply hyx 4; simp [hx]; done)
      | (fin_cases i <;> simp [hx] <;> apply key <;> first
          | (refine tiltOK_side1_off ?_ ?_ <;> linarith)
          | (refine tiltOK_side2_off ?_ ?_ <;> linarith)
          | (refine tiltOK_side1_on (Or.inl ⟨?_, ?_⟩) <;> linarith)
          | (refine tiltOK_side1_on (Or.inr ⟨?_, ?_⟩) <;> linarith)
          | (refine tiltOK_side2_on (Or.inl ⟨?_, ?_⟩) <;> linarith)
          | (refine tiltOK_side2_on (Or.inr ⟨?_, ?_⟩) <;> linarith)
          | (refine tiltOK_farA ht0 hu2 hch ?_
             first | (left; constructor <;> linarith) | (right; refine ⟨?_, ?_, ?_⟩ <;> linarith))
          | (refine tiltOK_farB ht6 hs2 hch ?_
             first | (left; constructor <;> linarith) | (right; refine ⟨?_, ?_, ?_⟩ <;> linarith)))
  have hz : (fun i : Fin 5 => ⟪x i, ez⟫) = ![z6, z4, z1, z0, z2] := by
    funext i; fin_cases i <;> simp [hx, oblPt, inner_ez]
  have hu0 : IsCyclicUnimodal (k := 5) fun i => ⟪x i, ez⟫ := by
    have := isCyclicUnimodal_of_localMin_unique (k := 5) (by norm_num) ![z6, z4, z1, z0, z2] hinj hext
    rw [show (fun i : ZMod 5 => ⟪x i, ez⟫) = ![z6, z4, z1, z0, z2] from hz]; exact this
  exact isRupert_of_tilted_unimodal' _ ez (oblPt 0 r1 r2 (1) (1) 0) hez (k := 5) (by norm_num)
    x hxV hcyc hrest IsCyclicUnimodal isOpen_isCyclicUnimodal
    (fun z c hc hz => isCyclicUnimodal_smul hc hz)
    (eventually_unimodal_tilt (k := 5) x ez (oblPt 0 r1 r2 (1) (1) 0) hu0) (fun z _ h => h)

set_option maxHeartbeats 4000000 in
set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in
theorem rupert02_W_A1B5 (O r1 r2 : ℝ²) (hρ : 0 < cross2 r1 r2)
    {t0 t1 t5 t6 s2 u2 z0 z1 z2 z3 z4 z5 z6 : ℝ} (ht0 : 0 < t0) (ht1 : 0 < t1) (ht5 : 0 < t5)
    (ht6 : 0 < t6) (hs2 : 0 < s2) (hu2 : 0 < u2)
    (hQ1 : ConvQuad 0 z3 t0 z0 t1 z1 0 z4) (hQ2 : ConvQuad 0 z3 t5 z5 t6 z6 0 z4)
    (ht01 : t0 < t1) (ht56 : t6 < t5) (hch : t1 * t5 < s2 * t5 + u2 * t1)
    (hinj : Function.Injective (![z5, z6, z4, z1, z2] : Fin 5 → ℝ))
    (hext : ∀ a b : Fin 5, (![z5, z6, z4, z1, z2] : Fin 5 → ℝ) a < (![z5, z6, z4, z1, z2] : Fin 5 → ℝ) (a - 1) →
      (![z5, z6, z4, z1, z2] : Fin 5 → ℝ) a < (![z5, z6, z4, z1, z2] : Fin 5 → ℝ) (a + 1) →
      (![z5, z6, z4, z1, z2] : Fin 5 → ℝ) b < (![z5, z6, z4, z1, z2] : Fin 5 → ℝ) (b - 1) →
      (![z5, z6, z4, z1, z2] : Fin 5 → ℝ) b < (![z5, z6, z4, z1, z2] : Fin 5 → ℝ) (b + 1) → a = b) :
    IsRupert ({oblPt O r1 r2 t0 0 z0, oblPt O r1 r2 t1 0 z1, oblPt O r1 r2 s2 u2 z2, oblPt O r1 r2 0 0 z3, oblPt O r1 r2 0 0 z4, oblPt O r1 r2 0 t5 z5, oblPt O r1 r2 0 t6 z6} : Finset ℝ³) := by
  obtain ⟨⟨q1a, q1b⟩, ⟨q1c, q1d⟩, ⟨q1e, q1f⟩, ⟨q1g, q1h⟩⟩ := hQ1
  obtain ⟨⟨q2a, q2b⟩, ⟨q2c, q2d⟩, ⟨q2e, q2f⟩, ⟨q2g, q2h⟩⟩ := hQ2
  have key : ∀ {ap bp zp aq bq zq ay by' zy : ℝ}, TiltOK ap bp zp aq bq zq ay by' zy (1) (1) →
      TiltSign (oblPt O r1 r2 aq bq zq - oblPt O r1 r2 ap bp zp)
        (oblPt O r1 r2 ay by' zy - oblPt O r1 r2 ap bp zp) ez (oblPt 0 r1 r2 (1) (1) 0) :=
    fun h => tiltSign_obl O r1 r2 hρ (1) (1) h
  have hez : (ez : ℝ³) ≠ 0 := by
    intro h; have := congrArg (fun x : ℝ³ => x 2) h; simp [ez] at this
  set x : Fin 5 → ℝ³ := ![oblPt O r1 r2 0 t5 z5, oblPt O r1 r2 0 t6 z6, oblPt O r1 r2 0 0 z4, oblPt O r1 r2 t1 0 z1, oblPt O r1 r2 s2 u2 z2] with hx
  have hxV : ∀ i : Fin 5, x i ∈ ({oblPt O r1 r2 t0 0 z0, oblPt O r1 r2 t1 0 z1, oblPt O r1 r2 s2 u2 z2, oblPt O r1 r2 0 0 z3, oblPt O r1 r2 0 0 z4, oblPt O r1 r2 0 t5 z5, oblPt O r1 r2 0 t6 z6} : Finset ℝ³) := by
    intro i; fin_cases i <;> simp [hx]
  have hcyc : ∀ i j : Fin 5, j ≠ i → j ≠ i + 1 →
      TiltSign (x (i + 1) - x i) (x j - x i) ez (oblPt 0 r1 r2 (1) (1) 0) := by
    intro i j hji hji1
    fin_cases i <;> fin_cases j <;> simp [hx] at hji hji1 ⊢ <;> apply key
    all_goals first
      | (refine tiltOK_side1_off ?_ ?_ <;> linarith)
      | (refine tiltOK_side2_off ?_ ?_ <;> linarith)
      | (refine tiltOK_side1_on (Or.inl ⟨?_, ?_⟩) <;> linarith)
      | (refine tiltOK_side1_on (Or.inr ⟨?_, ?_⟩) <;> linarith)
      | (refine tiltOK_side2_on (Or.inl ⟨?_, ?_⟩) <;> linarith)
      | (refine tiltOK_side2_on (Or.inr ⟨?_, ?_⟩) <;> linarith)
      | (refine tiltOK_farA ht1 hu2 hch ?_
         first | (left; constructor <;> linarith) | (right; refine ⟨?_, ?_, ?_⟩ <;> linarith))
      | (refine tiltOK_farB ht5 hs2 hch ?_
         first | (left; constructor <;> linarith) | (right; refine ⟨?_, ?_, ?_⟩ <;> linarith))
  have hrest : ∀ y ∈ ({oblPt O r1 r2 t0 0 z0, oblPt O r1 r2 t1 0 z1, oblPt O r1 r2 s2 u2 z2, oblPt O r1 r2 0 0 z3, oblPt O r1 r2 0 0 z4, oblPt O r1 r2 0 t5 z5, oblPt O r1 r2 0 t6 z6} : Finset ℝ³), (∀ j : Fin 5, y ≠ x j) → ∀ i : Fin 5,
      TiltSign (x (i + 1) - x i) (y - x i) ez (oblPt 0 r1 r2 (1) (1) 0) := by
    intro y hy hyx i
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | (exfalso; apply hyx 0; simp [hx]; done)
      | (exfalso; apply hyx 1; simp [hx]; done)
      | (exfalso; apply hyx 2; simp [hx]; done)
      | (exfalso; apply hyx 3; simp [hx]; done)
      | (exfalso; apply hyx 4; simp [hx]; done)
      | (fin_cases i <;> simp [hx] <;> apply key <;> first
          | (refine tiltOK_side1_off ?_ ?_ <;> linarith)
          | (refine tiltOK_side2_off ?_ ?_ <;> linarith)
          | (refine tiltOK_side1_on (Or.inl ⟨?_, ?_⟩) <;> linarith)
          | (refine tiltOK_side1_on (Or.inr ⟨?_, ?_⟩) <;> linarith)
          | (refine tiltOK_side2_on (Or.inl ⟨?_, ?_⟩) <;> linarith)
          | (refine tiltOK_side2_on (Or.inr ⟨?_, ?_⟩) <;> linarith)
          | (refine tiltOK_farA ht1 hu2 hch ?_
             first | (left; constructor <;> linarith) | (right; refine ⟨?_, ?_, ?_⟩ <;> linarith))
          | (refine tiltOK_farB ht5 hs2 hch ?_
             first | (left; constructor <;> linarith) | (right; refine ⟨?_, ?_, ?_⟩ <;> linarith)))
  have hz : (fun i : Fin 5 => ⟪x i, ez⟫) = ![z5, z6, z4, z1, z2] := by
    funext i; fin_cases i <;> simp [hx, oblPt, inner_ez]
  have hu0 : IsCyclicUnimodal (k := 5) fun i => ⟪x i, ez⟫ := by
    have := isCyclicUnimodal_of_localMin_unique (k := 5) (by norm_num) ![z5, z6, z4, z1, z2] hinj hext
    rw [show (fun i : ZMod 5 => ⟪x i, ez⟫) = ![z5, z6, z4, z1, z2] from hz]; exact this
  exact isRupert_of_tilted_unimodal' _ ez (oblPt 0 r1 r2 (1) (1) 0) hez (k := 5) (by norm_num)
    x hxV hcyc hrest IsCyclicUnimodal isOpen_isCyclicUnimodal
    (fun z c hc hz => isCyclicUnimodal_smul hc hz)
    (eventually_unimodal_tilt (k := 5) x ez (oblPt 0 r1 r2 (1) (1) 0) hu0) (fun z _ h => h)

set_option maxHeartbeats 4000000 in
set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in
theorem rupert02_W_A0B5 (O r1 r2 : ℝ²) (hρ : 0 < cross2 r1 r2)
    {t0 t1 t5 t6 s2 u2 z0 z1 z2 z3 z4 z5 z6 : ℝ} (ht0 : 0 < t0) (ht1 : 0 < t1) (ht5 : 0 < t5)
    (ht6 : 0 < t6) (hs2 : 0 < s2) (hu2 : 0 < u2)
    (hQ1 : ConvQuad 0 z3 t0 z0 t1 z1 0 z4) (hQ2 : ConvQuad 0 z3 t5 z5 t6 z6 0 z4)
    (ht01 : t1 < t0) (ht56 : t6 < t5) (hch : t0 * t5 < s2 * t5 + u2 * t0)
    (hinj : Function.Injective (![z5, z6, z4, z1, z0, z2] : Fin 6 → ℝ))
    (hext : ∀ a b : Fin 6, (![z5, z6, z4, z1, z0, z2] : Fin 6 → ℝ) a < (![z5, z6, z4, z1, z0, z2] : Fin 6 → ℝ) (a - 1) →
      (![z5, z6, z4, z1, z0, z2] : Fin 6 → ℝ) a < (![z5, z6, z4, z1, z0, z2] : Fin 6 → ℝ) (a + 1) →
      (![z5, z6, z4, z1, z0, z2] : Fin 6 → ℝ) b < (![z5, z6, z4, z1, z0, z2] : Fin 6 → ℝ) (b - 1) →
      (![z5, z6, z4, z1, z0, z2] : Fin 6 → ℝ) b < (![z5, z6, z4, z1, z0, z2] : Fin 6 → ℝ) (b + 1) → a = b) :
    IsRupert ({oblPt O r1 r2 t0 0 z0, oblPt O r1 r2 t1 0 z1, oblPt O r1 r2 s2 u2 z2, oblPt O r1 r2 0 0 z3, oblPt O r1 r2 0 0 z4, oblPt O r1 r2 0 t5 z5, oblPt O r1 r2 0 t6 z6} : Finset ℝ³) := by
  obtain ⟨⟨q1a, q1b⟩, ⟨q1c, q1d⟩, ⟨q1e, q1f⟩, ⟨q1g, q1h⟩⟩ := hQ1
  obtain ⟨⟨q2a, q2b⟩, ⟨q2c, q2d⟩, ⟨q2e, q2f⟩, ⟨q2g, q2h⟩⟩ := hQ2
  have key : ∀ {ap bp zp aq bq zq ay by' zy : ℝ}, TiltOK ap bp zp aq bq zq ay by' zy (1) (1) →
      TiltSign (oblPt O r1 r2 aq bq zq - oblPt O r1 r2 ap bp zp)
        (oblPt O r1 r2 ay by' zy - oblPt O r1 r2 ap bp zp) ez (oblPt 0 r1 r2 (1) (1) 0) :=
    fun h => tiltSign_obl O r1 r2 hρ (1) (1) h
  have hez : (ez : ℝ³) ≠ 0 := by
    intro h; have := congrArg (fun x : ℝ³ => x 2) h; simp [ez] at this
  set x : Fin 6 → ℝ³ := ![oblPt O r1 r2 0 t5 z5, oblPt O r1 r2 0 t6 z6, oblPt O r1 r2 0 0 z4, oblPt O r1 r2 t1 0 z1, oblPt O r1 r2 t0 0 z0, oblPt O r1 r2 s2 u2 z2] with hx
  have hxV : ∀ i : Fin 6, x i ∈ ({oblPt O r1 r2 t0 0 z0, oblPt O r1 r2 t1 0 z1, oblPt O r1 r2 s2 u2 z2, oblPt O r1 r2 0 0 z3, oblPt O r1 r2 0 0 z4, oblPt O r1 r2 0 t5 z5, oblPt O r1 r2 0 t6 z6} : Finset ℝ³) := by
    intro i; fin_cases i <;> simp [hx]
  have hcyc : ∀ i j : Fin 6, j ≠ i → j ≠ i + 1 →
      TiltSign (x (i + 1) - x i) (x j - x i) ez (oblPt 0 r1 r2 (1) (1) 0) := by
    intro i j hji hji1
    fin_cases i <;> fin_cases j <;> simp [hx] at hji hji1 ⊢ <;> apply key
    all_goals first
      | (refine tiltOK_side1_off ?_ ?_ <;> linarith)
      | (refine tiltOK_side2_off ?_ ?_ <;> linarith)
      | (refine tiltOK_side1_on (Or.inl ⟨?_, ?_⟩) <;> linarith)
      | (refine tiltOK_side1_on (Or.inr ⟨?_, ?_⟩) <;> linarith)
      | (refine tiltOK_side2_on (Or.inl ⟨?_, ?_⟩) <;> linarith)
      | (refine tiltOK_side2_on (Or.inr ⟨?_, ?_⟩) <;> linarith)
      | (refine tiltOK_farA ht0 hu2 hch ?_
         first | (left; constructor <;> linarith) | (right; refine ⟨?_, ?_, ?_⟩ <;> linarith))
      | (refine tiltOK_farB ht5 hs2 hch ?_
         first | (left; constructor <;> linarith) | (right; refine ⟨?_, ?_, ?_⟩ <;> linarith))
  have hrest : ∀ y ∈ ({oblPt O r1 r2 t0 0 z0, oblPt O r1 r2 t1 0 z1, oblPt O r1 r2 s2 u2 z2, oblPt O r1 r2 0 0 z3, oblPt O r1 r2 0 0 z4, oblPt O r1 r2 0 t5 z5, oblPt O r1 r2 0 t6 z6} : Finset ℝ³), (∀ j : Fin 6, y ≠ x j) → ∀ i : Fin 6,
      TiltSign (x (i + 1) - x i) (y - x i) ez (oblPt 0 r1 r2 (1) (1) 0) := by
    intro y hy hyx i
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | (exfalso; apply hyx 0; simp [hx]; done)
      | (exfalso; apply hyx 1; simp [hx]; done)
      | (exfalso; apply hyx 2; simp [hx]; done)
      | (exfalso; apply hyx 3; simp [hx]; done)
      | (exfalso; apply hyx 4; simp [hx]; done)
      | (exfalso; apply hyx 5; simp [hx]; done)
      | (fin_cases i <;> simp [hx] <;> apply key <;> first
          | (refine tiltOK_side1_off ?_ ?_ <;> linarith)
          | (refine tiltOK_side2_off ?_ ?_ <;> linarith)
          | (refine tiltOK_side1_on (Or.inl ⟨?_, ?_⟩) <;> linarith)
          | (refine tiltOK_side1_on (Or.inr ⟨?_, ?_⟩) <;> linarith)
          | (refine tiltOK_side2_on (Or.inl ⟨?_, ?_⟩) <;> linarith)
          | (refine tiltOK_side2_on (Or.inr ⟨?_, ?_⟩) <;> linarith)
          | (refine tiltOK_farA ht0 hu2 hch ?_
             first | (left; constructor <;> linarith) | (right; refine ⟨?_, ?_, ?_⟩ <;> linarith))
          | (refine tiltOK_farB ht5 hs2 hch ?_
             first | (left; constructor <;> linarith) | (right; refine ⟨?_, ?_, ?_⟩ <;> linarith)))
  have hz : (fun i : Fin 6 => ⟪x i, ez⟫) = ![z5, z6, z4, z1, z0, z2] := by
    funext i; fin_cases i <;> simp [hx, oblPt, inner_ez]
  have hu0 : IsCyclicUnimodal (k := 6) fun i => ⟪x i, ez⟫ := by
    have := isCyclicUnimodal_of_localMin_unique (k := 6) (by norm_num) ![z5, z6, z4, z1, z0, z2] hinj hext
    rw [show (fun i : ZMod 6 => ⟪x i, ez⟫) = ![z5, z6, z4, z1, z0, z2] from hz]; exact this
  exact isRupert_of_tilted_unimodal' _ ez (oblPt 0 r1 r2 (1) (1) 0) hez (k := 6) (by norm_num)
    x hxV hcyc hrest IsCyclicUnimodal isOpen_isCyclicUnimodal
    (fun z c hc hz => isCyclicUnimodal_smul hc hz)
    (eventually_unimodal_tilt (k := 6) x ez (oblPt 0 r1 r2 (1) (1) 0) hu0) (fun z _ h => h)

set_option maxHeartbeats 4000000 in
set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in
theorem rupert02_M_A1B6 (O r1 r2 : ℝ²) (hρ : 0 < cross2 r1 r2)
    {t0 t1 t5 t6 s2 u2 z0 z1 z2 z3 z4 z5 z6 : ℝ} (ht0 : 0 < t0) (ht1 : 0 < t1) (ht5 : 0 < t5)
    (ht6 : 0 < t6) (hs2 : 0 < s2) (hu2 : 0 < u2)
    (hQ1 : ConvQuad 0 z3 t0 z0 t1 z1 0 z4) (hQ2 : ConvQuad 0 z3 t5 z5 t6 z6 0 z4)
    (ht01 : t0 < t1) (ht56 : t5 < t6) (hch : t1 * t6 < s2 * t6 + u2 * t1)
    (hinj : Function.Injective (![z6, z5, z3, z0, z1, z2] : Fin 6 → ℝ))
    (hext : ∀ a b : Fin 6, (![z6, z5, z3, z0, z1, z2] : Fin 6 → ℝ) (a - 1) < (![z6, z5, z3, z0, z1, z2] : Fin 6 → ℝ) a →
      (![z6, z5, z3, z0, z1, z2] : Fin 6 → ℝ) (a + 1) < (![z6, z5, z3, z0, z1, z2] : Fin 6 → ℝ) a →
      (![z6, z5, z3, z0, z1, z2] : Fin 6 → ℝ) (b - 1) < (![z6, z5, z3, z0, z1, z2] : Fin 6 → ℝ) b →
      (![z6, z5, z3, z0, z1, z2] : Fin 6 → ℝ) (b + 1) < (![z6, z5, z3, z0, z1, z2] : Fin 6 → ℝ) b → a = b) :
    IsRupert ({oblPt O r1 r2 t0 0 z0, oblPt O r1 r2 t1 0 z1, oblPt O r1 r2 s2 u2 z2, oblPt O r1 r2 0 0 z3, oblPt O r1 r2 0 0 z4, oblPt O r1 r2 0 t5 z5, oblPt O r1 r2 0 t6 z6} : Finset ℝ³) := by
  obtain ⟨⟨q1a, q1b⟩, ⟨q1c, q1d⟩, ⟨q1e, q1f⟩, ⟨q1g, q1h⟩⟩ := hQ1
  obtain ⟨⟨q2a, q2b⟩, ⟨q2c, q2d⟩, ⟨q2e, q2f⟩, ⟨q2g, q2h⟩⟩ := hQ2
  have key : ∀ {ap bp zp aq bq zq ay by' zy : ℝ}, TiltOK ap bp zp aq bq zq ay by' zy (-1) (-1) →
      TiltSign (oblPt O r1 r2 aq bq zq - oblPt O r1 r2 ap bp zp)
        (oblPt O r1 r2 ay by' zy - oblPt O r1 r2 ap bp zp) ez (oblPt 0 r1 r2 (-1) (-1) 0) :=
    fun h => tiltSign_obl O r1 r2 hρ (-1) (-1) h
  have hez : (ez : ℝ³) ≠ 0 := by
    intro h; have := congrArg (fun x : ℝ³ => x 2) h; simp [ez] at this
  set x : Fin 6 → ℝ³ := ![oblPt O r1 r2 0 t6 z6, oblPt O r1 r2 0 t5 z5, oblPt O r1 r2 0 0 z3, oblPt O r1 r2 t0 0 z0, oblPt O r1 r2 t1 0 z1, oblPt O r1 r2 s2 u2 z2] with hx
  have hxV : ∀ i : Fin 6, x i ∈ ({oblPt O r1 r2 t0 0 z0, oblPt O r1 r2 t1 0 z1, oblPt O r1 r2 s2 u2 z2, oblPt O r1 r2 0 0 z3, oblPt O r1 r2 0 0 z4, oblPt O r1 r2 0 t5 z5, oblPt O r1 r2 0 t6 z6} : Finset ℝ³) := by
    intro i; fin_cases i <;> simp [hx]
  have hcyc : ∀ i j : Fin 6, j ≠ i → j ≠ i + 1 →
      TiltSign (x (i + 1) - x i) (x j - x i) ez (oblPt 0 r1 r2 (-1) (-1) 0) := by
    intro i j hji hji1
    fin_cases i <;> fin_cases j <;> simp [hx] at hji hji1 ⊢ <;> apply key
    all_goals first
      | (refine tiltOK_side1_off ?_ ?_ <;> linarith)
      | (refine tiltOK_side2_off ?_ ?_ <;> linarith)
      | (refine tiltOK_side1_on (Or.inl ⟨?_, ?_⟩) <;> linarith)
      | (refine tiltOK_side1_on (Or.inr ⟨?_, ?_⟩) <;> linarith)
      | (refine tiltOK_side2_on (Or.inl ⟨?_, ?_⟩) <;> linarith)
      | (refine tiltOK_side2_on (Or.inr ⟨?_, ?_⟩) <;> linarith)
      | (refine tiltOK_farA ht1 hu2 hch ?_
         first | (left; constructor <;> linarith) | (right; refine ⟨?_, ?_, ?_⟩ <;> linarith))
      | (refine tiltOK_farB ht6 hs2 hch ?_
         first | (left; constructor <;> linarith) | (right; refine ⟨?_, ?_, ?_⟩ <;> linarith))
  have hrest : ∀ y ∈ ({oblPt O r1 r2 t0 0 z0, oblPt O r1 r2 t1 0 z1, oblPt O r1 r2 s2 u2 z2, oblPt O r1 r2 0 0 z3, oblPt O r1 r2 0 0 z4, oblPt O r1 r2 0 t5 z5, oblPt O r1 r2 0 t6 z6} : Finset ℝ³), (∀ j : Fin 6, y ≠ x j) → ∀ i : Fin 6,
      TiltSign (x (i + 1) - x i) (y - x i) ez (oblPt 0 r1 r2 (-1) (-1) 0) := by
    intro y hy hyx i
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | (exfalso; apply hyx 0; simp [hx]; done)
      | (exfalso; apply hyx 1; simp [hx]; done)
      | (exfalso; apply hyx 2; simp [hx]; done)
      | (exfalso; apply hyx 3; simp [hx]; done)
      | (exfalso; apply hyx 4; simp [hx]; done)
      | (exfalso; apply hyx 5; simp [hx]; done)
      | (fin_cases i <;> simp [hx] <;> apply key <;> first
          | (refine tiltOK_side1_off ?_ ?_ <;> linarith)
          | (refine tiltOK_side2_off ?_ ?_ <;> linarith)
          | (refine tiltOK_side1_on (Or.inl ⟨?_, ?_⟩) <;> linarith)
          | (refine tiltOK_side1_on (Or.inr ⟨?_, ?_⟩) <;> linarith)
          | (refine tiltOK_side2_on (Or.inl ⟨?_, ?_⟩) <;> linarith)
          | (refine tiltOK_side2_on (Or.inr ⟨?_, ?_⟩) <;> linarith)
          | (refine tiltOK_farA ht1 hu2 hch ?_
             first | (left; constructor <;> linarith) | (right; refine ⟨?_, ?_, ?_⟩ <;> linarith))
          | (refine tiltOK_farB ht6 hs2 hch ?_
             first | (left; constructor <;> linarith) | (right; refine ⟨?_, ?_, ?_⟩ <;> linarith)))
  have hz : (fun i : Fin 6 => ⟪x i, ez⟫) = ![z6, z5, z3, z0, z1, z2] := by
    funext i; fin_cases i <;> simp [hx, oblPt, inner_ez]
  have hu0 : IsCyclicUnimodal (k := 6) fun i => ⟪x i, ez⟫ := by
    have := isCyclicUnimodal_of_localMax_unique (k := 6) (by norm_num) ![z6, z5, z3, z0, z1, z2] hinj hext
    rw [show (fun i : ZMod 6 => ⟪x i, ez⟫) = ![z6, z5, z3, z0, z1, z2] from hz]; exact this
  exact isRupert_of_tilted_unimodal' _ ez (oblPt 0 r1 r2 (-1) (-1) 0) hez (k := 6) (by norm_num)
    x hxV hcyc hrest IsCyclicUnimodal isOpen_isCyclicUnimodal
    (fun z c hc hz => isCyclicUnimodal_smul hc hz)
    (eventually_unimodal_tilt (k := 6) x ez (oblPt 0 r1 r2 (-1) (-1) 0) hu0) (fun z _ h => h)

set_option maxHeartbeats 4000000 in
set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in
theorem rupert02_M_A0B6 (O r1 r2 : ℝ²) (hρ : 0 < cross2 r1 r2)
    {t0 t1 t5 t6 s2 u2 z0 z1 z2 z3 z4 z5 z6 : ℝ} (ht0 : 0 < t0) (ht1 : 0 < t1) (ht5 : 0 < t5)
    (ht6 : 0 < t6) (hs2 : 0 < s2) (hu2 : 0 < u2)
    (hQ1 : ConvQuad 0 z3 t0 z0 t1 z1 0 z4) (hQ2 : ConvQuad 0 z3 t5 z5 t6 z6 0 z4)
    (ht01 : t1 < t0) (ht56 : t5 < t6) (hch : t0 * t6 < s2 * t6 + u2 * t0)
    (hinj : Function.Injective (![z6, z5, z3, z0, z2] : Fin 5 → ℝ))
    (hext : ∀ a b : Fin 5, (![z6, z5, z3, z0, z2] : Fin 5 → ℝ) (a - 1) < (![z6, z5, z3, z0, z2] : Fin 5 → ℝ) a →
      (![z6, z5, z3, z0, z2] : Fin 5 → ℝ) (a + 1) < (![z6, z5, z3, z0, z2] : Fin 5 → ℝ) a →
      (![z6, z5, z3, z0, z2] : Fin 5 → ℝ) (b - 1) < (![z6, z5, z3, z0, z2] : Fin 5 → ℝ) b →
      (![z6, z5, z3, z0, z2] : Fin 5 → ℝ) (b + 1) < (![z6, z5, z3, z0, z2] : Fin 5 → ℝ) b → a = b) :
    IsRupert ({oblPt O r1 r2 t0 0 z0, oblPt O r1 r2 t1 0 z1, oblPt O r1 r2 s2 u2 z2, oblPt O r1 r2 0 0 z3, oblPt O r1 r2 0 0 z4, oblPt O r1 r2 0 t5 z5, oblPt O r1 r2 0 t6 z6} : Finset ℝ³) := by
  obtain ⟨⟨q1a, q1b⟩, ⟨q1c, q1d⟩, ⟨q1e, q1f⟩, ⟨q1g, q1h⟩⟩ := hQ1
  obtain ⟨⟨q2a, q2b⟩, ⟨q2c, q2d⟩, ⟨q2e, q2f⟩, ⟨q2g, q2h⟩⟩ := hQ2
  have key : ∀ {ap bp zp aq bq zq ay by' zy : ℝ}, TiltOK ap bp zp aq bq zq ay by' zy (-1) (-1) →
      TiltSign (oblPt O r1 r2 aq bq zq - oblPt O r1 r2 ap bp zp)
        (oblPt O r1 r2 ay by' zy - oblPt O r1 r2 ap bp zp) ez (oblPt 0 r1 r2 (-1) (-1) 0) :=
    fun h => tiltSign_obl O r1 r2 hρ (-1) (-1) h
  have hez : (ez : ℝ³) ≠ 0 := by
    intro h; have := congrArg (fun x : ℝ³ => x 2) h; simp [ez] at this
  set x : Fin 5 → ℝ³ := ![oblPt O r1 r2 0 t6 z6, oblPt O r1 r2 0 t5 z5, oblPt O r1 r2 0 0 z3, oblPt O r1 r2 t0 0 z0, oblPt O r1 r2 s2 u2 z2] with hx
  have hxV : ∀ i : Fin 5, x i ∈ ({oblPt O r1 r2 t0 0 z0, oblPt O r1 r2 t1 0 z1, oblPt O r1 r2 s2 u2 z2, oblPt O r1 r2 0 0 z3, oblPt O r1 r2 0 0 z4, oblPt O r1 r2 0 t5 z5, oblPt O r1 r2 0 t6 z6} : Finset ℝ³) := by
    intro i; fin_cases i <;> simp [hx]
  have hcyc : ∀ i j : Fin 5, j ≠ i → j ≠ i + 1 →
      TiltSign (x (i + 1) - x i) (x j - x i) ez (oblPt 0 r1 r2 (-1) (-1) 0) := by
    intro i j hji hji1
    fin_cases i <;> fin_cases j <;> simp [hx] at hji hji1 ⊢ <;> apply key
    all_goals first
      | (refine tiltOK_side1_off ?_ ?_ <;> linarith)
      | (refine tiltOK_side2_off ?_ ?_ <;> linarith)
      | (refine tiltOK_side1_on (Or.inl ⟨?_, ?_⟩) <;> linarith)
      | (refine tiltOK_side1_on (Or.inr ⟨?_, ?_⟩) <;> linarith)
      | (refine tiltOK_side2_on (Or.inl ⟨?_, ?_⟩) <;> linarith)
      | (refine tiltOK_side2_on (Or.inr ⟨?_, ?_⟩) <;> linarith)
      | (refine tiltOK_farA ht0 hu2 hch ?_
         first | (left; constructor <;> linarith) | (right; refine ⟨?_, ?_, ?_⟩ <;> linarith))
      | (refine tiltOK_farB ht6 hs2 hch ?_
         first | (left; constructor <;> linarith) | (right; refine ⟨?_, ?_, ?_⟩ <;> linarith))
  have hrest : ∀ y ∈ ({oblPt O r1 r2 t0 0 z0, oblPt O r1 r2 t1 0 z1, oblPt O r1 r2 s2 u2 z2, oblPt O r1 r2 0 0 z3, oblPt O r1 r2 0 0 z4, oblPt O r1 r2 0 t5 z5, oblPt O r1 r2 0 t6 z6} : Finset ℝ³), (∀ j : Fin 5, y ≠ x j) → ∀ i : Fin 5,
      TiltSign (x (i + 1) - x i) (y - x i) ez (oblPt 0 r1 r2 (-1) (-1) 0) := by
    intro y hy hyx i
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | (exfalso; apply hyx 0; simp [hx]; done)
      | (exfalso; apply hyx 1; simp [hx]; done)
      | (exfalso; apply hyx 2; simp [hx]; done)
      | (exfalso; apply hyx 3; simp [hx]; done)
      | (exfalso; apply hyx 4; simp [hx]; done)
      | (fin_cases i <;> simp [hx] <;> apply key <;> first
          | (refine tiltOK_side1_off ?_ ?_ <;> linarith)
          | (refine tiltOK_side2_off ?_ ?_ <;> linarith)
          | (refine tiltOK_side1_on (Or.inl ⟨?_, ?_⟩) <;> linarith)
          | (refine tiltOK_side1_on (Or.inr ⟨?_, ?_⟩) <;> linarith)
          | (refine tiltOK_side2_on (Or.inl ⟨?_, ?_⟩) <;> linarith)
          | (refine tiltOK_side2_on (Or.inr ⟨?_, ?_⟩) <;> linarith)
          | (refine tiltOK_farA ht0 hu2 hch ?_
             first | (left; constructor <;> linarith) | (right; refine ⟨?_, ?_, ?_⟩ <;> linarith))
          | (refine tiltOK_farB ht6 hs2 hch ?_
             first | (left; constructor <;> linarith) | (right; refine ⟨?_, ?_, ?_⟩ <;> linarith)))
  have hz : (fun i : Fin 5 => ⟪x i, ez⟫) = ![z6, z5, z3, z0, z2] := by
    funext i; fin_cases i <;> simp [hx, oblPt, inner_ez]
  have hu0 : IsCyclicUnimodal (k := 5) fun i => ⟪x i, ez⟫ := by
    have := isCyclicUnimodal_of_localMax_unique (k := 5) (by norm_num) ![z6, z5, z3, z0, z2] hinj hext
    rw [show (fun i : ZMod 5 => ⟪x i, ez⟫) = ![z6, z5, z3, z0, z2] from hz]; exact this
  exact isRupert_of_tilted_unimodal' _ ez (oblPt 0 r1 r2 (-1) (-1) 0) hez (k := 5) (by norm_num)
    x hxV hcyc hrest IsCyclicUnimodal isOpen_isCyclicUnimodal
    (fun z c hc hz => isCyclicUnimodal_smul hc hz)
    (eventually_unimodal_tilt (k := 5) x ez (oblPt 0 r1 r2 (-1) (-1) 0) hu0) (fun z _ h => h)

set_option maxHeartbeats 4000000 in
set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in
theorem rupert02_M_A1B5 (O r1 r2 : ℝ²) (hρ : 0 < cross2 r1 r2)
    {t0 t1 t5 t6 s2 u2 z0 z1 z2 z3 z4 z5 z6 : ℝ} (ht0 : 0 < t0) (ht1 : 0 < t1) (ht5 : 0 < t5)
    (ht6 : 0 < t6) (hs2 : 0 < s2) (hu2 : 0 < u2)
    (hQ1 : ConvQuad 0 z3 t0 z0 t1 z1 0 z4) (hQ2 : ConvQuad 0 z3 t5 z5 t6 z6 0 z4)
    (ht01 : t0 < t1) (ht56 : t6 < t5) (hch : t1 * t5 < s2 * t5 + u2 * t1)
    (hinj : Function.Injective (![z5, z3, z0, z1, z2] : Fin 5 → ℝ))
    (hext : ∀ a b : Fin 5, (![z5, z3, z0, z1, z2] : Fin 5 → ℝ) (a - 1) < (![z5, z3, z0, z1, z2] : Fin 5 → ℝ) a →
      (![z5, z3, z0, z1, z2] : Fin 5 → ℝ) (a + 1) < (![z5, z3, z0, z1, z2] : Fin 5 → ℝ) a →
      (![z5, z3, z0, z1, z2] : Fin 5 → ℝ) (b - 1) < (![z5, z3, z0, z1, z2] : Fin 5 → ℝ) b →
      (![z5, z3, z0, z1, z2] : Fin 5 → ℝ) (b + 1) < (![z5, z3, z0, z1, z2] : Fin 5 → ℝ) b → a = b) :
    IsRupert ({oblPt O r1 r2 t0 0 z0, oblPt O r1 r2 t1 0 z1, oblPt O r1 r2 s2 u2 z2, oblPt O r1 r2 0 0 z3, oblPt O r1 r2 0 0 z4, oblPt O r1 r2 0 t5 z5, oblPt O r1 r2 0 t6 z6} : Finset ℝ³) := by
  obtain ⟨⟨q1a, q1b⟩, ⟨q1c, q1d⟩, ⟨q1e, q1f⟩, ⟨q1g, q1h⟩⟩ := hQ1
  obtain ⟨⟨q2a, q2b⟩, ⟨q2c, q2d⟩, ⟨q2e, q2f⟩, ⟨q2g, q2h⟩⟩ := hQ2
  have key : ∀ {ap bp zp aq bq zq ay by' zy : ℝ}, TiltOK ap bp zp aq bq zq ay by' zy (-1) (-1) →
      TiltSign (oblPt O r1 r2 aq bq zq - oblPt O r1 r2 ap bp zp)
        (oblPt O r1 r2 ay by' zy - oblPt O r1 r2 ap bp zp) ez (oblPt 0 r1 r2 (-1) (-1) 0) :=
    fun h => tiltSign_obl O r1 r2 hρ (-1) (-1) h
  have hez : (ez : ℝ³) ≠ 0 := by
    intro h; have := congrArg (fun x : ℝ³ => x 2) h; simp [ez] at this
  set x : Fin 5 → ℝ³ := ![oblPt O r1 r2 0 t5 z5, oblPt O r1 r2 0 0 z3, oblPt O r1 r2 t0 0 z0, oblPt O r1 r2 t1 0 z1, oblPt O r1 r2 s2 u2 z2] with hx
  have hxV : ∀ i : Fin 5, x i ∈ ({oblPt O r1 r2 t0 0 z0, oblPt O r1 r2 t1 0 z1, oblPt O r1 r2 s2 u2 z2, oblPt O r1 r2 0 0 z3, oblPt O r1 r2 0 0 z4, oblPt O r1 r2 0 t5 z5, oblPt O r1 r2 0 t6 z6} : Finset ℝ³) := by
    intro i; fin_cases i <;> simp [hx]
  have hcyc : ∀ i j : Fin 5, j ≠ i → j ≠ i + 1 →
      TiltSign (x (i + 1) - x i) (x j - x i) ez (oblPt 0 r1 r2 (-1) (-1) 0) := by
    intro i j hji hji1
    fin_cases i <;> fin_cases j <;> simp [hx] at hji hji1 ⊢ <;> apply key
    all_goals first
      | (refine tiltOK_side1_off ?_ ?_ <;> linarith)
      | (refine tiltOK_side2_off ?_ ?_ <;> linarith)
      | (refine tiltOK_side1_on (Or.inl ⟨?_, ?_⟩) <;> linarith)
      | (refine tiltOK_side1_on (Or.inr ⟨?_, ?_⟩) <;> linarith)
      | (refine tiltOK_side2_on (Or.inl ⟨?_, ?_⟩) <;> linarith)
      | (refine tiltOK_side2_on (Or.inr ⟨?_, ?_⟩) <;> linarith)
      | (refine tiltOK_farA ht1 hu2 hch ?_
         first | (left; constructor <;> linarith) | (right; refine ⟨?_, ?_, ?_⟩ <;> linarith))
      | (refine tiltOK_farB ht5 hs2 hch ?_
         first | (left; constructor <;> linarith) | (right; refine ⟨?_, ?_, ?_⟩ <;> linarith))
  have hrest : ∀ y ∈ ({oblPt O r1 r2 t0 0 z0, oblPt O r1 r2 t1 0 z1, oblPt O r1 r2 s2 u2 z2, oblPt O r1 r2 0 0 z3, oblPt O r1 r2 0 0 z4, oblPt O r1 r2 0 t5 z5, oblPt O r1 r2 0 t6 z6} : Finset ℝ³), (∀ j : Fin 5, y ≠ x j) → ∀ i : Fin 5,
      TiltSign (x (i + 1) - x i) (y - x i) ez (oblPt 0 r1 r2 (-1) (-1) 0) := by
    intro y hy hyx i
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | (exfalso; apply hyx 0; simp [hx]; done)
      | (exfalso; apply hyx 1; simp [hx]; done)
      | (exfalso; apply hyx 2; simp [hx]; done)
      | (exfalso; apply hyx 3; simp [hx]; done)
      | (exfalso; apply hyx 4; simp [hx]; done)
      | (fin_cases i <;> simp [hx] <;> apply key <;> first
          | (refine tiltOK_side1_off ?_ ?_ <;> linarith)
          | (refine tiltOK_side2_off ?_ ?_ <;> linarith)
          | (refine tiltOK_side1_on (Or.inl ⟨?_, ?_⟩) <;> linarith)
          | (refine tiltOK_side1_on (Or.inr ⟨?_, ?_⟩) <;> linarith)
          | (refine tiltOK_side2_on (Or.inl ⟨?_, ?_⟩) <;> linarith)
          | (refine tiltOK_side2_on (Or.inr ⟨?_, ?_⟩) <;> linarith)
          | (refine tiltOK_farA ht1 hu2 hch ?_
             first | (left; constructor <;> linarith) | (right; refine ⟨?_, ?_, ?_⟩ <;> linarith))
          | (refine tiltOK_farB ht5 hs2 hch ?_
             first | (left; constructor <;> linarith) | (right; refine ⟨?_, ?_, ?_⟩ <;> linarith)))
  have hz : (fun i : Fin 5 => ⟪x i, ez⟫) = ![z5, z3, z0, z1, z2] := by
    funext i; fin_cases i <;> simp [hx, oblPt, inner_ez]
  have hu0 : IsCyclicUnimodal (k := 5) fun i => ⟪x i, ez⟫ := by
    have := isCyclicUnimodal_of_localMax_unique (k := 5) (by norm_num) ![z5, z3, z0, z1, z2] hinj hext
    rw [show (fun i : ZMod 5 => ⟪x i, ez⟫) = ![z5, z3, z0, z1, z2] from hz]; exact this
  exact isRupert_of_tilted_unimodal' _ ez (oblPt 0 r1 r2 (-1) (-1) 0) hez (k := 5) (by norm_num)
    x hxV hcyc hrest IsCyclicUnimodal isOpen_isCyclicUnimodal
    (fun z c hc hz => isCyclicUnimodal_smul hc hz)
    (eventually_unimodal_tilt (k := 5) x ez (oblPt 0 r1 r2 (-1) (-1) 0) hu0) (fun z _ h => h)

set_option maxHeartbeats 4000000 in
set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in
theorem rupert02_M_A0B5 (O r1 r2 : ℝ²) (hρ : 0 < cross2 r1 r2)
    {t0 t1 t5 t6 s2 u2 z0 z1 z2 z3 z4 z5 z6 : ℝ} (ht0 : 0 < t0) (ht1 : 0 < t1) (ht5 : 0 < t5)
    (ht6 : 0 < t6) (hs2 : 0 < s2) (hu2 : 0 < u2)
    (hQ1 : ConvQuad 0 z3 t0 z0 t1 z1 0 z4) (hQ2 : ConvQuad 0 z3 t5 z5 t6 z6 0 z4)
    (ht01 : t1 < t0) (ht56 : t6 < t5) (hch : t0 * t5 < s2 * t5 + u2 * t0)
    (hinj : Function.Injective (![z5, z3, z0, z2] : Fin 4 → ℝ))
    (hext : ∀ a b : Fin 4, (![z5, z3, z0, z2] : Fin 4 → ℝ) (a - 1) < (![z5, z3, z0, z2] : Fin 4 → ℝ) a →
      (![z5, z3, z0, z2] : Fin 4 → ℝ) (a + 1) < (![z5, z3, z0, z2] : Fin 4 → ℝ) a →
      (![z5, z3, z0, z2] : Fin 4 → ℝ) (b - 1) < (![z5, z3, z0, z2] : Fin 4 → ℝ) b →
      (![z5, z3, z0, z2] : Fin 4 → ℝ) (b + 1) < (![z5, z3, z0, z2] : Fin 4 → ℝ) b → a = b) :
    IsRupert ({oblPt O r1 r2 t0 0 z0, oblPt O r1 r2 t1 0 z1, oblPt O r1 r2 s2 u2 z2, oblPt O r1 r2 0 0 z3, oblPt O r1 r2 0 0 z4, oblPt O r1 r2 0 t5 z5, oblPt O r1 r2 0 t6 z6} : Finset ℝ³) := by
  obtain ⟨⟨q1a, q1b⟩, ⟨q1c, q1d⟩, ⟨q1e, q1f⟩, ⟨q1g, q1h⟩⟩ := hQ1
  obtain ⟨⟨q2a, q2b⟩, ⟨q2c, q2d⟩, ⟨q2e, q2f⟩, ⟨q2g, q2h⟩⟩ := hQ2
  have key : ∀ {ap bp zp aq bq zq ay by' zy : ℝ}, TiltOK ap bp zp aq bq zq ay by' zy (-1) (-1) →
      TiltSign (oblPt O r1 r2 aq bq zq - oblPt O r1 r2 ap bp zp)
        (oblPt O r1 r2 ay by' zy - oblPt O r1 r2 ap bp zp) ez (oblPt 0 r1 r2 (-1) (-1) 0) :=
    fun h => tiltSign_obl O r1 r2 hρ (-1) (-1) h
  have hez : (ez : ℝ³) ≠ 0 := by
    intro h; have := congrArg (fun x : ℝ³ => x 2) h; simp [ez] at this
  set x : Fin 4 → ℝ³ := ![oblPt O r1 r2 0 t5 z5, oblPt O r1 r2 0 0 z3, oblPt O r1 r2 t0 0 z0, oblPt O r1 r2 s2 u2 z2] with hx
  have hxV : ∀ i : Fin 4, x i ∈ ({oblPt O r1 r2 t0 0 z0, oblPt O r1 r2 t1 0 z1, oblPt O r1 r2 s2 u2 z2, oblPt O r1 r2 0 0 z3, oblPt O r1 r2 0 0 z4, oblPt O r1 r2 0 t5 z5, oblPt O r1 r2 0 t6 z6} : Finset ℝ³) := by
    intro i; fin_cases i <;> simp [hx]
  have hcyc : ∀ i j : Fin 4, j ≠ i → j ≠ i + 1 →
      TiltSign (x (i + 1) - x i) (x j - x i) ez (oblPt 0 r1 r2 (-1) (-1) 0) := by
    intro i j hji hji1
    fin_cases i <;> fin_cases j <;> simp [hx] at hji hji1 ⊢ <;> apply key
    all_goals first
      | (refine tiltOK_side1_off ?_ ?_ <;> linarith)
      | (refine tiltOK_side2_off ?_ ?_ <;> linarith)
      | (refine tiltOK_side1_on (Or.inl ⟨?_, ?_⟩) <;> linarith)
      | (refine tiltOK_side1_on (Or.inr ⟨?_, ?_⟩) <;> linarith)
      | (refine tiltOK_side2_on (Or.inl ⟨?_, ?_⟩) <;> linarith)
      | (refine tiltOK_side2_on (Or.inr ⟨?_, ?_⟩) <;> linarith)
      | (refine tiltOK_farA ht0 hu2 hch ?_
         first | (left; constructor <;> linarith) | (right; refine ⟨?_, ?_, ?_⟩ <;> linarith))
      | (refine tiltOK_farB ht5 hs2 hch ?_
         first | (left; constructor <;> linarith) | (right; refine ⟨?_, ?_, ?_⟩ <;> linarith))
  have hrest : ∀ y ∈ ({oblPt O r1 r2 t0 0 z0, oblPt O r1 r2 t1 0 z1, oblPt O r1 r2 s2 u2 z2, oblPt O r1 r2 0 0 z3, oblPt O r1 r2 0 0 z4, oblPt O r1 r2 0 t5 z5, oblPt O r1 r2 0 t6 z6} : Finset ℝ³), (∀ j : Fin 4, y ≠ x j) → ∀ i : Fin 4,
      TiltSign (x (i + 1) - x i) (y - x i) ez (oblPt 0 r1 r2 (-1) (-1) 0) := by
    intro y hy hyx i
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | (exfalso; apply hyx 0; simp [hx]; done)
      | (exfalso; apply hyx 1; simp [hx]; done)
      | (exfalso; apply hyx 2; simp [hx]; done)
      | (exfalso; apply hyx 3; simp [hx]; done)
      | (fin_cases i <;> simp [hx] <;> apply key <;> first
          | (refine tiltOK_side1_off ?_ ?_ <;> linarith)
          | (refine tiltOK_side2_off ?_ ?_ <;> linarith)
          | (refine tiltOK_side1_on (Or.inl ⟨?_, ?_⟩) <;> linarith)
          | (refine tiltOK_side1_on (Or.inr ⟨?_, ?_⟩) <;> linarith)
          | (refine tiltOK_side2_on (Or.inl ⟨?_, ?_⟩) <;> linarith)
          | (refine tiltOK_side2_on (Or.inr ⟨?_, ?_⟩) <;> linarith)
          | (refine tiltOK_farA ht0 hu2 hch ?_
             first | (left; constructor <;> linarith) | (right; refine ⟨?_, ?_, ?_⟩ <;> linarith))
          | (refine tiltOK_farB ht5 hs2 hch ?_
             first | (left; constructor <;> linarith) | (right; refine ⟨?_, ?_, ?_⟩ <;> linarith)))
  have hz : (fun i : Fin 4 => ⟪x i, ez⟫) = ![z5, z3, z0, z2] := by
    funext i; fin_cases i <;> simp [hx, oblPt, inner_ez]
  have hu0 : IsCyclicUnimodal (k := 4) fun i => ⟪x i, ez⟫ := by
    have := isCyclicUnimodal_of_localMax_unique (k := 4) (by norm_num) ![z5, z3, z0, z2] hinj hext
    rw [show (fun i : ZMod 4 => ⟪x i, ez⟫) = ![z5, z3, z0, z2] from hz]; exact this
  exact isRupert_of_tilted_unimodal' _ ez (oblPt 0 r1 r2 (-1) (-1) 0) hez (k := 4) (by norm_num)
    x hxV hcyc hrest IsCyclicUnimodal isOpen_isCyclicUnimodal
    (fun z c hc hz => isCyclicUnimodal_smul hc hz)
    (eventually_unimodal_tilt (k := 4) x ez (oblPt 0 r1 r2 (-1) (-1) 0) hu0) (fun z _ h => h)

/-- **Theorem B, frame form** (FEWER-FACES-PROOFS.md §4, under (G) and (Z)):
seven points in the frame of the edge 34 (vertical, `z3 < z4`), with the quads
0134 and 3456 convex in their planes, the planes of 0235 and 1246 through 2
((Q3), (Q4)), 2 beyond the chord of the far vertices, the edges 01 and 56 not
parallel to 34, and distinct depths, are Rupert. -/
theorem isRupert_type02_frame (O r1 r2 : ℝ²) (hρ : 0 < cross2 r1 r2)
    {t0 t1 t5 t6 s2 u2 z0 z1 z2 z3 z4 z5 z6 : ℝ} (ht0 : 0 < t0) (ht1 : 0 < t1) (ht5 : 0 < t5)
    (ht6 : 0 < t6) (hs2 : 0 < s2) (hu2 : 0 < u2) (h34 : z3 < z4)
    (hQ1 : ConvQuad 0 z3 t0 z0 t1 z1 0 z4) (hQ2 : ConvQuad 0 z3 t5 z5 t6 z6 0 z4)
    (hQ3 : t0 * t5 * (z2 - z3) = s2 * t5 * (z0 - z3) + u2 * t0 * (z5 - z3))
    (hQ4 : t1 * t6 * (z2 - z4) = s2 * t6 * (z1 - z4) + u2 * t1 * (z6 - z4))
    (ht01 : t0 ≠ t1) (ht56 : t5 ≠ t6)
    (hch : max t0 t1 * max t5 t6 < s2 * max t5 t6 + u2 * max t0 t1)
    (hzinj : Function.Injective (![z0, z1, z2, z3, z4, z5, z6] : Fin 7 → ℝ)) :
    IsRupert ({oblPt O r1 r2 t0 0 z0, oblPt O r1 r2 t1 0 z1, oblPt O r1 r2 s2 u2 z2, oblPt O r1 r2 0 0 z3, oblPt O r1 r2 0 0 z4, oblPt O r1 r2 0 t5 z5, oblPt O r1 r2 0 t6 z6} : Finset ℝ³) := by
  have q1 := hQ1
  have q2 := hQ2
  obtain ⟨⟨q1a, q1b⟩, ⟨q1c, q1d⟩, ⟨q1e, q1f⟩, ⟨q1g, q1h⟩⟩ := q1
  obtain ⟨⟨q2a, q2b⟩, ⟨q2c, q2d⟩, ⟨q2e, q2f⟩, ⟨q2g, q2h⟩⟩ := q2
  rcases lt_or_gt_of_ne ht01 with h01 | h01 <;> rcases lt_or_gt_of_ne ht56 with h56 | h56
  · rw [max_eq_right h01.le, max_eq_right h56.le] at hch
    rcases cycles02_A1B6 h34 ht0 ht1 ht5 ht6 hs2 hu2 hQ3 hQ4 h01 h56 (by linarith) (by linarith)
        hch with hW | hM
    · exact rupert02_W_A1B6 O r1 r2 hρ ht0 ht1 ht5 ht6 hs2 hu2 hQ1 hQ2 h01 h56 hch
        (by
          have e : (![z6, z4, z1, z2] : Fin 4 → ℝ) = (![z0, z1, z2, z3, z4, z5, z6] : Fin 7 → ℝ) ∘
              (![6, 4, 1, 2] : Fin 4 → Fin 7) := by funext i; fin_cases i <;> rfl
          rw [e]; exact hzinj.comp (by decide)) hW
    · exact rupert02_M_A1B6 O r1 r2 hρ ht0 ht1 ht5 ht6 hs2 hu2 hQ1 hQ2 h01 h56 hch
        (by
          have e : (![z6, z5, z3, z0, z1, z2] : Fin 6 → ℝ) = (![z0, z1, z2, z3, z4, z5, z6] : Fin 7 → ℝ) ∘
              (![6, 5, 3, 0, 1, 2] : Fin 6 → Fin 7) := by funext i; fin_cases i <;> rfl
          rw [e]; exact hzinj.comp (by decide)) hM
  · rw [max_eq_right h01.le, max_eq_left h56.le] at hch
    rcases cycles02_A1B5 h34 ht0 ht1 ht5 ht6 hs2 hu2 hQ3 hQ4 h01 h56 (by linarith) (by linarith)
        hch with hW | hM
    · exact rupert02_W_A1B5 O r1 r2 hρ ht0 ht1 ht5 ht6 hs2 hu2 hQ1 hQ2 h01 h56 hch
        (by
          have e : (![z5, z6, z4, z1, z2] : Fin 5 → ℝ) = (![z0, z1, z2, z3, z4, z5, z6] : Fin 7 → ℝ) ∘
              (![5, 6, 4, 1, 2] : Fin 5 → Fin 7) := by funext i; fin_cases i <;> rfl
          rw [e]; exact hzinj.comp (by decide)) hW
    · exact rupert02_M_A1B5 O r1 r2 hρ ht0 ht1 ht5 ht6 hs2 hu2 hQ1 hQ2 h01 h56 hch
        (by
          have e : (![z5, z3, z0, z1, z2] : Fin 5 → ℝ) = (![z0, z1, z2, z3, z4, z5, z6] : Fin 7 → ℝ) ∘
              (![5, 3, 0, 1, 2] : Fin 5 → Fin 7) := by funext i; fin_cases i <;> rfl
          rw [e]; exact hzinj.comp (by decide)) hM
  · rw [max_eq_left h01.le, max_eq_right h56.le] at hch
    rcases cycles02_A0B6 h34 ht0 ht1 ht5 ht6 hs2 hu2 hQ3 hQ4 h01 h56 (by linarith) (by linarith)
        hch with hW | hM
    · exact rupert02_W_A0B6 O r1 r2 hρ ht0 ht1 ht5 ht6 hs2 hu2 hQ1 hQ2 h01 h56 hch
        (by
          have e : (![z6, z4, z1, z0, z2] : Fin 5 → ℝ) = (![z0, z1, z2, z3, z4, z5, z6] : Fin 7 → ℝ) ∘
              (![6, 4, 1, 0, 2] : Fin 5 → Fin 7) := by funext i; fin_cases i <;> rfl
          rw [e]; exact hzinj.comp (by decide)) hW
    · exact rupert02_M_A0B6 O r1 r2 hρ ht0 ht1 ht5 ht6 hs2 hu2 hQ1 hQ2 h01 h56 hch
        (by
          have e : (![z6, z5, z3, z0, z2] : Fin 5 → ℝ) = (![z0, z1, z2, z3, z4, z5, z6] : Fin 7 → ℝ) ∘
              (![6, 5, 3, 0, 2] : Fin 5 → Fin 7) := by funext i; fin_cases i <;> rfl
          rw [e]; exact hzinj.comp (by decide)) hM
  · rw [max_eq_left h01.le, max_eq_left h56.le] at hch
    rcases cycles02_A0B5 h34 ht0 ht1 ht5 ht6 hs2 hu2 hQ3 hQ4 h01 h56 (by linarith) (by linarith)
        hch with hW | hM
    · exact rupert02_W_A0B5 O r1 r2 hρ ht0 ht1 ht5 ht6 hs2 hu2 hQ1 hQ2 h01 h56 hch
        (by
          have e : (![z5, z6, z4, z1, z0, z2] : Fin 6 → ℝ) = (![z0, z1, z2, z3, z4, z5, z6] : Fin 7 → ℝ) ∘
              (![5, 6, 4, 1, 0, 2] : Fin 6 → Fin 7) := by funext i; fin_cases i <;> rfl
          rw [e]; exact hzinj.comp (by decide)) hW
    · exact rupert02_M_A0B5 O r1 r2 hρ ht0 ht1 ht5 ht6 hs2 hu2 hQ1 hQ2 h01 h56 hch
        (by
          have e : (![z5, z3, z0, z2] : Fin 4 → ℝ) = (![z0, z1, z2, z3, z4, z5, z6] : Fin 7 → ℝ) ∘
              (![5, 3, 0, 2] : Fin 4 → Fin 7) := by funext i; fin_cases i <;> rfl
          rw [e]; exact hzinj.comp (by decide)) hM

end Minimality
