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

/-! ### From the facets to the frame

An affine function in oblique coordinates is `K + α a + β b + γ z`. -/

theorem affine_obl (f : ℝ³ →ᵃ[ℝ] ℝ) (O r1 r2 : ℝ²) :
    ∃ K α β γ : ℝ, ∀ a b z : ℝ, f (oblPt O r1 r2 a b z) = K + α * a + β * b + γ * z := by
  set N : ℝ³ := (InnerProductSpace.toDual ℝ ℝ³).symm (LinearMap.toContinuousLinearMap f.linear)
    with hN
  have hNf : ∀ x, f x = ⟪N, x⟫ + f 0 := fun x => by
    rw [hN, InnerProductSpace.toDual_symm_apply]
    have := f.map_vadd 0 x
    simpa using this
  refine ⟨N 0 * O 0 + N 1 * O 1 + f 0, N 0 * r1 0 + N 1 * r1 1, N 0 * r2 0 + N 1 * r2 1, N 2,
    fun a b z => ?_⟩
  rw [hNf]; simp [oblPt, PiLp.inner_apply, Fin.sum_univ_three]; ring

/-- **The sheets at vertex 2.** The plane of 0235 is a lower face through 3
(`γ3 < 0`), the plane of 1246 an upper face through 4 (`γ4 > 0`), both through
2. If 2 lies over the closed triangle `O, A, B` (barycentric `1 - μ - ν, μ, ν`),
then it lies over the chord and its depth is the chord's. -/
theorem sheets_on_chord {μ ν tA tB ZA ZB Z2 Z3 Z4 K3 α3 β3 γ3 K4 α4 β4 γ4 : ℝ}
    (hμ : 0 ≤ μ) (hν : 0 ≤ ν) (hμν : μ + ν ≤ 1) (h34 : Z3 < Z4) (hγ3 : γ3 < 0) (hγ4 : 0 < γ4)
    (f33 : K3 + γ3 * Z3 ≤ 0) (f3A : K3 + α3 * tA + γ3 * ZA ≤ 0) (f3B : K3 + β3 * tB + γ3 * ZB ≤ 0)
    (f32 : K3 + α3 * (μ * tA) + β3 * (ν * tB) + γ3 * Z2 = 0)
    (f44 : K4 + γ4 * Z4 ≤ 0) (f4A : K4 + α4 * tA + γ4 * ZA ≤ 0) (f4B : K4 + β4 * tB + γ4 * ZB ≤ 0)
    (f42 : K4 + α4 * (μ * tA) + β4 * (ν * tB) + γ4 * Z2 = 0) :
    μ + ν = 1 ∧ Z2 = μ * ZA + ν * ZB := by
  set l := 1 - μ - ν with hl
  have hl0 : 0 ≤ l := by linarith
  -- the convex combination of 3, A, B lies above the lower plane, of 4, A, B below the upper
  have c3 : l * (K3 + γ3 * Z3) + μ * (K3 + α3 * tA + γ3 * ZA) + ν * (K3 + β3 * tB + γ3 * ZB) ≤ 0 := by
    have := mul_nonpos_of_nonneg_of_nonpos hl0 f33
    have := mul_nonpos_of_nonneg_of_nonpos hμ f3A
    have := mul_nonpos_of_nonneg_of_nonpos hν f3B
    linarith
  have c4 : l * (K4 + γ4 * Z4) + μ * (K4 + α4 * tA + γ4 * ZA) + ν * (K4 + β4 * tB + γ4 * ZB) ≤ 0 := by
    have := mul_nonpos_of_nonneg_of_nonpos hl0 f44
    have := mul_nonpos_of_nonneg_of_nonpos hμ f4A
    have := mul_nonpos_of_nonneg_of_nonpos hν f4B
    linarith
  have e3 : γ3 * (l * Z3 + μ * ZA + ν * ZB - Z2) ≤ 0 := by linear_combination c3 - f32
  have e4 : γ4 * (l * Z4 + μ * ZA + ν * ZB - Z2) ≤ 0 := by linear_combination c4 - f42
  have g3 : 0 ≤ l * Z3 + μ * ZA + ν * ZB - Z2 := by
    by_contra h; push Not at h; nlinarith
  have g4 : l * Z4 + μ * ZA + ν * ZB - Z2 ≤ 0 := by
    by_contra h; push Not at h; nlinarith
  have hl00 : l = 0 := by
    by_contra h
    have : 0 < l := lt_of_le_of_ne hl0 (Ne.symm h)
    nlinarith
  refine ⟨by linarith, ?_⟩
  rw [hl00] at g3 g4
  linarith

/-- Sign bookkeeping: `a < 0`, `a b < 0` give `b > 0`. -/
theorem pos_of_neg_mul {a b : ℝ} (ha : a < 0) (h : a * b < 0) : 0 < b := by
  by_contra hb; push Not at hb
  have := mul_nonneg_of_nonpos_of_nonpos ha.le hb; linarith

/-- `0 < a`, `a b < 0` give `b < 0`. -/
theorem neg_of_pos_mul {a b : ℝ} (ha : 0 < a) (h : a * b < 0) : b < 0 := by
  by_contra hb; push Not at hb
  have := mul_nonneg ha.le hb; linarith

/-- **Theorem B from four quadrilateral facets** (oblique frame, positive
orientation): the shadows of 0 and 5 span the frame (`t0 = t5 = 1`), 3 and 4
are vertical over `O`, and the quads 0134, 3456, 0235, 1246 are facets. With 2
not in the hull of 0, 1, 5, 6, (G) and (Z), the seven points are Rupert. -/
theorem isRupert_type02_obl (O r1 r2 : ℝ²) (hρ : 0 < cross2 r1 r2)
    {a1 b1 a2 b2 a6 b6 Z0 Z1 Z2 Z3 Z4 Z5 Z6 : ℝ} (h34 : Z3 < Z4)
    (hF1 : ∃ f : ℝ³ →ᵃ[ℝ] ℝ, f (oblPt O r1 r2 0 0 Z3) = 0 ∧
      f (oblPt O r1 r2 1 0 Z0) = 0 ∧
      f (oblPt O r1 r2 a1 b1 Z1) = 0 ∧
      f (oblPt O r1 r2 0 0 Z4) = 0 ∧
      f (oblPt O r1 r2 a2 b2 Z2) < 0 ∧
      f (oblPt O r1 r2 0 1 Z5) < 0 ∧
      f (oblPt O r1 r2 a6 b6 Z6) < 0)
    (hF2 : ∃ f : ℝ³ →ᵃ[ℝ] ℝ, f (oblPt O r1 r2 0 0 Z3) = 0 ∧
      f (oblPt O r1 r2 0 1 Z5) = 0 ∧
      f (oblPt O r1 r2 a6 b6 Z6) = 0 ∧
      f (oblPt O r1 r2 0 0 Z4) = 0 ∧
      f (oblPt O r1 r2 1 0 Z0) < 0 ∧
      f (oblPt O r1 r2 a1 b1 Z1) < 0 ∧
      f (oblPt O r1 r2 a2 b2 Z2) < 0)
    (hF3 : ∃ f : ℝ³ →ᵃ[ℝ] ℝ, f (oblPt O r1 r2 0 0 Z3) = 0 ∧
      f (oblPt O r1 r2 1 0 Z0) = 0 ∧
      f (oblPt O r1 r2 a2 b2 Z2) = 0 ∧
      f (oblPt O r1 r2 0 1 Z5) = 0 ∧
      f (oblPt O r1 r2 a1 b1 Z1) < 0 ∧
      f (oblPt O r1 r2 0 0 Z4) < 0 ∧
      f (oblPt O r1 r2 a6 b6 Z6) < 0)
    (hF4 : ∃ f : ℝ³ →ᵃ[ℝ] ℝ, f (oblPt O r1 r2 0 0 Z4) = 0 ∧
      f (oblPt O r1 r2 a1 b1 Z1) = 0 ∧
      f (oblPt O r1 r2 a2 b2 Z2) = 0 ∧
      f (oblPt O r1 r2 a6 b6 Z6) = 0 ∧
      f (oblPt O r1 r2 1 0 Z0) < 0 ∧
      f (oblPt O r1 r2 0 0 Z3) < 0 ∧
      f (oblPt O r1 r2 0 1 Z5) < 0)
    (hext : oblPt O r1 r2 a2 b2 Z2 ∉ convexHull ℝ ({oblPt O r1 r2 1 0 Z0, oblPt O r1 r2 a1 b1 Z1, oblPt O r1 r2 0 1 Z5, oblPt O r1 r2 a6 b6 Z6} : Set ℝ³))
    (hG1 : a1 ≠ 1 ∨ b1 ≠ 0) (hG2 : a6 ≠ 0 ∨ b6 ≠ 1)
    (hZ : Function.Injective (![Z0, Z1, Z2, Z3, Z4, Z5, Z6] : Fin 7 → ℝ)) :
    IsRupert ({oblPt O r1 r2 1 0 Z0, oblPt O r1 r2 a1 b1 Z1, oblPt O r1 r2 a2 b2 Z2, oblPt O r1 r2 0 0 Z3, oblPt O r1 r2 0 0 Z4, oblPt O r1 r2 0 1 Z5, oblPt O r1 r2 a6 b6 Z6} : Finset ℝ³) := by
  have hZ34 : 0 < Z4 - Z3 := by linarith
  -- 0134: a vertical plane, `f = β b`
  obtain ⟨f1, e13, e10, e11, e14, n12, n15, n16⟩ := hF1
  obtain ⟨K1, α1, β1, γ1, hf1⟩ := affine_obl f1 O r1 r2
  simp only [hf1] at e13 e10 e11 e14 n12 n15 n16
  have hγ1 : γ1 = 0 := by
    have : γ1 * (Z4 - Z3) = 0 := by linear_combination e14 - e13
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · linarith
  subst hγ1
  have hK1 : K1 = 0 := by linarith
  subst hK1
  have hα1 : α1 = 0 := by linarith
  subst hα1
  have hβ1 : β1 < 0 := by linarith
  have hb1 : b1 = 0 := by
    have : β1 * b1 = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · exact h
  subst hb1
  have hb2 : 0 < b2 := pos_of_neg_mul hβ1 (by linarith)
  have hb6 : 0 < b6 := pos_of_neg_mul hβ1 (by linarith)
  -- 3456: `f = α a`
  obtain ⟨f2, e23, e25, e26, e24, n20, n21, n22⟩ := hF2
  obtain ⟨K2, α2, β2, γ2, hf2⟩ := affine_obl f2 O r1 r2
  simp only [hf2] at e23 e25 e26 e24 n20 n21 n22
  have hγ2 : γ2 = 0 := by
    have : γ2 * (Z4 - Z3) = 0 := by linear_combination e24 - e23
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · linarith
  subst hγ2
  have hK2 : K2 = 0 := by linarith
  subst hK2
  have hβ2 : β2 = 0 := by linarith
  subst hβ2
  have hα2 : α2 < 0 := by linarith
  have ha6 : a6 = 0 := by
    have : α2 * a6 = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · exact h
  subst ha6
  have ha1 : 0 < a1 := pos_of_neg_mul hα2 (by linarith)
  have ha2 : 0 < a2 := pos_of_neg_mul hα2 (by linarith)
  have hG1' : a1 ≠ 1 := hG1.resolve_right (fun h => h rfl)
  have hG2' : b6 ≠ 1 := hG2.resolve_left (fun h => h rfl)
  -- 0235: the lower plane through 3
  obtain ⟨f3, e33, e30, e32, e35, n31, n34, n36⟩ := hF3
  obtain ⟨K3, α3, β3, γ3, hf3⟩ := affine_obl f3 O r1 r2
  simp only [hf3] at e33 e30 e32 e35 n31 n34 n36
  have hγ3 : γ3 < 0 := neg_of_mul_neg_pos (by linarith : γ3 * (Z4 - Z3) < 0) hZ34
  have hK3 : K3 = -(γ3 * Z3) := by linarith
  have hα3 : α3 = -(γ3 * (Z0 - Z3)) := by linarith
  have hβ3 : β3 = -(γ3 * (Z5 - Z3)) := by linarith
  have hQ3 : 1 * 1 * (Z2 - Z3) = a2 * 1 * (Z0 - Z3) + b2 * 1 * (Z5 - Z3) := by
    have : γ3 * ((Z2 - Z3) - a2 * (Z0 - Z3) - b2 * (Z5 - Z3)) = 0 := by
      linear_combination e32 - e33 - a2 * hα3 - b2 * hβ3
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · linarith
  have T301 : 0 < (Z1 - Z3) - a1 * (Z0 - Z3) :=
    pos_of_neg_mul hγ3 (by linear_combination n31 - e33 - a1 * hα3)
  have T356 : 0 < (Z6 - Z3) - b6 * (Z5 - Z3) :=
    pos_of_neg_mul hγ3 (by linear_combination n36 - e33 - b6 * hβ3)
  -- 1246: the upper plane through 4
  obtain ⟨f4, e44, e41, e42, e46, n40, n43, n45⟩ := hF4
  obtain ⟨K4, α4, β4, γ4, hf4⟩ := affine_obl f4 O r1 r2
  simp only [hf4] at e44 e41 e42 e46 n40 n43 n45
  have hγ4 : 0 < γ4 := pos_of_neg_mul (by linarith : Z3 - Z4 < 0)
    (by linarith : (Z3 - Z4) * γ4 < 0)
  have hK4 : K4 = -(γ4 * Z4) := by linarith
  have hα4 : α4 * a1 = -(γ4 * (Z1 - Z4)) := by linarith
  have hβ4 : β4 * b6 = -(γ4 * (Z6 - Z4)) := by linarith
  have hQ4 : a1 * b6 * (Z2 - Z4) = a2 * b6 * (Z1 - Z4) + b2 * a1 * (Z6 - Z4) := by
    have : γ4 * (a1 * b6 * (Z2 - Z4) - a2 * b6 * (Z1 - Z4) - b2 * a1 * (Z6 - Z4)) = 0 := by
      linear_combination (a1 * b6) * e42 - (a1 * b6) * e44 - (a2 * b6) * hα4 - (b2 * a1) * hβ4
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · linarith
  have T014 : a1 * (Z0 - Z4) - (Z1 - Z4) < 0 := by
    have h := mul_lt_mul_of_pos_left n40 ha1
    exact neg_of_pos_mul hγ4 (by linear_combination h - a1 * e44 - hα4)
  have T564 : b6 * (Z5 - Z4) - (Z6 - Z4) < 0 := by
    have h := mul_lt_mul_of_pos_left n45 hb6
    exact neg_of_pos_mul hγ4 (by linear_combination h - b6 * e44 - hβ4)
  have P1 : 0 < a1 * (Z4 - Z3) := mul_pos ha1 hZ34
  have P2 : 0 < b6 * (Z4 - Z3) := mul_pos hb6 hZ34
  have hQ1 : ConvQuad 0 Z3 1 Z0 a1 Z1 0 Z4 := by
    unfold ConvQuad
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> linarith
  have hQ2 : ConvQuad 0 Z3 1 Z5 b6 Z6 0 Z4 := by
    unfold ConvQuad
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> linarith
  -- 2 lies beyond the chord of the far vertices
  have hch : max 1 a1 * max 1 b6 < a2 * max 1 b6 + b2 * max 1 a1 := by
    by_contra hle
    push Not at hle
    -- the far vertices, their depths, and the facet values there
    obtain ⟨tA, ZA, htA, hmA, f3A, f4A, hyA⟩ : ∃ tA ZA : ℝ, 0 < tA ∧ max 1 a1 = tA ∧
        K3 + α3 * tA + γ3 * ZA ≤ 0 ∧ K4 + α4 * tA + γ4 * ZA ≤ 0 ∧
        (oblPt O r1 r2 tA 0 ZA = oblPt O r1 r2 1 0 Z0 ∨ oblPt O r1 r2 tA 0 ZA = oblPt O r1 r2 a1 0 Z1) := by
      rcases lt_or_gt_of_ne hG1' with h | h
      · exact ⟨1, Z0, one_pos, max_eq_left h.le, by linarith, by linarith, Or.inl rfl⟩
      · exact ⟨a1, Z1, ha1, max_eq_right h.le, by linarith, by linarith, Or.inr rfl⟩
    obtain ⟨tB, ZB, htB, hmB, f3B, f4B, hyB⟩ : ∃ tB ZB : ℝ, 0 < tB ∧ max 1 b6 = tB ∧
        K3 + β3 * tB + γ3 * ZB ≤ 0 ∧ K4 + β4 * tB + γ4 * ZB ≤ 0 ∧
        (oblPt O r1 r2 0 tB ZB = oblPt O r1 r2 0 1 Z5 ∨ oblPt O r1 r2 0 tB ZB = oblPt O r1 r2 0 b6 Z6) := by
      rcases lt_or_gt_of_ne hG2' with h | h
      · exact ⟨1, Z5, one_pos, max_eq_left h.le, by linarith, by linarith, Or.inl rfl⟩
      · exact ⟨b6, Z6, hb6, max_eq_right h.le, by linarith, by linarith, Or.inr rfl⟩
    rw [hmA, hmB] at hle
    set μ := a2 / tA with hμ
    set ν := b2 / tB with hν
    have hμt : μ * tA = a2 := by rw [hμ]; field_simp
    have hνt : ν * tB = b2 := by rw [hν]; field_simp
    have hμ0 : 0 ≤ μ := div_nonneg ha2.le htA.le
    have hν0 : 0 ≤ ν := div_nonneg hb2.le htB.le
    have hμν : μ + ν ≤ 1 := by
      have e : μ + ν = (a2 * tB + b2 * tA) / (tA * tB) := by rw [hμ, hν]; field_simp
      rw [e, div_le_one (mul_pos htA htB)]; linarith
    obtain ⟨hsum, hZ2⟩ := sheets_on_chord (Z2 := Z2) hμ0 hν0 hμν h34 hγ3 hγ4 (by linarith) f3A f3B
      (by rw [hμt, hνt]; linarith) (by linarith) f4A f4B (by rw [hμt, hνt]; linarith)
    apply hext
    have hseg : oblPt O r1 r2 a2 b2 Z2 ∈ segment ℝ (oblPt O r1 r2 tA 0 ZA) (oblPt O r1 r2 0 tB ZB) := by
      refine ⟨μ, ν, hμ0, hν0, hsum, ?_⟩
      rw [← hμt, ← hνt, hZ2]
      ext i; fin_cases i <;> simp [oblPt]
      · linear_combination (O 0) * hsum
      · linear_combination (O 1) * hsum
    refine segment_subset_convexHull ?_ ?_ hseg
    · rcases hyA with h | h <;> rw [h] <;> simp
    · rcases hyB with h | h <;> rw [h] <;> simp
  exact isRupert_type02_frame O r1 r2 hρ one_pos ha1 one_pos hb6 ha2 hb2 h34 hQ1 hQ2 hQ3 hQ4
    (Ne.symm hG1') (Ne.symm hG2') hch hZ

/-- Seven points as a literal set. -/
theorem univ_image_fin7 {α : Type*} [DecidableEq α] (y : Fin 7 → α) :
    Finset.univ.image y = {y 0, y 1, y 2, y 3, y 4, y 5, y 6} := by
  ext p
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨i, rfl⟩; fin_cases i <;> simp
  · rintro (h | h | h | h | h | h | h) <;> exact ⟨_, h.symm⟩

/-- Every affine function on `ℝ³` in coordinates. -/
theorem affine_xyz (f : ℝ³ →ᵃ[ℝ] ℝ) :
    ∃ K α β γ : ℝ, ∀ p : ℝ³, f p = K + α * p 0 + β * p 1 + γ * p 2 := by
  obtain ⟨K, α, β, γ, h⟩ := affine_obl f 0 !₂[1, 0] !₂[0, 1]
  refine ⟨K, α, β, γ, fun p => ?_⟩
  have : p = oblPt 0 !₂[1, 0] !₂[0, 1] (p 0) (p 1) (p 2) := by
    ext i; fin_cases i <;> simp [oblPt]
  rw [this, h]; simp [oblPt]

/-- Cramer's rule in the plane. -/
theorem cramer2 (u r1 r2 : ℝ²) (hρ : cross2 r1 r2 ≠ 0) :
    u 0 = cross2 u r2 / cross2 r1 r2 * r1 0 + cross2 r1 u / cross2 r1 r2 * r2 0 ∧
    u 1 = cross2 u r2 / cross2 r1 r2 * r1 1 + cross2 r1 u / cross2 r1 r2 * r2 1 := by
  have k0 : cross2 u r2 * r1 0 + cross2 r1 u * r2 0 = u 0 * cross2 r1 r2 := by unfold cross2; ring
  have k1 : cross2 u r2 * r1 1 + cross2 r1 u * r2 1 = u 1 * cross2 r1 r2 := by unfold cross2; ring
  constructor
  · rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, k0, mul_div_assoc, div_self hρ, mul_one]
  · rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, k1, mul_div_assoc, div_self hρ, mul_one]

set_option maxHeartbeats 1000000 in
/-- **Theorem B with the edge 34 vertical.** -/
theorem isRupert_type02_vertical (y : Fin 7 → ℝ³)
    (h340 : y 3 0 = y 4 0) (h341 : y 3 1 = y 4 1) (h34 : y 3 2 < y 4 2)
    (hF1 : ∃ f : ℝ³ →ᵃ[ℝ] ℝ, f (y 3) = 0 ∧
      f (y 0) = 0 ∧
      f (y 1) = 0 ∧
      f (y 4) = 0 ∧
      f (y 2) < 0 ∧
      f (y 5) < 0 ∧
      f (y 6) < 0)
    (hF2 : ∃ f : ℝ³ →ᵃ[ℝ] ℝ, f (y 3) = 0 ∧
      f (y 5) = 0 ∧
      f (y 6) = 0 ∧
      f (y 4) = 0 ∧
      f (y 0) < 0 ∧
      f (y 1) < 0 ∧
      f (y 2) < 0)
    (hF3 : ∃ f : ℝ³ →ᵃ[ℝ] ℝ, f (y 3) = 0 ∧
      f (y 0) = 0 ∧
      f (y 2) = 0 ∧
      f (y 5) = 0 ∧
      f (y 1) < 0 ∧
      f (y 4) < 0 ∧
      f (y 6) < 0)
    (hF4 : ∃ f : ℝ³ →ᵃ[ℝ] ℝ, f (y 4) = 0 ∧
      f (y 1) = 0 ∧
      f (y 2) = 0 ∧
      f (y 6) = 0 ∧
      f (y 0) < 0 ∧
      f (y 3) < 0 ∧
      f (y 5) < 0)
    (hext : y 2 ∉ convexHull ℝ ({y 0, y 1, y 5, y 6} : Set ℝ³))
    (hG1 : y 1 0 ≠ y 0 0 ∨ y 1 1 ≠ y 0 1) (hG2 : y 6 0 ≠ y 5 0 ∨ y 6 1 ≠ y 5 1)
    (hZ : Function.Injective fun i => y i 2) : IsRupert (Finset.univ.image y) := by
  set O : ℝ² := !₂[y 3 0, y 3 1] with hO
  set r1 : ℝ² := !₂[y 0 0 - y 3 0, y 0 1 - y 3 1] with hr1
  set r2 : ℝ² := !₂[y 5 0 - y 3 0, y 5 1 - y 3 1] with hr2
  -- the two edge-on quads make the frame non-degenerate
  have hρ : cross2 r1 r2 ≠ 0 := by
    obtain ⟨f1, e13, e10, -, e14, -, n15, -⟩ := hF1
    obtain ⟨f2, e23, e25, -, e24, n20, -, -⟩ := hF2
    obtain ⟨K1, α1, β1, γ1, h1⟩ := affine_xyz f1
    obtain ⟨K2, α2, β2, γ2, h2⟩ := affine_xyz f2
    rw [h1] at e13 e10 e14 n15
    rw [h2] at e23 e25 e24 n20
    have hZ34 : 0 < y 4 2 - y 3 2 := by linarith
    have hγ1 : γ1 = 0 := by
      have : γ1 * (y 4 2 - y 3 2) = 0 := by
        linear_combination e14 - e13 + α1 * h340 + β1 * h341
      exact (mul_eq_zero.mp this).resolve_right hZ34.ne'
    have hγ2 : γ2 = 0 := by
      have : γ2 * (y 4 2 - y 3 2) = 0 := by
        linear_combination e24 - e23 + α2 * h340 + β2 * h341
      exact (mul_eq_zero.mp this).resolve_right hZ34.ne'
    subst hγ1 hγ2
    intro hρ0
    simp only [hr1, hr2, cross2] at hρ0
    simp at hρ0
    -- f1 vanishes on r1 and is negative on r2; f2 the other way round
    have g1 : α1 * (y 0 0 - y 3 0) + β1 * (y 0 1 - y 3 1) = 0 := by linear_combination e10 - e13
    have g2 : α1 * (y 5 0 - y 3 0) + β1 * (y 5 1 - y 3 1) < 0 := by linarith
    have g3 : α2 * (y 0 0 - y 3 0) + β2 * (y 0 1 - y 3 1) < 0 := by linarith
    have g4 : α2 * (y 5 0 - y 3 0) + β2 * (y 5 1 - y 3 1) = 0 := by linear_combination e25 - e23
    -- (N · r2) r1 = (N · r1) r2 when cross2 r1 r2 = 0
    have k0 : (α1 * (y 5 0 - y 3 0) + β1 * (y 5 1 - y 3 1)) * (y 0 0 - y 3 0) = 0 := by
      linear_combination (y 5 0 - y 3 0) * g1 + β1 * hρ0
    have k1 : (α1 * (y 5 0 - y 3 0) + β1 * (y 5 1 - y 3 1)) * (y 0 1 - y 3 1) = 0 := by
      linear_combination (y 5 1 - y 3 1) * g1 - α1 * hρ0
    have r10 : y 0 0 - y 3 0 = 0 := (mul_eq_zero.mp k0).resolve_left g2.ne
    have r11 : y 0 1 - y 3 1 = 0 := (mul_eq_zero.mp k1).resolve_left g2.ne
    rw [r10, r11] at g3; linarith
  -- oblique coordinates (Cramer)
  set ρ := cross2 r1 r2 with hρdef
  set a : Fin 7 → ℝ := fun i => cross2 !₂[y i 0 - y 3 0, y i 1 - y 3 1] r2 / ρ with ha
  set b : Fin 7 → ℝ := fun i => cross2 r1 !₂[y i 0 - y 3 0, y i 1 - y 3 1] / ρ with hb
  have hy : ∀ i, y i = oblPt O r1 r2 (a i) (b i) (y i 2) := by
    intro i
    obtain ⟨c0, c1⟩ := cramer2 !₂[y i 0 - y 3 0, y i 1 - y 3 1] r1 r2 hρ
    ext j; fin_cases j
    · simp only [oblPt, ha, hb]; simp only [hO]; simp at c0 ⊢; linarith
    · simp only [oblPt, ha, hb]; simp only [hO]; simp at c1 ⊢; linarith
    · simp [oblPt]
  have ha0 : a 0 = 1 := by simp only [ha, hr1, hρdef]; exact div_self hρ
  have hb0 : b 0 = 0 := by
    simp only [hb]; exact div_eq_zero_iff.mpr (Or.inl (by simp only [hr1, cross2]; simp; ring))
  have ha5 : a 5 = 0 := by
    simp only [ha]; exact div_eq_zero_iff.mpr (Or.inl (by simp only [hr2, cross2]; simp; ring))
  have hb5 : b 5 = 1 := by simp only [hb, hr2, hρdef]; exact div_self hρ
  have ha3 : a 3 = 0 := by simp [ha, cross2]
  have hb3 : b 3 = 0 := by simp [hb, cross2]
  have ha4 : a 4 = 0 := by simp [ha, cross2, ← h340, ← h341]
  have hb4 : b 4 = 0 := by simp [hb, cross2, ← h340, ← h341]
  -- the seven points in the frame
  have E : ∀ i, oblPt O r1 r2 (a i) (b i) (y i 2) = y i := fun i => (hy i).symm
  have E0 : oblPt O r1 r2 1 0 (y 0 2) = y 0 := by
    have := E 0; rwa [ha0, hb0] at this
  have E3 : oblPt O r1 r2 0 0 (y 3 2) = y 3 := by
    have := E 3; rwa [ha3, hb3] at this
  have E4 : oblPt O r1 r2 0 0 (y 4 2) = y 4 := by
    have := E 4; rwa [ha4, hb4] at this
  have E5 : oblPt O r1 r2 0 1 (y 5 2) = y 5 := by
    have := E 5; rwa [ha5, hb5] at this
  have swap : ∀ p q z, oblPt O r2 r1 q p z = oblPt O r1 r2 p q z := by
    intro p q z; ext j; fin_cases j <;> simp [oblPt] <;> ring
  -- (G) in the frame
  have hG1' : a 1 ≠ 1 ∨ b 1 ≠ 0 := by
    by_contra h; push Not at h
    have c0 := congrArg (fun p : ℝ³ => p 0) (E 1)
    have c1 := congrArg (fun p : ℝ³ => p 1) (E 1)
    have d0 := congrArg (fun p : ℝ³ => p 0) E0
    have d1 := congrArg (fun p : ℝ³ => p 1) E0
    simp only [oblPt, h.1, h.2] at c0 c1 d0 d1
    simp at c0 c1 d0 d1
    rcases hG1 with h' | h' <;> apply h' <;> linarith
  have hG2' : a 6 ≠ 0 ∨ b 6 ≠ 1 := by
    by_contra h; push Not at h
    have c0 := congrArg (fun p : ℝ³ => p 0) (E 6)
    have c1 := congrArg (fun p : ℝ³ => p 1) (E 6)
    have d0 := congrArg (fun p : ℝ³ => p 0) E5
    have d1 := congrArg (fun p : ℝ³ => p 1) E5
    simp only [oblPt, h.1, h.2] at c0 c1 d0 d1
    simp at c0 c1 d0 d1
    rcases hG2 with h' | h' <;> apply h' <;> linarith
  have hZ7 : ∀ σ : Fin 7 → Fin 7, Function.Injective σ →
      Function.Injective (fun i => y (σ i) 2) := fun σ hσ => hZ.comp hσ
  rcases lt_or_gt_of_ne hρ with hneg | hpos
  · -- negative orientation: swap the two quads (0 5)(1 6) and the two rays
    have hpos' : 0 < cross2 r2 r1 := by
      have : cross2 r2 r1 = -cross2 r1 r2 := by unfold cross2; ring
      rw [this]; linarith
    obtain ⟨f1, e13, e10, e11, e14, n12, n15, n16⟩ := hF1
    obtain ⟨f2, e23, e25, e26, e24, n20, n21, n22⟩ := hF2
    obtain ⟨f3, e33, e30, e32, e35, n31, n34, n36⟩ := hF3
    obtain ⟨f4, e44, e41, e42, e46, n40, n43, n45⟩ := hF4
    have key := isRupert_type02_obl O r2 r1 hpos' (a1 := b 6) (b1 := a 6) (a2 := b 2) (b2 := a 2)
      (a6 := b 1) (b6 := a 1) (Z0 := y 5 2) (Z1 := y 6 2) (Z2 := y 2 2) (Z3 := y 3 2) (Z4 := y 4 2)
      (Z5 := y 0 2) (Z6 := y 1 2) h34
      ⟨f2, by rw [← E3, ← swap] at e23; exact e23, by rw [← E5, ← swap] at e25; exact e25,
        by rw [← E 6, ← swap] at e26; exact e26, by rw [← E4, ← swap] at e24; exact e24,
        by rw [← E 2, ← swap] at n22; exact n22, by rw [← E0, ← swap] at n20; exact n20,
        by rw [← E 1, ← swap] at n21; exact n21⟩
      ⟨f1, by rw [← E3, ← swap] at e13; exact e13, by rw [← E0, ← swap] at e10; exact e10,
        by rw [← E 1, ← swap] at e11; exact e11, by rw [← E4, ← swap] at e14; exact e14,
        by rw [← E5, ← swap] at n15; exact n15, by rw [← E 6, ← swap] at n16; exact n16,
        by rw [← E 2, ← swap] at n12; exact n12⟩
      ⟨f3, by rw [← E3, ← swap] at e33; exact e33, by rw [← E5, ← swap] at e35; exact e35,
        by rw [← E 2, ← swap] at e32; exact e32, by rw [← E0, ← swap] at e30; exact e30,
        by rw [← E 6, ← swap] at n36; exact n36, by rw [← E4, ← swap] at n34; exact n34,
        by rw [← E 1, ← swap] at n31; exact n31⟩
      ⟨f4, by rw [← E4, ← swap] at e44; exact e44, by rw [← E 6, ← swap] at e46; exact e46,
        by rw [← E 2, ← swap] at e42; exact e42, by rw [← E 1, ← swap] at e41; exact e41,
        by rw [← E5, ← swap] at n45; exact n45, by rw [← E3, ← swap] at n43; exact n43,
        by rw [← E0, ← swap] at n40; exact n40⟩
      (by
        rw [swap, swap, swap, swap, swap, E 2, E5, E 6, E0, E 1]
        have hs : ({y 5, y 6, y 0, y 1} : Set ℝ³) = {y 0, y 1, y 5, y 6} := by
          ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
        rw [hs]; exact hext)
      hG2'.symm hG1'.symm
      (by
        have := hZ7 ![5, 6, 2, 3, 4, 0, 1] (by decide)
        convert this using 1; funext i; fin_cases i <;> rfl)
    rw [swap, swap, swap, swap, swap, swap, swap, E5, E 6, E 2, E3, E4, E0, E 1] at key
    have hs : ({y 0, y 1, y 2, y 3, y 4, y 5, y 6} : Finset ℝ³) =
        {y 5, y 6, y 2, y 3, y 4, y 0, y 1} := by
      ext p; simp only [Finset.mem_insert, Finset.mem_singleton]
      constructor <;> intro h <;> rcases h with h | h | h | h | h | h | h <;>
        simp only [h, true_or, or_true]
    rw [univ_image_fin7, hs]; exact key
  · obtain ⟨f1, e13, e10, e11, e14, n12, n15, n16⟩ := hF1
    obtain ⟨f2, e23, e25, e26, e24, n20, n21, n22⟩ := hF2
    obtain ⟨f3, e33, e30, e32, e35, n31, n34, n36⟩ := hF3
    obtain ⟨f4, e44, e41, e42, e46, n40, n43, n45⟩ := hF4
    have key := isRupert_type02_obl O r1 r2 hpos (a1 := a 1) (b1 := b 1) (a2 := a 2) (b2 := b 2)
      (a6 := a 6) (b6 := b 6) (Z0 := y 0 2) (Z1 := y 1 2) (Z2 := y 2 2) (Z3 := y 3 2) (Z4 := y 4 2)
      (Z5 := y 5 2) (Z6 := y 6 2) h34
      ⟨f1, by rw [E3]; exact e13, by rw [E0]; exact e10, by rw [E 1]; exact e11, by rw [E4]; exact e14,
        by rw [E 2]; exact n12, by rw [E5]; exact n15, by rw [E 6]; exact n16⟩
      ⟨f2, by rw [E3]; exact e23, by rw [E5]; exact e25, by rw [E 6]; exact e26, by rw [E4]; exact e24,
        by rw [E0]; exact n20, by rw [E 1]; exact n21, by rw [E 2]; exact n22⟩
      ⟨f3, by rw [E3]; exact e33, by rw [E0]; exact e30, by rw [E 2]; exact e32, by rw [E5]; exact e35,
        by rw [E 1]; exact n31, by rw [E4]; exact n34, by rw [E 6]; exact n36⟩
      ⟨f4, by rw [E4]; exact e44, by rw [E 1]; exact e41, by rw [E 2]; exact e42, by rw [E 6]; exact e46,
        by rw [E0]; exact n40, by rw [E3]; exact n43, by rw [E5]; exact n45⟩
      (by rw [E 2, E0, E 1, E5, E 6]; exact hext) hG1' hG2'
      (by
        have := hZ7 id Function.injective_id
        convert this using 1; funext i; fin_cases i <;> rfl)
    rw [E0, E 1, E 2, E3, E4, E5, E 6] at key
    rw [univ_image_fin7]; exact key

/-- **Theorem B** (FEWER-FACES-PROOFS.md §4, generic case): seven points
labelled as type 02, with the quadrilaterals 0134, 3456, 0235, 1246 as facets
(given by their supporting affine functions), 2 not in the hull of 0, 1, 5, 6,
the edges 01 and 56 not parallel to 34 (G), and distinct depths along 34 (Z),
are Rupert. -/
theorem isRupert_type02 (x : Fin 7 → ℝ³) (h34 : x 3 ≠ x 4)
    (hF1 : ∃ f : ℝ³ →ᵃ[ℝ] ℝ, f (x 3) = 0 ∧
      f (x 0) = 0 ∧
      f (x 1) = 0 ∧
      f (x 4) = 0 ∧
      f (x 2) < 0 ∧
      f (x 5) < 0 ∧
      f (x 6) < 0)
    (hF2 : ∃ f : ℝ³ →ᵃ[ℝ] ℝ, f (x 3) = 0 ∧
      f (x 5) = 0 ∧
      f (x 6) = 0 ∧
      f (x 4) = 0 ∧
      f (x 0) < 0 ∧
      f (x 1) < 0 ∧
      f (x 2) < 0)
    (hF3 : ∃ f : ℝ³ →ᵃ[ℝ] ℝ, f (x 3) = 0 ∧
      f (x 0) = 0 ∧
      f (x 2) = 0 ∧
      f (x 5) = 0 ∧
      f (x 1) < 0 ∧
      f (x 4) < 0 ∧
      f (x 6) < 0)
    (hF4 : ∃ f : ℝ³ →ᵃ[ℝ] ℝ, f (x 4) = 0 ∧
      f (x 1) = 0 ∧
      f (x 2) = 0 ∧
      f (x 6) = 0 ∧
      f (x 0) < 0 ∧
      f (x 3) < 0 ∧
      f (x 5) < 0)
    (hext : x 2 ∉ convexHull ℝ ({x 0, x 1, x 5, x 6} : Set ℝ³))
    (hG1 : ∀ c : ℝ, x 1 - x 0 ≠ c • (x 4 - x 3)) (hG2 : ∀ c : ℝ, x 6 - x 5 ≠ c • (x 4 - x 3))
    (hZ : Function.Injective fun i => ⟪x i, x 4 - x 3⟫) :
    IsRupert (Finset.univ.image x) := by
  classical
  set e := x 4 - x 3 with he
  have he0 : e ≠ 0 := sub_ne_zero.mpr h34.symm
  obtain ⟨R, hR, r, hr, hRe⟩ := exists_rotation_to_ez_pos e he0
  apply isRupert_of_isRupert_image_rotation R hR
  set g := R.toEuclideanLin with hg
  set I := so3Isometry hR with hI
  have hgI : ∀ p, g p = I p := fun p => rfl
  have hginj : Function.Injective g := I.injective
  rw [Finset.image_image]
  have hge : g (x 4) - g (x 3) = r • ez := by rw [← map_sub]; exact hRe
  have hgz : ∀ p, g p 2 = ⟪p, e⟫ / r := fun p => by
    have := inner_toEuclideanLin_SO3 hR p e
    rw [hRe, real_inner_smul_right, inner_ez] at this
    field_simp; linarith
  -- facets transported by the inverse rotation
  have tr : ∀ {f : ℝ³ →ᵃ[ℝ] ℝ}, ∃ f' : ℝ³ →ᵃ[ℝ] ℝ, ∀ i, f' (g (x i)) = f (x i) := by
    intro f
    refine ⟨f.comp I.symm.toLinearEquiv.toLinearMap.toAffineMap, fun i => ?_⟩
    simp [hgI]
  refine isRupert_type02_vertical (fun i => g (x i)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · have := congrArg (fun p : ℝ³ => p 0) hge; simp [ez] at this; linarith
  · have := congrArg (fun p : ℝ³ => p 1) hge; simp [ez] at this; linarith
  · have := congrArg (fun p : ℝ³ => p 2) hge; simp [ez] at this; linarith
  · obtain ⟨f, h⟩ := hF1
    obtain ⟨f', hf'⟩ := tr (f := f)
    exact ⟨f', by simp only [hf']; exact h⟩
  · obtain ⟨f, h⟩ := hF2
    obtain ⟨f', hf'⟩ := tr (f := f)
    exact ⟨f', by simp only [hf']; exact h⟩
  · obtain ⟨f, h⟩ := hF3
    obtain ⟨f', hf'⟩ := tr (f := f)
    exact ⟨f', by simp only [hf']; exact h⟩
  · obtain ⟨f, h⟩ := hF4
    obtain ⟨f', hf'⟩ := tr (f := f)
    exact ⟨f', by simp only [hf']; exact h⟩
  · intro hmem
    apply hext
    have himg : ({g (x 0), g (x 1), g (x 5), g (x 6)} : Set ℝ³) =
        g '' ({x 0, x 1, x 5, x 6} : Set ℝ³) := by
      simp [Set.image_insert_eq]
    rw [himg, ← LinearMap.image_convexHull] at hmem
    obtain ⟨p, hp, hpe⟩ := hmem
    rwa [← hginj hpe]
  · -- (G): equal shadows would make 01 parallel to 34
    by_contra h; push Not at h
    obtain ⟨h0, h1⟩ := h
    apply hG1 ((g (x 1 - x 0)) 2 / r)
    apply hginj
    rw [map_smul, map_sub g (x 4), hge]
    ext j; fin_cases j
    · simp [ez, map_sub]; linarith
    · simp [ez, map_sub]; linarith
    · simp [ez]; field_simp
  · by_contra h; push Not at h
    obtain ⟨h0, h1⟩ := h
    apply hG2 ((g (x 6 - x 5)) 2 / r)
    apply hginj
    rw [map_smul, map_sub g (x 4), hge]
    ext j; fin_cases j
    · simp [ez, map_sub]; linarith
    · simp [ez, map_sub]; linarith
    · simp [ez]; field_simp
  · intro i j hij
    apply hZ
    simp only [hgz] at hij
    simpa [hr.ne'] using hij

/-! ### The cycle core of Theorem B′ (type 05, view along edge 12)

Labels as in §5: the edge 12 (`z1 < z2`), the quads 1032 and 6512 seen edge-on
(`t0, t3` on the first ray, `t5, t6` on the second), vertex 4 at `(s4, u4)`.
(P) is the plane of 0145 through 1; at the top vertex 2 there is no second
plane, only the concave upper sheet over the triangles 234 and 246 (C), used
on a chord from `(T1, 0)` to `(0, T2)` beyond which 4 lies, in cleared form:
`(s4 T2 + u4 T1 - T1 T2) z2 + T1 T2 z4 ≥ s4 T2 zy1 + u4 T1 zy2`. -/

/-- (C) with both chord ends above the top vertex: 4 is above it too. -/
theorem sheet_up {T1 T2 S U z2 z4 zy1 zy2 : ℝ} (hT : 0 < T1 * T2) (hS : 0 < S) (hU : 0 < U)
    (hC : (S + U - T1 * T2) * z2 + T1 * T2 * z4 ≥ S * zy1 + U * zy2)
    (h1 : z2 < zy1) (h2 : z2 < zy2) : z2 < z4 := by
  have : S * z2 + U * z2 < S * zy1 + U * zy2 := by
    have := mul_lt_mul_of_pos_left h1 hS; have := mul_lt_mul_of_pos_left h2 hU; linarith
  by_contra h; push Not at h
  have := mul_le_mul_of_nonneg_left h hT.le
  nlinarith

/-- (C) on a chord beyond which 4 lies: 4 cannot be strictly between the top
vertex and both chord ends. -/
theorem sheet_contra {T1 T2 S U z2 z4 zy1 zy2 : ℝ} (hT : 0 < T1 * T2) (hS : 0 < S) (hU : 0 < U)
    (hD : T1 * T2 < S + U)
    (hC : (S + U - T1 * T2) * z2 + T1 * T2 * z4 ≥ S * zy1 + U * zy2)
    (h24 : z2 < z4) (h1 : z4 < zy1) (h2 : z4 < zy2) : False := by
  have a1 := mul_lt_mul_of_pos_left h24 (by linarith : 0 < S + U - T1 * T2)
  have a2 := mul_lt_mul_of_pos_left h1 hS
  have a3 := mul_lt_mul_of_pos_left h2 hU
  nlinarith

/-- Case (i), both far vertices next to the top ((A, B) = (3, 6) in §5): the
plane through `b`, `x` (at `(T0, 0)`) and `y` (at `(0, T5)`), convex lower
chains `b, x, w` (`w` at `(T3, 0)`, `T0 < T3`) and `b, y, w'` (`w'` at
`(0, T6)`, `T5 < T6`), and `c` beyond the chord `w w'`: `c` is not above both. -/
theorem plane_both {T0 T3 T5 T6 S U zb x y w w' c : ℝ} (hT0 : 0 < T0) (hT5 : 0 < T5)
    (hS : 0 < S) (hU : 0 < U) (hT03 : T0 < T3) (hT56 : T5 < T6)
    (hpl : T0 * T5 * (c - zb) = S * T5 * (x - zb) + U * T0 * (y - zb))
    (hconv : (x - zb) * (T3 - T0) < (w - x) * T0) (hconv' : (y - zb) * (T6 - T5) < (w' - y) * T5)
    (hch : T3 * T6 < S * T6 + U * T3) (hx : x < zb) (hy : y < zb) (hcw : w < c) (hcw' : w' < c) :
    False := by
  obtain ⟨p, rfl⟩ : ∃ p, x = zb - p := ⟨zb - x, by ring⟩
  obtain ⟨q, rfl⟩ : ∃ q, y = zb - q := ⟨zb - y, by ring⟩
  have hp0 : 0 < p := by linarith
  have hq0 : 0 < q := by linarith
  have hpl' : T0 * T5 * (c - zb) = -(S * T5 * p) - U * T0 * q := by linear_combination hpl
  have hw : -(T3 * p) < T0 * (w - zb) := by linear_combination hconv
  have hw' : -(T6 * q) < T5 * (w' - zb) := by linear_combination hconv'
  have hTT : 0 < T0 * T5 := mul_pos hT0 hT5
  -- c > w: U T0 q < (T3 - S) T5 p;  c > w': S T5 p < (T6 - U) T0 q
  have e1 : T0 * T5 * (w - zb) < T0 * T5 * (c - zb) := mul_lt_mul_of_pos_left (by linarith) hTT
  have e1' : T5 * -(T3 * p) < T5 * (T0 * (w - zb)) := mul_lt_mul_of_pos_left hw hT5
  have A1 : U * T0 * q < (T3 - S) * T5 * p := by linear_combination e1 + e1' + hpl'
  have e2 : T0 * T5 * (w' - zb) < T0 * T5 * (c - zb) := mul_lt_mul_of_pos_left (by linarith) hTT
  have e2' : T0 * -(T6 * q) < T0 * (T5 * (w' - zb)) := mul_lt_mul_of_pos_left hw' hT0
  have A2 : S * T5 * p < (T6 - U) * T0 * q := by linear_combination e2 + e2' + hpl'
  have hUq : 0 < U * T0 * q := mul_pos (mul_pos hU hT0) hq0
  have hSp : 0 < S * T5 * p := mul_pos (mul_pos hS hT5) hp0
  by_cases h3 : T3 ≤ S
  · have : (T3 - S) * T5 * p ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (by linarith) hT5.le) hp0.le
    linarith
  rw [not_le] at h3
  by_cases h6 : T6 ≤ U
  · have : (T6 - U) * T0 * q ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (by linarith) hT0.le) hq0.le
    linarith
  rw [not_le] at h6
  -- multiply the two: S U (T5 p)(T0 q) < (T3 - S)(T6 - U) (T5 p)(T0 q)
  have m := mul_lt_mul'' A1 A2 hUq.le hSp.le
  have hPQ : 0 < (T5 * p) * (T0 * q) := mul_pos (mul_pos hT5 hp0) (mul_pos hT0 hq0)
  have key : (U * S) * ((T5 * p) * (T0 * q)) < ((T3 - S) * (T6 - U)) * ((T5 * p) * (T0 * q)) := by
    linear_combination m
  have := lt_of_mul_lt_mul_right key hPQ.le
  nlinarith

set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in
theorem cycles05_A3B6 {z0 z1 z2 z3 z4 z5 z6 t0 t3 t5 t6 s4 u4 : ℝ} (h12 : z1 < z2)
    (ht0 : 0 < t0) (ht3 : 0 < t3) (ht5 : 0 < t5) (ht6 : 0 < t6) (hs4 : 0 < s4) (hu4 : 0 < u4)
    (hP : t0 * t5 * (z4 - z1) = s4 * t5 * (z0 - z1) + u4 * t0 * (z5 - z1))
    (hC36 : (s4 * t6 + u4 * t3 - t3 * t6) * z2 + t3 * t6 * z4 ≥ s4 * t6 * z3 + u4 * t3 * z6)
    (hCAB : (s4 * t6 + u4 * t3 - t3 * t6) * z2 + t3 * t6 * z4 ≥ s4 * t6 * z3 + u4 * t3 * z6)
    (ht01 : t0 < t3) (ht56 : t5 < t6) (hch1 : (z0 - z1) * (t3 - t0) < (z3 - z0) * t0) (hch2 : (z5 - z1) * (t6 - t5) < (z6 - z5) * t5)
    (hch : t3 * t6 < s4 * t6 + u4 * t3) (hch36 : t3 * t6 < s4 * t6 + u4 * t3) :
    (∀ a b : Fin 4, (![z6, z2, z3, z4] : Fin 4 → ℝ) a < (![z6, z2, z3, z4] : Fin 4 → ℝ) (a - 1) → (![z6, z2, z3, z4] : Fin 4 → ℝ) a < (![z6, z2, z3, z4] : Fin 4 → ℝ) (a + 1) →
      (![z6, z2, z3, z4] : Fin 4 → ℝ) b < (![z6, z2, z3, z4] : Fin 4 → ℝ) (b - 1) → (![z6, z2, z3, z4] : Fin 4 → ℝ) b < (![z6, z2, z3, z4] : Fin 4 → ℝ) (b + 1) → a = b) ∨
    (∀ c d : Fin 6, (![z6, z5, z1, z0, z3, z4] : Fin 6 → ℝ) (c - 1) < (![z6, z5, z1, z0, z3, z4] : Fin 6 → ℝ) c → (![z6, z5, z1, z0, z3, z4] : Fin 6 → ℝ) (c + 1) < (![z6, z5, z1, z0, z3, z4] : Fin 6 → ℝ) c →
      (![z6, z5, z1, z0, z3, z4] : Fin 6 → ℝ) (d - 1) < (![z6, z5, z1, z0, z3, z4] : Fin 6 → ℝ) d → (![z6, z5, z1, z0, z3, z4] : Fin 6 → ℝ) (d + 1) < (![z6, z5, z1, z0, z3, z4] : Fin 6 → ℝ) d → c = d) := by
  have hT36 : 0 < t3 * t6 := mul_pos ht3 ht6
  have hTAB : 0 < t3 * t6 := mul_pos ht3 ht6
  have Fclaim : z2 < z3 → z2 < z6 → z0 < z1 → z5 < z1 → False := fun h3 h6 h0 h5 => by
    have := plane_below ht0 ht5 hs4 hu4 hP h0 h5
    have := sheet_up hT36 (mul_pos hs4 ht6) (mul_pos hu4 ht3) hC36 h3 h6
    linarith
  have Fi : z3 < z4 → z6 < z4 → z0 < z1 → z5 < z1 → False := fun ha hb h0 h5 =>
    plane_both ht0 ht5 hs4 hu4 ht01 ht56 hP hch1 hch2 hch36 h0 h5 ha hb
  have Fii : z4 < z3 → z4 < z6 → z2 < z3 → z2 < z6 → False := fun ha hb h3 h6 =>
    sheet_contra hTAB (mul_pos hs4 ht6) (mul_pos hu4 ht3) hch hCAB
      (sheet_up hT36 (mul_pos hs4 ht6) (mul_pos hu4 ht3) hC36 h3 h6) ha hb
  have Fc1 : z1 < z0 → z0 < z3 := fun h => by
    by_contra h'
    have : 0 < (z0 - z1) * (t3 - t0) := mul_pos (by linarith) (by linarith)
    have : (z3 - z0) * t0 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) ht0.le
    linarith
  have Fc2 : z1 < z5 → z5 < z6 := fun h => by
    by_contra h'
    have : 0 < (z5 - z1) * (t6 - t5) := mul_pos (by linarith) (by linarith)
    have : (z6 - z5) * t5 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) ht5.le
    linarith
  clear hP hC36 hCAB hch1 hch2 hch hch36 ht0 ht3 ht5 ht6 hs4 hu4 ht01 ht56 hT36 hTAB
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
theorem cycles05_A0B6 {z0 z1 z2 z3 z4 z5 z6 t0 t3 t5 t6 s4 u4 : ℝ} (h12 : z1 < z2)
    (ht0 : 0 < t0) (ht3 : 0 < t3) (ht5 : 0 < t5) (ht6 : 0 < t6) (hs4 : 0 < s4) (hu4 : 0 < u4)
    (hP : t0 * t5 * (z4 - z1) = s4 * t5 * (z0 - z1) + u4 * t0 * (z5 - z1))
    (hC36 : (s4 * t6 + u4 * t3 - t3 * t6) * z2 + t3 * t6 * z4 ≥ s4 * t6 * z3 + u4 * t3 * z6)
    (hCAB : (s4 * t6 + u4 * t0 - t0 * t6) * z2 + t0 * t6 * z4 ≥ s4 * t6 * z0 + u4 * t0 * z6)
    (ht01 : t3 < t0) (ht56 : t5 < t6) (hch1 : (z0 - z3) * t3 < (z3 - z2) * (t0 - t3)) (hch2 : (z5 - z1) * (t6 - t5) < (z6 - z5) * t5)
    (hch : t0 * t6 < s4 * t6 + u4 * t0) (hch36 : t3 * t6 < s4 * t6 + u4 * t3) :
    (∀ a b : Fin 5, (![z6, z2, z3, z0, z4] : Fin 5 → ℝ) a < (![z6, z2, z3, z0, z4] : Fin 5 → ℝ) (a - 1) → (![z6, z2, z3, z0, z4] : Fin 5 → ℝ) a < (![z6, z2, z3, z0, z4] : Fin 5 → ℝ) (a + 1) →
      (![z6, z2, z3, z0, z4] : Fin 5 → ℝ) b < (![z6, z2, z3, z0, z4] : Fin 5 → ℝ) (b - 1) → (![z6, z2, z3, z0, z4] : Fin 5 → ℝ) b < (![z6, z2, z3, z0, z4] : Fin 5 → ℝ) (b + 1) → a = b) ∨
    (∀ c d : Fin 5, (![z6, z5, z1, z0, z4] : Fin 5 → ℝ) (c - 1) < (![z6, z5, z1, z0, z4] : Fin 5 → ℝ) c → (![z6, z5, z1, z0, z4] : Fin 5 → ℝ) (c + 1) < (![z6, z5, z1, z0, z4] : Fin 5 → ℝ) c →
      (![z6, z5, z1, z0, z4] : Fin 5 → ℝ) (d - 1) < (![z6, z5, z1, z0, z4] : Fin 5 → ℝ) d → (![z6, z5, z1, z0, z4] : Fin 5 → ℝ) (d + 1) < (![z6, z5, z1, z0, z4] : Fin 5 → ℝ) d → c = d) := by
  have hT36 : 0 < t3 * t6 := mul_pos ht3 ht6
  have hTAB : 0 < t0 * t6 := mul_pos ht0 ht6
  have Fclaim : z2 < z3 → z2 < z6 → z0 < z1 → z5 < z1 → False := fun h3 h6 h0 h5 => by
    have := plane_below ht0 ht5 hs4 hu4 hP h0 h5
    have := sheet_up hT36 (mul_pos hs4 ht6) (mul_pos hu4 ht3) hC36 h3 h6
    linarith
  have Fi : z6 < z4 → z0 < z4 → z0 < z1 → z5 < z1 → False := fun ha hb h0 h5 =>
    plane_mixed (T0 := t5) (T1 := t6) (T5 := t0) (S := u4) (U := s4) (zb := z1) (x := z5)
      (y := z0) (w := z6) (c := z4) ht5 ht0 hu4 hs4 ht56 (by linear_combination hP) hch2
      (by linarith) h5 h0 ha hb
  have Fii : z4 < z0 → z4 < z6 → z2 < z3 → z2 < z6 → False := fun ha hb h3 h6 =>
    sheet_contra hTAB (mul_pos hs4 ht6) (mul_pos hu4 ht0) hch hCAB
      (sheet_up hT36 (mul_pos hs4 ht6) (mul_pos hu4 ht3) hC36 h3 h6) ha hb
  have Fc1 : z3 < z2 → z0 < z3 := fun h => by
    by_contra h'
    have : (z3 - z2) * (t0 - t3) < 0 := mul_neg_of_neg_of_pos (by linarith) (by linarith)
    have : 0 ≤ (z0 - z3) * t3 := mul_nonneg (by linarith) ht3.le
    linarith
  have Fc2 : z1 < z5 → z5 < z6 := fun h => by
    by_contra h'
    have : 0 < (z5 - z1) * (t6 - t5) := mul_pos (by linarith) (by linarith)
    have : (z6 - z5) * t5 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) ht5.le
    linarith
  clear hP hC36 hCAB hch1 hch2 hch hch36 ht0 ht3 ht5 ht6 hs4 hu4 ht01 ht56 hT36 hTAB
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
theorem cycles05_A3B5 {z0 z1 z2 z3 z4 z5 z6 t0 t3 t5 t6 s4 u4 : ℝ} (h12 : z1 < z2)
    (ht0 : 0 < t0) (ht3 : 0 < t3) (ht5 : 0 < t5) (ht6 : 0 < t6) (hs4 : 0 < s4) (hu4 : 0 < u4)
    (hP : t0 * t5 * (z4 - z1) = s4 * t5 * (z0 - z1) + u4 * t0 * (z5 - z1))
    (hC36 : (s4 * t6 + u4 * t3 - t3 * t6) * z2 + t3 * t6 * z4 ≥ s4 * t6 * z3 + u4 * t3 * z6)
    (hCAB : (s4 * t5 + u4 * t3 - t3 * t5) * z2 + t3 * t5 * z4 ≥ s4 * t5 * z3 + u4 * t3 * z5)
    (ht01 : t0 < t3) (ht56 : t6 < t5) (hch1 : (z0 - z1) * (t3 - t0) < (z3 - z0) * t0) (hch2 : (z5 - z6) * t6 < (z6 - z2) * (t5 - t6))
    (hch : t3 * t5 < s4 * t5 + u4 * t3) (hch36 : t3 * t6 < s4 * t6 + u4 * t3) :
    (∀ a b : Fin 5, (![z5, z6, z2, z3, z4] : Fin 5 → ℝ) a < (![z5, z6, z2, z3, z4] : Fin 5 → ℝ) (a - 1) → (![z5, z6, z2, z3, z4] : Fin 5 → ℝ) a < (![z5, z6, z2, z3, z4] : Fin 5 → ℝ) (a + 1) →
      (![z5, z6, z2, z3, z4] : Fin 5 → ℝ) b < (![z5, z6, z2, z3, z4] : Fin 5 → ℝ) (b - 1) → (![z5, z6, z2, z3, z4] : Fin 5 → ℝ) b < (![z5, z6, z2, z3, z4] : Fin 5 → ℝ) (b + 1) → a = b) ∨
    (∀ c d : Fin 5, (![z5, z1, z0, z3, z4] : Fin 5 → ℝ) (c - 1) < (![z5, z1, z0, z3, z4] : Fin 5 → ℝ) c → (![z5, z1, z0, z3, z4] : Fin 5 → ℝ) (c + 1) < (![z5, z1, z0, z3, z4] : Fin 5 → ℝ) c →
      (![z5, z1, z0, z3, z4] : Fin 5 → ℝ) (d - 1) < (![z5, z1, z0, z3, z4] : Fin 5 → ℝ) d → (![z5, z1, z0, z3, z4] : Fin 5 → ℝ) (d + 1) < (![z5, z1, z0, z3, z4] : Fin 5 → ℝ) d → c = d) := by
  have hT36 : 0 < t3 * t6 := mul_pos ht3 ht6
  have hTAB : 0 < t3 * t5 := mul_pos ht3 ht5
  have Fclaim : z2 < z3 → z2 < z6 → z0 < z1 → z5 < z1 → False := fun h3 h6 h0 h5 => by
    have := plane_below ht0 ht5 hs4 hu4 hP h0 h5
    have := sheet_up hT36 (mul_pos hs4 ht6) (mul_pos hu4 ht3) hC36 h3 h6
    linarith
  have Fi : z3 < z4 → z5 < z4 → z0 < z1 → z5 < z1 → False := fun ha hb h0 h5 =>
    plane_mixed ht0 ht5 hs4 hu4 ht01 hP hch1 hch h0 h5 ha hb
  have Fii : z4 < z3 → z4 < z5 → z2 < z3 → z2 < z6 → False := fun ha hb h3 h6 =>
    sheet_contra hTAB (mul_pos hs4 ht5) (mul_pos hu4 ht3) hch hCAB
      (sheet_up hT36 (mul_pos hs4 ht6) (mul_pos hu4 ht3) hC36 h3 h6) ha hb
  have Fc1 : z1 < z0 → z0 < z3 := fun h => by
    by_contra h'
    have : 0 < (z0 - z1) * (t3 - t0) := mul_pos (by linarith) (by linarith)
    have : (z3 - z0) * t0 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) ht0.le
    linarith
  have Fc2 : z6 < z2 → z5 < z6 := fun h => by
    by_contra h'
    have : (z6 - z2) * (t5 - t6) < 0 := mul_neg_of_neg_of_pos (by linarith) (by linarith)
    have : 0 ≤ (z5 - z6) * t6 := mul_nonneg (by linarith) ht6.le
    linarith
  clear hP hC36 hCAB hch1 hch2 hch hch36 ht0 ht3 ht5 ht6 hs4 hu4 ht01 ht56 hT36 hTAB
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
theorem cycles05_A0B5 {z0 z1 z2 z3 z4 z5 z6 t0 t3 t5 t6 s4 u4 : ℝ} (h12 : z1 < z2)
    (ht0 : 0 < t0) (ht3 : 0 < t3) (ht5 : 0 < t5) (ht6 : 0 < t6) (hs4 : 0 < s4) (hu4 : 0 < u4)
    (hP : t0 * t5 * (z4 - z1) = s4 * t5 * (z0 - z1) + u4 * t0 * (z5 - z1))
    (hC36 : (s4 * t6 + u4 * t3 - t3 * t6) * z2 + t3 * t6 * z4 ≥ s4 * t6 * z3 + u4 * t3 * z6)
    (hCAB : (s4 * t5 + u4 * t0 - t0 * t5) * z2 + t0 * t5 * z4 ≥ s4 * t5 * z0 + u4 * t0 * z5)
    (ht01 : t3 < t0) (ht56 : t6 < t5) (hch1 : (z0 - z3) * t3 < (z3 - z2) * (t0 - t3)) (hch2 : (z5 - z6) * t6 < (z6 - z2) * (t5 - t6))
    (hch : t0 * t5 < s4 * t5 + u4 * t0) (hch36 : t3 * t6 < s4 * t6 + u4 * t3) :
    (∀ a b : Fin 6, (![z5, z6, z2, z3, z0, z4] : Fin 6 → ℝ) a < (![z5, z6, z2, z3, z0, z4] : Fin 6 → ℝ) (a - 1) → (![z5, z6, z2, z3, z0, z4] : Fin 6 → ℝ) a < (![z5, z6, z2, z3, z0, z4] : Fin 6 → ℝ) (a + 1) →
      (![z5, z6, z2, z3, z0, z4] : Fin 6 → ℝ) b < (![z5, z6, z2, z3, z0, z4] : Fin 6 → ℝ) (b - 1) → (![z5, z6, z2, z3, z0, z4] : Fin 6 → ℝ) b < (![z5, z6, z2, z3, z0, z4] : Fin 6 → ℝ) (b + 1) → a = b) ∨
    (∀ c d : Fin 4, (![z5, z1, z0, z4] : Fin 4 → ℝ) (c - 1) < (![z5, z1, z0, z4] : Fin 4 → ℝ) c → (![z5, z1, z0, z4] : Fin 4 → ℝ) (c + 1) < (![z5, z1, z0, z4] : Fin 4 → ℝ) c →
      (![z5, z1, z0, z4] : Fin 4 → ℝ) (d - 1) < (![z5, z1, z0, z4] : Fin 4 → ℝ) d → (![z5, z1, z0, z4] : Fin 4 → ℝ) (d + 1) < (![z5, z1, z0, z4] : Fin 4 → ℝ) d → c = d) := by
  have hT36 : 0 < t3 * t6 := mul_pos ht3 ht6
  have hTAB : 0 < t0 * t5 := mul_pos ht0 ht5
  have Fclaim : z2 < z3 → z2 < z6 → z0 < z1 → z5 < z1 → False := fun h3 h6 h0 h5 => by
    have := plane_below ht0 ht5 hs4 hu4 hP h0 h5
    have := sheet_up hT36 (mul_pos hs4 ht6) (mul_pos hu4 ht3) hC36 h3 h6
    linarith
  have Fi : z0 < z4 → z5 < z4 → z0 < z1 → z5 < z1 → False := fun ha hb h0 h5 =>
    plane_far ht0 ht5 hs4 hu4 hP hch h0 h5 ha hb
  have Fii : z4 < z0 → z4 < z5 → z2 < z3 → z2 < z6 → False := fun ha hb h3 h6 =>
    sheet_contra hTAB (mul_pos hs4 ht5) (mul_pos hu4 ht0) hch hCAB
      (sheet_up hT36 (mul_pos hs4 ht6) (mul_pos hu4 ht3) hC36 h3 h6) ha hb
  have Fc1 : z3 < z2 → z0 < z3 := fun h => by
    by_contra h'
    have : (z3 - z2) * (t0 - t3) < 0 := mul_neg_of_neg_of_pos (by linarith) (by linarith)
    have : 0 ≤ (z0 - z3) * t3 := mul_nonneg (by linarith) ht3.le
    linarith
  have Fc2 : z6 < z2 → z5 < z6 := fun h => by
    by_contra h'
    have : (z6 - z2) * (t5 - t6) < 0 := mul_neg_of_neg_of_pos (by linarith) (by linarith)
    have : 0 ≤ (z5 - z6) * t6 := mul_nonneg (by linarith) ht6.le
    linarith
  clear hP hC36 hCAB hch1 hch2 hch hch36 ht0 ht3 ht5 ht6 hs4 hu4 ht01 ht56 hT36 hTAB
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

end Minimality
