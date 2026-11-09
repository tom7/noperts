module

public import Mathlib
public import MinimalityExtra
public import Minimality.SilS0XA
public import Minimality.Type20Bridge

/-!
# The quad-edge lemma

Proof of `QuadEdgeLemma` and `QuadEdgeLemmaStrict` of `MinimalityExtra.lean`. The algebra is done on
the six depths of the points along the view: A case analysis over their order, where each case is
closed by a positive combination of the order relations and the two linear dependencies among the
points (`bip_eq` is the weighted-averages fact behind the combinations; `c4_fail` and `c5_fail` list
the ways a 4-cycle and a 5-cycle can have a weak alternation). The last theorems translate this to
points and directions.
-/

@[expose] public section

open Matrix Minimality Minimality.H21

namespace QE

section Bip
/-- Complete bipartite flow: if weighted averages of "high" values and "low" values agree (equal
total weight) and every high is at least every low, then all of them are equal. -/
theorem bip_eq {ι κ : Type*} [Fintype ι] [Fintype κ] (p : ι → ℝ) (q : κ → ℝ) (x : ι → ℝ) (y : κ → ℝ)
    (hp : ∀ i, 0 < p i) (hq : ∀ j, 0 < q j) (hs : ∑ i, p i = ∑ j, q j)
    (he : ∑ i, p i * x i = ∑ j, q j * y j) (hxy : ∀ i j, y j ≤ x i) : ∀ i j, x i = y j := by
  have key : ∑ i, ∑ j, p i * q j * (x i - y j) = 0 := by
    have inner : ∀ i, ∑ j, p i * q j * (x i - y j) = p i * x i * (∑ j, q j) - p i * (∑ j, q j * y j) := by
      intro i
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    have : ∑ i, ∑ j, p i * q j * (x i - y j)
        = (∑ j, q j) * (∑ i, p i * x i) - (∑ i, p i) * (∑ j, q j * y j) := by
      rw [Finset.sum_congr rfl fun i _ => inner i, Finset.sum_sub_distrib, ← Finset.sum_mul,
        ← Finset.sum_mul]
      ring
    rw [this, he, ← hs]; ring
  have hnn : ∀ i, 0 ≤ ∑ j, p i * q j * (x i - y j) := fun i =>
    Finset.sum_nonneg fun j _ => mul_nonneg (mul_nonneg (hp i).le (hq j).le) (sub_nonneg.2 (hxy i j))
  have h1 := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hnn i).1 key
  intro i j
  have h2 := (Finset.sum_eq_zero_iff_of_nonneg fun j _ =>
    mul_nonneg (mul_nonneg (hp i).le (hq j).le) (sub_nonneg.2 (hxy i j))).1 (h1 i (Finset.mem_univ _)) j (Finset.mem_univ _)
  have := mul_pos (hp i) (hq j)
  have h3 : x i - y j = 0 := by
    rcases mul_eq_zero.1 h2 with h | h
    · exact absurd h this.ne'
    · exact h
  linarith
end Bip

section Cyc
def c4 (a f c g : ℝ) : ZMod 4 → ℝ := ![a, f, c, g]
def c5 (b m f c g : ℝ) : ZMod 5 → ℝ := ![b, m, f, c, g]

theorem zmod4_sums : (((0:ZMod 4) + 1) = 1) ∧
    (((0:ZMod 4) + 2) = 2) ∧
    (((0:ZMod 4) + 3) = 3) ∧
    (((1:ZMod 4) + 1) = 2) ∧
    (((1:ZMod 4) + 2) = 3) ∧
    (((1:ZMod 4) + 3) = 0) ∧
    (((2:ZMod 4) + 1) = 3) ∧
    (((2:ZMod 4) + 2) = 0) ∧
    (((2:ZMod 4) + 3) = 1) ∧
    (((3:ZMod 4) + 1) = 0) ∧
    (((3:ZMod 4) + 2) = 1) ∧
    (((3:ZMod 4) + 3) = 2) := by decide

/-- Failure of `RobUni` on `(a,f,c,g)`: either `{a,c}` above `{f,g}` or the reverse. -/
theorem c4_fail {a f c g : ℝ} (h : ¬ RobUni (c4 a f c g)) :
    (f ≤ a ∧ f ≤ c ∧ g ≤ a ∧ g ≤ c) ∨ (a ≤ f ∧ a ≤ g ∧ c ≤ f ∧ c ≤ g) := by
  unfold RobUni at h
  push Not at h
  obtain ⟨B, b, c', d, hb, hbc, hcd, hd, h⟩ := h
  have hb1 : b = 1 := by omega
  have hc1 : c' = 2 := by omega
  have hd1 : d = 3 := by omega
  subst hb1 hc1 hd1
  have hB : B = 0 ∨ B = 1 ∨ B = 2 ∨ B = 3 := (by decide : ∀ B : ZMod 4, B = 0 ∨ B = 1 ∨ B = 2 ∨ B = 3) B
  obtain ⟨e01, e02, e03, e11, e12, e13, e21, e22, e23, e31, e32, e33⟩ := zmod4_sums
  rcases hB with rfl | rfl | rfl | rfl <;>
  · simp only [Nat.cast_ofNat, Nat.cast_one, e01, e02, e03, e11, e12, e13, e21, e22, e23, e31, e32, e33] at h
    simp [c4] at h
    first | (left; exact ⟨by linarith, by linarith, by linarith, by linarith⟩) | (right; exact ⟨by linarith, by linarith, by linarith, by linarith⟩)

theorem zmod5_sums_ : (((0:ZMod 5) + 1) = 1) ∧
    (((0:ZMod 5) + 2) = 2) ∧
    (((0:ZMod 5) + 3) = 3) ∧
    (((0:ZMod 5) + 4) = 4) ∧
    (((1:ZMod 5) + 1) = 2) ∧
    (((1:ZMod 5) + 2) = 3) ∧
    (((1:ZMod 5) + 3) = 4) ∧
    (((1:ZMod 5) + 4) = 0) ∧
    (((2:ZMod 5) + 1) = 3) ∧
    (((2:ZMod 5) + 2) = 4) ∧
    (((2:ZMod 5) + 3) = 0) ∧
    (((2:ZMod 5) + 4) = 1) ∧
    (((3:ZMod 5) + 1) = 4) ∧
    (((3:ZMod 5) + 2) = 0) ∧
    (((3:ZMod 5) + 3) = 1) ∧
    (((3:ZMod 5) + 4) = 2) ∧
    (((4:ZMod 5) + 1) = 0) ∧
    (((4:ZMod 5) + 2) = 1) ∧
    (((4:ZMod 5) + 3) = 2) ∧
    (((4:ZMod 5) + 4) = 3) := by decide

/-- Failure of `RobUni` on `(b,m,f,c,g)`: one of ten alternating cones. -/
theorem c5_fail {b m f c g : ℝ} (h : ¬ RobUni (c5 b m f c g)) :
    (f ≤ m ∧ f ≤ c ∧ g ≤ m ∧ g ≤ c) ∨
    (m ≤ f ∧ m ≤ g ∧ c ≤ f ∧ c ≤ g) ∨
    (f ≤ b ∧ f ≤ c ∧ g ≤ b ∧ g ≤ c) ∨
    (b ≤ f ∧ b ≤ g ∧ c ≤ f ∧ c ≤ g) ∨
    (m ≤ b ∧ m ≤ c ∧ g ≤ b ∧ g ≤ c) ∨
    (b ≤ m ∧ b ≤ g ∧ c ≤ m ∧ c ≤ g) ∨
    (m ≤ b ∧ m ≤ f ∧ g ≤ b ∧ g ≤ f) ∨
    (b ≤ m ∧ b ≤ g ∧ f ≤ m ∧ f ≤ g) ∨
    (m ≤ b ∧ m ≤ f ∧ c ≤ b ∧ c ≤ f) ∨
    (b ≤ m ∧ b ≤ c ∧ f ≤ m ∧ f ≤ c) := by
  unfold RobUni at h
  push Not at h
  obtain ⟨B, b', c', d, hb, hbc, hcd, hd, h⟩ := h
  have hB : B = 0 ∨ B = 1 ∨ B = 2 ∨ B = 3 ∨ B = 4 :=
    (by decide : ∀ B : ZMod 5, B = 0 ∨ B = 1 ∨ B = 2 ∨ B = 3 ∨ B = 4) B
  obtain ⟨e01, e02, e03, e04, e11, e12, e13, e14, e21, e22, e23, e24, e31, e32, e33, e34, e41, e42, e43, e44⟩ := zmod5_sums_
  have hb4 : b' < 5 := by omega
  have hc4 : c' < 5 := by omega
  interval_cases b' <;> interval_cases c' <;> (try omega) <;> interval_cases d  <;>
  rcases hB with rfl | rfl | rfl | rfl | rfl <;>
  · simp only [Nat.cast_ofNat, Nat.cast_one, e01, e02, e03, e04, e11, e12, e13, e14, e21, e22, e23, e24, e31, e32, e33, e34, e41, e42, e43, e44] at h
    simp [c5] at h
    first | (exact Or.inl ⟨by linarith, by linarith, by linarith, by linarith⟩) | (exact Or.inr (Or.inl ⟨by linarith, by linarith, by linarith, by linarith⟩)) | (exact Or.inr (Or.inr (Or.inl ⟨by linarith, by linarith, by linarith, by linarith⟩))) | (exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by linarith, by linarith, by linarith, by linarith⟩)))) | (exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by linarith, by linarith, by linarith, by linarith⟩))))) | (exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by linarith, by linarith, by linarith, by linarith⟩)))))) | (exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by linarith, by linarith, by linarith, by linarith⟩))))))) | (exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by linarith, by linarith, by linarith, by linarith⟩)))))))) | (exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by linarith, by linarith, by linarith, by linarith⟩))))))))) | (exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by linarith, by linarith, by linarith, by linarith⟩))))))))))
end Cyc

section Core1
theorem bip23 {p1 p2 q1 q2 q3 x1 x2 y1 y2 y3 : ℝ} (hp1 : 0 < p1) (hp2 : 0 < p2) (hq1 : 0 < q1)
    (hq2 : 0 < q2) (hq3 : 0 < q3) (hs : p1 + p2 = q1 + q2 + q3)
    (he : p1 * x1 + p2 * x2 = q1 * y1 + q2 * y2 + q3 * y3)
    (h11 : y1 ≤ x1) (h12 : y2 ≤ x1) (h13 : y3 ≤ x1) (h21 : y1 ≤ x2) (h22 : y2 ≤ x2) (h23 : y3 ≤ x2) :
    x1 = y1 ∧ x1 = y2 ∧ x1 = y3 ∧ x2 = y1 ∧ x2 = y2 ∧ x2 = y3 := by
  have := bip_eq (ι := Fin 2) (κ := Fin 3) ![p1, p2] ![q1, q2, q3] ![x1, x2] ![y1, y2, y3]
    (by intro i; fin_cases i <;> simpa) (by intro j; fin_cases j <;> simpa)
    (by simpa [Fin.sum_univ_succ, add_assoc] using hs) (by simpa [Fin.sum_univ_succ, add_assoc] using he)
    (by intro i j; fin_cases i <;> fin_cases j <;> simpa)
  exact ⟨this 0 0, this 0 1, this 0 2, this 1 0, this 1 1, this 1 2⟩

theorem bip32 {p1 p2 p3 q1 q2 x1 x2 x3 y1 y2 : ℝ} (hp1 : 0 < p1) (hp2 : 0 < p2) (hp3 : 0 < p3)
    (hq1 : 0 < q1) (hq2 : 0 < q2) (hs : p1 + p2 + p3 = q1 + q2)
    (he : p1 * x1 + p2 * x2 + p3 * x3 = q1 * y1 + q2 * y2)
    (h11 : y1 ≤ x1) (h12 : y2 ≤ x1) (h21 : y1 ≤ x2) (h22 : y2 ≤ x2) (h31 : y1 ≤ x3) (h32 : y2 ≤ x3) :
    x1 = y1 ∧ x1 = y2 ∧ x2 = y1 ∧ x2 = y2 ∧ x3 = y1 ∧ x3 = y2 := by
  have := bip_eq (ι := Fin 3) (κ := Fin 2) ![p1, p2, p3] ![q1, q2] ![x1, x2, x3] ![y1, y2]
    (by intro i; fin_cases i <;> simpa) (by intro j; fin_cases j <;> simpa)
    (by simpa [Fin.sum_univ_succ, add_assoc] using hs) (by simpa [Fin.sum_univ_succ, add_assoc] using he)
    (by intro i j; fin_cases i <;> fin_cases j <;> simpa)
  exact ⟨this 0 0, this 0 1, this 1 0, this 1 1, this 2 0, this 2 1⟩

theorem bip22 {p1 p2 q1 q2 x1 x2 y1 y2 : ℝ} (hp1 : 0 < p1) (hp2 : 0 < p2) (hq1 : 0 < q1)
    (hq2 : 0 < q2) (hs : p1 + p2 = q1 + q2)
    (he : p1 * x1 + p2 * x2 = q1 * y1 + q2 * y2)
    (h11 : y1 ≤ x1) (h12 : y2 ≤ x1) (h21 : y1 ≤ x2) (h22 : y2 ≤ x2) :
    x1 = y1 ∧ x1 = y2 ∧ x2 = y1 ∧ x2 = y2 := by
  have := bip_eq (ι := Fin 2) (κ := Fin 2) ![p1, p2] ![q1, q2] ![x1, x2] ![y1, y2]
    (by intro i; fin_cases i <;> simpa) (by intro j; fin_cases j <;> simpa)
    (by simpa [Fin.sum_univ_succ] using hs) (by simpa [Fin.sum_univ_succ] using he)
    (by intro i j; fin_cases i <;> fin_cases j <;> simpa)
  exact ⟨this 0 0, this 0 1, this 1 0, this 1 1⟩
end Core1

section Core2
/-- Numeric data of the lemma: the Radon relation `E` (fg pierces abc) and the quad relation
(diagonals `am` and `bf` cross), applied to depths, together with `z_a < z_b`. -/
structure QS (a b m f c g : ℝ) where
  al : ℝ
  be : ℝ
  ga : ℝ
  s : ℝ
  t : ℝ
  u : ℝ
  hal : 0 < al
  hbe : 0 < be
  hga : 0 < ga
  hsum : al + be + ga = 1
  hs0 : 0 < s
  hs1 : s < 1
  ht0 : 0 < t
  ht1 : t < 1
  hu0 : 0 < u
  hu1 : u < 1
  r1 : al * a + be * b + ga * c = (1 - s) * f + s * g
  r0 : (1 - t) * a + t * m = (1 - u) * b + u * f
  hab : a < b

variable {a b m f c g : ℝ}

/-- `{a,c} ≥ {f,g}` is impossible (E, with `z_b > z_a`). -/
theorem kA (S : QS a b m f c g) (h1 : f ≤ a) (h2 : f ≤ c) (h3 : g ≤ a) (h4 : g ≤ c) : False := by
  obtain ⟨al, be, ga, s, t, u, hal, hbe, hga, hsum, hs0, hs1, ht0, ht1, hu0, hu1, r1, r0, hab⟩ := S
  have := bip32 (p1 := al) (p2 := be) (p3 := ga) (q1 := 1 - s) (q2 := s) (x1 := a) (x2 := b) (x3 := c)
    (y1 := f) (y2 := g) hal hbe hga (by linarith) hs0 (by linarith) r1 h1 h3 (by linarith) (by linarith) h2 h4
  obtain ⟨e1, -, e3, -⟩ := this
  linarith

/-- `{f,g} ≥ {a,b,c}` is impossible. -/
theorem kE (S : QS a b m f c g) (h1 : a ≤ f) (h2 : b ≤ f) (h3 : c ≤ f) (h4 : a ≤ g) (h5 : b ≤ g)
    (h6 : c ≤ g) : False := by
  obtain ⟨al, be, ga, s, t, u, hal, hbe, hga, hsum, hs0, hs1, ht0, ht1, hu0, hu1, r1, r0, hab⟩ := S
  have := bip23 (p1 := 1 - s) (p2 := s) (q1 := al) (q2 := be) (q3 := ga) (x1 := f) (x2 := g)
    (y1 := a) (y2 := b) (y3 := c) (by linarith) hs0 hal hbe hga (by linarith) (by linarith) h1 h2 h3 h4 h5 h6
  obtain ⟨e1, e2, -⟩ := this
  linarith

/-- `{b,f} ≥ {a,m}` is impossible (the quad relation, with `z_b > z_a`). -/
theorem kQ (S : QS a b m f c g) (h1 : a ≤ f) (h2 : m ≤ b) (h3 : m ≤ f) : False := by
  obtain ⟨al, be, ga, s, t, u, hal, hbe, hga, hsum, hs0, hs1, ht0, ht1, hu0, hu1, r1, r0, hab⟩ := S
  have := bip22 (p1 := 1 - u) (p2 := u) (q1 := 1 - t) (q2 := t) (x1 := b) (x2 := f) (y1 := a) (y2 := m)
    (by linarith) hu0 (by linarith) ht0 (by linarith) (by linarith) hab.le h2 h1 h3
  obtain ⟨e1, -⟩ := this
  linarith

/-- `{f,g} ≥ {a,c,m}` is impossible (E combined with the quad relation, which eliminates b). -/
theorem kB2 (S : QS a b m f c g) (h1 : a ≤ f) (h2 : c ≤ f) (h3 : m ≤ f) (h4 : a ≤ g) (h5 : c ≤ g)
    (h6 : m ≤ g) : False := by
  obtain ⟨al, be, ga, s, t, u, hal, hbe, hga, hsum, hs0, hs1, ht0, ht1, hu0, hu1, r1, r0, hab⟩ := S
  obtain rfl : ga = 1 - al - be := by linarith
  have hu' : 0 < 1 - u := by linarith
  have := bip23 (p1 := (1 - u) * (1 - s) + be * u) (p2 := (1 - u) * s)
    (q1 := (1 - u) * al + be * (1 - t)) (q2 := (1 - u) * (1 - al - be)) (q3 := be * t)
    (x1 := f) (x2 := g) (y1 := a) (y2 := c) (y3 := m)
    (by nlinarith [mul_pos hu' (sub_pos.2 hs1), mul_pos hbe hu0]) (mul_pos hu' hs0)
    (by nlinarith [mul_pos hu' hal, mul_pos hbe (sub_pos.2 ht1)]) (mul_pos hu' hga) (mul_pos hbe ht0)
    (by ring) (by linear_combination (-(1 - u)) * r1 - be * r0)
    h1 h2 h3 h4 h5 h6
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := this
  -- all equal: f = a = c = m, so r0 gives a = b
  have : (1 - u) * (b - a) = 0 := by
    have hm : m = a := by linarith
    have hf : f = a := by linarith
    rw [hm, hf] at r0
    linear_combination (-1) * r0
  have := mul_pos (show 0 < 1 - u by linarith) (sub_pos.2 hab)
  linarith
end Core2

section Core3
variable {a b m f c g : ℝ}

theorem zero_of_pos_mul {k d : ℝ} (hk : 0 < k) (h : k * d = 0) : d = 0 :=
  (mul_eq_zero.1 h).resolve_left hk.ne'

/-- The cone `B6` (`g ≥ a,b,c`, `f ≥ a,c`, `m ≥ b,c`) under `H1` (`be ≤ s`: b at least as far from the
plane acf as g).  It is empty unless `z_a = z_c = z_f`, which needs `be = s`. -/
theorem b6H1 (S : QS a b m f c g) (hgb : b ≤ g) (hgc : c ≤ g) (hfa : a ≤ f) (hfc : c ≤ f)
    (hH : S.be ≤ S.s) : (S.be < S.s → False) ∧ f = a ∧ f = c := by
  obtain ⟨al, be, ga, s, t, u, hal, hbe, hga, hsum, hs0, hs1, ht0, ht1, hu0, hu1, r1, r0, hab⟩ := S
  simp only at hH ⊢
  obtain rfl : ga = 1 - al - be := by linarith
  have hT : 0 < 1 - be := by linarith
  have hs' : 0 < 1 - s := by linarith
  have hz : (1 - be) * be * (g - b) + (1 - s) * al * (f - a) + (1 - s) * (1 - al - be) * (f - c)
      + (s - be) * al * (g - a) + (s - be) * (1 - al - be) * (g - c) = 0 := by
    linear_combination (-(1 - be)) * r1
  have t1 : 0 ≤ (1 - be) * be * (g - b) := mul_nonneg (mul_nonneg hT.le hbe.le) (by linarith)
  have t2 : 0 ≤ (1 - s) * al * (f - a) := mul_nonneg (mul_nonneg hs'.le hal.le) (by linarith)
  have t3 : 0 ≤ (1 - s) * (1 - al - be) * (f - c) := mul_nonneg (mul_nonneg hs'.le hga.le) (by linarith)
  have t4 : 0 ≤ (s - be) * al * (g - a) := mul_nonneg (mul_nonneg (by linarith) hal.le) (by linarith)
  have t5 : 0 ≤ (s - be) * (1 - al - be) * (g - c) := mul_nonneg (mul_nonneg (by linarith) hga.le) (by linarith)
  have e2 : f - a = 0 := zero_of_pos_mul (mul_pos hs' hal) (by linarith)
  have e3 : f - c = 0 := zero_of_pos_mul (mul_pos hs' hga) (by linarith)
  refine ⟨fun hlt => ?_, by linarith, by linarith⟩
  have e1 : g - b = 0 := zero_of_pos_mul (mul_pos hT hbe) (by linarith)
  have e4 : g - a = 0 := zero_of_pos_mul (mul_pos (sub_pos.2 hlt) hal) (by linarith)
  linarith
end Core3

section Core4
variable {a b m f c g : ℝ}

/-- The cone `B6` under `H2` (`(1-t)((1-s)-ga) ≤ al u`: c is no higher than f over the plane bgm).
It is empty unless `z_b = z_g = z_m`, which needs equality in `H2`. -/
theorem b6H2 (S : QS a b m f c g) (hgb : b ≤ g) (hgc : c ≤ g) (hfc : c ≤ f)
    (hmb : b ≤ m) (hmc : c ≤ m)
    (hH : (1 - S.t) * ((1 - S.s) - S.ga) ≤ S.al * S.u) :
    ((1 - S.t) * ((1 - S.s) - S.ga) < S.al * S.u → False) ∧ b = g ∧ g = m := by
  obtain ⟨al, be, ga, s, t, u, hal, hbe, hga, hsum, hs0, hs1, ht0, ht1, hu0, hu1, r1, r0, hab⟩ := S
  simp only at hH ⊢
  obtain rfl : ga = 1 - al - be := by linarith
  have hs' : 0 < 1 - s := by linarith
  have ht' : 0 < 1 - t := by linarith
  have hu' : 0 < 1 - u := by linarith
  by_cases hi : (1 - s) * (1 - t) ≤ al * u
  · -- case (i): no hypothesis needed
    exfalso
    have hbd : 0 < u * be + (1 - s) * (1 - u) := by nlinarith [mul_pos hu0 hbe, mul_pos hs' hu']
    have hA : 0 ≤ u * al - (1 - s) * (1 - t) := by linarith
    rcases hA.lt_or_eq with hA | hA
    · have := bip23 (p1 := u * s) (p2 := (1 - s) * t) (q1 := u * al - (1 - s) * (1 - t))
        (q2 := u * be + (1 - s) * (1 - u)) (q3 := u * (1 - al - be)) (x1 := g) (x2 := m)
        (y1 := a) (y2 := b) (y3 := c) (mul_pos hu0 hs0) (mul_pos hs' ht0) hA hbd (mul_pos hu0 hga)
        (by ring) (by linear_combination (-u) * r1 + (1 - s) * r0)
        (by linarith) hgb hgc (by linarith) hmb hmc
      obtain ⟨e1, e2, -⟩ := this
      linarith
    · have := bip22 (p1 := u * s) (p2 := (1 - s) * t) (q1 := u * be + (1 - s) * (1 - u))
        (q2 := u * (1 - al - be)) (x1 := g) (x2 := m) (y1 := b) (y2 := c) (mul_pos hu0 hs0)
        (mul_pos hs' ht0) hbd (mul_pos hu0 hga) (by linear_combination (-1) * hA)
        (by linear_combination (-u) * r1 + (1 - s) * r0 + (-a) * hA) hgb hgc hmb hmc
      obtain ⟨e1, e2, e3, e4⟩ := this
      -- g = b = c = m, f ≥ c, r1 gives al (a - b) = (1-s)(f - b)
      have h1 : al * (a - b) = (1 - s) * (f - b) := by
        have hgb' : g = b := e1
        have hcb : c = b := by linarith
        rw [hgb', hcb] at r1
        linear_combination r1
      have h2 : 0 ≤ (1 - s) * (f - b) := mul_nonneg hs'.le (by linarith)
      have h3 : 0 < al * (b - a) := mul_pos hal (sub_pos.2 hab)
      linarith
  · -- case (ii)
    push Not at hi
    set F := (1 - t) * (1 - s) - al * u with hF
    have hFp : 0 < F := by rw [hF]; linarith
    set G := (1 - t) * s with hG
    set M := al * t with hM
    set db := (1 - t) * be + al * (1 - u) with hdb
    set c' := (1 - t) * (1 - al - be) - F with hc'
    have hGp : 0 < G := mul_pos ht' hs0
    have hMp : 0 < M := mul_pos hal ht0
    have hdbp : 0 < db := by rw [hdb]; nlinarith [mul_pos ht' hbe, mul_pos hal hu']
    have hc'0 : 0 ≤ c' := by rw [hc', hF]; nlinarith
    have hz : (G + M) * F * (f - c) + G * db * (g - b) + G * c' * (g - c) + M * db * (m - b)
        + M * c' * (m - c) = 0 := by
      rw [hG, hM, hdb, hc', hF]
      linear_combination (-((1 - t) * s + al * t) * (1 - t)) * r1 + ((1 - t) * s + al * t) * al * r0
    have hcp : (1 - t) * ((1 - s) - (1 - al - be)) < al * u → 0 < c' := by
      intro hlt; rw [hc', hF]; nlinarith
    clear_value F G M db c'
    clear hF hG hM hdb hc'
    have t1 : 0 ≤ (G + M) * F * (f - c) := mul_nonneg (mul_nonneg (add_pos hGp hMp).le hFp.le) (by linarith)
    have t2 : 0 ≤ G * db * (g - b) := mul_nonneg (mul_nonneg hGp.le hdbp.le) (by linarith)
    have t3 : 0 ≤ G * c' * (g - c) := mul_nonneg (mul_nonneg hGp.le hc'0) (by linarith)
    have t4 : 0 ≤ M * db * (m - b) := mul_nonneg (mul_nonneg hMp.le hdbp.le) (by linarith)
    have t5 : 0 ≤ M * c' * (m - c) := mul_nonneg (mul_nonneg hMp.le hc'0) (by linarith)
    have e1 : f - c = 0 := zero_of_pos_mul (mul_pos (add_pos hGp hMp) hFp) (by linarith)
    have e2 : g - b = 0 := zero_of_pos_mul (mul_pos hGp hdbp) (by linarith)
    have e4 : m - b = 0 := zero_of_pos_mul (mul_pos hMp hdbp) (by linarith)
    refine ⟨fun hlt => ?_, by linarith, by linarith⟩
    have e3 : g - c = 0 := zero_of_pos_mul (mul_pos hGp (hcp hlt)) (by linarith)
    have hfb : f = b := by linarith
    have hmb' : m = b := by linarith
    rw [hfb, hmb'] at r0
    have : (1 - t) * (b - a) = 0 := by linear_combination (-1) * r0
    have := mul_pos ht' (sub_pos.2 hab)
    linarith
end Core4

section Core5
variable {a b m f c g : ℝ}

/-- Shared skeleton: all tuples are killed except `B6` and the tie `z_c = z_f = z_g`. -/
theorem core_main (S : QS a b m f c g) (Q : Prop)
    (hB6 : b ≤ g → c ≤ g → a ≤ f → c ≤ f → b ≤ m → c ≤ m → Q)
    (htie : c = f ∧ f = g → Q) :
    RobUni (c4 a f c g) ∨ RobUni (c5 b m f c g) ∨ Q := by
  by_cases h4 : RobUni (c4 a f c g)
  · exact Or.inl h4
  by_cases h5 : RobUni (c5 b m f c g)
  · exact Or.inr (Or.inl h5)
  right; right
  have hab := S.hab
  rcases c4_fail h4 with ⟨h1, h2, h3, h4'⟩ | ⟨hfa, hga, hfc, hgc⟩
  · exact (kA S h1 h2 h3 h4').elim
  rcases c5_fail h5 with
    ⟨x1, x2, x3, x4⟩ | ⟨x1, x2, x3, x4⟩ | ⟨x1, x2, x3, x4⟩ | ⟨x1, x2, x3, x4⟩ | ⟨x1, x2, x3, x4⟩ |
    ⟨x1, x2, x3, x4⟩ | ⟨x1, x2, x3, x4⟩ | ⟨x1, x2, x3, x4⟩ | ⟨x1, x2, x3, x4⟩ | ⟨x1, x2, x3, x4⟩
  · exact htie ⟨by linarith, by linarith⟩
  · exact (kB2 S hfa hfc x1 hga hgc x2).elim
  · exact htie ⟨by linarith, by linarith⟩
  · exact (kE S hfa x1 x3 hga x2 x4).elim
  · exact (kQ S hfa x1 (by linarith)).elim
  · exact hB6 x2 x4 hfa hfc x1 x3
  · exact (kQ S hfa x1 x2).elim
  · exact hB6 x2 (by linarith) hfa hfc x1 (by linarith)
  · exact (kQ S hfa x1 x2).elim
  · exact (kE S hfa (by linarith) hfc hga (by linarith) hgc).elim

/-- **Numeric core of the quad-edge lemma.**  Up to the three tie alternatives. -/
theorem core (S : QS a b m f c g)
    (hH : S.be ≤ S.s ∨ (1 - S.t) * ((1 - S.s) - S.ga) ≤ S.al * S.u) :
    RobUni (c4 a f c g) ∨ RobUni (c5 b m f c g) ∨
      ((c = f ∧ f = g) ∨ (a = c ∧ c = f) ∨ (b = g ∧ g = m)) := by
  refine core_main S _ (fun hgb hgc hfa hfc hmb hmc => ?_) (fun h => Or.inl h)
  rcases hH with h | h
  · obtain ⟨-, e1, e2⟩ := b6H1 S hgb hgc hfa hfc h
    exact Or.inr (Or.inl ⟨by linarith, by linarith⟩)
  · obtain ⟨-, e1, e2⟩ := b6H2 S hgb hgc hfc hmb hmc h
    exact Or.inr (Or.inr ⟨e1, e2⟩)

/-- **Numeric core, strict form**: with strict `H1` or `H2` the only exception is `z_c = z_f = z_g`. -/
theorem core_strict (S : QS a b m f c g)
    (hH : S.be < S.s ∨ (1 - S.t) * ((1 - S.s) - S.ga) < S.al * S.u) (hne : ¬ (c = f ∧ f = g)) :
    RobUni (c4 a f c g) ∨ RobUni (c5 b m f c g) := by
  have key := core_main S (c = f ∧ f = g) (fun hgb hgc hfa hfc hmb hmc => by
    rcases hH with h | h
    · exact ((b6H1 S hgb hgc hfa hfc h.le).1 h).elim
    · exact ((b6H2 S hgb hgc hfc hmb hmc h.le).1 h).elim) id
  rcases key with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact (hne h).elim
end Core5

theorem cyc4_eq (w a f c g : Fin 3 → ℝ) :
    (fun i : ZMod 4 => w ⬝ᵥ (![a, f, c, g] : ZMod 4 → Fin 3 → ℝ) i) = c4 (w ⬝ᵥ a) (w ⬝ᵥ f) (w ⬝ᵥ c) (w ⬝ᵥ g) := by
  funext i
  fin_cases i <;> rfl

theorem cyc5_eq (w b m f c g : Fin 3 → ℝ) :
    (fun i : ZMod 5 => w ⬝ᵥ (![b, m, f, c, g] : ZMod 5 → Fin 3 → ℝ) i)
      = c5 (w ⬝ᵥ b) (w ⬝ᵥ m) (w ⬝ᵥ f) (w ⬝ᵥ c) (w ⬝ᵥ g) := by
  funext i
  fin_cases i <;> rfl

/-- The two depth relations and the depth of `b` over `a`, as a `QS`. -/
def mkQS {a b m f c g : Fin 3 → ℝ} {w : Fin 3 → ℝ} {p q r s t u : ℝ}
    (hp : 0 < p) (hq0 : 0 < q) (hr : 0 < r) (hsum : p + q + r = 1) (hs0 : 0 < s) (hs1 : s < 1)
    (ht0 : 0 < t) (ht1 : t < 1) (hu0 : 0 < u) (hu1 : u < 1)
    (hQ : (1 - t) • a + t • m = (1 - u) • b + u • f)
    (hE : p • a + q • b + r • c = (1 - s) • f + s • g) (hw : 0 < w ⬝ᵥ (b - a)) :
    QS (w ⬝ᵥ a) (w ⬝ᵥ b) (w ⬝ᵥ m) (w ⬝ᵥ f) (w ⬝ᵥ c) (w ⬝ᵥ g) :=
  have r0 := congrArg (fun x => w ⬝ᵥ x) hQ
  have r1 := congrArg (fun x => w ⬝ᵥ x) hE
  have r0' : (1 - t) * (w ⬝ᵥ a) + t * (w ⬝ᵥ m) = (1 - u) * (w ⬝ᵥ b) + u * (w ⬝ᵥ f) := by
    simpa only [dotProduct_add, dotProduct_smul, smul_eq_mul] using r0
  have r1' : p * (w ⬝ᵥ a) + q * (w ⬝ᵥ b) + r * (w ⬝ᵥ c) = (1 - s) * (w ⬝ᵥ f) + s * (w ⬝ᵥ g) := by
    simpa only [dotProduct_add, dotProduct_smul, smul_eq_mul] using r1
  have hw' : w ⬝ᵥ a < w ⬝ᵥ b := by rw [dotProduct_sub] at hw; linarith
  ⟨p, q, r, s, t, u, hp, hq0, hr, hsum, hs0, hs1, ht0, ht1, hu0, hu1, r1', r0', hw'⟩

/-- `H1` gives `be ≤ s`. -/
theorem h1_le {a b c f g : Fin 3 → ℝ} {p q r s : ℝ} (hq0 : 0 < q) (hsum : p + q + r = 1)
    (hE : p • a + q • b + r • c = (1 - s) • f + s • g) {n : Fin 3 → ℝ} {k : ℝ}
    (ha : n ⬝ᵥ a = k) (hc : n ⬝ᵥ c = k) (hf : n ⬝ᵥ f = k) (hk : k < n ⬝ᵥ g) (hgb : n ⬝ᵥ g ≤ n ⬝ᵥ b) :
    (q ≤ s) ∧ (n ⬝ᵥ g < n ⬝ᵥ b → q < s) := by
  have e := congrArg (fun x => n ⬝ᵥ x) hE
  simp only [dotProduct_add, dotProduct_smul, smul_eq_mul, ha, hc, hf] at e
  have key : q * (n ⬝ᵥ b - k) = s * (n ⬝ᵥ g - k) := by linear_combination e - k * hsum
  constructor
  · by_contra h
    push Not at h
    nlinarith [mul_pos (sub_pos.2 h) (sub_pos.2 hk), mul_nonneg hq0.le (sub_nonneg.2 hgb)]
  · intro hlt
    by_contra h
    push Not at h
    nlinarith [mul_pos (sub_pos.2 hlt) hq0, mul_nonneg (sub_nonneg.2 h) (sub_pos.2 hk).le]

/-- `H2` gives `(1-t)((1-s)-r) ≤ p u`. -/
theorem h2_le {a b m c f g : Fin 3 → ℝ} {p q r s t u : ℝ} (hr : 0 < r) (ht1 : t < 1)
    (hsum : p + q + r = 1)
    (hQ : (1 - t) • a + t • m = (1 - u) • b + u • f)
    (hE : p • a + q • b + r • c = (1 - s) • f + s • g) {n : Fin 3 → ℝ} {k : ℝ}
    (hb : n ⬝ᵥ b = k) (hg : n ⬝ᵥ g = k) (hm : n ⬝ᵥ m = k) (hk : k < n ⬝ᵥ f)
    (hcf : n ⬝ᵥ c ≤ n ⬝ᵥ f) :
    ((1 - t) * ((1 - s) - r) ≤ p * u) ∧ (n ⬝ᵥ c < n ⬝ᵥ f → (1 - t) * ((1 - s) - r) < p * u) := by
  have e1 := congrArg (fun x => n ⬝ᵥ x) hE
  have e0 := congrArg (fun x => n ⬝ᵥ x) hQ
  simp only [dotProduct_add, dotProduct_smul, smul_eq_mul, hb, hg, hm] at e1 e0
  have h1 : (1 - t) * (n ⬝ᵥ a - k) = u * (n ⬝ᵥ f - k) := by linear_combination e0
  have h2 : p * (n ⬝ᵥ a - k) + r * (n ⬝ᵥ c - k) = (1 - s) * (n ⬝ᵥ f - k) := by
    linear_combination e1 - k * hsum
  have h3 : (n ⬝ᵥ f - k) * ((1 - t) * ((1 - s) - r) - p * u)
      = (1 - t) * r * (n ⬝ᵥ c - n ⬝ᵥ f) := by
    linear_combination (-(1 - t)) * h2 + p * h1
  have hX : 0 < n ⬝ᵥ f - k := sub_pos.2 hk
  have ht' : 0 < 1 - t := by linarith
  constructor
  · by_contra h
    push Not at h
    nlinarith [mul_pos hX (sub_pos.2 h), mul_nonneg (mul_pos ht' hr).le (sub_nonneg.2 hcf)]
  · intro hlt
    by_contra h
    push Not at h
    nlinarith [mul_nonneg hX.le (sub_nonneg.2 h), mul_pos (mul_pos ht' hr) (sub_pos.2 hlt)]

theorem quadEdgeLemma : MinimalityExtra.QuadEdgeLemma := by
  intro a b m f c g hq hE hH w hw
  obtain ⟨t, u, ht0, ht1, hu0, hu1, hQ⟩ := hq
  obtain ⟨p, q, r, s, hp, hq0, hr, hsum, hs0, hs1, hE⟩ := hE
  rw [cyc4_eq, cyc5_eq]
  let S := mkQS hp hq0 hr hsum hs0 hs1 ht0 ht1 hu0 hu1 hQ hE hw
  have hH' : S.be ≤ S.s ∨ (1 - S.t) * ((1 - S.s) - S.ga) ≤ S.al * S.u := by
    rcases hH with ⟨n, k, ha, hc, hf, hk, hgb⟩ | ⟨n, k, hb, hg, hm, hk, hcf⟩
    · exact Or.inl (h1_le hq0 hsum hE ha hc hf hk hgb).1
    · exact Or.inr (h2_le hr ht1 hsum hQ hE hb hg hm hk hcf).1
  rcases core S hH' with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

theorem quadEdgeLemmaStrict : MinimalityExtra.QuadEdgeLemmaStrict := by
  intro a b m f c g hq hE hH w hw hne
  obtain ⟨t, u, ht0, ht1, hu0, hu1, hQ⟩ := hq
  obtain ⟨p, q, r, s, hp, hq0, hr, hsum, hs0, hs1, hE⟩ := hE
  rw [cyc4_eq, cyc5_eq]
  let S := mkQS hp hq0 hr hsum hs0 hs1 ht0 ht1 hu0 hu1 hQ hE hw
  have hH' : S.be < S.s ∨ (1 - S.t) * ((1 - S.s) - S.ga) < S.al * S.u := by
    rcases hH with ⟨n, k, ha, hc, hf, hk, hgb⟩ | ⟨n, k, hb, hg, hm, hk, hcf⟩
    · exact Or.inl ((h1_le hq0 hsum hE ha hc hf hk hgb.le).2 hgb)
    · exact Or.inr ((h2_le hr ht1 hsum hQ hE hb hg hm hk hcf.le).2 hcf)
  exact core_strict S hH' hne


end QE

namespace MinimalityExtra

/-- Proof of `QuadEdgeLemma`. -/
theorem quadEdgeLemma : QuadEdgeLemma := QE.quadEdgeLemma

/-- Proof of `QuadEdgeLemmaStrict`. -/
theorem quadEdgeLemmaStrict : QuadEdgeLemmaStrict := QE.quadEdgeLemmaStrict

end MinimalityExtra

#print axioms MinimalityExtra.quadEdgeLemma
#print axioms MinimalityExtra.quadEdgeLemmaStrict
