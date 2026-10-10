module

public import SmallRupert.Polygon

@[expose] public section

/-!
# Theorem 7.3: from forces to a horizontal double normal (glue)

Translates the polygon setting of `hasHorizontalDoubleNormal_of_forces` into the
sequence setting of `forces_parallel`:
* cyclic unimodality gives the rise/fall structure in any rotated reading
  (`noZig`);
* the normal cones give the sign-switch properties of the forces;
* Step 5: parallel forces give a horizontal double normal.
-/

namespace SmallRupert

open scoped RealInnerProductSpace
open Finset

/-- A cyclic sequence of distinct reals with exactly one local maximum (hence
exactly one local minimum). -/
def IsCyclicUnimodal {k : ℕ} [NeZero k] (z : ZMod k → ℝ) : Prop :=
  Function.Injective z ∧
    (Finset.univ.filter (fun i : ZMod k => z (i - 1) < z i ∧ z (i + 1) < z i)).card = 1

/-- The corner `(p i, z i)` of the silhouette cycle in `ℝ³`. -/
noncomputable def liftPt (q : ℝ²) (t : ℝ) : ℝ³ := !₂[q 0, q 1, t]

/-- The silhouette cycle `C = x₀x₁⋯x_{k-1}x₀` has a *horizontal double normal*:
two points of `C` at the same depth whose projections span a double normal of
the shadow `conv p`. -/
def HasHorizontalDoubleNormal {k : ℕ} (p : ZMod k → ℝ²) (z : ZMod k → ℝ) : Prop :=
  ∃ y y' : ℝ³, (∃ i, y ∈ segment ℝ (liftPt (p i) (z i)) (liftPt (p (i + 1)) (z (i + 1)))) ∧
    (∃ j, y' ∈ segment ℝ (liftPt (p j) (z j)) (liftPt (p (j + 1)) (z (j + 1)))) ∧
    y 2 = y' 2 ∧ proj_xy y ≠ proj_xy y' ∧
    proj_xy y' - proj_xy y ∈ normalConeAt (convexHull ℝ (Set.range p)) (proj_xy y') ∧
    proj_xy y - proj_xy y' ∈ normalConeAt (convexHull ℝ (Set.range p)) (proj_xy y)


/-- An interior maximum over a window of the cycle is a strict local maximum. -/
theorem exists_localMax_window {k : ℕ} (z : ZMod k → ℝ) (hz : Function.Injective z)
    (B : ZMod k) (L : ℕ) (hL : L < k) (u : ℕ) (hu0 : 0 < u) (huL : u < L)
    (h0 : z B < z (B + u)) (hL' : z (B + L) < z (B + u)) :
    ∃ p : ℕ, 0 < p ∧ p < L ∧ z (B + p - 1) < z (B + p) ∧ z (B + p + 1) < z (B + p) := by
  obtain ⟨p, hp, hmax⟩ := (range (L + 1)).exists_max_image (fun q : ℕ => z (B + q))
    ⟨u, mem_range.mpr (by omega)⟩
  rw [mem_range] at hp
  have hp0 : p ≠ 0 := by
    rintro rfl
    have := hmax u (mem_range.mpr (by omega))
    simp at this; linarith
  have hpL : p ≠ L := by
    rintro rfl
    have := hmax u (mem_range.mpr (by omega))
    linarith
  refine ⟨p, by omega, by omega, ?_, ?_⟩
  · have h1 := hmax (p - 1) (mem_range.mpr (by omega))
    have hc : ((p - 1 : ℕ) : ZMod k) = (p : ZMod k) - 1 := by
      rw [Nat.cast_sub (by omega), Nat.cast_one]
    simp only [hc, ← add_sub_assoc] at h1
    refine lt_of_le_of_ne h1 (fun h => ?_)
    have := hz h
    have h2 := zmod_add_ne (k := k) (a := p - 1) (b := p) (by omega) (by omega) (by omega) B
    rw [hc, ← add_sub_assoc] at h2
    exact h2 this
  · have h1 := hmax (p + 1) (mem_range.mpr (by omega))
    simp only [Nat.cast_succ, ← add_assoc] at h1
    refine lt_of_le_of_ne h1 (fun h => ?_)
    have := hz h
    have h2 := zmod_add_ne (k := k) (a := p + 1) (b := p) (by omega) (by omega) (by omega) B
    rw [Nat.cast_succ, ← add_assoc] at h2
    exact h2 this

theorem natCast_mod_two {k : ℕ} {x y : ℕ} (hk : 0 < k) (hx : x < k) (hy : y < 2 * k)
    (h : (x : ZMod k) = (y : ZMod k)) : x = y ∨ x + k = y := by
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hx] at h
  by_cases hyk : y < k
  · left; rw [Nat.mod_eq_of_lt hyk] at h; exact h
  · right
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at h
    omega

/-- A cyclically unimodal sequence has at most one strict local maximum. -/
theorem IsCyclicUnimodal.eq_of_localMax {k : ℕ} [NeZero k] {z : ZMod k → ℝ}
    (hz : IsCyclicUnimodal z) {q1 q2 : ZMod k}
    (h1 : z (q1 - 1) < z q1 ∧ z (q1 + 1) < z q1) (h2 : z (q2 - 1) < z q2 ∧ z (q2 + 1) < z q2) :
    q1 = q2 := by
  by_contra hne
  have : 1 < (univ.filter (fun i : ZMod k => z (i - 1) < z i ∧ z (i + 1) < z i)).card :=
    one_lt_card.mpr ⟨q1, by simp [h1], q2, by simp [h2], hne⟩
  rw [hz.2] at this
  exact lt_irrefl _ this

theorem zmod_add_natCast_sub {k : ℕ} (B : ZMod k) {a x : ℕ} (h : a ≤ x) :
    B + (a : ZMod k) + ((x - a : ℕ) : ZMod k) = B + x := by
  rw [Nat.cast_sub h]; ring

/-- **No zigzag.**  In any linear reading of a cyclically unimodal sequence, four
positions never alternate low–high–low–high. -/
theorem IsCyclicUnimodal.noZig {k : ℕ} [NeZero k] {z : ZMod k → ℝ} (hz : IsCyclicUnimodal z)
    (B : ZMod k) {a b c d : ℕ} (hab : a < b) (hbc : b < c) (hcd : c < d) (hdk : d < k) :
    ¬ ((z (B + a) < z (B + b) ∧ z (B + c) < z (B + b) ∧ z (B + c) < z (B + d) ∧
        z (B + a) < z (B + d)) ∨
       (z (B + b) < z (B + a) ∧ z (B + b) < z (B + c) ∧ z (B + d) < z (B + c) ∧
        z (B + d) < z (B + a))) := by
  have hk0 : 0 < k := by omega
  have hkz : ((k : ℕ) : ZMod k) = 0 := ZMod.natCast_self k
  -- the two windows of a zigzag give two distinct local maxima
  have key : ∀ a b c d : ℕ, a < b → b < c → c < d → d < k →
      z (B + a) < z (B + b) → z (B + c) < z (B + b) → z (B + c) < z (B + d) →
      z (B + a) < z (B + d) → False := by
    intro a b c d hab hbc hcd hdk h1 h2 h3 h4
    obtain ⟨p1, hp1, hp1L, hl1, hr1⟩ := exists_localMax_window z hz.1 (B + a) (c - a) (by omega)
      (b - a) (by omega) (by omega)
      (by rw [zmod_add_natCast_sub B hab.le]; exact h1)
      (by rw [zmod_add_natCast_sub B (by omega : a ≤ c), zmod_add_natCast_sub B hab.le]; exact h2)
    obtain ⟨p2, hp2, hp2L, hl2, hr2⟩ := exists_localMax_window z hz.1 (B + c) (k - c + a)
      (by omega) (d - c) (by omega) (by omega)
      (by rw [zmod_add_natCast_sub B hcd.le]; exact h3)
      (by
        rw [zmod_add_natCast_sub B hcd.le,
          show B + (c : ZMod k) + ((k - c + a : ℕ) : ZMod k) = B + a by
            rw [Nat.cast_add, Nat.cast_sub (by omega), hkz]; ring]
        exact h4)
    have heq := hz.eq_of_localMax ⟨hl1, hr1⟩ ⟨hl2, hr2⟩
    have : ((a + p1 : ℕ) : ZMod k) = ((c + p2 : ℕ) : ZMod k) := by
      push_cast; linear_combination heq
    rcases natCast_mod_two hk0 (by omega) (by omega) this with h | h <;> omega
  rintro (⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩)
  · exact key a b c d hab hbc hcd hdk h1 h2 h3 h4
  · -- rotate the pattern: windows around `c` and around `a`
    obtain ⟨p1, hp1, hp1L, hl1, hr1⟩ := exists_localMax_window z hz.1 (B + b) (d - b) (by omega)
      (c - b) (by omega) (by omega)
      (by rw [zmod_add_natCast_sub B hbc.le]; exact h2)
      (by rw [zmod_add_natCast_sub B (by omega : b ≤ d), zmod_add_natCast_sub B hbc.le]; exact h3)
    obtain ⟨p2, hp2, hp2L, hl2, hr2⟩ := exists_localMax_window z hz.1 (B + d) (k - d + b)
      (by omega) (k - d + a) (by omega) (by omega)
      (by
        rw [show B + (d : ZMod k) + ((k - d + a : ℕ) : ZMod k) = B + a by
          rw [Nat.cast_add, Nat.cast_sub (by omega), hkz]; ring]
        exact h4)
      (by
        rw [show B + (d : ZMod k) + ((k - d + a : ℕ) : ZMod k) = B + a by
            rw [Nat.cast_add, Nat.cast_sub (by omega), hkz]; ring,
          show B + (d : ZMod k) + ((k - d + b : ℕ) : ZMod k) = B + b by
            rw [Nat.cast_add, Nat.cast_sub (by omega), hkz]; ring]
        exact h1)
    have heq := hz.eq_of_localMax ⟨hl1, hr1⟩ ⟨hl2, hr2⟩
    have : ((b + p1 : ℕ) : ZMod k) = ((d + p2 : ℕ) : ZMod k) := by
      push_cast; linear_combination heq
    rcases natCast_mod_two hk0 (by omega) (by omega) this with h | h <;> omega

end SmallRupert

end
