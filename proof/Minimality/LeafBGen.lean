module

public import Minimality.TorqueLeaves

@[expose] public section

/-!
# Leaf B on a general rim: Theorem 8.10 at a tilt of a three-point depth tie

Setting (`LEAFB24.md`, sections 1 and 3): a rim cycle `p : ZMod k → ℝ³` (`k ≥ 4`) that passes all
triple tests counterclockwise at the view `u`, with four consecutive corners
`V = p a, E' = p (a+1), E'' = p (a+2), W = p (a+3)` and one more corner `E = p b`
(`b ∉ {a, .., a+3}`).  At `u` the three points `E', E'', E` tie in depth and every other rim corner is
strictly deeper.  The key row `det3 (E' - V) (W - E'') u < 0` says that the screen angles at `E'` and
`E''` sum to less than `π`.  Then `V` is Rupert: a tilt `u + ε e` that orders the tie as
`E' < E'' < E` (pair: edge `V → E'`, far corner `E''`) or `E'' < E' < E` (pair: edge `E'' → W`, far
corner `E'`) gives a depth-separated parallel pair, and the torque form of Theorem 8.10
(`isRupert_rimTilt_torque`) closes it.  One of the two wedges always has a nonzero torque: if both
torques vanished, `E'' - E'` would be orthogonal to `E' - V`, `W - E''` and `u`, against the key row.

Main results:
* `far_fwd`, `far_bwd`: the far-corner lemma (LEAFB24 section 3) for any convex rim, from one
  Plücker relation; `parPair_fwd`, `parPair_bwd`: the two parallel pairs.
* `dsz_fwd`, `dsz_bwd`: the depth half of the two pairs, for any `k`.
* `isRupert_leafB_gen`: the generic Leaf B (positive orientation).

The seven single-isolated rims of type 24 OB1 are instances (`Dispatch24OB1`), the old rim-specific
proof `isRupert_leafB_04625_of_det'` (TorqueLeaves) is the case `k = 5`, `a = 1`, `b = 0`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped RealInnerProductSpace
open Filter Topology

namespace Minimality
open HDNApex LeafB24 FaceCircle

namespace LeafBGen

/-! ### Index arithmetic in `ZMod k` -/

theorem natCast_ne_zero {k : ℕ} {m : ℕ} (h0 : 0 < m) (h : m < k) : (m : ZMod k) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro hd
  exact absurd (Nat.le_of_dvd h0 hd) (by omega)

theorem add_ne_add {k : ℕ} (a : ZMod k) {m n : ℕ} (hm : m < k) (hn : n < k) (hmn : m ≠ n) :
    a + (m : ZMod k) ≠ a + (n : ZMod k) := by
  intro h
  have h' := add_left_cancel h
  have := congrArg ZMod.val h'
  rw [ZMod.val_cast_of_lt hm, ZMod.val_cast_of_lt hn] at this
  exact hmn this

/-- The corners `a, a+1, a+2, a+3` of a cycle of length `k ≥ 4` are distinct. -/
theorem four_distinct {k : ℕ} (hk : 4 ≤ k) (a : ZMod k) :
    a + 1 ≠ a ∧ a + 2 ≠ a ∧ a + 3 ≠ a ∧ a + 2 ≠ a + 1 ∧ a + 3 ≠ a + 1 ∧ a + 3 ≠ a + 2 := by
  have h := fun (m n : ℕ) (hm : m < 4) (hn : n < 4) (hmn : m ≠ n) =>
    add_ne_add a (k := k) (m := m) (n := n) (by omega) (by omega) hmn
  have h10 := h 1 0 (by norm_num) (by norm_num) (by norm_num)
  have h20 := h 2 0 (by norm_num) (by norm_num) (by norm_num)
  have h30 := h 3 0 (by norm_num) (by norm_num) (by norm_num)
  have h21 := h 2 1 (by norm_num) (by norm_num) (by norm_num)
  have h31 := h 3 1 (by norm_num) (by norm_num) (by norm_num)
  have h32 := h 3 2 (by norm_num) (by norm_num) (by norm_num)
  push_cast at h10 h20 h30 h21 h31 h32
  simp only [add_zero] at h10 h20 h30
  exact ⟨h10, h20, h30, h21, h31, h32⟩

/-! ### The far-corner lemma -/

/-- **Far corner, forward pair.**  Consecutive rim corners `P0 P1 P2 P3` and one more point `Q`,
all triple tests positive, and the key row (angles at `P1`, `P2` sum below `π`): `Q` is strictly
closer than `P2` to the line `P0 P1`. -/
theorem far_fwd (P0 P1 P2 P3 Q u : ℝ³) (h02 : 0 < det3 (P1 - P0) (P2 - P0) u)
    (h13 : 0 < det3 (P2 - P1) (P3 - P1) u) (h1Q : 0 < det3 (P2 - P1) (Q - P1) u)
    (h2Q : 0 < det3 (P3 - P2) (Q - P2) u) (key : det3 (P1 - P0) (P3 - P2) u < 0) :
    det3 (P1 - P0) (Q - P2) u < 0 := by
  have hpl : det3 (P1 - P0) (Q - P2) u * det3 (P2 - P1) (P3 - P1) u =
      -(det3 (P1 - P0) (P2 - P0) u * det3 (P3 - P2) (Q - P2) u) +
        det3 (P1 - P0) (P3 - P2) u * det3 (P2 - P1) (Q - P1) u := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have hlt : det3 (P1 - P0) (Q - P2) u * det3 (P2 - P1) (P3 - P1) u < 0 := by
    rw [hpl]; nlinarith [mul_pos h02 h2Q, mul_neg_of_neg_of_pos key h1Q]
  by_contra hc
  push Not at hc
  nlinarith [mul_nonneg hc h13.le]

/-- **Far corner, backward pair.**  As `far_fwd`, for the edge `P2 → P3` and the corner `P1`. -/
theorem far_bwd (P0 P1 P2 P3 Q u : ℝ³) (h02 : 0 < det3 (P1 - P0) (P2 - P0) u)
    (h13 : 0 < det3 (P2 - P1) (P3 - P1) u) (h0Q : 0 < det3 (P1 - P0) (Q - P0) u)
    (h1Q : 0 < det3 (P2 - P1) (Q - P1) u) (key : det3 (P1 - P0) (P3 - P2) u < 0) :
    det3 (P3 - P2) (Q - P1) u < 0 := by
  have hpl : det3 (P3 - P2) (Q - P1) u * det3 (P1 - P0) (P2 - P0) u =
      -(det3 (P2 - P1) (P3 - P1) u * det3 (P1 - P0) (Q - P0) u) +
        det3 (P1 - P0) (P3 - P2) u * det3 (P2 - P1) (Q - P1) u := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have hlt : det3 (P3 - P2) (Q - P1) u * det3 (P1 - P0) (P2 - P0) u < 0 := by
    rw [hpl]; nlinarith [mul_pos h13 h0Q, mul_neg_of_neg_of_pos key h1Q]
  by_contra hc
  push Not at hc
  nlinarith [mul_nonneg hc h02.le]

section Pairs
variable {k : ℕ} {p : ZMod k → ℝ³} {u : ℝ³}

/-- **The forward pair** (edge `a → a+1`, far corner `a+2`) of a convex rim with the key row. -/
theorem parPair_fwd (hk : 4 ≤ k)
    (hcyc : ∀ i j, j ≠ i → j ≠ i + 1 → 0 < det3 (p (i + 1) - p i) (p j - p i) u) (a : ZMod k)
    (key : det3 (p (a + 1) - p a) (p (a + 3) - p (a + 2)) u < 0) : ParPairAt p u a (a + 2) := by
  obtain ⟨d10, d20, d30, d21, d31, d32⟩ := four_distinct hk a
  have e2 : a + 1 + 1 = a + 2 := by ring
  have e3 : a + 2 + 1 = a + 3 := by ring
  have h02 : 0 < det3 (p (a + 1) - p a) (p (a + 2) - p a) u := hcyc a (a + 2) d20 d21
  have h13 : 0 < det3 (p (a + 2) - p (a + 1)) (p (a + 3) - p (a + 1)) u := by
    have := hcyc (a + 1) (a + 3) d31 (by rw [e2]; exact d32); rwa [e2] at this
  intro j hj
  refine mul_neg_of_neg_of_pos ?_ h02
  by_cases j1 : j = a + 1
  · subst j1
    have : det3 (p (a + 1) - p a) (p (a + 1) - p (a + 2)) u =
        -det3 (p (a + 1) - p a) (p (a + 2) - p a) u := by
      simp only [det3_expand, PiLp.sub_apply]; ring
    rw [this]; linarith
  by_cases j3 : j = a + 3
  · subst j3; exact key
  have h1Q : 0 < det3 (p (a + 2) - p (a + 1)) (p j - p (a + 1)) u := by
    have := hcyc (a + 1) j j1 (by rw [e2]; exact hj); rwa [e2] at this
  have h2Q : 0 < det3 (p (a + 3) - p (a + 2)) (p j - p (a + 2)) u := by
    have := hcyc (a + 2) j hj (by rw [e3]; exact j3); rwa [e3] at this
  exact far_fwd _ _ _ _ _ u h02 h13 h1Q h2Q key

/-- **The backward pair** (edge `a+2 → a+3`, far corner `a+1`) of a convex rim with the key row. -/
theorem parPair_bwd (hk : 4 ≤ k)
    (hcyc : ∀ i j, j ≠ i → j ≠ i + 1 → 0 < det3 (p (i + 1) - p i) (p j - p i) u) (a : ZMod k)
    (key : det3 (p (a + 1) - p a) (p (a + 3) - p (a + 2)) u < 0) :
    ParPairAt p u (a + 2) (a + 1) := by
  obtain ⟨d10, d20, d30, d21, d31, d32⟩ := four_distinct hk a
  have e2 : a + 1 + 1 = a + 2 := by ring
  have e3 : a + 2 + 1 = a + 3 := by ring
  have h02 : 0 < det3 (p (a + 1) - p a) (p (a + 2) - p a) u := hcyc a (a + 2) d20 d21
  have h13 : 0 < det3 (p (a + 2) - p (a + 1)) (p (a + 3) - p (a + 1)) u := by
    have := hcyc (a + 1) (a + 3) d31 (by rw [e2]; exact d32); rwa [e2] at this
  have h21 : 0 < det3 (p (a + 3) - p (a + 2)) (p (a + 1) - p (a + 2)) u := by
    have := hcyc (a + 2) (a + 1) d21.symm (by rw [e3]; exact d31.symm); rwa [e3] at this
  intro j hj
  rw [e3]
  refine mul_neg_of_neg_of_pos ?_ h21
  by_cases j0 : j = a
  · subst j0
    have : det3 (p (j + 3) - p (j + 2)) (p j - p (j + 1)) u =
        det3 (p (j + 1) - p j) (p (j + 3) - p (j + 2)) u := by
      simp only [det3_expand, PiLp.sub_apply]; ring
    rw [this]; exact key
  by_cases j2 : j = a + 2
  · subst j2
    have : det3 (p (a + 3) - p (a + 2)) (p (a + 2) - p (a + 1)) u =
        -det3 (p (a + 2) - p (a + 1)) (p (a + 3) - p (a + 1)) u := by
      simp only [det3_expand, PiLp.sub_apply]; ring
    rw [this]; linarith
  have h0Q : 0 < det3 (p (a + 1) - p a) (p j - p a) u := hcyc a j j0 hj
  have h1Q : 0 < det3 (p (a + 2) - p (a + 1)) (p j - p (a + 1)) u := by
    have := hcyc (a + 1) j hj (by rw [e2]; exact j2); rwa [e2] at this
  exact far_bwd _ _ _ _ _ u h02 h13 h0Q h1Q key

end Pairs

/-! ### The depth half -/

section Depth
variable {k : ℕ}

/-- Wedge 1 (`z (a+1) < z (a+2) <` every other corner): the forward pair is depth-separated. -/
theorem dsz_fwd (hk : 3 ≤ k) (z : ZMod k → ℝ) (a : ZMod k) (h1 : z (a + 1) < z (a + 2))
    (h2 : ∀ j, j ≠ a + 1 → j ≠ a + 2 → z (a + 2) < z j) : DepthSepZ z a (a + 2) := by
  have hcast : ((k - 2 : ℕ) : ZMod k) = -2 := by
    have : ((k - 2 : ℕ) : ZMod k) + ((2 : ℕ) : ZMod k) = 0 := by
      rw [← Nat.cast_add, Nat.sub_add_cancel (by omega), ZMod.natCast_self]
    push_cast at this; linear_combination this
  have hv : (a - (a + 2)).val = k - 2 := by
    rw [show a - (a + 2) = ((k - 2 : ℕ) : ZMod k) by rw [hcast]; ring,
      ZMod.val_cast_of_lt (by omega)]
  left
  rw [hv]
  refine ⟨fun s hs1 hs2 => h2 _ ?_ ?_, fun s hs1 hs2 => ?_⟩
  · intro h
    have : ((s + 1 : ℕ) : ZMod k) = 0 := by push_cast; linear_combination h
    exact natCast_ne_zero (by omega) (by omega) this
  · intro h
    have : ((s : ℕ) : ZMod k) = 0 := by linear_combination h
    exact natCast_ne_zero (by omega) (by omega) this
  · have hs : s = k - 1 := by omega
    have : a + 2 + (s : ZMod k) = a + 1 := by
      have h' : ((k - 1 : ℕ) : ZMod k) + ((1 : ℕ) : ZMod k) = 0 := by
        rw [← Nat.cast_add, Nat.sub_add_cancel (by omega), ZMod.natCast_self]
      push_cast at h'
      rw [hs]; linear_combination h'
    rw [this]; exact h1

/-- Wedge 2 (`z (a+2) < z (a+1) <` every other corner): the backward pair is depth-separated. -/
theorem dsz_bwd [NeZero k] (hk : 3 ≤ k) (z : ZMod k → ℝ) (a : ZMod k) (h1 : z (a + 2) < z (a + 1))
    (h2 : ∀ j, j ≠ a + 1 → j ≠ a + 2 → z (a + 1) < z j) : DepthSepZ z (a + 2) (a + 1) := by
  have hv : (a + 2 - (a + 1)).val = 1 := by
    rw [show a + 2 - (a + 1) = ((1 : ℕ) : ZMod k) by push_cast; ring,
      ZMod.val_cast_of_lt (by omega)]
  right
  rw [hv]
  refine ⟨fun s hs1 hs2 => ?_, fun s hs1 hs2 => h2 _ ?_ ?_⟩
  · have hs : s = 1 := by omega
    subst hs
    have : a + 1 + ((1 : ℕ) : ZMod k) = a + 2 := by push_cast; ring
    rw [this]; exact h1
  · intro h
    have : ((s : ℕ) : ZMod k) = 0 := by linear_combination h
    exact natCast_ne_zero (by omega) (by omega) this
  · intro h
    have : ((s - 1 : ℕ) : ZMod k) = 0 := by
      have e : ((s - 1 : ℕ) : ZMod k) + 1 = (s : ZMod k) := by
        rw [← Nat.cast_one (R := ZMod k), ← Nat.cast_add, Nat.sub_add_cancel (by omega)]
      linear_combination e + h
    exact natCast_ne_zero (by omega) (by omega) this

end Depth

/-! ### The hang condition -/

/-- If `w` is orthogonal to `A`, `B` and `u` and `det3 A B u ≠ 0`, then `w = 0`. -/
theorem eq_zero_of_orth3 {A B u w : ℝ³} (key : det3 A B u ≠ 0) (ha : ⟪w, A⟫ = 0)
    (hb : ⟪w, B⟫ = 0) (hu : ⟪w, u⟫ = 0) : w = 0 := by
  simp only [PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, conj_trivial] at ha hb hu
  rw [det3_expand] at key
  ext l
  fin_cases l
  · simp only [Fin.zero_eta, PiLp.zero_apply]
    apply (mul_eq_zero.mp (?_ : _ * w 0 = 0)).resolve_left key
    linear_combination (B 1 * u 2 - B 2 * u 1) * ha + (u 1 * A 2 - u 2 * A 1) * hb +
      (A 1 * B 2 - A 2 * B 1) * hu
  · simp only [Fin.mk_one, PiLp.zero_apply]
    apply (mul_eq_zero.mp (?_ : _ * w 1 = 0)).resolve_left key
    linear_combination (B 2 * u 0 - B 0 * u 2) * ha + (u 2 * A 0 - u 0 * A 2) * hb +
      (A 2 * B 0 - A 0 * B 2) * hu
  · simp only [Fin.reduceFinMk, PiLp.zero_apply]
    apply (mul_eq_zero.mp (?_ : _ * w 2 = 0)).resolve_left key
    linear_combination (B 0 * u 1 - B 1 * u 0) * ha + (u 0 * A 1 - u 1 * A 0) * hb +
      (A 0 * B 1 - A 1 * B 0) * hu

/-! ### Leaf B -/

/-- **Leaf B on a general rim.**  `p` is a rim cycle of length `k ≥ 4` passing all triple tests
counterclockwise at `u`, every other point of `V` strictly inside; `V = p a`, `E' = p (a+1)`,
`E'' = p (a+2)`, `W = p (a+3)`, and `E = p b` another corner.  At `u` the depths of `E'`, `E''`, `E`
tie and every other rim corner is strictly deeper; the key row `det3 (E' - V) (W - E'') u < 0`
holds.  Then `V` is Rupert. -/
theorem isRupert_leafB_gen (V : Finset ℝ³) {k : ℕ} [NeZero k] (hk : 4 ≤ k) (p : ZMod k → ℝ³)
    (hpV : ∀ i, p i ∈ V) {u : ℝ³} (hu : u ≠ 0)
    (hcyc : ∀ i j, j ≠ i → j ≠ i + 1 → 0 < det3 (p (i + 1) - p i) (p j - p i) u)
    (hrest : ∀ v ∈ V, (∀ j, v ≠ p j) → ∀ i, 0 < det3 (p (i + 1) - p i) (v - p i) u)
    (a b : ZMod k) (hb0 : b ≠ a) (hb1 : b ≠ a + 1) (hb2 : b ≠ a + 2) (hb3 : b ≠ a + 3)
    (t1 : ⟪p (a + 1), u⟫ = ⟪p (a + 2), u⟫) (tb : ⟪p b, u⟫ = ⟪p (a + 2), u⟫)
    (hv : ∀ j, j ≠ a + 1 → j ≠ a + 2 → j ≠ b → ⟪p (a + 2), u⟫ < ⟪p j, u⟫)
    (key : det3 (p (a + 1) - p a) (p (a + 3) - p (a + 2)) u < 0) : IsRupert V := by
  classical
  obtain ⟨d10, d20, d30, d21, d31, d32⟩ := four_distinct hk a
  have e2 : a + 1 + 1 = a + 2 := by ring
  have e3 : a + 2 + 1 = a + 3 := by ring
  have hk3 : 3 ≤ k := by omega
  have pp1 := parPair_fwd hk hcyc a key
  have pp2 := parPair_bwd hk hcyc a key
  have hcycE : ∀ e : ℝ³, ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ i j, j ≠ i → j ≠ i + 1 →
      0 < det3 (p (i + 1) - p i) (p j - p i) (u + ε • e) := fun e =>
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j =>
      ev_imp fun h1 => ev_imp fun h2 => ev_det_pos e (hcyc i j h1 h2)
  have hrestE : ∀ e : ℝ³, ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ v ∈ V, (∀ j, v ≠ p j) → ∀ i,
      0 < det3 (p (i + 1) - p i) (v - p i) (u + ε • e) := fun e =>
    (Filter.eventually_all_finset V).2 fun v hv => ev_imp fun hvp =>
      Filter.eventually_all.2 fun i => ev_det_pos e (hrest v hv hvp i)
  -- `E'' - E' ≠ 0` (a strict triple test), so one of the two torques is nonzero
  have hw0 : p (a + 2) - p (a + 1) ≠ 0 := by
    intro h0
    have := hcyc (a + 1) (a + 3) d31 (by rw [e2]; exact d32)
    rw [e2, h0] at this
    simp [det3_expand] at this
  have hang : ⟪p (a + 2) - p (a + 1), p (a + 1) - p a⟫ ≠ 0 ∨
      ⟪p (a + 1) - p (a + 2), p (a + 3) - p (a + 2)⟫ ≠ 0 := by
    by_contra hc
    push Not at hc
    obtain ⟨h1, h2⟩ := hc
    apply hw0
    refine eq_zero_of_orth3 key.ne h1 ?_ ?_
    · have : p (a + 1) - p (a + 2) = -(p (a + 2) - p (a + 1)) := by abel
      rw [this, inner_neg_left] at h2; linarith
    · rw [inner_sub_left]; linarith
  have hb1' : 0 < det3 (p (a + 2) - p (a + 1)) (p b - p (a + 1)) u := by
    have := hcyc (a + 1) b hb1 (by rw [e2]; exact hb2); rwa [e2] at this
  rcases hang with h | h
  · -- wedge 1: `E' < E'' < E`, pair (edge `a → a+1`, far corner `a+2`)
    have hd : det3 (p (a + 2) - p (a + 1)) (p b - p (a + 2)) u ≠ 0 := by
      have e : det3 (p (a + 2) - p (a + 1)) (p b - p (a + 2)) u =
          det3 (p (a + 2) - p (a + 1)) (p b - p (a + 1)) u := by
        simp only [det3_expand, PiLp.sub_apply]; ring
      rw [e]; exact hb1'.ne'
    obtain ⟨e, he1, he2⟩ := exists_tilt hd
    rw [inner_sub_left] at he1 he2
    have hz : ∀ᶠ ε in 𝓝[>] (0 : ℝ), DepthSepZ (fun i => ⟪p i, u + ε • e⟫) a (a + 2) := by
      have a1 := ev_inner_lt (a := p (a + 1)) (b := p (a + 2)) (u := u) e
        (Or.inr ⟨t1, by linarith⟩)
      have a2 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ j, j ≠ a + 1 → j ≠ a + 2 →
          ⟪p (a + 2), u + ε • e⟫ < ⟪p j, u + ε • e⟫ := by
        refine Filter.eventually_all.2 fun j => ev_imp fun hj1 => ev_imp fun hj2 => ?_
        by_cases hjb : j = b
        · subst hjb; exact ev_inner_lt e (Or.inr ⟨tb.symm, by linarith⟩)
        · exact ev_inner_lt e (Or.inl (hv j hj1 hj2 hjb))
      filter_upwards [a1, a2] with ε h1 h2
      exact dsz_fwd hk3 _ a h1 h2
    refine isRupert_rimTilt_torque V (by omega) p hpV hu (a := a) (c := a + 2)
      (ev_parPairAt e pp1) hz (hcycE e) (hrestE e) (Or.inl ?_)
    have hEu : ⟪p (a + 1) - p a, u⟫ ≠ 0 := by
      have := hv a d10.symm d20.symm hb0.symm
      rw [inner_sub_left]; linarith
    have hVE : ⟪p (a + 2) - p a, p (a + 1) - p a⟫ =
        ⟪p (a + 2) - p (a + 1), p (a + 1) - p a⟫ + ⟪p (a + 1) - p a, p (a + 1) - p a⟫ := by
      rw [← inner_add_left]; congr 1; abel
    have hV : ⟪p (a + 2) - p a, u⟫ = ⟪p (a + 1) - p a, u⟫ := by
      simp only [inner_sub_left]; rw [t1]
    rw [inner_Wv, hVE, hV]
    have : (⟪p (a + 2) - p (a + 1), p (a + 1) - p a⟫ + ⟪p (a + 1) - p a, p (a + 1) - p a⟫) *
          ⟪p (a + 1) - p a, u⟫ - ⟪p (a + 1) - p a, p (a + 1) - p a⟫ * ⟪p (a + 1) - p a, u⟫ =
        ⟪p (a + 2) - p (a + 1), p (a + 1) - p a⟫ * ⟪p (a + 1) - p a, u⟫ := by ring
    rw [this]; exact mul_ne_zero h hEu
  · -- wedge 2: `E'' < E' < E`, pair (edge `a+2 → a+3`, far corner `a+1`)
    have hd : det3 (p (a + 1) - p (a + 2)) (p b - p (a + 1)) u ≠ 0 := by
      have e : det3 (p (a + 1) - p (a + 2)) (p b - p (a + 1)) u =
          -det3 (p (a + 2) - p (a + 1)) (p b - p (a + 1)) u := by
        simp only [det3_expand, PiLp.sub_apply]; ring
      rw [e]; exact neg_ne_zero.2 hb1'.ne'
    obtain ⟨e, he1, he2⟩ := exists_tilt hd
    rw [inner_sub_left] at he1 he2
    have hz : ∀ᶠ ε in 𝓝[>] (0 : ℝ), DepthSepZ (fun i => ⟪p i, u + ε • e⟫) (a + 2) (a + 1) := by
      have a1 := ev_inner_lt (a := p (a + 2)) (b := p (a + 1)) (u := u) e
        (Or.inr ⟨t1.symm, by linarith⟩)
      have a2 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ j, j ≠ a + 1 → j ≠ a + 2 →
          ⟪p (a + 1), u + ε • e⟫ < ⟪p j, u + ε • e⟫ := by
        refine Filter.eventually_all.2 fun j => ev_imp fun hj1 => ev_imp fun hj2 => ?_
        by_cases hjb : j = b
        · subst hjb; exact ev_inner_lt e (Or.inr ⟨t1.trans tb.symm, by linarith⟩)
        · exact ev_inner_lt e (Or.inl (by rw [t1]; exact hv j hj1 hj2 hjb))
      filter_upwards [a1, a2] with ε h1 h2
      exact dsz_bwd hk3 _ a h1 h2
    refine isRupert_rimTilt_torque V (by omega) p hpV hu (a := a + 2) (c := a + 1)
      (ev_parPairAt e pp2) hz (hcycE e) (hrestE e) (Or.inl ?_)
    rw [e3]
    have hEu : ⟪p (a + 3) - p (a + 2), u⟫ ≠ 0 := by
      have := hv (a + 3) d31 d32 hb3.symm
      rw [inner_sub_left]; linarith
    have hV : ⟪p (a + 1) - p (a + 2), u⟫ = 0 := by
      rw [inner_sub_left, t1]; ring
    rw [inner_Wv, hV, mul_zero, sub_zero]
    exact mul_ne_zero h hEu

end LeafBGen
end Minimality
