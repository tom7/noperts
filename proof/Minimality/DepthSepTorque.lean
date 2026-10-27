module

public import Minimality.DepthSeparated

@[expose] public section

/-!
# Theorem D with torque

FEWER-FACES-PROOFS.md §8.10, Theorem D: at a depth-separated parallel pair
`(e, c)` the cone of balanced corner forces is a single ray, so the view is free
iff that ray's torque `(p_c − q)·d_e` is nonzero (`q` the point of `e` at depth
`z_c`), i.e. unless the pair's own segment is a horizontal double normal.

* `PairInterior p a c`: the interior condition `−n_e ∈ int N_c`, as "both
  neighbours of `c` have `⟪n_e, ·⟫` strictly larger than `c`".  It is needed:
  with only `−n_e ∈ N_c` a neighbour `c′` of `c` parallel to `e` can carry force.
  Depth separation does not imply it.
* `pairTorque p z a c := ⟪p c − q, d_e⟫`, `q = p a + t d_e`, `t = (z c − z a)/(z (a+1) − z a)`;
  the denominator is nonzero for a depth-separated pair (`PairInterior.depth_between`).
* `forces_supported_of_depthSeparated` (Theorem D, single ray): balanced forces
  are `f c = −s n`, `f a = α n`, `f (a+1) = β n`, zero elsewhere.
* `sum_cross2_of_depthSeparated`: the torque of the ray is `s · pairTorque`.
* `no_balanced_zeroTorque_of_depthSeparated`: `pairTorque ≠ 0` kills every balanced
  zero-torque system.
* `hasHorizontalDoubleNormal_of_pairTorque_eq_zero`: the converse.
* `exists_firstOrderInward_of_forces_zero`: the Lemma 7.1 glue with the criterion
  "every balanced zero-torque system vanishes" (no HDN hypothesis on the whole rim).
* `exists_firstOrderInward_of_depthSeparated_torque`, `..._image_..._torque`,
  `isRupert_of_chords_depthSeparated_torque`: torque forms of the Theorem 8.10
  glue (standard view, rotated view, Proposition 8.8).
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset

/-- The *torque* `⟪p c − q, d_e⟫` of the parallel pair `(e, c)`, where
`e = [p a, p (a + 1)]`, `d_e = p (a + 1) − p a`, and `q` is the point of `e` at
depth `z c` (`q = p a + t d_e`, `t = (z c − z a)/(z (a+1) − z a)`).  Meaningful
when `z (a + 1) ≠ z a` (true for a depth-separated pair). -/
noncomputable def pairTorque {k : ℕ} (p : ZMod k → ℝ²) (z : ZMod k → ℝ) (a c : ZMod k) : ℝ :=
  ⟪p c - (p a + ((z c - z a) / (z (a + 1) - z a)) • (p (a + 1) - p a)), p (a + 1) - p a⟫

/-- The interior condition `−n_e ∈ int N_c`: both neighbours of `c` lie strictly
farther from `c`'s supporting line `⟪n_e, ·⟫ = min` than `c` does. -/
def PairInterior {k : ℕ} (p : ZMod k → ℝ²) (a c : ZMod k) : Prop :=
  0 < ⟪outNormal (p a) (p (a + 1)), p (c + 1) - p c⟫ ∧
    0 < ⟪outNormal (p a) (p (a + 1)), p (c - 1) - p c⟫

namespace PairInterior

variable {k : ℕ} [NeZero k] {p : ZMod k → ℝ²} {a c : ZMod k}

theorem inner_outNormal_self (x y : ℝ²) : ⟪outNormal x y, y - x⟫ = 0 := by
  rw [inner_outNormal, cross2_self]; simp

theorem outNormal_ne_zero (hp : IsCcwPolygon p) (a : ZMod k) :
    outNormal (p a) (p (a + 1)) ≠ 0 := by
  intro h0
  have hne := hp.injective.ne (zmod_ne_add_one (by have := hp.1; omega) a)
  apply hne
  have e0 := congrArg (fun v : ℝ² => v 0) h0
  have e1 := congrArg (fun v : ℝ² => v 1) h0
  simp [outNormal] at e0 e1
  ext i; fin_cases i
  · simp; linarith
  · simp; linarith

theorem ne_a (h : PairInterior p a c) : c ≠ a := by
  rintro rfl
  have := h.1; rw [inner_outNormal_self] at this; exact lt_irrefl _ this

theorem ne_a_succ (h : PairInterior p a c) : c ≠ a + 1 := by
  rintro rfl
  have := h.2; simp only [add_sub_cancel_right] at this
  have h2 := inner_outNormal_self (p a) (p (a + 1))
  rw [← neg_sub, inner_neg_right, h2] at this; simp at this

/-- Strictly below the maximum off the edge. -/
theorem inner_lt (hp : IsCcwPolygon p) (a j : ZMod k) (hj : j ≠ a) (hj' : j ≠ a + 1) :
    ⟪outNormal (p a) (p (a + 1)), p j⟫ < ⟪outNormal (p a) (p (a + 1)), p a⟫ := by
  have e : ⟪outNormal (p a) (p (a + 1)), p j⟫ =
      ⟪outNormal (p a) (p (a + 1)), p a⟫ - cross2 (p (a + 1) - p a) (p j - p a) := by
    have := inner_outNormal (p a) (p (a + 1)) (p j - p a)
    rw [inner_sub_right] at this; linarith
  rw [e]; linarith [hp.2 a j hj hj']

/-- `c` is the unique minimizer of `⟪n_e, ·⟫`. -/
theorem min_unique (hp : IsCcwPolygon p) {a c : ZMod k} (h : PairInterior p a c)
    (hc : -outNormal (p a) (p (a + 1)) ∈ normalConeAt (convexHull ℝ (Set.range p)) (p c))
    (j : ZMod k) (hj : j ≠ c) :
    ⟪outNormal (p a) (p (a + 1)), p c⟫ < ⟪outNormal (p a) (p (a + 1)), p j⟫ := by
  set n := outNormal (p a) (p (a + 1)) with hn
  have hmin : ⟪n, p c⟫ ≤ ⟪n, p j⟫ := by
    have := hc (p j) (subset_convexHull ℝ _ ⟨j, rfl⟩)
    rw [inner_neg_left, inner_sub_right] at this; linarith
  refine lt_of_le_of_ne hmin fun heq => ?_
  have hk := hp.1
  have hu : ⟪n, p j - p c⟫ = 0 := by rw [inner_sub_right]; linarith
  have hn0 : n ≠ 0 := outNormal_ne_zero hp a
  have hnn : 0 < n 0 ^ 2 + n 1 ^ 2 := by
    by_contra hle
    apply hn0
    have h0 : n 0 = 0 := by nlinarith [sq_nonneg (n 0), sq_nonneg (n 1)]
    have h1 : n 1 = 0 := by nlinarith [sq_nonneg (n 0), sq_nonneg (n 1)]
    ext i; fin_cases i <;> simp [h0, h1]
  -- key identity: `‖n‖² cross2 u v = −cross2 n u ⟪n, v⟫` when `⟪n, u⟫ = 0`
  have key : ∀ u v : ℝ², ⟪n, u⟫ = 0 →
      (n 0 ^ 2 + n 1 ^ 2) * cross2 u v = -(cross2 n u * ⟪n, v⟫) := by
    intro u v huu
    simp only [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, conj_trivial, cross2] at huu ⊢
    linear_combination (n 0 * v 1 - n 1 * v 0) * huu
  have hu' : ⟪n, p j - p c⟫ = 0 := hu
  by_cases hj1 : j = c + 1
  · subst hj1; have := h.1; rw [hu'] at this; exact lt_irrefl _ this
  by_cases hj2 : j = c - 1
  · subst hj2; have := h.2; rw [hu'] at this; exact lt_irrefl _ this
  have p1 := hp.2 c j hj hj1
  have p2 := hp.2 (c - 1) j hj2 (by simpa using hj)
  rw [sub_add_cancel] at p2
  have c1 : cross2 (p j - p c) (p (c + 1) - p c) < 0 := by
    rw [cross2_comm]; linarith
  have c2 : 0 < cross2 (p j - p c) (p (c - 1) - p c) := by
    have e : cross2 (p c - p (c - 1)) (p j - p (c - 1)) =
        -cross2 (p (c - 1) - p c) (p j - p c) := by
      simp only [cross2, PiLp.sub_apply]; ring
    rw [e] at p2; rw [cross2_comm]; linarith
  have e1 := key _ (p (c + 1) - p c) hu'
  have e2 := key _ (p (c - 1) - p c) hu'
  have g1 := h.1
  have g2 := h.2
  have a1 : 0 < cross2 n (p j - p c) := by
    by_contra hh; push Not at hh
    nlinarith [mul_neg_of_pos_of_neg hnn c1, mul_nonneg (neg_nonneg.mpr hh) g1.le]
  have a2 : cross2 n (p j - p c) < 0 := by
    by_contra hh; push Not at hh
    nlinarith [mul_pos hnn c2, mul_nonneg hh g2.le]
  linarith

end PairInterior


variable {k : ℕ} [NeZero k] {p : ZMod k → ℝ²} {a c : ZMod k}

/-- The depths at the ends of `e` and at `c`: `z c` is strictly between. -/
theorem PairInterior.depth_between {z : ZMod k → ℝ} (h : PairInterior p a c)
    (hds : IsDepthSeparatedPair p z a c) :
    (z c < z a ∧ z (a + 1) < z c) ∨ (z a < z c ∧ z c < z (a + 1)) := by
  obtain ⟨-, ⟨hA, hB⟩ | ⟨hA, hB⟩⟩ := hds
  all_goals
    have hm0 : 0 < (a - c).val := by
      rcases Nat.eq_zero_or_pos (a - c).val with h0 | h0
      · exact absurd (sub_eq_zero.mp ((ZMod.val_eq_zero _).mp h0)).symm h.ne_a
      · exact h0
    have hmk : (a - c).val < k := ZMod.val_lt _
    have hm1 : (a - c).val + 1 < k := by
      by_contra hh
      have : (a - c).val + 1 = k := by omega
      apply h.ne_a_succ
      have h2 : c + (((a - c).val + 1 : ℕ) : ZMod k) = a + 1 := by
        rw [Nat.cast_succ, ← add_assoc, zmod_add_val_sub]
      rw [this, ZMod.natCast_self, add_zero] at h2
      exact h2
    have e1 : c + (((a - c).val : ℕ) : ZMod k) = a := zmod_add_val_sub c a
    have e2 : c + (((a - c).val + 1 : ℕ) : ZMod k) = a + 1 := by
      rw [Nat.cast_succ, ← add_assoc, e1]
    have g1 := hA (a - c).val hm0 le_rfl
    have g2 := hB ((a - c).val + 1) (by omega) hm1
    rw [e1] at g1
    rw [e2] at g2
  · exact Or.inl ⟨g1, g2⟩
  · exact Or.inr ⟨g1, g2⟩

/-- **Theorem D, single ray.**  At a depth-separated parallel pair `(e, c)` (with
`−n_e ∈ int N_c`) of a strictly convex counterclockwise polygon, a balanced
(E1, E2) corner-force system in the normal cones is supported on
`{a, a + 1, c}` and is a nonnegative combination along `n_e`:
`f c = −s n`, `f a = α n`, `f (a + 1) = β n` with `s = α + β`,
`s z_c = α z_a + β z_{a+1}`. -/
theorem forces_supported_of_depthSeparated
    {z : ZMod k → ℝ} (hp : IsCcwPolygon p) (hds : IsDepthSeparatedPair p z a c)
    (hint : PairInterior p a c)
    {f : ZMod k → ℝ²} (hf : ∀ i, f i ∈ normalConeAt (convexHull ℝ (Set.range p)) (p i))
    (h1 : ∑ i, f i = 0) (h2 : ∑ i, z i • f i = 0) :
    ∃ s α β : ℝ, 0 ≤ s ∧ 0 ≤ α ∧ 0 ≤ β ∧ s = α + β ∧ s * z c = α * z a + β * z (a + 1) ∧
      f c = -s • outNormal (p a) (p (a + 1)) ∧ f a = α • outNormal (p a) (p (a + 1)) ∧
      f (a + 1) = β • outNormal (p a) (p (a + 1)) ∧
      ∀ i, i ≠ c → i ≠ a → i ≠ a + 1 → f i = 0 := by
  classical
  set n := outNormal (p a) (p (a + 1)) with hn
  have hc := hds.1
  have hn0 : n ≠ 0 := PairInterior.outNormal_ne_zero hp a
  have hnn : 0 < ‖n‖ ^ 2 := by have := norm_pos_iff.mpr hn0; positivity
  have hpar := forces_parallel_of_depthSeparated hp hds hf h1 h2
  -- `f i = λ i • n`
  set l : ZMod k → ℝ := fun i => ⟪n, f i⟫ / ‖n‖ ^ 2 with hl
  have hfl : ∀ i, f i = l i • n := by
    intro i
    have := norm_sq_smul_of_cross2 (v := f i) (e := n) (by rw [cross2_comm, hpar i, neg_zero])
    apply smul_right_injective ℝ² hnn.ne'
    simp only [hl]
    rw [this, smul_smul, mul_div_cancel₀ _ hnn.ne']
  have hcone : ∀ i j, l i * ⟪n, p j - p i⟫ ≤ 0 := by
    intro i j
    have := hf i (p j) (subset_convexHull ℝ _ ⟨j, rfl⟩)
    rw [hfl i, inner_smul_left] at this; simpa using this
  have hca := hint.ne_a
  have hca' := hint.ne_a_succ
  have hk3 := hp.1
  have haa : a ≠ a + 1 := zmod_ne_add_one (by omega) a
  have hpos : ∀ i, 0 < l i → i = a ∨ i = a + 1 := by
    intro i hi
    by_contra hh; push Not at hh
    have := PairInterior.inner_lt hp a i hh.1 hh.2
    have h3 := hcone i a
    rw [inner_sub_right] at h3
    nlinarith
  have hneg : ∀ i, l i < 0 → i = c := by
    intro i hi
    by_contra hh
    have := PairInterior.min_unique hp hint hc i hh
    have h3 := hcone i c
    rw [inner_sub_right] at h3
    nlinarith
  have hsupp : ∀ i, i ≠ c → i ≠ a → i ≠ a + 1 → f i = 0 := by
    intro i h1' h2' h3'
    rw [hfl i]
    have : l i = 0 := by
      rcases lt_trichotomy (l i) 0 with h | h | h
      · exact absurd (hneg i h) h1'
      · exact h
      · rcases hpos i h with h | h
        · exact absurd h h2'
        · exact absurd h h3'
    rw [this, zero_smul]
  have hlc : l c ≤ 0 := by
    by_contra hh; push Not at hh
    rcases hpos c hh with h | h
    · exact hca h
    · exact hca' h
  have hla : 0 ≤ l a := by
    by_contra hh; push Not at hh
    exact hca (hneg a hh).symm
  have hlb : 0 ≤ l (a + 1) := by
    by_contra hh; push Not at hh
    exact hca' (hneg _ hh).symm
  -- sums over the support
  have hS : ∀ g : ZMod k → ℝ², (∀ i, i ≠ c → i ≠ a → i ≠ a + 1 → g i = 0) →
      ∑ i, g i = g a + g (a + 1) + g c := by
    intro g hg
    rw [← Finset.sum_subset (Finset.subset_univ {a, a + 1, c}) (fun i _ hi => by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
      exact hg i hi.2.2 hi.1 hi.2.1)]
    rw [Finset.sum_insert (by simp [haa, hca.symm]), Finset.sum_pair (by exact hca'.symm)]
    abel
  have E1 := hS f hsupp
  have E2 := hS (fun i => z i • f i) (fun i a1 a2 a3 => by simp [hsupp i a1 a2 a3])
  rw [h1, hfl a, hfl (a + 1), hfl c] at E1
  rw [h2] at E2
  simp only [hfl a, hfl (a + 1), hfl c, smul_smul] at E2
  have E1' : (l a + l (a + 1) + l c) • n = 0 := by rw [add_smul, add_smul]; exact E1.symm
  have E2' : (z a * l a + z (a + 1) * l (a + 1) + z c * l c) • n = 0 := by
    rw [add_smul, add_smul]; exact E2.symm
  have F1 := (smul_eq_zero.mp E1').resolve_right hn0
  have F2 := (smul_eq_zero.mp E2').resolve_right hn0
  refine ⟨-l c, l a, l (a + 1), by linarith, hla, hlb, by linarith, by linarith, ?_, hfl a, hfl _, hsupp⟩
  rw [hfl c, neg_smul]; simp [neg_smul]


theorem sum_support {M : Type*} [AddCommMonoid M] (hint : PairInterior p a c) (g : ZMod k → M)
    (hg : ∀ i, i ≠ c → i ≠ a → i ≠ a + 1 → g i = 0) (hp : IsCcwPolygon p) :
    ∑ i, g i = g a + g (a + 1) + g c := by
  classical
  have hca := hint.ne_a
  have hca' := hint.ne_a_succ
  have haa : a ≠ a + 1 := zmod_ne_add_one (by have := hp.1; omega) a
  rw [← Finset.sum_subset (Finset.subset_univ {a, a + 1, c}) (fun i _ hi => by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
    exact hg i hi.2.2 hi.1 hi.2.1)]
  rw [Finset.sum_insert (by simp [haa, hca.symm]), Finset.sum_pair (by exact hca'.symm)]
  abel

/-- The torque of the single-ray system is `s ·` `pairTorque`. -/
theorem sum_cross2_of_depthSeparated {z : ZMod k → ℝ}
    (hp : IsCcwPolygon p) (hds : IsDepthSeparatedPair p z a c) (hint : PairInterior p a c)
    {f : ZMod k → ℝ²} (hf : ∀ i, f i ∈ normalConeAt (convexHull ℝ (Set.range p)) (p i))
    (h1 : ∑ i, f i = 0) (h2 : ∑ i, z i • f i = 0) {s : ℝ}
    (hs : f c = -s • outNormal (p a) (p (a + 1))) :
    ∑ i, cross2 (p i) (f i) = s * pairTorque p z a c := by
  obtain ⟨s', α, β, hs0, hα, hβ, hss, hz, hfc, hfa, hfb, hsupp⟩ :=
    forces_supported_of_depthSeparated hp hds hint hf h1 h2
  have hn0 := PairInterior.outNormal_ne_zero hp a
  have hss' : s = s' := by
    have := hs.symm.trans hfc
    have := (smul_left_injective ℝ hn0) this
    linarith
  subst hss'
  have hD : z (a + 1) - z a ≠ 0 := by
    rcases hint.depth_between hds with ⟨u, v⟩ | ⟨u, v⟩ <;> intro h <;> linarith
  rw [sum_support hint _ (fun i a1 a2 a3 => by simp [hsupp i a1 a2 a3, cross2]) hp,
    hfa, hfb, hfc, cross2_smul_right, cross2_smul_right, cross2_smul_right, cross2_outNormal,
    cross2_outNormal, cross2_outNormal]
  have hβ' : β = s * ((z c - z a) / (z (a + 1) - z a)) := by
    field_simp; linear_combination (-1) * hz + z a * hss
  unfold pairTorque
  set d := p (a + 1) - p a with hd
  have hpa1 : p (a + 1) = p a + d := by rw [hd]; abel
  rw [hpa1]
  simp only [inner_sub_left, inner_add_left, real_inner_smul_left]
  rw [hβ']
  have : α = s - s * ((z c - z a) / (z (a + 1) - z a)) := by linarith
  rw [this]
  ring_nf

/-- A depth-separated pair with nonzero torque leaves no nonzero balanced
zero-torque force system. -/
theorem no_balanced_zeroTorque_of_depthSeparated {z : ZMod k → ℝ}
    (hp : IsCcwPolygon p) (hds : IsDepthSeparatedPair p z a c) (hint : PairInterior p a c)
    (hτ : pairTorque p z a c ≠ 0)
    {f : ZMod k → ℝ²} (hf : ∀ i, f i ∈ normalConeAt (convexHull ℝ (Set.range p)) (p i))
    (h1 : ∑ i, f i = 0) (h2 : ∑ i, z i • f i = 0) (h3 : ∑ i, cross2 (p i) (f i) = 0) :
    ∀ i, f i = 0 := by
  obtain ⟨s, α, β, hs0, hα, hβ, hss, hz, hfc, hfa, hfb, hsupp⟩ :=
    forces_supported_of_depthSeparated hp hds hint hf h1 h2
  have := sum_cross2_of_depthSeparated hp hds hint hf h1 h2 hfc
  rw [h3] at this
  have hs : s = 0 := by
    rcases mul_eq_zero.mp this.symm with h | h
    · exact h
    · exact absurd h hτ
  have ha0 : α = 0 := by linarith
  have hb0 : β = 0 := by linarith
  intro i
  by_cases h1 : i = c
  · subst h1; rw [hfc, hs]; simp
  by_cases h2 : i = a
  · subst h2; rw [hfa, ha0]; simp
  by_cases h3 : i = a + 1
  · subst h3; rw [hfb, hb0]; simp
  exact hsupp i h1 h2 h3


/-- Converse: zero torque of a depth-separated pair is a horizontal double
normal (`y = (q, z_c)`, `y' = (p c, z_c)`).  So `pairTorque ≠ 0` is implied by the
old hypothesis `¬HasHorizontalDoubleNormal`. -/
theorem hasHorizontalDoubleNormal_of_pairTorque_eq_zero {z : ZMod k → ℝ}
    (hp : IsCcwPolygon p) (hds : IsDepthSeparatedPair p z a c) (hint : PairInterior p a c)
    (hτ : pairTorque p z a c = 0) : HasHorizontalDoubleNormal p z := by
  have hc := hds.1
  have hn0 := PairInterior.outNormal_ne_zero hp a
  have hD : z (a + 1) - z a ≠ 0 := by
    rcases hint.depth_between hds with ⟨u, v⟩ | ⟨u, v⟩ <;> intro h <;> linarith
  set n := outNormal (p a) (p (a + 1)) with hn
  set d := p (a + 1) - p a with hd
  set t := (z c - z a) / (z (a + 1) - z a) with ht
  have ht0 : 0 < t := by
    rcases hint.depth_between hds with ⟨u, v⟩ | ⟨u, v⟩
    · exact div_pos_of_neg_of_neg (by linarith) (by linarith)
    · exact div_pos (by linarith) (by linarith)
  have ht1 : t < 1 := by
    rcases hint.depth_between hds with ⟨u, v⟩ | ⟨u, v⟩
    · rw [ht, div_lt_one_of_neg (by linarith)]; linarith
    · rw [ht, div_lt_one (by linarith)]; linarith
  have htD : t * (z (a + 1) - z a) = z c - z a := by rw [ht]; field_simp
  set q := p a + t • d with hq
  have hhull : ∀ r ∈ convexHull ℝ (Set.range p), ⟪n, r⟫ ≤ ⟪n, p a⟫ := by
    intro r hr
    have : convexHull ℝ (Set.range p) ⊆ {r | ⟪n, r⟫ ≤ ⟪n, p a⟫} :=
      convexHull_min (by rintro _ ⟨j, rfl⟩; exact hp.inner_outNormal_le a j)
        (convex_halfSpace_le (innerₛₗ ℝ n).isLinear _)
    exact this hr
  have hnq : ⟪n, q⟫ = ⟪n, p a⟫ := by
    have : ⟪n, d⟫ = 0 := PairInterior.inner_outNormal_self _ _
    rw [hq, inner_add_right, inner_smul_right, this]; ring
  have hlt : ⟪n, p c⟫ < ⟪n, p a⟫ := by
    have := PairInterior.min_unique hp hint hc a hint.ne_a.symm
    exact this
  set w := p c - q with hw
  have hwd : ⟪w, d⟫ = 0 := by rw [hw, hq]; exact hτ
  have hwn : cross2 w n = 0 := by
    rw [hn, cross2_outNormal]; rw [← hd]; rw [hwd]; simp
  have hwmu := norm_sq_smul_of_cross2 hwn
  have hnw : ⟪n, w⟫ < 0 := by
    rw [hw, inner_sub_right, hnq]; linarith
  have hnpos : 0 < ‖n‖ ^ 2 := by have := norm_pos_iff.mpr hn0; positivity
  set μ := ⟪n, w⟫ / ‖n‖ ^ 2 with hμ
  have hμneg : μ < 0 := div_neg_of_neg_of_pos hnw hnpos
  have hwμ : w = μ • n := by
    apply smul_right_injective ℝ² hnpos.ne'
    simp only [hμ]; rw [hwmu, smul_smul, mul_div_cancel₀ _ hnpos.ne']
  have hqc : q ≠ p c := by
    intro h
    have h1 := hp.2 a c hint.ne_a hint.ne_a_succ
    rw [← hd] at h1
    have : p c - p a = t • d := by rw [← h, hq]; abel
    rw [this, cross2_smul_right, cross2_self] at h1; simp at h1
  refine ⟨liftPt q (z c), liftPt (p c) (z c), ⟨a, ?_⟩, ⟨c, left_mem_segment ℝ _ _⟩, ?_, ?_, ?_, ?_⟩
  · refine ⟨1 - t, t, by linarith, ht0.le, by ring, ?_⟩
    ext i; fin_cases i
    · simp [liftPt, hq, hd]; ring
    · simp [liftPt, hq, hd]; ring
    · simp [liftPt]; linarith
  · simp [liftPt]
  · rw [proj_xy_liftPt, proj_xy_liftPt]; exact hqc
  · rw [proj_xy_liftPt, proj_xy_liftPt]
    intro r hr
    rw [← hw, hwμ, inner_smul_left, conj_trivial]
    have := hc r hr
    rw [inner_neg_left] at this
    nlinarith
  · rw [proj_xy_liftPt, proj_xy_liftPt]
    intro r hr
    have h2 : q - p c = -w := by rw [hw]; abel
    rw [h2, hwμ, inner_neg_left, inner_smul_left, conj_trivial]
    have := hhull r hr
    rw [inner_sub_right, hnq]
    nlinarith


/-- **Lemma 7.1 glue, zero-system form.**  As `exists_firstOrderInward_of_forces_hdn`, but
the criterion is directly that every balanced zero-torque system of corner forces
in the normal cones vanishes (no horizontal-double-normal hypothesis). -/
theorem exists_firstOrderInward_of_forces_zero (V : Finset ℝ³) {k : ℕ} [NeZero k]
    (x : ZMod k → ℝ³) (hxV : ∀ i, x i ∈ V) (hp : IsCcwPolygon (fun i => proj_xy (x i)))
    (hin : ∀ v ∈ V, (∀ i, v ≠ x i) →
      proj_xy v ∈ interior (convexHull ℝ (Set.range fun i => proj_xy (x i))))
    (H : ∀ f : ZMod k → ℝ²,
      (∀ i, f i ∈ normalConeAt (convexHull ℝ (Set.range fun i => proj_xy (x i))) (proj_xy (x i))) →
      ∑ i, f i = 0 → ∑ i, x i 2 • f i = 0 → ∑ i, cross2 (proj_xy (x i)) (f i) = 0 →
      ∀ i, f i = 0) :
    ∃ ω τ : ℝ³, FirstOrderInward V ω τ := by
  classical
  by_contra hno
  push Not at hno
  set p : ZMod k → ℝ² := fun i => proj_xy (x i) with hpdef
  set Q := convexHull ℝ (Set.range p) with hQdef
  have hSQ : proj_xy '' convexHull ℝ (V : Set ℝ³) = Q := by
    rw [show (proj_xy : ℝ³ → ℝ²) = projL from rfl, LinearMap.image_convexHull]
    apply le_antisymm
    · apply convexHull_min _ (convex_convexHull ℝ _)
      rintro _ ⟨v, hv, rfl⟩
      by_cases hc : ∃ i, v = x i
      · obtain ⟨i, rfl⟩ := hc; exact subset_convexHull ℝ _ ⟨i, rfl⟩
      · push Not at hc; exact interior_subset (hin v hv hc)
    · apply convexHull_mono
      rintro _ ⟨i, rfl⟩; exact ⟨x i, hxV i, rfl⟩
  obtain ⟨f, hfN, ⟨v₀, hv₀, hf₀⟩, hE1, hE2, hE3⟩ :=
    exists_forces_of_not_firstOrderInward V (by rw [hSQ]; exact hp.interior_nonempty) hno
  rw [hSQ] at hfN
  have hzero : ∀ v ∈ V, (∀ i, v ≠ x i) → f v = 0 := fun v hv hc =>
    normalConeAt_eq_zero_of_mem_interior (hin v hv hc) (hfN v hv)
  have hxinj : Function.Injective x := fun i j h => hp.injective (by rw [hpdef]; dsimp only; rw [h])
  have himg : univ.image x ⊆ V := fun v hv => by
    obtain ⟨i, -, rfl⟩ := mem_image.mp hv; exact hxV i
  have hred : ∀ {M : Type} [AddCommMonoid M] (G : ℝ³ → M), (∀ v, f v = 0 → G v = 0) →
      ∑ v ∈ V, G v = ∑ i, G (x i) := by
    intro M _ G hG
    rw [← sum_subset himg (fun v hv hni => hG v (hzero v hv fun i h => hni (by
      rw [h]; exact mem_image_of_mem x (mem_univ i)))), sum_image (fun i _ j _ h => hxinj h)]
  have hall := H (fun i => f (x i)) (fun i => hfN (x i) (hxV i))
    (by rw [← hred f (fun v h => h)]; exact hE1)
    (by rw [← hred (fun v => v 2 • f v) (fun v h => by simp [h])]; exact hE2)
    (by rw [← hred (fun v => cross2 (proj_xy v) (f v)) (fun v h => by simp [h, cross2])]; exact hE3)
  by_cases hc : ∃ i, v₀ = x i
  · obtain ⟨i, rfl⟩ := hc; exact hf₀ (hall i)
  · push Not at hc; exact hf₀ (hzero v₀ hv₀ hc)


/-- **Theorem 8.10 with torque, standard view.** -/
theorem exists_firstOrderInward_of_depthSeparated_torque (V : Finset ℝ³) {k : ℕ} [NeZero k]
    (x : ZMod k → ℝ³) (hxV : ∀ i, x i ∈ V) (hp : IsCcwPolygon (fun i => proj_xy (x i)))
    (hin : ∀ v ∈ V, (∀ i, v ≠ x i) →
      proj_xy v ∈ interior (convexHull ℝ (Set.range fun i => proj_xy (x i))))
    {a c : ZMod k} (hds : IsDepthSeparatedPair (fun i => proj_xy (x i)) (fun i => x i 2) a c)
    (hint : PairInterior (fun i => proj_xy (x i)) a c)
    (hτ : pairTorque (fun i => proj_xy (x i)) (fun i => x i 2) a c ≠ 0) :
    ∃ ω τ : ℝ³, FirstOrderInward V ω τ :=
  exists_firstOrderInward_of_forces_zero V x hxV hp hin
    (fun f hf h1 h2 h3 => no_balanced_zeroTorque_of_depthSeparated hp hds hint hτ hf h1 h2 h3)

/-- **Theorem 8.10 with torque, rotated view.**  As
`exists_firstOrderInward_image_of_depthSeparated` with `¬HasHorizontalDoubleNormal`
replaced by the pair's torque being nonzero (and the interior condition). -/
theorem exists_firstOrderInward_image_of_depthSeparated_torque (V : Finset ℝ³)
    (R : Matrix (Fin 3) (Fin 3) ℝ) (x : ZMod k → ℝ³) (hxV : ∀ i, x i ∈ V)
    (hp : IsCcwPolygon (fun i => proj_xy (R.toEuclideanLin (x i))))
    (hin : ∀ v ∈ V, (∀ i, v ≠ x i) → proj_xy (R.toEuclideanLin v) ∈
      interior (convexHull ℝ (Set.range fun i => proj_xy (R.toEuclideanLin (x i)))))
    (hds : IsDepthSeparatedPair (fun i => proj_xy (R.toEuclideanLin (x i)))
      (fun i => (R.toEuclideanLin (x i)) 2) a c)
    (hint : PairInterior (fun i => proj_xy (R.toEuclideanLin (x i))) a c)
    (hτ : pairTorque (fun i => proj_xy (R.toEuclideanLin (x i)))
      (fun i => (R.toEuclideanLin (x i)) 2) a c ≠ 0) :
    ∃ ω τ : ℝ³, FirstOrderInward (V.image R.toEuclideanLin) ω τ := by
  classical
  exact exists_firstOrderInward_of_depthSeparated_torque (V.image R.toEuclideanLin)
    (fun i => R.toEuclideanLin (x i)) (fun i => mem_image_of_mem _ (hxV i)) hp
    (by
      intro w hw hc
      obtain ⟨v, hv, rfl⟩ := mem_image.mp hw
      exact hin v hv fun i h => hc i (by rw [h]))
    hds hint hτ

/-- **Proposition 8.8 with a depth-separated `K′` and the torque hypothesis**
(the form Lemma 22.4 / 27.41 Step 4 needs): as `isRupert_of_chords_depthSeparated`
with `¬HasHorizontalDoubleNormal` replaced by `pairTorque ≠ 0` and `PairInterior`. -/
theorem isRupert_of_chords_depthSeparated_torque (V M : Finset ℝ³)
    (R : Matrix (Fin 3) (Fin 3) ℝ)
    (hR : R ∈ SO3) {u₀ : ℝ³} {r : ℝ} (hr : 0 < r) (hRu : R.toEuclideanLin u₀ = r • ez)
    (x : ZMod k → ℝ³) (hxV : ∀ i, x i ∈ V) (hxM : ∀ i, x i ∉ M)
    (hp : IsCcwPolygon (fun i => proj_xy (R.toEuclideanLin (x i))))
    (hin : ∀ v ∈ V, v ∉ M → (∀ i, v ≠ x i) → proj_xy (R.toEuclideanLin v) ∈
      interior (convexHull ℝ (Set.range fun i => proj_xy (R.toEuclideanLin (x i)))))
    (hds : IsDepthSeparatedPair (fun i => proj_xy (R.toEuclideanLin (x i)))
      (fun i => (R.toEuclideanLin (x i)) 2) a c)
    (hint : PairInterior (fun i => proj_xy (R.toEuclideanLin (x i))) a c)
    (hτ : pairTorque (fun i => proj_xy (R.toEuclideanLin (x i)))
      (fun i => (R.toEuclideanLin (x i)) 2) a c ≠ 0)
    (hM : ∀ m ∈ M, ∃ i : ZMod k, ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
      m = x i + s • (x (i + 1) - x i) + δ • u₀) : IsRupert V := by
  classical
  exact isRupert_of_chords_of_firstOrderInward V M R hR hr hRu x hxV hxM hp hin
    (exists_firstOrderInward_image_of_depthSeparated_torque (V \ M) R x
      (fun i => mem_sdiff.mpr ⟨hxV i, hxM i⟩) hp
      (fun v hv hvx => hin v (mem_sdiff.mp hv).1 (mem_sdiff.mp hv).2 hvx) hds hint hτ) hM

end Minimality
