module

public import Minimality.Type24Metric
public import Minimality.SlideDS

@[expose] public section

/-!
# Type 24 at every metric: the sink lemma and side-safety (§20, continued: 20.2 (d), 20.8′)

`FEWER-FACES-PROOFS.md` §20, continued (refereed 2026-10-22, scratch `referee_OO/`), at `K`'s own
metric (the depth at a view `d` is `⟪·, d⟫`).

* **Lemma 20.2 (b), converse form** (`exists_dip_of_not_unimodal`): a cycle that is not
  unimodal, whose corner `0` is below a neighbour, has a *dip* (a strict local minimum) in the
  interior of the path `1, …, k − 1`.
* **Rim facts** (`CapRim0.swap`, `CapRim0.rinj`, `CapRim0.ne_ax`, `CapRim0.path`): the rim data
  `CapRim0` is symmetric in the two ends, its labels are distinct and avoid the axis vertex, so
  its far corners are among `3, 4, 5`.
* **Lemma 20.2 (d), the sink lemma** (`capRim0_sink`; for `E_2`, `E_6`, whose far path starts or
  ends at `0`, `capRim0_sink_zero`, `Type24.sinkE2`, `Type24.sinkE6`; for `E_0`,
  `Type24.sinkE0`): a cap-edge crossing that fails with a rim end above the cap has a far corner
  at or below the higher end, or (only possible for `E_0`) three far corners, the middle corner
  `3` a weak local minimum and `min (z4, z5) ≤ z0`.
* **The `m = 2` corollary** (`not_unimodal_five_iff`, `not_unimodal_five_iff'`,
  `capRim0_five_fails_iff`): with `z(w) < z(1) < z(y)`, a 5-corner cap rim
  `(1, y, r_y, r_w, w)` fails iff `z(r_y) < min (z(y), z(r_w))` and `z(r_w) > z(w)`.
* **The common sink** (`common_sink`): two cap edges sinking at the same far corner below the
  shared end `h_ij` leave it below `max (z(i), z(j))` at every view `e_i + t e_j`, `t > 0`.
* **Side-safety** (`SideSafe`, `AcuteSafe.sideSafe`, `AcuteSafe.sideSafe'`,
  `acuteSafe_of_sideSafe`; Rupert forms `isRupert_capEdge_sideSafe`,
  `isRupert_capEdge_sideSafe'`): `E_x` is *safe on side `y`* if its rim depths
  `g X_x + h_y X_y + h_w X_w` are unimodal (when distinct) for every `g > 0`, `h_y > 0` and
  every `h_w`.  The six sides of the three cap edges (`Type24.SafeE2at0`, …), and
  `Type24.SideCovered`: each cosine `c_ab`, `c_ac`, `c_bc` is seen on a safe side.
* **Theorem 20.8′** (`isRupert_type24_side_safe`, `Type24.obtuse_of_side_safe`): Conjecture A
  for every class whose three cosines are side-covered.  Theorem 20.8 is the special case of two
  acute-safe cap edges (`Type24.sideCovered_of_twoSafe`).
* **Theorem 8.10 as a cap-edge item** (`isRupert_capRim0_depthSeparated`,
  `isRupert_capRim0_uos`; general edge views `isRupert_of_edgeView_depthSeparated`): a cap-edge
  crossing whose rim has a depth-separated parallel pair (`DepthSepAt`) certifies `K` even when
  its rim depths are not unimodal (the proxy "unimodal or depth-separated" of Conjecture B_DS).
  For a 4-corner rim this adds nothing (`not_fails4_of_depthSepAt`: a depth-separated pair puts
  the two neighbours of `c` on opposite sides, `DepthSepAt.nbrs`, which a failing 4-corner
  pattern never does), so the window chain's tests are unchanged; it matters for rims with 5 or 6 corners, such as the three edge crossings that
  certify the counterexample G1 to the weak form of Conjecture B.

Not formalized: the LPs that decide side-safety (`SideSafe` is a hypothesis, as `AcuteSafe` is),
the geometric half of 17.9 (`3` is the middle far corner when there are three, and `3` lies in
the plane of `0, 4, 5`: hypotheses, as in `Type24.hcap2`), the class counts.
-/

namespace Minimality

open Finset
open scoped RealInnerProductSpace

/-! ### Lemma 20.2 (b), converse form: a failing rim dips -/

/-- **A failing rim dips** (Lemma 20.2 (b), contrapositive of `isCyclicUnimodal_of_noDip`).  A
cyclic sequence of distinct values whose corner `0` is below one of its neighbours, and which is
not unimodal, has a strict local minimum at an interior position `n + 1` of the path
`1, …, k − 1` (`1 ≤ n`, `n + 3 ≤ k`). -/
theorem exists_dip_of_not_unimodal {k : ℕ} [NeZero k] (hk : 3 ≤ k) {z : ZMod k → ℝ}
    (hinj : Function.Injective z) (h0 : z 0 < z 1 ∨ z 0 < z ((k - 1 : ℕ) : ZMod k))
    (hF : ¬ IsCyclicUnimodal z) :
    ∃ n : ℕ, 1 ≤ n ∧ n + 3 ≤ k ∧ z ((n + 1 : ℕ) : ZMod k) < z (n : ZMod k) ∧
      z ((n + 1 : ℕ) : ZMod k) < z ((n + 2 : ℕ) : ZMod k) := by
  by_contra h
  exact hF (isCyclicUnimodal_of_noDip hk hinj h0 fun n h1 h2 hc => h ⟨n, h1, h2, hc.1, hc.2⟩)

/-! ### Facts about the rim of a cap-edge crossing -/

theorem natCast_zmod_inj {k : ℕ} {a b : ℕ} (ha : a < k) (hb : b < k)
    (h : (a : ZMod k) = (b : ZMod k)) : a = b := by
  rwa [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h

section CapRim0

variable {x : Fin 7 → ℝ³} {ax ay aw : Fin 7} {k : ℕ} [NeZero k] {r : ZMod k → Fin 7}

/-- The rim data of a cap-edge crossing is symmetric in the two ends of the far path. -/
theorem CapRim0.swap (hR : CapRim0 x ax ay aw k r) : CapRim0 x ax aw ay k r := by
  obtain ⟨hk, hr0, hends, rest⟩ := hR
  exact ⟨hk, hr0, hends.symm, rest⟩

/-- The labels of the rim are distinct (the rim depths are). -/
theorem CapRim0.rinj (hR : CapRim0 x ax ay aw k r) : Function.Injective r := fun _ _ e =>
  hR.2.2.2.2.2.1 (congrArg (fun v => ⟪x v, x ax - x 1⟫) e)

/-- The axis vertex `ax` (a double over the cap `1`) is not a rim corner. -/
theorem CapRim0.ne_ax (hR : CapRim0 x ax ay aw k r) (i : ZMod k) : r i ≠ ax := by
  obtain ⟨hk, hr0, -, hcyc, -⟩ := hR
  have n10 : ((1 : ℕ) : ZMod k) ≠ ((0 : ℕ) : ZMod k) := fun h => by
    have := natCast_zmod_inj (by omega) (by omega) h; omega
  have n20 : ((2 : ℕ) : ZMod k) ≠ ((0 : ℕ) : ZMod k) := fun h => by
    have := natCast_zmod_inj (by omega) (by omega) h; omega
  simp only [Nat.cast_one, Nat.cast_zero, Nat.cast_ofNat] at n10 n20
  have e11 : (1 : ZMod k) + 1 = 2 := one_add_one_eq_two
  intro e
  by_cases hi0 : i = 0
  · subst hi0
    rw [hr0] at e
    have := hcyc 1 0 n10.symm (by rw [e11]; exact n20.symm)
    rw [← e, sub_self] at this
    simp [det3_expand] at this
  by_cases hi1 : i = 1
  · subst hi1
    have := hcyc 1 0 n10.symm (by rw [e11]; exact n20.symm)
    rw [e, hr0] at this
    have h0 : det3 (x (r (1 + 1)) - x ax) (x 1 - x ax) (x ax - x 1) = 0 := by
      simp only [det3_expand, PiLp.sub_apply]; ring
    rw [h0] at this
    exact lt_irrefl _ this
  · have := hcyc 0 i hi0 (by rw [zero_add]; exact hi1)
    rw [e, hr0, det3_self_right'] at this
    exact lt_irrefl _ this

/-- **The far corners**: every rim position `2 ≤ n ≤ k − 2` carries a label other than `1`, the
two ends and the axis vertex; for type 24 these are among `3, 4, 5`. -/
theorem CapRim0.path (hR : CapRim0 x ax ay aw k r)
    (hlab : ∀ v : Fin 7, v ≠ 1 → v ≠ ax → v ≠ ay → v ≠ aw → v = 3 ∨ v = 4 ∨ v = 5) :
    ∀ n : ℕ, 2 ≤ n → n + 2 ≤ k → r n = 3 ∨ r n = 4 ∨ r n = 5 := by
  intro n h2 hk2
  have hrinj := hR.rinj
  have hax := hR.ne_ax
  obtain ⟨hk, hr0, hends, -⟩ := hR
  have hne : ∀ m : ℕ, m < k → m ≠ n → r n ≠ r m := fun m hm hmn e =>
    hmn (natCast_zmod_inj (by omega) hm (hrinj e)).symm
  have r0 : r ((0 : ℕ) : ZMod k) = 1 := by rw [Nat.cast_zero]; exact hr0
  have r1 : ∀ v, r 1 = v → r ((1 : ℕ) : ZMod k) = v := fun v e => by rw [Nat.cast_one]; exact e
  apply hlab
  · rw [← r0]; exact hne 0 (by omega) (by omega)
  · exact hax _
  · rcases hends with ⟨e1, -⟩ | ⟨-, e2⟩
    · rw [← r1 _ e1]; exact hne 1 (by omega) (by omega)
    · rw [← e2]; exact hne (k - 1) (by omega) (by omega)
  · rcases hends with ⟨-, e2⟩ | ⟨e1, -⟩
    · rw [← e2]; exact hne (k - 1) (by omega) (by omega)
    · rw [← r1 _ e1]; exact hne 1 (by omega) (by omega)

/-! ### Lemma 20.2 (d): the sink lemma -/

/-- **Lemma 20.2 (d), the sink lemma.**  Let a cap-edge crossing (view `u = x ax − x 1`) have
the rim data `CapRim0`, its far corners among `3, 4, 5` (`hpath`), `3` in the middle when there
are three (`hmid`), and `3` in the plane of `0, 4, 5` opposite `0` (17.4).  If one rim end is
above the cap (`hsign`) and the rim is not unimodal (`E_x` fails), then some far corner is at or
below the higher end, or there are three far corners, the middle one `3` is a weak local
minimum, and `min (z4, z5) ≤ z0`. -/
theorem capRim0_sink (hR : CapRim0 x ax ay aw k r)
    (hpath : ∀ n : ℕ, 2 ≤ n → n + 2 ≤ k → r n = 3 ∨ r n = 4 ∨ r n = 5)
    (hmid : ∀ n : ℕ, 3 ≤ n → n + 3 ≤ k → r n = 3)
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (hst : 1 < s + t)
    (hq : x 3 = x 0 + s • (x 4 - x 0) + t • (x 5 - x 0))
    (hsign : 0 < ⟪x ay - x 1, x ax - x 1⟫ ∨ 0 < ⟪x aw - x 1, x ax - x 1⟫)
    (hF : ¬ IsCyclicUnimodal fun i => ⟪x (r i), x ax - x 1⟫) :
    (∃ n : ℕ, 2 ≤ n ∧ n + 2 ≤ k ∧
      ⟪x (r n), x ax - x 1⟫ ≤ max ⟪x ay, x ax - x 1⟫ ⟪x aw, x ax - x 1⟫) ∨
    (∃ n : ℕ, 2 ≤ n ∧ n + 4 ≤ k ∧ r ((n + 1 : ℕ) : ZMod k) = 3 ∧
      ((r n = 4 ∧ r ((n + 2 : ℕ) : ZMod k) = 5) ∨ (r n = 5 ∧ r ((n + 2 : ℕ) : ZMod k) = 4)) ∧
      ⟪x 3, x ax - x 1⟫ ≤ ⟪x 4, x ax - x 1⟫ ∧ ⟪x 3, x ax - x 1⟫ ≤ ⟪x 5, x ax - x 1⟫ ∧
      (⟪x 4, x ax - x 1⟫ ≤ ⟪x 0, x ax - x 1⟫ ∨ ⟪x 5, x ax - x 1⟫ ≤ ⟪x 0, x ax - x 1⟫)) := by
  have hrinj := hR.rinj
  obtain ⟨hk, hr0, hends, -, -, hz, -⟩ := hR
  obtain ⟨n, h1, h3, c1, c2⟩ :=
    exists_dip_of_not_unimodal hk hz (capRim0_h0 hr0 hends hsign) hF
  have hend1 : ⟪x (r 1), x ax - x 1⟫ ≤ max ⟪x ay, x ax - x 1⟫ ⟪x aw, x ax - x 1⟫ := by
    rcases hends with ⟨e1, -⟩ | ⟨e1, -⟩ <;> rw [e1]
    · exact le_max_left _ _
    · exact le_max_right _ _
  have hendk : ⟪x (r ((k - 1 : ℕ) : ZMod k)), x ax - x 1⟫ ≤
      max ⟪x ay, x ax - x 1⟫ ⟪x aw, x ax - x 1⟫ := by
    rcases hends with ⟨-, e2⟩ | ⟨-, e2⟩ <;> rw [e2]
    · exact le_max_right _ _
    · exact le_max_left _ _
  rcases Nat.lt_or_ge n 2 with hn | hn
  · -- the dip is next to the first end
    obtain rfl : n = 1 := by omega
    left
    refine ⟨2, le_rfl, by omega, ?_⟩
    rw [Nat.cast_one] at c1
    exact (c1.trans_le hend1).le
  rcases Nat.lt_or_ge (n + 3) k with hk' | hk'
  · -- the dip is the middle corner `3`
    have m3 := hmid (n + 1) (by omega) (by omega)
    have a := hpath n hn (by omega)
    have b := hpath (n + 2) (by omega) (by omega)
    have hne : ∀ i j : ℕ, i < k → j < k → i ≠ j → r (i : ZMod k) ≠ r (j : ZMod k) :=
      fun i j hi hj hij e => hij (natCast_zmod_inj hi hj (hrinj e))
    have na : r n ≠ 3 := by rw [← m3]; exact hne n (n + 1) (by omega) (by omega) (by omega)
    have nb : r ((n + 2 : ℕ) : ZMod k) ≠ 3 := by
      rw [← m3]; exact hne (n + 2) (n + 1) (by omega) (by omega) (by omega)
    have nab : r n ≠ r ((n + 2 : ℕ) : ZMod k) := hne n (n + 2) (by omega) (by omega) (by omega)
    have hab : (r n = 4 ∧ r ((n + 2 : ℕ) : ZMod k) = 5) ∨
        (r n = 5 ∧ r ((n + 2 : ℕ) : ZMod k) = 4) := by
      rcases a with a | a | a
      · exact absurd a na
      · rcases b with b | b | b
        · exact absurd b nb
        · exact absurd (a.trans b.symm) nab
        · exact Or.inl ⟨a, b⟩
      · rcases b with b | b | b
        · exact absurd b nb
        · exact Or.inr ⟨a, b⟩
        · exact absurd (a.trans b.symm) nab
    rw [m3] at c1 c2
    have w45 : ⟪x 3, x ax - x 1⟫ ≤ ⟪x 4, x ax - x 1⟫ ∧ ⟪x 3, x ax - x 1⟫ ≤ ⟪x 5, x ax - x 1⟫ := by
      rcases hab with ⟨ea, eb⟩ | ⟨ea, eb⟩ <;> rw [ea] at c1 <;> rw [eb] at c2
      · exact ⟨c1.le, c2.le⟩
      · exact ⟨c2.le, c1.le⟩
    right
    refine ⟨n, hn, by omega, m3, hab, w45.1, w45.2, ?_⟩
    by_contra hc
    simp only [not_or, not_le] at hc
    exact mid3_not_dip hq hs ht hst hc.1 hc.2 w45
  · -- the dip is next to the last end
    left
    refine ⟨n + 1, by omega, by omega, ?_⟩
    have e : ((n + 2 : ℕ) : ZMod k) = ((k - 1 : ℕ) : ZMod k) := by congr 1; omega
    rw [e] at c2
    exact (c2.trans_le hendk).le

/-- **Lemma 20.2 (d) for a cap edge with `0` at an end of its far path** (`E_2`, `E_6`): some far
corner is at or below the higher end. -/
theorem capRim0_sink_zero (hR : CapRim0 x ax ay aw k r) (h0 : ay = 0 ∨ aw = 0)
    (hpath : ∀ n : ℕ, 2 ≤ n → n + 2 ≤ k → r n = 3 ∨ r n = 4 ∨ r n = 5)
    (hmid : ∀ n : ℕ, 3 ≤ n → n + 3 ≤ k → r n = 3)
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (hst : 1 < s + t)
    (hq : x 3 = x 0 + s • (x 4 - x 0) + t • (x 5 - x 0))
    (hsign : 0 < ⟪x ay - x 1, x ax - x 1⟫ ∨ 0 < ⟪x aw - x 1, x ax - x 1⟫)
    (hF : ¬ IsCyclicUnimodal fun i => ⟪x (r i), x ax - x 1⟫) :
    ∃ n : ℕ, 2 ≤ n ∧ n + 2 ≤ k ∧
      ⟪x (r n), x ax - x 1⟫ ≤ max ⟪x ay, x ax - x 1⟫ ⟪x aw, x ax - x 1⟫ := by
  rcases capRim0_sink hR hpath hmid hs ht hst hq hsign hF with h | ⟨n, hn, hk4, -, hab, -, -, h45⟩
  · exact h
  have hz0 : ⟪x 0, x ax - x 1⟫ ≤ max ⟪x ay, x ax - x 1⟫ ⟪x aw, x ax - x 1⟫ := by
    rcases h0 with rfl | rfl
    · exact le_max_left _ _
    · exact le_max_right _ _
  rcases h45 with h4 | h5
  · rcases hab with ⟨ea, -⟩ | ⟨-, eb⟩
    · exact ⟨n, hn, by omega, by rw [ea]; exact h4.trans hz0⟩
    · exact ⟨n + 2, by omega, by omega, by rw [eb]; exact h4.trans hz0⟩
  · rcases hab with ⟨-, eb⟩ | ⟨ea, -⟩
    · exact ⟨n + 2, by omega, by omega, by rw [eb]; exact h5.trans hz0⟩
    · exact ⟨n, hn, by omega, by rw [ea]; exact h5.trans hz0⟩

end CapRim0

namespace Type24

variable {x : Fin 7 → ℝ³} {k : ℕ} [NeZero k] {r : ZMod k → Fin 7}

/-- **Lemma 20.2 (d) for `E_2 = 012/126-2`** (view `e_b`, far path from `0` to `6`): if `E_2`
fails while `z0 > z1` or `z6 > z1`, some far corner has `z ≤ max (z0, z6)`. -/
theorem sinkE2 (hR : CapRim0 x 2 0 6 k r) (hmid : ∀ n : ℕ, 3 ≤ n → n + 3 ≤ k → r n = 3)
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (hst : 1 < s + t)
    (hq : x 3 = x 0 + s • (x 4 - x 0) + t • (x 5 - x 0))
    (hsign : 0 < ⟪x 0 - x 1, x 2 - x 1⟫ ∨ 0 < ⟪x 6 - x 1, x 2 - x 1⟫)
    (hF : ¬ IsCyclicUnimodal fun i => ⟪x (r i), x 2 - x 1⟫) :
    ∃ n : ℕ, 2 ≤ n ∧ n + 2 ≤ k ∧ ⟪x (r n), x 2 - x 1⟫ ≤ max ⟪x 0, x 2 - x 1⟫ ⟪x 6, x 2 - x 1⟫ :=
  capRim0_sink_zero hR (Or.inl rfl) (hR.path (by decide)) hmid hs ht hst hq hsign hF

/-- **Lemma 20.2 (d) for `E_6 = 016/126-6`** (view `e_c`, far path from `2` to `0`). -/
theorem sinkE6 (hR : CapRim0 x 6 2 0 k r) (hmid : ∀ n : ℕ, 3 ≤ n → n + 3 ≤ k → r n = 3)
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (hst : 1 < s + t)
    (hq : x 3 = x 0 + s • (x 4 - x 0) + t • (x 5 - x 0))
    (hsign : 0 < ⟪x 2 - x 1, x 6 - x 1⟫ ∨ 0 < ⟪x 0 - x 1, x 6 - x 1⟫)
    (hF : ¬ IsCyclicUnimodal fun i => ⟪x (r i), x 6 - x 1⟫) :
    ∃ n : ℕ, 2 ≤ n ∧ n + 2 ≤ k ∧ ⟪x (r n), x 6 - x 1⟫ ≤ max ⟪x 2, x 6 - x 1⟫ ⟪x 0, x 6 - x 1⟫ :=
  capRim0_sink_zero hR (Or.inr rfl) (hR.path (by decide)) hmid hs ht hst hq hsign hF

/-- **Lemma 20.2 (d) for `E_0 = 012/016-0`** (view `e_a`, far path from `2` to `6`): some far
corner has `z ≤ max (z2, z6)`, or the middle far corner `3` is a weak local minimum and
`min (z4, z5) ≤ z0` (`z0 − z1 = g_a`).  The second alternative is needed. -/
theorem sinkE0 (hR : CapRim0 x 0 2 6 k r) (hmid : ∀ n : ℕ, 3 ≤ n → n + 3 ≤ k → r n = 3)
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (hst : 1 < s + t)
    (hq : x 3 = x 0 + s • (x 4 - x 0) + t • (x 5 - x 0))
    (hsign : 0 < ⟪x 2 - x 1, x 0 - x 1⟫ ∨ 0 < ⟪x 6 - x 1, x 0 - x 1⟫)
    (hF : ¬ IsCyclicUnimodal fun i => ⟪x (r i), x 0 - x 1⟫) :
    (∃ n : ℕ, 2 ≤ n ∧ n + 2 ≤ k ∧
      ⟪x (r n), x 0 - x 1⟫ ≤ max ⟪x 2, x 0 - x 1⟫ ⟪x 6, x 0 - x 1⟫) ∨
    (∃ n : ℕ, 2 ≤ n ∧ n + 4 ≤ k ∧ r ((n + 1 : ℕ) : ZMod k) = 3 ∧
      ((r n = 4 ∧ r ((n + 2 : ℕ) : ZMod k) = 5) ∨ (r n = 5 ∧ r ((n + 2 : ℕ) : ZMod k) = 4)) ∧
      ⟪x 3, x 0 - x 1⟫ ≤ ⟪x 4, x 0 - x 1⟫ ∧ ⟪x 3, x 0 - x 1⟫ ≤ ⟪x 5, x 0 - x 1⟫ ∧
      (⟪x 4, x 0 - x 1⟫ ≤ ⟪x 0, x 0 - x 1⟫ ∨ ⟪x 5, x 0 - x 1⟫ ≤ ⟪x 0, x 0 - x 1⟫)) :=
  capRim0_sink hR (hR.path (by decide)) hmid hs ht hst hq hsign hF

end Type24

/-! ### The `m = 2` corollary -/

/-- **Five corners, the cap between its neighbours** (`z 4 < z 0 < z 1`): the cycle fails to be
unimodal iff both `2` and `4` are local minima, i.e. `z 2 < min (z 1, z 3)` and `z 4 < z 3`. -/
theorem not_unimodal_five_iff {z : ZMod 5 → ℝ} (hinj : Function.Injective z) (h40 : z 4 < z 0)
    (h01 : z 0 < z 1) : ¬ IsCyclicUnimodal z ↔ z 2 < z 1 ∧ z 2 < z 3 ∧ z 4 < z 3 := by
  have i0 : (0 : ZMod 5) - 1 = 4 := by decide
  have i1 : (1 : ZMod 5) - 1 = 0 := by decide
  have i2 : (2 : ZMod 5) - 1 = 1 := by decide
  have i3 : (3 : ZMod 5) - 1 = 2 := by decide
  have i4 : (4 : ZMod 5) - 1 = 3 := by decide
  have j0 : (0 : ZMod 5) + 1 = 1 := by decide
  have j1 : (1 : ZMod 5) + 1 = 2 := by decide
  have j2 : (2 : ZMod 5) + 1 = 3 := by decide
  have j3 : (3 : ZMod 5) + 1 = 4 := by decide
  have j4 : (4 : ZMod 5) + 1 = 0 := by decide
  constructor
  · intro hF
    by_contra hc
    apply hF
    refine isCyclicUnimodal_of_atMostOne (by norm_num) hinj fun i j hi hj => ?_
    have hmax : ∀ i : ZMod 5, z (i - 1) < z i ∧ z (i + 1) < z i →
        (i = 1 ∧ z 2 < z 1) ∨ (i = 2 ∧ z 1 < z 2 ∧ z 3 < z 2) ∨ (i = 3 ∧ z 2 < z 3 ∧ z 4 < z 3) := by
      intro i hi
      rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl
      · rw [j0] at hi; exact absurd hi.2 (not_lt.mpr h01.le)
      · rw [j1] at hi; exact Or.inl ⟨rfl, hi.2⟩
      · rw [i2, j2] at hi; exact Or.inr (Or.inl ⟨rfl, hi.1, hi.2⟩)
      · rw [i3, j3] at hi; exact Or.inr (Or.inr ⟨rfl, hi.1, hi.2⟩)
      · rw [j4] at hi; exact absurd hi.2 (not_lt.mpr h40.le)
    rcases hmax i hi with ⟨rfl, a⟩ | ⟨rfl, a, a'⟩ | ⟨rfl, a, a'⟩ <;>
      rcases hmax j hj with ⟨rfl, b⟩ | ⟨rfl, b, b'⟩ | ⟨rfl, b, b'⟩ <;>
      first
      | rfl
      | (exfalso; linarith)
      | exact (hc ⟨by assumption, by assumption, by assumption⟩).elim
  · rintro ⟨a, b, c⟩ hU
    have m1 : (1 : ZMod 5) ∈ univ.filter (fun i : ZMod 5 => z (i - 1) < z i ∧ z (i + 1) < z i) :=
      mem_filter.mpr ⟨mem_univ _, by rw [i1, j1]; exact ⟨h01, a⟩⟩
    have m3 : (3 : ZMod 5) ∈ univ.filter (fun i : ZMod 5 => z (i - 1) < z i ∧ z (i + 1) < z i) :=
      mem_filter.mpr ⟨mem_univ _, by rw [i3, j3]; exact ⟨b, c⟩⟩
    exact absurd (Finset.card_le_one.mp hU.2.le _ m1 _ m3) (by decide)

/-- **Five corners, the mirror** (`z 1 < z 0 < z 4`): the cycle fails to be unimodal iff
`z 3 < min (z 4, z 2)` and `z 1 < z 2`. -/
theorem not_unimodal_five_iff' {z : ZMod 5 → ℝ} (hinj : Function.Injective z) (h10 : z 1 < z 0)
    (h04 : z 0 < z 4) : ¬ IsCyclicUnimodal z ↔ z 3 < z 4 ∧ z 3 < z 2 ∧ z 1 < z 2 := by
  have i0 : (0 : ZMod 5) - 1 = 4 := by decide
  have i1 : (1 : ZMod 5) - 1 = 0 := by decide
  have i2 : (2 : ZMod 5) - 1 = 1 := by decide
  have i3 : (3 : ZMod 5) - 1 = 2 := by decide
  have i4 : (4 : ZMod 5) - 1 = 3 := by decide
  have j0 : (0 : ZMod 5) + 1 = 1 := by decide
  have j1 : (1 : ZMod 5) + 1 = 2 := by decide
  have j2 : (2 : ZMod 5) + 1 = 3 := by decide
  have j3 : (3 : ZMod 5) + 1 = 4 := by decide
  have j4 : (4 : ZMod 5) + 1 = 0 := by decide
  constructor
  · intro hF
    by_contra hc
    apply hF
    refine isCyclicUnimodal_of_atMostOne (by norm_num) hinj fun i j hi hj => ?_
    have hmax : ∀ i : ZMod 5, z (i - 1) < z i ∧ z (i + 1) < z i →
        (i = 4 ∧ z 3 < z 4) ∨ (i = 3 ∧ z 2 < z 3 ∧ z 4 < z 3) ∨ (i = 2 ∧ z 1 < z 2 ∧ z 3 < z 2) := by
      intro i hi
      rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl
      · rw [i0] at hi; exact absurd hi.1 (not_lt.mpr h04.le)
      · rw [i1] at hi; exact absurd hi.1 (not_lt.mpr h10.le)
      · rw [i2, j2] at hi; exact Or.inr (Or.inr ⟨rfl, hi.1, hi.2⟩)
      · rw [i3, j3] at hi; exact Or.inr (Or.inl ⟨rfl, hi.1, hi.2⟩)
      · rw [i4] at hi; exact Or.inl ⟨rfl, hi.1⟩
    rcases hmax i hi with ⟨rfl, a⟩ | ⟨rfl, a, a'⟩ | ⟨rfl, a, a'⟩ <;>
      rcases hmax j hj with ⟨rfl, b⟩ | ⟨rfl, b, b'⟩ | ⟨rfl, b, b'⟩ <;>
      first
      | rfl
      | (exfalso; linarith)
      | exact (hc ⟨by assumption, by assumption, by assumption⟩).elim
  · rintro ⟨a, b, c⟩ hU
    have m4 : (4 : ZMod 5) ∈ univ.filter (fun i : ZMod 5 => z (i - 1) < z i ∧ z (i + 1) < z i) :=
      mem_filter.mpr ⟨mem_univ _, by rw [i4, j4]; exact ⟨a, h04⟩⟩
    have m2 : (2 : ZMod 5) ∈ univ.filter (fun i : ZMod 5 => z (i - 1) < z i ∧ z (i + 1) < z i) :=
      mem_filter.mpr ⟨mem_univ _, by rw [i2, j2]; exact ⟨c, b⟩⟩
    exact absurd (Finset.card_le_one.mp hU.2.le _ m4 _ m2) (by decide)

/-- **The `m = 2` corollary of Lemma 20.2 (d).**  A cap-edge rim `(1, y, r_y, r_w, w)` (in either
orientation, `r_y` next to `y`) with `z(w) < z(1) < z(y)` fails iff
`z(r_y) < min (z(y), z(r_w))` and `z(r_w) > z(w)` (the depths being distinct). -/
theorem capRim0_five_fails_iff {x : Fin 7 → ℝ³} {ax ay aw : Fin 7} {r : ZMod 5 → Fin 7}
    (hR : CapRim0 x ax ay aw 5 r) {ry rw : Fin 7}
    (hor : (r 1 = ay ∧ r 2 = ry ∧ r 3 = rw ∧ r 4 = aw) ∨ (r 1 = aw ∧ r 2 = rw ∧ r 3 = ry ∧ r 4 = ay))
    (hy : ⟪x 1, x ax - x 1⟫ < ⟪x ay, x ax - x 1⟫) (hw : ⟪x aw, x ax - x 1⟫ < ⟪x 1, x ax - x 1⟫) :
    ¬ IsCyclicUnimodal (fun i => ⟪x (r i), x ax - x 1⟫) ↔
      ⟪x ry, x ax - x 1⟫ < ⟪x ay, x ax - x 1⟫ ∧ ⟪x ry, x ax - x 1⟫ < ⟪x rw, x ax - x 1⟫ ∧
        ⟪x aw, x ax - x 1⟫ < ⟪x rw, x ax - x 1⟫ := by
  have hz := hR.2.2.2.2.2.1
  have hr0 := hR.2.1
  rcases hor with ⟨e1, e2, e3, e4⟩ | ⟨e1, e2, e3, e4⟩
  · have := not_unimodal_five_iff (z := fun i => ⟪x (r i), x ax - x 1⟫) hz
      (by rw [e4, hr0]; exact hw) (by rw [hr0, e1]; exact hy)
    simp only [e1, e2, e3, e4] at this
    exact this
  · have := not_unimodal_five_iff' (z := fun i => ⟪x (r i), x ax - x 1⟫) hz
      (by rw [e1, hr0]; exact hw) (by rw [hr0, e4]; exact hy)
    simp only [e1, e2, e3, e4] at this
    exact this

/-! ### The common sink -/

/-- **The common sink** (remark after 20.2 (d)).  With `e_i ≠ e_j` (edge vectors at the cap) and a
far corner `p` (relative to the cap) whose depths along both cap edges are at most
`h_ij = ⟪e_i, e_j⟫`, at every view `e_i + t e_j` with `t > 0` the corner is strictly below one of
`i`, `j`: `z(p) ≤ (1 + t) h_ij < max (z(i), z(j))`, since `g_i, g_j ≤ h_ij` would force
`|e_i − e_j|² ≤ 0`. -/
theorem common_sink {ei ej p : ℝ³} (hne : ei ≠ ej) (hi : ⟪p, ei⟫ ≤ ⟪ei, ej⟫)
    (hj : ⟪p, ej⟫ ≤ ⟪ei, ej⟫) {t : ℝ} (ht : 0 < t) :
    ⟪p, ei + t • ej⟫ < max ⟪ei, ei + t • ej⟫ ⟪ej, ei + t • ej⟫ := by
  have hd : 0 < ⟪ei - ej, ei - ej⟫ := real_inner_self_pos.mpr (sub_ne_zero.mpr hne)
  have hc := real_inner_comm ei ej
  simp only [inner_sub_left, inner_sub_right] at hd
  rw [hc] at hd
  simp only [inner_add_right, real_inner_smul_right]
  rw [hc]
  have htj := mul_le_mul_of_nonneg_left hj ht.le
  by_contra hn
  rw [not_lt, max_le_iff] at hn
  obtain ⟨n1, n2⟩ := hn
  have a2 : t * ⟪ej, ej⟫ ≤ t * ⟪ei, ej⟫ := by linarith
  have a2' : ⟪ej, ej⟫ ≤ ⟪ei, ej⟫ := le_of_mul_le_mul_left a2 ht
  linarith

/-! ### Side-safety -/

/-- **Safe on side `y`** (§20, continued, 12): for every column `(g, h_y, h_w)` with `g > 0`,
`h_y > 0` and `h_w` free, the rim depths `g X_x + h_y X_y + h_w X_w` are cyclically unimodal when
distinct.  X-only; every such column is the column of some positive definite Gram matrix, so this
says that the cap edge does not fail at any metric with `c_xy > 0`. -/
def SideSafe (cx cy cw : Fin 7 → ℝ) {k : ℕ} [NeZero k] (r : ZMod k → Fin 7) : Prop :=
  ∀ g hy hw : ℝ, 0 < g → 0 < hy →
    Function.Injective (fun i => cx (r i) * g + cy (r i) * hy + cw (r i) * hw) →
    IsCyclicUnimodal (fun i => cx (r i) * g + cy (r i) * hy + cw (r i) * hw)

section SideSafe

variable {cx cy cw : Fin 7 → ℝ} {k : ℕ} [NeZero k] {r : ZMod k → Fin 7}

/-- Acute-safe is safe on side `y`. -/
theorem AcuteSafe.sideSafe (h : AcuteSafe cx cy cw r) : SideSafe cx cy cw r :=
  fun g hy hw hg h1 hinj => h g hy hw hg (Or.inl h1) hinj

/-- Acute-safe is safe on side `w`. -/
theorem AcuteSafe.sideSafe' (h : AcuteSafe cx cy cw r) : SideSafe cx cw cy r := by
  intro g hw hy hg h1 hinj
  have e : (fun i => cx (r i) * g + cw (r i) * hw + cy (r i) * hy) =
      fun i => cx (r i) * g + cy (r i) * hy + cw (r i) * hw := funext fun i => by ring
  rw [e] at hinj ⊢
  exact h g hy hw hg (Or.inr h1) hinj

/-- Safe on both sides is acute-safe. -/
theorem acuteSafe_of_sideSafe (hy : SideSafe cx cy cw r) (hw : SideSafe cx cw cy r) :
    AcuteSafe cx cy cw r := by
  intro g p q hg hs hinj
  rcases hs with h | h
  · exact hy g p q hg h hinj
  · have e : (fun i => cx (r i) * g + cy (r i) * p + cw (r i) * q) =
        fun i => cx (r i) * g + cw (r i) * q + cy (r i) * p := funext fun i => by ring
    rw [e] at hinj ⊢
    exact hw g q p hg h hinj

end SideSafe

/-- **A cap edge safe on side `y` certifies `K` at `K`'s own metric** whenever its angle with
the axis `y` at `1` is acute. -/
theorem isRupert_capEdge_sideSafe {x : Fin 7 → ℝ³} (hinj : Function.Injective x)
    {ax ay aw : Fin 7} {cx cy cw : Fin 7 → ℝ}
    (hrep : ∀ v, x v = x 1 + cx v • (x ax - x 1) + cy v • (x ay - x 1) + cw v • (x aw - x 1))
    (hax : ax ≠ 1) {k : ℕ} [NeZero k] {r : ZMod k → Fin 7} (hR : CapRim0 x ax ay aw k r)
    (hS : SideSafe cx cy cw r) (hsign : 0 < ⟪x ay - x 1, x ax - x 1⟫) :
    IsRupert (univ.image x) := by
  have hd : ∀ v, ⟪x v, x ax - x 1⟫ = ⟪x 1, x ax - x 1⟫ + (cx v * ⟪x ax - x 1, x ax - x 1⟫ +
      cy v * ⟪x ay - x 1, x ax - x 1⟫ + cw v * ⟪x aw - x 1, x ax - x 1⟫) := by
    intro v; rw [hrep v]; simp only [inner_add_left, real_inner_smul_left]; ring
  refine isRupert_capRim0 hinj hax hR ?_
  have hu : x ax - x 1 ≠ 0 := sub_ne_zero.mpr (hinj.ne hax)
  have hz := hR.2.2.2.2.2.1
  have hfun : (fun i => ⟪x (r i), x ax - x 1⟫) = fun i => ⟪x 1, x ax - x 1⟫ +
      (cx (r i) * ⟪x ax - x 1, x ax - x 1⟫ + cy (r i) * ⟪x ay - x 1, x ax - x 1⟫ +
        cw (r i) * ⟪x aw - x 1, x ax - x 1⟫) := funext fun i => hd (r i)
  rw [hfun] at hz ⊢
  refine isCyclicUnimodal_const_add _ (hS _ _ _ (real_inner_self_pos.mpr hu) hsign ?_)
  intro i j e
  exact hz (by simp only at e ⊢; rw [e])

/-- **A cap edge safe on side `w` certifies `K`** whenever its angle with the axis `w` at `1` is
acute. -/
theorem isRupert_capEdge_sideSafe' {x : Fin 7 → ℝ³} (hinj : Function.Injective x)
    {ax ay aw : Fin 7} {cx cy cw : Fin 7 → ℝ}
    (hrep : ∀ v, x v = x 1 + cx v • (x ax - x 1) + cy v • (x ay - x 1) + cw v • (x aw - x 1))
    (hax : ax ≠ 1) {k : ℕ} [NeZero k] {r : ZMod k → Fin 7} (hR : CapRim0 x ax ay aw k r)
    (hS : SideSafe cx cw cy r) (hsign : 0 < ⟪x aw - x 1, x ax - x 1⟫) :
    IsRupert (univ.image x) := by
  have hrep' : ∀ v, x v = x 1 + cx v • (x ax - x 1) + cw v • (x aw - x 1) +
      cy v • (x ay - x 1) := fun v => by rw [hrep v]; abel
  exact isRupert_capEdge_sideSafe hinj hrep' hax hR.swap hS hsign

namespace Type24

/-- `E_2` is safe on side `0` (it then does not fail where `c_ab > 0`). -/
def SafeE2at0 (x : Fin 7 → ℝ³) : Prop :=
  ∃ (k : ℕ) (_ : NeZero k) (r : ZMod k → Fin 7),
    CapRim0 x 2 0 6 k r ∧ SideSafe (oblX2 x) (oblX0 x) (oblX6 x) r

/-- `E_2` is safe on side `6` (`c_bc > 0`). -/
def SafeE2at6 (x : Fin 7 → ℝ³) : Prop :=
  ∃ (k : ℕ) (_ : NeZero k) (r : ZMod k → Fin 7),
    CapRim0 x 2 0 6 k r ∧ SideSafe (oblX2 x) (oblX6 x) (oblX0 x) r

/-- `E_6` is safe on side `2` (`c_bc > 0`). -/
def SafeE6at2 (x : Fin 7 → ℝ³) : Prop :=
  ∃ (k : ℕ) (_ : NeZero k) (r : ZMod k → Fin 7),
    CapRim0 x 6 2 0 k r ∧ SideSafe (oblX6 x) (oblX2 x) (oblX0 x) r

/-- `E_6` is safe on side `0` (`c_ac > 0`). -/
def SafeE6at0 (x : Fin 7 → ℝ³) : Prop :=
  ∃ (k : ℕ) (_ : NeZero k) (r : ZMod k → Fin 7),
    CapRim0 x 6 2 0 k r ∧ SideSafe (oblX6 x) (oblX0 x) (oblX2 x) r

/-- `E_0` is safe on side `2` (`c_ab > 0`). -/
def SafeE0at2 (x : Fin 7 → ℝ³) : Prop :=
  ∃ (k : ℕ) (_ : NeZero k) (r : ZMod k → Fin 7),
    CapRim0 x 0 2 6 k r ∧ SideSafe (oblX0 x) (oblX2 x) (oblX6 x) r

/-- `E_0` is safe on side `6` (`c_ac > 0`). -/
def SafeE0at6 (x : Fin 7 → ℝ³) : Prop :=
  ∃ (k : ℕ) (_ : NeZero k) (r : ZMod k → Fin 7),
    CapRim0 x 0 2 6 k r ∧ SideSafe (oblX0 x) (oblX6 x) (oblX2 x) r

/-- **Each cosine is seen on a safe side by one of its cap edges** (the hypothesis of 20.8′):
`c_ab` by `E_2` (side `0`) or `E_0` (side `2`), `c_ac` by `E_6` (side `0`) or `E_0` (side `6`),
`c_bc` by `E_2` (side `6`) or `E_6` (side `2`). -/
def SideCovered (x : Fin 7 → ℝ³) : Prop :=
  (SafeE2at0 x ∨ SafeE0at2 x) ∧ (SafeE6at0 x ∨ SafeE0at6 x) ∧ (SafeE2at6 x ∨ SafeE6at2 x)

theorem SafeE2.sides {x : Fin 7 → ℝ³} (h : SafeE2 x) : SafeE2at0 x ∧ SafeE2at6 x := by
  obtain ⟨k, hk, r, hR, hS⟩ := h
  exact ⟨⟨k, hk, r, hR, hS.sideSafe⟩, ⟨k, hk, r, hR, hS.sideSafe'⟩⟩

theorem SafeE6.sides {x : Fin 7 → ℝ³} (h : SafeE6 x) : SafeE6at2 x ∧ SafeE6at0 x := by
  obtain ⟨k, hk, r, hR, hS⟩ := h
  exact ⟨⟨k, hk, r, hR, hS.sideSafe⟩, ⟨k, hk, r, hR, hS.sideSafe'⟩⟩

theorem SafeE0.sides {x : Fin 7 → ℝ³} (h : SafeE0 x) : SafeE0at2 x ∧ SafeE0at6 x := by
  obtain ⟨k, hk, r, hR, hS⟩ := h
  exact ⟨⟨k, hk, r, hR, hS.sideSafe⟩, ⟨k, hk, r, hR, hS.sideSafe'⟩⟩

/-- **Theorem 20.8 is a special case of 20.8′**: two acute-safe cap edges see every cosine on a
safe side. -/
theorem sideCovered_of_twoSafe {x : Fin 7 → ℝ³} (h : TwoSafe x) : SideCovered x := by
  rcases h with ⟨h2, h6⟩ | ⟨h2, h0⟩ | ⟨h6, h0⟩
  · exact ⟨Or.inl h2.sides.1, Or.inl h6.sides.2, Or.inl h2.sides.2⟩
  · exact ⟨Or.inl h2.sides.1, Or.inr h0.sides.2, Or.inl h2.sides.2⟩
  · exact ⟨Or.inr h0.sides.1, Or.inl h6.sides.2, Or.inr h6.sides.1⟩

end Type24

/-- `E_2` safe on side `0`, Rupert form: `K` is Rupert if `c_ab > 0`. -/
theorem isRupert_type24_safeE2at0 {x : Fin 7 → ℝ³} (T : Type24 x) (h : Type24.SafeE2at0 x)
    (hsign : 0 < ⟪x 0 - x 1, x 2 - x 1⟫) : IsRupert (univ.image x) := by
  obtain ⟨k, _, r, hR, hS⟩ := h
  exact isRupert_capEdge_sideSafe T.inj T.rep2 (by decide) hR hS hsign

/-- `E_2` safe on side `6`, Rupert form: `K` is Rupert if `c_bc > 0`. -/
theorem isRupert_type24_safeE2at6 {x : Fin 7 → ℝ³} (T : Type24 x) (h : Type24.SafeE2at6 x)
    (hsign : 0 < ⟪x 6 - x 1, x 2 - x 1⟫) : IsRupert (univ.image x) := by
  obtain ⟨k, _, r, hR, hS⟩ := h
  exact isRupert_capEdge_sideSafe' T.inj T.rep2 (by decide) hR hS hsign

/-- `E_6` safe on side `2`, Rupert form: `K` is Rupert if `c_bc > 0`. -/
theorem isRupert_type24_safeE6at2 {x : Fin 7 → ℝ³} (T : Type24 x) (h : Type24.SafeE6at2 x)
    (hsign : 0 < ⟪x 2 - x 1, x 6 - x 1⟫) : IsRupert (univ.image x) := by
  obtain ⟨k, _, r, hR, hS⟩ := h
  exact isRupert_capEdge_sideSafe T.inj T.rep6 (by decide) hR hS hsign

/-- `E_6` safe on side `0`, Rupert form: `K` is Rupert if `c_ac > 0`. -/
theorem isRupert_type24_safeE6at0 {x : Fin 7 → ℝ³} (T : Type24 x) (h : Type24.SafeE6at0 x)
    (hsign : 0 < ⟪x 0 - x 1, x 6 - x 1⟫) : IsRupert (univ.image x) := by
  obtain ⟨k, _, r, hR, hS⟩ := h
  exact isRupert_capEdge_sideSafe' T.inj T.rep6 (by decide) hR hS hsign

/-- `E_0` safe on side `2`, Rupert form: `K` is Rupert if `c_ab > 0`. -/
theorem isRupert_type24_safeE0at2 {x : Fin 7 → ℝ³} (T : Type24 x) (h : Type24.SafeE0at2 x)
    (hsign : 0 < ⟪x 2 - x 1, x 0 - x 1⟫) : IsRupert (univ.image x) := by
  obtain ⟨k, _, r, hR, hS⟩ := h
  exact isRupert_capEdge_sideSafe T.inj T.rep (by decide) hR hS hsign

/-- `E_0` safe on side `6`, Rupert form: `K` is Rupert if `c_ac > 0`. -/
theorem isRupert_type24_safeE0at6 {x : Fin 7 → ℝ³} (T : Type24 x) (h : Type24.SafeE0at6 x)
    (hsign : 0 < ⟪x 6 - x 1, x 0 - x 1⟫) : IsRupert (univ.image x) := by
  obtain ⟨k, _, r, hR, hS⟩ := h
  exact isRupert_capEdge_sideSafe' T.inj T.rep (by decide) hR hS hsign

/-- **Theorem 20.8′ (side-safety), at `K`'s own metric.**  If each of the cosines `c_ab`, `c_ac`,
`c_bc` at the cap `1` is seen on a safe side by one of its cap edges (`Type24.SideCovered`, with
the rim data `CapRim0`: distinct depths, no horizontal double normal) and some face angle at `1`
is acute, `K` is Rupert: the cap edge that sees the acute cosine on a safe side does not fail.
No radius and no neighbourhood of the corner enter. -/
theorem isRupert_type24_side_safe {x : Fin 7 → ℝ³} (T : Type24 x) (hside : Type24.SideCovered x)
    (hacute : 0 < ⟪x 0 - x 1, x 2 - x 1⟫ ∨ 0 < ⟪x 0 - x 1, x 6 - x 1⟫ ∨
      0 < ⟪x 2 - x 1, x 6 - x 1⟫) :
    IsRupert (univ.image x) := by
  have c1 := real_inner_comm (x 0 - x 1) (x 2 - x 1)
  have c2 := real_inner_comm (x 0 - x 1) (x 6 - x 1)
  have c3 := real_inner_comm (x 2 - x 1) (x 6 - x 1)
  obtain ⟨hab, hac, hbc⟩ := hside
  rcases hacute with h | h | h
  · rcases hab with h' | h'
    · exact isRupert_type24_safeE2at0 T h' h
    · exact isRupert_type24_safeE0at2 T h' (by rw [c1]; exact h)
  · rcases hac with h' | h'
    · exact isRupert_type24_safeE6at0 T h' h
    · exact isRupert_type24_safeE0at6 T h' (by rw [c2]; exact h)
  · rcases hbc with h' | h'
    · exact isRupert_type24_safeE2at6 T h' (by rw [c3]; exact h)
    · exact isRupert_type24_safeE6at2 T h' h

/-- **Conjecture A for side-covered classes (Theorem 20.8′)**: a type-24 nopert candidate (not
Rupert) whose three cosines at `1` are each seen on a safe side has all three face angles at `1`
right or obtuse. -/
theorem Type24.obtuse_of_side_safe {x : Fin 7 → ℝ³} (T : Type24 x) (hside : Type24.SideCovered x)
    (hK : ¬ IsRupert (univ.image x)) :
    ⟪x 0 - x 1, x 2 - x 1⟫ ≤ 0 ∧ ⟪x 0 - x 1, x 6 - x 1⟫ ≤ 0 ∧ ⟪x 2 - x 1, x 6 - x 1⟫ ≤ 0 := by
  by_contra h
  simp only [not_and_or, not_le] at h
  exact hK (isRupert_type24_side_safe T hside h)

/-! ### Theorem 8.10 as an item: depth-separated pairs at an edge view -/

/-- **Theorem 8.10 at an edge view given by determinant tests** (Theorem 8.9 with a
depth-separated `K_v`).  The cycle `p` passes all triple tests at `u` (strictly convex,
counterclockwise), every other point except the middles `M` and the axle end `w = p i₀ − h u`
(`h ≠ 0`) is strictly inside, the rim has a depth-separated parallel pair (`DepthSepAt`, in
space) and no horizontal double normal, and each middle lies over a face of the edge `p i₀ w`
(`EdgeMiddle`).  Then `V` is Rupert, whether or not the rim depths are unimodal. -/
theorem isRupert_of_edgeView_depthSeparated (V M Wn : Finset ℝ³) (u : ℝ³) (hu : u ≠ 0)
    {k : ℕ} [NeZero k] (hk : 3 ≤ k) (p : ZMod k → ℝ³) (i₀ : ZMod k) (w : ℝ³) (h : ℝ)
    (hwV : w ∈ V) (hw : w = p i₀ - h • u) (hh : h ≠ 0) (hpV : ∀ i, p i ∈ V) (hpM : ∀ i, p i ∉ M)
    (hcyc : ∀ i j, j ≠ i → j ≠ i + 1 → 0 < det3 (p (i + 1) - p i) (p j - p i) u)
    (hrest : ∀ v ∈ V, v ∉ M → v ≠ w → (∀ j, v ≠ p j) → ∀ i,
      0 < det3 (p (i + 1) - p i) (v - p i) u)
    {a c : ZMod k} (hds : DepthSepAt p u a c) (hnd : NoHDNAt Wn u) (hpW : ∀ i, p i ∈ Wn)
    (hM : ∀ m ∈ M, EdgeMiddle u (p i₀) w (p (i₀ + 1)) (p (i₀ - 1)) h m) : IsRupert V := by
  classical
  obtain ⟨R, hR, ρ, hρ, hRu⟩ := exists_rotation_to_ez_pos u hu
  have hp : IsCcwPolygon (fun i => proj_xy (R.toEuclideanLin (p i))) := by
    refine ⟨hk, fun i j hi hj => ?_⟩
    simp only [proj_rot_sub]
    exact cross2_proj_rot_pos hR hρ hRu (hcyc i j hi hj)
  refine isRupert_of_edgeChords_depthSeparated V M R hR hρ hRu p i₀ w h hwV hw hh hpV hpM hp ?_
    (isDepthSeparatedPair_of_depthSepAt hR hρ hRu p hk hcyc hds)
    (hnd R hR ρ hρ.ne' hRu k p hpW hp) hM
  intro v hv hvM hvw hvp
  refine hp.mem_interior_of_left fun i => ?_
  simp only [proj_rot_sub]
  exact cross2_proj_rot_pos hR hρ hRu (hrest v hv hvM hvw hvp i)

/-- **In a depth-separated pair `(e, c)` the two rim neighbours of `c` lie strictly on opposite
sides of its depth** (the chain from `c` to `a` starts at `c + 1`, the chain from `a + 1` back to
`c` ends at `c − 1`, and both are nonempty since `c` is neither end of `e`). -/
theorem DepthSepAt.nbrs {k : ℕ} [NeZero k] (hk : 3 ≤ k) {p : ZMod k → ℝ³} {u : ℝ³}
    {a c : ZMod k} (h : DepthSepAt p u a c) :
    (⟪p c, u⟫ < ⟪p (c + 1), u⟫ ∧ ⟪p (c - 1), u⟫ < ⟪p c, u⟫) ∨
      (⟪p (c + 1), u⟫ < ⟪p c, u⟫ ∧ ⟪p c, u⟫ < ⟪p (c - 1), u⟫) := by
  obtain ⟨hn, hz⟩ := h
  have hc1 : c + 1 ≠ c := (zmod_ne_add_one (by omega) c).symm
  have hca : c ≠ a := by
    rintro rfl
    have := hn (c + 1) hc1
    rw [sub_self, show det3 (p (c + 1) - p c) 0 u = 0 by simp [det3_expand], mul_zero] at this
    exact lt_irrefl _ this
  have hca1 : c ≠ a + 1 := by
    rintro rfl
    have := hn (a + 1 + 1) hc1
    rw [show det3 (p (a + 1) - p a) (p (a + 1) - p a) u = 0 by simp only [det3_expand]; ring,
      mul_zero] at this
    exact lt_irrefl _ this
  have hv1 : 1 ≤ (a - c).val := by
    rcases Nat.eq_zero_or_pos (a - c).val with h0 | h0
    · exact absurd (sub_eq_zero.mp ((ZMod.val_eq_zero _).mp h0)) (Ne.symm hca)
    · exact h0
  have hvk : (a - c).val < k - 1 := by
    have hlt := ZMod.val_lt (a - c)
    rcases Nat.lt_or_ge (a - c).val (k - 1) with h' | h'
    · exact h'
    · exfalso
      have e : (a - c).val = k - 1 := by omega
      have e2 := ZMod.natCast_zmod_val (a - c)
      rw [e, zmod_natCast_pred (by omega)] at e2
      exact hca1 (by linear_combination e2)
  have s1 : c + ((1 : ℕ) : ZMod k) = c + 1 := by rw [Nat.cast_one]
  have sk : c + ((k - 1 : ℕ) : ZMod k) = c - 1 := by rw [zmod_natCast_pred (by omega)]; ring
  rcases hz with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have a1 := h1 1 (by norm_num) hv1
    have a2 := h2 (k - 1) hvk (by omega)
    rw [s1] at a1; rw [sk] at a2
    exact Or.inl ⟨a1, a2⟩
  · have a1 := h1 1 (by norm_num) hv1
    have a2 := h2 (k - 1) hvk (by omega)
    rw [s1] at a1; rw [sk] at a2
    exact Or.inr ⟨a1, a2⟩

/-- **For a 4-corner rim a depth-separated pair adds nothing**: it puts the two neighbours of a
corner on opposite sides of its depth, which no failure pattern of a 4-corner rim does.  So the
tests of the window chain (4-corner rims) are not strengthened by Theorem 8.10. -/
theorem not_fails4_of_depthSepAt {y a c b u : ℝ³} {e f : ZMod 4}
    (h : DepthSepAt (quad y a c b) u e f) : ¬ Fails4 y c a b u := by
  have hn := h.nbrs (by norm_num)
  have q0 : quad y a c b 0 = y := rfl
  have q1 : quad y a c b 1 = a := rfl
  have q2 : quad y a c b 2 = c := rfl
  have q3 : quad y a c b 3 = b := rfl
  intro hF
  simp only [Fails4, max_le_iff, le_min_iff] at hF
  rcases zmod4_cases f with rfl | rfl | rfl | rfl
  · rw [show (0 : ZMod 4) + 1 = 1 from rfl, show (0 : ZMod 4) - 1 = 3 from rfl, q0, q1, q3] at hn
    rcases hn with hn | hn <;> rcases hF with hF | hF <;> linarith [hn.1, hn.2, hF.1.1, hF.1.2,
      hF.2.1, hF.2.2]
  · rw [show (1 : ZMod 4) + 1 = 2 from rfl, show (1 : ZMod 4) - 1 = 0 from rfl, q0, q1, q2] at hn
    rcases hn with hn | hn <;> rcases hF with hF | hF <;> linarith [hn.1, hn.2, hF.1.1, hF.1.2,
      hF.2.1, hF.2.2]
  · rw [show (2 : ZMod 4) + 1 = 3 from rfl, show (2 : ZMod 4) - 1 = 1 from rfl, q1, q2, q3] at hn
    rcases hn with hn | hn <;> rcases hF with hF | hF <;> linarith [hn.1, hn.2, hF.1.1, hF.1.2,
      hF.2.1, hF.2.2]
  · rw [show (3 : ZMod 4) + 1 = 0 from rfl, show (3 : ZMod 4) - 1 = 2 from rfl, q0, q2, q3] at hn
    rcases hn with hn | hn <;> rcases hF with hF | hF <;> linarith [hn.1, hn.2, hF.1.1, hF.1.2,
      hF.2.1, hF.2.2]

/-- **A cap-edge crossing with a depth-separated pair certifies `K`** (Theorem 8.10 with
Theorem 8.9; the axis vertex `x ax` is the axle end over the cap `1`).  This is the cap-edge
item of the proxy "unimodal or depth-separated" (Conjecture B_DS): it applies whether or not
the rim depths are unimodal. -/
theorem isRupert_capRim0_depthSeparated {x : Fin 7 → ℝ³} (hinj : Function.Injective x)
    {ax ay aw : Fin 7} (hax : ax ≠ 1) {k : ℕ} [NeZero k] {r : ZMod k → Fin 7}
    (hR : CapRim0 x ax ay aw k r) {a c : ZMod k}
    (hds : DepthSepAt (fun i => x (r i)) (x ax - x 1) a c) : IsRupert (univ.image x) := by
  classical
  obtain ⟨hk, hr0, -, hcyc, hrest, -, hnd⟩ := hR
  have hu : x ax - x 1 ≠ 0 := sub_ne_zero.mpr (hinj.ne hax)
  refine isRupert_of_edgeView_depthSeparated (univ.image x) ∅ _ (x ax - x 1) hu hk
    (fun i => x (r i)) 0 (x ax) (-1) (mem_image_of_mem x (mem_univ _)) ?_ (by norm_num)
    (fun i => mem_image_of_mem x (mem_univ _)) (fun _ => Finset.notMem_empty _) hcyc ?_ hds hnd
    (fun i => mem_image_of_mem _ (mem_univ _)) (fun m hm => absurd hm (Finset.notMem_empty _))
  · simp only [hr0, neg_one_smul, sub_neg_eq_add]; abel
  · intro v hv _ hvw hvp i
    obtain ⟨v', -, rfl⟩ := mem_image.mp hv
    exact hrest v' (fun e => hvw (by rw [e])) (fun j e => hvp j (by rw [e])) i

/-- **A cap-edge crossing, unimodal or depth-separated**, certifies `K` (Theorem 7.3 or 8.10). -/
theorem isRupert_capRim0_uos {x : Fin 7 → ℝ³} (hinj : Function.Injective x)
    {ax ay aw : Fin 7} (hax : ax ≠ 1) {k : ℕ} [NeZero k] {r : ZMod k → Fin 7}
    (hR : CapRim0 x ax ay aw k r)
    (h : IsCyclicUnimodal (fun i => ⟪x (r i), x ax - x 1⟫) ∨
      ∃ a c : ZMod k, DepthSepAt (fun i => x (r i)) (x ax - x 1) a c) :
    IsRupert (univ.image x) := by
  rcases h with h | ⟨a, c, h⟩
  · exact isRupert_capRim0 hinj hax hR h
  · exact isRupert_capRim0_depthSeparated hinj hax hR h

end Minimality

end
