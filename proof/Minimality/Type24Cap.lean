module

public import Minimality.Type24
public import Minimality.UniformTilt

@[expose] public section

/-!
# Type 24 near the cube corner: the cap-edge crossings and the planar quad (§17)

`FEWER-FACES-PROOFS.md` §17 and its addendum, the statements that hold at every metric (here: the
inner product of `ℝ³`, i.e. at `K`'s own metric).

* **Lemma C (Theorem 17.10, the cap-edge dichotomy).**  At the view `u = x_x − x_1` along a cap
  edge, the closing `K_1` has the rim `(1, y, R, w)`; the depth of a point with oblique
  coordinates `(X_x, X_y, X_w)` at `1` is `⟪x 1, u⟫ + X_x ‖u‖² + X_y ⟪e_y, u⟫ + X_w ⟪e_w, u⟫`.
  Along the far path, each step keeps the sign of `ΔX_x` while
  `|ΔX_y ⟪e_y, u⟫ + ΔX_w ⟪e_w, u⟫| < ‖u‖² |ΔX_x|` (`capStep_pos`, `capStep_neg`), which holds when
  both cosines at `1` are below `δ` and `δ (L_y |ΔX_y| + L_w |ΔX_w|) ≤ L_x |ΔX_x|` for every step
  (`capStep_of_cos`: `δ_x` is the largest such `δ`).  If the far path has no interior local
  minimum of `X_x` (17.9's `(H-cap)`), the depths along it rise and then fall (`exists_arch`), and
  the cycle is unimodal as soon as `1` is not a local maximum, i.e. `⟪e_y, u⟫ > 0` or
  `⟪e_w, u⟫ > 0` (`isCyclicUnimodal_of_arch`).  The frame form is `capEdge_unimodal`, the Rupert
  form (Theorem 8.9 with Theorem 7.3, the axis vertex a double over `1`) `isRupert_capEdge`.
  For type 24, with the rim data `CapRim` (`isRupert_capEdge_frame`): `isRupert_type24_E2`,
  `isRupert_type24_E6` and the dichotomy
  `isRupert_type24_capEdge` (`E_2` or `E_6` certifies `K` unless all three inner products at `1`
  are `≤ 0`).  17.9's `(H-cap)` from "3 is the middle corner" and the planar quad
  (`noInteriorMin_of_mid3`, `Type24.hcap2`, `Type24.hcap6`).
* **Lemma Q and Remark Q′ (17.4, 17.19).**  If `c = y + s (a − y) + t (b − y)` with `s, t > 0`,
  `s + t > 1` (the planar quad `(y, a, c, b)` with `c` opposite `y`), the diagonals of the 4-cycle
  `(y, a, c, b)` are never weakly depth-separated, unless all four depths are equal
  (`planarQuad_fails4`); so with distinct depths the cycle is unimodal at every view
  (`planarQuad_unimodal`), and any crossing test with this rim certifies `K`
  (`isRupert_planarQuad`, through the 4-corner wrapper `isRupert_quadView`).
* **Lemma 17.15 (Proposition 8.8 for two faces without a common vertex).**  `isRupert_of_chords`
  needs no face structure; the determinant form is `isRupert_disjointFaces`.

`Fails4` is the closed failure condition of a 4-corner rim (two interleaved pairs weakly
depth-separated); `DepthSep` (strict) implies it.

Not formalized: the geometric half of 17.9 (that `K_1`'s rim is `(1, y, R, w)` with `R ⊂ {3, 4,
5}` and `3` in the middle when `|R| = 3`; taken as hypotheses), the third cap edge, Theorem 17.12's
neighbourhoods `N_I` beyond the cap edges.
-/

namespace Minimality

open Finset
open scoped RealInnerProductSpace

/-! ### Sequences that rise and then fall -/

/-- A finite sequence `a l, …, a r` with distinct consecutive terms and no interior local minimum
rises and then falls. -/
theorem exists_arch (a : ℕ → ℝ) (l r : ℕ) (hlr : l ≤ r)
    (hd : ∀ n, l ≤ n → n < r → a n ≠ a (n + 1))
    (hm : ∀ n, l ≤ n → n + 2 ≤ r → ¬ (a (n + 1) < a n ∧ a (n + 1) < a (n + 2))) :
    ∃ q, l ≤ q ∧ q ≤ r ∧ (∀ n, l ≤ n → n < q → a n < a (n + 1)) ∧
      (∀ n, q ≤ n → n < r → a (n + 1) < a n) := by
  classical
  have hex : ∃ n, l ≤ n ∧ (r ≤ n ∨ a (n + 1) < a n) := ⟨r, hlr, Or.inl le_rfl⟩
  set q := Nat.find hex with hq
  have hqP : l ≤ q ∧ (r ≤ q ∨ a (q + 1) < a q) := Nat.find_spec hex
  have hmin : ∀ n, n < q → ¬ (l ≤ n ∧ (r ≤ n ∨ a (n + 1) < a n)) := fun n hn =>
    Nat.find_min hex hn
  have hqr : q ≤ r := Nat.find_min' hex ⟨hlr, Or.inl le_rfl⟩
  have hup : ∀ n, l ≤ n → n < q → a n < a (n + 1) := by
    intro n hl hn
    have h := hmin n hn
    push Not at h
    obtain ⟨h1, h2⟩ := h hl
    exact lt_of_le_of_ne h2 (hd n hl (by omega))
  refine ⟨q, hqP.1, hqr, hup, ?_⟩
  intro n hn hnr
  induction n, hn using Nat.le_induction with
  | base =>
    rcases hqP.2 with h | h
    · omega
    · exact h
  | succ n hqn ih =>
    have h1 := ih (by omega)
    have h2 := hd (n + 1) (by omega) hnr
    rcases lt_or_gt_of_ne h2 with h | h
    · exact absurd ⟨h1, h⟩ (hm n (by omega) (by omega))
    · exact h

theorem zmod_natCast_sub_one {k : ℕ} {n : ℕ} (hn : 1 ≤ n) :
    ((n - 1 : ℕ) : ZMod k) = (n : ZMod k) - 1 := by
  rw [Nat.cast_sub hn, Nat.cast_one]

/-- **A cyclic sequence whose path `1, …, k − 1` rises and then falls** is unimodal as soon as
`z 0` is below one of its neighbours. -/
theorem isCyclicUnimodal_of_arch {k : ℕ} [NeZero k] (hk : 3 ≤ k) {z : ZMod k → ℝ}
    (hinj : Function.Injective z) (q : ℕ)
    (hup : ∀ n : ℕ, 1 ≤ n → n < q → z n < z (n + 1))
    (hdn : ∀ n : ℕ, q ≤ n → n + 1 < k → z (n + 1) < z n)
    (h0 : z 0 < z 1 ∨ z 0 < z ((k - 1 : ℕ) : ZMod k)) : IsCyclicUnimodal z := by
  refine isCyclicUnimodal_of_atMostOne (by omega) hinj ?_
  -- every local maximum is `q`
  have key : ∀ i : ZMod k, z (i - 1) < z i ∧ z (i + 1) < z i → i = (q : ZMod k) := by
    intro i hi
    have hiv : i = ((i.val : ℕ) : ZMod k) := (ZMod.natCast_zmod_val i).symm
    have hlt : i.val < k := ZMod.val_lt i
    set n := i.val
    rw [hiv] at hi ⊢
    rcases Nat.eq_zero_or_pos n with h | h
    · exfalso
      rw [h, Nat.cast_zero] at hi
      have e : (0 : ZMod k) - 1 = ((k - 1 : ℕ) : ZMod k) := by
        rw [zmod_natCast_sub_one (by omega), ZMod.natCast_self]
      rw [e, zero_add] at hi
      rcases h0 with h0 | h0 <;> linarith [hi.1, hi.2]
    · rcases lt_trichotomy n q with h1 | h1 | h1
      · exfalso
        have := hup n h h1
        linarith [hi.2]
      · rw [h1]
      · exfalso
        have := hdn (n - 1) (by omega) (by omega)
        rw [zmod_natCast_sub_one h, sub_add_cancel] at this
        linarith [hi.1]
  intro i j hi hj
  rw [key i hi, key j hj]

/-! ### Lemma C: one step of the far path -/

/-- **A step of the far path keeps the sign of `ΔX_x`** (17.10): the depth difference is
`ΔX ‖u‖² + ΔY ⟪e_y, u⟫ + ΔW ⟪e_w, u⟫`. -/
theorem capStep_pos {G cy cw dX dY dW : ℝ} (h : |dY * cy + dW * cw| < G * |dX|) (hX : 0 < dX) :
    0 < dX * G + dY * cy + dW * cw := by
  rw [abs_of_pos hX] at h
  have := neg_abs_le (dY * cy + dW * cw)
  nlinarith

theorem capStep_neg {G cy cw dX dY dW : ℝ} (h : |dY * cy + dW * cw| < G * |dX|) (hX : dX < 0) :
    dX * G + dY * cy + dW * cw < 0 := by
  rw [abs_of_neg hX] at h
  have := le_abs_self (dY * cy + dW * cw)
  nlinarith

/-- **The radius `δ_x` of 17.10.**  If both cosines at `1` are below `δ`
(`|⟪e_y, u⟫| < δ L_y L_x`, `|⟪e_w, u⟫| < δ L_w L_x`) and `δ (L_y |ΔY| + L_w |ΔW|) ≤ L_x |ΔX|`
with `ΔX ≠ 0`, the step condition holds. -/
theorem capStep_of_cos {Lx Ly Lw cy cw dX dY dW δ : ℝ} (hLx : 0 < Lx) (hX : dX ≠ 0)
    (hcy : |cy| < δ * (Ly * Lx)) (hcw : |cw| < δ * (Lw * Lx))
    (hδ : δ * (Ly * |dY| + Lw * |dW|) ≤ Lx * |dX|) :
    |dY * cy + dW * cw| < Lx ^ 2 * |dX| := by
  have hdX : 0 < |dX| := abs_pos.mpr hX
  have h1 : |dY * cy + dW * cw| ≤ |dY| * |cy| + |dW| * |cw| := by
    calc |dY * cy + dW * cw| ≤ |dY * cy| + |dW * cw| := abs_add_le _ _
      _ = |dY| * |cy| + |dW| * |cw| := by rw [abs_mul, abs_mul]
  have e3 : Lx * (δ * (Ly * |dY| + Lw * |dW|)) ≤ Lx * (Lx * |dX|) :=
    mul_le_mul_of_nonneg_left hδ hLx.le
  have hy : |dY| * |cy| ≤ |dY| * (δ * (Ly * Lx)) ∧
      (dY ≠ 0 → |dY| * |cy| < |dY| * (δ * (Ly * Lx))) :=
    ⟨mul_le_mul_of_nonneg_left hcy.le (abs_nonneg _),
      fun h => mul_lt_mul_of_pos_left hcy (abs_pos.mpr h)⟩
  have hw : |dW| * |cw| ≤ |dW| * (δ * (Lw * Lx)) ∧
      (dW ≠ 0 → |dW| * |cw| < |dW| * (δ * (Lw * Lx))) :=
    ⟨mul_le_mul_of_nonneg_left hcw.le (abs_nonneg _),
      fun h => mul_lt_mul_of_pos_left hcw (abs_pos.mpr h)⟩
  have hsum : |dY| * (δ * (Ly * Lx)) + |dW| * (δ * (Lw * Lx)) =
      Lx * (δ * (Ly * |dY| + Lw * |dW|)) := by ring
  by_cases hY : dY = 0
  · by_cases hW : dW = 0
    · subst hY hW
      simp only [zero_mul, zero_add, abs_zero]
      positivity
    · nlinarith [hw.2 hW]
  · nlinarith [hy.2 hY]

/-- A step of the far path, as an equivalence of signs (`ΔX ≠ 0`). -/
theorem capStep_iff {G cy cw dX dY dW : ℝ} (h : |dY * cy + dW * cw| < G * |dX|) (hX : dX ≠ 0) :
    (0 < dX * G + dY * cy + dW * cw ↔ 0 < dX) ∧ (dX * G + dY * cy + dW * cw < 0 ↔ dX < 0) := by
  rcases lt_or_gt_of_ne hX with hn | hp
  · have := capStep_neg h hn
    exact ⟨⟨fun h' => absurd h' (not_lt.mpr this.le), fun h' => absurd h' (not_lt.mpr hn.le)⟩,
      ⟨fun _ => hn, fun _ => this⟩⟩
  · have := capStep_pos h hp
    exact ⟨⟨fun _ => hp, fun _ => this⟩,
      ⟨fun h' => absurd h' (not_lt.mpr this.le), fun h' => absurd h' (not_lt.mpr hp.le)⟩⟩

theorem inner_frame (o u ey ew v : ℝ³) (X Y W : ℝ) :
    ⟪o + X • u + Y • ey + W • ew, v⟫ = ⟪o, v⟫ + X * ⟪u, v⟫ + Y * ⟪ey, v⟫ + W * ⟪ew, v⟫ := by
  simp only [inner_add_left, real_inner_smul_left]

/-! ### Lemma C: the frame form -/

/-- **Lemma C, the depth core (Theorem 17.10).**  At the view `u` along the cap edge `1 x`, the
rim of `K_1` is the cycle `p` with `p 0 = 1` (`= o`) and the far path `p 1, …, p (k − 1)` (from
`y` to `w`); each corner has oblique coordinates `(X, Y, W)` in a frame `o; u, e_y, e_w`.  Along
the path, `X` has distinct consecutive values and no interior local minimum (`(H-cap)`), and each
step satisfies the condition of `capStep_of_cos` (`hstep`, true for `|c| < δ_x`).  If the depths
are distinct and `1` lies strictly below `y` or `w` (`⟪e_y, u⟫ > 0` or `⟪e_w, u⟫ > 0` when
`p 1 = o + e_y`, `p (k − 1) = o + e_w`), the depths along the rim are cyclically unimodal. -/
theorem capEdge_unimodal {k : ℕ} [NeZero k] (hk : 3 ≤ k) (o u ey ew : ℝ³) (p : ZMod k → ℝ³)
    (X Y W : ZMod k → ℝ) (hp0 : p 0 = o)
    (hrep : ∀ i, p i = o + X i • u + Y i • ey + W i • ew)
    (hd : ∀ n : ℕ, 1 ≤ n → n + 1 < k → X n ≠ X (n + 1))
    (hm : ∀ n : ℕ, 1 ≤ n → n + 3 ≤ k → ¬ (X (n + 1) < X n ∧ X (n + 1) < X (n + 2)))
    (hstep : ∀ n : ℕ, 1 ≤ n → n + 1 < k →
      |(Y (n + 1) - Y n) * ⟪ey, u⟫ + (W (n + 1) - W n) * ⟪ew, u⟫| < ⟪u, u⟫ * |X (n + 1) - X n|)
    (hinj : Function.Injective fun i => ⟪p i, u⟫)
    (h0 : ⟪o, u⟫ < ⟪p 1, u⟫ ∨ ⟪o, u⟫ < ⟪p ((k - 1 : ℕ) : ZMod k), u⟫) :
    IsCyclicUnimodal fun i => ⟪p i, u⟫ := by
  -- the depth difference along a step
  have hdiff : ∀ i j : ZMod k, ⟪p j, u⟫ - ⟪p i, u⟫ =
      (X j - X i) * ⟪u, u⟫ + (Y j - Y i) * ⟪ey, u⟫ + (W j - W i) * ⟪ew, u⟫ := by
    intro i j; rw [hrep i, hrep j, inner_frame, inner_frame]; ring
  have hsign : ∀ n : ℕ, 1 ≤ n → n + 1 < k →
      (⟪p n, u⟫ < ⟪p (n + 1), u⟫ ↔ X n < X (n + 1)) ∧
        (⟪p (n + 1), u⟫ < ⟪p n, u⟫ ↔ X (n + 1) < X n) := by
    intro n h1 h2
    have hX : X (n + 1) - X n ≠ 0 := sub_ne_zero.mpr (hd n h1 h2).symm
    obtain ⟨c1, c2⟩ := capStep_iff (hstep n h1 h2) hX
    have e := hdiff n (n + 1)
    constructor
    · rw [← sub_pos, e, c1, sub_pos]
    · rw [← sub_neg, e, c2, sub_neg]
  set a : ℕ → ℝ := fun n => ⟪p n, u⟫ with ha
  have hcast : ∀ n : ℕ, a (n + 1) = ⟪p ((n : ZMod k) + 1), u⟫ := by
    intro n; simp only [ha, Nat.cast_add, Nat.cast_one]
  have hcast2 : ∀ n : ℕ, a (n + 2) = ⟪p ((n : ZMod k) + 1 + 1), u⟫ := by
    intro n; simp only [ha, Nat.cast_add, Nat.cast_ofNat, add_assoc, one_add_one_eq_two]
  obtain ⟨q, -, -, hup, hdn⟩ := exists_arch a 1 (k - 1) (by omega)
    (fun n h1 h2 => by
      rw [hcast]
      intro e
      rcases lt_or_gt_of_ne (hd n h1 (by omega)) with h | h
      · exact absurd e (((hsign n h1 (by omega)).1.mpr h).ne)
      · exact absurd e.symm (((hsign n h1 (by omega)).2.mpr h).ne))
    (fun n h1 h2 => by
      rw [hcast, hcast2]
      rintro ⟨c1, c2⟩
      have s1 := (hsign n h1 (by omega)).2.mp c1
      have s2 := (hsign (n + 1) (by omega) (by omega)).1.mp
        (by simpa only [Nat.cast_add, Nat.cast_one] using c2)
      simp only [Nat.cast_add, Nat.cast_one] at s2
      have h2' : ((n : ZMod k) + 2) = (n : ZMod k) + 1 + 1 := by
        rw [add_assoc, one_add_one_eq_two]
      exact hm n h1 (by omega) ⟨s1, by rw [h2']; exact s2⟩)
  refine isCyclicUnimodal_of_arch hk hinj q (fun n h1 h2 => ?_) (fun n h1 h2 => ?_) ?_
  · have := hup n h1 h2; rw [hcast] at this; exact this
  · have := hdn n h1 (by omega); rw [hcast] at this; exact this
  · simp only [hp0]; exact h0

/-- **Lemma C, the Rupert form (Theorem 17.10 with Theorem 8.9 and Theorem 7.3).**  At the view
`u = px − o` along the cap edge from the apex `o` to the axis vertex `px`, the rim of
`K_o = conv (V ∖ {px})` is the strictly convex counterclockwise cycle `p` (`p 0 = o`), every other
point except `px` is strictly inside, and the hypotheses of `capEdge_unimodal` hold.  Without a
horizontal double normal of the rim at `u`, `V` is Rupert: `px` is a double over the corner `o`
(Lemma 16.27′). -/
theorem isRupert_capEdge {k : ℕ} [NeZero k] (hk : 3 ≤ k) (V Wn : Finset ℝ³) (o px ey ew : ℝ³)
    (p : ZMod k → ℝ³) (X Y W : ZMod k → ℝ) (hpV : ∀ i, p i ∈ V)
    (hp0 : p 0 = o) (hrep : ∀ i, p i = o + X i • (px - o) + Y i • ey + W i • ew)
    (hcyc : ∀ i j, j ≠ i → j ≠ i + 1 → 0 < det3 (p (i + 1) - p i) (p j - p i) (px - o))
    (hrest : ∀ v ∈ V, v ≠ px → (∀ j, v ≠ p j) → ∀ i,
      0 < det3 (p (i + 1) - p i) (v - p i) (px - o))
    (hd : ∀ n : ℕ, 1 ≤ n → n + 1 < k → X n ≠ X (n + 1))
    (hm : ∀ n : ℕ, 1 ≤ n → n + 3 ≤ k → ¬ (X (n + 1) < X n ∧ X (n + 1) < X (n + 2)))
    (hstep : ∀ n : ℕ, 1 ≤ n → n + 1 < k →
      |(Y (n + 1) - Y n) * ⟪ey, px - o⟫ + (W (n + 1) - W n) * ⟪ew, px - o⟫| <
        ⟪px - o, px - o⟫ * |X (n + 1) - X n|)
    (hinj : Function.Injective fun i => ⟪p i, px - o⟫)
    (h0 : ⟪o, px - o⟫ < ⟪p 1, px - o⟫ ∨ ⟪o, px - o⟫ < ⟪p ((k - 1 : ℕ) : ZMod k), px - o⟫)
    (hnd : NoHDNAt Wn (px - o)) (hW : ∀ i, p i ∈ Wn) : IsRupert V := by
  classical
  have hu : px - o ≠ 0 := by
    intro h0'
    have n1 : (0 : ZMod k) - 1 ≠ 0 := by
      have := zmod_ne_add_one (by omega) ((0 : ZMod k) - 1)
      rwa [sub_add_cancel] at this
    have := hcyc 0 (0 - 1) n1 (zmod_sub_one_ne_add_one hk 0)
    rw [h0'] at this; simp only [det3, inner_zero_right, lt_irrefl] at this
  refine isRupert_of_edgeView_uniform V ∅ {px} Wn (px - o) hu hk p hpV
    (fun _ => Finset.notMem_empty _) hcyc ?_
    (capEdge_unimodal hk o (px - o) ey ew p X Y W hp0 hrep hd hm hstep hinj h0) hnd hW
    (fun m hm => absurd hm (Finset.notMem_empty _)) ?_
  · intro v hv _ hvD hvx
    exact hrest v hv (fun e => hvD (by rw [e]; exact mem_singleton_self _)) hvx
  · intro d hd'
    rw [mem_singleton.mp hd']
    exact ⟨0, -1, by norm_num, by rw [hp0, neg_one_smul, sub_neg_eq_add]; abel⟩

/-! ### Lemma C for type 24 -/

namespace Type24

variable {x : Fin 7 → ℝ³}

/-- Oblique coordinates of a point of the plane of `x 0, x a, x b` (affine in the point). -/
theorem oblX0_comb {v a b : Fin 7} {s t : ℝ} (h : x v = x 0 + s • (x a - x 0) + t • (x b - x 0)) :
    oblX0 x v = (1 - s - t) * oblX0 x 0 + s * oblX0 x a + t * oblX0 x b := by
  simp only [oblX0, h]
  have e : vol3 (x 0 + s • (x a - x 0) + t • (x b - x 0) - x 1) (x 2 - x 1) (x 6 - x 1) =
      (1 - s - t) * vol3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) +
        s * vol3 (x a - x 1) (x 2 - x 1) (x 6 - x 1) +
        t * vol3 (x b - x 1) (x 2 - x 1) (x 6 - x 1) := by
    simp only [vol3, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; ring
  rw [e]; ring

theorem oblX2_comb {v a b : Fin 7} {s t : ℝ} (h : x v = x 0 + s • (x a - x 0) + t • (x b - x 0)) :
    oblX2 x v = (1 - s - t) * oblX2 x 0 + s * oblX2 x a + t * oblX2 x b := by
  simp only [oblX2, h]
  have e : vol3 (x 0 - x 1) (x 0 + s • (x a - x 0) + t • (x b - x 0) - x 1) (x 6 - x 1) =
      (1 - s - t) * vol3 (x 0 - x 1) (x 0 - x 1) (x 6 - x 1) +
        s * vol3 (x 0 - x 1) (x a - x 1) (x 6 - x 1) +
        t * vol3 (x 0 - x 1) (x b - x 1) (x 6 - x 1) := by
    simp only [vol3, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; ring
  rw [e]; ring

theorem oblX6_comb {v a b : Fin 7} {s t : ℝ} (h : x v = x 0 + s • (x a - x 0) + t • (x b - x 0)) :
    oblX6 x v = (1 - s - t) * oblX6 x 0 + s * oblX6 x a + t * oblX6 x b := by
  simp only [oblX6, h]
  have e : vol3 (x 0 - x 1) (x 2 - x 1) (x 0 + s • (x a - x 0) + t • (x b - x 0) - x 1) =
      (1 - s - t) * vol3 (x 0 - x 1) (x 2 - x 1) (x 0 - x 1) +
        s * vol3 (x 0 - x 1) (x 2 - x 1) (x a - x 1) +
        t * vol3 (x 0 - x 1) (x 2 - x 1) (x b - x 1) := by
    simp only [vol3, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; ring
  rw [e]; ring

theorem oblX2_zero : oblX2 x 0 = 0 := by
  simp only [oblX2, vol3]; ring_nf

theorem oblX2_six : oblX2 x 6 = 0 := by
  simp only [oblX2, vol3]; ring_nf

theorem oblX6_zero : oblX6 x 0 = 0 := by
  simp only [oblX6, vol3]; ring_nf

theorem oblX6_two : oblX6 x 2 = 0 := by
  simp only [oblX6, vol3]; ring_nf

end Type24

/-- **The rim of a cap-edge crossing** (17.9, 17.10), for a point set `x : Fin 7 → ℝ³` with apex
`1` and axis vertices `ax` (the cap edge `1 ax`, view `u = x ax − x 1`), `ay`, `aw`, in oblique
coordinates `(cx, cy, cw)` at `1`.  The rim of `K_1` at `u` is the cycle `x ∘ r` (`r 0 = 1`, the
far path `r 1, …, r (k − 1)` from one of `ay`, `aw` to the other; strictly convex
counterclockwise, every other point except `x ax` strictly inside).  Along the far path `cx` has
distinct consecutive values and no interior local minimum (`(H-cap)`), and
`δ (L_y |Δcy| + L_w |Δcw|) ≤ L_x |Δcx|` on every step (`δ ≤ δ_x`).  The depths of the rim are
distinct, and the rim has no horizontal double normal at `u`. -/
def CapRim (x : Fin 7 → ℝ³) (ax ay aw : Fin 7) (cx cy cw : Fin 7 → ℝ) (δ : ℝ) (k : ℕ) [NeZero k]
    (r : ZMod k → Fin 7) : Prop :=
  3 ≤ k ∧ r 0 = 1 ∧ ((r 1 = ay ∧ r ((k - 1 : ℕ) : ZMod k) = aw) ∨
      (r 1 = aw ∧ r ((k - 1 : ℕ) : ZMod k) = ay)) ∧
    (∀ i j, j ≠ i → j ≠ i + 1 →
      0 < det3 (x (r (i + 1)) - x (r i)) (x (r j) - x (r i)) (x ax - x 1)) ∧
    (∀ v, v ≠ ax → (∀ j, v ≠ r j) → ∀ i,
      0 < det3 (x (r (i + 1)) - x (r i)) (x v - x (r i)) (x ax - x 1)) ∧
    (∀ n : ℕ, 1 ≤ n → n + 1 < k → cx (r n) ≠ cx (r (n + 1))) ∧
    (∀ n : ℕ, 1 ≤ n → n + 3 ≤ k →
      ¬ (cx (r (n + 1)) < cx (r n) ∧ cx (r (n + 1)) < cx (r (n + 2)))) ∧
    (∀ n : ℕ, 1 ≤ n → n + 1 < k →
      δ * (‖x ay - x 1‖ * |cy (r (n + 1)) - cy (r n)| + ‖x aw - x 1‖ * |cw (r (n + 1)) - cw (r n)|)
        ≤ ‖x ax - x 1‖ * |cx (r (n + 1)) - cx (r n)|) ∧
    Function.Injective (fun i => ⟪x (r i), x ax - x 1⟫) ∧
    NoHDNAt (univ.image fun i => x (r i)) (x ax - x 1)

/-- **Lemma C for one cap edge (Theorem 17.10), at `K`'s own metric.**  With the rim data
`CapRim`, if both cosines at `1` between the cap edge and the other two axis edges are below
`δ` in absolute value, and the cap edge makes an acute angle with one of them
(`⟪e_y, e_x⟫ > 0` or `⟪e_w, e_x⟫ > 0`), the point set is Rupert. -/
theorem isRupert_capEdge_frame {x : Fin 7 → ℝ³} (hinj : Function.Injective x) {ax ay aw : Fin 7}
    {cx cy cw : Fin 7 → ℝ}
    (hrep : ∀ v, x v = x 1 + cx v • (x ax - x 1) + cy v • (x ay - x 1) + cw v • (x aw - x 1))
    (hax : ax ≠ 1) {δ : ℝ} {k : ℕ} [NeZero k] {r : ZMod k → Fin 7}
    (hR : CapRim x ax ay aw cx cy cw δ k r)
    (hcy : |⟪x ay - x 1, x ax - x 1⟫| < δ * (‖x ay - x 1‖ * ‖x ax - x 1‖))
    (hcw : |⟪x aw - x 1, x ax - x 1⟫| < δ * (‖x aw - x 1‖ * ‖x ax - x 1‖))
    (hsign : 0 < ⟪x ay - x 1, x ax - x 1⟫ ∨ 0 < ⟪x aw - x 1, x ax - x 1⟫) :
    IsRupert (univ.image x) := by
  classical
  obtain ⟨hk, hr0, hends, hcyc, hrest, hd, hm, hδ, hz, hnd⟩ := hR
  have hLx : 0 < ‖x ax - x 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (hinj.ne hax))
  refine isRupert_capEdge hk (univ.image x) (univ.image fun i => x (r i)) (x 1) (x ax)
    (x ay - x 1) (x aw - x 1) (fun i => x (r i)) (fun i => cx (r i)) (fun i => cy (r i))
    (fun i => cw (r i)) (fun i => mem_image_of_mem x (mem_univ _)) (by simp only [hr0])
    (fun i => hrep (r i)) hcyc ?_ hd hm ?_ hz ?_ hnd (fun i => mem_image_of_mem _ (mem_univ _))
  · intro v hv hvx hvr i
    obtain ⟨w, -, rfl⟩ := mem_image.mp hv
    exact hrest w (fun e => hvx (by rw [e])) (fun j e => hvr j (by rw [e])) i
  · intro n h1 h2
    rw [real_inner_self_eq_norm_sq]
    exact capStep_of_cos hLx (sub_ne_zero.mpr (hd n h1 h2).symm) hcy hcw (hδ n h1 h2)
  · have ey : ⟪x 1, x ax - x 1⟫ < ⟪x ay, x ax - x 1⟫ ↔ 0 < ⟪x ay - x 1, x ax - x 1⟫ := by
      rw [inner_sub_left, sub_pos]
    have ew : ⟪x 1, x ax - x 1⟫ < ⟪x aw, x ax - x 1⟫ ↔ 0 < ⟪x aw - x 1, x ax - x 1⟫ := by
      rw [inner_sub_left, sub_pos]
    rcases hends with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2, ey, ew]
    · exact hsign
    · exact hsign.symm

/-- A point inside the far angle of a planar quad is above the lower of the two neighbours:
`s a + t b > min a b` for `s, t > 0`, `s + t > 1`, `a, b > 0` (17.4, 17.9). -/
theorem comb_not_below {s t a b : ℝ} (hs : 0 < s) (ht : 0 < t) (hst : 1 < s + t) (ha : 0 < a)
    (hb : 0 < b) : ¬ (s * a + t * b < a ∧ s * a + t * b < b) := by
  rintro ⟨h1, h2⟩
  rcases le_total a b with h | h
  · nlinarith [mul_le_mul_of_nonneg_left h ht.le, mul_pos (sub_pos.mpr hst) ha]
  · nlinarith [mul_le_mul_of_nonneg_left h hs.le, mul_pos (sub_pos.mpr hst) hb]

/-- `(H-cap)` from `3` in the middle (the arithmetic half of Lemma 17.9).  The far path of a
cap-edge crossing runs from `ay` to `aw` (`cx = 0` at both) through vertices among `3, 4, 5`
(`cx > 0`), the corner with both neighbours on the path is `3`, and `3` lies in the plane of
`0, 4, 5` opposite `0` (`cx 3 = s cx 4 + t cx 5`, `s, t > 0`, `s + t > 1`).  Then `cx` has no
interior local minimum along the path. -/
theorem noInteriorMin_of_mid3 {k : ℕ} [NeZero k] (hk : 3 ≤ k) {r : ZMod k → Fin 7}
    (hrinj : Function.Injective r) {cx : Fin 7 → ℝ} {ay aw : Fin 7}
    (hends : (r 1 = ay ∧ r ((k - 1 : ℕ) : ZMod k) = aw) ∨
      (r 1 = aw ∧ r ((k - 1 : ℕ) : ZMod k) = ay))
    (hy : cx ay = 0) (hw : cx aw = 0)
    (hpath : ∀ n : ℕ, 2 ≤ n → n + 2 ≤ k → r n = 3 ∨ r n = 4 ∨ r n = 5)
    (hpos : ∀ v, v = 3 ∨ v = 4 ∨ v = 5 → 0 < cx v)
    (hmid : ∀ n : ℕ, 3 ≤ n → n + 3 ≤ k → r n = 3)
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (hst : 1 < s + t) (h3 : cx 3 = s * cx 4 + t * cx 5) :
    ∀ n : ℕ, 1 ≤ n → n + 3 ≤ k →
      ¬ (cx (r (n + 1)) < cx (r n) ∧ cx (r (n + 1)) < cx (r (n + 2))) := by
  intro n h1 h2 ⟨c1, c2⟩
  have hn1 : (((n + 1 : ℕ) : ZMod k)) = (n : ZMod k) + 1 := by push_cast; ring
  have hn2 : (((n + 2 : ℕ) : ZMod k)) = (n : ZMod k) + 2 := by push_cast; ring
  have hmidpos : 0 < cx (r (n + 1)) := by
    have := hpath (n + 1) (by omega) (by omega)
    rw [hn1] at this
    exact hpos _ this
  have hend0 : cx (r 1) = 0 := by rcases hends with ⟨e, -⟩ | ⟨e, -⟩ <;> rw [e] <;> assumption
  have hendk : cx (r ((k - 1 : ℕ) : ZMod k)) = 0 := by
    rcases hends with ⟨-, e⟩ | ⟨-, e⟩ <;> rw [e] <;> assumption
  rcases Nat.lt_or_ge n 2 with hn | hn
  · -- `n = 1`: the left neighbour is an end
    have : n = 1 := by omega
    subst this
    have e : cx (r ((1 : ℕ) : ZMod k)) = 0 := by rw [Nat.cast_one]; exact hend0
    linarith
  rcases Nat.lt_or_ge (n + 3) k with hk' | hk'
  · -- the middle corner is `3`, its neighbours are `4` and `5`
    have m3 := hmid (n + 1) (by omega) (by omega)
    rw [hn1] at m3
    have a := hpath n hn (by omega)
    have b := hpath (n + 2) (by omega) (by omega)
    rw [hn2] at b
    have na : r n ≠ 3 := by
      rw [← m3]; intro e
      have := hrinj e
      exact zmod_ne_add_one (by omega) _ this
    have nb : r ((n : ZMod k) + 2) ≠ 3 := by
      rw [← m3]; intro e
      have := hrinj e
      have h' : (n : ZMod k) + 1 + 1 = (n : ZMod k) + 2 := by ring
      rw [← h'] at this
      exact (zmod_ne_add_one (by omega) _) this.symm
    have nab : r n ≠ r ((n : ZMod k) + 2) := by
      intro e
      have := hrinj e
      have h' := zmod_add_ne (k := k) (a := 0) (b := 2) (by omega) (by omega) (by omega)
        (n : ZMod k)
      simp only [Nat.cast_zero, add_zero, Nat.cast_ofNat] at h'
      exact h' this
    rw [m3, h3] at c1 c2
    have p4 := hpos 4 (by simp)
    have p5 := hpos 5 (by simp)
    have key := comb_not_below hs ht hst p4 p5
    rcases a with a | a | a
    · exact na a
    · rcases b with b | b | b
      · exact nb b
      · exact nab (a.trans b.symm)
      · rw [a] at c1; rw [b] at c2; exact key ⟨c1, c2⟩
    · rcases b with b | b | b
      · exact nb b
      · rw [a] at c1; rw [b] at c2; exact key ⟨c2, c1⟩
      · exact nab (a.trans b.symm)
  · -- `n + 3 = k`: the right neighbour is an end
    have : n + 2 = k - 1 := by omega
    have e : (n : ZMod k) + 2 = ((k - 1 : ℕ) : ZMod k) := by rw [← this, hn2]
    rw [e, hendk] at c2; linarith

/-- The oblique coordinates at `1` in the frame of the cap edge `12`. -/
theorem Type24.rep2 {x : Fin 7 → ℝ³} (T : Type24 x) (v : Fin 7) :
    x v = x 1 + oblX2 x v • (x 2 - x 1) + oblX0 x v • (x 0 - x 1) + oblX6 x v • (x 6 - x 1) := by
  conv_lhs => rw [T.rep v]
  abel

/-- The oblique coordinates at `1` in the frame of the cap edge `16`. -/
theorem Type24.rep6 {x : Fin 7 → ℝ³} (T : Type24 x) (v : Fin 7) :
    x v = x 1 + oblX6 x v • (x 6 - x 1) + oblX2 x v • (x 2 - x 1) + oblX0 x v • (x 0 - x 1) := by
  conv_lhs => rw [T.rep v]
  abel

/-- **Lemma C along the cap edge `12` (`E_2 = 012/126`, Theorem 17.10).**  With the rim of `K_1`
at `u = x 2 − x 1` given by `CapRim` (far path from `0` to `6`), cosines `c_ab`, `c_bc` below `δ`
and `c_ab > 0` or `c_bc > 0`, a type-24 point set is Rupert. -/
theorem isRupert_type24_E2 {x : Fin 7 → ℝ³} (T : Type24 x) {δ : ℝ} {k : ℕ} [NeZero k]
    {r : ZMod k → Fin 7} (hR : CapRim x 2 0 6 (oblX2 x) (oblX0 x) (oblX6 x) δ k r)
    (hcab : |⟪x 0 - x 1, x 2 - x 1⟫| < δ * (‖x 0 - x 1‖ * ‖x 2 - x 1‖))
    (hcbc : |⟪x 6 - x 1, x 2 - x 1⟫| < δ * (‖x 6 - x 1‖ * ‖x 2 - x 1‖))
    (hsign : 0 < ⟪x 0 - x 1, x 2 - x 1⟫ ∨ 0 < ⟪x 6 - x 1, x 2 - x 1⟫) :
    IsRupert (univ.image x) :=
  isRupert_capEdge_frame T.inj T.rep2 (by decide) hR hcab hcbc hsign

/-- **Lemma C along the cap edge `16` (`E_6 = 016/126`, Theorem 17.10).**  The mirror of
`isRupert_type24_E2`: far path from `2` to `0`, cosines `c_bc`, `c_ac`. -/
theorem isRupert_type24_E6 {x : Fin 7 → ℝ³} (T : Type24 x) {δ : ℝ} {k : ℕ} [NeZero k]
    {r : ZMod k → Fin 7} (hR : CapRim x 6 2 0 (oblX6 x) (oblX2 x) (oblX0 x) δ k r)
    (hcbc : |⟪x 2 - x 1, x 6 - x 1⟫| < δ * (‖x 2 - x 1‖ * ‖x 6 - x 1‖))
    (hcac : |⟪x 0 - x 1, x 6 - x 1⟫| < δ * (‖x 0 - x 1‖ * ‖x 6 - x 1‖))
    (hsign : 0 < ⟪x 2 - x 1, x 6 - x 1⟫ ∨ 0 < ⟪x 0 - x 1, x 6 - x 1⟫) :
    IsRupert (univ.image x) :=
  isRupert_capEdge_frame T.inj T.rep6 (by decide) hR hcbc hcac hsign

/-- **Theorem 17.10 (the cap-edge dichotomy; BB's Lemma C), at `K`'s own metric.**  Let `K` be
type 24 (any region), with the rims of both cap-edge crossings `E_2` and `E_6` given by
`CapRim` (off affine special position, `δ ≤ δ_cap = min (δ_2, δ_6)`).  If the three cosines at
`1` are below `δ` in absolute value (`|c|∞ < δ`), then `K` is Rupert unless all three inner
products at `1` are `≤ 0` (all face angles at `1` right or obtuse). -/
theorem isRupert_type24_capEdge {x : Fin 7 → ℝ³} (T : Type24 x) {δ : ℝ} {k₂ k₆ : ℕ}
    [NeZero k₂] [NeZero k₆] {r₂ : ZMod k₂ → Fin 7} {r₆ : ZMod k₆ → Fin 7}
    (h₂ : CapRim x 2 0 6 (oblX2 x) (oblX0 x) (oblX6 x) δ k₂ r₂)
    (h₆ : CapRim x 6 2 0 (oblX6 x) (oblX2 x) (oblX0 x) δ k₆ r₆)
    (hcab : |⟪x 0 - x 1, x 2 - x 1⟫| < δ * (‖x 0 - x 1‖ * ‖x 2 - x 1‖))
    (hcac : |⟪x 0 - x 1, x 6 - x 1⟫| < δ * (‖x 0 - x 1‖ * ‖x 6 - x 1‖))
    (hcbc : |⟪x 2 - x 1, x 6 - x 1⟫| < δ * (‖x 2 - x 1‖ * ‖x 6 - x 1‖))
    (hobt : ¬ (⟪x 0 - x 1, x 2 - x 1⟫ ≤ 0 ∧ ⟪x 0 - x 1, x 6 - x 1⟫ ≤ 0 ∧
      ⟪x 2 - x 1, x 6 - x 1⟫ ≤ 0)) :
    IsRupert (univ.image x) := by
  have hcbc' : |⟪x 6 - x 1, x 2 - x 1⟫| < δ * (‖x 6 - x 1‖ * ‖x 2 - x 1‖) := by
    rw [real_inner_comm, mul_comm ‖x 6 - x 1‖]; exact hcbc
  by_cases h : 0 < ⟪x 0 - x 1, x 2 - x 1⟫ ∨ 0 < ⟪x 2 - x 1, x 6 - x 1⟫
  · refine isRupert_type24_E2 T h₂ hcab hcbc' ?_
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (by rw [real_inner_comm]; exact h)
  · push Not at h
    have hac : 0 < ⟪x 0 - x 1, x 6 - x 1⟫ := by
      by_contra h'; push Not at h'; exact hobt ⟨h.1, h', h.2⟩
    exact isRupert_type24_E6 T h₆ hcbc hcac (Or.inr hac)

/-- `(H-cap)` for `E_2` from Lemma 17.9: the far path from `0` to `6` passes through vertices
among `3, 4, 5`, its corner with both neighbours on the path is `3`, and `3` lies in the plane
of `0, 4, 5` opposite `0` (the quadrilateral face `0345`). -/
theorem Type24.hcap2 {x : Fin 7 → ℝ³} (T : Type24 x) {k : ℕ} [NeZero k] (hk : 3 ≤ k)
    {r : ZMod k → Fin 7} (hrinj : Function.Injective r)
    (hends : (r 1 = 0 ∧ r ((k - 1 : ℕ) : ZMod k) = 6) ∨ (r 1 = 6 ∧ r ((k - 1 : ℕ) : ZMod k) = 0))
    (hpath : ∀ n : ℕ, 2 ≤ n → n + 2 ≤ k → r n = 3 ∨ r n = 4 ∨ r n = 5)
    (hmid : ∀ n : ℕ, 3 ≤ n → n + 3 ≤ k → r n = 3)
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (hst : 1 < s + t)
    (hq : x 3 = x 0 + s • (x 4 - x 0) + t • (x 5 - x 0)) :
    ∀ n : ℕ, 1 ≤ n → n + 3 ≤ k →
      ¬ (oblX2 x (r (n + 1)) < oblX2 x (r n) ∧ oblX2 x (r (n + 1)) < oblX2 x (r (n + 2))) := by
  refine noInteriorMin_of_mid3 hk hrinj hends Type24.oblX2_zero Type24.oblX2_six hpath ?_ hmid hs
    ht hst ?_
  · rintro v (rfl | rfl | rfl) <;> exact T.X2_pos (by decide)
  · rw [Type24.oblX2_comb hq, Type24.oblX2_zero]; ring

/-- `(H-cap)` for `E_6` (the mirror of `Type24.hcap2`). -/
theorem Type24.hcap6 {x : Fin 7 → ℝ³} (T : Type24 x) {k : ℕ} [NeZero k] (hk : 3 ≤ k)
    {r : ZMod k → Fin 7} (hrinj : Function.Injective r)
    (hends : (r 1 = 2 ∧ r ((k - 1 : ℕ) : ZMod k) = 0) ∨ (r 1 = 0 ∧ r ((k - 1 : ℕ) : ZMod k) = 2))
    (hpath : ∀ n : ℕ, 2 ≤ n → n + 2 ≤ k → r n = 3 ∨ r n = 4 ∨ r n = 5)
    (hmid : ∀ n : ℕ, 3 ≤ n → n + 3 ≤ k → r n = 3)
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (hst : 1 < s + t)
    (hq : x 3 = x 0 + s • (x 4 - x 0) + t • (x 5 - x 0)) :
    ∀ n : ℕ, 1 ≤ n → n + 3 ≤ k →
      ¬ (oblX6 x (r (n + 1)) < oblX6 x (r n) ∧ oblX6 x (r (n + 1)) < oblX6 x (r (n + 2))) := by
  refine noInteriorMin_of_mid3 hk hrinj hends Type24.oblX6_two Type24.oblX6_zero hpath ?_ hmid hs
    ht hst ?_
  · rintro v (rfl | rfl | rfl) <;> exact T.X6_pos (by decide)
  · rw [Type24.oblX6_comb hq, Type24.oblX6_zero]; ring

/-! ### Lemma Q and Remark Q′: the planar quad (17.4, 17.19) -/

/-- The closed failure condition of a 4-corner rim `(y, a, c, b)` at `u`: the diagonals
`{d₀, d₁} = {y, c}` and `{e₀, e₁} = {a, b}` are weakly depth-separated. -/
def Fails4 (d₀ d₁ e₀ e₁ u : ℝ³) : Prop :=
  max ⟪d₀, u⟫ ⟪d₁, u⟫ ≤ min ⟪e₀, u⟫ ⟪e₁, u⟫ ∨ max ⟪e₀, u⟫ ⟪e₁, u⟫ ≤ min ⟪d₀, u⟫ ⟪d₁, u⟫

theorem DepthSep.fails4 {d₀ d₁ e₀ e₁ u : ℝ³} (h : DepthSep d₀ d₁ e₀ e₁ u) :
    Fails4 d₀ d₁ e₀ e₁ u := by
  rcases h with h | h
  · exact Or.inl h.le
  · exact Or.inr h.le

/-- **Lemma Q / Remark Q′ (17.4, 17.19), every metric.**  If `c = y + s (a − y) + t (b − y)` with
`s, t > 0` and `s + t > 1` (`y, a, c, b` a planar quad, `c` opposite `y`), the diagonals of the
4-cycle `(y, a, c, b)` are weakly depth-separated at a view `u` only when all four depths are
equal. -/
theorem planarQuad_fails4 {y a c b u : ℝ³} {s t : ℝ} (hc : c = y + s • (a - y) + t • (b - y))
    (hs : 0 < s) (ht : 0 < t) (hst : 1 < s + t) (hF : Fails4 y c a b u) :
    ⟪c, u⟫ = ⟪y, u⟫ ∧ ⟪a, u⟫ = ⟪y, u⟫ ∧ ⟪b, u⟫ = ⟪y, u⟫ := by
  have hz : ⟪c, u⟫ = ⟪y, u⟫ + s * (⟪a, u⟫ - ⟪y, u⟫) + t * (⟪b, u⟫ - ⟪y, u⟫) := by
    rw [hc]; simp only [inner_add_left, real_inner_smul_left, inner_sub_left]
  set A := ⟪a, u⟫ - ⟪y, u⟫ with hA
  set B := ⟪b, u⟫ - ⟪y, u⟫ with hB
  have hst' : 0 < s + t - 1 := by linarith
  rcases hF with h | h
  · rw [max_le_iff, le_min_iff, le_min_iff] at h
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := h
    have hA0 : 0 ≤ A := by linarith
    have hB0 : 0 ≤ B := by linarith
    have hsA : s * A + t * B ≤ A := by linarith
    have hsB : s * A + t * B ≤ B := by linarith
    have hA' : A = 0 ∧ B = 0 := by
      rcases le_total A B with hAB | hAB
      · have k1 := mul_le_mul_of_nonneg_left hAB ht.le
        have k2 : (s + t - 1) * A ≤ 0 := by nlinarith
        have k3 : A = 0 := le_antisymm (by
          by_contra hn; push Not at hn; nlinarith [mul_pos hst' hn]) hA0
        refine ⟨k3, ?_⟩
        rw [k3, mul_zero, zero_add] at hsA
        exact le_antisymm (by by_contra hn; push Not at hn; nlinarith [mul_pos ht hn]) hB0
      · have k1 := mul_le_mul_of_nonneg_left hAB hs.le
        have k3 : B = 0 := le_antisymm (by
          by_contra hn; push Not at hn; nlinarith [mul_pos hst' hn]) hB0
        refine ⟨?_, k3⟩
        rw [k3, mul_zero, add_zero] at hsB
        exact le_antisymm (by by_contra hn; push Not at hn; nlinarith [mul_pos hs hn]) hA0
    obtain ⟨e1, e2⟩ := hA'
    refine ⟨?_, by linarith, by linarith⟩
    rw [hz, e1, e2]; ring
  · rw [max_le_iff, le_min_iff, le_min_iff] at h
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := h
    have hA0 : A ≤ 0 := by linarith
    have hB0 : B ≤ 0 := by linarith
    have hsA : A ≤ s * A + t * B := by linarith
    have hsB : B ≤ s * A + t * B := by linarith
    have hA' : A = 0 ∧ B = 0 := by
      rcases le_total A B with hAB | hAB
      · have k1 := mul_le_mul_of_nonneg_left hAB hs.le
        have k3 : B = 0 := le_antisymm hB0 (by
          by_contra hn; push Not at hn; nlinarith [mul_pos hst' (neg_pos.mpr hn)])
        refine ⟨?_, k3⟩
        rw [k3, mul_zero, add_zero] at hsA
        exact le_antisymm hA0 (by
          by_contra hn; push Not at hn; nlinarith [mul_pos hs (neg_pos.mpr hn)])
      · have k1 := mul_le_mul_of_nonneg_left hAB ht.le
        have k3 : A = 0 := le_antisymm hA0 (by
          by_contra hn; push Not at hn; nlinarith [mul_pos hst' (neg_pos.mpr hn)])
        refine ⟨k3, ?_⟩
        rw [k3, mul_zero, zero_add] at hsB
        exact le_antisymm hB0 (by
          by_contra hn; push Not at hn; nlinarith [mul_pos ht (neg_pos.mpr hn)])
    obtain ⟨e1, e2⟩ := hA'
    refine ⟨?_, by linarith, by linarith⟩
    rw [hz, e1, e2]; ring

/-- The planar quad is never depth-separated (strictly). -/
theorem planarQuad_not_depthSep {y a c b u : ℝ³} {s t : ℝ}
    (hc : c = y + s • (a - y) + t • (b - y)) (hs : 0 < s) (ht : 0 < t) (hst : 1 < s + t) :
    ¬ DepthSep y c a b u := by
  intro h
  obtain ⟨e1, e2, e3⟩ := planarQuad_fails4 hc hs ht hst h.fails4
  rcases h with h | h
  · rw [max_lt_iff, lt_min_iff] at h; linarith [h.1.1]
  · rw [max_lt_iff, lt_min_iff] at h; linarith [h.1.1]

/-- **Lemma Q′: the planar quad is unimodal at every view** where its four depths are
distinct. -/
theorem planarQuad_unimodal {y a c b u : ℝ³} {s t : ℝ}
    (hc : c = y + s • (a - y) + t • (b - y)) (hs : 0 < s) (ht : 0 < t) (hst : 1 < s + t)
    (hz : [⟪y, u⟫, ⟪a, u⟫, ⟪c, u⟫, ⟪b, u⟫].Nodup) :
    IsCyclicUnimodal fun i => ⟪quad y a c b i, u⟫ := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hz
  obtain ⟨⟨z1, z2, z3⟩, ⟨z4, z5⟩, z6, -⟩ := hz
  have hov := overlap4_of_not_depthSep (planarQuad_not_depthSep hc hs ht hst) z1 z2 z3 z4 z5 z6
  rw [quad_inner]
  refine isCyclicUnimodal_of_NWS4 (quad_injective z1 z2 z3 z4 z5 z6) ?_
  simp only [NWS4, quad_0, quad_1, quad_2, quad_3]
  exact ⟨hov.1, hov.2.1⟩

/-- **A 4-corner test, certified** (Proposition 8.8 / Theorem 8.9 / Lemma 17.15 with Theorem 7.3
and Lemma 16.27′): at the view `u` the rim `(y, a, c, b)` is a strictly convex counterclockwise
quadrilateral (`q₁`–`q₄`), every point of `V` other than the corners, the middles `M` and the
doubles `D` is strictly inside, the depths are distinct and the diagonals are not
depth-separated.  The middles lie over sides of the rim at a nonzero depth offset, the doubles
over its corners.  Without a horizontal double normal of the rim at `u`, `V` is Rupert. -/
theorem isRupert_quadView (V M D Wn : Finset ℝ³) {u y a c b : ℝ³} (hu : u ≠ 0)
    (hyV : y ∈ V) (haV : a ∈ V) (hbV : b ∈ V) (hcV : c ∈ V)
    (hyM : y ∉ M) (haM : a ∉ M) (hbM : b ∉ M) (hcM : c ∉ M)
    (q₁ : 0 < det3 (a - y) (c - y) u) (q₂ : 0 < det3 (c - a) (b - a) u)
    (q₃ : 0 < det3 (b - c) (y - c) u) (q₄ : 0 < det3 (y - b) (a - b) u)
    (hrest : ∀ z ∈ V, z ∉ M → z ∉ D → z ≠ y → z ≠ a → z ≠ c → z ≠ b → EdgeHidden u y a c b z)
    (hz : [⟪y, u⟫, ⟪a, u⟫, ⟪c, u⟫, ⟪b, u⟫].Nodup) (hsep : ¬ DepthSep y c a b u)
    (hM : ∀ m ∈ M, ∃ i : ZMod 4, ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
      m = quad y a c b i + s • (quad y a c b (i + 1) - quad y a c b i) + δ • u)
    (hD : ∀ d ∈ D, ∃ i : ZMod 4, ∃ h : ℝ, h ≠ 0 ∧ d = quad y a c b i - h • u)
    (hnd : NoHDNAt Wn u) (hW : y ∈ Wn ∧ a ∈ Wn ∧ c ∈ Wn ∧ b ∈ Wn) : IsRupert V := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hz
  obtain ⟨⟨z1, z2, z3⟩, ⟨z4, z5⟩, z6, -⟩ := hz
  have hov := overlap4_of_not_depthSep hsep z1 z2 z3 z4 z5 z6
  have i2 : det3 (a - y) (b - y) u = det3 (y - b) (a - b) u := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have i4 : det3 (c - a) (y - a) u = det3 (a - y) (c - y) u := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have i6 : det3 (b - c) (a - c) u = det3 (c - a) (b - a) u := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have i8 : det3 (y - b) (c - b) u = det3 (b - c) (y - c) u := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  obtain ⟨a0, a1, a2, a3⟩ := zmod4_add_one
  refine isRupert_of_edgeView_uniform V M D Wn u hu (k := 4) (by norm_num)
    (quad y a c b) ?_ ?_ ?_ ?_ ?_ hnd ?_ hM hD
  · intro i; rcases zmod4_cases i with rfl | rfl | rfl | rfl
    exacts [hyV, haV, hcV, hbV]
  · intro i; rcases zmod4_cases i with rfl | rfl | rfl | rfl
    exacts [hyM, haM, hcM, hbM]
  · intro i j hi hj
    rcases zmod4_pairs i j hi hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3]
    exacts [q₁, by rw [i2]; exact q₄, q₂, by rw [i4]; exact q₁, q₃, by rw [i6]; exact q₂, q₄,
      by rw [i8]; exact q₃]
  · intro z hz hzM hzD hzx i
    obtain ⟨r1, r2, r3, r4⟩ := hrest z hz hzM hzD (hzx 0) (hzx 1) (hzx 2) (hzx 3)
    rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
      simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3]
    exacts [r1, r2, r3, r4]
  · rw [quad_inner]
    refine isCyclicUnimodal_of_NWS4 (quad_injective z1 z2 z3 z4 z5 z6) ?_
    simp only [NWS4, quad_0, quad_1, quad_2, quad_3]
    exact ⟨hov.1, hov.2.1⟩
  · intro i; rcases zmod4_cases i with rfl | rfl | rfl | rfl
    exacts [hW.1, hW.2.1, hW.2.2.1, hW.2.2.2]

/-- **Lemma Q / Remark Q′, the Rupert form (17.4, 17.19).**  Any crossing test (vertex crossing:
`D = ∅`; edge crossing: `D` the other axle end; faces without a common vertex: `D = ∅`, Lemma
17.15) whose rim at `u` is the planar quad `(y, a, c, b)` with `c` opposite `y`
(`c = y + s (a − y) + t (b − y)`, `s, t > 0`, `s + t > 1`) certifies `V` at every metric, off
the ties of its four depths and its horizontal double normals.  For type 24, `(y, a, c, b) =
(0, 4, 3, 5)` or `(0, 5, 3, 4)`: `S_0 = 025/046` (Lemma Q), `025|346`, `046|235`, `235/346`,
`046/346-6` (Q′). -/
theorem isRupert_planarQuad (V M D Wn : Finset ℝ³) {u y a c b : ℝ³} {s t : ℝ} (hu : u ≠ 0)
    (hc : c = y + s • (a - y) + t • (b - y)) (hs : 0 < s) (ht : 0 < t) (hst : 1 < s + t)
    (hyV : y ∈ V) (haV : a ∈ V) (hbV : b ∈ V) (hcV : c ∈ V)
    (hyM : y ∉ M) (haM : a ∉ M) (hbM : b ∉ M) (hcM : c ∉ M)
    (q₁ : 0 < det3 (a - y) (c - y) u) (q₂ : 0 < det3 (c - a) (b - a) u)
    (q₃ : 0 < det3 (b - c) (y - c) u) (q₄ : 0 < det3 (y - b) (a - b) u)
    (hrest : ∀ z ∈ V, z ∉ M → z ∉ D → z ≠ y → z ≠ a → z ≠ c → z ≠ b → EdgeHidden u y a c b z)
    (hz : [⟪y, u⟫, ⟪a, u⟫, ⟪c, u⟫, ⟪b, u⟫].Nodup)
    (hM : ∀ m ∈ M, ∃ i : ZMod 4, ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
      m = quad y a c b i + s • (quad y a c b (i + 1) - quad y a c b i) + δ • u)
    (hD : ∀ d ∈ D, ∃ i : ZMod 4, ∃ h : ℝ, h ≠ 0 ∧ d = quad y a c b i - h • u)
    (hnd : NoHDNAt Wn u) (hW : y ∈ Wn ∧ a ∈ Wn ∧ c ∈ Wn ∧ b ∈ Wn) : IsRupert V :=
  isRupert_quadView V M D Wn hu hyV haV hbV hcV hyM haM hbM hcM q₁ q₂ q₃ q₄ hrest hz
    (planarQuad_not_depthSep hc hs ht hst) hM hD hnd hW

/-! ### Lemma 17.15: Proposition 8.8 for two faces without a common vertex -/

/-- **Lemma 17.15 (Proposition 8.8 for two disjoint faces), determinant form.**  Theorem 8.8's tilt
argument uses only that each middle lies over a chord of the reduced shadow
(`m = x i + s (x (i + 1) − x i) + δ u`, `δ ≠ 0`); no face structure and no common vertex are
needed (`isRupert_of_chords`, `isRupert_of_edgeView_uniform`).  So for faces `F_1`, `F_2` with no
common vertex and `u ∥ n_1 × n_2`, whose middles lie over the two silhouette edges `s_1`, `s_2`
(or over any other sides), a unimodal reduced rim without horizontal double normal certifies
`V`. -/
theorem isRupert_disjointFaces (V M Wn : Finset ℝ³) (u : ℝ³) (hu : u ≠ 0) {k : ℕ} [NeZero k]
    (hk : 3 ≤ k) (x : ZMod k → ℝ³) (hxV : ∀ i, x i ∈ V) (hxM : ∀ i, x i ∉ M)
    (hcyc : ∀ i j, j ≠ i → j ≠ i + 1 → 0 < det3 (x (i + 1) - x i) (x j - x i) u)
    (hrest : ∀ y ∈ V, y ∉ M → (∀ j, y ≠ x j) → ∀ i, 0 < det3 (x (i + 1) - x i) (y - x i) u)
    (hz : IsCyclicUnimodal (fun i => ⟪x i, u⟫)) (hnd : NoHDNAt Wn u) (hxW : ∀ i, x i ∈ Wn)
    (hM : ∀ m ∈ M, ∃ i : ZMod k, ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
      m = x i + s • (x (i + 1) - x i) + δ • u) : IsRupert V :=
  isRupert_of_edgeView_uniform V M ∅ Wn u hu hk x hxV hxM hcyc
    (fun y hy hyM _ hyx => hrest y hy hyM hyx) hz hnd hxW hM
    (fun _ hd => absurd hd (Finset.notMem_empty _))

end Minimality

end
