module

public import Minimality.Type24Corner
public import Minimality.Prism

@[expose] public section

/-!
# Type 24 in case C: Lemma W, WP as an item, L7, the arc criterion (§17)

`FEWER-FACES-PROOFS.md` §17 and its addendum, the parts that `Type24Cap.lean` and
`Type24Corner.lean` leave out.  The depth at a view `d` is `⟪·, d⟫` (`K`'s own metric).

* **Lemma W (the window lemma)** (`isRupert_lemmaW`): let `B = V ∖ {p}` have, at the view `u`,
  a certified reduced rim (strictly convex counterclockwise, the other points of `B` strictly
  inside, middles over sides, doubles over corners, cyclically unimodal, no horizontal double
  normal).  If the view hides `p`, strictly (`p` projects strictly inside the rim) or on the
  boundary (`p` lies over an open side of the rim at a nonzero depth offset, as the cap `1` does
  on the arc of a cap face), then `V` is Rupert.  The certificate of `B` is Lemma 16.27′
  (`isRupert_of_edgeView_uniform`); `p` costs nothing, as a hidden point or as one more middle.
  (Lemma W's converse, `K` free ⇒ `K − 1` free, is not needed for Rupertness.)
* **WP as a Rupert item** (`isRupert_wp`, `isRupert_wp2`, `isRupert_wp6`): on the arc
  `e_a + t e_b` (`t > 0`) of the cap face `1 0 b`, the cap `1` lies over the side `0 b` of `B`'s
  shadow (`cap_middle`, `cap_middle'`).  If `B`'s rim is the pentagon `(c, q, 0, b, 3)` with the
  sixth vertex strictly inside (`WPRim`, either orientation), and `z_c < z_q < z_0 < z_b`
  (`WPChain`), the rim is cyclically unimodal as soon as `z_3` differs from the other four
  depths (four consecutive corners of a 5-cycle are monotone: `isCyclicUnimodal_five_inc`,
  `isCyclicUnimodal_five_dec`), so without a horizontal double normal `K` is Rupert.
* **M1 with WP discharged** (`Type24.m1_corner_Ioo`, `isRupert_m1_corner_wp`): at an exact
  corner, M1's WP alternative holds on a whole open interval of arc views, so the Lemma W
  hypothesis `hWP` of `isRupert_m1_corner` is replaced by the rim of `B` on the face interval
  `(lo, ω3)` and the exclusions (distinct depths of `3`, no horizontal double normal) off a finite
  set of arc views.
* **L7 (Lemma 15.15 = W's Lemma 7, with BB's radius 17.8′)**: for `T′(x, c)` with the rim
  `(y, x, g, h)` at the view `ω e_x + e_y`, the rim does not fail when `z_h > z_y` and
  `z_g > z_x` (`l7_not_fails`).  In a frame at `1` the two forms are
  `l7_form_h`, `l7_form_g` (17.1: exactly linear in the inner products of the axes); at a
  diagonal metric they are positive when `X_x(g) ≥ 1` and `X_y(h) ≥ 1` (`l7_frame_corner`), and
  at every metric within the radius `δ_L7` of 17.8′ (`l7_frame_radius`, through the general
  bound `radius_pos` of 17.1′).  For type 24: `T′(2,6)`, `T′(6,2)` and `T′(0,6)`
  (`Type24.l7_t26`, `Type24.l7_t62`, `Type24.l7_t06`, and the Rupert forms
  `isRupert_l7_t26`, `isRupert_l7_t62`, `isRupert_l7_t06`).
* **The arc criterion 17.16′ on circle 2** (`Type24.arc_criterion2`, with WP
  `Type24.arc_criterion2_wp`, Rupert form `isRupert_arc_criterion2`): at an exact corner, if for
  every `κ > 0` some item's rim does not fail in the pencil at `t_τ κ` (or WP_2's pencil chain
  `WPPencil` holds at some arc view, `wpChain2_iff_pencil`), some item does not fail (or WP_2
  holds).  The **pair form** (`pair_rule`, the Cramer certificate
  `t2 B2 ℓ1 + t1 (−B1) ℓ2 = g_a (t2 B2 A1 − t1 B1 A2)`; `Type24.circle2_pair`,
  `isRupert_circle2_pair`): one test failing in the pencil only at `ν ≤ m1`, the other only at
  `ν ≥ m2`, do not both fail when `m1 / t1 < m2 / t2`.  The T′ pair of `Type24Corner.lean`
  (`tpair_corner`) has this form, with `T′(2,6)` failing only at `ν ≤ m` and `T′(0,6)` only at
  `ν ≥ ν34`.
* **Radii (17.1, 17.1′, 17.11, 17.12 for WP)**: the depth difference in a frame is exactly linear
  in the axis inner products (`inner_frame_diff`); a form `ℓ⁰ + Σ β h` with `|h_ij| ≤ δ ρ_ij` is
  positive when `δ Σ |β| ρ < ℓ⁰` (`radius_pos`), and on the octant `h ≤ 0` when
  `δ Σ max (0, β) ρ < ℓ⁰` (`radius_pos_octant`).  WP_2's three forms (`Type24.wp_form`) give
  WP_2 near the corner (`Type24.wpChain2_radius`, `isRupert_wp2_radius`) and on the obtuse
  octant (Lemma 17.11, `Type24.wpChain2_octant`).  Theorem 17.12 with WP_2 as the item
  (`isRupert_type24_near_wp2`): for `|c|∞ < δ` with `δ` below Lemma C's `δ_cap` (the `CapRim`
  data) and below WP_2's octant radius, `K` is Rupert (WP on the obtuse octant, Lemma C
  elsewhere).

Not formalized: the face conditions of 17.6 (that `B`'s rim is `(c, q, 0, b, 3)` exactly on
`(lo_f, ω3)`; the rim is a hypothesis, `WPRim`), the finiteness of the exclusions on the arc
(`isRupert_m1_corner_wp` takes the finite set `S` as a hypothesis), the "only if" half of 17.16′
(it needs other metrics of the same affine class), Lemma 17.16's general interval formula and
17.17 (b)–(d) beyond `Type24Corner.lean`, the radii of the other items (17.1′ for `S_0`, M3's
`δ_M3`, 17.20) and 17.12 for items other than WP_2.
-/

namespace Minimality

open Finset
open scoped RealInnerProductSpace

/-! ### Lemma W -/

/-- **Lemma W (the window lemma), Rupert form.**  Let `p ∈ V` and `B = V ∖ {p}`.  At the view
`u₀`, the cycle `x` is a certified reduced rim of `B` (Lemma 16.27′ with Theorem 7.3: strictly
convex counterclockwise, every other point of `B` outside `M ∪ D` strictly inside, middles `M`
over sides, doubles `D` over corners, cyclically unimodal depths, no horizontal double normal).
If the view hides `p`, strictly inside the rim or over an open side of it at a nonzero depth
offset (the closed window), `V` is Rupert. -/
theorem isRupert_lemmaW (V M D Wn : Finset ℝ³) (p u₀ : ℝ³) (hu₀ : u₀ ≠ 0) (hpV : p ∈ V)
    {k : ℕ} [NeZero k] (hk : 3 ≤ k) (x : ZMod k → ℝ³) (hxB : ∀ i, x i ∈ V.erase p)
    (hxM : ∀ i, x i ∉ M)
    (hcyc : ∀ i j, j ≠ i → j ≠ i + 1 → 0 < det3 (x (i + 1) - x i) (x j - x i) u₀)
    (hrest : ∀ y ∈ V.erase p, y ∉ M → y ∉ D → (∀ j, y ≠ x j) → ∀ i,
      0 < det3 (x (i + 1) - x i) (y - x i) u₀)
    (hz : IsCyclicUnimodal (fun i => ⟪x i, u₀⟫)) (hnd : NoHDNAt Wn u₀) (hxW : ∀ i, x i ∈ Wn)
    (hM : ∀ m ∈ M, ∃ i : ZMod k, ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
      m = x i + s • (x (i + 1) - x i) + δ • u₀)
    (hD : ∀ y ∈ D, ∃ i : ZMod k, ∃ h : ℝ, h ≠ 0 ∧ y = x i - h • u₀)
    (hp : (∀ i, 0 < det3 (x (i + 1) - x i) (p - x i) u₀) ∨
      ∃ i : ZMod k, ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
        p = x i + s • (x (i + 1) - x i) + δ • u₀) :
    IsRupert V := by
  classical
  have hxV : ∀ i, x i ∈ V := fun i => mem_of_mem_erase (hxB i)
  have hxp : ∀ i, x i ≠ p := fun i => ne_of_mem_erase (hxB i)
  rcases hp with hp | hp
  · refine isRupert_of_edgeView_uniform V M D Wn u₀ hu₀ hk x hxV hxM hcyc ?_ hz hnd hxW hM hD
    intro y hy hyM hyD hyx
    by_cases hyp : y = p
    · subst hyp; exact hp
    · exact hrest y (mem_erase.mpr ⟨hyp, hy⟩) hyM hyD hyx
  · refine isRupert_of_edgeView_uniform V (insert p M) D Wn u₀ hu₀ hk x hxV ?_ hcyc ?_ hz hnd
      hxW ?_ hD
    · intro i hi
      rcases mem_insert.mp hi with h | h
      · exact hxp i h
      · exact hxM i h
    · intro y hy hyM hyD hyx
      have hyp : y ≠ p := fun e => hyM (mem_insert.mpr (Or.inl e))
      exact hrest y (mem_erase.mpr ⟨hyp, hy⟩) (fun h => hyM (mem_insert_of_mem h)) hyD hyx
    · intro m hm
      rcases mem_insert.mp hm with h | h
      · subst h; exact hp
      · exact hM m h

/-! ### 5-cycles with four consecutive monotone corners -/

/-- A 5-cycle whose corners `0, 1, 2, 3` rise is unimodal (the fifth is free). -/
theorem isCyclicUnimodal_five_inc {z : ZMod 5 → ℝ} (hinj : Function.Injective z)
    (h01 : z 0 < z 1) (h12 : z 1 < z 2) (h23 : z 2 < z 3) : IsCyclicUnimodal z := by
  obtain ⟨a0, a1, a2, a3, a4⟩ := zmod5_add_one
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_sub_one
  have key : ∀ i : ZMod 5, z (i - 1) < z i ∧ z (i + 1) < z i → i = 3 ∨ i = 4 := by
    intro i hi
    rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl
    · rw [a0] at hi; linarith [hi.2]
    · rw [a1] at hi; linarith [hi.2]
    · rw [a2] at hi; linarith [hi.2]
    · exact Or.inl rfl
    · exact Or.inr rfl
  refine isCyclicUnimodal_of_atMostOne (by norm_num) hinj fun i j hi hj => ?_
  rcases key i hi with rfl | rfl <;> rcases key j hj with rfl | rfl
  · rfl
  · rw [a3] at hi; rw [b4] at hj; linarith [hi.2, hj.1]
  · rw [b4] at hi; rw [a3] at hj; linarith [hi.1, hj.2]
  · rfl

/-- A 5-cycle whose corners `0, 1, 2, 3` fall is unimodal (the fifth is free). -/
theorem isCyclicUnimodal_five_dec {z : ZMod 5 → ℝ} (hinj : Function.Injective z)
    (h01 : z 1 < z 0) (h12 : z 2 < z 1) (h23 : z 3 < z 2) : IsCyclicUnimodal z := by
  obtain ⟨a0, a1, a2, a3, a4⟩ := zmod5_add_one
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_sub_one
  have key : ∀ i : ZMod 5, z (i - 1) < z i ∧ z (i + 1) < z i → i = 0 ∨ i = 4 := by
    intro i hi
    rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · rw [b1] at hi; linarith [hi.1]
    · rw [b2] at hi; linarith [hi.1]
    · rw [b3] at hi; linarith [hi.1]
    · exact Or.inr rfl
  refine isCyclicUnimodal_of_atMostOne (by norm_num) hinj fun i j hi hj => ?_
  rcases key i hi with rfl | rfl <;> rcases key j hj with rfl | rfl
  · rfl
  · rw [b0] at hi; rw [a4] at hj; linarith [hi.1, hj.2]
  · rw [a4] at hi; rw [b0] at hj; linarith [hi.2, hj.1]
  · rfl

theorem quint_inner24 (p₀ p₁ p₂ p₃ p₄ u : ℝ³) :
    (fun i => ⟪quint p₀ p₁ p₂ p₃ p₄ i, u⟫) =
      quint ⟪p₀, u⟫ ⟪p₁, u⟫ ⟪p₂, u⟫ ⟪p₃, u⟫ ⟪p₄, u⟫ := by
  funext i; rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;> rfl

/-! ### WP as a Rupert item -/

/-- The arc view `e_a + t e_b` of the cap face `1 0 b`. -/
noncomputable def wpView (x : Fin 7 → ℝ³) (b : Fin 7) (t : ℝ) : ℝ³ :=
  (x 0 - x 1) + t • (x b - x 1)

/-- **On the arc (`t > 0`) the cap `1` lies over the open side `0 b`** (the closed window of
`1`): `x 1 = x 0 + t/(1 + t) (x b − x 0) − 1/(1 + t) d`. -/
theorem cap_middle (x : Fin 7 → ℝ³) (b : Fin 7) {t : ℝ} (ht : 0 < t) :
    x 1 = x 0 + (t / (1 + t)) • (x b - x 0) + (-(1 / (1 + t))) • wpView x b t := by
  have h : (1 + t) ≠ 0 := by positivity
  ext i
  simp only [wpView, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  field_simp
  ring

/-- The same, read along the side `b 0`. -/
theorem cap_middle' (x : Fin 7 → ℝ³) (b : Fin 7) {t : ℝ} (ht : 0 < t) :
    x 1 = x b + (1 / (1 + t)) • (x 0 - x b) + (-(1 / (1 + t))) • wpView x b t := by
  have h : (1 + t) ≠ 0 := by positivity
  ext i
  simp only [wpView, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  field_simp
  ring

/-- **The rim of `B = K − 1` at a WP view**: the 5-cycle `p` is strictly convex and
counterclockwise at `u`, and the vertex `x i` is strictly inside. -/
def WPRim (x : Fin 7 → ℝ³) (u : ℝ³) (p : ZMod 5 → ℝ³) (i : Fin 7) : Prop :=
  (∀ k j, j ≠ k → j ≠ k + 1 → 0 < det3 (p (k + 1) - p k) (p j - p k) u) ∧
    ∀ k, 0 < det3 (p (k + 1) - p k) (x i - p k) u

/-- **WP's depth chain** on the arc of `1 0 b`: `z_c < z_q < z_0 < z_b`. -/
def WPChain (x : Fin 7 → ℝ³) (b c q : Fin 7) (t : ℝ) : Prop :=
  ⟪x c, wpView x b t⟫ < ⟪x q, wpView x b t⟫ ∧ ⟪x q, wpView x b t⟫ < ⟪x 0, wpView x b t⟫ ∧
    ⟪x 0, wpView x b t⟫ < ⟪x b, wpView x b t⟫

/-- **The WP item at the arc view `t`, certified up to its depth chain**: `B`'s rim is the
pentagon `(c, q, 0, b, 3)` (either orientation) with `i` strictly inside, `z_3` differs from the
other four corner depths, and the rim has no horizontal double normal. -/
def WPItem (x : Fin 7 → ℝ³) (b c q i : Fin 7) (t : ℝ) : Prop :=
  (WPRim x (wpView x b t) (quint (x c) (x q) (x 0) (x b) (x 3)) i ∨
      WPRim x (wpView x b t) (quint (x b) (x 0) (x q) (x c) (x 3)) i) ∧
    ⟪x 3, wpView x b t⟫ ≠ ⟪x c, wpView x b t⟫ ∧ ⟪x 3, wpView x b t⟫ ≠ ⟪x q, wpView x b t⟫ ∧
    ⟪x 3, wpView x b t⟫ ≠ ⟪x 0, wpView x b t⟫ ∧ ⟪x 3, wpView x b t⟫ ≠ ⟪x b, wpView x b t⟫ ∧
    NoHDNAt {x c, x q, x 0, x b, x 3} (wpView x b t)

/-- **WP as a Rupert item (Fact 17.0 with Lemma W).**  On the arc `e_a + t e_b` (`t > 0`) of the
cap face `1 0 b`, with the vertices `1, c, q, 0, b, 3, i` exhausting `K`: if the WP item is
certified (`WPItem`) and WP's depth chain `z_c < z_q < z_0 < z_b` holds, `K` is Rupert. -/
theorem isRupert_wp {x : Fin 7 → ℝ³} (T : Type24 x) {b c q i : Fin 7} (hb : b ≠ 1) (hc : c ≠ 1)
    (hq : q ≠ 1) (hall : ∀ v : Fin 7, v = 1 ∨ v = c ∨ v = q ∨ v = 0 ∨ v = b ∨ v = 3 ∨ v = i)
    {t : ℝ} (ht : 0 < t) (hI : WPItem x b c q i t) (hC : WPChain x b c q t) :
    IsRupert (univ.image x) := by
  classical
  obtain ⟨hR, n1, n2, n3, n4, hnd⟩ := hI
  obtain ⟨c1, c2, c3⟩ := hC
  set u := wpView x b t with hu_def
  have hu : u ≠ 0 := by
    intro h0; rw [h0, inner_zero_right, inner_zero_right] at c1; exact lt_irrefl _ c1
  have mem : ∀ v, x v ∈ univ.image x := fun v => mem_image_of_mem x (mem_univ v)
  have hne : ∀ v, v ≠ 1 → x v ∈ (univ.image x).erase (x 1) := fun v hv =>
    mem_erase.mpr ⟨T.inj.ne hv, mem v⟩
  obtain ⟨a0, a1, a2, a3, a4⟩ := zmod5_add_one
  have h01 : (0 : Fin 7) ≠ 1 := by decide
  have h31 : (3 : Fin 7) ≠ 1 := by decide
  have hpos : 0 < t / (1 + t) := by positivity
  have hlt : t / (1 + t) < 1 := by rw [div_lt_one (by positivity)]; linarith
  have hpos' : 0 < 1 / (1 + t) := by positivity
  have hlt' : 1 / (1 + t) < 1 := by rw [div_lt_one (by positivity)]; linarith
  have hδ : -(1 / (1 + t)) ≠ 0 := by
    have : (0 : ℝ) < 1 / (1 + t) := by positivity
    linarith
  -- the other points of `B`: only `x i`
  have hother : ∀ y ∈ (univ.image x).erase (x 1), y ≠ x c → y ≠ x q → y ≠ x 0 → y ≠ x b →
      y ≠ x 3 → y = x i := by
    intro y hy yc yq y0 yb y3
    obtain ⟨hy1, hyV⟩ := mem_erase.mp hy
    obtain ⟨v, -, rfl⟩ := mem_image.mp hyV
    rcases hall v with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [absurd rfl hy1, absurd rfl yc, absurd rfl yq, absurd rfl y0, absurd rfl yb,
      absurd rfl y3, rfl]
  rcases hR with ⟨hcyc, h5⟩ | ⟨hcyc, h5⟩
  · refine isRupert_lemmaW (univ.image x) ∅ ∅ {x c, x q, x 0, x b, x 3} (x 1) u hu (mem 1)
      (k := 5) (by norm_num) (quint (x c) (x q) (x 0) (x b) (x 3)) ?_
      (fun _ => notMem_empty _) hcyc ?_ ?_ hnd ?_ (fun _ h => absurd h (notMem_empty _))
      (fun _ h => absurd h (notMem_empty _)) ?_
    · intro k
      rcases zmod5_cases k with rfl | rfl | rfl | rfl | rfl
      exacts [hne c hc, hne q hq, hne 0 h01, hne b hb, hne 3 h31]
    · intro y hy _ _ hyx k
      rw [hother y hy (hyx 0) (hyx 1) (hyx 2) (hyx 3) (hyx 4)]
      exact h5 k
    · rw [quint_inner24]
      refine isCyclicUnimodal_five_inc (quint_injective c1.ne (by linarith) (by linarith)
        (Ne.symm n1) c2.ne (by linarith) (Ne.symm n2) c3.ne (Ne.symm n3) (Ne.symm n4))
        c1 c2 c3
    · intro k
      rcases zmod5_cases k with rfl | rfl | rfl | rfl | rfl <;> simp [quint_0, quint_1,
        quint_2, quint_3, quint_4]
    · refine Or.inr ⟨2, t / (1 + t), -(1 / (1 + t)), hpos, hlt, hδ, ?_⟩
      rw [a2, quint_2, quint_3]
      exact cap_middle x b ht
  · refine isRupert_lemmaW (univ.image x) ∅ ∅ {x c, x q, x 0, x b, x 3} (x 1) u hu (mem 1)
      (k := 5) (by norm_num) (quint (x b) (x 0) (x q) (x c) (x 3)) ?_
      (fun _ => notMem_empty _) hcyc ?_ ?_ hnd ?_ (fun _ h => absurd h (notMem_empty _))
      (fun _ h => absurd h (notMem_empty _)) ?_
    · intro k
      rcases zmod5_cases k with rfl | rfl | rfl | rfl | rfl
      exacts [hne b hb, hne 0 h01, hne q hq, hne c hc, hne 3 h31]
    · intro y hy _ _ hyx k
      rw [hother y hy (hyx 3) (hyx 2) (hyx 1) (hyx 0) (hyx 4)]
      exact h5 k
    · rw [quint_inner24]
      refine isCyclicUnimodal_five_dec (quint_injective c3.ne' (by linarith) (by linarith)
        (Ne.symm n4) c2.ne' (by linarith) (Ne.symm n3) c1.ne' (Ne.symm n2) (Ne.symm n1))
        c3 c2 c1
    · intro k
      rcases zmod5_cases k with rfl | rfl | rfl | rfl | rfl <;> simp [quint_0, quint_1,
        quint_2, quint_3, quint_4]
    · refine Or.inr ⟨0, 1 / (1 + t), -(1 / (1 + t)), hpos', hlt', hδ, ?_⟩
      rw [a0, quint_0, quint_1]
      exact cap_middle' x b ht

/-- **WP_2 as a Rupert item**: `B`'s rim `(6, 4, 0, 2, 3)` on the arc of `1 0 2`, `5` inside. -/
theorem isRupert_wp2 {x : Fin 7 → ℝ³} (T : Type24 x) {t : ℝ} (ht : 0 < t)
    (hI : WPItem x 2 6 4 5 t) (hC : WPChain x 2 6 4 t) : IsRupert (univ.image x) :=
  isRupert_wp T (by decide) (by decide) (by decide) (by decide) ht hI hC

/-- **WP_6 as a Rupert item** (the mirror): `B`'s rim `(2, 5, 0, 6, 3)` on the arc of `1 0 6`,
`4` inside. -/
theorem isRupert_wp6 {x : Fin 7 → ℝ³} (T : Type24 x) {t : ℝ} (ht : 0 < t)
    (hI : WPItem x 6 2 5 4 t) (hC : WPChain x 6 2 5 t) : IsRupert (univ.image x) :=
  isRupert_wp T (by decide) (by decide) (by decide) (by decide) ht hI hC

theorem wpChain2_iff {x : Fin 7 → ℝ³} {t : ℝ} : Type24.WPChain2 x t ↔ WPChain x 2 6 4 t :=
  Iff.rfl

/-! ### M1 with WP discharged -/

namespace Type24

variable {x : Fin 7 → ℝ³} (T : Type24 x)
include T

/-- **M1 (Theorem 17.8) at the exact corner, interval form.**  As `m1_corner`, but WP_2's depth
chain holds on a whole open interval `(L, U) ⊂ (lo, ω3)` of arc views. -/
theorem m1_corner_Ioo (hE : ExactCorner x) (h3 : 0 < omega3 x) (h4 : 0 < omega4 x)
    (h5 : 0 < omega5 x) (h45 : 1 < omega4 x * omega5 x) {lo : ℝ} (hlo : 0 < lo)
    (hlo3 : lo < omega3 x)
    (hab : (omega3 x * (omega4 x * omega5 x - 1) < 1 + omega5 x ∨
        omega3 x * (omega4 x * omega5 x - 1) * oblX2 x 4 < (1 - oblX0 x 4) * (1 + omega5 x)) ∨
      (oblX2 x 4 < 1 - oblX0 x 4 ∧
        lo * (omega4 x * omega5 x - 1) * oblX2 x 4 < (1 - oblX0 x 4) * (1 + omega5 x))) :
    ¬ Fails4 (x 0) (x 6) (x 2) (x 4) (viewT26 x) ∨
      (∃ L U, lo ≤ L ∧ L < U ∧ U ≤ omega3 x ∧ ∀ t, L < t → t < U → WPChain2 x t) ∨
      ¬ Fails4 (x 0) (x 3) (x 2) (x 6) (view0 x) := by
  by_cases hT : Fails4 (x 0) (x 6) (x 2) (x 4) (viewT26 x)
  swap; · exact Or.inl hT
  by_cases hS : Fails4 (x 0) (x 3) (x 2) (x 6) (view0 x)
  swap; · exact Or.inr (Or.inr hS)
  refine Or.inr (Or.inl ?_)
  have ga := T.ga_pos; have gb := T.gb_pos; have gc := T.gc_pos
  have a4 := T.X0_pos (v := 4) (by decide)
  have b4 := T.X2_pos (v := 4) (by decide)
  obtain ⟨t1, t2⟩ := T.t26_fails_corner hE h3 hT
  have s := T.s0_fails_corner hE h3 h4 h5 h45 hS
  have hm : omega5 x * omega4 x = omega4 x * omega5 x := mul_comm _ _
  rw [hm] at s
  set ga' := ⟪x 0 - x 1, x 0 - x 1⟫
  set gb' := ⟪x 2 - x 1, x 2 - x 1⟫
  have h5' : 0 < 1 + omega5 x := by linarith
  have s' := mul_le_mul_of_nonneg_left s h3.le
  rcases hab with (ha | ha) | ⟨hr4, hH5⟩
  · exfalso
    nlinarith [mul_lt_mul_of_pos_right ha ga, mul_le_mul_of_nonneg_left t1 h5'.le]
  · exfalso
    have k1 : (1 - oblX0 x 4) * ga' ≤ omega3 x * gb' * oblX2 x 4 := by linarith
    nlinarith [mul_lt_mul_of_pos_right ha ga, mul_le_mul_of_nonneg_left k1 h5'.le,
      mul_le_mul_of_nonneg_left s' b4.le]
  · have k1 : (1 - oblX0 x 4) * ga' ≤ omega3 x * gb' * oblX2 x 4 := by linarith
    have hgt : ga' < omega3 x * gb' := by nlinarith [mul_lt_mul_of_pos_right hr4 ga]
    have hlo' : lo * oblX2 x 4 * gb' < (1 - oblX0 x 4) * ga' := by
      have k2 := mul_le_mul_of_nonneg_left s (mul_pos hlo b4).le
      nlinarith [mul_lt_mul_of_pos_right hH5 ga]
    set U := min (omega3 x) ((1 - oblX0 x 4) * ga' / (oblX2 x 4 * gb')) with hU
    set L := max lo (ga' / gb') with hL
    have hLU : L < U := by
      rw [hL, hU, max_lt_iff, lt_min_iff, lt_min_iff, div_lt_iff₀ gb,
        lt_div_iff₀ (mul_pos b4 gb), div_lt_div_iff₀ gb (mul_pos b4 gb)]
      refine ⟨⟨hlo3, by nlinarith⟩, by linarith, ?_⟩
      nlinarith [mul_lt_mul_of_pos_right hr4 (mul_pos ga gb)]
    refine ⟨L, U, le_max_left _ _, hLU, min_le_left _ _, fun t htL htU => ?_⟩
    rw [hL, max_lt_iff, div_lt_iff₀ gb] at htL
    rw [hU, lt_min_iff, lt_div_iff₀ (mul_pos b4 gb)] at htU
    have dW := fun v => T.depth_corner hE v 1 t 0
    have hw : (1 : ℝ) • (x 0 - x 1) + t • (x 2 - x 1) + (0 : ℝ) • (x 6 - x 1) =
        (x 0 - x 1) + t • (x 2 - x 1) := by module
    rw [hw] at dW
    have ht0 : 0 < t := by nlinarith
    simp only [WPChain2]
    rw [dW 6, dW 4, dW 0, dW 2]
    simp only [T.oblX0_zero', Type24.oblX2_zero, Type24.oblX6_zero,
      Type24.oblX0_six, Type24.oblX2_six, T.oblX6_six, Type24.oblX0_two, T.oblX2_two,
      Type24.oblX6_two]
    refine ⟨?_, ?_, ?_⟩
    · nlinarith [mul_pos ga a4, mul_pos (mul_pos ht0 gb) b4]
    · nlinarith
    · nlinarith

end Type24

/-- **M1 (Theorem 17.8) at an exact corner, Rupert form, with WP as an item.**  As
`isRupert_m1_corner`, with the Lemma W hypothesis `hWP` discharged: it suffices that WP_2 is
certified up to its depth chain (`WPItem`: `B`'s rim `(6, 4, 0, 2, 3)` with `5` inside, `z_3`
distinct, no horizontal double normal) at every arc view `t ∈ (lo, ω3)` outside a finite set
`S` (17.6: the rim holds on the whole face interval; the exclusions are finitely many views). -/
theorem isRupert_m1_corner_wp {x : Fin 7 → ℝ³} (T : Type24 x) (hE : ExactCorner x)
    (h3 : 0 < omega3 x) (h4 : 0 < omega4 x) (h5 : 0 < omega5 x)
    (h45 : 1 < omega4 x * omega5 x) {lo : ℝ} (hlo : 0 < lo) (hlo3 : lo < omega3 x)
    (hab : (omega3 x * (omega4 x * omega5 x - 1) < 1 + omega5 x ∨
        omega3 x * (omega4 x * omega5 x - 1) * oblX2 x 4 < (1 - oblX0 x 4) * (1 + omega5 x)) ∨
      (oblX2 x 4 < 1 - oblX0 x 4 ∧
        lo * (omega4 x * omega5 x - 1) * oblX2 x 4 < (1 - oblX0 x 4) * (1 + omega5 x)))
    (hT : QuadTest' (univ.image x) (viewT26 x) (x 0) (x 2) (x 6) (x 4))
    (hS : QuadTest' (univ.image x) (view0 x) (x 0) (x 2) (x 3) (x 6))
    (S : Finset ℝ) (hWP : ∀ t, lo < t → t < omega3 x → t ∉ S → WPItem x 2 6 4 5 t) :
    IsRupert (univ.image x) := by
  rcases T.m1_corner_Ioo hE h3 h4 h5 h45 hlo hlo3 hab with h | ⟨L, U, hL, hLU, hU, hch⟩ | h
  · exact hT.isRupert h
  · obtain ⟨t, ⟨htL, htU⟩, htS⟩ := ((Set.Ioo_infinite hLU).sdiff S.finite_toSet).nonempty
    exact isRupert_wp2 T (by linarith) (hWP t (by linarith) (by linarith) htS) (hch t htL htU)
  · exact hS.isRupert h

/-! ### L7 (Lemma 15.15 = W's Lemma 7) and its radius (17.8′) -/

/-- **The radius bound of 17.1′.**  A form `ℓ⁰ + Σ β_ij h_ij`, with `|h_ij| ≤ δ ρ_ij`, is positive
when `δ Σ |β_ij| ρ_ij < ℓ⁰`. -/
theorem radius_pos {l0 b1 b2 b3 h1 h2 h3 r1 r2 r3 δ : ℝ} (hh1 : |h1| ≤ δ * r1)
    (hh2 : |h2| ≤ δ * r2) (hh3 : |h3| ≤ δ * r3)
    (hδ : δ * (|b1| * r1 + |b2| * r2 + |b3| * r3) < l0) :
    0 < l0 + b1 * h1 + b2 * h2 + b3 * h3 := by
  have k : ∀ b h r : ℝ, |h| ≤ δ * r → -(|b| * (δ * r)) ≤ b * h := by
    intro b h r hh
    have e1 := neg_abs_le (b * h)
    rw [abs_mul] at e1
    nlinarith [mul_le_mul_of_nonneg_left hh (abs_nonneg b)]
  nlinarith [k b1 h1 r1 hh1, k b2 h2 r2 hh2, k b3 h3 r3 hh3]

/-- **L7, the rule at every metric.**  The rim `(y, x, g, h)` does not fail when `z_h > z_y` and
`z_g > z_x` (each failure pattern contains `z_h ≤ z_y` or `z_g ≤ z_x`). -/
theorem l7_not_fails {Py Px Pg Ph u : ℝ³} (hh : ⟪Py, u⟫ < ⟪Ph, u⟫) (hg : ⟪Px, u⟫ < ⟪Pg, u⟫) :
    ¬ Fails4 Py Pg Px Ph u := by
  rintro (h | h) <;> rw [max_le_iff, le_min_iff, le_min_iff] at h
  · linarith [h.2.1]
  · linarith [h.2.2]

/-- **L7's form `z_h − z_y` (17.8′, exactly linear in the axis inner products, 17.1)** at the view
`ω e_x + e_y`, for `P_h = o + X e_x + Y e_y + C e_c`. -/
theorem l7_form_h (o ex ey ec : ℝ³) (ω X Y C : ℝ) :
    ⟪o + X • ex + Y • ey + C • ec, ω • ex + ey⟫ - ⟪o + ey, ω • ex + ey⟫ =
      ω * X * ⟪ex, ex⟫ + (Y - 1) * ⟪ey, ey⟫ + (ω * (Y - 1) + X) * ⟪ex, ey⟫ +
        (ω * C) * ⟪ex, ec⟫ + C * ⟪ey, ec⟫ := by
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    real_inner_comm ex ey, real_inner_comm ex ec, real_inner_comm ey ec]
  ring

/-- **L7's form `z_g − z_x` (17.8′).** -/
theorem l7_form_g (o ex ey ec : ℝ³) (ω X Y C : ℝ) :
    ⟪o + X • ex + Y • ey + C • ec, ω • ex + ey⟫ - ⟪o + ex, ω • ex + ey⟫ =
      ω * (X - 1) * ⟪ex, ex⟫ + Y * ⟪ey, ey⟫ + (ω * Y + X - 1) * ⟪ex, ey⟫ +
        (ω * C) * ⟪ex, ec⟫ + C * ⟪ey, ec⟫ := by
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    real_inner_comm ex ey, real_inner_comm ex ec, real_inner_comm ey ec]
  ring

/-- **L7 at a diagonal metric (Lemma 15.15).**  In a frame `o; e_x, e_y, e_c` with pairwise
orthogonal axes, at the view `ω e_x + e_y` (`ω > 0`), the rim `(y, x, g, h)` with `y = o + e_y`,
`x = o + e_x` does not fail when `X_x(g) ≥ 1`, `X_y(g) > 0`, `X_x(h) > 0` and `X_y(h) ≥ 1`. -/
theorem l7_frame_corner {o ex ey ec Py Px Pg Ph u : ℝ³} {ω Xg Yg Cg Xh Yh Ch : ℝ}
    (hω : 0 < ω) (hex : ex ≠ 0) (hey : ey ≠ 0) (hxy : ⟪ex, ey⟫ = 0) (hxc : ⟪ex, ec⟫ = 0)
    (hyc : ⟪ey, ec⟫ = 0) (hy : Py = o + ey) (hx : Px = o + ex)
    (hg : Pg = o + Xg • ex + Yg • ey + Cg • ec) (hh : Ph = o + Xh • ex + Yh • ey + Ch • ec)
    (hu : u = ω • ex + ey) (hXg : 1 ≤ Xg) (hYg : 0 < Yg) (hXh : 0 < Xh) (hYh : 1 ≤ Yh) :
    ¬ Fails4 Py Pg Px Ph u := by
  have gx : 0 < ⟪ex, ex⟫ := real_inner_self_pos.mpr hex
  have gy : 0 < ⟪ey, ey⟫ := real_inner_self_pos.mpr hey
  subst hy hx hg hh hu
  refine l7_not_fails ?_ ?_
  · have e := l7_form_h o ex ey ec ω Xh Yh Ch
    rw [hxy, hxc, hyc] at e
    nlinarith [mul_pos (mul_pos hω hXh) gx, mul_nonneg (sub_nonneg.mpr hYh) gy.le]
  · have e := l7_form_g o ex ey ec ω Xg Yg Cg
    rw [hxy, hxc, hyc] at e
    nlinarith [mul_nonneg (mul_nonneg hω.le (sub_nonneg.mpr hXg)) gx.le, mul_pos hYg gy]

/-- **L7 off the corner, with BB's radius (17.8′).**  In a frame `o; e_x, e_y, e_c` with
`L_i = ‖e_i‖`, if the three axis cosines are at most `δ` in absolute value
(`|⟪e_i, e_j⟫| ≤ δ L_i L_j`) and `δ` is below both radii of 17.8′ (`δ₁`, `δ₂` multiplied out:
`δ Σ |β| L L < ℓ⁰` for the forms `z_h − z_y`, `z_g − z_x`), the rim `(y, x, g, h)` does not
fail at the view `ω e_x + e_y`. -/
theorem l7_frame_radius {o ex ey ec Py Px Pg Ph u : ℝ³} {ω Xg Yg Cg Xh Yh Ch δ : ℝ}
    (hxy : |⟪ex, ey⟫| ≤ δ * (‖ex‖ * ‖ey‖)) (hxc : |⟪ex, ec⟫| ≤ δ * (‖ex‖ * ‖ec‖))
    (hyc : |⟪ey, ec⟫| ≤ δ * (‖ey‖ * ‖ec‖)) (hy : Py = o + ey) (hx : Px = o + ex)
    (hg : Pg = o + Xg • ex + Yg • ey + Cg • ec) (hh : Ph = o + Xh • ex + Yh • ey + Ch • ec)
    (hu : u = ω • ex + ey)
    (hδh : δ * (|ω * (Yh - 1) + Xh| * (‖ex‖ * ‖ey‖) + |ω * Ch| * (‖ex‖ * ‖ec‖) +
      |Ch| * (‖ey‖ * ‖ec‖)) < ω * Xh * ‖ex‖ ^ 2 + (Yh - 1) * ‖ey‖ ^ 2)
    (hδg : δ * (|ω * Yg + Xg - 1| * (‖ex‖ * ‖ey‖) + |ω * Cg| * (‖ex‖ * ‖ec‖) +
      |Cg| * (‖ey‖ * ‖ec‖)) < ω * (Xg - 1) * ‖ex‖ ^ 2 + Yg * ‖ey‖ ^ 2) :
    ¬ Fails4 Py Pg Px Ph u := by
  subst hy hx hg hh hu
  refine l7_not_fails ?_ ?_
  · have e := l7_form_h o ex ey ec ω Xh Yh Ch
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at e
    have := radius_pos hxy hxc hyc hδh
    linarith
  · have e := l7_form_g o ex ey ec ω Xg Yg Cg
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at e
    have := radius_pos hxy hxc hyc hδg
    linarith

namespace Type24

variable {x : Fin 7 → ℝ³} (T : Type24 x)
include T

theorem rep_ba (v : Fin 7) : x v = x 1 + oblX2 x v • (x 2 - x 1) + oblX0 x v • (x 0 - x 1) +
    oblX6 x v • (x 6 - x 1) := by
  conv_lhs => rw [T.rep v]
  abel

theorem rep_ca (v : Fin 7) : x v = x 1 + oblX6 x v • (x 6 - x 1) + oblX0 x v • (x 0 - x 1) +
    oblX2 x v • (x 2 - x 1) := by
  conv_lhs => rw [T.rep v]
  abel

theorem ne_ea : x 0 - x 1 ≠ 0 := sub_ne_zero.mpr (T.inj.ne (by decide))
theorem ne_eb : x 2 - x 1 ≠ 0 := sub_ne_zero.mpr (T.inj.ne (by decide))
theorem ne_ec : x 6 - x 1 ≠ 0 := sub_ne_zero.mpr (T.inj.ne (by decide))

omit T in
theorem mem345 : ∀ h : Fin 7, h ∈ ({3, 4, 5} : Finset (Fin 7)) →
    h ∉ ({1, 2, 6} : Finset (Fin 7)) ∧ h ∉ ({0, 1, 6} : Finset (Fin 7)) ∧
      h ∉ ({0, 1, 2} : Finset (Fin 7)) := by decide

omit T in
theorem add_sub_one' (v : Fin 7) : x v = x 1 + (x v - x 1) := by abel

/-- **L7 for `T′(2,6) = 012/236` at an exact corner (Lemma 15.15).**  With the rim `(0, 2, 3, h)`
(`(y, x, g) = (0, 2, 3)`, `h ∈ {4, 5}`), `b3 ≥ 1` and `a_h ≥ 1`, the test does not fail. -/
theorem l7_t26 (hE : ExactCorner x) (h3 : 0 < omega3 x) {h : Fin 7}
    (hh : h ∈ ({3, 4, 5} : Finset (Fin 7)))
    (hb3 : 1 ≤ oblX2 x 3) (hah : 1 ≤ oblX0 x h) :
    ¬ Fails4 (x 0) (x 3) (x 2) (x h) (viewT26 x) := by
  obtain ⟨e1, e2, e3⟩ := hE
  exact l7_frame_corner h3 T.ne_eb T.ne_ea (by rw [real_inner_comm]; exact e1) e3 e2
    (add_sub_one' 0) (add_sub_one' 2) (T.rep_ba 3) (T.rep_ba h) (by simp only [viewT26]; abel)
    hb3 (T.X0_pos (v := 3) (by decide)) (T.X2_pos (mem345 h hh).2.1) hah

/-- **L7 for `T′(6,2) = 016/236` at an exact corner** (the mirror): rim `(0, 6, 3, h)`,
`c3 ≥ 1`, `a_h ≥ 1`. -/
theorem l7_t62 (hE : ExactCorner x) (h3 : 0 < omega3 x) {h : Fin 7}
    (hh : h ∈ ({3, 4, 5} : Finset (Fin 7))) (hc3 : 1 ≤ oblX6 x 3) (hah : 1 ≤ oblX0 x h) :
    ¬ Fails4 (x 0) (x 3) (x 6) (x h) (viewT62 x) := by
  obtain ⟨e1, e2, e3⟩ := hE
  exact l7_frame_corner h3 T.ne_ec T.ne_ea (by rw [real_inner_comm]; exact e2)
    (by rw [real_inner_comm]; exact e3) e1
    (add_sub_one' 0) (add_sub_one' 6) (T.rep_ca 3) (T.rep_ca h) (by simp only [viewT62]; abel)
    hc3 (T.X0_pos (v := 3) (by decide)) (T.X6_pos (mem345 h hh).2.2) hah

/-- **L7 for `T′(0,6) = 012/046` at an exact corner**: rim `(2, 0, 4, h)`
(`(y, x, g) = (2, 0, 4)`), `a4 ≥ 1`, `b_h ≥ 1`. -/
theorem l7_t06 (hE : ExactCorner x) (h4 : 0 < omega4 x) {h : Fin 7}
    (hh : h ∈ ({3, 4, 5} : Finset (Fin 7))) (ha4 : 1 ≤ oblX0 x 4) (hbh : 1 ≤ oblX2 x h) :
    ¬ Fails4 (x 2) (x 4) (x 0) (x h) (viewT06 x) := by
  obtain ⟨e1, e2, e3⟩ := hE
  exact l7_frame_corner h4 T.ne_ea T.ne_eb e1 e2 e3
    (add_sub_one' 2) (add_sub_one' 0) (T.rep 4) (T.rep h) rfl
    ha4 (T.X2_pos (v := 4) (by decide)) (T.X0_pos (mem345 h hh).1) hbh

/-- **L7 for `T′(2,6)` off the corner (17.8′)**: at every metric whose three cosines at `1` are
at most `δ`, with `δ` below both radii of 17.8′ (multiplied out, `L_a, L_b, L_c` the axis
lengths), the rim `(0, 2, 3, h)` does not fail. -/
theorem l7_t26_radius {h : Fin 7} {δ : ℝ}
    (hab : |⟪x 2 - x 1, x 0 - x 1⟫| ≤ δ * (‖x 2 - x 1‖ * ‖x 0 - x 1‖))
    (hbc : |⟪x 2 - x 1, x 6 - x 1⟫| ≤ δ * (‖x 2 - x 1‖ * ‖x 6 - x 1‖))
    (hac : |⟪x 0 - x 1, x 6 - x 1⟫| ≤ δ * (‖x 0 - x 1‖ * ‖x 6 - x 1‖))
    (hδh : δ * (|omega3 x * (oblX0 x h - 1) + oblX2 x h| * (‖x 2 - x 1‖ * ‖x 0 - x 1‖) +
      |omega3 x * oblX6 x h| * (‖x 2 - x 1‖ * ‖x 6 - x 1‖) +
      |oblX6 x h| * (‖x 0 - x 1‖ * ‖x 6 - x 1‖)) <
        omega3 x * oblX2 x h * ‖x 2 - x 1‖ ^ 2 + (oblX0 x h - 1) * ‖x 0 - x 1‖ ^ 2)
    (hδg : δ * (|omega3 x * oblX0 x 3 + oblX2 x 3 - 1| * (‖x 2 - x 1‖ * ‖x 0 - x 1‖) +
      |omega3 x * oblX6 x 3| * (‖x 2 - x 1‖ * ‖x 6 - x 1‖) +
      |oblX6 x 3| * (‖x 0 - x 1‖ * ‖x 6 - x 1‖)) <
        omega3 x * (oblX2 x 3 - 1) * ‖x 2 - x 1‖ ^ 2 + oblX0 x 3 * ‖x 0 - x 1‖ ^ 2) :
    ¬ Fails4 (x 0) (x 3) (x 2) (x h) (viewT26 x) :=
  l7_frame_radius hab hbc hac (add_sub_one' 0) (add_sub_one' 2) (T.rep_ba 3) (T.rep_ba h)
    (by simp only [viewT26]; abel) hδh hδg

end Type24

/-- **L7 for `T′(2,6)`, Rupert form, at an exact corner**: with the rim `(0, 2, 3, h)` certified
up to its depth pattern, `b3 ≥ 1` and `a_h ≥ 1`, the point set is Rupert. -/
theorem isRupert_l7_t26 {x : Fin 7 → ℝ³} (T : Type24 x) (hE : ExactCorner x)
    (h3 : 0 < omega3 x) {h : Fin 7} (hh : h ∈ ({3, 4, 5} : Finset (Fin 7)))
    (hb3 : 1 ≤ oblX2 x 3) (hah : 1 ≤ oblX0 x h)
    (hT : QuadTest' (univ.image x) (viewT26 x) (x 0) (x 2) (x 3) (x h)) :
    IsRupert (univ.image x) :=
  hT.isRupert (T.l7_t26 hE h3 hh hb3 hah)

/-- **L7 for `T′(6,2)`, Rupert form, at an exact corner** (rim `(0, 6, 3, h)`). -/
theorem isRupert_l7_t62 {x : Fin 7 → ℝ³} (T : Type24 x) (hE : ExactCorner x)
    (h3 : 0 < omega3 x) {h : Fin 7} (hh : h ∈ ({3, 4, 5} : Finset (Fin 7)))
    (hc3 : 1 ≤ oblX6 x 3) (hah : 1 ≤ oblX0 x h)
    (hT : QuadTest' (univ.image x) (viewT62 x) (x 0) (x 6) (x 3) (x h)) :
    IsRupert (univ.image x) :=
  hT.isRupert (T.l7_t62 hE h3 hh hc3 hah)

/-- **L7 for `T′(0,6)`, Rupert form, at an exact corner** (rim `(2, 0, 4, h)`). -/
theorem isRupert_l7_t06 {x : Fin 7 → ℝ³} (T : Type24 x) (hE : ExactCorner x)
    (h4 : 0 < omega4 x) {h : Fin 7} (hh : h ∈ ({3, 4, 5} : Finset (Fin 7)))
    (ha4 : 1 ≤ oblX0 x 4) (hbh : 1 ≤ oblX2 x h)
    (hT : QuadTest' (univ.image x) (viewT06 x) (x 2) (x 0) (x 4) (x h)) :
    IsRupert (univ.image x) :=
  hT.isRupert (T.l7_t06 hE h4 hh ha4 hbh)

/-- **L7 for `T′(2,6)`, Rupert form, off the corner (17.8′).** -/
theorem isRupert_l7_t26_radius {x : Fin 7 → ℝ³} (T : Type24 x) {h : Fin 7} {δ : ℝ}
    (hab : |⟪x 2 - x 1, x 0 - x 1⟫| ≤ δ * (‖x 2 - x 1‖ * ‖x 0 - x 1‖))
    (hbc : |⟪x 2 - x 1, x 6 - x 1⟫| ≤ δ * (‖x 2 - x 1‖ * ‖x 6 - x 1‖))
    (hac : |⟪x 0 - x 1, x 6 - x 1⟫| ≤ δ * (‖x 0 - x 1‖ * ‖x 6 - x 1‖))
    (hδh : δ * (|omega3 x * (oblX0 x h - 1) + oblX2 x h| * (‖x 2 - x 1‖ * ‖x 0 - x 1‖) +
      |omega3 x * oblX6 x h| * (‖x 2 - x 1‖ * ‖x 6 - x 1‖) +
      |oblX6 x h| * (‖x 0 - x 1‖ * ‖x 6 - x 1‖)) <
        omega3 x * oblX2 x h * ‖x 2 - x 1‖ ^ 2 + (oblX0 x h - 1) * ‖x 0 - x 1‖ ^ 2)
    (hδg : δ * (|omega3 x * oblX0 x 3 + oblX2 x 3 - 1| * (‖x 2 - x 1‖ * ‖x 0 - x 1‖) +
      |omega3 x * oblX6 x 3| * (‖x 2 - x 1‖ * ‖x 6 - x 1‖) +
      |oblX6 x 3| * (‖x 0 - x 1‖ * ‖x 6 - x 1‖)) <
        omega3 x * (oblX2 x 3 - 1) * ‖x 2 - x 1‖ ^ 2 + oblX0 x 3 * ‖x 0 - x 1‖ ^ 2)
    (hT : QuadTest' (univ.image x) (viewT26 x) (x 0) (x 2) (x 3) (x h)) :
    IsRupert (univ.image x) :=
  hT.isRupert (T.l7_t26_radius hab hbc hac hδh hδg)

/-! ### The arc criterion 17.16′ on circle 2 -/

/-- **The pair rule as a Cramer certificate (17.16′).**  If `τ1` fails only where
`ℓ1 = g_a A1 + t1 g_b B1 ≥ 0` with `B1 < 0` and `τ2` only where `ℓ2 = g_a A2 + t2 g_b B2 ≥ 0`
with `B2 > 0`, then `t2 B2 ℓ1 + t1 (−B1) ℓ2 = g_a (t2 B2 A1 − t1 B1 A2)`, so they do not both
fail when `ν1 / t1 < ν2 / t2` (`ν_i = −A_i / B_i`; multiplied out: `t2 B2 A1 < t1 B1 A2`). -/
theorem pair_rule {ga gb t1 t2 A1 B1 A2 B2 : ℝ} (hga : 0 < ga) (ht1 : 0 < t1) (ht2 : 0 < t2)
    (hB1 : B1 < 0) (hB2 : 0 < B2) (hcov : t2 * B2 * A1 < t1 * B1 * A2) :
    ¬ (0 ≤ ga * A1 + t1 * gb * B1 ∧ 0 ≤ ga * A2 + t2 * gb * B2) := by
  rintro ⟨h1, h2⟩
  have e : t2 * B2 * (ga * A1 + t1 * gb * B1) + t1 * (-B1) * (ga * A2 + t2 * gb * B2) =
      ga * (t2 * B2 * A1 - t1 * B1 * A2) := by ring
  have k1 := mul_nonneg (mul_pos ht2 hB2).le h1
  have k2 := mul_nonneg (mul_pos ht1 (neg_pos.mpr hB1)).le h2
  nlinarith [mul_pos hga (sub_pos.mpr hcov)]

namespace Type24

variable {x : Fin 7 → ℝ³} (T : Type24 x)
include T

/-- The ratio of 17.14 (a) at the view `α e_a + β e_b`: `ν = β g_b / (α g_a) = (β / α) κ`. -/
theorem nu_eq {α β : ℝ} (hα : 0 < α) :
    β * ⟪x 2 - x 1, x 2 - x 1⟫ / (α * ⟪x 0 - x 1, x 0 - x 1⟫) =
      β / α * (⟪x 2 - x 1, x 2 - x 1⟫ / ⟪x 0 - x 1, x 0 - x 1⟫) := by
  have ga := T.ga_pos
  field_simp

/-- **The arc criterion 17.16′ on circle 2 ("if"), at an exact corner.**  Items `j ∈ I` are
tests at the views `α_j e_a + β_j e_b` (`α_j > 0`, so `t_j = β_j / α_j`) with rim diagonals
`{d₀ j, d₁ j}`, `{e₀ j, e₁ j}`.  If for every `κ > 0` some item's rim does not fail in the pencil
at `ν = t_j κ` (`∩ Φ_τ = ∅`), then some item does not fail. -/
theorem arc_criterion2 (hE : ExactCorner x) {ι : Type*} (I : Finset ι) (α β : ι → ℝ)
    (hα : ∀ j ∈ I, 0 < α j) (d₀ d₁ e₀ e₁ : ι → Fin 7)
    (hcov : ∀ κ, 0 < κ → ∃ j ∈ I, ¬ PencilFails x (β j / α j * κ) (d₀ j) (d₁ j) (e₀ j) (e₁ j)) :
    ∃ j ∈ I, ¬ Fails4 (x (d₀ j)) (x (d₁ j)) (x (e₀ j)) (x (e₁ j))
      (α j • (x 0 - x 1) + β j • (x 2 - x 1)) := by
  obtain ⟨j, hj, hn⟩ := hcov _ (div_pos T.gb_pos T.ga_pos)
  refine ⟨j, hj, ?_⟩
  rw [T.fails4_circle2_iff hE (hα j hj), T.nu_eq (hα j hj)]
  exact hn

/-- **WP_2's chain in the pencil**: `ζ_ν(6) < ζ_ν(4) < ζ_ν(0) < ζ_ν(2)`. -/
def WPPencil (x : Fin 7 → ℝ³) (ν : ℝ) : Prop :=
  pencil2 x ν 6 < pencil2 x ν 4 ∧ pencil2 x ν 4 < pencil2 x ν 0 ∧ pencil2 x ν 0 < pencil2 x ν 2

/-- **17.14 (d) for WP_2**: at an exact corner, WP_2's chain at the arc view `t` depends on
`ν = t κ` only. -/
theorem wpChain2_iff_pencil (hE : ExactCorner x) (t : ℝ) :
    WPChain2 x t ↔ WPPencil x (t * (⟪x 2 - x 1, x 2 - x 1⟫ / ⟪x 0 - x 1, x 0 - x 1⟫)) := by
  have ga := T.ga_pos
  have hp : ∀ v : Fin 7, ⟪x v, (x 0 - x 1) + t • (x 2 - x 1)⟫ =
      ⟪x 1, (x 0 - x 1) + t • (x 2 - x 1)⟫ + ⟪x 0 - x 1, x 0 - x 1⟫ *
        pencil2 x (t * (⟪x 2 - x 1, x 2 - x 1⟫ / ⟪x 0 - x 1, x 0 - x 1⟫)) v := by
    intro v
    have hw : (x 0 - x 1) + t • (x 2 - x 1) =
        (1 : ℝ) • (x 0 - x 1) + t • (x 2 - x 1) + (0 : ℝ) • (x 6 - x 1) := by module
    rw [hw, T.depth_corner hE v]
    simp only [pencil2]
    field_simp
    ring
  simp only [WPChain2, WPPencil]
  rw [hp 6, hp 4, hp 0, hp 2]
  simp only [add_lt_add_iff_left, mul_lt_mul_iff_right₀ ga]

/-- **The arc criterion with WP_2 (17.16′).**  As `arc_criterion2`, where for some `κ` WP_2's
pencil chain may hold instead at some `ν = t κ` with `t` in the face interval `(lo, hi)`; then
some item does not fail or WP_2's depth chain holds at an arc view in `(lo, hi)`. -/
theorem arc_criterion2_wp (hE : ExactCorner x) {ι : Type*} (I : Finset ι) (α β : ι → ℝ)
    (hα : ∀ j ∈ I, 0 < α j) (d₀ d₁ e₀ e₁ : ι → Fin 7) {lo hi : ℝ}
    (hcov : ∀ κ, 0 < κ →
      (∃ j ∈ I, ¬ PencilFails x (β j / α j * κ) (d₀ j) (d₁ j) (e₀ j) (e₁ j)) ∨
        ∃ t, lo < t ∧ t < hi ∧ WPPencil x (t * κ)) :
    (∃ j ∈ I, ¬ Fails4 (x (d₀ j)) (x (d₁ j)) (x (e₀ j)) (x (e₁ j))
      (α j • (x 0 - x 1) + β j • (x 2 - x 1))) ∨ ∃ t, lo < t ∧ t < hi ∧ WPChain2 x t := by
  rcases hcov _ (div_pos T.gb_pos T.ga_pos) with ⟨j, hj, hn⟩ | ⟨t, h1, h2, hw⟩
  · refine Or.inl ⟨j, hj, ?_⟩
    rw [T.fails4_circle2_iff hE (hα j hj), T.nu_eq (hα j hj)]
    exact hn
  · exact Or.inr ⟨t, h1, h2, (T.wpChain2_iff_pencil hE t).mpr hw⟩

/-- **The pair form of the arc criterion (17.16′ with the pair rule), at an exact corner.**
Test 1 at the view `α1 e_a + β1 e_b` fails in the pencil only at `ν ≤ m1`, test 2 at
`α2 e_a + β2 e_b` only at `ν ≥ m2` (`α_i, β_i > 0`).  If `m1 / t1 < m2 / t2`
(`t_i = β_i / α_i`; multiplied out), they do not both fail. -/
theorem circle2_pair (hE : ExactCorner x) {α1 β1 α2 β2 m1 m2 : ℝ} (hα1 : 0 < α1)
    (hβ1 : 0 < β1) (hα2 : 0 < α2) (hβ2 : 0 < β2) {d₀ d₁ e₀ e₁ d₀' d₁' e₀' e₁' : Fin 7}
    (hF1 : ∀ ν, 0 < ν → PencilFails x ν d₀ d₁ e₀ e₁ → ν ≤ m1)
    (hF2 : ∀ ν, 0 < ν → PencilFails x ν d₀' d₁' e₀' e₁' → m2 ≤ ν)
    (hcov : m1 * α1 * β2 < m2 * α2 * β1) :
    ¬ (Fails4 (x d₀) (x d₁) (x e₀) (x e₁) (α1 • (x 0 - x 1) + β1 • (x 2 - x 1)) ∧
      Fails4 (x d₀') (x d₁') (x e₀') (x e₁') (α2 • (x 0 - x 1) + β2 • (x 2 - x 1))) := by
  rintro ⟨h1, h2⟩
  rw [T.fails4_circle2_iff hE hα1, T.nu_eq hα1] at h1
  rw [T.fails4_circle2_iff hE hα2, T.nu_eq hα2] at h2
  set κ := ⟪x 2 - x 1, x 2 - x 1⟫ / ⟪x 0 - x 1, x 0 - x 1⟫
  have hκ : 0 < κ := div_pos T.gb_pos T.ga_pos
  have k1 := hF1 _ (by positivity) h1
  have k2 := hF2 _ (by positivity) h2
  rw [div_mul_eq_mul_div, div_le_iff₀ hα1] at k1
  rw [div_mul_eq_mul_div, le_div_iff₀ hα2] at k2
  nlinarith [mul_le_mul_of_nonneg_right k1 hβ2.le, mul_le_mul_of_nonneg_right k2 hβ1.le]

end Type24

/-- **The arc criterion on circle 2, Rupert form.**  Every item certified up to its depth
pattern (`QuadTest'` with the rim `(d₀, e₀, d₁, e₁)`) and `∩ Φ_τ = ∅` make `K` Rupert. -/
theorem isRupert_arc_criterion2 {x : Fin 7 → ℝ³} (T : Type24 x) (hE : ExactCorner x)
    {ι : Type*} (I : Finset ι) (α β : ι → ℝ) (hα : ∀ j ∈ I, 0 < α j) (d₀ d₁ e₀ e₁ : ι → Fin 7)
    (hcov : ∀ κ, 0 < κ → ∃ j ∈ I, ¬ Type24.PencilFails x (β j / α j * κ) (d₀ j) (d₁ j) (e₀ j) (e₁ j))
    (hQ : ∀ j ∈ I, QuadTest' (univ.image x) (α j • (x 0 - x 1) + β j • (x 2 - x 1))
      (x (d₀ j)) (x (e₀ j)) (x (d₁ j)) (x (e₁ j))) :
    IsRupert (univ.image x) := by
  obtain ⟨j, hj, hn⟩ := T.arc_criterion2 hE I α β hα d₀ d₁ e₀ e₁ hcov
  exact (hQ j hj).isRupert hn

/-- **The pair form on circle 2, Rupert form.** -/
theorem isRupert_circle2_pair {x : Fin 7 → ℝ³} (T : Type24 x) (hE : ExactCorner x)
    {α1 β1 α2 β2 m1 m2 : ℝ} (hα1 : 0 < α1) (hβ1 : 0 < β1) (hα2 : 0 < α2) (hβ2 : 0 < β2)
    {d₀ d₁ e₀ e₁ d₀' d₁' e₀' e₁' : Fin 7}
    (hF1 : ∀ ν, 0 < ν → Type24.PencilFails x ν d₀ d₁ e₀ e₁ → ν ≤ m1)
    (hF2 : ∀ ν, 0 < ν → Type24.PencilFails x ν d₀' d₁' e₀' e₁' → m2 ≤ ν)
    (hcov : m1 * α1 * β2 < m2 * α2 * β1)
    (hQ1 : QuadTest' (univ.image x) (α1 • (x 0 - x 1) + β1 • (x 2 - x 1)) (x d₀) (x e₀) (x d₁)
      (x e₁))
    (hQ2 : QuadTest' (univ.image x) (α2 • (x 0 - x 1) + β2 • (x 2 - x 1)) (x d₀') (x e₀')
      (x d₁') (x e₁')) :
    IsRupert (univ.image x) :=
  isRupert_of_two_tests hQ1 hQ2 (T.circle2_pair hE hα1 hβ1 hα2 hβ2 hF1 hF2 hcov)

/-! ### Radii: 17.1, 17.1′ and WP's radius (17.11) -/

/-- **Lemma 17.1 (exactness)**: in a frame `e_a, e_b, e_c` the depth difference
`⟪Δ, d⟫ = Σ d_i Δ_i g_i + Σ_{i<j} (d_i Δ_j + d_j Δ_i) h_ij` is exactly linear in the axis inner
products `h_ij`. -/
theorem inner_frame_diff (ea eb ec : ℝ³) (Da Db Dc da db dc : ℝ) :
    ⟪Da • ea + Db • eb + Dc • ec, da • ea + db • eb + dc • ec⟫ =
      da * Da * ⟪ea, ea⟫ + db * Db * ⟪eb, eb⟫ + dc * Dc * ⟪ec, ec⟫ +
        (da * Db + db * Da) * ⟪ea, eb⟫ + (da * Dc + dc * Da) * ⟪ea, ec⟫ +
        (db * Dc + dc * Db) * ⟪eb, ec⟫ := by
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    real_inner_comm ea eb, real_inner_comm ea ec, real_inner_comm eb ec]
  ring

/-- **The octant radius of 17.1′**: on `h_ij ≤ 0` with `|h_ij| ≤ δ ρ_ij`, the form
`ℓ⁰ + Σ β_ij h_ij` is positive when `δ Σ max (0, β_ij) ρ_ij < ℓ⁰`. -/
theorem radius_pos_octant {l0 b1 b2 b3 h1 h2 h3 r1 r2 r3 δ : ℝ} (hn1 : h1 ≤ 0) (hn2 : h2 ≤ 0)
    (hn3 : h3 ≤ 0) (hh1 : -h1 ≤ δ * r1) (hh2 : -h2 ≤ δ * r2) (hh3 : -h3 ≤ δ * r3)
    (hδ : δ * (max 0 b1 * r1 + max 0 b2 * r2 + max 0 b3 * r3) < l0) :
    0 < l0 + b1 * h1 + b2 * h2 + b3 * h3 := by
  have k : ∀ b h r : ℝ, h ≤ 0 → -h ≤ δ * r → -(max 0 b * (δ * r)) ≤ b * h := by
    intro b h r hn hh
    have m1 : b * h ≥ max 0 b * h := by
      rcases le_total 0 b with hb | hb
      · rw [max_eq_right hb]
      · rw [max_eq_left hb]; nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hh (le_max_left 0 b)]
  nlinarith [k b1 h1 r1 hn1 hh1, k b2 h2 r2 hn2 hh2, k b3 h3 r3 hn3 hh3]

namespace Type24

variable {x : Fin 7 → ℝ³} (T : Type24 x)
include T

theorem diff_frame (v w : Fin 7) : x v - x w =
    (oblX0 x v - oblX0 x w) • (x 0 - x 1) + (oblX2 x v - oblX2 x w) • (x 2 - x 1) +
      (oblX6 x v - oblX6 x w) • (x 6 - x 1) := by
  conv_lhs => rw [T.rep v, T.rep w]
  module

/-- **WP_2's three forms (17.11)** at the arc view `t`, at every metric (`h_ij = ⟪e_i, e_j⟫`):
`z_v − z_w = (a_v − a_w) g_a + t (b_v − b_w) g_b + ((b_v − b_w) + t (a_v − a_w)) h_ab
+ (c_v − c_w) (h_ac + t h_bc)`. -/
theorem wp_form (v w : Fin 7) (t : ℝ) :
    ⟪x v, (x 0 - x 1) + t • (x 2 - x 1)⟫ - ⟪x w, (x 0 - x 1) + t • (x 2 - x 1)⟫ =
      (oblX0 x v - oblX0 x w) * ‖x 0 - x 1‖ ^ 2 + t * (oblX2 x v - oblX2 x w) * ‖x 2 - x 1‖ ^ 2 +
        ((oblX2 x v - oblX2 x w) + t * (oblX0 x v - oblX0 x w)) * ⟪x 0 - x 1, x 2 - x 1⟫ +
        (oblX6 x v - oblX6 x w) * ⟪x 0 - x 1, x 6 - x 1⟫ +
        (t * (oblX6 x v - oblX6 x w)) * ⟪x 2 - x 1, x 6 - x 1⟫ := by
  rw [← inner_sub_left, T.diff_frame v w]
  have hw : (x 0 - x 1) + t • (x 2 - x 1) =
      (1 : ℝ) • (x 0 - x 1) + t • (x 2 - x 1) + (0 : ℝ) • (x 6 - x 1) := by module
  rw [hw, inner_frame_diff, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
  ring

/-- **WP_2 near the corner (17.1′ for WP's three forms).**  If the three cosines at `1` are at
most `δ` (`|h_ij| ≤ δ L_i L_j`) and `δ ‖β_k‖ < ℓ⁰_k` for WP's forms `z4 − z6`, `z0 − z4`,
`z2 − z0` at the view `t` (multiplied out), WP_2's depth chain holds there. -/
theorem wpChain2_radius {t δ : ℝ}
    (hab : |⟪x 0 - x 1, x 2 - x 1⟫| ≤ δ * (‖x 0 - x 1‖ * ‖x 2 - x 1‖))
    (hac : |⟪x 0 - x 1, x 6 - x 1⟫| ≤ δ * (‖x 0 - x 1‖ * ‖x 6 - x 1‖))
    (hbc : |⟪x 2 - x 1, x 6 - x 1⟫| ≤ δ * (‖x 2 - x 1‖ * ‖x 6 - x 1‖))
    (r1 : δ * (|oblX2 x 4 + t * oblX0 x 4| * (‖x 0 - x 1‖ * ‖x 2 - x 1‖) +
      |oblX6 x 4 - 1| * (‖x 0 - x 1‖ * ‖x 6 - x 1‖) +
      |t * (oblX6 x 4 - 1)| * (‖x 2 - x 1‖ * ‖x 6 - x 1‖)) <
        oblX0 x 4 * ‖x 0 - x 1‖ ^ 2 + t * oblX2 x 4 * ‖x 2 - x 1‖ ^ 2)
    (r2 : δ * (|t * (1 - oblX0 x 4) - oblX2 x 4| * (‖x 0 - x 1‖ * ‖x 2 - x 1‖) +
      |oblX6 x 4| * (‖x 0 - x 1‖ * ‖x 6 - x 1‖) +
      |t * oblX6 x 4| * (‖x 2 - x 1‖ * ‖x 6 - x 1‖)) <
        (1 - oblX0 x 4) * ‖x 0 - x 1‖ ^ 2 - t * oblX2 x 4 * ‖x 2 - x 1‖ ^ 2)
    (r3 : δ * (|1 - t| * (‖x 0 - x 1‖ * ‖x 2 - x 1‖)) <
        t * ‖x 2 - x 1‖ ^ 2 - ‖x 0 - x 1‖ ^ 2) :
    WPChain2 x t := by
  have a0 := T.oblX0_zero'; have b0 := Type24.oblX2_zero' (x := x)
  have c0' := Type24.oblX6_zero (x := x)
  have a2 := Type24.oblX0_two (x := x); have b2 := T.oblX2_two
  have c2 := Type24.oblX6_two (x := x)
  have a6 := Type24.oblX0_six (x := x); have b6 := Type24.oblX2_six (x := x)
  have c6 := T.oblX6_six
  refine ⟨?_, ?_, ?_⟩
  · have e := T.wp_form 4 6 t
    rw [a6, b6, c6] at e
    have := radius_pos (b1 := oblX2 x 4 - 0 + t * (oblX0 x 4 - 0)) (b2 := oblX6 x 4 - 1)
      (b3 := t * (oblX6 x 4 - 1)) hab hac hbc
      (l0 := (oblX0 x 4 - 0) * ‖x 0 - x 1‖ ^ 2 + t * (oblX2 x 4 - 0) * ‖x 2 - x 1‖ ^ 2)
      (by simpa only [sub_zero] using r1)
    linarith
  · have e := T.wp_form 0 4 t
    rw [a0, b0, c0'] at e
    have := radius_pos (b1 := 0 - oblX2 x 4 + t * (1 - oblX0 x 4)) (b2 := 0 - oblX6 x 4)
      (b3 := t * (0 - oblX6 x 4)) hab hac hbc
      (l0 := (1 - oblX0 x 4) * ‖x 0 - x 1‖ ^ 2 + t * (0 - oblX2 x 4) * ‖x 2 - x 1‖ ^ 2)
      (by
        have e1 : |0 - oblX2 x 4 + t * (1 - oblX0 x 4)| = |t * (1 - oblX0 x 4) - oblX2 x 4| := by
          ring_nf
        have e2 : |0 - oblX6 x 4| = |oblX6 x 4| := by rw [zero_sub, abs_neg]
        have e3 : |t * (0 - oblX6 x 4)| = |t * oblX6 x 4| := by
          rw [zero_sub, mul_neg, abs_neg]
        rw [e1, e3, e2]; linarith)
    linarith
  · have e := T.wp_form 2 0 t
    rw [a0, b0, c0', a2, b2, c2] at e
    have := radius_pos (b1 := 1 - 0 + t * (0 - 1)) (b2 := 0 - 0) (b3 := t * (0 - 0)) hab hac hbc
      (l0 := (0 - 1) * ‖x 0 - x 1‖ ^ 2 + t * (1 - 0) * ‖x 2 - x 1‖ ^ 2)
      (by
        have e1 : |1 - 0 + t * (0 - 1)| = |1 - t| := by ring_nf
        rw [e1]; simp only [sub_self, mul_zero, abs_zero, zero_mul, add_zero]; linarith)
    linarith

end Type24

/-- **WP_2 as a Rupert item near the corner (17.1′, 17.11).** -/
theorem isRupert_wp2_radius {x : Fin 7 → ℝ³} (T : Type24 x) {t δ : ℝ} (ht : 0 < t)
    (hab : |⟪x 0 - x 1, x 2 - x 1⟫| ≤ δ * (‖x 0 - x 1‖ * ‖x 2 - x 1‖))
    (hac : |⟪x 0 - x 1, x 6 - x 1⟫| ≤ δ * (‖x 0 - x 1‖ * ‖x 6 - x 1‖))
    (hbc : |⟪x 2 - x 1, x 6 - x 1⟫| ≤ δ * (‖x 2 - x 1‖ * ‖x 6 - x 1‖))
    (r1 : δ * (|oblX2 x 4 + t * oblX0 x 4| * (‖x 0 - x 1‖ * ‖x 2 - x 1‖) +
      |oblX6 x 4 - 1| * (‖x 0 - x 1‖ * ‖x 6 - x 1‖) +
      |t * (oblX6 x 4 - 1)| * (‖x 2 - x 1‖ * ‖x 6 - x 1‖)) <
        oblX0 x 4 * ‖x 0 - x 1‖ ^ 2 + t * oblX2 x 4 * ‖x 2 - x 1‖ ^ 2)
    (r2 : δ * (|t * (1 - oblX0 x 4) - oblX2 x 4| * (‖x 0 - x 1‖ * ‖x 2 - x 1‖) +
      |oblX6 x 4| * (‖x 0 - x 1‖ * ‖x 6 - x 1‖) +
      |t * oblX6 x 4| * (‖x 2 - x 1‖ * ‖x 6 - x 1‖)) <
        (1 - oblX0 x 4) * ‖x 0 - x 1‖ ^ 2 - t * oblX2 x 4 * ‖x 2 - x 1‖ ^ 2)
    (r3 : δ * (|1 - t| * (‖x 0 - x 1‖ * ‖x 2 - x 1‖)) <
        t * ‖x 2 - x 1‖ ^ 2 - ‖x 0 - x 1‖ ^ 2)
    (hI : WPItem x 2 6 4 5 t) : IsRupert (univ.image x) :=
  isRupert_wp2 T ht hI (T.wpChain2_radius hab hac hbc r1 r2 r3)

namespace Type24

variable {x : Fin 7 → ℝ³} (T : Type24 x)
include T

/-- **Lemma 17.11 (WP on the obtuse octant).**  If the three inner products at `1` are `≤ 0`, the
cosines at most `δ`, and `δ` is below `r₋(t)` of 17.11 (multiplied out, with positive parts
`max 0 β`), WP_2's depth chain holds at the arc view `t`. -/
theorem wpChain2_octant {t δ : ℝ}
    (nab : ⟪x 0 - x 1, x 2 - x 1⟫ ≤ 0) (nac : ⟪x 0 - x 1, x 6 - x 1⟫ ≤ 0)
    (nbc : ⟪x 2 - x 1, x 6 - x 1⟫ ≤ 0)
    (hab : -⟪x 0 - x 1, x 2 - x 1⟫ ≤ δ * (‖x 0 - x 1‖ * ‖x 2 - x 1‖))
    (hac : -⟪x 0 - x 1, x 6 - x 1⟫ ≤ δ * (‖x 0 - x 1‖ * ‖x 6 - x 1‖))
    (hbc : -⟪x 2 - x 1, x 6 - x 1⟫ ≤ δ * (‖x 2 - x 1‖ * ‖x 6 - x 1‖))
    (r1 : δ * (max 0 (oblX2 x 4 + t * oblX0 x 4) * (‖x 0 - x 1‖ * ‖x 2 - x 1‖) +
      max 0 (oblX6 x 4 - 1) * (‖x 0 - x 1‖ * ‖x 6 - x 1‖) +
      max 0 (t * (oblX6 x 4 - 1)) * (‖x 2 - x 1‖ * ‖x 6 - x 1‖)) <
        oblX0 x 4 * ‖x 0 - x 1‖ ^ 2 + t * oblX2 x 4 * ‖x 2 - x 1‖ ^ 2)
    (r2 : δ * (max 0 (t * (1 - oblX0 x 4) - oblX2 x 4) * (‖x 0 - x 1‖ * ‖x 2 - x 1‖) +
      max 0 (-oblX6 x 4) * (‖x 0 - x 1‖ * ‖x 6 - x 1‖) +
      max 0 (-(t * oblX6 x 4)) * (‖x 2 - x 1‖ * ‖x 6 - x 1‖)) <
        (1 - oblX0 x 4) * ‖x 0 - x 1‖ ^ 2 - t * oblX2 x 4 * ‖x 2 - x 1‖ ^ 2)
    (r3 : δ * (max 0 (1 - t) * (‖x 0 - x 1‖ * ‖x 2 - x 1‖)) <
        t * ‖x 2 - x 1‖ ^ 2 - ‖x 0 - x 1‖ ^ 2) :
    WPChain2 x t := by
  have a0 := T.oblX0_zero'; have b0 := Type24.oblX2_zero' (x := x)
  have c0' := Type24.oblX6_zero (x := x)
  have a2 := Type24.oblX0_two (x := x); have b2 := T.oblX2_two
  have c2 := Type24.oblX6_two (x := x)
  have a6 := Type24.oblX0_six (x := x); have b6 := Type24.oblX2_six (x := x)
  have c6 := T.oblX6_six
  refine ⟨?_, ?_, ?_⟩
  · have e := T.wp_form 4 6 t
    rw [a6, b6, c6] at e
    have := radius_pos_octant (b1 := oblX2 x 4 - 0 + t * (oblX0 x 4 - 0))
      (b2 := oblX6 x 4 - 1) (b3 := t * (oblX6 x 4 - 1)) nab nac nbc hab hac hbc
      (l0 := (oblX0 x 4 - 0) * ‖x 0 - x 1‖ ^ 2 + t * (oblX2 x 4 - 0) * ‖x 2 - x 1‖ ^ 2)
      (by simpa only [sub_zero] using r1)
    linarith
  · have e := T.wp_form 0 4 t
    rw [a0, b0, c0'] at e
    have := radius_pos_octant (b1 := 0 - oblX2 x 4 + t * (1 - oblX0 x 4))
      (b2 := 0 - oblX6 x 4) (b3 := t * (0 - oblX6 x 4)) nab nac nbc hab hac hbc
      (l0 := (1 - oblX0 x 4) * ‖x 0 - x 1‖ ^ 2 + t * (0 - oblX2 x 4) * ‖x 2 - x 1‖ ^ 2)
      (by
        have e1 : 0 - oblX2 x 4 + t * (1 - oblX0 x 4) = t * (1 - oblX0 x 4) - oblX2 x 4 := by
          ring
        have e2 : (0 : ℝ) - oblX6 x 4 = -oblX6 x 4 := by ring
        have e3 : t * (0 - oblX6 x 4) = -(t * oblX6 x 4) := by ring
        rw [e1, e3, e2]; linarith)
    linarith
  · have e := T.wp_form 2 0 t
    rw [a0, b0, c0', a2, b2, c2] at e
    have := radius_pos_octant (b1 := 1 - 0 + t * (0 - 1)) (b2 := 0 - 0) (b3 := t * (0 - 0))
      nab nac nbc hab hac hbc
      (l0 := (0 - 1) * ‖x 0 - x 1‖ ^ 2 + t * (1 - 0) * ‖x 2 - x 1‖ ^ 2)
      (by
        have e1 : 1 - 0 + t * (0 - 1) = 1 - t := by ring
        rw [e1]; simp only [sub_self, mul_zero, max_self, zero_mul, add_zero]; linarith)
    linarith

end Type24

/-- **Theorem 17.12 with WP_2 as the item (the obtuse octant by WP, the rest by Lemma C).**  Let
the three cosines at `1` be below `δ` (`|c|∞ < δ`), with the rims of both cap-edge crossings
given by `CapRim` at `δ` (`δ ≤ δ_cap`), and let `δ` be below WP_2's octant radius `r₋(t)`
(17.11) at an arc view `t > 0` where WP_2 is certified up to its depth chain.  Then `K` is
Rupert: if all three inner products at `1` are `≤ 0`, WP_2 holds (17.11); otherwise `E_2` or
`E_6` is good (17.10). -/
theorem isRupert_type24_near_wp2 {x : Fin 7 → ℝ³} (T : Type24 x) {δ t : ℝ} (ht : 0 < t)
    {k₂ k₆ : ℕ} [NeZero k₂] [NeZero k₆] {r₂ : ZMod k₂ → Fin 7} {r₆ : ZMod k₆ → Fin 7}
    (h₂ : CapRim x 2 0 6 (oblX2 x) (oblX0 x) (oblX6 x) δ k₂ r₂)
    (h₆ : CapRim x 6 2 0 (oblX6 x) (oblX2 x) (oblX0 x) δ k₆ r₆)
    (hcab : |⟪x 0 - x 1, x 2 - x 1⟫| < δ * (‖x 0 - x 1‖ * ‖x 2 - x 1‖))
    (hcac : |⟪x 0 - x 1, x 6 - x 1⟫| < δ * (‖x 0 - x 1‖ * ‖x 6 - x 1‖))
    (hcbc : |⟪x 2 - x 1, x 6 - x 1⟫| < δ * (‖x 2 - x 1‖ * ‖x 6 - x 1‖))
    (r1 : δ * (max 0 (oblX2 x 4 + t * oblX0 x 4) * (‖x 0 - x 1‖ * ‖x 2 - x 1‖) +
      max 0 (oblX6 x 4 - 1) * (‖x 0 - x 1‖ * ‖x 6 - x 1‖) +
      max 0 (t * (oblX6 x 4 - 1)) * (‖x 2 - x 1‖ * ‖x 6 - x 1‖)) <
        oblX0 x 4 * ‖x 0 - x 1‖ ^ 2 + t * oblX2 x 4 * ‖x 2 - x 1‖ ^ 2)
    (r2 : δ * (max 0 (t * (1 - oblX0 x 4) - oblX2 x 4) * (‖x 0 - x 1‖ * ‖x 2 - x 1‖) +
      max 0 (-oblX6 x 4) * (‖x 0 - x 1‖ * ‖x 6 - x 1‖) +
      max 0 (-(t * oblX6 x 4)) * (‖x 2 - x 1‖ * ‖x 6 - x 1‖)) <
        (1 - oblX0 x 4) * ‖x 0 - x 1‖ ^ 2 - t * oblX2 x 4 * ‖x 2 - x 1‖ ^ 2)
    (r3 : δ * (max 0 (1 - t) * (‖x 0 - x 1‖ * ‖x 2 - x 1‖)) <
        t * ‖x 2 - x 1‖ ^ 2 - ‖x 0 - x 1‖ ^ 2)
    (hI : WPItem x 2 6 4 5 t) : IsRupert (univ.image x) := by
  by_cases hobt : ⟪x 0 - x 1, x 2 - x 1⟫ ≤ 0 ∧ ⟪x 0 - x 1, x 6 - x 1⟫ ≤ 0 ∧
      ⟪x 2 - x 1, x 6 - x 1⟫ ≤ 0
  · obtain ⟨nab, nac, nbc⟩ := hobt
    have k : ∀ {h r : ℝ}, |h| < δ * r → -h ≤ δ * r := fun hh => (neg_le_abs _).trans hh.le
    exact isRupert_wp2 T ht hI
      (T.wpChain2_octant nab nac nbc (k hcab) (k hcac) (k hcbc) r1 r2 r3)
  · exact isRupert_type24_capEdge T h₂ h₆ hcab hcac hcbc hobt

end Minimality

end
