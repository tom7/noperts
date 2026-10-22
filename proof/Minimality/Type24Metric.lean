module

public import Minimality.Type24WP

@[expose] public section

/-!
# Type 24 at every metric: depth covectors and the cap-edge crossings (§20.1, 20.2, 20.6, 20.8)

`FEWER-FACES-PROOFS.md` §20 (refereed 2026-10-22).  The depth at a view `d` is `⟪·, d⟫` (`K`'s
own metric); in oblique coordinates at `1` it is `z(v) = z(1) + u · X(v)`, with the **depth
covector** `u = G d = (⟪e_a, d⟫, ⟪e_b, d⟫, ⟪e_c, d⟫)`.

* **Proposition 20.1 (a)** (`fails4_iff_covFails`): a 4-corner test fails at a view `d` iff its
  rim fails for the covector depths `covDepth` at `u = G d` (`CovFails`, X-only).
* **Lemma 20.2 (b), the dip mechanism** (`isCyclicUnimodal_of_noDip`): a cycle whose corner `0`
  is below a neighbour and whose path `1, …, k − 1` has no interior strict local minimum (no
  *dip*) is cyclically unimodal.  Rupert form for a cap-edge crossing, at `K`'s own metric
  with no radius (`isRupert_capEdge_noDip`; the rim data `CapRim0`, i.e. `CapRim` without the
  radius `δ` and the step conditions).  This strengthens `isRupert_capEdge_frame`.
* **Lemma 20.2 (c)** (`mid3_not_dip`): with `3` in the plane of `0, 4, 5` opposite `0`, and
  `z0 < min (z4, z5)`, the corner `3` is not a weak local minimum; for a rim with three far
  corners only `4` and `5` can then dip (`isRupert_capEdge_mid3`).
* **Acute-safety and Lemma 20.2 (a)** (`AcuteSafe`, `acuteSafe_four`): a cap edge is
  *acute-safe* if, for every column `(g_x, h_xy, h_xw)` with `g_x > 0` and `h_xy > 0` or
  `h_xw > 0`, its rim depths `g_x X_x + h_xy X_y + h_xw X_w` are cyclically unimodal (when
  distinct).  This is an X-only property.  A cap edge with a single far corner `r`
  (`X_y(r) + X_w(r) > 1`, from the rim, `capRim_far_sum`) is acute-safe.
  `isRupert_capEdge_acuteSafe` is the Rupert form at `K`'s own metric.
* **Type 24** (`Type24.SafeE2`, `SafeE6`, `SafeE0`: a cap-edge rim with an acute-safe far path;
  `Type24.safeE2_of_four` and relatives: a single far corner suffices; `isRupert_type24_safeE2`
  and relatives).  **Theorem 20.8** (`isRupert_type24_two_safe`): with two acute-safe cap edges,
  a type-24 point set with some face angle at `1` acute is Rupert, at every metric (no
  neighbourhood of the corner); so a non-Rupert one has all three angles at `1` right or obtuse
  (`Type24.obtuse_of_two_safe`, Conjecture A for these classes).
* **Lemma 20.6** (`Type24.s0_e05_corner`, Rupert form `isRupert_s0_e05_corner`): at an exact
  corner in `C̄`, `S_0 = 025/046` with the rim `(0, 2, 3, 6)` and the edge crossing
  `E_05 = 025/0345-0` (view `x 5 − x 0`) with the rim `(2, 5, q, 6)` do not both fail, under
  (i), (ii).

`E_05`'s mirror `E_04` is `Type24.s0_e04_corner`, `isRupert_s0_e04_corner`.  Not formalized:
Proposition 20.1 (c), (d) (the general-metric pencil on circle 2), and the
converse half-space statement of 20.1 (every `u` with `u · d > 0` is `G d` for some positive
definite `G`; it shows that the X-only conditions are exact, which soundness does not need), the
LP that decides acute-safety for rims with two or three far corners (`AcuteSafe` is a hypothesis
there), 20.6 near the corner (its Cramer radius) and the class counts.
-/

namespace Minimality

open Finset
open scoped RealInnerProductSpace

/-! ### Proposition 20.1 (a): failure depends on the depth covector only -/

/-- The depth of the label `v` for the covector `u = (ua, ub, uc)`, in oblique coordinates
`(Xa, Xb, Xc)`, up to the depth of the frame origin. -/
def covDepth (Xa Xb Xc : Fin 7 → ℝ) (ua ub uc : ℝ) (v : Fin 7) : ℝ :=
  Xa v * ua + Xb v * ub + Xc v * uc

/-- The closed failure of a 4-corner rim with diagonals `{d₀, d₁}`, `{e₀, e₁}` for the covector
`(ua, ub, uc)` (X-only). -/
def CovFails (Xa Xb Xc : Fin 7 → ℝ) (ua ub uc : ℝ) (d₀ d₁ e₀ e₁ : Fin 7) : Prop :=
  max (covDepth Xa Xb Xc ua ub uc d₀) (covDepth Xa Xb Xc ua ub uc d₁) ≤
      min (covDepth Xa Xb Xc ua ub uc e₀) (covDepth Xa Xb Xc ua ub uc e₁) ∨
    max (covDepth Xa Xb Xc ua ub uc e₀) (covDepth Xa Xb Xc ua ub uc e₁) ≤
      min (covDepth Xa Xb Xc ua ub uc d₀) (covDepth Xa Xb Xc ua ub uc d₁)

/-- The depth in a frame: `⟪x v, w⟫ = ⟪o, w⟫ + u · X(v)`, `u = (⟪e_a, w⟫, ⟪e_b, w⟫, ⟪e_c, w⟫)`. -/
theorem inner_covDepth {x : Fin 7 → ℝ³} {o ea eb ec : ℝ³} {Xa Xb Xc : Fin 7 → ℝ}
    (hrep : ∀ v, x v = o + Xa v • ea + Xb v • eb + Xc v • ec) (w : ℝ³) (v : Fin 7) :
    ⟪x v, w⟫ = ⟪o, w⟫ + covDepth Xa Xb Xc ⟪ea, w⟫ ⟪eb, w⟫ ⟪ec, w⟫ v := by
  rw [hrep v]
  simp only [inner_add_left, real_inner_smul_left, covDepth]
  ring

/-- **Proposition 20.1 (a).**  A 4-corner test fails at the view `w` iff its rim fails for the
covector depths at `u = G w`: failure is X-only given `u`. -/
theorem fails4_iff_covFails {x : Fin 7 → ℝ³} {o ea eb ec : ℝ³} {Xa Xb Xc : Fin 7 → ℝ}
    (hrep : ∀ v, x v = o + Xa v • ea + Xb v • eb + Xc v • ec) (w : ℝ³) (d₀ d₁ e₀ e₁ : Fin 7) :
    Fails4 (x d₀) (x d₁) (x e₀) (x e₁) w ↔
      CovFails Xa Xb Xc ⟪ea, w⟫ ⟪eb, w⟫ ⟪ec, w⟫ d₀ d₁ e₀ e₁ := by
  simp only [Fails4, CovFails, max_le_iff, le_min_iff, inner_covDepth hrep w,
    add_le_add_iff_left]

/-! ### Lemma 20.2 (b): unimodal unless a far corner dips -/

/-- **Lemma 20.2 (b), the dip mechanism.**  A cyclic sequence whose corner `0` is below one of
its neighbours, and whose path `1, …, k − 1` has no interior strict local minimum, is
cyclically unimodal (when its values are distinct).  For a cap-edge crossing (`0` the cap `1`,
the path the far path from `y` to `w`): failure needs a *dip*, a far corner below both of its
rim neighbours. -/
theorem isCyclicUnimodal_of_noDip {k : ℕ} [NeZero k] (hk : 3 ≤ k) {z : ZMod k → ℝ}
    (hinj : Function.Injective z) (h0 : z 0 < z 1 ∨ z 0 < z ((k - 1 : ℕ) : ZMod k))
    (hdip : ∀ n : ℕ, 1 ≤ n → n + 3 ≤ k →
      ¬ (z ((n + 1 : ℕ) : ZMod k) < z (n : ZMod k) ∧
        z ((n + 1 : ℕ) : ZMod k) < z ((n + 2 : ℕ) : ZMod k))) :
    IsCyclicUnimodal z := by
  set a : ℕ → ℝ := fun n => z n with ha
  obtain ⟨q, -, -, hup, hdn⟩ := exists_arch a 1 (k - 1) (by omega)
    (fun n h1 h2 => by
      simp only [ha]
      intro e
      have := hinj e
      rw [Nat.cast_add, Nat.cast_one] at this
      exact zmod_ne_add_one (by omega) _ this)
    (fun n h1 h2 => hdip n h1 (by omega))
  refine isCyclicUnimodal_of_arch hk hinj q (fun n h1 h2 => ?_) (fun n h1 h2 => ?_) h0
  · have := hup n h1 h2
    simp only [ha, Nat.cast_add, Nat.cast_one] at this
    exact this
  · have := hdn n h1 (by omega)
    simp only [ha, Nat.cast_add, Nat.cast_one] at this
    exact this

/-- **Lemma 20.2 (c).**  If `p3 = p0 + s (p4 − p0) + t (p5 − p0)` with `s, t > 0`, `s + t > 1`
(the middle far corner `3` in the plane of `0, 4, 5`, opposite `0`) and `z0 < min (z4, z5)`,
then `3` is not a weak local minimum between `4` and `5`. -/
theorem mid3_not_dip {p0 p3 p4 p5 u : ℝ³} {s t : ℝ}
    (hq : p3 = p0 + s • (p4 - p0) + t • (p5 - p0)) (hs : 0 < s) (ht : 0 < t) (hst : 1 < s + t)
    (h4 : ⟪p0, u⟫ < ⟪p4, u⟫) (h5 : ⟪p0, u⟫ < ⟪p5, u⟫) :
    ¬ (⟪p3, u⟫ ≤ ⟪p4, u⟫ ∧ ⟪p3, u⟫ ≤ ⟪p5, u⟫) := by
  have hz : ⟪p3, u⟫ = ⟪p0, u⟫ + s * (⟪p4, u⟫ - ⟪p0, u⟫) + t * (⟪p5, u⟫ - ⟪p0, u⟫) := by
    rw [hq]; simp only [inner_add_left, real_inner_smul_left, inner_sub_left]
  rintro ⟨c1, c2⟩
  have hA : 0 < ⟪p4, u⟫ - ⟪p0, u⟫ := by linarith
  have hB : 0 < ⟪p5, u⟫ - ⟪p0, u⟫ := by linarith
  have hst' : 0 < s + t - 1 := by linarith
  rcases le_total (⟪p4, u⟫ - ⟪p0, u⟫) (⟪p5, u⟫ - ⟪p0, u⟫) with h | h
  · nlinarith [mul_le_mul_of_nonneg_left h ht.le, mul_pos hst' hA]
  · nlinarith [mul_le_mul_of_nonneg_left h hs.le, mul_pos hst' hB]

/-! ### The rim of a cap-edge crossing, without a radius -/

/-- **The rim of a cap-edge crossing** (17.9), without the radius of Lemma C: the rim of `K_1`
at the view `u = x ax − x 1` is the cycle `x ∘ r` (`r 0 = 1`, the far path `r 1, …, r (k − 1)`
from one of `ay`, `aw` to the other; strictly convex counterclockwise, every other point except
`x ax` strictly inside), with distinct depths and no horizontal double normal. -/
def CapRim0 (x : Fin 7 → ℝ³) (ax ay aw : Fin 7) (k : ℕ) [NeZero k] (r : ZMod k → Fin 7) :
    Prop :=
  3 ≤ k ∧ r 0 = 1 ∧ ((r 1 = ay ∧ r ((k - 1 : ℕ) : ZMod k) = aw) ∨
      (r 1 = aw ∧ r ((k - 1 : ℕ) : ZMod k) = ay)) ∧
    (∀ i j, j ≠ i → j ≠ i + 1 →
      0 < det3 (x (r (i + 1)) - x (r i)) (x (r j) - x (r i)) (x ax - x 1)) ∧
    (∀ v, v ≠ ax → (∀ j, v ≠ r j) → ∀ i,
      0 < det3 (x (r (i + 1)) - x (r i)) (x v - x (r i)) (x ax - x 1)) ∧
    Function.Injective (fun i => ⟪x (r i), x ax - x 1⟫) ∧
    NoHDNAt (univ.image fun i => x (r i)) (x ax - x 1)

/-- **A cap-edge crossing with unimodal rim depths certifies `K`** (Theorem 8.9 with Theorem 7.3;
the axis vertex `x ax` is a double over `1`, Lemma 16.27′). -/
theorem isRupert_capRim0 {x : Fin 7 → ℝ³} (hinj : Function.Injective x) {ax ay aw : Fin 7}
    (hax : ax ≠ 1) {k : ℕ} [NeZero k] {r : ZMod k → Fin 7} (hR : CapRim0 x ax ay aw k r)
    (hz : IsCyclicUnimodal fun i => ⟪x (r i), x ax - x 1⟫) : IsRupert (univ.image x) := by
  classical
  obtain ⟨hk, hr0, -, hcyc, hrest, -, hnd⟩ := hR
  have hu : x ax - x 1 ≠ 0 := sub_ne_zero.mpr (hinj.ne hax)
  refine isRupert_of_edgeView_uniform (univ.image x) ∅ {x ax} (univ.image fun i => x (r i))
    (x ax - x 1) hu hk (fun i => x (r i)) (fun i => mem_image_of_mem x (mem_univ _))
    (fun _ => Finset.notMem_empty _) hcyc ?_ hz hnd (fun i => mem_image_of_mem _ (mem_univ _))
    (fun m hm => absurd hm (Finset.notMem_empty _)) ?_
  · intro v hv _ hvD hvx i
    obtain ⟨w, -, rfl⟩ := mem_image.mp hv
    exact hrest w (fun e => hvD (by rw [e]; exact mem_singleton_self _))
      (fun j e => hvx j (by rw [e])) i
  · intro d hd'
    rw [mem_singleton.mp hd']
    exact ⟨0, -1, by norm_num, by simp only [hr0, neg_one_smul, sub_neg_eq_add]; abel⟩

/-- The cap `1` below one rim neighbour, from an acute angle at `1`. -/
theorem capRim0_h0 {x : Fin 7 → ℝ³} {ax ay aw : Fin 7} {k : ℕ} [NeZero k]
    {r : ZMod k → Fin 7} (hr0 : r 0 = 1)
    (hends : (r 1 = ay ∧ r ((k - 1 : ℕ) : ZMod k) = aw) ∨
      (r 1 = aw ∧ r ((k - 1 : ℕ) : ZMod k) = ay))
    (hsign : 0 < ⟪x ay - x 1, x ax - x 1⟫ ∨ 0 < ⟪x aw - x 1, x ax - x 1⟫) :
    ⟪x (r 0), x ax - x 1⟫ < ⟪x (r 1), x ax - x 1⟫ ∨
      ⟪x (r 0), x ax - x 1⟫ < ⟪x (r ((k - 1 : ℕ) : ZMod k)), x ax - x 1⟫ := by
  have ey : ⟪x 1, x ax - x 1⟫ < ⟪x ay, x ax - x 1⟫ ↔ 0 < ⟪x ay - x 1, x ax - x 1⟫ := by
    rw [inner_sub_left, sub_pos]
  have ew : ⟪x 1, x ax - x 1⟫ < ⟪x aw, x ax - x 1⟫ ↔ 0 < ⟪x aw - x 1, x ax - x 1⟫ := by
    rw [inner_sub_left, sub_pos]
  rw [hr0]
  rcases hends with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2, ey, ew]
  · exact hsign
  · exact hsign.symm

/-- **Lemma 20.2 (b), Rupert form (Lemma C at `K`'s own metric, without a radius).**  A cap-edge
crossing with the rim data `CapRim0`, an acute angle at `1` between the cap edge and one of the
other two axes, and no far corner dipping below both of its rim neighbours, certifies `K`. -/
theorem isRupert_capEdge_noDip {x : Fin 7 → ℝ³} (hinj : Function.Injective x) {ax ay aw : Fin 7}
    (hax : ax ≠ 1) {k : ℕ} [NeZero k] {r : ZMod k → Fin 7} (hR : CapRim0 x ax ay aw k r)
    (hsign : 0 < ⟪x ay - x 1, x ax - x 1⟫ ∨ 0 < ⟪x aw - x 1, x ax - x 1⟫)
    (hdip : ∀ n : ℕ, 1 ≤ n → n + 3 ≤ k →
      ¬ (⟪x (r ((n + 1 : ℕ) : ZMod k)), x ax - x 1⟫ < ⟪x (r (n : ZMod k)), x ax - x 1⟫ ∧
        ⟪x (r ((n + 1 : ℕ) : ZMod k)), x ax - x 1⟫ < ⟪x (r ((n + 2 : ℕ) : ZMod k)), x ax - x 1⟫)) :
    IsRupert (univ.image x) := by
  obtain ⟨hk, hr0, hends, -, -, hz, -⟩ := id hR
  exact isRupert_capRim0 hinj hax hR
    (isCyclicUnimodal_of_noDip hk hz (capRim0_h0 hr0 hends hsign) hdip)

/-- **Lemma 20.2 (b) with (c): three far corners.**  A cap-edge rim `(1, y, r₂, 3, r₄, w)` with
`{r₂, r₄} = {4, 5}` and `3` in the plane of `0, 4, 5` opposite `0` (the quadrilateral `0345`):
if `z0 < min (z4, z5)` at the view, only `4` and `5` can dip, so with an acute angle at `1` and
neither `r₂` nor `r₄` below both rim neighbours, `K` is Rupert. -/
theorem isRupert_capEdge_mid3 {x : Fin 7 → ℝ³} (hinj : Function.Injective x) {ax ay aw : Fin 7}
    (hax : ax ≠ 1) {r : ZMod 6 → Fin 7} (hR : CapRim0 x ax ay aw 6 r) (h3 : r 3 = 3)
    (h24 : (r 2 = 4 ∧ r 4 = 5) ∨ (r 2 = 5 ∧ r 4 = 4)) {s t : ℝ}
    (hq : x 3 = x 0 + s • (x 4 - x 0) + t • (x 5 - x 0)) (hs : 0 < s) (ht : 0 < t)
    (hst : 1 < s + t) (h04 : ⟪x 0, x ax - x 1⟫ < ⟪x 4, x ax - x 1⟫)
    (h05 : ⟪x 0, x ax - x 1⟫ < ⟪x 5, x ax - x 1⟫)
    (hsign : 0 < ⟪x ay - x 1, x ax - x 1⟫ ∨ 0 < ⟪x aw - x 1, x ax - x 1⟫)
    (hd2 : ¬ (⟪x (r 2), x ax - x 1⟫ < ⟪x (r 1), x ax - x 1⟫ ∧
      ⟪x (r 2), x ax - x 1⟫ < ⟪x 3, x ax - x 1⟫))
    (hd4 : ¬ (⟪x (r 4), x ax - x 1⟫ < ⟪x 3, x ax - x 1⟫ ∧
      ⟪x (r 4), x ax - x 1⟫ < ⟪x (r 5), x ax - x 1⟫)) :
    IsRupert (univ.image x) := by
  have key := mid3_not_dip (u := x ax - x 1) hq hs ht hst h04 h05
  refine isRupert_capEdge_noDip hinj hax hR hsign fun n h1 h2 => ?_
  have hn : n = 1 ∨ n = 2 ∨ n = 3 := by omega
  rcases hn with rfl | rfl | rfl
  · rw [show ((1 + 1 : ℕ) : ZMod 6) = 2 from rfl, show ((1 : ℕ) : ZMod 6) = 1 from rfl,
      show ((1 + 2 : ℕ) : ZMod 6) = 3 from rfl, h3]
    exact hd2
  · rw [show ((2 + 1 : ℕ) : ZMod 6) = 3 from rfl, show ((2 : ℕ) : ZMod 6) = 2 from rfl,
      show ((2 + 2 : ℕ) : ZMod 6) = 4 from rfl, h3]
    rintro ⟨c1, c2⟩
    rcases h24 with ⟨e2, e4⟩ | ⟨e2, e4⟩ <;> rw [e2] at c1 <;> rw [e4] at c2
    · exact key ⟨c1.le, c2.le⟩
    · exact key ⟨c2.le, c1.le⟩
  · rw [show ((3 + 1 : ℕ) : ZMod 6) = 4 from rfl, show ((3 : ℕ) : ZMod 6) = 3 from rfl,
      show ((3 + 2 : ℕ) : ZMod 6) = 5 from rfl, h3]
    exact hd4

/-! ### Acute-safety and Lemma 20.2 (a) -/

/-- **Acute-safe** (§20.2): for every column `(g, h_y, h_w)` of a Gram matrix with `g > 0` and
`h_y > 0` or `h_w > 0`, the rim depths `g X_x + h_y X_y + h_w X_w` are cyclically unimodal when
distinct.  X-only; since `g_y`, `g_w` are free, every such column occurs at some metric, so this
says that the cap edge does not fail at any metric with an acute angle next to it. -/
def AcuteSafe (cx cy cw : Fin 7 → ℝ) {k : ℕ} [NeZero k] (r : ZMod k → Fin 7) : Prop :=
  ∀ g hy hw : ℝ, 0 < g → (0 < hy ∨ 0 < hw) →
    Function.Injective (fun i => cx (r i) * g + cy (r i) * hy + cw (r i) * hw) →
    IsCyclicUnimodal (fun i => cx (r i) * g + cy (r i) * hy + cw (r i) * hw)

theorem isCyclicUnimodal_const_add {k : ℕ} [NeZero k] {z : ZMod k → ℝ} (c : ℝ)
    (h : IsCyclicUnimodal z) : IsCyclicUnimodal (fun i => c + z i) := by
  refine ⟨fun i j e => h.1 (add_left_cancel e), ?_⟩
  simp only [add_lt_add_iff_left]
  exact h.2

/-- **An acute-safe cap edge certifies `K` at `K`'s own metric** whenever the cap edge makes an
acute angle with one of the other two axes at `1`. -/
theorem isRupert_capEdge_acuteSafe {x : Fin 7 → ℝ³} (hinj : Function.Injective x)
    {ax ay aw : Fin 7} {cx cy cw : Fin 7 → ℝ}
    (hrep : ∀ v, x v = x 1 + cx v • (x ax - x 1) + cy v • (x ay - x 1) + cw v • (x aw - x 1))
    (hax : ax ≠ 1) {k : ℕ} [NeZero k] {r : ZMod k → Fin 7} (hR : CapRim0 x ax ay aw k r)
    (hS : AcuteSafe cx cy cw r)
    (hsign : 0 < ⟪x ay - x 1, x ax - x 1⟫ ∨ 0 < ⟪x aw - x 1, x ax - x 1⟫) :
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

/-- **Lemma 20.2 (a), at every metric.**  A 4-corner cap-edge rim `(1, y, r, w)` (either
orientation) whose far corner has `X_x(r) > 0`, `X_y(r), X_w(r) ≥ 0` and `X_y(r) + X_w(r) > 1`
(the corner lies beyond the line `y w` of the screen) is acute-safe: failure forces
`h_xy ≤ 0` and `h_xw ≤ 0`. -/
theorem acuteSafe_four {cx cy cw : Fin 7 → ℝ} {r : ZMod 4 → Fin 7} {ay aw : Fin 7}
    (h1 : cx (r 0) = 0 ∧ cy (r 0) = 0 ∧ cw (r 0) = 0)
    (hends : (r 1 = ay ∧ r 3 = aw) ∨ (r 1 = aw ∧ r 3 = ay))
    (hy : cx ay = 0 ∧ cy ay = 1 ∧ cw ay = 0) (hw : cx aw = 0 ∧ cy aw = 0 ∧ cw aw = 1)
    (hβ : 0 < cx (r 2)) (hα : 0 ≤ cy (r 2)) (hγ : 0 ≤ cw (r 2))
    (hαγ : 1 < cy (r 2) + cw (r 2)) : AcuteSafe cx cy cw r := by
  intro g p q hg hs hinj
  refine isCyclicUnimodal_of_NWS4 hinj ?_
  obtain ⟨a1, b1, c1⟩ := h1
  set α := cy (r 2)
  set β := cx (r 2)
  set γ := cw (r 2)
  have hS : cx (r 2) * g + cy (r 2) * p + cw (r 2) * q = β * g + α * p + γ * q := by ring
  have hβg : 0 < β * g := mul_pos hβ hg
  -- the impossible pattern `{y, w} ≥ {1, r}`
  have key : ∀ P Q : ℝ, 0 ≤ P → 0 ≤ Q → (P = p ∧ Q = q ∨ P = q ∧ Q = p) →
      ¬ (β * g + α * p + γ * q ≤ P ∧ β * g + α * p + γ * q ≤ Q) := by
    rintro P Q hP hQ hPQ ⟨c1, c2⟩
    have hp : 0 ≤ p := by rcases hPQ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
    have hq : 0 ≤ q := by rcases hPQ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
    have hp' : β * g + α * p + γ * q ≤ p := by
      rcases hPQ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
    have hq' : β * g + α * p + γ * q ≤ q := by
      rcases hPQ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
    nlinarith [mul_le_mul_of_nonneg_left hp' hα, mul_le_mul_of_nonneg_left hq' hγ,
      mul_nonneg hα hp, mul_nonneg hγ hq]
  rcases hends with ⟨e1, e3⟩ | ⟨e1, e3⟩
  · simp only [NWS4, a1, b1, c1, e1, e3, hy.1, hy.2.1, hy.2.2, hw.1, hw.2.1, hw.2.2, hS]
    refine ⟨by rcases hs with h | h <;> [left; (right; left)] <;> linarith, ?_⟩
    by_contra hn
    simp only [not_or, not_lt] at hn
    exact key p q (by linarith [hn.1]) (by linarith [hn.2.1]) (Or.inl ⟨rfl, rfl⟩)
      ⟨by linarith [hn.2.2.1], by linarith [hn.2.2.2]⟩
  · simp only [NWS4, a1, b1, c1, e1, e3, hy.1, hy.2.1, hy.2.2, hw.1, hw.2.1, hw.2.2, hS]
    refine ⟨by rcases hs with h | h <;> [(right; left); left] <;> linarith, ?_⟩
    by_contra hn
    simp only [not_or, not_lt] at hn
    exact key q p (by linarith [hn.1]) (by linarith [hn.2.1]) (Or.inr ⟨rfl, rfl⟩)
      ⟨by linarith [hn.2.2.1], by linarith [hn.2.2.2]⟩

/-! ### The far corner of a 4-corner cap-edge rim -/

theorem det3_capFrame (u ey ew : ℝ³) (a1 b1 c1 a2 b2 c2 : ℝ) :
    det3 (a1 • u + b1 • ey + c1 • ew) (a2 • u + b2 • ey + c2 • ew) u =
      (b1 * c2 - c1 * b2) * det3 ey ew u := by
  simp only [det3_expand, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring

theorem zmod4_three : ((4 - 1 : ℕ) : ZMod 4) = 3 := rfl

/-- **The far corner of a 4-corner cap-edge rim is a fourth label**: it is not `1`, `ay`, `aw`
or the axis vertex `ax`. -/
theorem capRim0_four_far {x : Fin 7 → ℝ³} {ax ay aw : Fin 7} {r : ZMod 4 → Fin 7}
    (hR : CapRim0 x ax ay aw 4 r) : r 2 ≠ 1 ∧ r 2 ≠ ay ∧ r 2 ≠ aw ∧ r 2 ≠ ax := by
  obtain ⟨-, hr0, hends, hcyc, -⟩ := hR
  rw [zmod4_three] at hends
  obtain ⟨a0, a1, a2, a3⟩ := zmod4_add_one
  have c02 := hcyc 0 2 (by decide) (by decide)
  have c13 := hcyc 1 3 (by decide) (by decide)
  rw [a0] at c02; rw [a1] at c13
  have n1 : r 2 ≠ r 1 := by intro e; rw [e, det3_self_left] at c02; exact lt_irrefl _ c02
  have n3 : r 2 ≠ r 3 := by intro e; rw [e, det3_self_left] at c13; exact lt_irrefl _ c13
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro e; rw [e, ← hr0, sub_self, det3_zero_mid] at c02; exact lt_irrefl _ c02
  · rcases hends with ⟨e1, e3⟩ | ⟨e1, e3⟩
    · rw [← e1]; exact n1
    · rw [← e3]; exact n3
  · rcases hends with ⟨e1, e3⟩ | ⟨e1, e3⟩
    · rw [← e3]; exact n3
    · rw [← e1]; exact n1
  · intro e; rw [e, hr0, det3_self_right'] at c02; exact lt_irrefl _ c02

/-- **The far corner lies beyond the line `y w`** of the screen (the rim `(1, y, r, w)` is a
strictly convex quadrilateral): `X_y(r) + X_w(r) > 1`. -/
theorem capRim_far_sum {x : Fin 7 → ℝ³} {ax ay aw : Fin 7} {cx cy cw : Fin 7 → ℝ}
    (hrep : ∀ v, x v = x 1 + cx v • (x ax - x 1) + cy v • (x ay - x 1) + cw v • (x aw - x 1))
    {r : ZMod 4 → Fin 7} (hR : CapRim0 x ax ay aw 4 r)
    (h1 : cx 1 = 0 ∧ cy 1 = 0 ∧ cw 1 = 0)
    (hy : cx ay = 0 ∧ cy ay = 1 ∧ cw ay = 0) (hw : cx aw = 0 ∧ cy aw = 0 ∧ cw aw = 1)
    (hα : 0 < cy (r 2)) (hγ : 0 < cw (r 2)) : 1 < cy (r 2) + cw (r 2) := by
  obtain ⟨-, hr0, hends, hcyc, -⟩ := hR
  rw [zmod4_three] at hends
  obtain ⟨a0, a1, a2, a3⟩ := zmod4_add_one
  have hdiff : ∀ v w : Fin 7, x v - x w = (cx v - cx w) • (x ax - x 1) +
      (cy v - cy w) • (x ay - x 1) + (cw v - cw w) • (x aw - x 1) := by
    intro v w
    have e1 := hrep v
    have e2 := hrep w
    rw [e1, e2]; module
  have c02 := hcyc 0 2 (by decide) (by decide)
  have c13 := hcyc 1 3 (by decide) (by decide)
  rw [a0] at c02; rw [a1] at c13
  rw [hdiff (r 1) (r 0), hdiff (r 2) (r 0), det3_capFrame, hr0, h1.2.1, h1.2.2] at c02
  rw [hdiff (r 2) (r 1), hdiff (r 3) (r 1), det3_capFrame] at c13
  set D := det3 (x ay - x 1) (x aw - x 1) (x ax - x 1)
  rcases hends with ⟨e1, e3⟩ | ⟨e1, e3⟩
  · rw [e1, hy.2.1, hy.2.2] at c02
    rw [e1, e3, hy.2.1, hy.2.2, hw.2.1, hw.2.2] at c13
    have hD : 0 < D := by
      by_contra hn; push Not at hn; nlinarith [mul_nonneg hγ.le (neg_nonneg.mpr hn)]
    by_contra hn; push Not at hn
    nlinarith [mul_nonneg (sub_nonneg.mpr hn) hD.le]
  · rw [e1, hw.2.1, hw.2.2] at c02
    rw [e1, e3, hy.2.1, hy.2.2, hw.2.1, hw.2.2] at c13
    have hD : D < 0 := by
      by_contra hn; push Not at hn; nlinarith [mul_nonneg hα.le hn]
    by_contra hn; push Not at hn
    nlinarith [mul_nonneg (sub_nonneg.mpr hn) (neg_nonneg.mpr hD.le)]

/-! ### Type 24: the three cap edges -/

namespace Type24

variable {x : Fin 7 → ℝ³}

theorem oblX0_one : oblX0 x 1 = 0 := by simp only [oblX0, sub_self, vol3]; simp

theorem oblX2_one : oblX2 x 1 = 0 := by simp only [oblX2, sub_self, vol3]; simp

theorem oblX6_one : oblX6 x 1 = 0 := by simp only [oblX6, sub_self, vol3]; simp

/-- `E_2 = 012/126-2` (view `e_b`, far path from `0` to `6`) has an acute-safe rim. -/
def SafeE2 (x : Fin 7 → ℝ³) : Prop :=
  ∃ (k : ℕ) (_ : NeZero k) (r : ZMod k → Fin 7),
    CapRim0 x 2 0 6 k r ∧ AcuteSafe (oblX2 x) (oblX0 x) (oblX6 x) r

/-- `E_6 = 016/126-6` (view `e_c`, far path from `2` to `0`) has an acute-safe rim. -/
def SafeE6 (x : Fin 7 → ℝ³) : Prop :=
  ∃ (k : ℕ) (_ : NeZero k) (r : ZMod k → Fin 7),
    CapRim0 x 6 2 0 k r ∧ AcuteSafe (oblX6 x) (oblX2 x) (oblX0 x) r

/-- `E_0 = 012/016-0` (view `e_a`, far path from `2` to `6`) has an acute-safe rim. -/
def SafeE0 (x : Fin 7 → ℝ³) : Prop :=
  ∃ (k : ℕ) (_ : NeZero k) (r : ZMod k → Fin 7),
    CapRim0 x 0 2 6 k r ∧ AcuteSafe (oblX0 x) (oblX2 x) (oblX6 x) r

theorem far345 {v : Fin 7} (h1 : v ≠ 1) (h0 : v ≠ 0) (h2 : v ≠ 2) (h6 : v ≠ 6) :
    v = 3 ∨ v = 4 ∨ v = 5 := by
  revert v; decide

variable (T : Type24 x)
include T

theorem pos345 {v : Fin 7} (hv : v = 3 ∨ v = 4 ∨ v = 5) :
    0 < oblX0 x v ∧ 0 < oblX2 x v ∧ 0 < oblX6 x v := by
  rcases hv with rfl | rfl | rfl <;>
    exact ⟨T.X0_pos (by decide), T.X2_pos (by decide), T.X6_pos (by decide)⟩

/-- **Lemma 20.2 (a) for `E_2`**: a single far corner makes `E_2` acute-safe. -/
theorem safeE2_of_four {r : ZMod 4 → Fin 7} (hR : CapRim0 x 2 0 6 4 r) : SafeE2 x := by
  obtain ⟨n1, ny, nw, nx⟩ := capRim0_four_far hR
  obtain ⟨p0, p2, p6⟩ := T.pos345 (far345 n1 ny nx nw)
  have h1 : oblX2 x 1 = 0 ∧ oblX0 x 1 = 0 ∧ oblX6 x 1 = 0 := ⟨oblX2_one, oblX0_one, oblX6_one⟩
  have hy : oblX2 x 0 = 0 ∧ oblX0 x 0 = 1 ∧ oblX6 x 0 = 0 :=
    ⟨oblX2_zero, T.oblX0_zero', oblX6_zero⟩
  have hw : oblX2 x 6 = 0 ∧ oblX0 x 6 = 0 ∧ oblX6 x 6 = 1 :=
    ⟨oblX2_six, oblX0_six, T.oblX6_six⟩
  refine ⟨4, inferInstance, r, hR, acuteSafe_four (by rw [hR.2.1]; exact h1) ?_ hy hw p2 p0.le
    p6.le (capRim_far_sum T.rep2 hR h1 hy hw p0 p6)⟩
  have := hR.2.2.1; rwa [zmod4_three] at this

/-- **Lemma 20.2 (a) for `E_6`**: a single far corner makes `E_6` acute-safe. -/
theorem safeE6_of_four {r : ZMod 4 → Fin 7} (hR : CapRim0 x 6 2 0 4 r) : SafeE6 x := by
  obtain ⟨n1, ny, nw, nx⟩ := capRim0_four_far hR
  obtain ⟨p0, p2, p6⟩ := T.pos345 (far345 n1 nw ny nx)
  have h1 : oblX6 x 1 = 0 ∧ oblX2 x 1 = 0 ∧ oblX0 x 1 = 0 := ⟨oblX6_one, oblX2_one, oblX0_one⟩
  have hy : oblX6 x 2 = 0 ∧ oblX2 x 2 = 1 ∧ oblX0 x 2 = 0 :=
    ⟨oblX6_two, T.oblX2_two, oblX0_two⟩
  have hw : oblX6 x 0 = 0 ∧ oblX2 x 0 = 0 ∧ oblX0 x 0 = 1 :=
    ⟨oblX6_zero, oblX2_zero, T.oblX0_zero'⟩
  refine ⟨4, inferInstance, r, hR, acuteSafe_four (by rw [hR.2.1]; exact h1) ?_ hy hw p6 p2.le
    p0.le (capRim_far_sum T.rep6 hR h1 hy hw p2 p0)⟩
  have := hR.2.2.1; rwa [zmod4_three] at this

/-- **Lemma 20.2 (a) for `E_0`** (referee's extension): a single far corner makes `E_0`
acute-safe. -/
theorem safeE0_of_four {r : ZMod 4 → Fin 7} (hR : CapRim0 x 0 2 6 4 r) : SafeE0 x := by
  obtain ⟨n1, ny, nw, nx⟩ := capRim0_four_far hR
  obtain ⟨p0, p2, p6⟩ := T.pos345 (far345 n1 nx ny nw)
  have h1 : oblX0 x 1 = 0 ∧ oblX2 x 1 = 0 ∧ oblX6 x 1 = 0 := ⟨oblX0_one, oblX2_one, oblX6_one⟩
  have hy : oblX0 x 2 = 0 ∧ oblX2 x 2 = 1 ∧ oblX6 x 2 = 0 :=
    ⟨oblX0_two, T.oblX2_two, oblX6_two⟩
  have hw : oblX0 x 6 = 0 ∧ oblX2 x 6 = 0 ∧ oblX6 x 6 = 1 :=
    ⟨oblX0_six, oblX2_six, T.oblX6_six⟩
  refine ⟨4, inferInstance, r, hR, acuteSafe_four (by rw [hR.2.1]; exact h1) ?_ hy hw p0 p2.le
    p6.le (capRim_far_sum T.rep hR h1 hy hw p2 p6)⟩
  have := hR.2.2.1; rwa [zmod4_three] at this

end Type24

/-- **`E_2` acute-safe, Rupert form**: `K` is Rupert if `c_ab > 0` or `c_bc > 0`. -/
theorem isRupert_type24_safeE2 {x : Fin 7 → ℝ³} (T : Type24 x) (h : Type24.SafeE2 x)
    (hsign : 0 < ⟪x 0 - x 1, x 2 - x 1⟫ ∨ 0 < ⟪x 6 - x 1, x 2 - x 1⟫) :
    IsRupert (univ.image x) := by
  obtain ⟨k, _, r, hR, hS⟩ := h
  exact isRupert_capEdge_acuteSafe T.inj T.rep2 (by decide) hR hS hsign

/-- **`E_6` acute-safe, Rupert form**: `K` is Rupert if `c_bc > 0` or `c_ac > 0`. -/
theorem isRupert_type24_safeE6 {x : Fin 7 → ℝ³} (T : Type24 x) (h : Type24.SafeE6 x)
    (hsign : 0 < ⟪x 2 - x 1, x 6 - x 1⟫ ∨ 0 < ⟪x 0 - x 1, x 6 - x 1⟫) :
    IsRupert (univ.image x) := by
  obtain ⟨k, _, r, hR, hS⟩ := h
  exact isRupert_capEdge_acuteSafe T.inj T.rep6 (by decide) hR hS hsign

/-- **`E_0` acute-safe, Rupert form**: `K` is Rupert if `c_ab > 0` or `c_ac > 0`. -/
theorem isRupert_type24_safeE0 {x : Fin 7 → ℝ³} (T : Type24 x) (h : Type24.SafeE0 x)
    (hsign : 0 < ⟪x 2 - x 1, x 0 - x 1⟫ ∨ 0 < ⟪x 6 - x 1, x 0 - x 1⟫) :
    IsRupert (univ.image x) := by
  obtain ⟨k, _, r, hR, hS⟩ := h
  exact isRupert_capEdge_acuteSafe T.inj T.rep (by decide) hR hS hsign

/-- Two of the three cap edges are acute-safe. -/
def Type24.TwoSafe (x : Fin 7 → ℝ³) : Prop :=
  (Type24.SafeE2 x ∧ Type24.SafeE6 x) ∨ (Type24.SafeE2 x ∧ Type24.SafeE0 x) ∨
    (Type24.SafeE6 x ∧ Type24.SafeE0 x)

/-- **Theorem 20.8 (Conjecture A for two acute-safe cap edges), at `K`'s own metric.**  If two
of `E_2`, `E_6`, `E_0` are acute-safe (with their rims, distinct depths and no horizontal double
normal, `CapRim0`) and some face angle of the cap `1` is acute, `K` is Rupert: any two cap edges
see all three cosines.  No radius and no neighbourhood of the corner enter. -/
theorem isRupert_type24_two_safe {x : Fin 7 → ℝ³} (T : Type24 x) (hsafe : Type24.TwoSafe x)
    (hacute : 0 < ⟪x 0 - x 1, x 2 - x 1⟫ ∨ 0 < ⟪x 0 - x 1, x 6 - x 1⟫ ∨
      0 < ⟪x 2 - x 1, x 6 - x 1⟫) :
    IsRupert (univ.image x) := by
  have c1 := real_inner_comm (x 0 - x 1) (x 2 - x 1)
  have c2 := real_inner_comm (x 0 - x 1) (x 6 - x 1)
  have c3 := real_inner_comm (x 2 - x 1) (x 6 - x 1)
  rcases hsafe with ⟨h2, h6⟩ | ⟨h2, h0⟩ | ⟨h6, h0⟩
  · rcases hacute with h | h | h
    · exact isRupert_type24_safeE2 T h2 (Or.inl h)
    · exact isRupert_type24_safeE6 T h6 (Or.inr h)
    · exact isRupert_type24_safeE6 T h6 (Or.inl h)
  · rcases hacute with h | h | h
    · exact isRupert_type24_safeE2 T h2 (Or.inl h)
    · exact isRupert_type24_safeE0 T h0 (Or.inr (by rw [c2]; exact h))
    · exact isRupert_type24_safeE2 T h2 (Or.inr (by rw [c3]; exact h))
  · rcases hacute with h | h | h
    · exact isRupert_type24_safeE0 T h0 (Or.inl (by rw [c1]; exact h))
    · exact isRupert_type24_safeE6 T h6 (Or.inr h)
    · exact isRupert_type24_safeE6 T h6 (Or.inl h)

/-- **Conjecture A for two acute-safe cap edges**: a type-24 nopert candidate (not Rupert) with
two acute-safe cap edges has all three face angles at `1` right or obtuse. -/
theorem Type24.obtuse_of_two_safe {x : Fin 7 → ℝ³} (T : Type24 x) (hsafe : Type24.TwoSafe x)
    (hK : ¬ IsRupert (univ.image x)) :
    ⟪x 0 - x 1, x 2 - x 1⟫ ≤ 0 ∧ ⟪x 0 - x 1, x 6 - x 1⟫ ≤ 0 ∧ ⟪x 2 - x 1, x 6 - x 1⟫ ≤ 0 := by
  by_contra h
  simp only [not_and_or, not_le] at h
  exact hK (isRupert_type24_two_safe T hsafe h)

/-! ### Lemma 20.6: `S_0` and the edge crossing along `05` at the exact corner -/

namespace Type24

variable {x : Fin 7 → ℝ³} (T : Type24 x)
include T

/-- **17.5 (b), both halves**: at an exact corner in case C, `S_0 = 025/046` with the rim
`(0, 2, 3, 6)` fails only where `z0 ≥ z2` and `z0 ≥ z6` at its view:
`(1 + ω5) g_b ≤ (ω5 ω4 − 1) g_a` and `(1 + ω4) g_c ≤ (ω5 ω4 − 1) g_a`. -/
theorem s0_fails_corner2 (hE : ExactCorner x) (h3 : 0 < omega3 x) (h4 : 0 < omega4 x)
    (h5 : 0 < omega5 x) (h45 : 1 < omega4 x * omega5 x)
    (hF : Fails4 (x 0) (x 3) (x 2) (x 6) (view0 x)) :
    (1 + omega5 x) * ⟪x 2 - x 1, x 2 - x 1⟫ ≤
        (omega5 x * omega4 x - 1) * ⟪x 0 - x 1, x 0 - x 1⟫ ∧
      (1 + omega4 x) * ⟪x 6 - x 1, x 6 - x 1⟫ ≤
        (omega5 x * omega4 x - 1) * ⟪x 0 - x 1, x 0 - x 1⟫ := by
  have ga := T.ga_pos; have gb := T.gb_pos; have gc := T.gc_pos
  have dS := fun v => T.depth_corner hE v (omega5 x * omega4 x - 1) (1 + omega5 x)
    (1 + omega4 x)
  rw [← Type24.view0_eq] at dS
  have a3 := T.X0_pos (v := 3) (by decide)
  have b3 := T.X2_pos (v := 3) (by decide)
  have c3 := T.X6_pos (v := 3) (by decide)
  have e3 := T.eq3
  have hα : 0 < omega5 x * omega4 x - 1 := by linarith [mul_comm (omega4 x) (omega5 x)]
  set α := (omega5 x * omega4 x - 1) * ⟪x 0 - x 1, x 0 - x 1⟫ with hαd
  set β := (1 + omega5 x) * ⟪x 2 - x 1, x 2 - x 1⟫ with hβd
  set γ := (1 + omega4 x) * ⟪x 6 - x 1, x 6 - x 1⟫ with hγd
  have hα0 : 0 < α := mul_pos hα ga
  have hβ0 : 0 < β := mul_pos (by linarith) gb
  have hγ0 : 0 < γ := mul_pos (by linarith) gc
  rcases hF with h | h <;> rw [max_le_iff, le_min_iff, le_min_iff, dS 0, dS 3, dS 2, dS 6] at h <;>
    simp only [T.oblX0_zero', Type24.oblX2_zero, Type24.oblX6_zero, Type24.oblX0_six,
      Type24.oblX2_six, T.oblX6_six, Type24.oblX0_two, T.oblX2_two, Type24.oblX6_two] at h
  · exfalso
    obtain ⟨-, h32, h36⟩ := h
    have hbc : oblX2 x 3 + oblX6 x 3 = 1 + omega3 x * oblX0 x 3 := by linarith
    have hpos : 0 < α * oblX0 x 3 := mul_pos hα0 a3
    have hω : 0 < omega3 x * oblX0 x 3 := mul_pos h3 a3
    rcases le_total β γ with hbg | hbg
    · nlinarith [mul_le_mul_of_nonneg_left hbg c3.le, mul_pos hβ0 hω]
    · nlinarith [mul_le_mul_of_nonneg_left hbg b3.le, mul_pos hγ0 hω]
  · exact ⟨by linarith [h.1.1], by linarith [h.2.1]⟩

/-- The view of `E_05 = 025/0345-0` in the corner frame: `x 5 − x 0 = (a5 − 1) e_a + b5 e_b +
c5 e_c`. -/
theorem view05_eq : x 5 - x 0 = (oblX0 x 5 - 1) • (x 0 - x 1) + oblX2 x 5 • (x 2 - x 1) +
    oblX6 x 5 • (x 6 - x 1) := by
  have e := T.rep 5
  rw [e]; module

/-- The view of `E_04 = 046/0345-0`: `x 4 − x 0 = (a4 − 1) e_a + b4 e_b + c4 e_c`. -/
theorem view04_eq : x 4 - x 0 = (oblX0 x 4 - 1) • (x 0 - x 1) + oblX2 x 4 • (x 2 - x 1) +
    oblX6 x 4 • (x 6 - x 1) := by
  have e := T.rep 4
  rw [e]; module

/-- **Lemma 20.6.**  At an exact corner in `C̄` (all `ω > 0`, `ω4 ω5 > 1`), let `S_0` have the
rim `(0, 2, 3, 6)` and `E_05 = 025/0345-0` (view `x 5 − x 0`) the rim `(2, 5, q, 6)`,
`q ∈ {3, 4}`, with `a5 > 1` and
- (i) `(ω4 ω5 − 1) b5 (1 − b5) < (1 + ω5)(a5 − 1) a5` (automatic if `b5 ≥ 1`),
- (ii) `(ω4 ω5 − 1) c5 (1 − c_q) < (1 + ω4)(a5 − 1) a_q` (automatic if `c_q ≥ 1`).

Then `S_0` and `E_05` do not both fail, at every diagonal metric. -/
theorem s0_e05_corner (hE : ExactCorner x) (h3 : 0 < omega3 x) (h4 : 0 < omega4 x)
    (h5 : 0 < omega5 x) (h45 : 1 < omega4 x * omega5 x) {q : Fin 7} (hq : q = 3 ∨ q = 4)
    (ha5 : 1 < oblX0 x 5)
    (hi : (omega4 x * omega5 x - 1) * oblX2 x 5 * (1 - oblX2 x 5) <
      (1 + omega5 x) * (oblX0 x 5 - 1) * oblX0 x 5)
    (hii : (omega4 x * omega5 x - 1) * oblX6 x 5 * (1 - oblX6 x q) <
      (1 + omega4 x) * (oblX0 x 5 - 1) * oblX0 x q) :
    ¬ (Fails4 (x 0) (x 3) (x 2) (x 6) (view0 x) ∧ Fails4 (x 2) (x q) (x 5) (x 6) (x 5 - x 0)) := by
  rintro ⟨hS, hF⟩
  obtain ⟨sb, sc⟩ := T.s0_fails_corner2 hE h3 h4 h5 h45 hS
  have ga := T.ga_pos; have gb := T.gb_pos; have gc := T.gc_pos
  have b5 := T.X2_pos (v := 5) (by decide)
  have c5 := T.X6_pos (v := 5) (by decide)
  have aq : 0 < oblX0 x q := by rcases hq with rfl | rfl <;> exact T.X0_pos (by decide)
  have bq : 0 < oblX2 x q := by rcases hq with rfl | rfl <;> exact T.X2_pos (by decide)
  have dE := fun v => T.depth_corner hE v (oblX0 x 5 - 1) (oblX2 x 5) (oblX6 x 5)
  rw [← T.view05_eq] at dE
  have hK : omega5 x * omega4 x - 1 = omega4 x * omega5 x - 1 := by ring
  rw [hK] at sb sc
  set K := omega4 x * omega5 x - 1
  set A := oblX0 x 5 - 1
  have hA : 0 < A := by simp only [A]; linarith
  rcases hF with h | h <;> rw [max_le_iff, le_min_iff, le_min_iff, dE 2, dE q, dE 5, dE 6] at h <;>
    simp only [Type24.oblX0_six, Type24.oblX2_six, T.oblX6_six, Type24.oblX0_two, T.oblX2_two,
      Type24.oblX6_two] at h
  · -- `{2, q}` below `{5, 6}`: `z6 ≥ z_q`
    have h6 := h.2.2
    -- `g_c c5 (1 − c_q) ≥ g_a A a_q + g_b b5 b_q > g_a A a_q`
    have k1 : ⟪x 0 - x 1, x 0 - x 1⟫ * (A * oblX0 x q) <
        ⟪x 6 - x 1, x 6 - x 1⟫ * (oblX6 x 5 * (1 - oblX6 x q)) := by
      nlinarith [mul_pos (mul_pos gb b5) bq]
    have hcq : 0 < 1 - oblX6 x q := by
      by_contra hn; push Not at hn
      nlinarith [mul_pos ga (mul_pos hA aq), mul_nonneg gc.le (mul_nonneg c5.le (neg_nonneg.mpr hn))]
    have k2 := mul_le_mul_of_nonneg_right sc (mul_pos c5 hcq).le
    nlinarith [mul_lt_mul_of_pos_left hii ga, mul_lt_mul_of_pos_left k1 (show (0 : ℝ) < 1 + omega4 x
      by linarith)]
  · -- `{5, 6}` below `{2, q}`: `z2 ≥ z5`
    have h2 := h.1.1
    have k1 : ⟪x 0 - x 1, x 0 - x 1⟫ * (A * oblX0 x 5) <
        ⟪x 2 - x 1, x 2 - x 1⟫ * (oblX2 x 5 * (1 - oblX2 x 5)) := by
      nlinarith [mul_pos gc (mul_pos c5 c5)]
    have hb : 0 < 1 - oblX2 x 5 := by
      by_contra hn; push Not at hn
      nlinarith [mul_pos ga (mul_pos hA (show 0 < oblX0 x 5 by linarith)),
        mul_nonneg gb.le (mul_nonneg b5.le (neg_nonneg.mpr hn))]
    have k2 := mul_le_mul_of_nonneg_right sb (mul_pos b5 hb).le
    nlinarith [mul_lt_mul_of_pos_left hi ga, mul_lt_mul_of_pos_left k1 (show (0 : ℝ) < 1 + omega5 x
      by linarith)]

/-- **Lemma 20.6, mirror**: `S_0` and `E_04 = 046/0345-0` (view `x 4 − x 0`) with the rim
`(6, 4, q, 2)`, `q ∈ {3, 5}`, `a4 > 1`, and
- (i′) `(ω4 ω5 − 1) c4 (1 − c4) < (1 + ω4)(a4 − 1) a4`,
- (ii′) `(ω4 ω5 − 1) b4 (1 − b_q) < (1 + ω5)(a4 − 1) a_q`,

do not both fail, at every diagonal metric. -/
theorem s0_e04_corner (hE : ExactCorner x) (h3 : 0 < omega3 x) (h4 : 0 < omega4 x)
    (h5 : 0 < omega5 x) (h45 : 1 < omega4 x * omega5 x) {q : Fin 7} (hq : q = 3 ∨ q = 5)
    (ha4 : 1 < oblX0 x 4)
    (hi : (omega4 x * omega5 x - 1) * oblX6 x 4 * (1 - oblX6 x 4) <
      (1 + omega4 x) * (oblX0 x 4 - 1) * oblX0 x 4)
    (hii : (omega4 x * omega5 x - 1) * oblX2 x 4 * (1 - oblX2 x q) <
      (1 + omega5 x) * (oblX0 x 4 - 1) * oblX0 x q) :
    ¬ (Fails4 (x 0) (x 3) (x 2) (x 6) (view0 x) ∧ Fails4 (x 6) (x q) (x 4) (x 2) (x 4 - x 0)) := by
  rintro ⟨hS, hF⟩
  obtain ⟨sb, sc⟩ := T.s0_fails_corner2 hE h3 h4 h5 h45 hS
  have ga := T.ga_pos; have gb := T.gb_pos; have gc := T.gc_pos
  have b4 := T.X2_pos (v := 4) (by decide)
  have c4 := T.X6_pos (v := 4) (by decide)
  have aq : 0 < oblX0 x q := by rcases hq with rfl | rfl <;> exact T.X0_pos (by decide)
  have cq : 0 < oblX6 x q := by rcases hq with rfl | rfl <;> exact T.X6_pos (by decide)
  have dE := fun v => T.depth_corner hE v (oblX0 x 4 - 1) (oblX2 x 4) (oblX6 x 4)
  rw [← T.view04_eq] at dE
  have hK : omega5 x * omega4 x - 1 = omega4 x * omega5 x - 1 := by ring
  rw [hK] at sb sc
  set K := omega4 x * omega5 x - 1
  set A := oblX0 x 4 - 1
  have hA : 0 < A := by simp only [A]; linarith
  rcases hF with h | h <;> rw [max_le_iff, le_min_iff, le_min_iff, dE 6, dE q, dE 4, dE 2] at h <;>
    simp only [Type24.oblX0_six, Type24.oblX2_six, T.oblX6_six, Type24.oblX0_two, T.oblX2_two,
      Type24.oblX6_two] at h
  · -- `{6, q}` below `{4, 2}`: `z2 ≥ z_q`
    have h2 := h.2.2
    have k1 : ⟪x 0 - x 1, x 0 - x 1⟫ * (A * oblX0 x q) <
        ⟪x 2 - x 1, x 2 - x 1⟫ * (oblX2 x 4 * (1 - oblX2 x q)) := by
      nlinarith [mul_pos (mul_pos gc c4) cq]
    have hbq : 0 < 1 - oblX2 x q := by
      by_contra hn; push Not at hn
      nlinarith [mul_pos ga (mul_pos hA aq), mul_nonneg gb.le (mul_nonneg b4.le (neg_nonneg.mpr hn))]
    have k2 := mul_le_mul_of_nonneg_right sb (mul_pos b4 hbq).le
    nlinarith [mul_lt_mul_of_pos_left hii ga, mul_lt_mul_of_pos_left k1 (show (0 : ℝ) < 1 + omega5 x
      by linarith)]
  · -- `{4, 2}` below `{6, q}`: `z6 ≥ z4`
    have h6 := h.1.1
    have k1 : ⟪x 0 - x 1, x 0 - x 1⟫ * (A * oblX0 x 4) <
        ⟪x 6 - x 1, x 6 - x 1⟫ * (oblX6 x 4 * (1 - oblX6 x 4)) := by
      nlinarith [mul_pos gb (mul_pos b4 b4)]
    have hc : 0 < 1 - oblX6 x 4 := by
      by_contra hn; push Not at hn
      nlinarith [mul_pos ga (mul_pos hA (show 0 < oblX0 x 4 by linarith)),
        mul_nonneg gc.le (mul_nonneg c4.le (neg_nonneg.mpr hn))]
    have k2 := mul_le_mul_of_nonneg_right sc (mul_pos c4 hc).le
    nlinarith [mul_lt_mul_of_pos_left hi ga, mul_lt_mul_of_pos_left k1 (show (0 : ℝ) < 1 + omega4 x
      by linarith)]

end Type24

/-- **Lemma 20.6, Rupert form.**  With `S_0` (rim `(0, 2, 3, 6)`) and `E_05` (rim
`(2, 5, q, 6)`) certified up to their depth patterns (`QuadTest'`; for `E_05` the double `x 0`
over the corner `5`), the point set is Rupert at an exact corner under (i), (ii). -/
theorem isRupert_s0_e05_corner {x : Fin 7 → ℝ³} (T : Type24 x) (hE : ExactCorner x)
    (h3 : 0 < omega3 x) (h4 : 0 < omega4 x) (h5 : 0 < omega5 x)
    (h45 : 1 < omega4 x * omega5 x) {q : Fin 7} (hq : q = 3 ∨ q = 4) (ha5 : 1 < oblX0 x 5)
    (hi : (omega4 x * omega5 x - 1) * oblX2 x 5 * (1 - oblX2 x 5) <
      (1 + omega5 x) * (oblX0 x 5 - 1) * oblX0 x 5)
    (hii : (omega4 x * omega5 x - 1) * oblX6 x 5 * (1 - oblX6 x q) <
      (1 + omega4 x) * (oblX0 x 5 - 1) * oblX0 x q)
    (hS : QuadTest' (univ.image x) (view0 x) (x 0) (x 2) (x 3) (x 6))
    (hE5 : QuadTest' (univ.image x) (x 5 - x 0) (x 2) (x 5) (x q) (x 6)) :
    IsRupert (univ.image x) :=
  isRupert_of_two_tests hS hE5 (T.s0_e05_corner hE h3 h4 h5 h45 hq ha5 hi hii)

/-- **Lemma 20.6, mirror, Rupert form**: `S_0` and `E_04` (rim `(6, 4, q, 2)`). -/
theorem isRupert_s0_e04_corner {x : Fin 7 → ℝ³} (T : Type24 x) (hE : ExactCorner x)
    (h3 : 0 < omega3 x) (h4 : 0 < omega4 x) (h5 : 0 < omega5 x)
    (h45 : 1 < omega4 x * omega5 x) {q : Fin 7} (hq : q = 3 ∨ q = 5) (ha4 : 1 < oblX0 x 4)
    (hi : (omega4 x * omega5 x - 1) * oblX6 x 4 * (1 - oblX6 x 4) <
      (1 + omega4 x) * (oblX0 x 4 - 1) * oblX0 x 4)
    (hii : (omega4 x * omega5 x - 1) * oblX2 x 4 * (1 - oblX2 x q) <
      (1 + omega5 x) * (oblX0 x 4 - 1) * oblX0 x q)
    (hS : QuadTest' (univ.image x) (view0 x) (x 0) (x 2) (x 3) (x 6))
    (hE4 : QuadTest' (univ.image x) (x 4 - x 0) (x 6) (x 4) (x q) (x 2)) :
    IsRupert (univ.image x) :=
  isRupert_of_two_tests hS hE4 (T.s0_e04_corner hE h3 h4 h5 h45 hq ha4 hi hii)

end Minimality

end
