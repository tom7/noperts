module

public import Minimality.Type24Snap

@[expose] public section

/-!
# The snap lemma at a degree-3 vertex, type-free (Fable Lemmas F1, F2)

For a polytope with a vertex `o` of degree 3 with neighbours at `o + e_a, o + e_b, o + e_c` (a
frame), every vertex has frame coordinates `X_a, X_b, X_c` (`x v − x w = Σ (X_i v − X_i w) e_i`),
and the depth difference at the oblique view `d` is exactly linear in the three axis inner
products `h_ij` (`CornerSnap.depth_sub`).  Nothing else of type 24 is used: a certified rim
(`RimTestR`, depths open) all of whose failure patterns are broken at the snap is Rupert on a
region of `h` (`isRupert_corner_snap`, the octant box of radius `δ`; `isRupert_corner_snap'`, the
whole fibre polytope `P`).

* `cosine_sum_ge`: **Lemma F1**, the three cosines of a Gram matrix sum to at least `−3/2`.
* `InFibre`: the 10-vertex polytope `P`; `radius_pos_fibre`: the sharp radius
  `max (b_1, b_2, b_3, b_i + b_j / 2)`.
* `Type24.isRupert_type24_snap'`: the type 24 statement as a corollary.
-/

namespace Minimality
open Finset
open scoped RealInnerProductSpace

namespace CornerSnap

/-! ### Lemma F1: cosine sums -/

/-- **Cosine-sum bound (Lemma F1).** For any three vectors, the cosines (`0` for a zero vector)
sum to at least `−3/2`: `|u_a + u_b + u_c|² ≥ 0` for the normalised vectors.  Neither
definiteness nor the sign of the cosines is needed. -/
theorem cosine_sum_ge (a b c : ℝ³) :
    -(3 / 2) ≤ ⟪a, b⟫ / (‖a‖ * ‖b‖) + ⟪a, c⟫ / (‖a‖ * ‖c‖) + ⟪b, c⟫ / (‖b‖ * ‖c‖) := by
  have key : ∀ u : ℝ³, ‖u‖ ≠ 0 → ‖(‖u‖⁻¹) • u‖ = 1 := by
    intro u hu
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hu]
  by_cases ha : ‖a‖ = 0
  · have : a = 0 := norm_eq_zero.mp ha
    subst this
    by_cases hb0 : ‖b‖ = 0
    · have : b = 0 := norm_eq_zero.mp hb0
      simp [this]; norm_num
    by_cases hc0 : ‖c‖ = 0
    · have : c = 0 := norm_eq_zero.mp hc0
      simp [this]; norm_num
    have := abs_real_inner_div_norm_mul_norm_le_one b c
    have := (abs_le.mp this).1
    simp
    linarith
  by_cases hb : ‖b‖ = 0
  · have : b = 0 := norm_eq_zero.mp hb
    subst this
    by_cases hc0 : ‖c‖ = 0
    · have : c = 0 := norm_eq_zero.mp hc0
      simp [this]; norm_num
    have := (abs_le.mp (abs_real_inner_div_norm_mul_norm_le_one a c)).1
    simp
    linarith
  by_cases hc : ‖c‖ = 0
  · have : c = 0 := norm_eq_zero.mp hc
    subst this
    have := (abs_le.mp (abs_real_inner_div_norm_mul_norm_le_one a b)).1
    simp only [inner_zero_right, zero_div, add_zero]
    linarith
  set u := (‖a‖⁻¹) • a
  set v := (‖b‖⁻¹) • b
  set w := (‖c‖⁻¹) • c
  have hu := key a ha
  have hv := key b hb
  have hw := key c hc
  have h0 : 0 ≤ ‖u + v + w‖ ^ 2 := sq_nonneg _
  have e : ‖u + v + w‖ ^ 2 = ‖u‖ ^ 2 + ‖v‖ ^ 2 + ‖w‖ ^ 2 + 2 * (⟪u, v⟫ + ⟪u, w⟫ + ⟪v, w⟫) := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
      ← real_inner_self_eq_norm_sq]
    simp only [inner_add_left, inner_add_right, real_inner_comm u v, real_inner_comm u w,
      real_inner_comm v w]
    ring
  have f : ∀ (p q : ℝ³), ‖p‖ ≠ 0 → ‖q‖ ≠ 0 →
      ⟪(‖p‖⁻¹) • p, (‖q‖⁻¹) • q⟫ = ⟪p, q⟫ / (‖p‖ * ‖q‖) := by
    intro p q hp hq
    rw [real_inner_smul_left, real_inner_smul_right]
    field_simp
  rw [f a b ha hb] at e
  rw [f a c ha hc] at e
  rw [f b c hb hc] at e
  rw [hu, hv, hw] at e
  linarith

/-- The cosine of two vectors is at most `1` in absolute value. -/
theorem abs_cos_le (a b : ℝ³) : |⟪a, b⟫ / (‖a‖ * ‖b‖)| ≤ 1 := by
  exact abs_real_inner_div_norm_mul_norm_le_one a b

/-- `⟪a, b⟫ = (⟪a, b⟫ / (‖a‖ ‖b‖)) · (‖a‖ ‖b‖)`, also when a vector is zero. -/
theorem inner_eq_cos_mul (a b : ℝ³) : ⟪a, b⟫ = ⟪a, b⟫ / (‖a‖ * ‖b‖) * (‖a‖ * ‖b‖) := by
  by_cases h : ‖a‖ * ‖b‖ = 0
  · have : ⟪a, b⟫ = 0 := by
      rcases mul_eq_zero.mp h with h | h
      · simp [norm_eq_zero.mp h]
      · simp [norm_eq_zero.mp h]
    simp [h, this]
  · rw [div_mul_cancel₀ _ h]

/-! ### The fibre polytope `P` and the sharp radius -/

/-- **The fibre polytope `P` (Lemma F1)**, in the cosine coordinates `t = −cos`: the cube
`[0,1]³` cut by `t_1 + t_2 + t_3 ≤ 3/2`.  Its ten vertices are `0`, the unit points and the six
permutations of `(1, 1/2, 0)`. -/
def InFibre (t1 t2 t3 : ℝ) : Prop :=
  0 ≤ t1 ∧ 0 ≤ t2 ∧ 0 ≤ t3 ∧ t1 ≤ 1 ∧ t2 ≤ 1 ∧ t3 ≤ 1 ∧ t1 + t2 + t3 ≤ 3 / 2

/-- **The Gram matrix of three vectors with pairwise obtuse (non-acute) angles lies in `P`.** -/
theorem inFibre_of_obtuse (a b c : ℝ³) (hab : ⟪a, b⟫ ≤ 0) (hac : ⟪a, c⟫ ≤ 0) (hbc : ⟪b, c⟫ ≤ 0) :
    InFibre (-(⟪a, b⟫ / (‖a‖ * ‖b‖))) (-(⟪a, c⟫ / (‖a‖ * ‖c‖))) (-(⟪b, c⟫ / (‖b‖ * ‖c‖))) := by
  have nn : ∀ p q : ℝ³, ⟪p, q⟫ ≤ 0 → 0 ≤ -(⟪p, q⟫ / (‖p‖ * ‖q‖)) := by
    intro p q h
    have : ⟪p, q⟫ / (‖p‖ * ‖q‖) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg h (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    linarith
  have le1 : ∀ p q : ℝ³, -(⟪p, q⟫ / (‖p‖ * ‖q‖)) ≤ 1 := fun p q =>
    by linarith [(abs_le.mp (abs_cos_le p q)).1]
  refine ⟨nn a b hab, nn a c hac, nn b c hbc, le1 a b, le1 a c, le1 b c, ?_⟩
  linarith [cosine_sum_ge a b c]

/-- **The sharp radius over `P`**: a linear form `Σ B_i t_i` with `B_i ≥ 0` on `P` is at most
`max (B_1, B_2, B_3, B_i + B_j / 2)`. -/
theorem sum_le_vertex_max_sorted {B1 B2 B3 t1 t2 t3 : ℝ} (h12 : B2 ≤ B1) (h23 : B3 ≤ B2)
    (h3 : 0 ≤ B3) (ht : InFibre t1 t2 t3) : B1 * t1 + B2 * t2 + B3 * t3 ≤ B1 + B2 / 2 := by
  obtain ⟨p1, p2, p3, q1, q2, q3, s⟩ := ht
  nlinarith [mul_le_mul_of_nonneg_left q1 (sub_nonneg.2 h12),
    mul_le_mul_of_nonneg_left (show t1 + t2 ≤ 3 / 2 by linarith) (sub_nonneg.2 h23),
    mul_le_mul_of_nonneg_left s h3]

/-- The vertex maximum `max (B_1, B_2, B_3, B_i + B_j / 2)` of a nonnegative linear form on `P`
(the unit points are dominated by `B_i + B_j / 2`, but are kept for the statement). -/
noncomputable def vertexMax (B1 B2 B3 : ℝ) : ℝ :=
  max (max (max B1 B2) B3)
    (max (max (max (B1 + B2 / 2) (B2 + B1 / 2)) (max (B1 + B3 / 2) (B3 + B1 / 2)))
      (max (B2 + B3 / 2) (B3 + B2 / 2)))

theorem sum_le_vertexMax {B1 B2 B3 t1 t2 t3 : ℝ} (h1 : 0 ≤ B1) (h2 : 0 ≤ B2) (h3 : 0 ≤ B3)
    (ht : InFibre t1 t2 t3) : B1 * t1 + B2 * t2 + B3 * t3 ≤ vertexMax B1 B2 B3 := by
  obtain ⟨p1, p2, p3, q1, q2, q3, s⟩ := ht
  have m12 : B1 + B2 / 2 ≤ vertexMax B1 B2 B3 := by unfold vertexMax; simp [le_max_iff]
  have m21 : B2 + B1 / 2 ≤ vertexMax B1 B2 B3 := by unfold vertexMax; simp [le_max_iff]
  have m13 : B1 + B3 / 2 ≤ vertexMax B1 B2 B3 := by unfold vertexMax; simp [le_max_iff]
  have m31 : B3 + B1 / 2 ≤ vertexMax B1 B2 B3 := by unfold vertexMax; simp [le_max_iff]
  have m23 : B2 + B3 / 2 ≤ vertexMax B1 B2 B3 := by unfold vertexMax; simp [le_max_iff]
  have m32 : B3 + B2 / 2 ≤ vertexMax B1 B2 B3 := by unfold vertexMax; simp [le_max_iff]
  rcases le_total B1 B2 with a | a <;> rcases le_total B2 B3 with b | b <;>
    rcases le_total B1 B3 with c | c
  · linarith [sum_le_vertex_max_sorted (t1 := t3) (t2 := t2) (t3 := t1) b a h1
      ⟨p3, p2, p1, q3, q2, q1, by linarith⟩]
  · linarith [sum_le_vertex_max_sorted (t1 := t3) (t2 := t2) (t3 := t1) b a h1
      ⟨p3, p2, p1, q3, q2, q1, by linarith⟩]
  · linarith [sum_le_vertex_max_sorted (t1 := t2) (t2 := t3) (t3 := t1) b c h1
      ⟨p2, p3, p1, q2, q3, q1, by linarith⟩]
  · linarith [sum_le_vertex_max_sorted (t1 := t2) (t2 := t1) (t3 := t3) a c h3
      ⟨p2, p1, p3, q2, q1, q3, by linarith⟩]
  · linarith [sum_le_vertex_max_sorted (t1 := t3) (t2 := t1) (t3 := t2) c a h2
      ⟨p3, p1, p2, q3, q1, q2, by linarith⟩]
  · linarith [sum_le_vertex_max_sorted (t1 := t1) (t2 := t3) (t3 := t2) c b h2
      ⟨p1, p3, p2, q1, q3, q2, by linarith⟩]
  · linarith [sum_le_vertex_max_sorted (t1 := t1) (t2 := t2) (t3 := t3) a b h3
      ⟨p1, p2, p3, q1, q2, q3, by linarith⟩]
  · linarith [sum_le_vertex_max_sorted (t1 := t1) (t2 := t2) (t3 := t3) a b h3
      ⟨p1, p2, p3, q1, q2, q3, by linarith⟩]

/-- **The radius over `P`**: if `t ∈ P`, `ρ_i ≥ 0`, `h_i = −t_i ρ_i` and
`vertexMax (max 0 b_i · ρ_i) < ℓ⁰`, then `ℓ⁰ + Σ b_i h_i > 0`. -/
theorem radius_pos_fibre {l0 b1 b2 b3 t1 t2 t3 r1 r2 r3 : ℝ} (hr1 : 0 ≤ r1) (hr2 : 0 ≤ r2)
    (hr3 : 0 ≤ r3) (ht : InFibre t1 t2 t3)
    (hl : vertexMax (max 0 b1 * r1) (max 0 b2 * r2) (max 0 b3 * r3) < l0) :
    0 < l0 + b1 * (-(t1 * r1)) + b2 * (-(t2 * r2)) + b3 * (-(t3 * r3)) := by
  obtain ⟨p1, p2, p3, -⟩ := id ht
  have k : ∀ b t r : ℝ, 0 ≤ t → 0 ≤ r → -(max 0 b * r * t) ≤ b * (-(t * r)) := by
    intro b t r ht hr
    have := mul_nonneg ht hr
    nlinarith [le_max_right 0 b, mul_le_mul_of_nonneg_right (le_max_right 0 b) this]
  have hs := sum_le_vertexMax (mul_nonneg (le_max_left 0 b1) hr1)
    (mul_nonneg (le_max_left 0 b2) hr2) (mul_nonneg (le_max_left 0 b3) hr3) ht
  nlinarith [k b1 t1 r1 p1 hr1, k b2 t2 r2 p2 hr2, k b3 t3 r3 p3 hr3]

/-! ### The corner frame and the snap -/

/-- **A corner frame**: three axes `e_a, e_b, e_c` of a vertex and the frame coordinates of the
vertices of the solid (`x v − x w = Σ (X_i v − X_i w) e_i`, see `Corner.Rep`). -/
structure Corner (ι : Type*) where
  ea : ℝ³
  eb : ℝ³
  ec : ℝ³
  Xa : ι → ℝ
  Xb : ι → ℝ
  Xc : ι → ℝ

variable {ι : Type*}

/-- The frame coordinates represent the points `x`. -/
def Corner.Rep (C : Corner ι) (x : ι → ℝ³) : Prop :=
  ∀ v w, x v - x w = (C.Xa v - C.Xa w) • C.ea + (C.Xb v - C.Xb w) • C.eb +
    (C.Xc v - C.Xc w) • C.ec

/-- The space view of oblique view coordinates `d`. -/
noncomputable def Corner.view (C : Corner ι) (d : Fin 3 → ℝ) : ℝ³ :=
  d 0 • C.ea + d 1 • C.eb + d 2 • C.ec

/-- **The snap depth** (depth at the exact corner, same oblique coordinates and axis lengths). -/
noncomputable def Corner.snapDepth (C : Corner ι) (d : Fin 3 → ℝ) (v : ι) : ℝ :=
  d 0 * ‖C.ea‖ ^ 2 * C.Xa v + d 1 * ‖C.eb‖ ^ 2 * C.Xb v + d 2 * ‖C.ec‖ ^ 2 * C.Xc v

/-- The coefficient of `h_ab = ⟪e_a, e_b⟫` in `z_v − z_w` at the view `d` (17.1). -/
noncomputable def Corner.cosCoefAB (C : Corner ι) (d : Fin 3 → ℝ) (v w : ι) : ℝ :=
  d 0 * (C.Xb v - C.Xb w) + d 1 * (C.Xa v - C.Xa w)

/-- The coefficient of `h_ac`. -/
noncomputable def Corner.cosCoefAC (C : Corner ι) (d : Fin 3 → ℝ) (v w : ι) : ℝ :=
  d 0 * (C.Xc v - C.Xc w) + d 2 * (C.Xa v - C.Xa w)

/-- The coefficient of `h_bc`. -/
noncomputable def Corner.cosCoefBC (C : Corner ι) (d : Fin 3 → ℝ) (v w : ι) : ℝ :=
  d 1 * (C.Xc v - C.Xc w) + d 2 * (C.Xb v - C.Xb w)

/-- **Lemma F2 (ii) / 17.1 at any oblique view**: `z_v − z_w` is the snap depth difference plus
a form linear in the three axis inner products. -/
theorem Corner.Rep.depth_sub {C : Corner ι} {x : ι → ℝ³} (hC : C.Rep x) (d : Fin 3 → ℝ) (v w : ι) :
    ⟪x v, C.view d⟫ - ⟪x w, C.view d⟫ =
      (C.snapDepth d v - C.snapDepth d w) + C.cosCoefAB d v w * ⟪C.ea, C.eb⟫ +
        C.cosCoefAC d v w * ⟪C.ea, C.ec⟫ + C.cosCoefBC d v w * ⟪C.eb, C.ec⟫ := by
  rw [← inner_sub_left, hC v w]
  simp only [Corner.view]
  rw [inner_frame_diff, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
    real_inner_self_eq_norm_sq]
  simp only [Corner.snapDepth, Corner.cosCoefAB, Corner.cosCoefAC, Corner.cosCoefBC]
  ring

/-- **The octant box**: `h_ij ≤ 0` and `−h_ij ≤ δ L_i L_j`. -/
def Corner.ObtuseNear (C : Corner ι) (δ : ℝ) : Prop :=
  ⟪C.ea, C.eb⟫ ≤ 0 ∧ ⟪C.ea, C.ec⟫ ≤ 0 ∧ ⟪C.eb, C.ec⟫ ≤ 0 ∧
    -⟪C.ea, C.eb⟫ ≤ δ * (‖C.ea‖ * ‖C.eb‖) ∧ -⟪C.ea, C.ec⟫ ≤ δ * (‖C.ea‖ * ‖C.ec‖) ∧
    -⟪C.eb, C.ec⟫ ≤ δ * (‖C.eb‖ * ‖C.ec‖)

/-- **`v` above `w` at the snap, box radius `δ`** (17.1′). -/
def Corner.SnapAbove (C : Corner ι) (d : Fin 3 → ℝ) (δ : ℝ) (v w : ι) : Prop :=
  δ * (max 0 (C.cosCoefAB d v w) * (‖C.ea‖ * ‖C.eb‖) +
      max 0 (C.cosCoefAC d v w) * (‖C.ea‖ * ‖C.ec‖) +
      max 0 (C.cosCoefBC d v w) * (‖C.eb‖ * ‖C.ec‖)) < C.snapDepth d v - C.snapDepth d w

/-- **`v` above `w` at the snap, over the whole fibre polytope `P`** (Lemma F1): the sharp
radius `max (B_1, B_2, B_3, B_i + B_j / 2)`, `B_i = max 0 β_i · ρ_i`, in place of
`δ (B_1 + B_2 + B_3)`.  No `δ`: it holds for every obtuse corner. -/
def Corner.SnapAbove' (C : Corner ι) (d : Fin 3 → ℝ) (v w : ι) : Prop :=
  vertexMax (max 0 (C.cosCoefAB d v w) * (‖C.ea‖ * ‖C.eb‖))
      (max 0 (C.cosCoefAC d v w) * (‖C.ea‖ * ‖C.ec‖))
      (max 0 (C.cosCoefBC d v w) * (‖C.eb‖ * ‖C.ec‖)) < C.snapDepth d v - C.snapDepth d w

/-- **Corollary 17.1′ for one pair, box radius.** -/
theorem Corner.Rep.depth_lt_of_snapAbove {C : Corner ι} {x : ι → ℝ³} (hC : C.Rep x)
    {d : Fin 3 → ℝ} {δ : ℝ} {v w : ι} (hn : C.ObtuseNear δ) (h : C.SnapAbove d δ v w) :
    ⟪x w, C.view d⟫ < ⟪x v, C.view d⟫ := by
  obtain ⟨n1, n2, n3, h1, h2, h3⟩ := hn
  have := radius_pos_octant n1 n2 n3 h1 h2 h3 h
  linarith [hC.depth_sub d v w]

/-- **The same over the whole fibre polytope `P`**: a pair above at the snap in the
`SnapAbove'` sense stays ordered at every obtuse corner (any lengths, any cosines). -/
theorem Corner.Rep.depth_lt_of_snapAbove' {C : Corner ι} {x : ι → ℝ³} (hC : C.Rep x)
    {d : Fin 3 → ℝ} {v w : ι} (hn : ⟪C.ea, C.eb⟫ ≤ 0 ∧ ⟪C.ea, C.ec⟫ ≤ 0 ∧ ⟪C.eb, C.ec⟫ ≤ 0)
    (h : C.SnapAbove' d v w) : ⟪x w, C.view d⟫ < ⟪x v, C.view d⟫ := by
  obtain ⟨n1, n2, n3⟩ := hn
  have hP := inFibre_of_obtuse C.ea C.eb C.ec n1 n2 n3
  have e1 := inner_eq_cos_mul C.ea C.eb
  have e2 := inner_eq_cos_mul C.ea C.ec
  have e3 := inner_eq_cos_mul C.eb C.ec
  have key := radius_pos_fibre (b1 := C.cosCoefAB d v w) (b2 := C.cosCoefAC d v w)
    (b3 := C.cosCoefBC d v w) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    hP h
  have eq1 : ⟪C.ea, C.eb⟫ = -(-(⟪C.ea, C.eb⟫ / (‖C.ea‖ * ‖C.eb‖)) * (‖C.ea‖ * ‖C.eb‖)) := by
    rw [neg_mul, neg_neg]; exact e1
  have eq2 : ⟪C.ea, C.ec⟫ = -(-(⟪C.ea, C.ec⟫ / (‖C.ea‖ * ‖C.ec‖)) * (‖C.ea‖ * ‖C.ec‖)) := by
    rw [neg_mul, neg_neg]; exact e2
  have eq3 : ⟪C.eb, C.ec⟫ = -(-(⟪C.eb, C.ec⟫ / (‖C.eb‖ * ‖C.ec‖)) * (‖C.eb‖ * ‖C.ec‖)) := by
    rw [neg_mul, neg_neg]; exact e3
  have := hC.depth_sub d v w
  rw [eq1, eq2, eq3] at this
  linarith

/-! ### The type-free snap lemma -/

/-- **A certified rim plus a strict order relation**: if `A v w` implies `z_w < z_v` at `u`, a rim
(`k ≥ 4`, depths open) whose every failure pattern has an `A`-pair is Rupert. -/
theorem isRupert_of_above [Fintype ι] {x : ι → ℝ³} {u : ℝ³} (A : ι → ι → Prop)
    (hA : ∀ v w, A v w → ⟪x w, u⟫ < ⟪x v, u⟫) {k : ℕ} [NeZero k] (hk : 4 ≤ k)
    {r : ZMod k → ι} (hR : Type24.RimTestR (univ.image x) u fun i => x (r i))
    (hpat : ∀ (B : ZMod k) (a b c e : ℕ), a < b → b < c → c < e → e < k →
      (A (r (B + b)) (r (B + a)) ∨ A (r (B + b)) (r (B + c)) ∨
        A (r (B + e)) (r (B + a)) ∨ A (r (B + e)) (r (B + c))) ∧
      (A (r (B + a)) (r (B + b)) ∨ A (r (B + a)) (r (B + e)) ∨
        A (r (B + c)) (r (B + b)) ∨ A (r (B + c)) (r (B + e)))) :
    IsRupert (univ.image x) := by
  refine hR.isRupert (Type24.NoWeakSep.isRobustUnimodal hk ?_)
  intro B a b c e h1 h2 h3 h4
  obtain ⟨p1, p2⟩ := hpat B a b c e h1 h2 h3 h4
  simp only [max_le_iff, le_min_iff]
  constructor
  · rintro ⟨⟨u1, u2⟩, u3, u4⟩
    rcases p1 with k | k | k | k <;> linarith [hA _ _ k]
  · rintro ⟨⟨u1, u2⟩, u3, u4⟩
    rcases p2 with k | k | k | k <;> linarith [hA _ _ k]

/-- **The snap lemma at a degree-3 vertex, any polytope** (the type-free form of
`Type24.isRupert_type24_snap`): a certified rim at the oblique view `d` (`k ≥ 4`) whose every
failure pattern is broken at the snap with octant margin `δ` makes the solid Rupert on the whole
box `ObtuseNear δ`.  The vertex frame is the only structure used. -/
theorem isRupert_corner_snap [Fintype ι] {C : Corner ι} {x : ι → ℝ³} (hC : C.Rep x)
    (d : Fin 3 → ℝ) {k : ℕ} [NeZero k] (hk : 4 ≤ k) {r : ZMod k → ι}
    (hR : Type24.RimTestR (univ.image x) (C.view d) fun i => x (r i)) {δ : ℝ}
    (hn : C.ObtuseNear δ)
    (hpat : ∀ (B : ZMod k) (a b c e : ℕ), a < b → b < c → c < e → e < k →
      (C.SnapAbove d δ (r (B + b)) (r (B + a)) ∨ C.SnapAbove d δ (r (B + b)) (r (B + c)) ∨
        C.SnapAbove d δ (r (B + e)) (r (B + a)) ∨ C.SnapAbove d δ (r (B + e)) (r (B + c))) ∧
      (C.SnapAbove d δ (r (B + a)) (r (B + b)) ∨ C.SnapAbove d δ (r (B + a)) (r (B + e)) ∨
        C.SnapAbove d δ (r (B + c)) (r (B + b)) ∨ C.SnapAbove d δ (r (B + c)) (r (B + e)))) :
    IsRupert (univ.image x) :=
  isRupert_of_above (C.SnapAbove d δ) (fun _ _ h => hC.depth_lt_of_snapAbove hn h) hk hR hpat

/-- **The snap lemma over the whole fibre**: the same with `SnapAbove'`; the hypothesis on the
corner is only that the three angles are non-acute.  Rupert for every obtuse corner with the
given frame coordinates, any axis lengths and cosines. -/
theorem isRupert_corner_snap' [Fintype ι] {C : Corner ι} {x : ι → ℝ³} (hC : C.Rep x)
    (d : Fin 3 → ℝ) {k : ℕ} [NeZero k] (hk : 4 ≤ k) {r : ZMod k → ι}
    (hR : Type24.RimTestR (univ.image x) (C.view d) fun i => x (r i))
    (hn : ⟪C.ea, C.eb⟫ ≤ 0 ∧ ⟪C.ea, C.ec⟫ ≤ 0 ∧ ⟪C.eb, C.ec⟫ ≤ 0)
    (hpat : ∀ (B : ZMod k) (a b c e : ℕ), a < b → b < c → c < e → e < k →
      (C.SnapAbove' d (r (B + b)) (r (B + a)) ∨ C.SnapAbove' d (r (B + b)) (r (B + c)) ∨
        C.SnapAbove' d (r (B + e)) (r (B + a)) ∨ C.SnapAbove' d (r (B + e)) (r (B + c))) ∧
      (C.SnapAbove' d (r (B + a)) (r (B + b)) ∨ C.SnapAbove' d (r (B + a)) (r (B + e)) ∨
        C.SnapAbove' d (r (B + c)) (r (B + b)) ∨ C.SnapAbove' d (r (B + c)) (r (B + e)))) :
    IsRupert (univ.image x) :=
  isRupert_of_above (C.SnapAbove' d) (fun _ _ h => hC.depth_lt_of_snapAbove' hn h) hk hR hpat

end CornerSnap

namespace Type24
open CornerSnap

/-- The corner frame of a type 24 solid at its vertex `1`. -/
noncomputable def cornerOf (x : Fin 7 → ℝ³) : Corner (Fin 7) where
  ea := x 0 - x 1
  eb := x 2 - x 1
  ec := x 6 - x 1
  Xa := oblX0 x
  Xb := oblX2 x
  Xc := oblX6 x

theorem cornerOf_rep {x : Fin 7 → ℝ³} (T : Type24 x) : (cornerOf x).Rep x := fun v w =>
  T.diff_frame v w

/-- **`isRupert_type24_snap` is a corollary of the type-free `isRupert_corner_snap`.** -/
theorem isRupert_type24_snap_of_corner {x : Fin 7 → ℝ³} (T : Type24 x) (d : Fin 3 → ℝ)
    {k : ℕ} [NeZero k] (hk : 4 ≤ k) {r : ZMod k → Fin 7}
    (hR : RimTestR (Finset.univ.image x) (viewOf x d) fun i => x (r i)) {δ : ℝ}
    (hn : ObtuseNear x δ)
    (hpat : ∀ (B : ZMod k) (a b c e : ℕ), a < b → b < c → c < e → e < k →
      (SnapAbove x d δ (r (B + b)) (r (B + a)) ∨ SnapAbove x d δ (r (B + b)) (r (B + c)) ∨
        SnapAbove x d δ (r (B + e)) (r (B + a)) ∨ SnapAbove x d δ (r (B + e)) (r (B + c))) ∧
      (SnapAbove x d δ (r (B + a)) (r (B + b)) ∨ SnapAbove x d δ (r (B + a)) (r (B + e)) ∨
        SnapAbove x d δ (r (B + c)) (r (B + b)) ∨ SnapAbove x d δ (r (B + c)) (r (B + e)))) :
    IsRupert (Finset.univ.image x) :=
  isRupert_corner_snap (C := cornerOf x) T.cornerOf_rep d hk hR hn hpat

/-- **The fibre version for type 24**: no `δ`, every obtuse corner. -/
theorem isRupert_type24_snap' {x : Fin 7 → ℝ³} (T : Type24 x) (d : Fin 3 → ℝ)
    {k : ℕ} [NeZero k] (hk : 4 ≤ k) {r : ZMod k → Fin 7}
    (hR : RimTestR (Finset.univ.image x) (viewOf x d) fun i => x (r i))
    (hn : ⟪x 0 - x 1, x 2 - x 1⟫ ≤ 0 ∧ ⟪x 0 - x 1, x 6 - x 1⟫ ≤ 0 ∧ ⟪x 2 - x 1, x 6 - x 1⟫ ≤ 0)
    (hpat : ∀ (B : ZMod k) (a b c e : ℕ), a < b → b < c → c < e → e < k →
      ((cornerOf x).SnapAbove' d (r (B + b)) (r (B + a)) ∨
        (cornerOf x).SnapAbove' d (r (B + b)) (r (B + c)) ∨
        (cornerOf x).SnapAbove' d (r (B + e)) (r (B + a)) ∨
        (cornerOf x).SnapAbove' d (r (B + e)) (r (B + c))) ∧
      ((cornerOf x).SnapAbove' d (r (B + a)) (r (B + b)) ∨
        (cornerOf x).SnapAbove' d (r (B + a)) (r (B + e)) ∨
        (cornerOf x).SnapAbove' d (r (B + c)) (r (B + b)) ∨
        (cornerOf x).SnapAbove' d (r (B + c)) (r (B + e)))) :
    IsRupert (Finset.univ.image x) :=
  isRupert_corner_snap' (C := cornerOf x) T.cornerOf_rep d hk hR hn hpat

end Type24


end Minimality
