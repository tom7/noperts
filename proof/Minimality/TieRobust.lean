module

public import Minimality.TieForces

@[expose] public section

/-!
# Lemma T at the tie, robust form: the geometric layer

Views `tw v ε = e_z + ε v`; every quantity the scalar core `tie_core` needs
is a polynomial in `ε`, so its eventual bounds come from two elementary
facts (`ev_half`, `ev_abs_quad`).
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

/-- The tilted view `e_z + ε v`. -/
noncomputable def tw (v : ℝ³) (ε : ℝ) : ℝ³ := ez + ε • v

theorem ev_half {A B : ℝ} (h : 0 < A) : ∀ᶠ ε in 𝓝[>] (0 : ℝ), A / 2 ≤ A + ε * B := by
  have hc : Continuous fun ε : ℝ => A + ε * B := by fun_prop
  have : ∀ᶠ ε in 𝓝 (0 : ℝ), A / 2 < A + ε * B :=
    hc.continuousAt.eventually (lt_mem_nhds (by simp; linarith))
  exact (this.filter_mono nhdsWithin_le_nhds).mono fun _ h => h.le

theorem ev_le_one : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε ∧ ε ≤ 1 := by
  have h1 : ∀ᶠ ε in 𝓝 (0 : ℝ), ε < 1 := gt_mem_nhds (by norm_num : (0 : ℝ) < 1)
  filter_upwards [self_mem_nhdsWithin, h1.filter_mono nhdsWithin_le_nhds] with ε h0 h1
  exact ⟨h0, h1.le⟩

theorem ev_abs_quad (A B C : ℝ) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), |A + ε * B + ε ^ 2 * C| ≤ |A| + |B| + |C| := by
  filter_upwards [ev_le_one] with ε ⟨h0, h1⟩
  have e1 : |ε * B| ≤ |B| := by
    rw [abs_mul, abs_of_pos h0]; exact mul_le_of_le_one_left (abs_nonneg _) h1
  have e2 : |ε ^ 2 * C| ≤ |C| := by
    rw [abs_mul, abs_of_pos (by positivity)]
    exact mul_le_of_le_one_left (abs_nonneg _) (by nlinarith)
  calc |A + ε * B + ε ^ 2 * C| ≤ |A| + |ε * B| + |ε ^ 2 * C| :=
        (abs_add_le _ _).trans (by gcongr; exact abs_add_le _ _)
    _ ≤ _ := by linarith

theorem ev_small {k : ℝ} : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε * k < 1 := by
  have hc : Continuous fun ε : ℝ => ε * k := by fun_prop
  exact (hc.continuousAt.eventually (gt_mem_nhds (by simp))).filter_mono nhdsWithin_le_nhds

theorem inner_tw (x v : ℝ³) (ε : ℝ) : ⟪x, tw v ε⟫ = x 2 + ε * ⟪x, v⟫ := by
  rw [tw, inner_add_right, real_inner_smul_right, inner_ez]

theorem cross_tw_left (v d : ℝ³) (ε : ℝ) : cross (tw v ε) d = cross ez d + ε • cross v d := by
  ext i; fin_cases i <;> simp [tw, cross, ez] <;> ring

theorem cross_tw_right (v d : ℝ³) (ε : ℝ) : cross d (tw v ε) = cross d ez + ε • cross d v := by
  ext i; fin_cases i <;> simp [tw, cross, ez] <;> ring

theorem cross_swap (a b : ℝ³) : cross a b = -cross b a := by
  ext i; fin_cases i <;> simp [cross] <;> ring

theorem cross_neg_sub (w a b : ℝ³) : cross w (a - b) = cross (b - a) w := by
  ext i; fin_cases i <;> simp [cross] <;> ring

/-- Inner products of a tilted generator with a fixed vector are affine in `ε`. -/
theorem inner_gen_left (v d x : ℝ³) (ε : ℝ) :
    ⟪cross (tw v ε) d, x⟫ = ⟪cross ez d, x⟫ + ε * ⟪cross v d, x⟫ := by
  rw [cross_tw_left, inner_add_left, real_inner_smul_left]

theorem inner_gen_right (v d x : ℝ³) (ε : ℝ) :
    ⟪cross d (tw v ε), x⟫ = ⟪cross d ez, x⟫ + ε * ⟪cross d v, x⟫ := by
  rw [cross_tw_right, inner_add_left, real_inner_smul_left]

/-- Torques of tilted generators are quadratic in `ε`. -/
theorem torque_quad (y G0 G1 v : ℝ³) (ε : ℝ) :
    ⟪cross y (G0 + ε • G1), ez + ε • v⟫ =
      ⟪cross y G0, ez⟫ + ε * (⟪cross y G1, ez⟫ + ⟪cross y G0, v⟫) + ε ^ 2 * ⟪cross y G1, v⟫ := by
  have : cross y (G0 + ε • G1) = cross y G0 + ε • cross y G1 := by
    ext i; fin_cases i <;> simp [cross] <;> ring
  rw [this]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
  ring

/-- A force system at the view `w` (`isRupert_of_no_forces`). -/
def IsForceSys (V : Finset ℝ³) (w : ℝ³) (F : ℝ³ → ℝ³) : Prop :=
  (∀ v ∈ V, ⟪F v, w⟫ = 0) ∧ (∀ v ∈ V, ∀ y ∈ V, ⟪F v, y - v⟫ ≤ 0) ∧
    ∑ v ∈ V, F v = 0 ∧ ∑ v ∈ V, ⟪v, w⟫ • F v = 0 ∧ ∑ v ∈ V, ⟪cross v (F v), w⟫ = 0

/-- A sum over `V` of a function vanishing off `X ∪ {a, b}`. -/
theorem sum_split {M : Type*} [AddCommMonoid M] (V X : Finset ℝ³) {a b : ℝ³} (φ : ℝ³ → M)
    (hXV : X ⊆ V) (ha : a ∈ V) (hb : b ∈ V) (hab : a ≠ b) (haX : a ∉ X) (hbX : b ∉ X)
    (h0 : ∀ y ∈ V, y ∉ X → y ≠ a → y ≠ b → φ y = 0) :
    ∑ y ∈ V, φ y = ∑ y ∈ X, φ y + φ a + φ b := by
  classical
  have hS : insert a (insert b X) ⊆ V := by
    intro y hy
    rcases mem_insert.mp hy with rfl | hy
    · exact ha
    rcases mem_insert.mp hy with rfl | hy
    · exact hb
    · exact hXV hy
  rw [← sum_subset hS (fun y hy hyS => h0 y hy (fun h => hyS (by simp [h]))
    (fun h => hyS (by simp [h])) (fun h => hyS (by simp [h]))),
    sum_insert (by simp [hab, haX]), sum_insert hbX]
  abel

/-- The generators of the corners above the tie: `(y, false)` the normal
`w × (nb0 y - y)` of the edge into `y`, `(y, true)` the normal
`(nb1 y - y) × w` of the edge out of `y`. -/
noncomputable def tgen (nb0 nb1 : ℝ³ → ℝ³) (w : ℝ³) (j : ℝ³ × Bool) : ℝ³ :=
  if j.2 then cross (nb1 j.1 - j.1) w else cross w (nb0 j.1 - j.1)

/-- The first-order part of `tgen` along the tilt `v`. -/
noncomputable def tgen' (nb0 nb1 : ℝ³ → ℝ³) (v : ℝ³) (j : ℝ³ × Bool) : ℝ³ :=
  if j.2 then cross (nb1 j.1 - j.1) v else cross v (nb0 j.1 - j.1)

theorem tgen_tw (nb0 nb1 : ℝ³ → ℝ³) (v : ℝ³) (ε : ℝ) (j : ℝ³ × Bool) :
    tgen nb0 nb1 (tw v ε) j = tgen nb0 nb1 ez j + ε • tgen' nb0 nb1 v j := by
  unfold tgen tgen'
  split_ifs
  · exact cross_tw_right v _ ε
  · exact cross_tw_left v _ ε

/-- A finite family of positive numbers has a positive lower bound (`1/(Σ 1/f + 1)`). -/
theorem exists_pos_lower {α : Type*} (s : Finset α) (f : α → ℝ) (h : ∀ x ∈ s, 0 < f x) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ x ∈ s, κ ≤ f x := by
  have hS : 0 ≤ ∑ x ∈ s, 1 / f x := sum_nonneg fun x hx => (one_div_pos.mpr (h x hx)).le
  refine ⟨1 / (∑ x ∈ s, 1 / f x + 1), by positivity, fun x hxs => ?_⟩
  have hx := h x hxs
  have hle : 1 / f x ≤ ∑ y ∈ s, 1 / f y :=
    single_le_sum (f := fun y => 1 / f y) (fun y hy => (one_div_pos.mpr (h y hy)).le) hxs
  rw [div_le_iff₀ (by positivity)]
  have : f x * (1 / f x) = 1 := by field_simp
  nlinarith

/-- The far system's determinant: the far ends' generators `Ga` (at `a`), `G3`
(the edge `a b`), `Gb` (at `b`) by their screen components and torques. -/
noncomputable def farDet (Ga G3 Gb a b w : ℝ³) : ℝ :=
  Ga 0 * (G3 1 * ⟪cross b Gb, w⟫ - ⟪cross b G3, w⟫ * Gb 1) -
    Ga 1 * (G3 0 * ⟪cross b Gb, w⟫ - ⟪cross b G3, w⟫ * Gb 0) +
    ⟪cross a Ga, w⟫ * (G3 0 * Gb 1 - G3 1 * Gb 0)

theorem cross_add_smul_right (y G0 G1 : ℝ³) (s t : ℝ) :
    cross y (s • G0 + t • G1) = s • cross y G0 + t • cross y G1 := by
  ext i; fin_cases i <;> simp [cross] <;> ring

theorem inner_single0 (x : ℝ³) : ⟪x, EuclideanSpace.single 0 1⟫ = x 0 := by
  simp [PiLp.inner_apply, Fin.sum_univ_three]

theorem inner_single1 (x : ℝ³) : ⟪x, EuclideanSpace.single 1 1⟫ = x 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_three]

/-- Splitting a sum over the generators of `X`. -/
theorem sum_gen {M : Type*} [AddCommMonoid M] (X : Finset ℝ³) (φ : ℝ³ × Bool → M) :
    ∑ j ∈ X ×ˢ (univ : Finset Bool), φ j = ∑ y ∈ X, (φ (y, false) + φ (y, true)) := by
  rw [sum_product]; simp [Fintype.sum_bool, add_comm]

set_option maxHeartbeats 8000000 in
/-- **The robust tie at one view.** At a view `w`: the corners `X` (each
convex between its neighbours), the far ends `a` (between `a0` and `b`) and
`b` (between `a` and `b1`), every other point inside a triangle of test
points; the scalar bounds of `tie_core` at `w`. Then every force system at
`w` vanishes. -/
theorem tie_no_forces_at (V X : Finset ℝ³) (w a b a0 b1 m p : ℝ³) (nb0 nb1 : ℝ³ → ℝ³)
    (hXV : X ⊆ V) (ha : a ∈ V) (hb : b ∈ V) (hab : a ≠ b) (haX : a ∉ X) (hbX : b ∉ X)
    (ha0 : a0 ∈ V) (hb1 : b1 ∈ V) (hnb0 : ∀ y ∈ X, nb0 y ∈ V) (hnb1 : ∀ y ∈ X, nb1 y ∈ V)
    (hconvX : ∀ y ∈ X, 0 < det3 (nb1 y - y) (nb0 y - y) w)
    (hconva : 0 < det3 (b - a) (a0 - a) w) (hconvb : 0 < det3 (b1 - b) (a - b) w)
    (hin : ∀ y ∈ V, y ∉ X → y ≠ a → y ≠ b → ∃ q1 ∈ V, ∃ q2 ∈ V, ∃ q3 ∈ V,
      0 < det3 (q2 - y) (q3 - y) w ∧ 0 < det3 (q3 - y) (q1 - y) w ∧ 0 < det3 (q1 - y) (q2 - y) w)
    (κ η Z K L c3 c : ℝ)
    (hκ : 0 < κ) (hη : 0 < η) (hc3 : 0 < c3) (hc : 0 < c) (hL : 0 ≤ L) (hZ : 0 ≤ Z)
    (hδ : 0 < ⟪b - a, w⟫)
    (hM : ∀ j ∈ X ×ˢ (univ : Finset Bool), κ ≤ ⟪tgen nb0 nb1 w j, m⟫)
    (hζ : ∀ y ∈ X, η ≤ ⟪y - a, w⟫) (hζZ : ∀ y ∈ X, ⟪y - a, w⟫ ≤ Z)
    (hP : ∀ j ∈ X ×ˢ (univ : Finset Bool), -(L * ⟪b - a, w⟫) ≤ ⟪tgen nb0 nb1 w j, p⟫)
    (hPK : ∀ j ∈ X ×ˢ (univ : Finset Bool), |⟪tgen nb0 nb1 w j, p⟫| ≤ K)
    (hX1 : ∀ j ∈ X ×ˢ (univ : Finset Bool), |tgen nb0 nb1 w j 0| ≤ K)
    (hX2 : ∀ j ∈ X ×ˢ (univ : Finset Bool), |tgen nb0 nb1 w j 1| ≤ K)
    (hT : ∀ j ∈ X ×ˢ (univ : Finset Bool), |⟪cross j.1 (tgen nb0 nb1 w j), w⟫| ≤ K)
    (hM3 : |⟪cross (b - a) w, m⟫| ≤ K) (hMb : |⟪cross (b1 - b) w, m⟫| ≤ K)
    (hPa : |⟪cross w (a0 - a), p⟫| ≤ L * ⟪b - a, w⟫) (hP3 : ⟪cross (b - a) w, p⟫ ≤ -c3)
    (hX13 : |cross (b - a) w 0| ≤ K) (hX23 : |cross (b - a) w 1| ≤ K)
    (hT3a : |⟪cross a (cross (b - a) w), w⟫| ≤ K)
    (hX1a : |cross w (a0 - a) 0| ≤ K) (hX2a : |cross w (a0 - a) 1| ≤ K)
    (hTa : |⟪cross a (cross w (a0 - a)), w⟫| ≤ K) (hT3b : |⟪cross b (cross (b - a) w), w⟫| ≤ K)
    (hX1b : |cross (b1 - b) w 0| ≤ K) (hX2b : |cross (b1 - b) w 1| ≤ K)
    (hTb : |⟪cross b (cross (b1 - b) w), w⟫| ≤ K)
    (hdet : c ≤ |farDet (cross w (a0 - a)) (cross (b - a) w) (cross (b1 - b) w) a b w|)
    (hsmall : ⟪b - a, w⟫ * (18 * K ^ 3 * (K / (η * κ) + ((K + L * Z) * K / (η * κ) + L) / c3) / c +
      ((K + L * Z) * K / (η * κ) + L) / c3) < 1)
    (F : ℝ³ → ℝ³) (hF : IsForceSys V w F) : ∀ y ∈ V, F y = 0 := by
  classical
  obtain ⟨hFw, hFn, hE1, hE2, hE3⟩ := hF
  set J := X ×ˢ (univ : Finset Bool) with hJ
  set G := tgen nb0 nb1 w
  -- points off the silhouette carry no force
  have hzero : ∀ y ∈ V, y ∉ X → y ≠ a → y ≠ b → F y = 0 := by
    intro y hy hyX hya hyb
    obtain ⟨q1, hq1, q2, hq2, q3, hq3, d1, d2, d3⟩ := hin y hy hyX hya hyb
    exact force_eq_zero_of_inside d1 d2 d3 (hFw y hy) (hFn y hy q1 hq1) (hFn y hy q2 hq2)
      (hFn y hy q3 hq3)
  -- corner forces on their generators
  have hcone : ∀ y ∈ X, ∃ s t : ℝ, 0 ≤ s ∧ 0 ≤ t ∧ F y = s • G (y, false) + t • G (y, true) := by
    intro y hy
    obtain ⟨s, t, hs, ht, e⟩ := force_mem_cone (hconvX y hy) (hFw y (hXV hy))
      (hFn y (hXV hy) _ (hnb1 y hy)) (hFn y (hXV hy) _ (hnb0 y hy))
    exact ⟨s, t, hs, ht, by simp only [G, tgen, ite_false, ite_true]; exact e⟩
  choose! s t hs ht hst using hcone
  obtain ⟨π1, π3, h1, h3, hFa⟩ := force_mem_cone hconva (hFw a ha) (hFn a ha b hb) (hFn a ha a0 ha0)
  obtain ⟨κ3, κ2, k3, k2, hFb⟩ := force_mem_cone hconvb (hFw b hb) (hFn b hb b1 hb1) (hFn b hb a ha)
  rw [cross_neg_sub] at hFb
  set Ga := cross w (a0 - a); set G3 := cross (b - a) w; set Gb := cross (b1 - b) w
  set δ := ⟪b - a, w⟫
  let l : ℝ³ × Bool → ℝ := fun j => if j.2 then t j.1 else s j.1
  have hFX : ∀ y ∈ X, F y = l (y, false) • G (y, false) + l (y, true) • G (y, true) := by
    intro y hy; simp only [l, ite_false, ite_true]; exact hst y hy
  -- sums over `V` split as `X`, `a`, `b`
  have split : ∀ {M : Type} [AddCommMonoid M] (φ : ℝ³ → M), (∀ y, F y = 0 → φ y = 0) →
      ∑ y ∈ V, φ y = ∑ y ∈ X, φ y + φ a + φ b := fun φ hφ =>
    sum_split V X φ hXV ha hb hab haX hbX fun y hy h1 h2 h3 => hφ y (hzero y hy h1 h2 h3)
  -- scalar equations
  have lin : ∀ x : ℝ³, ∑ y ∈ X, ⟪F y, x⟫ = ∑ j ∈ J, l j * ⟪G j, x⟫ := by
    intro x
    rw [hJ, sum_gen]
    refine sum_congr rfl fun y hy => ?_
    rw [hFX y hy, inner_add_left, real_inner_smul_left, real_inner_smul_left]
  have E1d : ∀ x : ℝ³, ∑ j ∈ J, l j * ⟪G j, x⟫ + π1 * ⟪Ga, x⟫ + (π3 + κ3) * ⟪G3, x⟫ +
      κ2 * ⟪Gb, x⟫ = 0 := by
    intro x
    have h := congrArg (fun z => ⟪z, x⟫) hE1
    simp only [sum_inner, inner_zero_left] at h
    rw [split (fun y => ⟪F y, x⟫) (fun y hy => by rw [hy, inner_zero_left]), lin, hFa, hFb] at h
    simp only [inner_add_left, real_inner_smul_left] at h
    linarith
  have E2r : ∑ y ∈ V, ⟪y - a, w⟫ • F y = 0 := by
    have : ∑ y ∈ V, ⟪y - a, w⟫ • F y = ∑ y ∈ V, ⟪y, w⟫ • F y - ⟪a, w⟫ • ∑ y ∈ V, F y := by
      rw [smul_sum, ← sum_sub_distrib]
      exact sum_congr rfl fun y _ => by rw [inner_sub_left, sub_smul]
    rw [this, hE2, hE1, smul_zero, sub_zero]
  have E2d : ∀ x : ℝ³, ∑ j ∈ J, l j * ⟪j.1 - a, w⟫ * ⟪G j, x⟫ + δ * (κ3 * ⟪G3, x⟫ + κ2 * ⟪Gb, x⟫) = 0 := by
    intro x
    have h := congrArg (fun z => ⟪z, x⟫) E2r
    simp only [sum_inner, inner_zero_left, real_inner_smul_left] at h
    rw [split (fun y => ⟪y - a, w⟫ * ⟪F y, x⟫) (fun y hy => by rw [hy, inner_zero_left, mul_zero]),
      sub_self, inner_zero_left, zero_mul, add_zero, hFb] at h
    have hX : ∑ y ∈ X, ⟪y - a, w⟫ * ⟪F y, x⟫ = ∑ j ∈ J, l j * ⟪j.1 - a, w⟫ * ⟪G j, x⟫ := by
      rw [hJ, sum_gen]
      refine sum_congr rfl fun y hy => ?_
      rw [hFX y hy, inner_add_left, real_inner_smul_left, real_inner_smul_left]; ring
    rw [hX] at h
    simp only [inner_add_left, real_inner_smul_left] at h
    linarith
  have E3d : ∑ j ∈ J, l j * ⟪cross j.1 (G j), w⟫ + π1 * ⟪cross a Ga, w⟫ + π3 * ⟪cross a G3, w⟫ +
      κ3 * ⟪cross b G3, w⟫ + κ2 * ⟪cross b Gb, w⟫ = 0 := by
    rw [split (fun y => ⟪cross y (F y), w⟫) (fun y hy => by
      rw [hy]; simp [cross, PiLp.inner_apply, Fin.sum_univ_three])] at hE3
    have hX : ∑ y ∈ X, ⟪cross y (F y), w⟫ = ∑ j ∈ J, l j * ⟪cross j.1 (G j), w⟫ := by
      rw [hJ, sum_gen]
      refine sum_congr rfl fun y hy => ?_
      rw [hFX y hy, cross_add_smul_right, inner_add_left, real_inner_smul_left,
        real_inner_smul_left]
    rw [hX, hFa, hFb, cross_add_smul_right, cross_add_smul_right] at hE3
    simp only [inner_add_left, real_inner_smul_left] at hE3
    linarith
  -- the scalar core
  have hl : ∀ j ∈ J, 0 ≤ l j := by
    intro j hj
    obtain ⟨hy, -⟩ := mem_product.mp hj
    simp only [l]; split_ifs
    exacts [ht j.1 hy, hs j.1 hy]
  have core := tie_core J l (fun j => ⟪j.1 - a, w⟫) (fun j => ⟪G j, m⟫) (fun j => ⟪G j, p⟫)
    (fun j => G j 0) (fun j => G j 1) (fun j => ⟪cross j.1 (G j), w⟫) π1 π3 κ3 κ2 δ
    ⟪G3, m⟫ ⟪Gb, m⟫ ⟪Ga, p⟫ ⟪G3, p⟫ ⟪Gb, p⟫ (Ga 0) (G3 0) (Gb 0) (Ga 1) (G3 1) (Gb 1)
    ⟪cross a Ga, w⟫ ⟪cross a G3, w⟫ ⟪cross b G3, w⟫ ⟪cross b Gb, w⟫ κ η Z K L c3 c
    hl h1 h3 k3 k2 hκ hη hc3 hc hδ hL hZ hM
    (fun j hj => hζ j.1 (mem_product.mp hj).1) (fun j hj => hζZ j.1 (mem_product.mp hj).1)
    hP hPK hX1 hX2 hT hM3 hMb hPa hP3 hX13 hX23 hT3a hX1a hX2a hTa hT3b hX1b hX2b hTb
    (by simpa [farDet] using hdet)
    (by have := E1d (EuclideanSpace.single 0 1); simpa [inner_single0] using this)
    (by have := E1d (EuclideanSpace.single 1 1); simpa [inner_single1] using this)
    (E1d p) (E2d m) (E2d p) E3d hsmall
  obtain ⟨hl0, hπ1, hπ3, hκ3, hκ2⟩ := core
  intro y hy
  by_cases hyX : y ∈ X
  · rw [hFX y hyX, hl0 _ (mem_product.mpr ⟨hyX, mem_univ _⟩),
      hl0 _ (mem_product.mpr ⟨hyX, mem_univ _⟩), zero_smul, zero_smul, add_zero]
  by_cases hya : y = a
  · rw [hya, hFa, hπ1, hπ3, zero_smul, zero_smul, add_zero]
  by_cases hyb : y = b
  · rw [hyb, hFb, hκ3, hκ2, zero_smul, zero_smul, add_zero]
  exact hzero y hy hyX hya hyb

end Minimality

end
