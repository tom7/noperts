module

public import Mathlib
public import Minimality.RimCellPerp

@[expose] public section

/-!
# The corner-normal cone lemma (Lemma N, "PP*")

Setting: `y : ZMod k → ℝ³` is the rim of a cell, `Y` the point set.  For a view `u`,
`omega u x z = det (x, z, u)`.  `convSet y = {u | ∀ i, 0 < omega u (y (i+1) - y i) (y (i+2) - y i)}`
is the cone of views along which every consecutive triple of the rim turns left (the open cone
`Conv(R) = {u | ν_i ⬝ u > 0}` of the corner normals).

* `edge_pos_of_weak`: **the local-to-global step, without turning numbers.**  If all consecutive
  triples turn strictly left and all cyclically ordered triples turn weakly left, then all
  triples `(i, i+1, j)` turn strictly left.  Proof: if `j` lies on the line through the edge
  `(i, i+1)`, the two neighbouring corners `i+2` and `i-1` are strictly on the left, and the
  weak triples `(i, i+2, j)` and `(i+1, j, i-1)` place `j` both at or before `i` and at or after
  `i+1` on that line (a Plücker relation for the 2-form `omega u`).
* `strict_of_conv_path`: **(1) of Lemma N.**  If the rim is strictly convex along `p` and
  `c ∈ convSet y`, it is strictly convex along `c` (all cyclically ordered triples positive).
  Route: the path `(1-t) p + t c` stays in `convSet` (convex); the set of `t` where all triples
  are positive is open, and closed because weak positivity in the limit plus
  `edge_pos_of_weak` gives strict positivity.  No turning numbers; connectedness of `[0,1]` only.
* `isRupert_of_conv_pair`: **(2)**.  `p` interior to a cell `A` (orientation inequalities of the
  rim `y`), `c ∈ convSet y`, `((Eᵀ E) c) ⬝ᵥ p = 0` (views orthogonal): `E Y` is Rupert.
  Generic perturbation of `p` (and `c`, to keep orthogonality) gives distinct depths; the
  equator lemma `isCyclicUnimodal_perp` finishes.
* `isRupert_of_conv_pair_closure`: **(3)**, the checkable form: `ρ ∈ closure A`,
  `σ ∈ closure (convSet y)`, `((Eᵀ E) σ) ⬝ᵥ ρ < 0` give Rupert, where `A = cellSet Y y`.
-/

set_option autoImplicit false

namespace Minimality.RimCell

open Finset Matrix Filter Topology MeasureTheory
open scoped RealInnerProductSpace

/-- The orientation form of the view `u`: `omega u x z = det (x, z, u)`. -/
noncomputable def omega (u x z : Fin 3 → ℝ) : ℝ := (Matrix.of ![x, z, u]).det

theorem omega_comb (a b : ℝ) (p c x z : Fin 3 → ℝ) :
    omega (a • p + b • c) x z = a * omega p x z + b * omega c x z := by
  simp only [omega, Matrix.det_fin_three]; simp; ring

theorem continuous_omega (x z : Fin 3 → ℝ) : Continuous fun u => omega u x z := by
  simp only [omega, Matrix.det_fin_three]; simp; fun_prop

/-- The Plücker relation for the 2-form `omega u`, in the contradiction form used below. -/
theorem omega_key (u d a b w : Fin 3 → ℝ) (hα : 0 < omega u d a) (hβ : 0 < omega u d b)
    (hγ : 0 ≤ omega u a w) (hδ : 0 ≤ omega u (w - d) (b - d)) (hw : omega u d w = 0) :
    False := by
  have hP : omega u d a * omega u b w - omega u d b * omega u a w
      + omega u d w * omega u a b = 0 := by
    simp only [omega, Matrix.det_fin_three]; simp; ring
  have hδ' : omega u (w - d) (b - d) = - omega u b w + omega u d w - omega u d b := by
    simp only [omega, Matrix.det_fin_three]; simp; ring
  have h1 : omega u b w < 0 := by rw [hδ', hw] at hδ; linarith
  have h2 := mul_neg_of_pos_of_neg hα h1
  have h3 := mul_nonneg hβ.le hγ
  rw [hw] at hP
  nlinarith

theorem two_ne {k : ℕ} (hk : 3 ≤ k) (i : ZMod k) : i + 2 ≠ i ∧ i + 2 ≠ i + 1 := by
  constructor
  · have := zmod_add_ne (k := k) (a := 2) (b := 0) (by omega) (by omega) (by omega) i
    simpa using this
  · have := zmod_add_ne (k := k) (a := 2) (b := 1) (by omega) (by omega) (by omega) i
    simpa using this

/-- **Local-to-global step.**  Consecutive triples strictly left and all cyclic triples weakly
left force strict positivity of every triple `(i, i+1, j)`. -/
theorem edge_pos_of_weak {k : ℕ} [NeZero k] (hk : 3 ≤ k) (y : ZMod k → Fin 3 → ℝ)
    (u : Fin 3 → ℝ)
    (h1 : ∀ i, 0 < omega u (y (i + 1) - y i) (y (i + 2) - y i))
    (h2 : ∀ i j l, CycBetween i j l → 0 ≤ omega u (y j - y i) (y l - y i))
    (i j : ZMod k) (hj1 : j ≠ i) (hj2 : j ≠ i + 1) :
    0 < omega u (y (i + 1) - y i) (y j - y i) := by
  by_contra hneg
  have hw : omega u (y (i + 1) - y i) (y j - y i) = 0 :=
    le_antisymm (not_lt.mp hneg) (h2 i (i + 1) j (cycBetween_succ hk i j hj1 hj2))
  have hα := h1 i
  have hβ : 0 < omega u (y (i + 1) - y i) (y (i - 1) - y i) := by
    have := h1 (i - 1)
    rw [sub_add_cancel, show i - 1 + 2 = i + 1 by ring] at this
    have e : omega u (y i - y (i - 1)) (y (i + 1) - y (i - 1)) =
        omega u (y (i + 1) - y i) (y (i - 1) - y i) := by
      simp only [omega, Matrix.det_fin_three]; simp; ring
    rwa [e] at this
  -- j is neither i+2 nor i-1
  have hj3 : j ≠ i + 2 := by
    rintro rfl; rw [hw] at hα; exact lt_irrefl _ hα
  have hj4 : j ≠ i - 1 := by
    rintro rfl; rw [hw] at hβ; exact lt_irrefl _ hβ
  set m := (j - i).val with hm
  have hmk : m < k := ZMod.val_lt _
  have hjm : j = i + (m : ZMod k) := by rw [hm, ZMod.natCast_zmod_val]; ring
  have hm0 : m ≠ 0 := fun h => hj1 (by rw [hjm, h]; simp)
  have hm1 : m ≠ 1 := fun h => hj2 (by rw [hjm, h]; simp)
  have hm2 : m ≠ 2 := fun h => hj3 (by rw [hjm, h]; push_cast; rfl)
  have hm3 : m ≠ k - 1 := fun h => hj4 (by
    rw [hjm, h, zmod_natCast_pred (by omega)]; ring)
  have hc1 : CycBetween i (i + 2) j := by
    have := cycBetween_of_lt i (a := 0) (b := 2) (c := m) (by omega) (by omega) hmk
    rw [← hjm] at this
    simpa using this
  have hc2 : CycBetween (i + 1) j (i - 1) := by
    have := cycBetween_of_lt (i + 1) (a := 0) (b := m - 1) (c := k - 2) (by omega) (by omega)
      (by omega)
    have e1 : i + 1 + ((m - 1 : ℕ) : ZMod k) = j := by
      rw [hjm, Nat.cast_sub (by omega : 1 ≤ m)]; push_cast; ring
    have e2 : i + 1 + ((k - 2 : ℕ) : ZMod k) = i - 1 := by
      rw [Nat.cast_sub (by omega : 2 ≤ k), ZMod.natCast_self]; push_cast; ring
    rw [e1, e2] at this
    simpa using this
  have hγ := h2 i (i + 2) j hc1
  have hδ := h2 (i + 1) j (i - 1) hc2
  rw [← sub_sub_sub_cancel_right (y j) (y (i + 1)) (y i),
    ← sub_sub_sub_cancel_right (y (i - 1)) (y (i + 1)) (y i)] at hδ
  exact omega_key u _ _ _ _ hα hβ hγ hδ hw


theorem exists_rot_cross2 (E : Matrix (Fin 3) (Fin 3) ℝ) (hE : 0 < E.det) (u : Fin 3 → ℝ)
    (hu : u ≠ 0) :
    ∃ R : Matrix (Fin 3) (Fin 3) ℝ, R ∈ SO3 ∧ ∃ r : ℝ, 0 < r ∧ ∀ a b : Fin 3 → ℝ,
      r * cross2 (proj_xy (R.toEuclideanLin (emb E a))) (proj_xy (R.toEuclideanLin (emb E b))) =
        E.det * omega u a b := by
  have hw0 : emb E u ≠ 0 := by
    intro h
    apply hu
    apply Matrix.eq_zero_of_mulVec_eq_zero hE.ne'
    ext i; simpa [emb_apply] using congrArg (fun v : ℝ³ => v i) h
  obtain ⟨R, hR, lam, hlam, hRw⟩ := exists_rotation_to_ez_pos _ hw0
  refine ⟨R, hR, lam, hlam, fun a b => ?_⟩
  rw [cross2_proj_rot hR hRw, det3_emb]; rfl

theorem omega_zero (x z : Fin 3 → ℝ) : omega 0 x z = 0 := by
  simp [omega, Matrix.det_fin_three]

theorem ne_zero_of_edge {k : ℕ} (hk : 3 ≤ k) (y : ZMod k → Fin 3 → ℝ) (u : Fin 3 → ℝ)
    (hedge : ∀ i j : ZMod k, j ≠ i → j ≠ i + 1 → 0 < omega u (y (i + 1) - y i) (y j - y i)) :
    u ≠ 0 := by
  rintro rfl
  have := hedge 0 2 (by simpa using (two_ne hk 0).1) (by simpa using (two_ne hk 0).2)
  rw [omega_zero] at this
  exact lt_irrefl _ this

/-- Strict positivity of the triples `(i, i+1, j)` along `u` gives all cyclically ordered
triples (the projected rim is a strictly convex polygon). -/
theorem triples_of_edge {k : ℕ} [NeZero k] (hk : 3 ≤ k) (y : ZMod k → Fin 3 → ℝ)
    (u : Fin 3 → ℝ)
    (hedge : ∀ i j : ZMod k, j ≠ i → j ≠ i + 1 → 0 < omega u (y (i + 1) - y i) (y j - y i)) :
    ∀ i j l, CycBetween i j l → 0 < omega u (y j - y i) (y l - y i) := by
  have hu := ne_zero_of_edge hk y u hedge
  obtain ⟨R, hR, r, hr, hrel⟩ := exists_rot_cross2 1 (by simp) u hu
  have e : ∀ i j : ZMod k, proj_xy (R.toEuclideanLin (emb 1 (y j))) -
      proj_xy (R.toEuclideanLin (emb 1 (y i))) = proj_xy (R.toEuclideanLin (emb 1 (y j - y i))) :=
    fun i j => by rw [proj_rot_sub, ← emb_sub]
  have hP : IsCcwPolygon (fun i => proj_xy (R.toEuclideanLin (emb 1 (y i)))) := by
    refine ⟨hk, fun i j hj1 hj2 => ?_⟩
    simp only [e]
    have := hrel (y (i + 1) - y i) (y j - y i)
    have h0 := hedge i j hj1 hj2
    simp only [Matrix.det_one, one_mul] at this
    exact pos_of_mul_pos_right (this ▸ h0) hr.le
  intro i j l h
  have h1 := hP.cross2_pos_of_cycBetween h
  simp only [e] at h1
  have := hrel (y j - y i) (y l - y i)
  simp only [Matrix.det_one, one_mul] at this
  rw [← this]; exact mul_pos hr h1


/-- The cone of views along which every consecutive triple of the rim turns left. -/
def convSet {k : ℕ} (y : ZMod k → Fin 3 → ℝ) : Set (Fin 3 → ℝ) :=
  {u | ∀ i, 0 < omega u (y (i + 1) - y i) (y (i + 2) - y i)}

theorem isOpen_convSet {k : ℕ} [NeZero k] (y : ZMod k → Fin 3 → ℝ) : IsOpen (convSet y) := by
  have : convSet y = ⋂ i : ZMod k, {u | 0 < omega u (y (i + 1) - y i) (y (i + 2) - y i)} := by
    ext u; simp [convSet]
  rw [this]
  exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (continuous_omega _ _)

/-- **(1) of Lemma N.**  If the rim is strictly convex along `p` (all `(i, i+1, j)` positive) and
`c` lies in `convSet y`, then all cyclically ordered triples of the rim are positive along `c`. -/
theorem strict_of_conv_path {k : ℕ} [NeZero k] (hk : 3 ≤ k) (y : ZMod k → Fin 3 → ℝ)
    (p c : Fin 3 → ℝ)
    (hp : ∀ i j : ZMod k, j ≠ i → j ≠ i + 1 → 0 < omega p (y (i + 1) - y i) (y j - y i))
    (hc : c ∈ convSet y) :
    ∀ i j l, CycBetween i j l → 0 < omega c (y j - y i) (y l - y i) := by
  let O : Set (Fin 3 → ℝ) := {u | ∀ i j l, CycBetween i j l → 0 < omega u (y j - y i) (y l - y i)}
  let C : Set (Fin 3 → ℝ) := {u | ∀ i j l, CycBetween i j l → 0 ≤ omega u (y j - y i) (y l - y i)}
  have hO : IsOpen O := by
    have : O = ⋂ i : ZMod k, ⋂ j : ZMod k, ⋂ l : ZMod k, ⋂ (_ : CycBetween i j l),
        {u | 0 < omega u (y j - y i) (y l - y i)} := by
      ext u; simp [O]
    rw [this]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      isOpen_iInter_of_finite fun l => isOpen_iInter_of_finite fun _ =>
        isOpen_lt continuous_const (continuous_omega _ _)
  have hC : IsClosed C := by
    have : C = ⋂ i : ZMod k, ⋂ j : ZMod k, ⋂ l : ZMod k, ⋂ (_ : CycBetween i j l),
        {u | 0 ≤ omega u (y j - y i) (y l - y i)} := by
      ext u; simp [C]
    rw [this]
    exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun l =>
      isClosed_iInter fun _ => isClosed_le continuous_const (continuous_omega _ _)
  have hpO : p ∈ O := triples_of_edge hk y p hp
  let u : unitInterval → (Fin 3 → ℝ) := fun t => (1 - (t : ℝ)) • p + (t : ℝ) • c
  have hu : Continuous u := by fun_prop
  have hp1 : ∀ i, 0 < omega p (y (i + 1) - y i) (y (i + 2) - y i) := fun i =>
    hp i (i + 2) (two_ne hk i).1 (two_ne hk i).2
  have hH1 : ∀ t : unitInterval, ∀ i, 0 < omega (u t) (y (i + 1) - y i) (y (i + 2) - y i) := by
    intro t i
    have h0 := t.2.1
    have h1 := t.2.2
    show 0 < omega ((1 - (t : ℝ)) • p + (t : ℝ) • c) _ _
    rw [omega_comb]
    have := hp1 i
    have := hc i
    rcases eq_or_lt_of_le h0 with h | h
    · rw [← h]; nlinarith
    · nlinarith [mul_pos h (hc i), mul_nonneg (sub_nonneg.mpr h1) (hp1 i).le]
  have hS : IsClopen (u ⁻¹' O) := by
    refine ⟨?_, hO.preimage hu⟩
    have : u ⁻¹' O = u ⁻¹' C := by
      ext t
      constructor
      · intro h i j l hl; exact (h i j l hl).le
      · intro h
        have hedge := edge_pos_of_weak hk y (u t) (hH1 t) h
        exact triples_of_edge hk y (u t) hedge
    rw [this]; exact hC.preimage hu
  have h0 : (0 : unitInterval) ∈ u ⁻¹' O := by
    show u 0 ∈ O
    have : u 0 = p := by simp [u]
    rw [this]; exact hpO
  have := hS.eq_univ ⟨0, h0⟩
  have h1 : (1 : unitInterval) ∈ u ⁻¹' O := by rw [this]; trivial
  have e : u 1 = c := by simp [u]
  rw [← e]; exact h1


/-- The orientation inequalities of the rim `y` against the points of `Y` (the open cell). -/
def cellSet {k : ℕ} (Y : Finset (Fin 3 → ℝ)) (y : ZMod k → Fin 3 → ℝ) : Set (Fin 3 → ℝ) :=
  {q | ∀ i : ZMod k, ∀ v ∈ Y, v ≠ y i → v ≠ y (i + 1) →
    0 < (Matrix.of ![y (i + 1) - y i, v - y i, q]).det}

theorem gram_pos (E : Matrix (Fin 3) (Fin 3) ℝ) (hE : 0 < E.det) {x : Fin 3 → ℝ} (hx : x ≠ 0) :
    0 < ((Eᵀ * E) *ᵥ x) ⬝ᵥ x := by
  have h1 := inner_emb E x x
  have h2 : emb E x ≠ 0 := by
    intro h
    apply hx
    apply emb_injective hE.ne'
    rw [h]; ext i; simp [emb_apply]
  rw [← h1]
  exact real_inner_self_pos.mpr h2

theorem edge_of_cell {k : ℕ} [NeZero k] {Y : Finset (Fin 3 → ℝ)} {y : ZMod k → Fin 3 → ℝ}
    (hy : Function.Injective y) (hyY : ∀ i, y i ∈ Y) {q : Fin 3 → ℝ} (hq : q ∈ cellSet Y y) :
    ∀ i j : ZMod k, j ≠ i → j ≠ i + 1 → 0 < omega q (y (i + 1) - y i) (y j - y i) :=
  fun i j h1 h2 => hq i (y j) (hyY j) (fun h => h1 (hy h)) (fun h => h2 (hy h))

theorem cellSet_subset_convSet {k : ℕ} [NeZero k] (hk : 3 ≤ k) {Y : Finset (Fin 3 → ℝ)}
    {y : ZMod k → Fin 3 → ℝ} (hy : Function.Injective y) (hyY : ∀ i, y i ∈ Y) :
    cellSet Y y ⊆ convSet y :=
  fun _ hq i => edge_of_cell hy hyY hq i (i + 2) (two_ne hk i).1 (two_ne hk i).2

/-- **(2) of Lemma N, the corner-normal pair certificate.**  `p` is interior to a set `A` of views
satisfying the orientation inequalities of the rim `y` (a cell, `k ≥ 3`); `c` turns every
consecutive rim triple left (`c ∈ convSet y`, the open cone `Conv(R)`); the views `E p`, `E c`
are orthogonal.  Then `E Y` is Rupert.  Only `c ∈ convSet y` is used, not that `R` is a rim
of the polytope along `c`. -/
theorem isRupert_of_conv_pair {k : ℕ} [NeZero k] (hk : 3 ≤ k)
    (E : Matrix (Fin 3) (Fin 3) ℝ) (hE : 0 < E.det)
    (y : ZMod k → Fin 3 → ℝ) (hy : Function.Injective y) (Y : Finset (Fin 3 → ℝ))
    (hyY : ∀ i, y i ∈ Y) {A : Set (Fin 3 → ℝ)} (hA : A ⊆ cellSet Y y)
    {p c : Fin 3 → ℝ} (hp : p ∈ interior A) (hc : c ∈ convSet y)
    (hperp : ((Eᵀ * E) *ᵥ c) ⬝ᵥ p = 0) :
    IsRupert (Y.image (emb E)) := by
  set G := Eᵀ * E with hG
  have hpA : p ∈ cellSet Y y := hA (interior_subset hp)
  have hp0 : p ≠ 0 := ne_zero_of_edge hk y p (edge_of_cell hy hyY hpA)
  have hden : 0 < (G *ᵥ p) ⬝ᵥ p := gram_pos E hE hp0
  let f : (Fin 3 → ℝ) → (Fin 3 → ℝ) := fun q => c - (((G *ᵥ c) ⬝ᵥ q) / ((G *ᵥ q) ⬝ᵥ q)) • q
  have hfc : ContinuousAt f p := by
    have : ContinuousAt (fun q : Fin 3 → ℝ => ((G *ᵥ c) ⬝ᵥ q) / ((G *ᵥ q) ⬝ᵥ q)) p := by
      refine ContinuousAt.div ?_ ?_ hden.ne'
      · refine Continuous.continuousAt ?_
        show Continuous fun q : Fin 3 → ℝ => (G *ᵥ c) ⬝ᵥ q
        simp only [dotProduct]; fun_prop
      · refine Continuous.continuousAt ?_
        simp only [dotProduct, Matrix.mulVec]; fun_prop
    exact continuousAt_const.sub (this.smul continuousAt_id)
  have hfp : f p = c := by
    simp only [f]; rw [hperp]; simp
  have ev1 : ∀ᶠ q in 𝓝 p, f q ∈ convSet y := by
    refine hfc.eventually_mem ?_
    rw [hfp]; exact (isOpen_convSet y).mem_nhds hc
  have ev2 : ∀ᶠ q in 𝓝 p, q ∈ interior A := isOpen_interior.mem_nhds hp
  obtain ⟨U, hUs, hUo, hpU⟩ := mem_nhds_iff.mp (ev1.and ev2)
  have hpos : 0 < volume U := hUo.measure_pos volume ⟨p, hpU⟩
  have hnull : volume (⋃ (ij : {ij : ZMod k × ZMod k // ij.1 ≠ ij.2}),
      {c : Fin 3 → ℝ | (G *ᵥ c) ⬝ᵥ y ij.1.1 = (G *ᵥ c) ⬝ᵥ y ij.1.2}) = 0 := by
    refine (measure_iUnion_null fun ij => ?_)
    exact volume_tie_eq_zero E hE _ _ (fun h => ij.2 (hy h))
  obtain ⟨q, hqU, hqn⟩ : ∃ q ∈ U, q ∉ ⋃ (ij : {ij : ZMod k × ZMod k // ij.1 ≠ ij.2}),
      {c : Fin 3 → ℝ | (G *ᵥ c) ⬝ᵥ y ij.1.1 = (G *ᵥ c) ⬝ᵥ y ij.1.2} := by
    by_contra hcon
    push Not at hcon
    have : volume U ≤ 0 := hnull ▸ measure_mono (fun c hc => hcon c hc)
    exact absurd hpos (not_lt.mpr this)
  obtain ⟨hqc, hqA⟩ := hUs hqU
  have hqA' : q ∈ cellSet Y y := hA (interior_subset hqA)
  have hq0 : q ≠ 0 := ne_zero_of_edge hk y q (edge_of_cell hy hyY hqA')
  have hqq : 0 < (G *ᵥ q) ⬝ᵥ q := gram_pos E hE hq0
  have hinj : Function.Injective fun i : ZMod k => (G *ᵥ q) ⬝ᵥ y i := by
    intro i j hij
    by_contra hne
    exact hqn (Set.mem_iUnion.mpr ⟨⟨(i, j), hne⟩, hij⟩)
  -- all triples are positive along `f q`
  have htri := strict_of_conv_path hk y q (f q) (edge_of_cell hy hyY hqA') hqc
  have hperp' : (G *ᵥ f q) ⬝ᵥ q = 0 := by
    simp only [f, Matrix.mulVec_sub, Matrix.mulVec_smul, sub_dotProduct, smul_dotProduct,
      smul_eq_mul]
    rw [dotProduct_comm (G *ᵥ c) q, div_mul_cancel₀ _ hqq.ne']
    ring
  have hcell' : ∀ i : ZMod k, ∀ v ∈ (Finset.univ.image y), v ≠ y i → v ≠ y (i + 1) →
      0 < (Matrix.of ![y (i + 1) - y i, v - y i, f q]).det := by
    intro i v hv h1 h2
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hv
    exact htri i (i + 1) j (cycBetween_succ hk i j (fun h => h1 (by rw [h])) (fun h => h2 (by rw [h])))
  have hz := isCyclicUnimodal_perp hk E hE y hy (Finset.univ.image y)
    (fun i => Finset.mem_image_of_mem _ (Finset.mem_univ i)) (f q) hcell' q hperp' hinj
  exact isRupert_of_rimCell_zmod hk E hE y hy Y hyY q hq0 hqA' hz


theorem isOpen_cellSet {k : ℕ} [NeZero k] (Y : Finset (Fin 3 → ℝ)) (y : ZMod k → Fin 3 → ℝ) :
    IsOpen (cellSet Y y) := by
  have : cellSet Y y = ⋂ i : ZMod k, ⋂ v : Y, ⋂ (_ : v.1 ≠ y i ∧ v.1 ≠ y (i + 1)),
      {q | 0 < omega q (y (i + 1) - y i) (v.1 - y i)} := by
    ext q
    simp only [cellSet, Set.mem_ofPred_eq, Set.mem_iInter, Subtype.forall, and_imp]
    rfl
  rw [this]
  exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun v =>
    isOpen_iInter_of_finite fun _ => isOpen_lt continuous_const (continuous_omega _ _)

theorem convSet_combo {k : ℕ} (y : ZMod k → Fin 3 → ℝ) {p c : Fin 3 → ℝ} (hp : p ∈ convSet y)
    (hc : c ∈ convSet y) {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    (1 - t) • p + t • c ∈ convSet y := by
  intro i
  rw [omega_comb]
  have := hp i
  have := hc i
  rcases eq_or_lt_of_le h0 with h | h
  · rw [← h]; nlinarith
  · nlinarith [mul_pos h (hc i), mul_nonneg (sub_nonneg.mpr h1) (hp i).le]

/-- **(3) of Lemma N, the checkable form.**  If `ρ` is in the closure of the cell `A` of the rim
`y` and `σ` in the closure of the cone `Conv(R) = convSet y` with `((Eᵀ E) σ) ⬝ᵥ ρ < 0`, then
`E Y` is Rupert. -/
theorem isRupert_of_conv_pair_closure {k : ℕ} [NeZero k] (hk : 3 ≤ k)
    (E : Matrix (Fin 3) (Fin 3) ℝ) (hE : 0 < E.det)
    (y : ZMod k → Fin 3 → ℝ) (hy : Function.Injective y) (Y : Finset (Fin 3 → ℝ))
    (hyY : ∀ i, y i ∈ Y) {ρ σ : Fin 3 → ℝ} (hρ : ρ ∈ closure (cellSet Y y))
    (hσ : σ ∈ closure (convSet y)) (hneg : ((Eᵀ * E) *ᵥ σ) ⬝ᵥ ρ < 0) :
    IsRupert (Y.image (emb E)) := by
  set G := Eᵀ * E with hG
  let F : (Fin 3 → ℝ) × (Fin 3 → ℝ) → ℝ := fun z => (G *ᵥ z.2) ⬝ᵥ z.1
  have hF : Continuous F := by
    simp only [F, dotProduct, Matrix.mulVec]; fun_prop
  have hmem : (ρ, σ) ∈ closure (cellSet Y y ×ˢ convSet y) := by
    rw [closure_prod_eq]; exact ⟨hρ, hσ⟩
  obtain ⟨z, hzF, hz⟩ := mem_closure_iff.mp hmem _ (isOpen_Iio.preimage hF) hneg
  have hz1 : z.1 ∈ cellSet Y y := hz.1
  have hz2 : z.2 ∈ convSet y := hz.2
  have hz10 : z.1 ≠ 0 := ne_zero_of_edge hk y _ (edge_of_cell hy hyY hz1)
  have hz1c : z.1 ∈ convSet y := cellSet_subset_convSet hk hy hyY hz1
  let g : ℝ → ℝ := fun t => (G *ᵥ ((1 - t) • z.2 + t • z.1)) ⬝ᵥ z.1
  have hg : Continuous g := by
    simp only [g, dotProduct, Matrix.mulVec]; fun_prop
  have hg0 : g 0 < 0 := by simpa [g, F] using hzF
  have hg1 : 0 < g 1 := by
    simpa [g] using gram_pos E hE hz10
  obtain ⟨t, ht, hgt⟩ := intermediate_value_Icc (zero_le_one) hg.continuousOn
    (show (0 : ℝ) ∈ Set.Icc (g 0) (g 1) from ⟨hg0.le, hg1.le⟩)
  exact isRupert_of_conv_pair hk E hE y hy Y hyY (subset_refl _)
    (by rw [(isOpen_cellSet Y y).interior_eq]; exact hz1) (convSet_combo y hz2 hz1c ht.1 ht.2) hgt


end Minimality.RimCell
