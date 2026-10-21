module

public import Minimality.DepthSeparated
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty

@[expose] public section

/-!
# Freedom from the extreme rays of the balanced force cone

CRIT5-WRITEUP.md §4 (the closed freedom criterion for small silhouettes,
refereed 2026-10-20), via Lemma 7.1.  Corners `p j` of a strictly convex
counterclockwise polygon with depths `z j`; a *slot* `(j, s)` is a force along
the outward normal `n` of one of the two edges at `j` (`slotNormal`); a load
`x ≥ 0` on the slots is *balanced* if (E1) `Σ x n = 0` and (E2) `Σ x z n = 0`,
i.e. `Σ x (n, z n) = 0` in `ℝ⁴` (`slotCol`), and its torque is
`Σ x (p_j × n)` (`slotTorque`).  Every balanced corner-force system is a
balanced load (`exists_slots_of_forces`, by `normalCone_decomp`), so the
silhouette is first-order free as soon as every nonzero balanced load has
torque of one strict sign `σ`.

* The cone layer (any finite set of columns in any real vector space):
  `pos_of_extremeSlots` — a linear functional positive on every *extreme ray*
  (`IsExtremeSlots`: a nonzero balanced load of minimal support) is positive on
  every nonzero balanced load (induction on the support, `exists_shrink`);
  an extreme ray spans the relations on its support (`IsExtremeSlots.eq_smul`)
  and so loads at most `dim + 1` slots (`IsExtremeSlots.card_support_le`).
* The closed (Cramer) form for columns in `ℝ⁴`: for five slots `T` the Cramer
  coefficients `λ_r = (−1)^r Δ_r` (`cramerCoeff`, `Δ_r` the `4 × 4` minors)
  satisfy `Σ λ_r a (T r) = 0` (`sum_cramerCoeff_smul`), and `Σ λ_r t (T r)`
  is the `5 × 5` determinant with the extra row `t` (`cramerTorque_eq_det`).
  `pos_of_cramer`: if the columns have full rank, every extreme ray is (a
  positive multiple of) `ε λ(T)` for five distinct slots `T` with
  sign-consistent `λ(T)`; this covers the parallel (support 4), level and
  mixed rays of the writeup's list.  The proof extends the independent
  columns of the ray's support by a basis (`exists_linearIndepOn_extension`).
  `det_slotCols`: the closed form of `Δ` (Plücker relation),
  `[12][34]⟨13⟩⟨24⟩ − [13][24]⟨12⟩⟨34⟩`.
* The polygon layer: `RaysFree p z` (every extreme ray has torque of sign
  `σ`), `torque_pos_of_extremeRays` (then so has every nonzero balanced force
  system), `raysFree_of_five_slots` (it suffices to test loads on at most five
  slots), `CramerCert p z` (the closed test: full rank and, for every five
  distinct slots with sign-consistent nonzero `λ`, `σ ε det > 0`) and
  `cramerCert_raysFree`.  Nothing here needs `k ≤ 5`; for `k = 4, 5` there are
  8 resp. 10 slots, so at most `C(8, 5) = 56` resp. `C(10, 5) = 252` sets.
* The views (as `DepthSeparated.lean`): `exists_firstOrderInward_of_torque_ne_zero`
  (Lemma 7.1 glue), `isRupert_of_raysFreeView`, the certificate form
  `exists_tiltCert_of_raysFree`, and the crossings
  `isRupert_of_chords_raysFree` (Proposition 8.8) and
  `isRupert_of_edgeChords_raysFree` (Theorem 8.9).  Unlike Theorems 7.3 and
  8.10 no exclusion of horizontal double normals is assumed: a strict torque
  sign on every ray excludes them.

Not formalized: the converse (a free silhouette passes the test), Theorems A
(corner tripods) and B (four corners) of the writeup, and the description of
which supports are parallel, level or mixed rays.
-/

namespace Minimality

open scoped RealInnerProductSpace
open Finset

section Cone

variable {ι M : Type*} [Fintype ι] [AddCommGroup M] [Module ℝ M]

/-- A *balanced slot system*: nonnegative loads `x i` on the slots `i`, whose
columns `a i` sum to zero with these weights. -/
def IsBalancedSlots (a : ι → M) (x : ι → ℝ) : Prop :=
  (∀ i, 0 ≤ x i) ∧ ∑ i, x i • a i = 0

/-- An *extreme ray* of the cone of balanced slot systems: a nonzero balanced
system whose support is minimal among the supports of nonzero balanced
systems. -/
def IsExtremeSlots (a : ι → M) (x : ι → ℝ) : Prop :=
  IsBalancedSlots a x ∧ x ≠ 0 ∧
    ∀ y, IsBalancedSlots a y → y ≠ 0 → (∀ i, x i = 0 → y i = 0) → ∀ i, y i = 0 → x i = 0

/-- **Shrinking the support.**  If `x` is balanced and `w` is a signed
relation supported in the support of `x` with a positive entry, then
`x − c w` (`c > 0` maximal) is balanced and vanishes at a slot where `x` does
not. -/
theorem exists_shrink {a : ι → M} {x w : ι → ℝ} (hx : IsBalancedSlots a x)
    (hw : ∑ i, w i • a i = 0) (hsub : ∀ i, x i = 0 → w i = 0) (hpos : ∃ i, 0 < w i) :
    ∃ c : ℝ, 0 < c ∧ IsBalancedSlots a (fun i => x i - c * w i) ∧
      ∃ j, x j ≠ 0 ∧ x j - c * w j = 0 := by
  classical
  set P := univ.filter fun i => 0 < w i
  have hP : P.Nonempty := by
    obtain ⟨i, hi⟩ := hpos; exact ⟨i, mem_filter.mpr ⟨mem_univ _, hi⟩⟩
  obtain ⟨j, hjP, hj⟩ := P.exists_min_image (fun i => x i / w i) hP
  have hwj : 0 < w j := (mem_filter.mp hjP).2
  have hxj : x j ≠ 0 := fun h => hwj.ne' (hsub j h)
  have hxj' : 0 < x j := lt_of_le_of_ne (hx.1 j) (Ne.symm hxj)
  have hc : 0 < x j / w j := div_pos hxj' hwj
  refine ⟨x j / w j, hc, ⟨fun i => ?_, ?_⟩, j, hxj, ?_⟩
  · by_cases hi : 0 < w i
    · have := hj i (mem_filter.mpr ⟨mem_univ _, hi⟩)
      rw [le_div_iff₀ hi] at this; linarith
    · push Not at hi
      have := hx.1 i
      nlinarith
  · simp only [sub_smul, sum_sub_distrib, mul_smul, ← smul_sum, hx.2, hw, smul_zero, sub_zero]
  · field_simp; ring

theorem exists_pos_of_ne_zero {x : ι → ℝ} (hx : ∀ i, 0 ≤ x i) (hx0 : x ≠ 0) : ∃ i, 0 < x i := by
  by_contra hc; push Not at hc
  exact hx0 (funext fun i => le_antisymm (hc i) (hx i))

/-- **Extreme rays decide the sign of a linear functional.**  If a linear
functional `t` is positive on every extreme ray of the cone of balanced slot
systems, it is positive on every nonzero balanced system. -/
theorem pos_of_extremeSlots (a : ι → M) (t : ι → ℝ)
    (h : ∀ x, IsExtremeSlots a x → 0 < ∑ i, x i * t i) :
    ∀ x, IsBalancedSlots a x → x ≠ 0 → 0 < ∑ i, x i * t i := by
  classical
  suffices H : ∀ n, ∀ x : ι → ℝ, (univ.filter fun i => x i ≠ 0).card = n →
      IsBalancedSlots a x → x ≠ 0 → 0 < ∑ i, x i * t i from fun x => H _ x rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro x hn hx hx0
  by_cases hmin : ∀ y, IsBalancedSlots a y → y ≠ 0 → (∀ i, x i = 0 → y i = 0) →
      ∀ i, y i = 0 → x i = 0
  · exact h x ⟨hx, hx0, hmin⟩
  push Not at hmin
  obtain ⟨y, hy, hy0, hsub, i0, hyi0, hxi0⟩ := hmin
  obtain ⟨c, hc, hz, j, hxj, hzj⟩ := exists_shrink hx hy.2 hsub (exists_pos_of_ne_zero hy.1 hy0)
  have hcard_lt : ∀ v : ι → ℝ, (∀ i, x i = 0 → v i = 0) → (∃ j, x j ≠ 0 ∧ v j = 0) →
      (univ.filter fun i => v i ≠ 0).card < n := by
    rintro v hv ⟨j, hxj, hvj⟩
    rw [← hn]
    apply card_lt_card
    rw [ssubset_iff_of_subset]
    · exact ⟨j, by simp [hxj], by simp [hvj]⟩
    · intro i; simp only [mem_filter, mem_univ, true_and]; exact fun hvi hxi => hvi (hv i hxi)
  have hty := ih _ (hcard_lt y hsub ⟨i0, hxi0, hyi0⟩) y rfl hy hy0
  have hsplit : ∑ i, x i * t i = ∑ i, (x i - c * y i) * t i + c * ∑ i, y i * t i := by
    rw [mul_sum, ← sum_add_distrib]; congr 1; ext i; ring
  rw [hsplit]
  by_cases hz0 : (fun i => x i - c * y i) = 0
  · have : ∑ i, (x i - c * y i) * t i = 0 := by
      have := congrFun hz0; simp only [Pi.zero_apply] at this; simp [this]
    rw [this, zero_add]; exact mul_pos hc hty
  · have := ih _ (hcard_lt _ (fun i hi => by simp [hi, hsub i hi]) ⟨j, hxj, hzj⟩) _ rfl hz hz0
    linarith [mul_pos hc hty]

/-- **An extreme ray spans the relations on its support**: every signed
relation supported in the support of an extreme ray is a multiple of it. -/
theorem IsExtremeSlots.eq_smul {a : ι → M} {x : ι → ℝ} (hx : IsExtremeSlots a x) {w : ι → ℝ}
    (hw : ∑ i, w i • a i = 0) (hsub : ∀ i, x i = 0 → w i = 0) : ∃ c : ℝ, w = c • x := by
  obtain ⟨hb, hx0, hmin⟩ := hx
  obtain ⟨j0, hj0⟩ : ∃ j, x j ≠ 0 := by
    by_contra h; push Not at h; exact hx0 (funext h)
  refine ⟨w j0 / x j0, ?_⟩
  by_contra hne
  set v : ι → ℝ := fun i => w i - w j0 / x j0 * x i with hv_def
  have hv : ∑ i, v i • a i = 0 := by
    simp only [hv_def, sub_smul, sum_sub_distrib, mul_smul, ← smul_sum, hw, hb.2, smul_zero,
      sub_zero]
  have hvsub : ∀ i, x i = 0 → v i = 0 := fun i hi => by simp [hv_def, hi, hsub i hi]
  have hvj0 : v j0 = 0 := by simp only [hv_def]; field_simp; ring
  have key : ∀ u : ι → ℝ, ∑ i, u i • a i = 0 → (∀ i, x i = 0 → u i = 0) → u j0 = 0 →
      (∃ i, 0 < u i) → False := by
    intro u hu husub huj0 hpos
    obtain ⟨d, -, hz, j, hxj, hzj⟩ := exists_shrink hb hu husub hpos
    refine hxj (hmin _ hz (fun h => ?_) (fun i hi => by simp [hi, husub i hi]) j hzj)
    have := congrFun h j0; simp [huj0] at this; exact hj0 this
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra h; push Not at h; apply hne; ext i
    have := h i; simp only [hv_def] at this; simp only [Pi.smul_apply, smul_eq_mul]; linarith
  rcases lt_or_gt_of_ne hi with h | h
  · exact key (fun i => -v i) (by simp only [neg_smul, sum_neg_distrib, hv, neg_zero])
      (fun i hi => by simp [hvsub i hi]) (by simp [hvj0]) ⟨i, by linarith⟩
  · exact key v hv hvsub hvj0 ⟨i, h⟩

/-- The columns of an extreme ray's support, without one of them, are
linearly independent. -/
theorem IsExtremeSlots.linearIndepOn_erase [DecidableEq ι] {a : ι → M} {x : ι → ℝ}
    (hx : IsExtremeSlots a x) (s₀ : ι) (hs₀ : x s₀ ≠ 0) :
    LinearIndepOn ℝ a (((univ.filter fun i => x i ≠ 0).erase s₀ : Finset ι) : Set ι) := by
  rw [linearIndepOn_finset_iff]
  set S' := (univ.filter fun i => x i ≠ 0).erase s₀ with hS'
  intro g hg i hi
  set w : ι → ℝ := fun j => if j ∈ S' then g j else 0 with hw_def
  have hw : ∑ j, w j • a j = 0 := by
    rw [← sum_subset (subset_univ S') (fun j _ hj => by simp only [hw_def, hj, ↓reduceIte, zero_smul]),
      ← hg]
    exact sum_congr rfl fun j hj => by simp only [hw_def, hj, ↓reduceIte]
  have hxS : ∀ j, x j = 0 → j ∉ S' := fun j hj hjS => by
    rw [hS', mem_erase, mem_filter] at hjS; exact hjS.2.2 hj
  obtain ⟨c, hc⟩ := hx.eq_smul hw (fun j hj => by simp only [hw_def, hxS j hj, ↓reduceIte])
  have hc0 : c = 0 := by
    have := congrFun hc s₀
    simp only [hw_def, hS', mem_erase, ne_eq, not_true_eq_false, false_and, ↓reduceIte,
      Pi.smul_apply, smul_eq_mul] at this
    exact (mul_eq_zero.mp this.symm).resolve_right hs₀
  have := congrFun hc i
  simp only [hw_def, hi, ↓reduceIte, Pi.smul_apply, hc0, zero_smul] at this
  exact this

/-- **Extreme rays have at most `d + 1` loaded slots** when the columns lie in
a space of dimension `d`. -/
theorem IsExtremeSlots.card_support_le [FiniteDimensional ℝ M] {a : ι → M} {x : ι → ℝ}
    (hx : IsExtremeSlots a x) :
    (univ.filter fun i => x i ≠ 0).card ≤ Module.finrank ℝ M + 1 := by
  classical
  obtain ⟨s₀, hs₀⟩ : ∃ j, x j ≠ 0 := by
    by_contra h; push Not at h; exact hx.2.1 (funext h)
  have hli := hx.linearIndepOn_erase s₀ hs₀
  have hle := hli.fintype_card_le_finrank
  simp only [Finset.coe_sort_coe, Fintype.card_coe] at hle
  have := card_erase_add_one (s := univ.filter fun i => x i ≠ 0) (a := s₀) (by simp [hs₀])
  omega

/-- **Balanced systems on at most `d + 1` slots suffice.** -/
theorem pos_of_small_support [FiniteDimensional ℝ M] (a : ι → M) (t : ι → ℝ)
    (h : ∀ x, IsBalancedSlots a x → x ≠ 0 →
      (univ.filter fun i => x i ≠ 0).card ≤ Module.finrank ℝ M + 1 → 0 < ∑ i, x i * t i) :
    ∀ x, IsBalancedSlots a x → x ≠ 0 → 0 < ∑ i, x i * t i :=
  pos_of_extremeSlots a t fun x hx => h x hx.1 hx.2.1 hx.card_support_le

end Cone

section Spread

variable {ι : Type*} [DecidableEq ι] {n : ℕ}

/-- A function on `Fin n` carried to `ι` along `T` (zero off the range). -/
noncomputable def spread (T : Fin n → ι) (g : Fin n → ℝ) : ι → ℝ :=
  fun i => ∑ r, if T r = i then g r else 0

theorem spread_apply {T : Fin n → ι} (hT : Function.Injective T) (g : Fin n → ℝ) (r : Fin n) :
    spread T g (T r) = g r := by
  simp [spread, hT.eq_iff]

theorem spread_eq_zero {T : Fin n → ι} (g : Fin n → ℝ) {i : ι} (h : ∀ r, T r ≠ i) :
    spread T g i = 0 := by
  simp [spread, h]

theorem sum_spread_smul [Fintype ι] {M : Type*} [AddCommGroup M] [Module ℝ M] (T : Fin n → ι)
    (g : Fin n → ℝ) (v : ι → M) : ∑ i, spread T g i • v i = ∑ r, g r • v (T r) := by
  simp only [spread, sum_smul, ite_smul, zero_smul]
  rw [sum_comm]
  exact sum_congr rfl fun r _ => by simp

end Spread

section Cramer

variable {ι : Type*}

/-- The *Cramer coefficients* of five columns `a (T 0), …, a (T 4)` in `ℝ⁴`:
`λ_r = (−1)^r Δ_r`, `Δ_r` the `4 × 4` determinant of the other four columns
(written as rows).  They satisfy `Σ λ_r a (T r) = 0`
(`sum_cramerCoeff_smul`); when some `Δ_r ≠ 0` they span the relations among
the five columns. -/
noncomputable def cramerCoeff (a : ι → Fin 4 → ℝ) (T : Fin 5 → ι) (r : Fin 5) : ℝ :=
  (-1 : ℝ) ^ (r : ℕ) * (Matrix.of fun j : Fin 4 => a (T (r.succAbove j))).det

/-- The value `Σ λ_r t (T r)` of the functional `t` on the Cramer relation of
`T`; it is the `5 × 5` determinant with rows `(t, a)` (`cramerTorque_eq_det`). -/
noncomputable def cramerTorque (a : ι → Fin 4 → ℝ) (t : ι → ℝ) (T : Fin 5 → ι) : ℝ :=
  ∑ r, cramerCoeff a T r * t (T r)

/-- **Cramer's relation**: `Σ_r λ_r a (T r) = 0` (expand the `5 × 5`
determinant with a repeated column). -/
theorem sum_cramerCoeff_smul (a : ι → Fin 4 → ℝ) (T : Fin 5 → ι) :
    ∑ r, cramerCoeff a T r • a (T r) = 0 := by
  funext i
  set N : Matrix (Fin 5) (Fin 5) ℝ :=
    Matrix.of fun r c => (Fin.cons (a (T r) i) (a (T r)) : Fin 5 → ℝ) c with hN
  have h0 : N.det = 0 :=
    Matrix.det_zero_of_column_eq (i := 0) (j := i.succ) (Fin.succ_ne_zero i).symm
      (fun r => by simp [hN])
  rw [Matrix.det_succ_column_zero] at h0
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
  rw [← h0]
  refine sum_congr rfl fun r _ => ?_
  have hsub : N.submatrix r.succAbove Fin.succ = Matrix.of fun j : Fin 4 => a (T (r.succAbove j)) := by
    ext j m; simp [hN]
  rw [hsub]
  simp only [cramerCoeff, hN, Matrix.of_apply, Fin.cons_zero]
  ring

/-- `cramerTorque` is the `5 × 5` determinant whose `r`-th row is
`(t (T r), a (T r))`. -/
theorem cramerTorque_eq_det (a : ι → Fin 4 → ℝ) (t : ι → ℝ) (T : Fin 5 → ι) :
    cramerTorque a t T =
      (Matrix.of fun r c => (Fin.cons (t (T r)) (a (T r)) : Fin 5 → ℝ) c).det := by
  rw [Matrix.det_succ_column_zero, cramerTorque]
  refine sum_congr rfl fun r _ => ?_
  have hsub : (Matrix.of fun r c => (Fin.cons (t (T r)) (a (T r)) : Fin 5 → ℝ) c).submatrix
      r.succAbove Fin.succ = Matrix.of fun j : Fin 4 => a (T (r.succAbove j)) := by
    ext j m; simp
  rw [hsub]
  simp only [cramerCoeff, Matrix.of_apply, Fin.cons_zero]
  ring

/-- **The Cramer certificate.**  Columns `a` in `ℝ⁴` of full rank (some four
have a nonzero determinant).  If for every five distinct slots `T` whose
Cramer coefficients have one sign `ε` (and are not all zero) the functional
`t` has `ε · cramerTorque > 0`, then `t` is positive on every extreme ray of
the cone of balanced slot systems. -/
theorem pos_of_cramer [Fintype ι] [DecidableEq ι] (a : ι → Fin 4 → ℝ) (t : ι → ℝ)
    (hrank : ∃ B : Fin 4 → ι, (Matrix.of fun j => a (B j)).det ≠ 0)
    (h : ∀ T : Fin 5 → ι, Function.Injective T → ∀ ε : ℝ, (ε = 1 ∨ ε = -1) →
      (∀ r, 0 ≤ ε * cramerCoeff a T r) → (∃ r, cramerCoeff a T r ≠ 0) →
      0 < ε * cramerTorque a t T) :
    ∀ x, IsExtremeSlots a x → 0 < ∑ i, x i * t i := by
  intro x hx
  obtain ⟨s₀, hs₀⟩ : ∃ j, x j ≠ 0 := by
    by_contra h; push Not at h; exact hx.2.1 (funext h)
  have hxs₀ : 0 < x s₀ := lt_of_le_of_ne (hx.1.1 s₀) (Ne.symm hs₀)
  -- extend the independent columns of the support (without `s₀`) to a basis
  obtain ⟨b, -, hsb, hspan, hbli⟩ :=
    exists_linearIndepOn_extension (hx.linearIndepOn_erase s₀ hs₀) (Set.subset_univ _)
  have htop : Submodule.span ℝ (a '' b) = ⊤ := by
    obtain ⟨B, hB⟩ := hrank
    have hBli : LinearIndependent ℝ (fun j => a (B j)) := by
      have := Matrix.linearIndependent_rows_iff_isUnit.mpr
        ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hB))
      exact this
    have hBtop : Submodule.span ℝ (Set.range fun j => a (B j)) = ⊤ :=
      hBli.span_eq_top_of_card_eq_finrank (by simp)
    rw [eq_top_iff, ← hBtop]
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact hspan ⟨B j, Set.mem_univ _, rfl⟩
  classical
  set bF := b.toFinset with hbF_def
  have hbF : LinearIndepOn ℝ a (bF : Set ι) := by rw [hbF_def, Set.coe_toFinset]; exact hbli
  have hcard : bF.card = 4 := by
    have h1 := finrank_span_eq_card hbli
    rw [← Set.image_eq_range, htop, finrank_top, Module.finrank_fin_fun] at h1
    rw [hbF_def, Set.toFinset_card]; convert h1.symm
  have hsupp : ∀ i, x i ≠ 0 → i ≠ s₀ → i ∈ bF := fun i hi his => by
    rw [hbF_def, Set.mem_toFinset]; apply hsb; simp [hi, his]
  have hs₀b : s₀ ∉ bF := by
    intro hs
    have hsum : ∑ i ∈ bF, x i • a i = 0 := by
      rw [sum_subset (subset_univ bF) (fun i _ hi => ?_)]
      · exact hx.1.2
      · by_cases his : i = s₀
        · subst his; exact absurd hs hi
        · by_cases hxi : x i = 0
          · simp [hxi]
          · exact absurd (hsupp i hxi his) hi
    exact hs₀ ((linearIndepOn_finset_iff.mp hbF) x hsum s₀ hs)
  -- enumerate the basis and put `s₀` last
  set e := (bF.equivFinOfCardEq hcard).symm with he
  set E : Fin 4 → ι := fun j => (e j : ι) with hE_def
  have hEmem : ∀ j, E j ∈ bF := fun j => (e j).2
  have hEinj : Function.Injective E := fun j j' h => e.injective (Subtype.ext h)
  have hEsurj : ∀ i ∈ bF, ∃ j, E j = i := fun i hi => ⟨e.symm ⟨i, hi⟩, by simp only [hE_def, Equiv.apply_symm_apply]⟩
  set T : Fin 5 → ι := Fin.snoc (α := fun _ => ι) E s₀ with hT_def
  have hTlast : T (Fin.last 4) = s₀ := by
    rw [hT_def]; exact Fin.snoc_last (α := fun _ => ι) _ _
  have hTcs : ∀ j, T j.castSucc = E j := fun j => by simp [hT_def]
  have hTinj : Function.Injective T := by
    intro r r' hrr
    rcases Fin.eq_castSucc_or_eq_last r with ⟨j, rfl⟩ | rfl <;>
      rcases Fin.eq_castSucc_or_eq_last r' with ⟨j', rfl⟩ | rfl
    · rw [hTcs, hTcs] at hrr; rw [hEinj hrr]
    · rw [hTcs, hTlast] at hrr; exact absurd (hrr ▸ hEmem j) hs₀b
    · rw [hTcs, hTlast] at hrr; exact absurd (hrr ▸ hEmem j') hs₀b
    · rfl
  -- the last Cramer coefficient is the determinant of the basis
  have hEli : LinearIndependent ℝ (fun j => a (E j)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg j
    have hsum : ∑ i ∈ bF, spread E g i • a i = 0 := by
      rw [sum_subset (subset_univ bF) (fun i _ hi => ?_), sum_spread_smul]
      · exact hg
      · rw [spread_eq_zero (T := E) (i := i) g (fun r hr => hi (hr ▸ hEmem r)), zero_smul]
    have := (linearIndepOn_finset_iff.mp hbF) _ hsum (E j) (hEmem j)
    rwa [spread_apply hEinj] at this
  set lam := cramerCoeff a T with hlam
  have hl4 : lam (Fin.last 4) ≠ 0 := by
    have hdet : (Matrix.of fun j => a (E j)).det ≠ 0 := by
      have := (Matrix.linearIndependent_rows_iff_isUnit (A := Matrix.of fun j => a (E j))).mp hEli
      exact ((Matrix.isUnit_iff_isUnit_det _).mp this).ne_zero
    have e1 : lam (Fin.last 4) = (Matrix.of fun j => a (E j)).det := by
      simp only [hlam, cramerCoeff, Fin.val_last, Fin.succAbove_last, hTcs]
      norm_num
    rwa [e1]
  set l4 := lam (Fin.last 4)
  -- the relation `l4 x − x s₀ Λ` lives on the basis, so it vanishes
  set Λ := spread T lam with hΛ
  have hΛs₀ : Λ s₀ = l4 := by rw [← hTlast, hΛ, spread_apply hTinj]
  have hΛoff : ∀ i, i ∉ bF → i ≠ s₀ → Λ i = 0 := fun i hi his =>
    spread_eq_zero lam fun r hr => by
      rcases Fin.eq_castSucc_or_eq_last r with ⟨j, rfl⟩ | rfl
      · rw [hTcs] at hr; exact hi (hr ▸ hEmem j)
      · rw [hTlast] at hr; exact his hr.symm
  set y : ι → ℝ := fun i => l4 * x i - x s₀ * Λ i with hy_def
  have hy : ∑ i, y i • a i = 0 := by
    simp only [hy_def, sub_smul, sum_sub_distrib, mul_smul, ← smul_sum, hx.1.2, smul_zero,
      zero_sub, neg_eq_zero]
    rw [hΛ, sum_spread_smul, sum_cramerCoeff_smul, smul_zero]
  have hyoff : ∀ i, i ∉ bF → y i = 0 := fun i hi => by
    by_cases his : i = s₀
    · subst his; simp only [hy_def, hΛs₀]; ring
    · have hxi : x i = 0 := by
        by_contra hxi; exact hi (hsupp i hxi his)
      simp [hy_def, hxi, hΛoff i hi his]
  have hy0 : ∀ i, y i = 0 := by
    have hsum : ∑ i ∈ bF, y i • a i = 0 := by
      rw [sum_subset (subset_univ bF) (fun i _ hi => by rw [hyoff i hi, zero_smul])]; exact hy
    intro i
    by_cases hi : i ∈ bF
    · exact (linearIndepOn_finset_iff.mp hbF) y hsum i hi
    · exact hyoff i hi
  have hrel : ∀ r, lam r = l4 / x s₀ * x (T r) := fun r => by
    have := hy0 (T r)
    simp only [hy_def, hΛ, spread_apply hTinj] at this
    field_simp; linarith
  -- the sign `ε` of the ray and the torque
  set ε : ℝ := if 0 < l4 then 1 else -1 with hε_def
  have hε : ε = 1 ∨ ε = -1 := by by_cases h : 0 < l4 <;> simp [hε_def, h]
  have hεl : 0 < ε * l4 := by
    by_cases h : 0 < l4
    · simp [hε_def, h]
    · simp only [hε_def, h, ↓reduceIte, neg_mul, one_mul, neg_pos]
      exact lt_of_le_of_ne (not_lt.mp h) hl4
  have hq : 0 < ε * l4 / x s₀ := div_pos hεl hxs₀
  have hsign : ∀ r, 0 ≤ ε * lam r := fun r => by
    rw [hrel r]
    have : ε * (l4 / x s₀ * x (T r)) = ε * l4 / x s₀ * x (T r) := by ring
    rw [this]; exact mul_nonneg hq.le (hx.1.1 _)
  have hpos := h T hTinj ε hε hsign ⟨Fin.last 4, hl4⟩
  have hxT : ∑ i, x i * t i = ∑ r, x (T r) * t (T r) := by
    have hxs : ∀ i, x i = spread T (fun r => x (T r)) i := fun i => by
      by_cases hi : ∃ r, T r = i
      · obtain ⟨r, rfl⟩ := hi; rw [spread_apply hTinj]
      · push Not at hi
        rw [spread_eq_zero _ hi]
        by_contra hxi
        by_cases his : i = s₀
        · exact hi (Fin.last 4) (hTlast.trans his.symm)
        · obtain ⟨j, hj⟩ := hEsurj i (hsupp i hxi his)
          exact hi j.castSucc ((hTcs j).trans hj)
    rw [sum_congr rfl fun i _ => by rw [hxs i]]
    simpa [smul_eq_mul] using sum_spread_smul T (fun r => x (T r)) t
  have htq : ε * cramerTorque a t T = ε * l4 / x s₀ * ∑ i, x i * t i := by
    rw [hxT, cramerTorque, mul_sum, mul_sum]
    refine sum_congr rfl fun r _ => ?_
    rw [← hlam, hrel r]; ring
  rw [htq] at hpos
  exact pos_of_mul_pos_right hpos hq.le

end Cramer

section Polygon

variable {k : ℕ}

/-- The force direction of a *slot* `(j, s)` of the polygon `p`: the outward
normal of the edge `(j − 1, j)` for `s = 0`, of the edge `(j, j + 1)` for
`s = 1`. -/
noncomputable def slotNormal (p : ZMod k → ℝ²) (r : ZMod k × Fin 2) : ℝ² :=
  ![outNormal (p (r.1 - 1)) (p r.1), outNormal (p r.1) (p (r.1 + 1))] r.2

/-- The column `(n, z n) ∈ ℝ⁴` of a slot: a unit load on it contributes `n`
to (E1) and `z n` to (E2). -/
noncomputable def slotCol (p : ZMod k → ℝ²) (z : ZMod k → ℝ) (r : ZMod k × Fin 2) : Fin 4 → ℝ :=
  ![slotNormal p r 0, slotNormal p r 1, z r.1 * slotNormal p r 0, z r.1 * slotNormal p r 1]

/-- The torque `p_j × n` of a unit load on the slot `(j, s)`. -/
noncomputable def slotTorque (p : ZMod k → ℝ²) (r : ZMod k × Fin 2) : ℝ :=
  cross2 (p r.1) (slotNormal p r)

/-- **Corner forces as slot loads.**  A nonzero balanced force system of a
strictly convex polygon (forces in the normal cones, (E1), (E2)) is a nonzero
balanced slot system with the same torque. -/
theorem exists_slots_of_forces [NeZero k] {p : ZMod k → ℝ²} (z : ZMod k → ℝ)
    (hp : IsCcwPolygon p) {f : ZMod k → ℝ²}
    (hf : ∀ i, f i ∈ normalConeAt (convexHull ℝ (Set.range p)) (p i))
    (hne : ∃ i, f i ≠ 0) (h1 : ∑ i, f i = 0) (h2 : ∑ i, z i • f i = 0) :
    ∃ x, IsBalancedSlots (slotCol p z) x ∧ x ≠ 0 ∧
      ∑ i, cross2 (p i) (f i) = ∑ r, x r * slotTorque p r := by
  choose α β hα hβ hf' using fun i => hp.normalCone_decomp i (hf i)
  set x : ZMod k × Fin 2 → ℝ := fun r => ![α r.1, β r.1] r.2 with hx_def
  have hfx : ∀ i, f i = ∑ s : Fin 2, x (i, s) • slotNormal p (i, s) := by
    intro i; rw [hf' i]; simp [Fin.sum_univ_two, hx_def, slotNormal]
  have hsplit : ∀ (g : ZMod k × Fin 2 → ℝ), ∑ r, g r = ∑ i, ∑ s : Fin 2, g (i, s) := fun g =>
    Fintype.sum_prod_type g
  refine ⟨x, ⟨?_, ?_⟩, ?_, ?_⟩
  · rintro ⟨i, s⟩; fin_cases s
    · simpa [hx_def] using hα i
    · simpa [hx_def] using hβ i
  · have e1 : ∀ m : Fin 2, ∑ r, x r * slotNormal p r m = 0 := by
      intro m
      have := congrArg (fun v : ℝ² => v m) h1
      simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.zero_apply] at this
      rw [hsplit, ← this]
      refine sum_congr rfl fun i _ => ?_
      rw [hfx i]
      simp [PiLp.smul_apply, smul_eq_mul]
    have e2 : ∀ m : Fin 2, ∑ r, x r * (z r.1 * slotNormal p r m) = 0 := by
      intro m
      have := congrArg (fun v : ℝ² => v m) h2
      simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.zero_apply, PiLp.smul_apply,
        smul_eq_mul] at this
      rw [hsplit, ← this]
      refine sum_congr rfl fun i _ => ?_
      rw [hfx i]
      simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul, mul_sum]
      exact sum_congr rfl fun s _ => by ring
    funext m
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    fin_cases m
    · simpa [slotCol] using e1 0
    · simpa [slotCol] using e1 1
    · simpa [slotCol] using e2 0
    · simpa [slotCol] using e2 1
  · intro h0
    obtain ⟨i, hi⟩ := hne
    apply hi
    rw [hfx i]
    simp [h0]
  · rw [hsplit]
    refine sum_congr rfl fun i _ => ?_
    rw [hfx i, cross2_sum_right]
    exact sum_congr rfl fun s _ => by rw [cross2_smul_right, slotTorque]

/-- **Freedom from the extreme rays.**  The polygon `p` with depths `z`
*passes the ray test* if for one sense `σ` every extreme ray of the cone `C`
of balanced slot systems (CRIT5-WRITEUP §4) has torque of sign `σ`. -/
def RaysFree [NeZero k] (p : ZMod k → ℝ²) (z : ZMod k → ℝ) : Prop :=
  ∃ σ : ℝ, ∀ x, IsExtremeSlots (slotCol p z) x → 0 < σ * ∑ r, x r * slotTorque p r

/-- **The ray criterion, force form.**  If every extreme ray of `C` has torque
of sign `σ`, so has every nonzero balanced force system. -/
theorem torque_pos_of_extremeRays [NeZero k] {p : ZMod k → ℝ²} (z : ZMod k → ℝ)
    (hp : IsCcwPolygon p) (σ : ℝ)
    (h : ∀ x, IsExtremeSlots (slotCol p z) x → 0 < σ * ∑ r, x r * slotTorque p r)
    {f : ZMod k → ℝ²} (hf : ∀ i, f i ∈ normalConeAt (convexHull ℝ (Set.range p)) (p i))
    (hne : ∃ i, f i ≠ 0) (h1 : ∑ i, f i = 0) (h2 : ∑ i, z i • f i = 0) :
    0 < σ * ∑ i, cross2 (p i) (f i) := by
  obtain ⟨x, hx, hx0, htq⟩ := exists_slots_of_forces z hp hf hne h1 h2
  rw [htq, mul_sum]
  have := pos_of_extremeSlots (slotCol p z) (fun r => σ * slotTorque p r)
    (fun x hx => by have := h x hx; rw [mul_sum] at this; simpa [mul_left_comm] using this) x hx hx0
  simpa [mul_left_comm] using this

/-- Under the ray test no nonzero balanced force system has zero torque. -/
theorem RaysFree.torque_ne_zero [NeZero k] {p : ZMod k → ℝ²} {z : ZMod k → ℝ}
    (hrf : RaysFree p z) (hp : IsCcwPolygon p) {f : ZMod k → ℝ²}
    (hf : ∀ i, f i ∈ normalConeAt (convexHull ℝ (Set.range p)) (p i))
    (hne : ∃ i, f i ≠ 0) (h1 : ∑ i, f i = 0) (h2 : ∑ i, z i • f i = 0) :
    ∑ i, cross2 (p i) (f i) ≠ 0 := by
  obtain ⟨σ, hσ⟩ := hrf
  intro h0
  have := torque_pos_of_extremeRays z hp σ hσ hf hne h1 h2
  rw [h0, mul_zero] at this
  exact lt_irrefl _ this

/-- **The 5-slot test** (no rank condition): if every nonzero balanced slot
system loading at most five slots has torque of sign `σ`, the polygon passes
the ray test (extreme rays load at most `4 + 1` slots). -/
theorem raysFree_of_five_slots {p : ZMod k → ℝ²} {z : ZMod k → ℝ} [NeZero k] (σ : ℝ)
    (h : ∀ x, IsBalancedSlots (slotCol p z) x → x ≠ 0 →
      (univ.filter fun r => x r ≠ 0).card ≤ 5 → 0 < σ * ∑ r, x r * slotTorque p r) :
    RaysFree p z :=
  ⟨σ, fun x hx => h x hx.1 hx.2.1 (by simpa using hx.card_support_le)⟩

/-- **The closed ray test (Cramer form).**  The slot columns have full rank
(four slots `B` with a nonzero determinant), and for one sense `σ`: for every
five distinct slots `T` whose Cramer coefficients `λ_r` (`cramerCoeff`) have
one sign `ε` and are not all zero, `σ ε Σ λ_r τ_{T r} > 0`
(`cramerTorque`, the `5 × 5` determinant `det [τ_r, n_r, z_r n_r]`).
These `T` carry exactly the extreme rays of `C` (the parallel, level and
mixed rays of CRIT5-WRITEUP §4); see `cramerCert_raysFree`. -/
def CramerCert [NeZero k] (p : ZMod k → ℝ²) (z : ZMod k → ℝ) : Prop :=
  (∃ B : Fin 4 → ZMod k × Fin 2, (Matrix.of fun j => slotCol p z (B j)).det ≠ 0) ∧
    ∃ σ : ℝ, ∀ T : Fin 5 → ZMod k × Fin 2, Function.Injective T → ∀ ε : ℝ, (ε = 1 ∨ ε = -1) →
      (∀ r, 0 ≤ ε * cramerCoeff (slotCol p z) T r) → (∃ r, cramerCoeff (slotCol p z) T r ≠ 0) →
      0 < σ * ε * cramerTorque (slotCol p z) (slotTorque p) T

/-- The closed (Cramer) test implies the ray test. -/
theorem cramerCert_raysFree [NeZero k] {p : ZMod k → ℝ²} {z : ZMod k → ℝ}
    (h : CramerCert p z) : RaysFree p z := by
  classical
  obtain ⟨hrank, σ, hσ⟩ := h
  refine ⟨σ, fun x hx => ?_⟩
  have := pos_of_cramer (slotCol p z) (fun r => σ * slotTorque p r) hrank
    (fun T hT ε hε hs hne => by
      have := hσ T hT ε hε hs hne
      simp only [cramerTorque, mul_sum] at this ⊢
      simpa [mul_comm, mul_left_comm, mul_assoc] using this) x hx
  rw [mul_sum]; simpa [mul_left_comm] using this

/-- **The four-column determinant in closed form** (CRIT5-WRITEUP §4, the
Plücker relation): for columns `(n_a, z_a n_a)`,
`Δ = [12][34]⟨13⟩⟨24⟩ − [13][24]⟨12⟩⟨34⟩` with `[ab] = n_a × n_b`,
`⟨ab⟩ = z_b − z_a`. -/
theorem det_slotCols (n : Fin 4 → ℝ²) (z : Fin 4 → ℝ) :
    (Matrix.of fun j : Fin 4 => ![n j 0, n j 1, z j * n j 0, z j * n j 1]).det =
      cross2 (n 0) (n 1) * cross2 (n 2) (n 3) * (z 2 - z 0) * (z 3 - z 1) -
        cross2 (n 0) (n 2) * cross2 (n 1) (n 3) * (z 1 - z 0) * (z 3 - z 2) := by
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_fin_three, Fin.succAbove, cross2]
  ring

end Polygon

section Views

/-- **Lemma 7.1 glue for a torque criterion.**  At the standard view the
silhouette is the cycle `x`, every other point of `V` projects into the
interior, and no nonzero balanced corner-force system of the silhouette has
zero torque.  Then some first-order motion is strictly inward. -/
theorem exists_firstOrderInward_of_torque_ne_zero (V : Finset ℝ³) {k : ℕ} [NeZero k]
    (x : ZMod k → ℝ³) (hxV : ∀ i, x i ∈ V) (hp : IsCcwPolygon (fun i => proj_xy (x i)))
    (hin : ∀ v ∈ V, (∀ i, v ≠ x i) →
      proj_xy v ∈ interior (convexHull ℝ (Set.range fun i => proj_xy (x i))))
    (H : ∀ f : ZMod k → ℝ²,
      (∀ i, f i ∈ normalConeAt (convexHull ℝ (Set.range fun i => proj_xy (x i))) (proj_xy (x i))) →
      (∃ i, f i ≠ 0) → ∑ i, f i = 0 → ∑ i, x i 2 • f i = 0 →
      ∑ i, cross2 (proj_xy (x i)) (f i) ≠ 0) :
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
  refine H (fun i => f (x i)) (fun i => hfN (x i) (hxV i)) ?_ ?_ ?_ ?_
  · by_contra hall; push Not at hall
    by_cases hc : ∃ i, v₀ = x i
    · obtain ⟨i, rfl⟩ := hc; exact hf₀ (hall i)
    · push Not at hc; exact hf₀ (hzero v₀ hv₀ hc)
  · rw [← hred f (fun v h => h)]; exact hE1
  · rw [← hred (fun v => v 2 • f v) (fun v h => by simp [h])]; exact hE2
  · rw [← hred (fun v => cross2 (proj_xy v) (f v)) (fun v h => by simp [h, cross2])]; exact hE3

/-- **The ray test at a rotated view.**  The silhouette of `V` at the view of
`R` is the strictly convex counterclockwise polygon `x` (every other point
inside) and passes the ray test.  Then some first-order motion is strictly
inward.  (No exclusion of horizontal double normals is needed: the ray test
excludes them.) -/
theorem exists_firstOrderInward_image_of_raysFree (V : Finset ℝ³)
    (R : Matrix (Fin 3) (Fin 3) ℝ) {k : ℕ} [NeZero k] (x : ZMod k → ℝ³) (hxV : ∀ i, x i ∈ V)
    (hp : IsCcwPolygon (fun i => proj_xy (R.toEuclideanLin (x i))))
    (hin : ∀ v ∈ V, (∀ i, v ≠ x i) → proj_xy (R.toEuclideanLin v) ∈
      interior (convexHull ℝ (Set.range fun i => proj_xy (R.toEuclideanLin (x i)))))
    (hrf : RaysFree (fun i => proj_xy (R.toEuclideanLin (x i)))
      (fun i => (R.toEuclideanLin (x i)) 2)) :
    ∃ ω τ : ℝ³, FirstOrderInward (V.image R.toEuclideanLin) ω τ := by
  classical
  exact exists_firstOrderInward_of_torque_ne_zero (V.image R.toEuclideanLin)
    (fun i => R.toEuclideanLin (x i)) (fun i => mem_image_of_mem _ (hxV i)) hp
    (by
      intro w hw hc
      obtain ⟨v, hv, rfl⟩ := mem_image.mp hw
      exact hin v hv fun i h => hc i (by rw [h]))
    (fun f hf hne h1 h2 => hrf.torque_ne_zero hp hf hne h1 h2)

/-- **The ray test, Rupert form, at the view of a rotation `R`.** -/
theorem isRupert_of_raysFreeView (V : Finset ℝ³) (R : Matrix (Fin 3) (Fin 3) ℝ)
    (hR : R ∈ SO3) {k : ℕ} [NeZero k] (x : ZMod k → ℝ³) (hxV : ∀ i, x i ∈ V)
    (hp : IsCcwPolygon (fun i => proj_xy (R.toEuclideanLin (x i))))
    (hin : ∀ v ∈ V, (∀ i, v ≠ x i) → proj_xy (R.toEuclideanLin v) ∈
      interior (convexHull ℝ (Set.range fun i => proj_xy (R.toEuclideanLin (x i)))))
    (hrf : RaysFree (fun i => proj_xy (R.toEuclideanLin (x i)))
      (fun i => (R.toEuclideanLin (x i)) 2)) :
    IsRupert V := by
  obtain ⟨ω, τ, h⟩ := exists_firstOrderInward_image_of_raysFree V R x hxV hp hin hrf
  exact isRupert_of_firstOrderInward_image V R hR ω τ h

/-- **The ray test, certificate form** (as `exists_tiltCert_of_depthSeparated`). -/
theorem exists_tiltCert_of_raysFree (V : Finset ℝ³) (R : Matrix (Fin 3) (Fin 3) ℝ)
    (hR : R ∈ SO3) {u₀ : ℝ³} {r : ℝ} (hr : 0 < r) (hRu : R.toEuclideanLin u₀ = r • ez)
    {k : ℕ} [NeZero k] (x : ZMod k → ℝ³) (hxV : ∀ i, x i ∈ V)
    (hp : IsCcwPolygon (fun i => proj_xy (R.toEuclideanLin (x i))))
    (hin : ∀ v ∈ V, (∀ i, v ≠ x i) → proj_xy (R.toEuclideanLin v) ∈
      interior (convexHull ℝ (Set.range fun i => proj_xy (R.toEuclideanLin (x i)))))
    (hrf : RaysFree (fun i => proj_xy (R.toEuclideanLin (x i)))
      (fun i => (R.toEuclideanLin (x i)) 2)) :
    ∃ ω τ : ℝ³, (∀ y ∈ V, TiltCert V u₀ ω τ y) ∧
      ∀ i, 0 < det3 (x (i + 1) - x i) (cross ω (x i) + τ) u₀ ∧
        0 < det3 (x (i + 1) - x i) (cross ω (x (i + 1)) + τ) u₀ :=
  exists_tiltCert_of_firstOrderInward V R hR hr hRu x hxV hp hin
    (exists_firstOrderInward_image_of_raysFree V R x hxV hp hin hrf)

/-- **Proposition 8.8 with a `K′` passing the ray test.**  As
`isRupert_of_chords_depthSeparated`. -/
theorem isRupert_of_chords_raysFree (V M : Finset ℝ³) (R : Matrix (Fin 3) (Fin 3) ℝ)
    (hR : R ∈ SO3) {u₀ : ℝ³} {r : ℝ} (hr : 0 < r) (hRu : R.toEuclideanLin u₀ = r • ez)
    {k : ℕ} [NeZero k] (x : ZMod k → ℝ³) (hxV : ∀ i, x i ∈ V) (hxM : ∀ i, x i ∉ M)
    (hp : IsCcwPolygon (fun i => proj_xy (R.toEuclideanLin (x i))))
    (hin : ∀ v ∈ V, v ∉ M → (∀ i, v ≠ x i) → proj_xy (R.toEuclideanLin v) ∈
      interior (convexHull ℝ (Set.range fun i => proj_xy (R.toEuclideanLin (x i)))))
    (hrf : RaysFree (fun i => proj_xy (R.toEuclideanLin (x i)))
      (fun i => (R.toEuclideanLin (x i)) 2))
    (hM : ∀ m ∈ M, ∃ i : ZMod k, ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
      m = x i + s • (x (i + 1) - x i) + δ • u₀) : IsRupert V := by
  classical
  exact isRupert_of_chords_of_firstOrderInward V M R hR hr hRu x hxV hxM hp hin
    (exists_firstOrderInward_image_of_raysFree (V \ M) R x
      (fun i => mem_sdiff.mpr ⟨hxV i, hxM i⟩) hp
      (fun v hv hvx => hin v (mem_sdiff.mp hv).1 (mem_sdiff.mp hv).2 hvx) hrf) hM

/-- **Theorem 8.9 with a `K_v` passing the ray test.**  As
`isRupert_of_edgeChords_depthSeparated`: two faces share the edge `vw`,
`w = v − h u₀`, `v = x i₀` with the far ends its neighbours, middles `M`. -/
theorem isRupert_of_edgeChords_raysFree (V M : Finset ℝ³) (R : Matrix (Fin 3) (Fin 3) ℝ)
    (hR : R ∈ SO3) {u₀ : ℝ³} {r : ℝ} (hr : 0 < r) (hRu : R.toEuclideanLin u₀ = r • ez)
    {k : ℕ} [NeZero k] (x : ZMod k → ℝ³) (i₀ : ZMod k) (w : ℝ³) (h : ℝ) (hwV : w ∈ V)
    (hw : w = x i₀ - h • u₀) (hh : h ≠ 0) (hxV : ∀ i, x i ∈ V) (hxM : ∀ i, x i ∉ M)
    (hp : IsCcwPolygon (fun i => proj_xy (R.toEuclideanLin (x i))))
    (hin : ∀ v ∈ V, v ∉ M → v ≠ w → (∀ i, v ≠ x i) → proj_xy (R.toEuclideanLin v) ∈
      interior (convexHull ℝ (Set.range fun i => proj_xy (R.toEuclideanLin (x i)))))
    (hrf : RaysFree (fun i => proj_xy (R.toEuclideanLin (x i)))
      (fun i => (R.toEuclideanLin (x i)) 2))
    (hM : ∀ m ∈ M, EdgeMiddle u₀ (x i₀) w (x (i₀ + 1)) (x (i₀ - 1)) h m) : IsRupert V := by
  classical
  exact isRupert_of_edgeChords_of_firstOrderInward V M R hR hr hRu x i₀ w h hwV hw hh hxV hxM hp
    hin (exists_firstOrderInward_image_of_raysFree ((V \ M).erase w) R x
      (fun i => mem_erase.mpr ⟨corner_ne_axle hr hRu hp hw hh i, mem_sdiff.mpr ⟨hxV i, hxM i⟩⟩) hp
      (fun v hv hvx => by
        obtain ⟨hvw, hv'⟩ := mem_erase.mp hv
        exact hin v (mem_sdiff.mp hv').1 (mem_sdiff.mp hv').2 hvw hvx) hrf) hM

end Views

end Minimality

end
