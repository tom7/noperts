module

public import Mathlib
public import Minimality.Unimodal

@[expose] public section

/-!
# The rim-cell test (Lemma Q4)

Setting: the rim of a view is a 4-cycle `y 0, y 1, y 2, y 3` of points of `ℝⁿ` (`n = 3` in use), a
view is a vector `c` with depths `z i = (Γ c) ⬝ᵥ y i` for an invertible matrix `Γ` (a Gram matrix),
and the views of a *cell* form a convex set `A` not containing `0`.

* `exists_mixed_sign`: the convexity argument.  Finitely many linear forms on a convex set `A` on
  which they have no common zero: if some form is negative at one point of `A` and some form is
  positive at another, then at one point of `A` both signs occur.
* `exists_mixed_sign_of_closure`: the same when the two signs occur only at points of `closure A`
  (for instance at extreme rays of the closure of an open cone).
* `exists_mem_forall_ne_zero`: an open nonempty set contains a point where finitely many nonzero
  continuous linear forms are all nonzero.
* `isCyclicUnimodal_four` (Lemma AQ for `k = 4`): distinct depths on a 4-cycle are cyclically
  unimodal iff one diagonal does not lie entirely above the other.
* `rimCell_exists_unimodal` (Lemma Q4, "if"): if the forms `(Γ g) ⬝ᵥ (y i - y j)`, `i ∈ {0, 2}`,
  `j ∈ {1, 3}`, take both strict signs at points `g` of `closure A`, then some view of the open
  convex cell `A` has distinct, cyclically unimodal depths.
* `rimCell_no_unimodal` (Lemma Q4, "only if"): if all forms are `≥ 0` (or all `≤ 0`) at generators
  of `A`, no view of `A` has unimodal depths.
* `isRupert_of_rimCell`: the certificate form, feeding `isRupert_of_genericUnimodalView`.
-/

set_option autoImplicit false

namespace Minimality.RimCell

open Finset Matrix
open scoped Topology

/-! ### Linear forms on a convex set -/

/-- **Convexity step of Lemma Q4.** -/
theorem exists_mixed_sign {E ι : Type*} [AddCommGroup E] [Module ℝ E]
    (f : ι → E →ₗ[ℝ] ℝ) {A : Set E} (hA : Convex ℝ A)
    (hz : ∀ c ∈ A, ∃ k, f k c ≠ 0) {c₁ c₂ : E} (h₁ : c₁ ∈ A) (h₂ : c₂ ∈ A)
    (hn : ∃ k, f k c₁ < 0) (hp : ∃ k, 0 < f k c₂) :
    ∃ c ∈ A, (∃ k, f k c < 0) ∧ ∃ k, 0 < f k c := by
  by_contra hcon
  push Not at hcon
  -- the point on the segment
  let pt : ℝ → E := fun t => c₁ + t • (c₂ - c₁)
  have hpt : ∀ t ∈ Set.Icc (0:ℝ) 1, pt t ∈ A := fun t ht =>
    hA.add_smul_sub_mem h₁ h₂ ht
  have hf : ∀ k t, f k (pt t) = f k c₁ + t * (f k c₂ - f k c₁) := by
    intro k t; simp [pt, map_add, map_smul, map_sub]
  have hcont : ∀ k, Continuous fun t : ℝ => f k c₁ + t * (f k c₂ - f k c₁) := fun k => by fun_prop
  set U : Set ℝ := {t | ∀ k, f k c₁ + t * (f k c₂ - f k c₁) ≤ 0} with hU
  set W : Set ℝ := {t | ∀ k, 0 ≤ f k c₁ + t * (f k c₂ - f k c₁)} with hW
  have hUc : IsClosed U := by
    have : U = ⋂ k, {t | f k c₁ + t * (f k c₂ - f k c₁) ≤ 0} := by ext; simp [hU]
    rw [this]; exact isClosed_iInter fun k => isClosed_le (hcont k) continuous_const
  have hWc : IsClosed W := by
    have : W = ⋂ k, {t | 0 ≤ f k c₁ + t * (f k c₂ - f k c₁)} := by ext; simp [hW]
    rw [this]; exact isClosed_iInter fun k => isClosed_le continuous_const (hcont k)
  have hcover : Set.Icc (0:ℝ) 1 ⊆ U ∪ W := by
    intro t ht
    by_cases hneg : ∃ k, f k (pt t) < 0
    · left
      intro k
      have := hcon (pt t) (hpt t ht) hneg k
      rw [← hf]; exact this
    · right
      push Not at hneg
      intro k; rw [← hf]; exact hneg k
  have h0 : (0:ℝ) ∈ Set.Icc (0:ℝ) 1 ∩ U := by
    refine ⟨⟨le_rfl, zero_le_one⟩, fun k => ?_⟩
    have := hcon c₁ h₁ hn k; simpa using this
  have h1 : (1:ℝ) ∈ Set.Icc (0:ℝ) 1 ∩ W := by
    refine ⟨⟨zero_le_one, le_rfl⟩, fun k => ?_⟩
    obtain ⟨l, hl⟩ := hp
    by_contra hk
    push Not at hk
    have := hcon c₂ h₂ ⟨k, by simpa using hk⟩ l
    linarith
  obtain ⟨t, ht, htU, htW⟩ := isPreconnected_closed_iff.1 isPreconnected_Icc U W hUc hWc hcover ⟨0, h0⟩ ⟨1, h1⟩
  obtain ⟨k, hk⟩ := hz _ (hpt t ht)
  have a := htU k
  have b := htW k
  apply hk
  rw [hf]; linarith

/-- The same when the two signs occur only at points of `closure A`. -/
theorem exists_mixed_sign_of_closure {E ι : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] (f : ι → E →ₗ[ℝ] ℝ) (hfc : ∀ k, Continuous (f k))
    {A : Set E} (hA : Convex ℝ A) (hz : ∀ c ∈ A, ∃ k, f k c ≠ 0) {g₁ g₂ : E}
    (h₁ : g₁ ∈ closure A) (h₂ : g₂ ∈ closure A)
    (hn : ∃ k, f k g₁ < 0) (hp : ∃ k, 0 < f k g₂) :
    ∃ c ∈ A, (∃ k, f k c < 0) ∧ ∃ k, 0 < f k c := by
  obtain ⟨k, hk⟩ := hn
  obtain ⟨l, hl⟩ := hp
  obtain ⟨c₁, hc₁, hc₁'⟩ := mem_closure_iff.1 h₁ {c | f k c < 0} (isOpen_lt (hfc k) continuous_const) hk
  obtain ⟨c₂, hc₂, hc₂'⟩ := mem_closure_iff.1 h₂ {c | 0 < f l c} (isOpen_lt continuous_const (hfc l)) hl
  exact exists_mixed_sign f hA hz hc₁' hc₂' ⟨k, hc₁⟩ ⟨l, hc₂⟩

/-- An open nonempty set contains a point where finitely many nonzero continuous linear forms
are all nonzero. -/
theorem exists_mem_forall_ne_zero {E ι : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    (g : ι → E →ₗ[ℝ] ℝ) (s : Finset ι) (hg : ∀ j ∈ s, g j ≠ 0) :
    ∀ U : Set E, IsOpen U → U.Nonempty → ∃ c ∈ U, ∀ j ∈ s, g j c ≠ 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => intro U _ hne; obtain ⟨c, hc⟩ := hne; exact ⟨c, hc, by simp⟩
  | insert a s ha ih =>
    intro U hU hne
    obtain ⟨c, hc, hcs⟩ := ih (fun j hj => hg j (mem_insert_of_mem hj)) U hU hne
    by_cases hca : g a c = 0
    · -- move off the hyperplane
      have hga : g a ≠ 0 := hg a (mem_insert_self _ _)
      obtain ⟨d, hd⟩ : ∃ d, g a d ≠ 0 := by
        by_contra h; push Not at h; exact hga (LinearMap.ext h)
      -- small multiples of `d` stay in `U` ; avoid finitely many bad values of the parameter
      have hcont : Continuous fun t : ℝ => c + t • d := by fun_prop
      have hopen : IsOpen {t : ℝ | c + t • d ∈ U} := hU.preimage hcont
      have h0 : (0:ℝ) ∈ {t : ℝ | c + t • d ∈ U} := by simpa using hc
      obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hopen 0 h0
      -- bad parameters: `t` with `g j (c + t d) = 0` for some `j ∈ s`
      have hbad : ∀ j ∈ s, {t : ℝ | g j (c + t • d) = 0}.Finite ∨ g j d = 0 := by
        intro j _
        by_cases hjd : g j d = 0
        · exact Or.inr hjd
        · left
          refine (Set.finite_singleton (-(g j c) / g j d)).subset fun t ht => ?_
          simp only [Set.mem_ofPred_eq, map_add, map_smul, smul_eq_mul] at ht
          simp only [Set.mem_singleton_iff]
          field_simp
          linarith
      -- choose `t` in the ball, nonzero and avoiding the finitely many bad values
      have hfin : {t : ℝ | ∃ j ∈ s, g j d ≠ 0 ∧ g j (c + t • d) = 0}.Finite := by
        have : {t : ℝ | ∃ j ∈ s, g j d ≠ 0 ∧ g j (c + t • d) = 0} ⊆
            ⋃ j ∈ s, {t : ℝ | g j d ≠ 0 ∧ g j (c + t • d) = 0} := by
          intro t ht; obtain ⟨j, hj, h⟩ := ht; simp only [Set.mem_iUnion]; exact ⟨j, hj, h⟩
        refine Set.Finite.subset (Set.Finite.biUnion s.finite_toSet fun j hj => ?_) this
        rcases hbad j hj with h | h
        · exact h.subset fun t ht => ht.2
        · exact (Set.finite_empty).subset fun t ht => (ht.1 h).elim
      have hinf : (Metric.ball (0:ℝ) ε \ ({0} ∪ {t : ℝ | ∃ j ∈ s, g j d ≠ 0 ∧ g j (c + t • d) = 0})).Nonempty := by
        have hI : (Metric.ball (0:ℝ) ε).Infinite := by
          have : (Set.Ioo (-ε) ε).Infinite := Set.Ioo_infinite (by linarith)
          exact this.mono fun t ht => by
            simp only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]; exact ht
        exact (hI.sdiff ((Set.finite_singleton 0).union hfin)).nonempty
      obtain ⟨t, ht, htn⟩ := hinf
      simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_ofPred_eq, not_or, not_exists, not_and] at htn
      refine ⟨c + t • d, hεU ht, fun j hj => ?_⟩
      rcases mem_insert.1 hj with rfl | hjs
      · simp [hca, hd, htn.1]
      · by_cases hjd : g j d = 0
        · simp [hjd, hcs j hjs]
        · exact fun h => htn.2 j hjs hjd h
    · refine ⟨c, hc, fun j hj => ?_⟩
      rcases mem_insert.1 hj with rfl | hjs
      · exact hca
      · exact hcs j hjs

/-! ### Lemma AQ for a 4-cycle -/

/-- **Lemma AQ, `k = 4`.**  Distinct depths on a 4-cycle are cyclically unimodal unless one
diagonal lies entirely above the other: if some `z i - z j` (`i ∈ {0, 2}`, `j ∈ {1, 3}`) is
negative and some is positive. -/
theorem isCyclicUnimodal_four (z : ZMod 4 → ℝ) (hinj : Function.Injective z)
    (hn : z 0 < z 1 ∨ z 0 < z 3 ∨ z 2 < z 1 ∨ z 2 < z 3)
    (hp : z 1 < z 0 ∨ z 3 < z 0 ∨ z 1 < z 2 ∨ z 3 < z 2) :
    Minimality.IsCyclicUnimodal z := by
  refine ⟨hinj, ?_⟩
  have d01 : z 0 ≠ z 1 := fun h => by have := hinj h; revert this; decide
  have d02 : z 0 ≠ z 2 := fun h => by have := hinj h; revert this; decide
  have d03 : z 0 ≠ z 3 := fun h => by have := hinj h; revert this; decide
  have d12 : z 1 ≠ z 2 := fun h => by have := hinj h; revert this; decide
  have d13 : z 1 ≠ z 3 := fun h => by have := hinj h; revert this; decide
  have d23 : z 2 ≠ z 3 := fun h => by have := hinj h; revert this; decide
  rw [Finset.card_filter]
  have hu : (Finset.univ : Finset (ZMod 4)) = {0, 1, 2, 3} := by decide
  rw [hu]
  have e1 : (0 : ZMod 4) - 1 = 3 := by decide
  have e2 : (1 : ZMod 4) - 1 = 0 := by decide
  have e3 : (2 : ZMod 4) - 1 = 1 := by decide
  have e4 : (3 : ZMod 4) - 1 = 2 := by decide
  have f1 : (0 : ZMod 4) + 1 = 1 := by decide
  have f2 : (1 : ZMod 4) + 1 = 2 := by decide
  have f3 : (2 : ZMod 4) + 1 = 3 := by decide
  have f4 : (3 : ZMod 4) + 1 = 0 := by decide
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, e1, e2, e3, e4, f1, f2, f3, f4]
  rcases lt_or_gt_of_ne d01 with a | a <;> rcases lt_or_gt_of_ne d02 with b | b <;>
    rcases lt_or_gt_of_ne d03 with c | c <;> rcases lt_or_gt_of_ne d12 with d | d <;>
    rcases lt_or_gt_of_ne d13 with e | e <;> rcases lt_or_gt_of_ne d23 with f | f <;>
    simp [*, not_lt_of_gt] <;> (exfalso; rcases hn with h | h | h | h <;> rcases hp with h' | h' | h' | h' <;> linarith)

/-! ### Depth forms -/

section Depth

variable {n : ℕ}

/-- The linear form `c ↦ (Γ c) ⬝ᵥ (a - b)`: the depth difference `z a - z b` of the view `c`
when the depth of a point `v` is `(Γ c) ⬝ᵥ v`. -/
noncomputable def depthDiff (Γ : Matrix (Fin n) (Fin n) ℝ) (a b : Fin n → ℝ) :
    (Fin n → ℝ) →ₗ[ℝ] ℝ where
  toFun c := (Γ *ᵥ c) ⬝ᵥ (a - b)
  map_add' c d := by simp [Matrix.mulVec_add, add_dotProduct]; ring
  map_smul' r c := by simp [Matrix.mulVec_smul, smul_dotProduct]; ring

theorem depthDiff_apply (Γ : Matrix (Fin n) (Fin n) ℝ) (a b c : Fin n → ℝ) :
    depthDiff Γ a b c = (Γ *ᵥ c) ⬝ᵥ a - (Γ *ᵥ c) ⬝ᵥ b := by
  simp [depthDiff, dotProduct_sub]

theorem continuous_depthDiff (Γ : Matrix (Fin n) (Fin n) ℝ) (a b : Fin n → ℝ) :
    Continuous (depthDiff Γ a b) := by
  have : (depthDiff Γ a b : (Fin n → ℝ) → ℝ) = fun c => (Γ *ᵥ c) ⬝ᵥ (a - b) := rfl
  rw [this]
  exact (continuous_const.matrix_mulVec continuous_id).dotProduct continuous_const

theorem depthDiff_ne_zero {Γ : Matrix (Fin n) (Fin n) ℝ} (hΓ : Γ.det ≠ 0) {a b : Fin n → ℝ}
    (hab : a ≠ b) : depthDiff Γ a b ≠ 0 := by
  intro h
  have hu : IsUnit Γ.det := isUnit_iff_ne_zero.2 hΓ
  have h1 := LinearMap.congr_fun h (Γ⁻¹ *ᵥ (a - b))
  simp only [depthDiff, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.zero_apply,
    Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec] at h1
  exact hab (sub_eq_zero.1 (dotProduct_self_eq_zero.1 h1))

/-- The pairs `(i, j)` of opposite-diagonal corners. -/
def diagPairs : Finset (ZMod 4 × ZMod 4) := ({0, 2} : Finset (ZMod 4)) ×ˢ ({1, 3} : Finset (ZMod 4))

/-- The depth of the corner `y i` at the view `c`. -/
noncomputable def depth (Γ : Matrix (Fin n) (Fin n) ℝ) (y : ZMod 4 → Fin n → ℝ)
    (c : Fin n → ℝ) : ZMod 4 → ℝ := fun i => (Γ *ᵥ c) ⬝ᵥ y i

/-- **Lemma Q4 ("if"), the 4-gon rim-cell test.**  `A` is an open convex set of views not
containing `0`, `Γ` is invertible, `y 0, y 1, y 2, y 3` are four distinct corners whose diagonal
differences `y i - y j` (`i ∈ {0, 2}`, `j ∈ {1, 3}`) span the space (the corners are not
coplanar).  If the forms `(Γ g) ⬝ᵥ (y i - y j)` take a strictly negative value at some `g` of
`closure A` and a strictly positive value at some `g'` of `closure A` (for a cone: at its extreme
rays), then some view `c ∈ A` has distinct, cyclically unimodal depths. -/
theorem rimCell_exists_unimodal {n : ℕ} (Γ : Matrix (Fin n) (Fin n) ℝ) (hΓ : Γ.det ≠ 0)
    (y : ZMod 4 → Fin n → ℝ) (hy : Function.Injective y)
    (hspan : ∀ w : Fin n → ℝ, (∀ p ∈ diagPairs, w ⬝ᵥ (y p.1 - y p.2) = 0) → w = 0)
    {A : Set (Fin n → ℝ)} (hAo : IsOpen A) (hAc : Convex ℝ A) (hA0 : (0 : Fin n → ℝ) ∉ A)
    {g g' : Fin n → ℝ} (hg : g ∈ closure A) (hg' : g' ∈ closure A)
    (hneg : ∃ p ∈ diagPairs, (Γ *ᵥ g) ⬝ᵥ (y p.1 - y p.2) < 0)
    (hpos : ∃ p ∈ diagPairs, 0 < (Γ *ᵥ g') ⬝ᵥ (y p.1 - y p.2)) :
    ∃ c ∈ A, Minimality.IsCyclicUnimodal (depth Γ y c) := by
  classical
  have hu : IsUnit Γ.det := isUnit_iff_ne_zero.2 hΓ
  let f : diagPairs → (Fin n → ℝ) →ₗ[ℝ] ℝ := fun p => depthDiff Γ (y p.1.1) (y p.1.2)
  have hfa : ∀ p c, f p c = (Γ *ᵥ c) ⬝ᵥ (y p.1.1 - y p.1.2) := fun p c => rfl
  have hz : ∀ c ∈ A, ∃ k, f k c ≠ 0 := by
    intro c hc
    by_contra h
    push Not at h
    have hc0 : c ≠ 0 := fun h0 => hA0 (h0 ▸ hc)
    apply hc0
    have hw := hspan (Γ *ᵥ c) fun p hp => h ⟨p, hp⟩
    have := congrArg (fun w => Γ⁻¹ *ᵥ w) hw
    simpa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu] using this
  have hfc : ∀ k, Continuous (f k) := fun k => continuous_depthDiff _ _ _
  obtain ⟨⟨p, hp⟩, hk⟩ : ∃ k : diagPairs, f k g < 0 := by
    obtain ⟨p, hp, h⟩ := hneg; exact ⟨⟨p, hp⟩, by rw [hfa]; exact h⟩
  obtain ⟨⟨q, hq⟩, hl⟩ : ∃ k : diagPairs, 0 < f k g' := by
    obtain ⟨p, hp, h⟩ := hpos; exact ⟨⟨p, hp⟩, by rw [hfa]; exact h⟩
  obtain ⟨c₀, hc₀, hneg₀, hpos₀⟩ := exists_mixed_sign_of_closure f hfc hAc hz hg hg'
    ⟨⟨p, hp⟩, hk⟩ ⟨⟨q, hq⟩, hl⟩
  -- an open set of such views
  let U : Set (Fin n → ℝ) := A ∩ (⋃ k, {c | f k c < 0}) ∩ (⋃ k, {c | 0 < f k c})
  have hUo : IsOpen U :=
    (hAo.inter (isOpen_iUnion fun k => isOpen_lt (hfc k) continuous_const)).inter
      (isOpen_iUnion fun k => isOpen_lt continuous_const (hfc k))
  have hUne : U.Nonempty := by
    obtain ⟨k, hk⟩ := hneg₀; obtain ⟨l, hl⟩ := hpos₀
    exact ⟨c₀, ⟨hc₀, Set.mem_iUnion.2 ⟨k, hk⟩⟩, Set.mem_iUnion.2 ⟨l, hl⟩⟩
  -- avoid the hyperplanes `z i = z j`
  let S : Finset (ZMod 4 × ZMod 4) := Finset.univ.filter fun p => p.1 ≠ p.2
  obtain ⟨c, hcU, hcS⟩ := exists_mem_forall_ne_zero
    (fun p : ZMod 4 × ZMod 4 => depthDiff Γ (y p.1) (y p.2)) S
    (fun p hp => depthDiff_ne_zero hΓ fun h => by
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      exact hp (hy h)) U hUo hUne
  obtain ⟨⟨hcA, hcn⟩, hcp⟩ := hcU
  refine ⟨c, hcA, ?_⟩
  have hd : ∀ i j : ZMod 4, i ≠ j → depth Γ y c i ≠ depth Γ y c j := by
    intro i j hij h
    have := hcS (i, j) (by simp [S, hij])
    apply this
    simp only [depthDiff_apply]
    simp only [depth] at h
    linarith
  have hinj : Function.Injective (depth Γ y c) := fun i j h => by
    by_contra hij; exact hd i j hij h
  obtain ⟨k, hk⟩ := Set.mem_iUnion.1 hcn
  obtain ⟨l, hl⟩ := Set.mem_iUnion.1 hcp
  have hsgn : ∀ m : diagPairs, f m c = depth Γ y c m.1.1 - depth Γ y c m.1.2 := fun m => by
    rw [hfa, dotProduct_sub]; rfl
  have hmem : ∀ m : diagPairs, (m.1.1 = 0 ∨ m.1.1 = 2) ∧ (m.1.2 = 1 ∨ m.1.2 = 3) := by
    rintro ⟨⟨a, b⟩, hm⟩
    simpa [diagPairs] using hm
  have hk' : f k c < 0 := hk
  have hl' : 0 < f l c := hl
  apply isCyclicUnimodal_four _ hinj
  · have h1 := hsgn k; have h2 := hmem k
    rcases h2 with ⟨h2 | h2, h3 | h3⟩ <;> rw [h2, h3] at h1 <;> simp only [depth] at h1 ⊢ <;>
    first
    | exact Or.inl (by linarith)
    | exact Or.inr (Or.inl (by linarith))
    | exact Or.inr (Or.inr (Or.inl (by linarith)))
    | exact Or.inr (Or.inr (Or.inr (by linarith)))
  · have h1 := hsgn l; have h2 := hmem l
    rcases h2 with ⟨h2 | h2, h3 | h3⟩ <;> rw [h2, h3] at h1 <;> simp only [depth] at h1 ⊢ <;>
    first
    | exact Or.inl (by linarith)
    | exact Or.inr (Or.inl (by linarith))
    | exact Or.inr (Or.inr (Or.inl (by linarith)))
    | exact Or.inr (Or.inr (Or.inr (by linarith)))

/-- A diagonal lying entirely above the other gives two peaks. -/
theorem not_isCyclicUnimodal_four_of_above (z : ZMod 4 → ℝ)
    (h : (z 1 < z 0 ∧ z 3 < z 0 ∧ z 1 < z 2 ∧ z 3 < z 2) ∨
      (z 0 < z 1 ∧ z 0 < z 3 ∧ z 2 < z 1 ∧ z 2 < z 3)) : ¬ Minimality.IsCyclicUnimodal z := by
  classical
  rintro ⟨-, hc⟩
  have e1 : (0 : ZMod 4) - 1 = 3 := by decide
  have e2 : (1 : ZMod 4) - 1 = 0 := by decide
  have e3 : (2 : ZMod 4) - 1 = 1 := by decide
  have e4 : (3 : ZMod 4) - 1 = 2 := by decide
  have f1 : (0 : ZMod 4) + 1 = 1 := by decide
  have f2 : (1 : ZMod 4) + 1 = 2 := by decide
  have f3 : (2 : ZMod 4) + 1 = 3 := by decide
  have f4 : (3 : ZMod 4) + 1 = 0 := by decide
  rcases h with ⟨a, b, c, d⟩ | ⟨a, b, c, d⟩
  · have hs : ({0, 2} : Finset (ZMod 4)) ⊆
        Finset.univ.filter (fun i : ZMod 4 => z (i - 1) < z i ∧ z (i + 1) < z i) := by
      intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl <;> simp [*]
    have := Finset.card_le_card hs
    rw [hc] at this
    have h2 : ({0, 2} : Finset (ZMod 4)).card = 2 := by decide
    omega
  · have hs : ({1, 3} : Finset (ZMod 4)) ⊆
        Finset.univ.filter (fun i : ZMod 4 => z (i - 1) < z i ∧ z (i + 1) < z i) := by
      intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl <;> simp [*]
    have := Finset.card_le_card hs
    rw [hc] at this
    have h2 : ({1, 3} : Finset (ZMod 4)).card = 2 := by decide
    omega

/-- A nonzero linear form that is `≥ 0` at the generators of an open set `A` of nonnegative
combinations is `> 0` on `A`. -/
theorem pos_of_nonneg_gen {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] (f : E →ₗ[ℝ] ℝ) (hf : f ≠ 0) {A : Set E}
    (hAo : IsOpen A) (hnn : ∀ c ∈ A, 0 ≤ f c) : ∀ c ∈ A, 0 < f c := by
  intro c hc
  rcases (hnn c hc).lt_or_eq with h | h
  · exact h
  · exfalso
    obtain ⟨d, hd⟩ : ∃ d, f d ≠ 0 := by
      by_contra h; push Not at h; exact hf (LinearMap.ext h)
    wlog hd0 : 0 < f d generalizing d
    · exact this (-d) (by simpa using hd) (by simp; exact lt_of_le_of_ne (not_lt.1 hd0) hd)
    have hcont : Continuous fun t : ℝ => c - t • d := by fun_prop
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (hAo.preimage hcont) 0 (by simpa using hc)
    have hmem : ε / 2 ∈ Metric.ball (0:ℝ) ε := by
      simp only [Metric.mem_ball, Real.dist_eq, sub_zero]; rw [abs_of_pos (by linarith)]; linarith
    have := hnn _ (hball hmem)
    simp [map_sub, map_smul, ← h] at this
    nlinarith

/-- **Lemma Q4 ("only if").**  If `A` is an open set of nonnegative combinations of the vectors
`G` (e.g. the extreme rays of the closure of an open cone) and all forms `(Γ g) ⬝ᵥ (y i - y j)`
are `≥ 0` on `G` (or all `≤ 0`), then no view of `A` has unimodal depths: one diagonal lies above
the other throughout `A`. -/
theorem rimCell_no_unimodal {n : ℕ} (Γ : Matrix (Fin n) (Fin n) ℝ) (hΓ : Γ.det ≠ 0)
    (y : ZMod 4 → Fin n → ℝ) (hy : Function.Injective y) {A : Set (Fin n → ℝ)} (hAo : IsOpen A)
    (G : Finset (Fin n → ℝ))
    (hAG : ∀ c ∈ A, ∃ a : (Fin n → ℝ) → ℝ, (∀ g ∈ G, 0 ≤ a g) ∧ c = ∑ g ∈ G, a g • g)
    (hsign : (∀ g ∈ G, ∀ p ∈ diagPairs, 0 ≤ (Γ *ᵥ g) ⬝ᵥ (y p.1 - y p.2)) ∨
      (∀ g ∈ G, ∀ p ∈ diagPairs, (Γ *ᵥ g) ⬝ᵥ (y p.1 - y p.2) ≤ 0)) :
    ∀ c ∈ A, ¬ Minimality.IsCyclicUnimodal (depth Γ y c) := by
  have hne : ∀ p ∈ diagPairs, y p.1 ≠ y p.2 := by
    intro p hp h
    have := hy h
    simp only [diagPairs, Finset.mem_product, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with ⟨h1 | h1, h2 | h2⟩ <;> rw [h1, h2] at this <;> revert this <;> decide
  have key : ∀ (s : ℝ) (p : ZMod 4 × ZMod 4), p ∈ diagPairs → (s = 1 ∨ s = -1) →
      (∀ g ∈ G, 0 ≤ s * depthDiff Γ (y p.1) (y p.2) g) → ∀ c ∈ A, 0 < s * depthDiff Γ (y p.1) (y p.2) c := by
    intro s p hp hs hG
    have hf : s • depthDiff Γ (y p.1) (y p.2) ≠ 0 := by
      intro h0
      have := depthDiff_ne_zero hΓ (hne p hp)
      apply this
      rcases hs with rfl | rfl
      · simpa using h0
      · simpa using h0
    refine pos_of_nonneg_gen (s • depthDiff Γ (y p.1) (y p.2)) hf hAo ?_
    intro c hc
    obtain ⟨a, ha, rfl⟩ := hAG c hc
    simp only [LinearMap.smul_apply, smul_eq_mul, map_sum, map_smul]
    exact Finset.sum_nonneg fun g hg => by
      have := mul_nonneg (ha g hg) (hG g hg); linarith
  intro c hc
  apply not_isCyclicUnimodal_four_of_above
  have hd : ∀ i j : ZMod 4, depthDiff Γ (y i) (y j) c = depth Γ y c i - depth Γ y c j := fun i j => by
    rw [depthDiff_apply]; rfl
  rcases hsign with h | h
  · left
    have k := fun p (hp : p ∈ diagPairs) => key 1 p hp (Or.inl rfl)
      (fun g hg => by simpa [depthDiff_apply] using h g hg p hp) c hc
    have k01 := k (0, 1) (by decide); have k03 := k (0, 3) (by decide)
    have k21 := k (2, 1) (by decide); have k23 := k (2, 3) (by decide)
    simp only [one_mul, hd] at k01 k03 k21 k23
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  · right
    have k := fun p (hp : p ∈ diagPairs) => key (-1) p hp (Or.inr rfl)
      (fun g hg => by simpa [depthDiff_apply] using h g hg p hp) c hc
    have k01 := k (0, 1) (by decide); have k03 := k (0, 3) (by decide)
    have k21 := k (2, 1) (by decide); have k23 := k (2, 3) (by decide)
    simp only [neg_one_mul, hd] at k01 k03 k21 k23
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- **A rim-cell certificate gives Rupert.**  Let `A` be an open convex cell of views (`0 ∉ A`) and
`x 0, …, x 3` four points of `V`.  Suppose every view `c ∈ A` is realised by a rotation `R` at
which `x` is a strictly convex counterclockwise silhouette with every other point of `V` strictly
inside, and whose corner depths are `(Γ c) ⬝ᵥ y i`.  If the Q4 forms take both strict signs on
`closure A`, then `V` is Rupert. -/
theorem isRupert_of_rimCell (V : Finset ℝ³) (x : ZMod 4 → ℝ³) (hxV : ∀ i, x i ∈ V)
    {n : ℕ} (Γ : Matrix (Fin n) (Fin n) ℝ) (hΓ : Γ.det ≠ 0)
    (y : ZMod 4 → Fin n → ℝ) (hy : Function.Injective y)
    (hspan : ∀ w : Fin n → ℝ, (∀ p ∈ diagPairs, w ⬝ᵥ (y p.1 - y p.2) = 0) → w = 0)
    {A : Set (Fin n → ℝ)} (hAo : IsOpen A) (hAc : Convex ℝ A) (hA0 : (0 : Fin n → ℝ) ∉ A)
    (hview : ∀ c ∈ A, ∃ R : Matrix (Fin 3) (Fin 3) ℝ, R ∈ SO3 ∧
      IsCcwPolygon (fun i => proj_xy (R.toEuclideanLin (x i))) ∧
      (∀ v ∈ V, (∀ i, v ≠ x i) → proj_xy (R.toEuclideanLin v) ∈
        interior (convexHull ℝ (Set.range fun i => proj_xy (R.toEuclideanLin (x i))))) ∧
      ∀ i, (R.toEuclideanLin (x i)) 2 = (Γ *ᵥ c) ⬝ᵥ y i)
    {g g' : Fin n → ℝ} (hg : g ∈ closure A) (hg' : g' ∈ closure A)
    (hneg : ∃ p ∈ diagPairs, (Γ *ᵥ g) ⬝ᵥ (y p.1 - y p.2) < 0)
    (hpos : ∃ p ∈ diagPairs, 0 < (Γ *ᵥ g') ⬝ᵥ (y p.1 - y p.2)) :
    IsRupert V := by
  obtain ⟨c, hcA, hcu⟩ := rimCell_exists_unimodal Γ hΓ y hy hspan hAo hAc hA0 hg hg' hneg hpos
  obtain ⟨R, hR, hp, hin, hz⟩ := hview c hcA
  refine isRupert_of_genericUnimodalView V R hR x hxV hp hin ?_
  have : (fun i => (R.toEuclideanLin (x i)) 2) = depth Γ y c := funext hz
  rw [this]; exact hcu

end Depth


end Minimality.RimCell
