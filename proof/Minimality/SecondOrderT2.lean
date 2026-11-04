module

public import Minimality.SecondOrder

@[expose] public section

/-!
# Theorem T2(a)

nopert229/out/bottleneck/virial/draft.md §2.  At the standard view, a weakly inward first-order motion `(ω, τ)`
(every vertex/edge pair slack or tight with `⟪n, screenVel⟫ ≤ 0`) gives a passage unless some nonzero load `λ ≥ 0`
on the doubly tight pairs, with force balance, screen torque balance and depth balance, has second-order term
`Σ λ ⟪n, P(ω×(ω×v))⟫ ≥ 0` (`isRupert_of_secondOrder_noBalanced`).  The step from loads to the second-order data
`(γ, β)` is the Motzkin alternative `exists_strict_of_no_balanced`.
-/
namespace Minimality
open scoped RealInnerProductSpace Matrix Topology
open Filter

theorem exists_strict_of_no_balanced {κ E : Type*} [Fintype κ] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (a : κ → E) (b : κ → ℝ)
    (h : ∀ lam : κ → ℝ, (∀ k, 0 ≤ lam k) → (∃ k, lam k ≠ 0) → ∑ k, lam k • a k = 0 → 0 < ∑ k, lam k * b k) :
    ∃ x : E, ∀ k, ⟪a k, x⟫ < b k := by
  classical
  let g : Option κ → E × ℝ := fun i => match i with
    | none => (0, -1)
    | some k => (a k, -b k)
  let L : (Option κ → ℝ) →ₗ[ℝ] E × ℝ := ∑ i, (LinearMap.proj i).smulRight (g i)
  have hL : ∀ μ, L μ = ∑ i, μ i • g i := by
    intro μ; simp [L]
  let t : Set (E × ℝ) := L '' stdSimplex ℝ (Option κ)
  have ht1 : Convex ℝ t := (convex_stdSimplex ℝ _).linear_image L
  have ht2 : IsClosed t :=
    ((isCompact_stdSimplex ℝ (Option κ) : IsCompact (stdSimplex ℝ (Option κ))).image (LinearMap.continuous_of_finiteDimensional L)).isClosed
  have h0 : (0 : E × ℝ) ∉ t := by
    rintro ⟨μ, ⟨hμ0, hμ1⟩, hμ⟩
    rw [hL, Fintype.sum_option] at hμ
    have h1 := congrArg Prod.fst hμ
    have h2 := congrArg Prod.snd hμ
    simp [g, Prod.fst_sum, Prod.snd_sum] at h1 h2
    rw [Fintype.sum_option] at hμ1
    have hb : ∑ k, μ (some k) * b k = - μ none := by
      linarith
    by_cases hz : ∃ k, μ (some k) ≠ 0
    · have := h (fun k => μ (some k)) (fun k => hμ0 _) hz h1
      have := hμ0 none
      linarith
    · push Not at hz
      have : ∑ k, μ (some k) = 0 := Finset.sum_eq_zero fun k _ => hz k
      have hn : μ none = 1 := by linarith
      have : ∑ k, μ (some k) * b k = 0 := Finset.sum_eq_zero fun k _ => by rw [hz k]; ring
      linarith
  obtain ⟨f, u, hu0, hu⟩ := geometric_hahn_banach_point_closed ht1 ht2 h0
  rw [map_zero] at hu0
  have hg : ∀ i, u < f (g i) := fun i => by
    apply hu
    refine ⟨Pi.single i 1, ⟨fun j => ?_, ?_⟩, ?_⟩
    · by_cases hj : j = i <;> simp [Pi.single_apply, hj]
    · simp
    · rw [hL]; simp [Finset.sum_ite_eq]
  let ℓ : E →L[ℝ] ℝ := f.comp (ContinuousLinearMap.inl ℝ E ℝ)
  let c : ℝ := f (0, 1)
  have hf : ∀ (x : E) (s : ℝ), f (x, s) = ℓ x + s * c := by
    intro x s
    have : (x, s) = (x, 0) + s • ((0 : E), (1 : ℝ)) := by simp
    rw [this, map_add, map_smul]; simp [ℓ, c]
  have hc : c < 0 := by
    have := hg none
    simp only [g, hf] at this
    simp at this
    linarith
  refine ⟨(1 / c) • (InnerProductSpace.toDual ℝ E).symm ℓ, fun k => ?_⟩
  have := hg (some k)
  simp only [g, hf] at this
  rw [inner_smul_right, real_inner_comm, InnerProductSpace.toDual_symm_apply]
  have key : b k * c < ℓ (a k) := by linarith
  rw [one_div_mul_eq_div, div_lt_iff_of_neg hc]
  linarith

theorem t2_sum_subtype_dite {α M : Type*} [Fintype α] [AddCommMonoid M] (J : α → Prop) [DecidablePred J]
    (G : {p // J p} → M) :
    ∑ p : {p // J p}, G p = ∑ p : α, if h : J p then G ⟨p, h⟩ else 0 := by
  classical
  have h1 : ∑ p : {p // J p}, G p = ∑ p : {p // J p}, (fun q => if h : J q then G ⟨q, h⟩ else 0) p.1 :=
    Finset.sum_congr rfl fun p _ => by simp [p.2]
  rw [h1, ← Finset.sum_subtype (Finset.univ.filter J) (by simp) (fun q => if h : J q then G ⟨q, h⟩ else 0)]
  rw [Finset.sum_filter_of_ne]
  intro p _ hp
  by_contra hJ
  exact hp (dif_neg hJ)

/-- Second-order term, linear in the unknowns `x = (γ, β₂)`:
`⟪n, secondVel ω γ β v⟫ = ⟪n, P(ω×(ω×v))⟫ + ⟪a, x⟫` with
`a = (-2 n₁ v₂, 2 n₀ v₂, 2 (v₀ n₁ - v₁ n₀), n₀, n₁)`. -/
theorem inner_secondVel (n : ℝ²) (ω v : ℝ³) (x : EuclideanSpace ℝ (Fin 5)) :
    ⟪n, secondVel ω !₂[x 0, x 1, x 2] !₂[x 3, x 4, 0] v⟫ =
      ⟪n, proj_xy ((crossMatrix ω).toEuclideanLin ((crossMatrix ω).toEuclideanLin v))⟫ +
      ⟪(!₂[-2 * (n 1 * v 2), 2 * (n 0 * v 2), 2 * (v 0 * n 1 - v 1 * n 0), n 0, n 1] :
        EuclideanSpace ℝ (Fin 5)), x⟫ := by
  simp [secondVel, proj_xy, crossMatrix, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
    Fin.sum_univ_three, Fin.sum_univ_two, Fin.sum_univ_five, PiLp.inner_apply]
  ring

theorem isRupert_of_secondOrder_noBalanced (V : Finset ℝ³) {ι : Type*} [Fintype ι] (n : ι → ℝ²) (h : ι → ℝ)
    (hpoly : {y : ℝ² | ∀ e, ⟪n e, y⟫ < h e} ⊆ proj_xy '' convexHull ℝ (V : Set ℝ³))
    (ω τ : ℝ³)
    (hweak : ∀ v ∈ V, ∀ e, ⟪n e, proj_xy v⟫ < h e ∨
      (⟪n e, proj_xy v⟫ = h e ∧ ⟪n e, screenVel ω τ v⟫ ≤ 0))
    (hQ : ∀ lam : V → ι → ℝ, (∀ v e, 0 ≤ lam v e) →
      (∀ v e, lam v e ≠ 0 → ⟪n e, proj_xy (v : ℝ³)⟫ = h e ∧ ⟪n e, screenVel ω τ v⟫ = 0) →
      (∃ v e, lam v e ≠ 0) →
      ∑ v, ∑ e, lam v e • n e = 0 →
      ∑ v, ∑ e, lam v e * ((proj_xy (v : ℝ³)) 0 * n e 1 - (proj_xy (v : ℝ³)) 1 * n e 0) = 0 →
      ∑ v, ∑ e, (lam v e * (v : ℝ³) 2) • n e = 0 →
      ∑ v, ∑ e, lam v e *
        ⟪n e, proj_xy ((crossMatrix ω).toEuclideanLin ((crossMatrix ω).toEuclideanLin (v : ℝ³)))⟫ < 0) :
    IsRupert V := by
  classical
  let J : V × ι → Prop := fun p => ⟪n p.2, proj_xy (p.1 : ℝ³)⟫ = h p.2 ∧ ⟪n p.2, screenVel ω τ p.1⟫ = 0
  let A : V × ι → EuclideanSpace ℝ (Fin 5) := fun p =>
    !₂[-2 * (n p.2 1 * (p.1 : ℝ³) 2), 2 * (n p.2 0 * (p.1 : ℝ³) 2),
      2 * ((p.1 : ℝ³) 0 * n p.2 1 - (p.1 : ℝ³) 1 * n p.2 0), n p.2 0, n p.2 1]
  let B : V × ι → ℝ := fun p =>
    -⟪n p.2, proj_xy ((crossMatrix ω).toEuclideanLin ((crossMatrix ω).toEuclideanLin (p.1 : ℝ³)))⟫
  -- conversion of sums over the subtype to sums over `V × ι`
  have conv : ∀ (lam : {p // J p} → ℝ) (F : V × ι → ℝ),
      ∑ k : {p // J p}, lam k * F k.1 =
        ∑ v : V, ∑ e : ι, (if hJ : J (v, e) then lam ⟨(v, e), hJ⟩ else 0) * F (v, e) := by
    intro lam F
    rw [t2_sum_subtype_dite J (fun k => lam k * F k.1), ← Fintype.sum_prod_type']
    refine Finset.sum_congr rfl fun p _ => ?_
    by_cases hp : J p <;> simp [hp]
  have hmot := exists_strict_of_no_balanced (κ := {p // J p}) (fun k => A k.1) (fun k => B k.1) (by
    intro lam hl0 hne hsum
    set L : V → ι → ℝ := fun v e => if hJ : J (v, e) then lam ⟨(v, e), hJ⟩ else 0 with hL
    have hcomp : ∀ j : Fin 5, ∑ v : V, ∑ e : ι, L v e * (A (v, e)) j = 0 := by
      intro j
      rw [← conv lam (fun p => (A p) j)]
      have := congrArg (fun y => y j) hsum
      simpa [Finset.sum_apply] using this
    have hL0 : ∀ v e, 0 ≤ L v e := fun v e => by
      simp only [hL]; split_ifs
      · exact hl0 _
      · exact le_rfl
    have key := hQ L hL0 (fun v e hne => by
        simp only [hL] at hne
        by_cases hJ : J (v, e)
        · exact hJ
        · exact absurd (dif_neg hJ) hne)
      (by
        obtain ⟨k, hk⟩ := hne
        refine ⟨k.1.1, k.1.2, ?_⟩
        simp only [hL]
        rw [dif_pos k.2]
        exact hk)
      (by
        ext i
        fin_cases i
        · have := hcomp 3
          simpa [A, Finset.sum_apply] using this
        · have := hcomp 4
          simpa [A, Finset.sum_apply] using this)
      (by
        have := hcomp 2
        simp only [A] at this
        simp only [proj_xy]
        simp [Fin.isValue] at this ⊢
        refine (mul_eq_zero.mp (?_ : (2:ℝ) * _ = 0)).resolve_left two_ne_zero
        rw [← this]; simp only [Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring)
      (by
        ext i
        fin_cases i
        · have := hcomp 1
          simp [A, Finset.sum_apply] at this ⊢
          refine (mul_eq_zero.mp (?_ : (2:ℝ) * _ = 0)).resolve_left two_ne_zero
          rw [← this]; simp only [Finset.mul_sum]
          exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
        · have := hcomp 0
          simp [A, Finset.sum_apply] at this ⊢
          refine (mul_eq_zero.mp (?_ : (2:ℝ) * _ = 0)).resolve_left two_ne_zero
          rw [← this]; simp only [Finset.mul_sum]
          exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring)
    have hb : ∑ k : {p // J p}, lam k * B k.1 = -∑ v : V, ∑ e : ι, L v e *
        ⟪n e, proj_xy ((crossMatrix ω).toEuclideanLin ((crossMatrix ω).toEuclideanLin (v : ℝ³)))⟫ := by
      rw [conv lam B]
      simp [B, mul_neg, Finset.sum_neg_distrib, hL]
    rw [hb]; linarith)
  obtain ⟨x, hx⟩ := hmot
  refine isRupert_of_secondOrderLex V n h hpoly ω !₂[x 0, x 1, x 2] τ !₂[x 3, x 4, 0] ?_
  intro v hv e
  rcases hweak v hv e with h1 | ⟨h1, h2⟩
  · exact Or.inl h1
  · right
    refine ⟨h1, ?_⟩
    rcases h2.lt_or_eq with h3 | h3
    · exact Or.inl h3
    · refine Or.inr ⟨h3, ?_⟩
      have := hx ⟨(⟨v, hv⟩, e), h1, h3⟩
      simp only [A, B] at this
      rw [inner_secondVel]
      linarith
end Minimality
