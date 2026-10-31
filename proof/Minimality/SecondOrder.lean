module

public import Minimality.FirstOrder

@[expose] public section

/-!
# Second-order lexicographic passages

Theorem T2(a), analytic half (nopert229/out/bottleneck/virial/draft.md §2): along the Cayley curve
`R(s) = cayley ((s/2)•ω + (s²/2)•γ)` with screen offset `s•Pτ + (s²/2)•Pβ`, a vertex `v` passes a shadow edge
`⟪n, y⟫ ≤ h` if it is slack, or tight with `⟪n, screenVel ω τ v⟫ < 0`, or tight with first-order term `0` and
`⟪n, secondVel ω γ β v⟫ < 0`.  If every (vertex, edge) pair passes, `V` is Rupert (`isRupert_of_secondOrderLex`).
-/

namespace Minimality

open scoped RealInnerProductSpace Matrix Topology
open Filter

/-- Eventual sign of `F s = a0 + a1 s + a2 s² + s³ G s` as `s → 0⁺`, lexicographically. -/
theorem eventually_neg_of_lex (a0 a1 a2 : ℝ) (G : ℝ → ℝ) (hG : ContinuousAt G 0)
    (h : a0 < 0 ∨ (a0 = 0 ∧ (a1 < 0 ∨ (a1 = 0 ∧ a2 < 0)))) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), a0 + a1 * s + a2 * s ^ 2 + s ^ 3 * G s < 0 := by
  have hpos : ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 < s := self_mem_nhdsWithin
  rcases h with h | ⟨rfl, h | ⟨rfl, h⟩⟩
  · have hc : ContinuousAt (fun s => a0 + a1 * s + a2 * s ^ 2 + s ^ 3 * G s) 0 := by
      fun_prop (disch := exact hG)
    have ht := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
    simp only [mul_zero, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, zero_mul] at ht
    exact ht.eventually_lt_const h
  · have hc : ContinuousAt (fun s => a1 + a2 * s + s ^ 2 * G s) 0 := by
      fun_prop (disch := exact hG)
    have ht := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
    simp only [mul_zero, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, zero_mul] at ht
    filter_upwards [ht.eventually_lt_const h, hpos] with s hs hs0
    have : s * (a1 + a2 * s + s ^ 2 * G s) < 0 := mul_neg_of_pos_of_neg hs0 hs
    nlinarith
  · have hc : ContinuousAt (fun s => a2 + s * G s) 0 := by
      fun_prop (disch := exact hG)
    have ht := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
    simp only [mul_zero, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, zero_mul] at ht
    filter_upwards [ht.eventually_lt_const h, hpos] with s hs hs0
    have : s ^ 2 * (a2 + s * G s) < 0 := mul_neg_of_pos_of_neg (by positivity) hs
    nlinarith

/-- Second-order acceleration of `v` along the curve `cayley ((s/2)•ω + (s^2/2)•γ) v + s•τ + (s^2/2)•β`:
`x(s) = v + s (ω×v + τ) + (s²/2) (ω×(ω×v) + 2 γ×v + β) + O(s³)`. -/
noncomputable def secondVel (ω γ β x : ℝ³) : ℝ² :=
  proj_xy ((crossMatrix ω).toEuclideanLin ((crossMatrix ω).toEuclideanLin x)
    + (2 : ℝ) • (crossMatrix γ).toEuclideanLin x + β)

/-- The Cayley vector of the second-order curve. -/
noncomputable def secCayleyVec (ω γ : ℝ³) (s : ℝ) : ℝ³ := (s / 2) • ω + (s ^ 2 / 2) • γ

/-- The screen translation of the second-order curve. -/
noncomputable def secOffset (τ β : ℝ³) (s : ℝ) : ℝ² := s • proj_xy τ + (s ^ 2 / 2) • proj_xy β

theorem crossMatrix_add_apply (a b x : ℝ³) :
    (crossMatrix (a + b)).toEuclideanLin x =
      (crossMatrix a).toEuclideanLin x + (crossMatrix b).toEuclideanLin x := by
  ext i; fin_cases i <;> simp [crossMatrix, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
    Fin.sum_univ_three] <;> ring

theorem crossMatrix_smul_apply (t : ℝ) (a x : ℝ³) :
    (crossMatrix (t • a)).toEuclideanLin x = t • (crossMatrix a).toEuclideanLin x := by
  ext i; fin_cases i <;> simp [crossMatrix, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
    Fin.sum_univ_three] <;> ring

theorem cayley_apply (c x : ℝ³) :
    (cayley c).toEuclideanLin x = x + (2 * (cayleyDen c)⁻¹) •
      ((crossMatrix c).toEuclideanLin x + (crossMatrix c).toEuclideanLin ((crossMatrix c).toEuclideanLin x)) := by
  have hd := (cayleyDen_pos c).ne'
  ext i; fin_cases i <;> simp [cayley, crossMatrix, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
    Fin.sum_univ_three] <;> field_simp <;> simp only [cayleyDen] <;> ring

/-- `w(s) = |d|²/D`, `d = (ω + sγ)/2`. -/
noncomputable def secW (ω γ : ℝ³) (s : ℝ) : ℝ :=
  (((ω 0 + s * γ 0) / 2) ^ 2 + ((ω 1 + s * γ 1) / 2) ^ 2 + ((ω 2 + s * γ 2) / 2) ^ 2) /
    (1 + s ^ 2 * (((ω 0 + s * γ 0) / 2) ^ 2 + ((ω 1 + s * γ 1) / 2) ^ 2 + ((ω 2 + s * γ 2) / 2) ^ 2))

theorem secCayleyDen (ω γ : ℝ³) (s : ℝ) :
    cayleyDen (secCayleyVec ω γ s) =
      1 + s ^ 2 * (((ω 0 + s * γ 0) / 2) ^ 2 + ((ω 1 + s * γ 1) / 2) ^ 2 + ((ω 2 + s * γ 2) / 2) ^ 2) := by
  simp [cayleyDen, secCayleyVec]; ring

theorem secW_cont (ω γ : ℝ³) : Continuous (secW ω γ) := by
  unfold secW
  refine Continuous.div (by fun_prop) (by fun_prop) fun s => ?_
  positivity

theorem secW_spec (ω γ : ℝ³) (s : ℝ) :
    (cayleyDen (secCayleyVec ω γ s))⁻¹ = 1 - s ^ 2 * secW ω γ s := by
  rw [secCayleyDen]
  unfold secW
  have : 0 < 1 + s ^ 2 * (((ω 0 + s * γ 0) / 2) ^ 2 + ((ω 1 + s * γ 1) / 2) ^ 2 + ((ω 2 + s * γ 2) / 2) ^ 2) := by positivity
  field_simp
  ring

/-- The polynomial expansion of one constraint along the second-order curve. -/
theorem secondOrder_expansion (n : ℝ²) (ω γ τ β v : ℝ³) :
    ∃ G : ℝ → ℝ, Continuous G ∧ ∀ (s h : ℝ),
      ⟪n, secOffset τ β s + proj_xy ((cayley (secCayleyVec ω γ s)).toEuclideanLin v)⟫ - h =
        (⟪n, proj_xy v⟫ - h) + ⟪n, screenVel ω τ v⟫ * s +
          (1 / 2 * ⟪n, secondVel ω γ β v⟫) * s ^ 2 + s ^ 3 * G s := by
  set p1 := ⟪n, proj_xy ((crossMatrix ω).toEuclideanLin v)⟫ with hp1
  set p2 := ⟪n, proj_xy ((crossMatrix γ).toEuclideanLin v)⟫ with hp2
  set p3 := ⟪n, proj_xy ((crossMatrix ω).toEuclideanLin ((crossMatrix ω).toEuclideanLin v))⟫ with hp3
  set p4 := ⟪n, proj_xy ((crossMatrix ω).toEuclideanLin ((crossMatrix γ).toEuclideanLin v))⟫ +
    ⟪n, proj_xy ((crossMatrix γ).toEuclideanLin ((crossMatrix ω).toEuclideanLin v))⟫ with hp4
  set p5 := ⟪n, proj_xy ((crossMatrix γ).toEuclideanLin ((crossMatrix γ).toEuclideanLin v))⟫ with hp5
  refine ⟨fun s => p4 / 2 + s * (p5 / 2) - secW ω γ s *
    (p1 + s * ((p2 + p3 / 2) + s * (p4 / 2) + s ^ 2 * (p5 / 2))),
    ?_, fun s h => ?_⟩
  · have := secW_cont ω γ
    fun_prop
  · have hq := secW_spec ω γ s
    have key : ⟪n, secOffset τ β s + proj_xy ((cayley (secCayleyVec ω γ s)).toEuclideanLin v)⟫ =
        ⟪n, proj_xy v⟫ + s * ⟪n, proj_xy τ⟫ + s ^ 2 / 2 * ⟪n, proj_xy β⟫ +
        (2 * (1 - s ^ 2 * secW ω γ s)) *
          (s / 2 * p1 + s ^ 2 / 2 * p2 + (s / 2) ^ 2 * p3 + s / 2 * (s ^ 2 / 2) * p4 +
            (s ^ 2 / 2) ^ 2 * p5) := by
      rw [cayley_apply, hq]
      simp only [secOffset, secCayleyVec, crossMatrix_add_apply, crossMatrix_smul_apply,
        map_add, map_smul, proj_xy_add', proj_xy_smul', inner_add_right, inner_smul_right,
        hp1, hp2, hp3, hp4, hp5, smul_eq_mul]
      ring
    have e1 : ⟪n, screenVel ω τ v⟫ = p1 + ⟪n, proj_xy τ⟫ := by
      simp [screenVel, proj_xy_add', inner_add_right, hp1]
    have e2 : ⟪n, secondVel ω γ β v⟫ = p3 + 2 * p2 + ⟪n, proj_xy β⟫ := by
      simp [secondVel, proj_xy_add', proj_xy_smul', inner_add_right, inner_smul_right, hp2, hp3]
    rw [key, e1, e2]
    ring

/-- **Second-order lexicographic lemma.** -/
theorem isRupert_of_secondOrderLex (V : Finset ℝ³) {ι : Type*} [Fintype ι] (n : ι → ℝ²) (h : ι → ℝ)
    (hpoly : {y : ℝ² | ∀ e, ⟪n e, y⟫ < h e} ⊆ proj_xy '' convexHull ℝ (V : Set ℝ³))
    (ω γ τ β : ℝ³)
    (hlex : ∀ v ∈ V, ∀ e, ⟪n e, proj_xy v⟫ < h e ∨
      (⟪n e, proj_xy v⟫ = h e ∧ (⟪n e, screenVel ω τ v⟫ < 0 ∨
        (⟪n e, screenVel ω τ v⟫ = 0 ∧ ⟪n e, secondVel ω γ β v⟫ < 0)))) :
    IsRupert V := by
  set S := proj_xy '' convexHull ℝ (V : Set ℝ³) with hSdef
  have hS : Convex ℝ S := by
    rw [hSdef, show (proj_xy : ℝ³ → ℝ²) = projL from rfl]
    exact (convex_convexHull ℝ _).linear_image projL
  have hopen : IsOpen {y : ℝ² | ∀ e, ⟪n e, y⟫ < h e} := by
    have : {y : ℝ² | ∀ e, ⟪n e, y⟫ < h e} = ⋂ e, {y : ℝ² | ⟪n e, y⟫ < h e} := by
      ext y; simp
    rw [this]
    exact isOpen_iInter_of_finite fun e => isOpen_lt (by fun_prop) continuous_const
  have hU : {y : ℝ² | ∀ e, ⟪n e, y⟫ < h e} ⊆ interior S := interior_maximal hpoly hopen
  have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), ∀ v ∈ V, ∀ e,
      ⟪n e, secOffset τ β s + proj_xy ((cayley (secCayleyVec ω γ s)).toEuclideanLin v)⟫ < h e := by
    rw [eventually_all_finset]
    intro v hv
    rw [eventually_all]
    intro e
    obtain ⟨G, hGc, hG⟩ := secondOrder_expansion (n e) ω γ τ β v
    have := eventually_neg_of_lex (⟪n e, proj_xy v⟫ - h e) ⟪n e, screenVel ω τ v⟫
      (1 / 2 * ⟪n e, secondVel ω γ β v⟫) G hGc.continuousAt (by
        rcases hlex v hv e with h1 | ⟨h1, h2 | ⟨h2, h3⟩⟩
        · exact Or.inl (by linarith)
        · exact Or.inr ⟨by linarith, Or.inl h2⟩
        · exact Or.inr ⟨by linarith, Or.inr ⟨h2, by linarith⟩⟩)
    filter_upwards [this] with s hs
    have := hG s (h e)
    linarith
  obtain ⟨s, hs⟩ := hev.exists
  refine (isRupert_iff_shadows V).mpr ⟨cayley (secCayleyVec ω γ s), cayley_mem_SO3 _,
    secOffset τ β s, 1, one_mem _, ?_⟩
  rw [outerShadow_one, innerShadow_convexHull]
  refine convexHull_min ?_ hS.interior
  rintro _ ⟨v, hv, rfl⟩
  exact hU (fun e => hs v hv e)

end Minimality
