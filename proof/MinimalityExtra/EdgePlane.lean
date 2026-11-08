module

public import MinimalityExtra.DepthSeparated

/-!
# The Edge-Plane Lemma

Rotations whose axis lies in the plane through a rim edge normal to its support plane: freedom of
this form is the separation of two point sets in a plane. Theorem 8.10 is its steep case.
-/

@[expose] public section

namespace MinimalityExtra

open scoped RealInnerProductSpace
open Finset

/-! ## The Edge-Plane Lemma: axis in the plane of an edge (SPEC.md §8) -/

/-- **Edge-Plane Lemma, explicit motion.**  The rows are affine in `(α, μ)`: each row asks the
line `ρ = α + μ z` to pass on one side of a point of the `(z, ρ)` plane.  Geometrically the axis
lies in the plane through the edge `a` normal to its support plane. -/
theorem exists_motion_of_edgePlane {n k : ℕ} [NeZero k] (hk : 3 ≤ k) (x : Fin n → ℝ³) (w : ℝ³)
    (lab : ZMod k → Fin n) (hinj : Function.Injective lab) (hrim : StrictRimN x w lab)
    (a : ZMod k) (s α μ : ℝ) (hD : ⟪x (lab (a + 1)) - x (lab a), w⟫ ≠ 0)
    (hrows : ∀ i j : ZMod k, i ≠ a → (j = i ∨ j = i + 1) →
      0 < (α + μ * ⟪x (lab j) - x (lab a), w⟫) *
          det3 (x (lab (i + 1)) - x (lab i)) (x (lab (a + 1)) - x (lab a)) w +
        s * edgePlaneSpin (fun i => x (lab i)) w a i j) :
    ∃ ω τ : ℝ³, ∀ i : ZMod k,
      0 < det3 (x (lab (i + 1)) - x (lab i)) (cross ω (x (lab i)) + τ) w ∧
      0 < det3 (x (lab (i + 1)) - x (lab i)) (cross ω (x (lab (i + 1))) + τ) w := by
  set X : ZMod k → ℝ³ := fun i => x (lab i) with hX
  set d := X (a + 1) - X a with hd
  set D := ⟪d, w⟫ with hDdef
  set C := X a with hC
  set N := cross d w with hN
  set β := s / D with hβ
  set ω₂ := s • w + β • cross w N with hω₂
  set τ₂ := α • d - s • cross w C - (β * ⟪C, w⟫) • N with hτ₂
  set ω₀ := μ • cross w d + ω₂ with hω₀
  set τ₀ := μ • ((-⟪C, w⟫) • d) + τ₂ with hτ₀
  have hrow : ∀ E y : ℝ³, det3 E (cross ω₀ y + τ₀) w =
      (α + μ * ⟪y - C, w⟫) * det3 E d w + s * (det3 E (cross w (y - C)) w +
        (⟪y - C, w⟫ / D) * det3 E N w) := by
    intro E y
    rw [hω₀, hτ₀, det3_sum_motion, col_turn, hω₂, hτ₂, col_fix E d w y C (α • d) s β]
    have e : det3 E (α • d) w = α * det3 E d w := by
      simp only [det3, PiLp.smul_apply, smul_eq_mul]; ring
    rw [e, hβ]
    ring
  have hne : lab (a - 1) ≠ lab (a + 1) ∧ lab (a - 1) ≠ lab a := by
    refine ⟨fun h => zmod_pred_ne_succ hk a (hinj h), fun e => ?_⟩
    have h1 : a - (a - 1) = 0 := by rw [hinj e]; ring
    have : (1 : ZMod k) = 0 := by simpa using h1
    have hf : Fact (1 < k) := ⟨by omega⟩
    exact one_ne_zero this
  have hNN : 0 < ⟪N, N⟫ := by
    have hP : 0 < det3 d (X (a - 1) - C) w := hrim (lab (a - 1)) a hne.2 hne.1
    refine real_inner_self_pos.2 fun h0 => ?_
    have e : det3 d (X (a - 1) - C) w = -⟪N, X (a - 1) - C⟫ := by
      simp only [hN, det3, inner3, cross_0, cross_1, cross_2]; ring
    rw [e, h0] at hP
    simp at hP
  have hdN : det3 d (-N) w = ⟪N, N⟫ := by
    simp only [hN, det3, inner3, PiLp.neg_apply, cross_0, cross_1, cross_2]; ring
  have hdd : det3 d d w = 0 := by simp only [det3]; ring
  have hdwd : det3 d (cross w d) w + det3 d N w = 0 := by
    simp only [hN, det3, cross_0, cross_1, cross_2]; ring
  have hXa : det3 d (cross ω₀ C + τ₀) w = 0 := by
    have e0 : det3 d (cross w (0 : ℝ³)) w = 0 := by
      simp only [det3, cross_0, cross_1, cross_2, PiLp.zero_apply]; ring
    rw [hrow, hdd, sub_self, e0]
    simp
  have hXa1 : det3 d (cross ω₀ (X (a + 1)) + τ₀) w = 0 := by
    rw [hrow, show X (a + 1) - C = d from rfl, hdd, ← hDdef, div_self hD]
    linear_combination s * hdwd
  have hsum : ∀ (L : ℝ) (E y : ℝ³),
      det3 E (cross (L • ω₀ + 0) y + (L • τ₀ + -N)) w =
        L * det3 E (cross ω₀ y + τ₀) w + det3 E (-N) w := by
    intro L E y
    rw [det3_sum_motion]
    simp only [det3, cross_0, cross_1, cross_2, PiLp.add_apply, PiLp.zero_apply]
    ring
  let J : ZMod k × Bool → ZMod k := fun t => if t.2 then t.1 + 1 else t.1
  let Ed : ZMod k × Bool → ℝ³ := fun t => X (t.1 + 1) - X t.1
  obtain ⟨L, hL⟩ := exists_large (ι := ZMod k × Bool)
    (fun t => det3 (Ed t) (cross ω₀ (X (J t)) + τ₀) w) (fun t => det3 (Ed t) (-N) w) (by
      rintro ⟨i, b⟩
      by_cases hi : i = a
      · subst hi
        right
        refine ⟨?_, by simp only [Ed, ← hd]; rw [hdN]; exact hNN⟩
        cases b
        · simp only [J, Ed, ← hd, Bool.false_eq_true, ite_false]; exact hXa
        · simp only [J, Ed, ← hd, ite_true]; exact hXa1
      · left
        have hj : J (i, b) = i ∨ J (i, b) = i + 1 := by
          cases b
          · exact Or.inl rfl
          · exact Or.inr rfl
        have := hrows i (J (i, b)) hi hj
        simp only [Ed]
        rw [hrow]
        exact this)
  refine ⟨L • ω₀ + 0, L • τ₀ + -N, fun i => ⟨?_, ?_⟩⟩
  · have := hL (i, false)
    rw [hsum]; exact this
  · have := hL (i, true)
    rw [hsum]; exact this

/-- **Edge-Plane Lemma.** -/
theorem freeAt_of_edgePlane {n k : ℕ} [NeZero k] (hk : 3 ≤ k) (x : Fin n → ℝ³) (w : ℝ³)
    (lab : ZMod k → Fin n) (hinj : Function.Injective lab) (hrim : StrictRimN x w lab)
    (hhid : HiddenInTriangles x w lab) (a : ZMod k) (s α μ : ℝ)
    (hD : ⟪x (lab (a + 1)) - x (lab a), w⟫ ≠ 0)
    (hrows : ∀ i j : ZMod k, i ≠ a → (j = i ∨ j = i + 1) →
      0 < (α + μ * ⟪x (lab j) - x (lab a), w⟫) *
          det3 (x (lab (i + 1)) - x (lab i)) (x (lab (a + 1)) - x (lab a)) w +
        s * edgePlaneSpin (fun i => x (lab i)) w a i j) :
    FreeAt (univ.image x) w :=
  freeAt_of_rimMotion hk x w lab hinj hrim hhid
    (exists_motion_of_edgePlane hk x w lab hinj hrim a s α μ hD hrows)

/-- **Vertex form (the Dip Test).**  A candidate `(α, μ, s)` with two rows exactly tight, the two
tight rows independent, and every other row strictly positive.  Rows are homogeneous in
`(α, μ, s)`, so the tight rows are opened by adding a small direction. -/
theorem freeAt_of_edgePlane_vertex {n k : ℕ} [NeZero k] (hk : 3 ≤ k) (x : Fin n → ℝ³) (w : ℝ³)
    (lab : ZMod k → Fin n) (hinj : Function.Injective lab) (hrim : StrictRimN x w lab)
    (hhid : HiddenInTriangles x w lab) (a : ZMod k) (s α μ : ℝ)
    (hD : ⟪x (lab (a + 1)) - x (lab a), w⟫ ≠ 0) (i₁ j₁ i₂ j₂ : ZMod k)
    (hdet : det3 (x (lab (i₁ + 1)) - x (lab i₁)) (x (lab (a + 1)) - x (lab a)) w ≠ 0 ∧
      det3 (x (lab (i₂ + 1)) - x (lab i₂)) (x (lab (a + 1)) - x (lab a)) w ≠ 0 ∧
      ⟪x (lab j₁) - x (lab a), w⟫ ≠ ⟪x (lab j₂) - x (lab a), w⟫)
    (ht₁ : (α + μ * ⟪x (lab j₁) - x (lab a), w⟫) *
        det3 (x (lab (i₁ + 1)) - x (lab i₁)) (x (lab (a + 1)) - x (lab a)) w +
      s * edgePlaneSpin (fun i => x (lab i)) w a i₁ j₁ = 0)
    (ht₂ : (α + μ * ⟪x (lab j₂) - x (lab a), w⟫) *
        det3 (x (lab (i₂ + 1)) - x (lab i₂)) (x (lab (a + 1)) - x (lab a)) w +
      s * edgePlaneSpin (fun i => x (lab i)) w a i₂ j₂ = 0)
    (hrows : ∀ i j : ZMod k, i ≠ a → (j = i ∨ j = i + 1) → (i, j) ≠ (i₁, j₁) → (i, j) ≠ (i₂, j₂) →
      0 < (α + μ * ⟪x (lab j) - x (lab a), w⟫) *
          det3 (x (lab (i + 1)) - x (lab i)) (x (lab (a + 1)) - x (lab a)) w +
        s * edgePlaneSpin (fun i => x (lab i)) w a i j) :
    FreeAt (univ.image x) w := by
  classical
  set A : ZMod k → ℝ := fun i =>
    det3 (x (lab (i + 1)) - x (lab i)) (x (lab (a + 1)) - x (lab a)) w with hA
  set Z : ZMod k → ℝ := fun j => ⟪x (lab j) - x (lab a), w⟫ with hZ
  set S : ZMod k → ZMod k → ℝ := fun i j => edgePlaneSpin (fun i => x (lab i)) w a i j with hS
  obtain ⟨hA₁, hA₂, hZ₁₂⟩ := hdet
  have hA₁' : A i₁ ≠ 0 := hA₁
  have hA₂' : A i₂ ≠ 0 := hA₂
  have hz : Z j₂ - Z j₁ ≠ 0 := sub_ne_zero.2 fun h => hZ₁₂ h.symm
  set dm := (1 / A i₂ - 1 / A i₁) / (Z j₂ - Z j₁) with hdm
  set da := 1 / A i₁ - Z j₁ * dm with hda
  have hq₁ : (da + dm * Z j₁) * A i₁ = 1 := by
    rw [hda]; field_simp; ring
  have hq₂ : (da + dm * Z j₂) * A i₂ = 1 := by
    have : da + dm * Z j₂ = 1 / A i₂ := by
      rw [hda, hdm]; field_simp; ring
    rw [this]; field_simp
  let J : ZMod k × Bool → ZMod k := fun t => if t.2 then t.1 + 1 else t.1
  obtain ⟨L, hL⟩ := exists_large (ι := ZMod k × Bool)
    (fun t => if t.1 = a then 1 else (α + μ * Z (J t)) * A t.1 + s * S t.1 (J t))
    (fun t => if t.1 = a then 0 else (da + dm * Z (J t)) * A t.1) (by
      rintro ⟨i, b⟩
      by_cases hi : i = a
      · left; simp [hi]
      · have hj : J (i, b) = i ∨ J (i, b) = i + 1 := by
          cases b
          · exact Or.inl rfl
          · exact Or.inr rfl
        simp only [hi, if_false]
        by_cases h1 : (i, J (i, b)) = (i₁, j₁)
        · obtain ⟨e1, e2⟩ := Prod.mk.inj h1
          right
          rw [e2, e1]
          exact ⟨ht₁, by rw [hq₁]; norm_num⟩
        · by_cases h2 : (i, J (i, b)) = (i₂, j₂)
          · obtain ⟨e1, e2⟩ := Prod.mk.inj h2
            right
            rw [e2, e1]
            exact ⟨ht₂, by rw [hq₂]; norm_num⟩
          · left
            exact hrows i (J (i, b)) hi hj h1 h2)
  refine freeAt_of_edgePlane hk x w lab hinj hrim hhid a (L * s) (L * α + da) (L * μ + dm) hD ?_
  intro i j hi hj
  have hb : ∃ b, J (i, b) = j := by
    rcases hj with rfl | rfl
    · exact ⟨false, rfl⟩
    · exact ⟨true, rfl⟩
  obtain ⟨b, rfl⟩ := hb
  have := hL (i, b)
  simp only [hi, if_false] at this
  have e : ((L * α + da) + (L * μ + dm) * Z (J (i, b))) * A i + (L * s) * S i (J (i, b)) =
      L * ((α + μ * Z (J (i, b))) * A i + s * S i (J (i, b))) +
        (da + dm * Z (J (i, b))) * A i := by ring
  exact e ▸ this


theorem edgePlaneFreedom : EdgePlaneFreedom :=
  fun _ _ _ hk x w lab hinj hrim hhid a s α μ hD hrows =>
    freeAt_of_edgePlane hk x w lab hinj hrim hhid a s α μ hD hrows

#print axioms edgePlaneFreedom
#print axioms freeAt_of_edgePlane_vertex

end MinimalityExtra
