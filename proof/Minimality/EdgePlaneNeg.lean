module

public import Minimality.Type24DeepC
public import Minimality.EdgePlaneRev

/-!
# Edge-Plane symmetry under `w ↦ -w`

Reversing the rim cycle `lab' i := lab (-i)` and negating the view `w ↦ -w` preserves
`EdgePlaneAt` (`edgePlaneAt_neg` and `edgePlaneAt_neg_iff`):

* `StrictRimN` and `HiddenInTriangles` are preserved by `Split.Rev.strictRimN_rev` and
  `Split.Rev.hiddenInTriangles_rev`.
* Certifying edge `a` maps to `a' := -a - 1` (so `lab' a' = lab (a + 1)` and
  `lab' (a' + 1) = lab a`), keeping `⟪X' (a' + 1) - X' a', -w⟫ = ⟪X (a + 1) - X a, w⟫ ≠ 0`.
* Row `(i, j)` maps to `(i', j') := (-i - 1, -j)`, flipping the signs of both
  `det3 (X' (i' + 1) - X' i') (X' (a' + 1) - X' a') (-w)` and `edgePlaneSpin X' (-w) a' i' j'`,
  while `⟪X' j' - X' a', -w⟫ = D - ⟪X j - X a, w⟫` (with `D = ⟪X (a + 1) - X a, w⟫`).
* Taking `(s', α', μ') := (-s, -(α + μ * D), μ)` leaves every row's value identical.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace
open Minimality

namespace Minimality.T24.DeepC

/-- Reversing `i ↦ X (-i)` and negating `w ↦ -w` negates `Split.edgePlaneSpin` at
`(a', i', j') = (-a - 1, -i - 1, -j)`. -/
theorem edgePlaneSpin_rev {k : ℕ} (X : ZMod k → ℝ³) (w : ℝ³) (a i j : ZMod k)
    (hD : ⟪X (a + 1) - X a, w⟫ ≠ 0) :
    Split.edgePlaneSpin (fun t => X (-t)) (-w) (-a - 1) (-i - 1) (-j) =
      -Split.edgePlaneSpin X w a i j := by
  unfold Split.edgePlaneSpin
  have hi1 : -i - 1 + 1 = -i := by ring
  have ha1 : -a - 1 + 1 = -a := by ring
  rw [hi1, ha1]
  dsimp only
  have hi2 : -(-i - 1) = i + 1 := by ring
  have ha2 : -(-a - 1) = a + 1 := by ring
  rw [hi2, ha2]
  simp only [neg_neg]
  have e1 : Split.det3 (X i - X (i + 1)) (cross (-w) (X j - X (a + 1))) (-w) =
      -(Split.det3 (X (i + 1) - X i) (cross w (X j - X a)) w +
        Split.det3 (X (i + 1) - X i) (cross (X (a + 1) - X a) w) w) := by
    simp only [Split.det3, Split.cross_0, Split.cross_1, Split.cross_2,
      PiLp.sub_apply, PiLp.neg_apply]
    ring
  have e2 : Split.det3 (X i - X (i + 1)) (cross (X a - X (a + 1)) (-w)) (-w) =
      Split.det3 (X (i + 1) - X i) (cross (X (a + 1) - X a) w) w := by
    simp only [Split.det3, Split.cross_0, Split.cross_1, Split.cross_2,
      PiLp.sub_apply, PiLp.neg_apply]
    ring
  have e3 : ⟪X j - X (a + 1), -w⟫ = -(⟪X j - X a, w⟫ - ⟪X (a + 1) - X a, w⟫) := by
    simp only [Split.inner3, PiLp.sub_apply, PiLp.neg_apply]
    ring
  have e4 : ⟪X a - X (a + 1), -w⟫ = ⟪X (a + 1) - X a, w⟫ := by
    simp only [Split.inner3, PiLp.sub_apply, PiLp.neg_apply]
    ring
  rw [e1, e2, e3, e4]
  field_simp [hD]
  ring

/-- `EdgePlaneAt` is preserved under `w ↦ -w` (by reversing the rim cycle). -/
theorem edgePlaneAt_neg {n : ℕ} (x : Fin n → ℝ³) (w : ℝ³) :
    EdgePlaneAt x w → EdgePlaneAt x (-w) := by
  rintro ⟨k, hne, lab, a, s, α, μ, hk, hinj, hrim, hhid, hD, hrows⟩
  let lab' : ZMod k → Fin n := fun t => lab (-t)
  let a' : ZMod k := -a - 1
  let D : ℝ := ⟪x (lab (a + 1)) - x (lab a), w⟫
  refine ⟨k, hne, lab', a', -s, -(α + μ * D), μ, hk,
    fun i j h => neg_injective (hinj h),
    Split.Rev.strictRimN_rev x w lab hrim,
    Split.Rev.hiddenInTriangles_rev x w lab hhid, ?_, ?_⟩
  · have ha1 : -(a' + 1) = a := by simp [a']
    have ha0 : -a' = a + 1 := by simp [a']; ring
    have heq : ⟪x (lab' (a' + 1)) - x (lab' a'), -w⟫ = D := by
      simp only [lab', ha1, ha0, D]
      simp only [Split.inner3, PiLp.sub_apply, PiLp.neg_apply]
      ring
    rw [heq]
    exact hD
  · intro i' j' hi' hj'
    let i : ZMod k := -i' - 1
    let j : ZMod k := -j'
    have hi : i ≠ a := by
      intro h
      apply hi'
      calc
        i' = -i - 1 := by dsimp only [i]; ring
        _ = -a - 1 := by rw [h]
        _ = a' := rfl
    have hj : j = i ∨ j = i + 1 := by
      rcases hj' with rfl | rfl
      · right; dsimp only [i, j]; ring
      · left; dsimp only [i, j]; ring
    have hi'eq : i' = -i - 1 := by simp [i]
    have hj'eq : j' = -j := by simp [j]
    have ha'eq : a' = -a - 1 := rfl
    have hrow := hrows i j hi hj
    have hspin : Split.edgePlaneSpin (fun t => x (lab' t)) (-w) a' i' j' =
        -Split.edgePlaneSpin (fun t => x (lab t)) w a i j := by
      rw [ha'eq, hi'eq, hj'eq]
      exact edgePlaneSpin_rev (fun t => x (lab t)) w a i j hD
    have hdet : Split.det3 (x (lab' (i' + 1)) - x (lab' i')) (x (lab' (a' + 1)) - x (lab' a')) (-w) =
        -Split.det3 (x (lab (i + 1)) - x (lab i)) (x (lab (a + 1)) - x (lab a)) w := by
      have e1 : -(i' + 1) = i := by dsimp only [i]; ring
      have e2 : -i' = i + 1 := by dsimp only [i]; ring
      have e3 : -(a' + 1) = a := by simp [a']
      have e4 : -a' = a + 1 := by simp [a']; ring
      simp only [lab', e1, e2, e3, e4]
      simp only [Split.det3, PiLp.sub_apply, PiLp.neg_apply]
      ring
    have hz : ⟪x (lab' j') - x (lab' a'), -w⟫ = D - ⟪x (lab j) - x (lab a), w⟫ := by
      have e4 : -a' = a + 1 := by simp [a']; ring
      simp only [lab', hj'eq, neg_neg, e4, D]
      simp only [Split.inner3, PiLp.sub_apply, PiLp.neg_apply]
      ring
    rw [hspin, hdet, hz]
    linarith

/-- `EdgePlaneAt x (-w)` holds iff `EdgePlaneAt x w` holds. -/
theorem edgePlaneAt_neg_iff {n : ℕ} (x : Fin n → ℝ³) (w : ℝ³) :
    EdgePlaneAt x (-w) ↔ EdgePlaneAt x w :=
  ⟨fun h => by simpa only [neg_neg] using edgePlaneAt_neg x (-w) h, edgePlaneAt_neg x w⟩

end Minimality.T24.DeepC
