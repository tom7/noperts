module

public import Minimality.EdgePlaneLWrap

/-!
# Cycle reversal for strict rims and L-Wrap at edge `a - 1`

Reversing the rim cycle `lab' i := lab (-i)` and negating the view `w ↦ -w` preserves
`StrictRimN` and `HiddenInTriangles` (`strictRimN_rev`, `hiddenInTriangles_rev`), because
both `w ↦ -w` and reversing edge direction flip the sign of `det3`.

Applying `Minimality.Split.LWrap.edgePlaneAny_of_lwrap_adj_twoRed` to `(lab', -w₀, -a - 1, -ε, σ)`
yields the mirror L-Wrap theorem `edgePlaneAny_of_lwrap_adj_twoBlue` (Carbon A78 Theorem 2.1,
"two Blue edges"), certifying `Gen.EdgePlaneAny x` at the **adjacent edge `a - 1`** (`a - 1 → a`)
with zero tilt:
- `H1a`: `⟪x (lab (a + 1)) - x (lab a), w₀⟫ = 0` (the level edge `a → a + 1`)
- `H1b`: `0 < ε * ⟪x (lab j) - x (lab a), w₀⟫` for `j ∉ {a, a + 1}` (`ε = 1` shallowest, `ε = -1` deepest)
- `H2a`: `0 < det3 (x (lab a) - x (lab (a - 1))) (x (lab (a + 1 + 1)) - x (lab (a + 1))) w₀` (L-Wrap)
- `H2b`: `0 < det3 (x (lab (i + 1)) - x (lab i)) (x (lab a) - x (lab (a - 1))) w₀` for `i ∉ {a - 1, a, a + 1}`
- `H3`: 1D slope separation at `b = a - 1` comparing `(i, j) = (a + 1, a + 1 + 1)` against all `i ∉ {a - 1, a, a + 1}`, `j ∈ {i, i + 1}`, with threshold `max 0 (max (σ * lwY ... (a-1) a (a+1)) (σ * lwY ... (a-1) (a+1) (a+1)))`.
-/

@[expose] public section

set_option autoImplicit false

open scoped RealInnerProductSpace
open Finset

namespace Minimality.Split.Rev

/-- Reversing the rim cycle `i ↦ lab (-i)` and negating the view `w ↦ -w` preserves `StrictRimN`. -/
theorem strictRimN_rev {n k : ℕ} [NeZero k] (x : Fin n → ℝ³) (w : ℝ³) (lab : ZMod k → Fin n)
    (hrim : StrictRimN x w lab) : StrictRimN x (-w) (fun i => lab (-i)) := by
  intro m i hm1 hm2
  have h1 : m ≠ lab (-i - 1) := by simpa [sub_eq_add_neg, add_comm, neg_add] using hm2
  have h2 : m ≠ lab (-i - 1 + 1) := by simpa [sub_add_cancel] using hm1
  have hr := hrim m (-i - 1) h1 h2
  have heq : det3 (x (lab (-(i + 1))) - x (lab (-i))) (x m - x (lab (-i))) (-w) =
      det3 (x (lab (-i - 1 + 1)) - x (lab (-i - 1))) (x m - x (lab (-i - 1))) w := by
    have hidx1 : -(i + 1) = -i - 1 := by ring
    have hidx2 : -i - 1 + 1 = -i := by ring
    rw [hidx1, hidx2]
    simp only [det3, PiLp.sub_apply, PiLp.neg_apply]
    ring
  rw [heq]
  exact hr

/-- Reversing the rim cycle `i ↦ lab (-i)` and negating the view `w ↦ -w` preserves `HiddenInTriangles`. -/
theorem hiddenInTriangles_rev {n k : ℕ} [NeZero k] (x : Fin n → ℝ³) (w : ℝ³) (lab : ZMod k → Fin n)
    (hhid : HiddenInTriangles x w lab) : HiddenInTriangles x (-w) (fun i => lab (-i)) := by
  intro m hm
  have hm' : ∀ i, m ≠ lab i := fun i => by simpa using hm (-i)
  obtain ⟨p, hp, q, hq, r, hr, h1, h2, h3, h4⟩ := hhid m hm'
  refine ⟨p, hp, r, hr, q, hq, ?_, ?_, ?_, ?_⟩
  · have e : det3 (r - p) (q - p) (-w) = det3 (q - p) (r - p) w := by
      simp only [det3, PiLp.sub_apply, PiLp.neg_apply]; ring
    linarith
  · have e : det3 (r - p) (x m - p) (-w) = det3 (p - r) (x m - r) w := by
      simp only [det3, PiLp.sub_apply, PiLp.neg_apply]; ring
    linarith
  · have e : det3 (q - r) (x m - r) (-w) = det3 (r - q) (x m - q) w := by
      simp only [det3, PiLp.sub_apply, PiLp.neg_apply]; ring
    linarith
  · have e : det3 (p - q) (x m - q) (-w) = det3 (q - p) (x m - p) w := by
      simp only [det3, PiLp.sub_apply, PiLp.neg_apply]; ring
    linarith

/-- Reversing `i ↦ X (-i)` and `w ↦ -w` preserves `LWrap.lwY` at `b = a - 1` (mapped to `-a`),
when the edge `a - 1 → a` is non-level (`⟪X a - X (a - 1), w⟫ ≠ 0`). -/
theorem lwY_rev {k : ℕ} (X : ZMod k → ℝ³) (w : ℝ³) (a i j : ZMod k)
    (hD : ⟪X a - X (a - 1), w⟫ ≠ 0) :
    LWrap.lwY (fun t => X (-t)) (-w) (-a) (-i - 1) (-j) = LWrap.lwY X w (a - 1) i j := by
  unfold LWrap.lwY edgePlaneSpin
  have h1 : -i - 1 + 1 = -i := by ring
  have h2 : -a + 1 = -(a - 1) := by ring
  have h3 : a - 1 + 1 = a := by ring
  rw [h1, h2, h3]
  dsimp only
  have hi : -(-i - 1) = i + 1 := by ring
  have ha : -(-a) = a := by ring
  have ha1 : -(-(a - 1)) = a - 1 := by ring
  have hj : -(-j) = j := by ring
  simp only [hi, ha, ha1, hj, neg_neg]
  have hnum :
      det3 (X i - X (i + 1)) (cross (-w) (X j - X a)) (-w) +
        ⟪X j - X a, -w⟫ / ⟪X (a - 1) - X a, -w⟫ *
          det3 (X i - X (i + 1)) (cross (X (a - 1) - X a) (-w)) (-w) =
      -(det3 (X (i + 1) - X i) (cross w (X j - X (a - 1))) w +
        ⟪X j - X (a - 1), w⟫ / ⟪X a - X (a - 1), w⟫ *
          det3 (X (i + 1) - X i) (cross (X a - X (a - 1)) w) w) := by
    have e1 : det3 (X i - X (i + 1)) (cross (-w) (X j - X a)) (-w) =
        -(det3 (X (i + 1) - X i) (cross w (X j - X (a - 1))) w +
          det3 (X (i + 1) - X i) (cross (X a - X (a - 1)) w) w) := by
      simp only [det3, cross_0, cross_1, cross_2, PiLp.sub_apply, PiLp.neg_apply]; ring
    have e2 : det3 (X i - X (i + 1)) (cross (X (a - 1) - X a) (-w)) (-w) =
        det3 (X (i + 1) - X i) (cross (X a - X (a - 1)) w) w := by
      simp only [det3, cross_0, cross_1, cross_2, PiLp.sub_apply, PiLp.neg_apply]; ring
    have e3 : ⟪X j - X a, -w⟫ = -(⟪X j - X (a - 1), w⟫ - ⟪X a - X (a - 1), w⟫) := by
      simp only [inner3, PiLp.sub_apply, PiLp.neg_apply]; ring
    have e4 : ⟪X (a - 1) - X a, -w⟫ = ⟪X a - X (a - 1), w⟫ := by
      simp only [inner3, PiLp.sub_apply, PiLp.neg_apply]; ring
    rw [e1, e2, e3, e4]
    field_simp [hD]; ring
  have hden :
      det3 (X i - X (i + 1)) (X (a - 1) - X a) (-w) =
      -det3 (X (i + 1) - X i) (X a - X (a - 1)) w := by
    simp only [det3, PiLp.sub_apply, PiLp.neg_apply]; ring
  rw [hnum, hden]
  ring

/-- **LWRAP (Carbon A78 Theorem 2.1, two Blue edges, certifying at edge `a - 1`).**
Mirror of `LWrap.edgePlaneAny_of_lwrap_adj_twoRed` obtained by reversing the cycle `lab' i := lab (-i)`
and negating the view `w₀ ↦ -w₀`, mapping edge `a - 1` of `lab` to edge `(-a - 1) + 1` of `lab'`. -/
theorem edgePlaneAny_of_lwrap_adj_twoBlue {n k : ℕ} [NeZero k] (hk : 4 ≤ k) (x : Fin n → ℝ³)
    (lab : ZMod k → Fin n) (hinj : Function.Injective lab) (w₀ : ℝ³)
    (hrim : StrictRimN x w₀ lab) (hhid : HiddenInTriangles x w₀ lab) (a : ZMod k)
    (ε : ℝ)
    (H1a : ⟪x (lab (a + 1)) - x (lab a), w₀⟫ = 0)
    (H1b : ∀ j, j ≠ a → j ≠ a + 1 → 0 < ε * ⟪x (lab j) - x (lab a), w₀⟫)
    (H2a : 0 < det3 (x (lab a) - x (lab (a - 1))) (x (lab (a + 1 + 1)) - x (lab (a + 1))) w₀)
    (H2b : ∀ i, i ≠ a - 1 → i ≠ a → i ≠ a + 1 →
      0 < det3 (x (lab (i + 1)) - x (lab i)) (x (lab a) - x (lab (a - 1))) w₀)
    (σ : ℝ)
    (H3 : ∀ i j : ZMod k, i ≠ a - 1 → i ≠ a → i ≠ a + 1 → (j = i ∨ j = i + 1) →
      (σ * LWrap.lwY (fun i => x (lab i)) w₀ (a - 1) (a + 1) (a + 1 + 1) -
          max 0 (max (σ * LWrap.lwY (fun i => x (lab i)) w₀ (a - 1) a (a + 1))
            (σ * LWrap.lwY (fun i => x (lab i)) w₀ (a - 1) (a + 1) (a + 1)))) /
        (ε * ⟪x (lab (a + 1 + 1)) - x (lab a), w₀⟫) <
      (σ * LWrap.lwY (fun i => x (lab i)) w₀ (a - 1) i j -
          max 0 (max (σ * LWrap.lwY (fun i => x (lab i)) w₀ (a - 1) a (a + 1))
            (σ * LWrap.lwY (fun i => x (lab i)) w₀ (a - 1) (a + 1) (a + 1)))) /
        (ε * ⟪x (lab j) - x (lab a), w₀⟫)) :
    Gen.EdgePlaneAny x := by
  have hk3 : 3 ≤ k := by omega
  obtain ⟨_, _, ha_m1_ne_a, _, ha_m1_ne_ap1⟩ := Level.zk_ne hk3 a
  have hD_edge : ⟪x (lab a) - x (lab (a - 1)), w₀⟫ ≠ 0 := by
    have hlt := H1b (a - 1) ha_m1_ne_a ha_m1_ne_ap1
    intro h0
    have h0' : ⟪x (lab (a - 1)) - x (lab a), w₀⟫ = 0 := by
      have e : x (lab (a - 1)) - x (lab a) = -(x (lab a) - x (lab (a - 1))) := by abel
      rw [e, inner_neg_left, h0, neg_zero]
    rw [h0', mul_zero] at hlt
    exact lt_irrefl _ hlt
  let lab' : ZMod k → Fin n := fun i => lab (-i)
  let a' : ZMod k := -a - 1
  have hinj' : Function.Injective lab' := fun i j h => neg_injective (hinj h)
  have hrim' : StrictRimN x (-w₀) lab' := strictRimN_rev x w₀ lab hrim
  have hhid' : HiddenInTriangles x (-w₀) lab' := hiddenInTriangles_rev x w₀ lab hhid
  have ha1 : a' + 1 = -a := by simp [a']
  have ha2 : a' + 1 + 1 = -(a - 1) := by simp [a']; ring
  have ha0 : a' - 1 = -(a + 1) - 1 := by simp [a']; ring
  have H1a' : ⟪x (lab' (a' + 1)) - x (lab' a'), -w₀⟫ = 0 := by
    have hidx : -a' = a + 1 := by simp [a']; ring
    simp only [lab', ha1, neg_neg, hidx]
    have e : x (lab a) - x (lab (a + 1)) = -(x (lab (a + 1)) - x (lab a)) := by abel
    rw [e, inner_neg_left, inner_neg_right, neg_neg, H1a]
  have H1b' : ∀ j', j' ≠ a' → j' ≠ a' + 1 →
      0 < (-ε) * ⟪x (lab' j') - x (lab' (a' + 1)), -w₀⟫ := by
    intro j' hj1 hj2
    have hj1' : -j' ≠ a + 1 := fun h => hj1 (by dsimp [a']; linear_combination -h)
    have hj2' : -j' ≠ a := fun h => hj2 (by rw [ha1, ← h, neg_neg])
    have e : (-ε) * ⟪x (lab' j') - x (lab' (a' + 1)), -w₀⟫ =
        ε * ⟪x (lab (-j')) - x (lab a), w₀⟫ := by
      simp only [lab', ha1, neg_neg, inner_neg_right]; ring
    rw [e]
    exact H1b (-j') hj2' hj1'
  have H2a' : 0 < det3 (x (lab' a') - x (lab' (a' - 1)))
      (x (lab' (a' + 1 + 1)) - x (lab' (a' + 1))) (-w₀) := by
    have hidx0 : -(a' - 1) = a + 1 + 1 := by simp [a']; ring
    have hidx1 : -a' = a + 1 := by simp [a']; ring
    have hidx2 : -(-a + 1) = a - 1 := by ring
    simp only [lab', ha1, hidx0, hidx1, hidx2, neg_neg]
    have e : det3 (x (lab (a + 1)) - x (lab (a + 1 + 1))) (x (lab (a - 1)) - x (lab a)) (-w₀) =
        det3 (x (lab a) - x (lab (a - 1))) (x (lab (a + 1 + 1)) - x (lab (a + 1))) w₀ := by
      simp only [det3, PiLp.sub_apply, PiLp.neg_apply]; ring
    rw [e]
    exact H2a
  have H2b' : ∀ i', i' ≠ a' - 1 → i' ≠ a' → i' ≠ a' + 1 →
      det3 (x (lab' (i' + 1)) - x (lab' i'))
        (x (lab' (a' + 1 + 1)) - x (lab' (a' + 1))) (-w₀) < 0 := by
    intro i' hi1 hi2 hi3
    let i : ZMod k := -i' - 1
    have hi1' : i ≠ a + 1 := fun h => hi1 (by dsimp [i, a'] at h ⊢; linear_combination -h)
    have hi2' : i ≠ a := fun h => hi2 (by dsimp [i, a'] at h ⊢; linear_combination -h)
    have hi3' : i ≠ a - 1 := fun h => hi3 (by rw [ha1]; dsimp [i] at h ⊢; linear_combination -h)
    have hidx1 : -(i' + 1) = i := by simp [i]; ring
    have hidx2 : -i' = i + 1 := by simp [i]
    have hidx3 : -(-a + 1) = a - 1 := by ring
    simp only [lab', ha1, hidx1, hidx2, hidx3, neg_neg]
    have e : det3 (x (lab i) - x (lab (i + 1))) (x (lab (a - 1)) - x (lab a)) (-w₀) =
        -det3 (x (lab (i + 1)) - x (lab i)) (x (lab a) - x (lab (a - 1))) w₀ := by
      simp only [det3, PiLp.sub_apply, PiLp.neg_apply]; ring
    rw [e, neg_lt_zero]
    exact H2b i hi3' hi2' hi1'
  have H3' : ∀ i' j' : ZMod k, i' ≠ a' - 1 → i' ≠ a' → i' ≠ a' + 1 → (j' = i' ∨ j' = i' + 1) →
      (σ * LWrap.lwY (fun i => x (lab' i)) (-w₀) (a' + 1) (a' - 1) (a' - 1) -
          max 0 (max (σ * LWrap.lwY (fun i => x (lab' i)) (-w₀) (a' + 1) a' a')
            (σ * LWrap.lwY (fun i => x (lab' i)) (-w₀) (a' + 1) (a' - 1) a'))) /
        ((-ε) * ⟪x (lab' (a' - 1)) - x (lab' (a' + 1)), -w₀⟫) <
      (σ * LWrap.lwY (fun i => x (lab' i)) (-w₀) (a' + 1) i' j' -
          max 0 (max (σ * LWrap.lwY (fun i => x (lab' i)) (-w₀) (a' + 1) a' a')
            (σ * LWrap.lwY (fun i => x (lab' i)) (-w₀) (a' + 1) (a' - 1) a'))) /
        ((-ε) * ⟪x (lab' j') - x (lab' (a' + 1)), -w₀⟫) := by
    intro i' j' hi1 hi2 hi3 hj
    let i : ZMod k := -i' - 1
    let j : ZMod k := -j'
    have hi1' : i ≠ a + 1 := fun h => hi1 (by dsimp [i, a'] at h ⊢; linear_combination -h)
    have hi2' : i ≠ a := fun h => hi2 (by dsimp [i, a'] at h ⊢; linear_combination -h)
    have hi3' : i ≠ a - 1 := fun h => hi3 (by rw [ha1]; dsimp [i] at h ⊢; linear_combination -h)
    have hj' : j = i ∨ j = i + 1 := by
      rcases hj with rfl | rfl
      · right; simp [i, j]
      · left; simp [i, j]; ring
    have hw1 : LWrap.lwY (fun t => x (lab' t)) (-w₀) (a' + 1) (a' - 1) (a' - 1) =
        LWrap.lwY (fun t => x (lab t)) w₀ (a - 1) (a + 1) (a + 1 + 1) := by
      have h1 : -a = a' + 1 := ha1.symm
      have h2 : -(a + 1) - 1 = a' - 1 := ha0.symm
      have h3 : -(a + 1 + 1) = a' - 1 := by simp [a']; ring
      simpa [lab', h1, h2, h3] using lwY_rev (fun t => x (lab t)) w₀ a (a + 1) (a + 1 + 1) hD_edge
    have hw2 : LWrap.lwY (fun t => x (lab' t)) (-w₀) (a' + 1) a' a' =
        LWrap.lwY (fun t => x (lab t)) w₀ (a - 1) a (a + 1) := by
      have h1 : -a = a' + 1 := ha1.symm
      have h2 : -a - 1 = a' := rfl
      have h3 : -(a + 1) = a' := by simp [a']; ring
      simpa [lab', h1, h2, h3] using lwY_rev (fun t => x (lab t)) w₀ a a (a + 1) hD_edge
    have hw3 : LWrap.lwY (fun t => x (lab' t)) (-w₀) (a' + 1) (a' - 1) a' =
        LWrap.lwY (fun t => x (lab t)) w₀ (a - 1) (a + 1) (a + 1) := by
      have h1 : -a = a' + 1 := ha1.symm
      have h2 : -(a + 1) - 1 = a' - 1 := ha0.symm
      have h3 : -(a + 1) = a' := by simp [a']; ring
      simpa [lab', h1, h2, h3] using lwY_rev (fun t => x (lab t)) w₀ a (a + 1) (a + 1) hD_edge
    have hw4 : LWrap.lwY (fun t => x (lab' t)) (-w₀) (a' + 1) i' j' =
        LWrap.lwY (fun t => x (lab t)) w₀ (a - 1) i j := by
      have h1 : -a = a' + 1 := ha1.symm
      have h2 : -i - 1 = i' := by simp [i]
      have h3 : -j = j' := by simp [j]
      simpa [lab', h1, h2, h3] using lwY_rev (fun t => x (lab t)) w₀ a i j hD_edge
    have hd1 : (-ε) * ⟪x (lab' (a' - 1)) - x (lab' (a' + 1)), -w₀⟫ =
        ε * ⟪x (lab (a + 1 + 1)) - x (lab a), w₀⟫ := by
      have hidx : -(a' - 1) = a + 1 + 1 := by simp [a']; ring
      simp only [lab', ha1, neg_neg, hidx, inner_neg_right]; ring
    have hd2 : (-ε) * ⟪x (lab' j') - x (lab' (a' + 1)), -w₀⟫ =
        ε * ⟪x (lab j) - x (lab a), w₀⟫ := by
      have hidx : -j' = j := by simp [j]
      simp only [lab', ha1, neg_neg, hidx, inner_neg_right]; ring
    rw [hw1, hw2, hw3, hw4, hd1, hd2]
    exact H3 i j hi3' hi2' hi1' hj'
  exact LWrap.edgePlaneAny_of_lwrap_adj_twoRed hk x lab' hinj' (-w₀) hrim' hhid' a' (-ε)
    H1a' H1b' H2a' H2b' σ H3'

end Minimality.Split.Rev
