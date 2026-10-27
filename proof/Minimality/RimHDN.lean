module

public import Minimality.RobustCert
public import Minimality.Type08Cases

@[expose] public section

/-!
# A level triangle always has a horizontal double normal; rim-only HDN hypotheses
(`FEWER-FACES-PROOFS.md` §18.3)

* `hasHorizontalDoubleNormal_of_level_triangle`: a strictly convex triangle whose three corners
  have one depth has a horizontal double normal (the altitude from the vertex of the largest angle).
  This is why `IsRobustUnimodal`'s (R2) "no three equal" costs nothing at a view without
  horizontal double normals: Theorem 18.3 applies to every triangle rim.
* `NoHDNRim x u`: the rim cycle `x` has no horizontal double normal at the view `u` (the part of
  `NoHDNAt V u` that the certificates use); `NoHDNAt.rim`, `NoHDNRim.neg`.
* `isRupert_of_vertexView_robust_or`: `isRupert_of_vertexView_robust` with the rim-only hypothesis
  and with a level triangle rim allowed in place of robust unimodality.
-/

namespace Minimality

open scoped RealInnerProductSpace
open Finset

theorem inner_r2 (a b : ℝ²) : ⟪a, b⟫ = a 0 * b 0 + a 1 * b 1 := by
  simp only [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, conj_trivial]
  ring

/-- A vector whose inner products with the corners are `≤` those at a corner `p i` is in the
normal cone of the hull at `p i`. -/
theorem mem_normalConeAt_of_vertices {k : ℕ} (p : ZMod k → ℝ²) (n : ℝ²) (i : ZMod k)
    (h : ∀ j, ⟪n, p j - p i⟫ ≤ 0) :
    n ∈ normalConeAt (convexHull ℝ (Set.range p)) (p i) := by
  intro q hq
  have hsub : convexHull ℝ (Set.range p) ⊆ {w : ℝ² | ⟪n, w⟫ ≤ ⟪n, p i⟫} := by
    refine convexHull_min ?_ (convex_halfSpace_le (f := fun w : ℝ² => ⟪n, w⟫) ?_ _)
    · rintro _ ⟨j, rfl⟩
      have := h j
      rw [inner_sub_right] at this
      show ⟪n, p j⟫ ≤ ⟪n, p i⟫
      linarith
    · exact ⟨fun x y => inner_add_right _ _ _, fun c x => by simp [real_inner_smul_right]⟩
  have := hsub hq
  rw [inner_sub_right]
  simp only [Set.mem_setOf_eq] at this
  linarith

theorem sum_zmod3_of_distinct {M : Type*} [AddCommMonoid M] (g : ZMod 3 → M) (i j l : ZMod 3)
    (hij : i ≠ j) (hjl : j ≠ l) (hil : i ≠ l) : ∑ x, g x = g i + g j + g l := by
  have h3 : ∑ x, g x = g 0 + g 1 + g 2 := by
    first
      | exact Fin.sum_univ_three g
      | (rw [show (Finset.univ : Finset (ZMod 3)) = {0, 1, 2} from by decide]
         simp [add_assoc])
  have hc : ∀ i : ZMod 3, i = 0 ∨ i = 1 ∨ i = 2 := by decide
  rw [h3]
  rcases hc i with rfl | rfl | rfl <;> rcases hc j with rfl | rfl | rfl <;>
    rcases hc l with rfl | rfl | rfl <;>
    first | exact absurd rfl hij | exact absurd rfl hjl | exact absurd rfl hil | abel

set_option maxHeartbeats 1000000 in
/-- The level triangle with the top corner `p i` whose altitude foot lies on the side `p j p l`
(the angles at `p j`, `p l` are not obtuse). -/
theorem hdn_level_triangle_core (p : ZMod 3 → ℝ²) (z : ZMod 3 → ℝ) (z0 : ℝ)
    (hz : ∀ x, z x = z0) (hp : IsCcwPolygon p) (i j l : ZMod 3) (hij : i ≠ j) (hjl : j ≠ l)
    (hil : i ≠ l) (hall : ∀ x : ZMod 3, x = i ∨ x = j ∨ x = l)
    (hcr : 0 < cross2 (p j - p i) (p l - p i))
    (hB : 0 ≤ ⟪p i - p j, p l - p j⟫) (hC : 0 ≤ ⟪p i - p l, p j - p l⟫) :
    HasHorizontalDoubleNormal p z := by
  obtain ⟨W, hW⟩ : ∃ W : ℝ, W = (p l 0 - p j 0) * (p l 0 - p j 0) +
      (p l 1 - p j 1) * (p l 1 - p j 1) := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = (p i 0 - p j 0) * (p l 0 - p j 0) +
      (p i 1 - p j 1) * (p l 1 - p j 1) := ⟨_, rfl⟩
  obtain ⟨E, hE0, hE1⟩ : ∃ E : ℝ², E 0 = W * (p i 0 - p j 0) - s * (p l 0 - p j 0) ∧
      E 1 = W * (p i 1 - p j 1) - s * (p l 1 - p j 1) :=
    ⟨!₂[W * (p i 0 - p j 0) - s * (p l 0 - p j 0), W * (p i 1 - p j 1) - s * (p l 1 - p j 1)],
      by simp, by simp⟩
  have hcr' : 0 < (p j 0 - p i 0) * (p l 1 - p i 1) - (p j 1 - p i 1) * (p l 0 - p i 0) := by
    simpa only [cross2, PiLp.sub_apply] using hcr
  have hs0 : 0 ≤ s := by
    have := hB
    rw [inner_r2] at this
    simp only [PiLp.sub_apply] at this
    rw [hs]
    linarith
  have hWs : 0 ≤ W - s := by
    have := hC
    rw [inner_r2] at this
    simp only [PiLp.sub_apply] at this
    have e : W - s = (p i 0 - p l 0) * (p j 0 - p l 0) + (p i 1 - p l 1) * (p j 1 - p l 1) := by
      rw [hW, hs]; ring
    linarith
  -- `E` paired with the corners
  have hK : ⟪E, p i⟫ - ⟪E, p j⟫ =
      ((p i 0 - p j 0) * (p l 1 - p j 1) - (p i 1 - p j 1) * (p l 0 - p j 0)) ^ 2 := by
    rw [← inner_sub_right, inner_r2, hE0, hE1]
    simp only [PiLp.sub_apply]
    rw [hW, hs]
    ring
  have hKpos : 0 < ⟪E, p i⟫ - ⟪E, p j⟫ := by
    rw [hK]
    have hne : (p i 0 - p j 0) * (p l 1 - p j 1) - (p i 1 - p j 1) * (p l 0 - p j 0) ≠ 0 := by
      intro h0
      nlinarith [hcr']
    exact lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hne))
  have hEC : ⟪E, p l⟫ = ⟪E, p j⟫ := by
    have : ⟪E, p l⟫ - ⟪E, p j⟫ = 0 := by
      rw [← inner_sub_right, inner_r2, hE0, hE1]
      simp only [PiLp.sub_apply]
      rw [hW, hs]
      ring
    linarith
  have hWpos : 0 < W := by
    by_contra hneg
    have hW0 : W = 0 := le_antisymm (not_lt.mp hneg) (by
      rw [hW]; nlinarith [mul_self_nonneg (p l 0 - p j 0), mul_self_nonneg (p l 1 - p j 1)])
    have h1 : (p l 0 - p j 0) * (p l 0 - p j 0) = 0 := by
      nlinarith [mul_self_nonneg (p l 0 - p j 0), mul_self_nonneg (p l 1 - p j 1)]
    have h2 : (p l 1 - p j 1) * (p l 1 - p j 1) = 0 := by
      nlinarith [mul_self_nonneg (p l 0 - p j 0), mul_self_nonneg (p l 1 - p j 1)]
    have e0 := mul_self_eq_zero.mp h1
    have e1 := mul_self_eq_zero.mp h2
    rw [hK] at hKpos
    rw [e0, e1] at hKpos
    simp at hKpos
  have hE : E ≠ 0 := by
    intro h0
    rw [h0] at hKpos
    simp at hKpos
  obtain ⟨c, hci, hcj, hcl⟩ : ∃ c : ZMod 3 → ℝ, c i = W ∧ c j = -(W - s) ∧ c l = -s :=
    ⟨fun x => if x = i then W else if x = j then -(W - s) else -s, by simp,
      by simp [Ne.symm hij], by simp [Ne.symm hil, Ne.symm hjl]⟩
  have hf : ∀ x, c x • E ∈ normalConeAt (convexHull ℝ (Set.range p)) (p x) := by
    intro x
    refine mem_normalConeAt_of_vertices p (c x • E) x fun y => ?_
    rw [real_inner_smul_left, inner_sub_right]
    obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = ⟪E, p i⟫ - ⟪E, p j⟫ := ⟨_, rfl⟩
    have hKp : 0 < K := by rw [hKdef]; exact hKpos
    have hA : ⟪E, p i⟫ = ⟪E, p j⟫ + K := by rw [hKdef]; ring
    rcases hall x with hx | hx | hx <;> rcases hall y with hy | hy | hy <;>
      rw [hx, hy] <;> simp only [hci, hcj, hcl, hA, hEC] <;>
      nlinarith [mul_pos hWpos hKp, mul_nonneg hWs hKp.le, mul_nonneg hs0 hKp.le]
  have h1 : ∑ x, c x • E = 0 := by
    have hs : ∑ x, c x • E = c i • E + c j • E + c l • E :=
      sum_zmod3_of_distinct (fun x => c x • E) i j l hij hjl hil
    rw [hs]
    simp only [hci, hcj, hcl]
    rw [← add_smul, ← add_smul]
    have : W + -(W - s) + -s = 0 := by ring
    rw [this, zero_smul]
  have h2 : ∑ x, z x • (c x • E) = 0 := by
    simp only [hz]
    rw [← Finset.smul_sum, h1, smul_zero]
  have h3 : ∑ x, cross2 (p x) (c x • E) = 0 := by
    have hs : ∑ x, cross2 (p x) (c x • E) =
        cross2 (p i) (c i • E) + cross2 (p j) (c j • E) + cross2 (p l) (c l • E) :=
      sum_zmod3_of_distinct (fun x => cross2 (p x) (c x • E)) i j l hij hjl hil
    rw [hs]
    simp only [hci, hcj, hcl, cross2_smul_right]
    simp only [cross2, hE0, hE1]
    ring
  exact IsCcwPolygon.hdn_of_parallel hp z (f := fun x => c x • E) hf (e := E) hE c
    (fun x => rfl) (B := i) (by rw [hci]; exact hWpos) h1 h2 h3

set_option maxHeartbeats 1000000 in
/-- **A level triangle has a horizontal double normal** (§18.3): a strictly convex triangle whose
corners all have the same depth. -/
theorem hasHorizontalDoubleNormal_of_level_triangle (p : ZMod 3 → ℝ²) (z : ZMod 3 → ℝ)
    (hp : IsCcwPolygon p) (hz : ∀ i j, z i = z j) : HasHorizontalDoubleNormal p z := by
  have hz0 : ∀ x, z x = z 0 := fun x => hz x 0
  have hall : ∀ x : ZMod 3, x = 0 ∨ x = 1 ∨ x = 2 := by decide
  have hall1 : ∀ x : ZMod 3, x = 1 ∨ x = 2 ∨ x = 0 := by decide
  have hall2 : ∀ x : ZMod 3, x = 2 ∨ x = 0 ∨ x = 1 := by decide
  -- the angle products at the three corners
  have hs01 : 0 ≤ ((p 1 0 - p 0 0) * (p 2 0 - p 0 0) + (p 1 1 - p 0 1) * (p 2 1 - p 0 1)) +
      ((p 2 0 - p 1 0) * (p 0 0 - p 1 0) + (p 2 1 - p 1 1) * (p 0 1 - p 1 1)) := by
    nlinarith [sq_nonneg (p 1 0 - p 0 0), sq_nonneg (p 1 1 - p 0 1)]
  have hs12 : 0 ≤ ((p 2 0 - p 1 0) * (p 0 0 - p 1 0) + (p 2 1 - p 1 1) * (p 0 1 - p 1 1)) +
      ((p 0 0 - p 2 0) * (p 1 0 - p 2 0) + (p 0 1 - p 2 1) * (p 1 1 - p 2 1)) := by
    nlinarith [sq_nonneg (p 2 0 - p 1 0), sq_nonneg (p 2 1 - p 1 1)]
  have hs20 : 0 ≤ ((p 0 0 - p 2 0) * (p 1 0 - p 2 0) + (p 0 1 - p 2 1) * (p 1 1 - p 2 1)) +
      ((p 1 0 - p 0 0) * (p 2 0 - p 0 0) + (p 1 1 - p 0 1) * (p 2 1 - p 0 1)) := by
    nlinarith [sq_nonneg (p 0 0 - p 2 0), sq_nonneg (p 0 1 - p 2 1)]
  obtain ⟨d0, hd0⟩ : ∃ d, d = (p 1 0 - p 0 0) * (p 2 0 - p 0 0) +
      (p 1 1 - p 0 1) * (p 2 1 - p 0 1) := ⟨_, rfl⟩
  obtain ⟨d1, hd1⟩ : ∃ d, d = (p 2 0 - p 1 0) * (p 0 0 - p 1 0) +
      (p 2 1 - p 1 1) * (p 0 1 - p 1 1) := ⟨_, rfl⟩
  obtain ⟨d2, hd2⟩ : ∃ d, d = (p 0 0 - p 2 0) * (p 1 0 - p 2 0) +
      (p 0 1 - p 2 1) * (p 1 1 - p 2 1) := ⟨_, rfl⟩
  -- the cross products
  have e1 : (1 : ZMod 3) + 1 = 2 := by decide
  have e2 : (2 : ZMod 3) + 1 = 0 := by decide
  have e0 : (0 : ZMod 3) + 1 = 1 := by decide
  have c0 : 0 < cross2 (p 1 - p 0) (p 2 - p 0) := by
    have := hp.2 0 2 (by decide) (by decide)
    rw [e0] at this
    exact this
  have c1 : 0 < cross2 (p 2 - p 1) (p 0 - p 1) := by
    have := hp.2 1 0 (by decide) (by decide)
    rw [e1] at this
    exact this
  have c2 : 0 < cross2 (p 0 - p 2) (p 1 - p 2) := by
    have := hp.2 2 1 (by decide) (by decide)
    rw [e2] at this
    exact this
  -- the top corner
  rcases lt_or_ge d0 0 with h0 | h0
  · refine hdn_level_triangle_core p z (z 0) hz0 hp 0 1 2 (by decide) (by decide) (by decide)
      hall c0 ?_ ?_
    · rw [inner_r2]; simp only [PiLp.sub_apply]; nlinarith [hd1, hs01]
    · rw [inner_r2]; simp only [PiLp.sub_apply]; nlinarith [hd2, hs20]
  rcases lt_or_ge d1 0 with h1 | h1
  · refine hdn_level_triangle_core p z (z 0) hz0 hp 1 2 0 (by decide) (by decide) (by decide)
      hall1 c1 ?_ ?_
    · rw [inner_r2]; simp only [PiLp.sub_apply]; nlinarith [hd2, hs12]
    · rw [inner_r2]; simp only [PiLp.sub_apply]; nlinarith [hd0]
  rcases lt_or_ge d2 0 with h2 | h2
  · refine hdn_level_triangle_core p z (z 0) hz0 hp 2 0 1 (by decide) (by decide) (by decide)
      hall2 c2 ?_ ?_
    · rw [inner_r2]; simp only [PiLp.sub_apply]; nlinarith [hd0]
    · rw [inner_r2]; simp only [PiLp.sub_apply]; nlinarith [hd1]
  · refine hdn_level_triangle_core p z (z 0) hz0 hp 0 1 2 (by decide) (by decide) (by decide)
      hall c0 ?_ ?_
    · rw [inner_r2]; simp only [PiLp.sub_apply]; nlinarith [hd1]
    · rw [inner_r2]; simp only [PiLp.sub_apply]; nlinarith [hd2]

/-- **The rim cycle `x` has no horizontal double normal at the view `u`.** -/
def NoHDNRim {k : ℕ} (x : ZMod k → ℝ³) (u : ℝ³) : Prop :=
  ∀ R ∈ SO3, ∀ r : ℝ, r ≠ 0 → R.toEuclideanLin u = r • ez →
    IsCcwPolygon (fun i => proj_xy (R.toEuclideanLin (x i))) →
    ¬ HasHorizontalDoubleNormal (fun i => proj_xy (R.toEuclideanLin (x i)))
      (fun i => (R.toEuclideanLin (x i)) 2)

theorem NoHDNAt.rim {V : Finset ℝ³} {u : ℝ³} (h : NoHDNAt V u) {k : ℕ} (x : ZMod k → ℝ³)
    (hx : ∀ i, x i ∈ V) : NoHDNRim x u :=
  fun R hR r hr hRu hp => h R hR r hr hRu k x hx hp

theorem NoHDNRim.neg {k : ℕ} {x : ZMod k → ℝ³} {u : ℝ³} (h : NoHDNRim x u) : NoHDNRim x (-u) := by
  intro R hR r hr hRu
  refine h R hR (-r) (neg_ne_zero.mpr hr) ?_
  rw [map_neg] at hRu
  rw [neg_smul, ← hRu, neg_neg]

/-- **`isRupert_of_vertexView_robust`, rim-only, with a level triangle allowed**: the hypothesis
on the horizontal double normals is for the rim cycle only, and the depths are robustly unimodal
or (for a triangle) all equal (a level triangle always has a horizontal double normal, so that
case is excluded by `hnd`). -/
theorem isRupert_of_vertexView_robust_or (V M : Finset ℝ³) (u₀ : ℝ³) (hu₀ : u₀ ≠ 0) {k : ℕ}
    [NeZero k] (hk : 3 ≤ k) (x : ZMod k → ℝ³) (hxV : ∀ i, x i ∈ V) (hxM : ∀ i, x i ∉ M)
    (hcyc : ∀ i j, j ≠ i → j ≠ i + 1 → 0 < det3 (x (i + 1) - x i) (x j - x i) u₀)
    (hrest : ∀ y ∈ V, y ∉ M → (∀ j, y ≠ x j) → ∀ i,
      0 < det3 (x (i + 1) - x i) (y - x i) u₀)
    (hz : IsRobustUnimodal (fun i => ⟪x i, u₀⟫) ∨
      (k = 3 ∧ ∀ i j, ⟪x i, u₀⟫ = ⟪x j, u₀⟫)) (hnd : NoHDNRim x u₀)
    (hM : ∀ m ∈ M, ∃ i : ZMod k, ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
      m = x i + s • (x (i + 1) - x i) + δ • u₀) : IsRupert V := by
  obtain ⟨R, hR, r, hr, hRu⟩ := exists_rotation_to_ez_pos u₀ hu₀
  have hp : IsCcwPolygon (fun i => proj_xy (R.toEuclideanLin (x i))) := by
    refine ⟨hk, fun i j hi hj => ?_⟩
    simp only [proj_rot_sub]
    exact cross2_proj_rot_pos hR hr hRu (hcyc i j hi hj)
  have hdepth : ∀ y, (R.toEuclideanLin y) 2 = r⁻¹ * ⟪y, u₀⟫ := by
    intro y
    have : r * (R.toEuclideanLin y) 2 = ⟪y, u₀⟫ := by
      rw [← inner_ez, ← real_inner_smul_right, ← hRu, inner_toEuclideanLin_SO3 hR]
    rw [← this]; field_simp
  have hhdn := hnd R hR r hr.ne' hRu hp
  rcases hz with hz | ⟨hk3, hlev⟩
  · refine isRupert_of_chords_robustUnimodal V M R hR hr hRu x hxV hxM hp ?_ ?_ hhdn hM
    · intro y hy hyM hyx
      refine hp.mem_interior_of_left fun i => ?_
      simp only [proj_rot_sub]
      exact cross2_proj_rot_pos hR hr hRu (hrest y hy hyM hyx i)
    · simp only [hdepth]; exact hz.smul (inv_pos.mpr hr)
  · exfalso
    subst hk3
    refine hhdn (hasHorizontalDoubleNormal_of_level_triangle _ _ hp fun i j => ?_)
    show (R.toEuclideanLin (x i)) 2 = (R.toEuclideanLin (x j)) 2
    rw [hdepth, hdepth, hlev i j]

end Minimality

end
