module

public import Minimality.SplitEdgePlane
public import Minimality.SplitApex

/-!
# Every strict 3-rim view is Edge-Plane (up to a generic perturbation)

L1 of job L3R (FACENORM24.md, A73 REFEREE side claim; Carbon A75 Lemma 2.1).  Statement
`edgePlaneAny_of_strictRim3`: a strict triangle rim `lab : ZMod 3 → Fin n` of a view `w₀` (`StrictRimN`, so
every other point is strictly inside the projected triangle) gives `Gen.EdgePlaneAny x` for the point family `x`;
no injectivity of `x`, no facets, no other hypothesis.  Proof: perturb `w₀` (open conditions) so that the three
rim depths are distinct and the planes `hD`, `hnd` are avoided, take the median-depth vertex `c`, `a = c + 1`
(`SplitRows` by `splitRows_of_unimodal_separated` with `k = 3`), then `Split.EV.epRows_of_splitRows`.
-/

@[expose] public section

set_option autoImplicit false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality.Split.Rim3

variable {n : ℕ}

theorem zmod3_cases (j c : ZMod 3) : j = c ∨ j = c + 1 ∨ j = c + 1 + 1 := by
  revert j c; decide

theorem zmod3_val (j c : ZMod 3) :
    ((j - (c + 1) - 1).val < (c - (c + 1) - 1).val → j = c + 1 + 1) ∧
    ((c - (c + 1) - 1).val < (j - (c + 1) - 1).val → j = c + 1) := by
  revert j c; decide

theorem zmod3_cube (c : ZMod 3) : c + 1 + 1 + 1 = c := by revert c; decide

theorem zmod3_pred (c : ZMod 3) : c - 1 = c + 1 + 1 := by revert c; decide

/-- The rim edge `c+1 → c+2` of the triangle. -/
noncomputable def rd (x : Fin n → ℝ³) (lab : ZMod 3 → Fin n) (c : ZMod 3) : ℝ³ :=
  x (lab (c + 1 + 1)) - x (lab (c + 1))

/-- The component of `x (lab c) - x (lab (c+1))` orthogonal to the edge `rd c`. -/
noncomputable def re (x : Fin n → ℝ³) (lab : ZMod 3 → Fin n) (c : ZMod 3) : ℝ³ :=
  x (lab c) - x (lab (c + 1)) -
    (⟪x (lab c) - x (lab (c + 1)), rd x lab c⟫ / ⟪rd x lab c, rd x lab c⟫) • rd x lab c

theorem median3 {z0 z1 z2 : ℝ} (h01 : z0 ≠ z1) (h12 : z1 ≠ z2) (h20 : z2 ≠ z0) :
    (z1 - z0) * (z2 - z0) < 0 ∨ (z2 - z1) * (z0 - z1) < 0 ∨ (z0 - z2) * (z1 - z2) < 0 := by
  rcases lt_or_gt_of_ne h01 with a | a <;> rcases lt_or_gt_of_ne h12 with b | b <;>
    rcases lt_or_gt_of_ne h20 with c | c <;>
    first
    | (exfalso; linarith)
    | (left; nlinarith)
    | (right; left; nlinarith)
    | (right; right; nlinarith)

/-- The generic case: distinct depths and the two nondegeneracy planes avoided. -/
theorem edgePlaneAny_rim3_generic (x : Fin n → ℝ³) (lab : ZMod 3 → Fin n)
    (hinj : Function.Injective lab) (w : ℝ³) (hR : StrictRimN x w lab)
    (hd : ∀ c, ⟪rd x lab c, w⟫ ≠ 0) (he : ∀ c, ⟪re x lab c, w⟫ ≠ 0) :
    Gen.EdgePlaneAny x := by
  have n1 : ∀ c : ZMod 3, c + 1 ≠ c := by intro c; revert c; decide
  have n2 : ∀ c : ZMod 3, c + 1 + 1 ≠ c := by intro c; revert c; decide
  have n3 : ∀ c : ZMod 3, c + 1 + 1 ≠ c + 1 := by intro c; revert c; decide
  -- depths
  have hz : ∀ c : ZMod 3, ⟪x (lab (c + 1 + 1)), w⟫ ≠ ⟪x (lab (c + 1)), w⟫ := by
    intro c h
    apply hd c
    rw [rd, inner_sub_left, h, sub_self]
  have hz1 : ∀ c : ZMod 3, ⟪x (lab (c + 1)), w⟫ ≠ ⟪x (lab c), w⟫ := by
    intro c
    have := hz (c + 1 + 1)
    rw [zmod3_cube c] at this
    exact this
  obtain ⟨c, hc⟩ : ∃ c : ZMod 3, (⟪x (lab (c + 1)), w⟫ - ⟪x (lab c), w⟫) *
      (⟪x (lab (c + 1 + 1)), w⟫ - ⟪x (lab c), w⟫) < 0 := by
    have e1 : (0 : ZMod 3) + 1 = 1 := by decide
    have e2 : (0 : ZMod 3) + 1 + 1 = 2 := by decide
    have f1 : (1 : ZMod 3) + 1 = 2 := by decide
    have f2 : (1 : ZMod 3) + 1 + 1 = 0 := by decide
    have g1 : (2 : ZMod 3) + 1 = 0 := by decide
    have g2 : (2 : ZMod 3) + 1 + 1 = 1 := by decide
    have h01 := hz1 0
    have h12 := hz1 1
    have h20 := hz1 2
    rw [e1] at h01; rw [f1] at h12; rw [g1] at h20
    rcases median3 (z0 := ⟪x (lab 0), w⟫) (z1 := ⟪x (lab 1), w⟫) (z2 := ⟪x (lab 2), w⟫)
      (Ne.symm h01) (Ne.symm h12) (Ne.symm h20) with h | h | h
    · exact ⟨0, by rw [e2, e1]; exact h⟩
    · exact ⟨1, by rw [f2, f1]; exact h⟩
    · exact ⟨2, by rw [g2, g1]; exact h⟩
  set σ : ℝ := ⟪x (lab (c + 1)), w⟫ - ⟪x (lab c), w⟫ with hσ
  have hσ0 : σ ≠ 0 := sub_ne_zero.2 (hz1 c)
  have hS : SplitRows (fun i => x (lab i)) w (c + 1) c σ := by
    refine splitRows_of_unimodal_separated (ρ := 1) (by norm_num) ?_ (n1 c).symm
      (n2 c).symm ?_ ?_ ?_
    · intro i j hj1 hj2
      have := hR (lab j) i (fun h => hj1 (hinj h)) (fun h => hj2 (hinj h))
      simpa using this
    · intro j h1 h2 h3
      exfalso
      rcases zmod3_cases j c with h | h | h
      exacts [h3 h, h1 h, h2 h]
    · intro j hj
      have hj' := (zmod3_val j c).1 hj
      subst hj'
      nlinarith [hc]
    · intro j hj
      have hj' := (zmod3_val j c).2 hj
      subst hj'
      nlinarith [mul_self_pos.2 hσ0]
  have hD : ⟪x (lab (c + 1 + 1)) - x (lab (c + 1)), w⟫ ≠ 0 := hd c
  -- `hnd`
  have hd0 : rd x lab c ≠ 0 := by
    intro h0; apply hd c; rw [h0, inner_zero_left]
  have hnd : ⟪levelPoint (fun i => x (lab i)) w (c + 1) c - x (lab c),
      x (lab (c + 1 + 1)) - x (lab (c + 1))⟫ ≠ 0 := by
    have hdd : 0 < ⟪rd x lab c, rd x lab c⟫ := real_inner_self_pos.2 hd0
    have e1 : levelPoint (fun i => x (lab i)) w (c + 1) c - x (lab c) =
        (⟪x (lab c) - x (lab (c + 1)), w⟫ / ⟪rd x lab c, w⟫) • rd x lab c -
          (x (lab c) - x (lab (c + 1))) := by
      simp only [levelPoint, rd]; abel
    have e2 : x (lab (c + 1 + 1)) - x (lab (c + 1)) = rd x lab c := rfl
    rw [e2, e1, inner_sub_left, real_inner_smul_left]
    have hew' : ⟪x (lab c) - x (lab (c + 1)), w⟫ -
        (⟪x (lab c) - x (lab (c + 1)), rd x lab c⟫ / ⟪rd x lab c, rd x lab c⟫) * ⟪rd x lab c, w⟫
        ≠ 0 := by
      have := he c
      rwa [re, inner_sub_left, real_inner_smul_left] at this
    set κ := ⟪x (lab c) - x (lab (c + 1)), rd x lab c⟫ / ⟪rd x lab c, rd x lab c⟫ with hκ
    have hC : ⟪x (lab c) - x (lab (c + 1)), rd x lab c⟫ = κ * ⟪rd x lab c, rd x lab c⟫ := by
      rw [hκ]; field_simp
    rw [hC]
    intro h
    apply hew'
    have h2 : (⟪x (lab c) - x (lab (c + 1)), w⟫ / ⟪rd x lab c, w⟫ - κ) *
        ⟪rd x lab c, rd x lab c⟫ = 0 := by rw [sub_mul]; linarith
    have h3 := (mul_eq_zero.1 h2).resolve_right hdd.ne'
    rw [sub_eq_zero, div_eq_iff (hd c)] at h3
    linarith
  have hcv : Split.det3 (x (lab (c + 1)) - x (lab c)) (x (lab (c - 1)) - x (lab c)) w ≠ 0 := by
    have hcm := zmod3_pred c
    have := hR (lab (c - 1)) c (fun h => by
      have := hinj h; rw [hcm] at this; exact n2 c this)
      (fun h => by have := hinj h; rw [hcm] at this; exact n3 c this)
    exact this.ne'
  have hhid : HiddenInTriangles x w lab := by
    intro m hm
    have e01 : (0 : ZMod 3) + 1 = 1 := by decide
    have e12 : (1 : ZMod 3) + 1 = 2 := by decide
    have e20 : (2 : ZMod 3) + 1 = 0 := by decide
    have t0 := hR m 0 (hm 0) (by rw [e01]; exact hm 1)
    have t1 := hR m 1 (hm 1) (by rw [e12]; exact hm 2)
    have t2 := hR m 2 (hm 2) (by rw [e20]; exact hm 0)
    have t3 := hR (lab 2) 0 (hinj.ne (by decide)) (by rw [e01]; exact hinj.ne (by decide))
    rw [e01] at t0; rw [e12] at t1; rw [e20] at t2
    rw [e01] at t3
    exact ⟨x (lab 0), mem_image_of_mem _ (mem_univ _), x (lab 1), mem_image_of_mem _ (mem_univ _),
      x (lab 2), mem_image_of_mem _ (mem_univ _), t3, t0, t1, t2⟩
  obtain ⟨s, α, μ, hrow⟩ := Split.EV.epRows_of_splitRows (k := 3) (by norm_num)
    (fun i => x (lab i)) w (c + 1) c σ (n1 c).symm (n2 c).symm hS hD hnd hcv
  exact ⟨3, inferInstance, lab, w, c + 1, s, α, μ, le_rfl, hinj, hR, hhid, hD, hrow⟩

/-- **L1.**  A strict triangle rim of a view `w₀` carries an Edge-Plane certificate at a nearby view: every strict
3-rim view is `Gen.EdgePlaneAny` (no tie hypothesis; the perturbation is inside the proof). -/
theorem edgePlaneAny_of_strictRim3 (x : Fin n → ℝ³) (lab : ZMod 3 → Fin n)
    (hinj : Function.Injective lab) (w₀ : ℝ³) (hR : StrictRimN x w₀ lab) :
    Gen.EdgePlaneAny x := by
  have n1 : ∀ c : ZMod 3, c + 1 ≠ c := by intro c; revert c; decide
  have n2 : ∀ c : ZMod 3, c + 1 + 1 ≠ c := by intro c; revert c; decide
  have n3 : ∀ c : ZMod 3, c + 1 + 1 ≠ c + 1 := by intro c; revert c; decide
  have hd0 : ∀ c, rd x lab c ≠ 0 := by
    intro c h0
    have h := hR (lab c) (c + 1) (hinj.ne (n1 c).symm) (hinj.ne (n2 c).symm)
    have h' : x (lab (c + 1 + 1)) - x (lab (c + 1)) = 0 := h0
    rw [h'] at h
    simp [Split.det3] at h
  have he0 : ∀ c, re x lab c ≠ 0 := by
    intro c h0
    have h := hR (lab c) (c + 1) (hinj.ne (n1 c).symm) (hinj.ne (n2 c).symm)
    have h1 : x (lab c) - x (lab (c + 1)) =
        (⟪x (lab c) - x (lab (c + 1)), rd x lab c⟫ / ⟪rd x lab c, rd x lab c⟫) • rd x lab c := by
      rw [← sub_eq_zero]; exact h0
    have e2 : x (lab (c + 1 + 1)) - x (lab (c + 1)) = rd x lab c := rfl
    rw [e2, h1, det3_smul2, det3_self, mul_zero] at h
    exact lt_irrefl _ h
  let vec : ZMod 3 × Bool → ℝ³ := fun p => if p.2 then rd x lab p.1 else re x lab p.1
  have hvec : ∀ p, vec p ≠ 0 := by
    rintro ⟨c, b⟩
    cases b
    · simpa [vec] using he0 c
    · simpa [vec] using hd0 c
  obtain ⟨v, -, hv⟩ := Minimality.exists_avoid_kernels (ι := ZMod 3 × Bool)
    (fun p => innerₗ ℝ³ (vec p))
    (fun p hy => by
      have h1 := LinearMap.congr_fun hy (vec p)
      simp only [innerₗ_apply_apply, LinearMap.zero_apply, inner_self_eq_zero] at h1
      exact hvec p h1) isOpen_univ Set.univ_nonempty
  have hK : ∀ᶠ s in 𝓝[>] (0 : ℝ), ∀ p, ⟪vec p, w₀⟫ + s * ⟪vec p, v⟫ ≠ 0 :=
    eventually_all.2 fun p => Minimality.eventually_affine_ne fun _ => by simpa using hv p
  obtain ⟨s, hs1, hs2⟩ := ((strictRim_ev hR v).and hK).exists
  have key : ∀ (y : ℝ³), ⟪y, w₀⟫ + s * ⟪y, v⟫ = ⟪y, w₀ + s • v⟫ := by
    intro y; rw [inner_add_right, real_inner_smul_right]
  refine edgePlaneAny_rim3_generic x lab hinj (w₀ + s • v) hs1 (fun c => ?_) (fun c => ?_)
  · have := hs2 (c, true)
    simp only [vec, ite_true] at this
    rwa [key] at this
  · have := hs2 (c, false)
    simp only [vec, Bool.false_eq_true, ite_false] at this
    rwa [key] at this

end Minimality.Split.Rim3
