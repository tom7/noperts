module

public import Minimality.Type24DeepC

/-!
# Hidden-vertex transfer for `EdgePlaneAt` (`FJ1` & `FJ2`)

* `edgePlaneAt_of_hidden` (`FJ1`): if `EdgePlaneAt (x ∘ v.succAbove) w` holds and `x v` lies
  strictly inside a projected triangle `(p, q, r)` of vertices from `x ∘ v.succAbove`, then
  `EdgePlaneAt x w` holds (via `lab' := v.succAbove ∘ lab`).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace
open Finset
open Minimality

namespace Minimality.T24.DeepC

/-- Cramer / barycentric identity in `w^⊥` for `Split.det3 · · w`. -/
private theorem det3_barycentric (u0 u1 p q r y w : ℝ³) :
    Split.det3 (q - p) (r - p) w * Split.det3 (u1 - u0) (y - u0) w =
      Split.det3 (r - q) (y - q) w * Split.det3 (u1 - u0) (p - u0) w +
      Split.det3 (p - r) (y - r) w * Split.det3 (u1 - u0) (q - u0) w +
      Split.det3 (q - p) (y - p) w * Split.det3 (u1 - u0) (r - u0) w := by
  simp only [Split.det3, PiLp.sub_apply]
  ring

/-- **FJ1 (`edgePlaneAt_of_hidden`):** if `EdgePlaneAt (x ∘ v.succAbove) w` holds and `x v` is
strictly inside a projected triangle `(p, q, r)` of `x ∘ v.succAbove` at view `w`, then
`EdgePlaneAt x w` holds. -/
theorem edgePlaneAt_of_hidden {n : ℕ} (x : Fin (n + 1) → ℝ³) (v : Fin (n + 1)) (w : ℝ³)
    (hEP : EdgePlaneAt (x ∘ v.succAbove) w)
    (hv : ∃ p q r : ℝ³,
      p ∈ univ.image (x ∘ v.succAbove) ∧
      q ∈ univ.image (x ∘ v.succAbove) ∧
      r ∈ univ.image (x ∘ v.succAbove) ∧
      0 < Split.det3 (q - p) (r - p) w ∧
      0 < Split.det3 (q - p) (x v - p) w ∧
      0 < Split.det3 (r - q) (x v - q) w ∧
      0 < Split.det3 (p - r) (x v - r) w) :
    EdgePlaneAt x w := by
  rcases hEP with ⟨k, hne, lab, a, s, α, μ, hk, hinj, hrim, hhid, hDw, hrows⟩
  have : NeZero k := hne
  let lab' : ZMod k → Fin (n + 1) := fun i => v.succAbove (lab i)
  have hinj' : Function.Injective lab' := fun i j h => hinj (Fin.succAbove_right_injective h)
  have hx_eq : ∀ t : ZMod k, x (lab' t) = (x ∘ v.succAbove) (lab t) := fun _ => rfl
  rcases hv with ⟨p, q, r, hp, hq, hr, hD, ht1, ht2, ht3⟩
  have hrim' : Split.StrictRimN x w lab' := by
    intro m i hm1 hm2
    by_cases hmv : m = v
    · rw [hmv]
      have hge : ∀ y ∈ univ.image (x ∘ v.succAbove),
          0 ≤ Split.det3 (x (lab' (i + 1)) - x (lab' i)) (y - x (lab' i)) w := by
        rintro y hy
        obtain ⟨m', _, rfl⟩ := mem_image.mp hy
        by_cases hm1' : m' = lab i
        · subst hm1'; simp only [hx_eq]; simp [Split.det3]
        · by_cases hm2' : m' = lab (i + 1)
          · subst hm2'; simp only [hx_eq]
            have h0 : Split.det3 ((x ∘ v.succAbove) (lab (i + 1)) - (x ∘ v.succAbove) (lab i))
                ((x ∘ v.succAbove) (lab (i + 1)) - (x ∘ v.succAbove) (lab i)) w = 0 := by
              simp only [Split.det3, PiLp.sub_apply]; ring
            rw [h0]
          · exact (hrim m' i hm1' hm2').le
      have hp_ge := hge p hp
      have hq_ge := hge q hq
      have hr_ge := hge r hr
      -- At least one of `p, q, r` has `0 < det3 (X (i+1) - X i) (· - X i) w`,
      -- since `3 ≤ k` gives some `j` with `0 < det3 (X (i+1) - X i) (X j - X i) w`.
      have hex : ∃ y ∈ ({p, q, r} : Finset ℝ³),
          0 < Split.det3 (x (lab' (i + 1)) - x (lab' i)) (y - x (lab' i)) w := by
        by_contra hnone
        push Not at hnone
        have hp0 : Split.det3 (x (lab' (i + 1)) - x (lab' i)) (p - x (lab' i)) w = 0 :=
          le_antisymm (hnone p (by simp)) hp_ge
        have hq0 : Split.det3 (x (lab' (i + 1)) - x (lab' i)) (q - x (lab' i)) w = 0 :=
          le_antisymm (hnone q (by simp)) hq_ge
        have hr0 : Split.det3 (x (lab' (i + 1)) - x (lab' i)) (r - x (lab' i)) w = 0 :=
          le_antisymm (hnone r (by simp)) hr_ge
        have hj : ∃ j : ZMod k, j ≠ i ∧ j ≠ i + 1 := by
          refine ⟨i + 2, ?_, ?_⟩
          · simpa using (Minimality.zmod_add_ne (k := k) (a := 0) (b := 2) (by omega) (by omega)
              (by decide) i).symm
          · simpa using (Minimality.zmod_add_ne (k := k) (a := 1) (b := 2) (by omega) (by omega)
              (by decide) i).symm
        obtain ⟨j, hj1, hj2⟩ := hj
        have hpos := hrim (lab j) i (fun h => hj1 (hinj h)) (fun h => hj2 (hinj h))
        have hid := det3_barycentric (x (lab' i)) (x (lab' (i + 1))) p q r (x (lab' j)) w
        rw [hp0, hq0, hr0, mul_zero, mul_zero, mul_zero, zero_add, zero_add] at hid
        have hmul0 := mul_eq_zero.mp hid
        rcases hmul0 with hD0 | hdet0
        · linarith
        · simp only [hx_eq] at hdet0; linarith
      have hid := det3_barycentric (x (lab' i)) (x (lab' (i + 1))) p q r (x v) w
      have hpos_rhs : 0 <
          Split.det3 (r - q) (x v - q) w * Split.det3 (x (lab' (i + 1)) - x (lab' i)) (p - x (lab' i)) w +
          Split.det3 (p - r) (x v - r) w * Split.det3 (x (lab' (i + 1)) - x (lab' i)) (q - x (lab' i)) w +
          Split.det3 (q - p) (x v - p) w * Split.det3 (x (lab' (i + 1)) - x (lab' i)) (r - x (lab' i)) w := by
        rcases hex with ⟨y, hy, hypos⟩
        rcases Finset.mem_insert.mp hy with rfl | hy
        · nlinarith [mul_pos ht2 hypos, mul_nonneg ht3.le hq_ge, mul_nonneg ht1.le hr_ge]
        rcases Finset.mem_insert.mp hy with rfl | hy
        · nlinarith [mul_nonneg ht2.le hp_ge, mul_pos ht3 hypos, mul_nonneg ht1.le hr_ge]
        · have hyr : y = r := Finset.mem_singleton.mp hy
          subst hyr
          nlinarith [mul_nonneg ht2.le hp_ge, mul_nonneg ht3.le hq_ge, mul_pos ht1 hypos]
      rw [← hid] at hpos_rhs
      exact (mul_pos_iff.mp hpos_rhs).elim (fun h => h.2) (fun h => absurd h.1 (not_lt_of_gt hD))
    · obtain ⟨m', rfl⟩ := Fin.exists_succAbove_eq hmv
      have hm1' : m' ≠ lab i := fun h => hm1 (congrArg v.succAbove h)
      have hm2' : m' ≠ lab (i + 1) := fun h => hm2 (congrArg v.succAbove h)
      exact hrim m' i hm1' hm2'
  have hhid' : Split.HiddenInTriangles x w lab' := by
    intro m hm
    have hsub : univ.image (x ∘ v.succAbove) ⊆ univ.image x := by
      intro y hy
      obtain ⟨j, _, rfl⟩ := mem_image.mp hy
      exact mem_image_of_mem x (mem_univ _)
    by_cases hmv : m = v
    · rw [hmv]
      exact ⟨p, hsub hp, q, hsub hq, r, hsub hr, hD, ht1, ht2, ht3⟩
    · obtain ⟨m', rfl⟩ := Fin.exists_succAbove_eq hmv
      have hm' : ∀ i, m' ≠ lab i := fun i h => hm i (congrArg v.succAbove h)
      obtain ⟨p', hp', q', hq', r', hr', t1, t2, t3, t4⟩ := hhid m' hm'
      exact ⟨p', hsub hp', q', hsub hq', r', hsub hr', t1, t2, t3, t4⟩
  refine ⟨k, hne, lab', a, s, α, μ, hk, hinj', hrim', hhid', ?_, ?_⟩
  · simpa [hx_eq] using hDw
  · intro i j hia hj
    simpa [hx_eq] using hrows i j hia hj

end Minimality.T24.DeepC
