module

public import Minimality.Type24DeepC
public import Minimality.EdgePlaneNeg

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
open Minimality Minimality.H21 Minimality.T24.SAT

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

/-! ## FJ2: `T_0` instance (`v = 0`, facets `{0, 1, 2, 3, 4}`) -/

/-- Five vectors `p1, p2, p5, p4, p6` in `w^⊥` with `0 < det3 p_i p_{i+1} w` around the cycle
`(1, 2, 5, 4, 6, 1)` contain `0` strictly inside one of their triangles `(p_a, p_b, p_c)`. -/
private theorem triangle_of_five_ccw (p1 p2 p5 p4 p6 w : ℝ³)
    (h12 : 0 < Split.det3 p1 p2 w)
    (h25 : 0 < Split.det3 p2 p5 w)
    (h54 : 0 < Split.det3 p5 p4 w)
    (h46 : 0 < Split.det3 p4 p6 w)
    (h61 : 0 < Split.det3 p6 p1 w) :
    ∃ a b c : ℝ³, (a ∈ ({p1, p2, p5, p4, p6} : Finset ℝ³) ∧
      b ∈ ({p1, p2, p5, p4, p6} : Finset ℝ³) ∧
      c ∈ ({p1, p2, p5, p4, p6} : Finset ℝ³)) ∧
      0 < Split.det3 (b - a) (c - a) w ∧
      0 < Split.det3 (b - a) (-a) w ∧
      0 < Split.det3 (c - b) (-b) w ∧
      0 < Split.det3 (a - c) (-c) w := by
  have mkTri : ∀ a b c : ℝ³,
      a ∈ ({p1, p2, p5, p4, p6} : Finset ℝ³) →
      b ∈ ({p1, p2, p5, p4, p6} : Finset ℝ³) →
      c ∈ ({p1, p2, p5, p4, p6} : Finset ℝ³) →
      0 < Split.det3 a b w → 0 < Split.det3 b c w → 0 < Split.det3 c a w →
      ∃ a' b' c' : ℝ³, (a' ∈ ({p1, p2, p5, p4, p6} : Finset ℝ³) ∧
        b' ∈ ({p1, p2, p5, p4, p6} : Finset ℝ³) ∧
        c' ∈ ({p1, p2, p5, p4, p6} : Finset ℝ³)) ∧
        0 < Split.det3 (b' - a') (c' - a') w ∧
        0 < Split.det3 (b' - a') (-a') w ∧
        0 < Split.det3 (c' - b') (-b') w ∧
        0 < Split.det3 (a' - c') (-c') w := by
    intro a b c ha hb hc hab hbc hca
    refine ⟨a, b, c, ⟨ha, hb, hc⟩, ?_, ?_, ?_, ?_⟩
    · have e : Split.det3 (b - a) (c - a) w =
          Split.det3 a b w + Split.det3 b c w + Split.det3 c a w := by
        simp only [Split.det3, PiLp.sub_apply]; ring
      linarith
    · have e : Split.det3 (b - a) (-a) w = Split.det3 a b w := by
        simp only [Split.det3, PiLp.sub_apply, PiLp.neg_apply]; ring
      linarith
    · have e : Split.det3 (c - b) (-b) w = Split.det3 b c w := by
        simp only [Split.det3, PiLp.sub_apply, PiLp.neg_apply]; ring
      linarith
    · have e : Split.det3 (a - c) (-c) w = Split.det3 c a w := by
        simp only [Split.det3, PiLp.sub_apply, PiLp.neg_apply]; ring
      linarith
  have mem1 : p1 ∈ ({p1, p2, p5, p4, p6} : Finset ℝ³) := by simp
  have mem2 : p2 ∈ ({p1, p2, p5, p4, p6} : Finset ℝ³) := by simp
  have mem5 : p5 ∈ ({p1, p2, p5, p4, p6} : Finset ℝ³) := by simp
  have mem4 : p4 ∈ ({p1, p2, p5, p4, p6} : Finset ℝ³) := by simp
  have mem6 : p6 ∈ ({p1, p2, p5, p4, p6} : Finset ℝ³) := by simp
  -- Plücker identity in `w^⊥`: `det(u,v) * det(a,b) = det(u,a) * det(v,b) - det(u,b) * det(v,a)`
  have plucker : ∀ u v a b : ℝ³,
      Split.det3 u v w * Split.det3 a b w =
        Split.det3 u a w * Split.det3 v b w - Split.det3 u b w * Split.det3 v a w := by
    intro u v a b; simp only [Split.det3]; ring
  rcases lt_trichotomy (Split.det3 p1 p5 w) 0 with h15 | h15 | h15
  · exact mkTri p1 p2 p5 mem1 mem2 mem5 h12 h25 (by
      have : Split.det3 p5 p1 w = -Split.det3 p1 p5 w := by simp only [Split.det3]; ring
      linarith)
  · -- `det3 p1 p5 w = 0`: `det3 p2 p4 w` and `det3 p5 p6 w` handle all subcases
    have h56 : 0 < Split.det3 p5 p6 w := by
      have hp := plucker p1 p2 p5 p6
      rw [h15, zero_mul] at hp
      have h16 : Split.det3 p1 p6 w < 0 := by
        have : Split.det3 p1 p6 w = -Split.det3 p6 p1 w := by simp only [Split.det3]; ring
        linarith
      nlinarith
    rcases lt_trichotomy (Split.det3 p2 p6 w) 0 with h26 | h26 | h26
    · exact mkTri p2 p5 p6 mem2 mem5 mem6 h25 h56 (by
        have : Split.det3 p6 p2 w = -Split.det3 p2 p6 w := by simp only [Split.det3]; ring
        linarith)
    · -- `det3 p2 p6 w = 0` and `det3 p1 p5 w = 0`
      have hp2 := plucker p1 p5 p2 p4
      rw [h15, zero_mul] at hp2
      have h14 : Split.det3 p1 p4 w < 0 := by
        have h52 : Split.det3 p5 p2 w = -Split.det3 p2 p5 w := by simp only [Split.det3]; ring
        rw [h52] at hp2
        nlinarith
      have h24 : 0 < Split.det3 p2 p4 w := by
        have hp3 := plucker p1 p6 p2 p4
        have h62 : Split.det3 p6 p2 w = 0 := by
          have : Split.det3 p6 p2 w = -Split.det3 p2 p6 w := by simp only [Split.det3]; ring
          linarith
        rw [h62, mul_zero, sub_zero] at hp3
        have h16 : Split.det3 p1 p6 w < 0 := by
          have : Split.det3 p1 p6 w = -Split.det3 p6 p1 w := by simp only [Split.det3]; ring
          linarith
        have h64 : Split.det3 p6 p4 w < 0 := by
          have : Split.det3 p6 p4 w = -Split.det3 p4 p6 w := by simp only [Split.det3]; ring
          linarith
        nlinarith
      exact mkTri p1 p2 p4 mem1 mem2 mem4 h12 h24 (by
        have : Split.det3 p4 p1 w = -Split.det3 p1 p4 w := by simp only [Split.det3]; ring
        linarith)
    · have h14 : Split.det3 p1 p4 w < 0 := by
        have hp2 := plucker p1 p5 p2 p4
        rw [h15, zero_mul] at hp2
        have h52 : Split.det3 p5 p2 w = -Split.det3 p2 p5 w := by simp only [Split.det3]; ring
        rw [h52] at hp2
        nlinarith
      -- `det3 p2 p6 w > 0` and `det3 p4 p6 w > 0` and `det3 p1 p4 w < 0`:
      -- Check `det3 p2 p4 w`:
      rcases lt_trichotomy (Split.det3 p2 p4 w) 0 with h24 | h24 | h24
      · -- `det3 p2 p4 w < 0`: `det3 p4 p2 w > 0`, so `(p2, p5, p4)` works!
        exact mkTri p2 p5 p4 mem2 mem5 mem4 h25 h54 (by
          have : Split.det3 p4 p2 w = -Split.det3 p2 p4 w := by simp only [Split.det3]; ring
          linarith)
      · -- `det3 p2 p4 w = 0`: contradicts `det3 p2 p6 w > 0` and `det3 p4 p6 w > 0` via `plucker p1 p2 p4 p6`?
        -- Actually `det3 p1 p2 w * det3 p4 p6 w = det3 p1 p4 w * det3 p2 p6 w - det3 p1 p6 w * det3 p2 p4 w`:
        -- LHS `> 0`, RHS `< 0 - 0 = 0`, contradiction!
        exfalso
        have hp3 := plucker p1 p2 p4 p6
        rw [h24, mul_zero, sub_zero] at hp3
        nlinarith
      · exact mkTri p1 p2 p4 mem1 mem2 mem4 h12 h24 (by
          have : Split.det3 p4 p1 w = -Split.det3 p1 p4 w := by simp only [Split.det3]; ring
          linarith)
  · -- `0 < det3 p1 p5 w`
    rcases lt_trichotomy (Split.det3 p1 p4 w) 0 with h14 | h14 | h14
    · exact mkTri p1 p5 p4 mem1 mem5 mem4 h15 h54 (by
        have : Split.det3 p4 p1 w = -Split.det3 p1 p4 w := by simp only [Split.det3]; ring
        linarith)
    · -- `det3 p1 p4 w = 0`
      rcases lt_trichotomy (Split.det3 p5 p6 w) 0 with h56 | h56 | h56
      · -- `det3 p5 p6 w < 0` => `det3 p6 p5 w > 0`, so `(p5, p4, p6)` works!
        exact mkTri p5 p4 p6 mem5 mem4 mem6 h54 h46 (by
          have : Split.det3 p6 p5 w = -Split.det3 p5 p6 w := by simp only [Split.det3]; ring
          linarith)
      · have hp := plucker p1 p5 p2 p6
        rw [h56, mul_zero, zero_sub] at hp
        have h16 : Split.det3 p1 p6 w < 0 := by
          have : Split.det3 p1 p6 w = -Split.det3 p6 p1 w := by simp only [Split.det3]; ring
          linarith
        have h52 : Split.det3 p5 p2 w = -Split.det3 p2 p5 w := by simp only [Split.det3]; ring
        rw [h52] at hp
        have h62 : 0 < Split.det3 p6 p2 w := by
          have : Split.det3 p6 p2 w = -Split.det3 p2 p6 w := by simp only [Split.det3]; ring
          nlinarith
        have hp2 := plucker p1 p5 p2 p4
        rw [h14, zero_mul, sub_zero] at hp2
        have h24 : 0 < Split.det3 p2 p4 w := by nlinarith
        exact mkTri p2 p4 p6 mem2 mem4 mem6 h24 h46 h62
      · exact mkTri p1 p5 p6 mem1 mem5 mem6 h15 h56 h61
    · exact mkTri p1 p4 p6 mem1 mem4 mem6 h14 h46 h61

/-- **FJ2 (`edgePlaneAt_of_T0`):** if all five facets `{0, 1, 2, 3, 4}` incident to vertex `0`
have strictly negative (or all strictly positive) inner product with `w`, then `EdgePlaneAt`
on the base `x ∘ (0 : Fin 7).succAbove` transfers to `EdgePlaneAt x w`. -/
theorem edgePlaneAt_of_T0 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) {w : ℝ³}
    (hw : (∀ t ∈ ({0, 1, 2, 3, 4} : Finset (Fin 9)), ⟪F.N t, w⟫ < 0) ∨
          (∀ t ∈ ({0, 1, 2, 3, 4} : Finset (Fin 9)), 0 < ⟪F.N t, w⟫))
    (hEP : EdgePlaneAt (x ∘ (0 : Fin 7).succAbove) w) :
    EdgePlaneAt x w := by
  -- Reduce the `0 < ⟪F.N t, w⟫` branch to `⟪F.N t, -w⟫ < 0` via `edgePlaneAt_neg_iff`.
  suffices hneg : ∀ w' : ℝ³,
      (∀ t ∈ ({0, 1, 2, 3, 4} : Finset (Fin 9)), ⟪F.N t, w'⟫ < 0) →
      EdgePlaneAt (x ∘ (0 : Fin 7).succAbove) w' → EdgePlaneAt x w' by
    rcases hw with hw_neg | hw_pos
    · exact hneg w hw_neg hEP
    · have hw_neg : ∀ t ∈ ({0, 1, 2, 3, 4} : Finset (Fin 9)), ⟪F.N t, -w⟫ < 0 := fun t ht => by
        rw [inner_neg_right, neg_lt_zero]; exact hw_pos t ht
      exact (edgePlaneAt_neg_iff x w).mp (hneg (-w) hw_neg ((edgePlaneAt_neg_iff _ w).mpr hEP))
  intro w' hw' hEP'
  let e1 := x 1 - x 0
  let e2 := x 2 - x 0
  let e4 := x 4 - x 0
  let e5 := x 5 - x 0
  let e6 := x 6 - x 0
  have hdet_ne : Split.det3 e1 e2 e6 ≠ 0 := by
    have hne := (M4.type24OfFac F).det_ne
    intro h0; apply hne
    have heq : det24 x = -Split.det3 e1 e2 e6 := by
      dsimp only [e1, e2, e6]
      simp only [det24, vol3, Split.det3, PiLp.sub_apply]
      ring
    rw [heq, h0, neg_zero]
  -- Helper: if `N ⊥ u, v` and `⟪N, x q0 - x 0⟫ < 0` with `det3 u v (x q0 - x 0) ≠ 0`,
  -- then `det3 u v z * ⟪N, x q0 - x 0⟫ = det3 u v (x q0 - x 0) * ⟪N, z⟫` for all `z`.
  have hcross_eq : ∀ (t : Fin 9) (u v : ℝ³) (hu : ⟪F.N t, u⟫ = 0) (hv : ⟪F.N t, v⟫ = 0)
      (q0 : Fin 7) (hq0 : ⟪F.N t, x q0 - x 0⟫ < 0)
      (hdq : Split.det3 u v (x q0 - x 0) ≠ 0) (z : ℝ³),
      Split.det3 u v z * ⟪F.N t, x q0 - x 0⟫ = Split.det3 u v (x q0 - x 0) * ⟪F.N t, z⟫ := by
    intro t u v hu hv q0 hq0 hdq z
    let N := F.N t
    let d0 := x q0 - x 0
    have horth : ∀ r : ℝ³, ⟪r, u⟫ = 0 → ⟪r, v⟫ = 0 → ⟪r, d0⟫ = 0 → r = 0 := by
      intro r hru hrv hrd
      have hlin : ∀ y : ℝ³, Split.det3 u v d0 * ⟪r, y⟫ = 0 := by
        intro y
        have hid : Split.det3 u v d0 * ⟪r, y⟫ =
            ⟪r, u⟫ * Split.det3 v d0 y - ⟪r, v⟫ * Split.det3 u d0 y + ⟪r, d0⟫ * Split.det3 u v y := by
          simp only [Split.det3, Split.inner3]; ring
        rw [hid, hru, hrv, hrd]; ring
      have hr0 : ⟪r, r⟫ = 0 := (mul_eq_zero.mp (hlin r)).resolve_left hdq
      exact inner_self_eq_zero.mp hr0
    let r := Split.det3 u v d0 • N - ⟪N, d0⟫ • cross u v
    have hr0 : r = 0 := horth r
      (by rw [inner_sub_left, real_inner_smul_left, real_inner_smul_left, hu, mul_zero,
        show ⟪cross u v, u⟫ = 0 by simp only [Split.inner3, Split.cross_0, Split.cross_1, Split.cross_2]; ring,
        mul_zero, sub_zero])
      (by rw [inner_sub_left, real_inner_smul_left, real_inner_smul_left, hv, mul_zero,
        show ⟪cross u v, v⟫ = 0 by simp only [Split.inner3, Split.cross_0, Split.cross_1, Split.cross_2]; ring,
        mul_zero, sub_zero])
      (by rw [inner_sub_left, real_inner_smul_left, real_inner_smul_left]
          have : ⟪cross u v, d0⟫ = Split.det3 u v d0 := by
            simp only [Split.inner3, Split.det3, Split.cross_0, Split.cross_1, Split.cross_2]
          rw [this]; ring)
    have hrz : ⟪r, z⟫ = 0 := by rw [hr0, inner_zero_left]
    rw [inner_sub_left, real_inner_smul_left, real_inner_smul_left] at hrz
    have hcz : ⟪cross u v, z⟫ = Split.det3 u v z := by
      simp only [Split.inner3, Split.det3, Split.cross_0, Split.cross_1, Split.cross_2]
    rw [hcz] at hrz
    linarith
  have hplane_pos : ∀ (t : Fin 9) (ht : t ∈ ({0, 1, 2, 3, 4} : Finset (Fin 9))) (u v : ℝ³)
      (hu : ⟪F.N t, u⟫ = 0) (hv : ⟪F.N t, v⟫ = 0)
      (q0 : Fin 7) (hq0 : ⟪F.N t, x q0 - x 0⟫ < 0)
      (σ : ℝ) (hσq : 0 < σ * Split.det3 u v (x q0 - x 0)),
      0 < σ * Split.det3 u v w' := by
    intro t ht u v hu hv q0 hq0 σ hσq
    have hdq : Split.det3 u v (x q0 - x 0) ≠ 0 := by
      intro h0; rw [h0, mul_zero] at hσq; exact lt_irrefl 0 hσq
    have hcw := hcross_eq t u v hu hv q0 hq0 hdq w'
    have hNw : ⟪F.N t, w'⟫ < 0 := hw' t ht
    have hmul : 0 < (σ * Split.det3 u v (x q0 - x 0)) * ⟪F.N t, w'⟫ * ⟪F.N t, x q0 - x 0⟫ := by
      nlinarith [mul_neg_of_pos_of_neg hσq hNw]
    have heq : (σ * Split.det3 u v w') * (⟪F.N t, x q0 - x 0⟫ * ⟪F.N t, x q0 - x 0⟫) =
        (σ * Split.det3 u v (x q0 - x 0)) * ⟪F.N t, w'⟫ * ⟪F.N t, x q0 - x 0⟫ := by
      calc (σ * Split.det3 u v w') * (⟪F.N t, x q0 - x 0⟫ * ⟪F.N t, x q0 - x 0⟫)
          = σ * (Split.det3 u v w' * ⟪F.N t, x q0 - x 0⟫) * ⟪F.N t, x q0 - x 0⟫ := by ring
        _ = σ * (Split.det3 u v (x q0 - x 0) * ⟪F.N t, w'⟫) * ⟪F.N t, x q0 - x 0⟫ := by rw [hcw]
        _ = (σ * Split.det3 u v (x q0 - x 0)) * ⟪F.N t, w'⟫ * ⟪F.N t, x q0 - x 0⟫ := by ring
    rw [← heq] at hmul
    have hsq : 0 < ⟪F.N t, x q0 - x 0⟫ * ⟪F.N t, x q0 - x 0⟫ := mul_self_pos.mpr hq0.ne
    exact (mul_pos_iff.mp hmul).elim (fun h => h.1) (fun h => absurd h.2 (not_lt_of_gt hsq))
  -- Verify `⟪F.N t, x q - x 0⟫ < 0` for `q ∉ s0x_S24 t`
  have hf_lt : ∀ (t : Fin 9) (q : Fin 7), (0 : Fin 7) ∈ s0x_S24 t → q ∉ s0x_S24 t →
      ⟪F.N t, x q - x 0⟫ < 0 := by
    intro t q h0t hq
    rw [F.inner_sub t q 0, F.zero t 0 h0t, sub_zero]; exact F.neg t q hq
  have h10 : ⟪F.N 0, e1⟫ = 0 := by rw [F.inner_sub 0 1 0, F.zero 0 1 (by decide), F.zero 0 0 (by decide), sub_self]
  have h20 : ⟪F.N 0, e2⟫ = 0 := by rw [F.inner_sub 0 2 0, F.zero 0 2 (by decide), F.zero 0 0 (by decide), sub_self]
  have h61 : ⟪F.N 1, e6⟫ = 0 := by rw [F.inner_sub 1 6 0, F.zero 1 6 (by decide), F.zero 1 0 (by decide), sub_self]
  have h11 : ⟪F.N 1, e1⟫ = 0 := by rw [F.inner_sub 1 1 0, F.zero 1 1 (by decide), F.zero 1 0 (by decide), sub_self]
  have h22 : ⟪F.N 2, e2⟫ = 0 := by rw [F.inner_sub 2 2 0, F.zero 2 2 (by decide), F.zero 2 0 (by decide), sub_self]
  have h52 : ⟪F.N 2, e5⟫ = 0 := by rw [F.inner_sub 2 5 0, F.zero 2 5 (by decide), F.zero 2 0 (by decide), sub_self]
  have h53 : ⟪F.N 3, e5⟫ = 0 := by rw [F.inner_sub 3 5 0, F.zero 3 5 (by decide), F.zero 3 0 (by decide), sub_self]
  have h43 : ⟪F.N 3, e4⟫ = 0 := by rw [F.inner_sub 3 4 0, F.zero 3 4 (by decide), F.zero 3 0 (by decide), sub_self]
  have h44 : ⟪F.N 4, e4⟫ = 0 := by rw [F.inner_sub 4 4 0, F.zero 4 4 (by decide), F.zero 4 0 (by decide), sub_self]
  have h64 : ⟪F.N 4, e6⟫ = 0 := by rw [F.inner_sub 4 6 0, F.zero 4 6 (by decide), F.zero 4 0 (by decide), sub_self]
  let σ : ℝ := if 0 < Split.det3 e1 e2 e6 then 1 else -1
  have hσD : 0 < σ * Split.det3 e1 e2 e6 := by
    dsimp only [σ]; split_ifs with h
    · linarith
    · have := lt_of_le_of_ne (not_lt.mp h) hdet_ne; linarith
  have hs_612 : 0 < σ * Split.det3 e6 e1 e2 := by
    have : Split.det3 e6 e1 e2 = Split.det3 e1 e2 e6 := by simp only [Split.det3]; ring
    rw [this]; exact hσD
  have h612_ne : Split.det3 e6 e1 e2 ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hs_612; exact lt_irrefl 0 hs_612
  -- Helper to propagate `0 < σ * det3 u v z` from `0 < σ * det3 u v (x q0 - x 0)`
  have hprop : ∀ (t : Fin 9) (u v : ℝ³) (hu : ⟪F.N t, u⟫ = 0) (hv : ⟪F.N t, v⟫ = 0)
      (q0 q1 : Fin 7) (h0t : (0 : Fin 7) ∈ s0x_S24 t) (hq0 : q0 ∉ s0x_S24 t) (hq1 : q1 ∉ s0x_S24 t)
      (hσq : 0 < σ * Split.det3 u v (x q0 - x 0)),
      0 < σ * Split.det3 u v (x q1 - x 0) := by
    intro t u v hu hv q0 q1 h0t hq0 hq1 hσq
    have hdq : Split.det3 u v (x q0 - x 0) ≠ 0 := by
      intro h0; rw [h0, mul_zero] at hσq; exact lt_irrefl 0 hσq
    have hlt0 := hf_lt t q0 h0t hq0
    have hlt1 := hf_lt t q1 h0t hq1
    have hcw := hcross_eq t u v hu hv q0 hlt0 hdq (x q1 - x 0)
    have hmul : 0 < (σ * Split.det3 u v (x q0 - x 0)) * ⟪F.N t, x q1 - x 0⟫ * ⟪F.N t, x q0 - x 0⟫ := by
      nlinarith [mul_neg_of_pos_of_neg hσq hlt1]
    have heq : (σ * Split.det3 u v (x q1 - x 0)) * (⟪F.N t, x q0 - x 0⟫ * ⟪F.N t, x q0 - x 0⟫) =
        (σ * Split.det3 u v (x q0 - x 0)) * ⟪F.N t, x q1 - x 0⟫ * ⟪F.N t, x q0 - x 0⟫ := by
      calc (σ * Split.det3 u v (x q1 - x 0)) * (⟪F.N t, x q0 - x 0⟫ * ⟪F.N t, x q0 - x 0⟫)
          = σ * (Split.det3 u v (x q1 - x 0) * ⟪F.N t, x q0 - x 0⟫) * ⟪F.N t, x q0 - x 0⟫ := by ring
        _ = σ * (Split.det3 u v (x q0 - x 0) * ⟪F.N t, x q1 - x 0⟫) * ⟪F.N t, x q0 - x 0⟫ := by rw [hcw]
        _ = (σ * Split.det3 u v (x q0 - x 0)) * ⟪F.N t, x q1 - x 0⟫ * ⟪F.N t, x q0 - x 0⟫ := by ring
    rw [← heq] at hmul
    have hsq : 0 < ⟪F.N t, x q0 - x 0⟫ * ⟪F.N t, x q0 - x 0⟫ := mul_self_pos.mpr hlt0.ne
    exact (mul_pos_iff.mp hmul).elim (fun h => h.1) (fun h => absurd h.2 (not_lt_of_gt hsq))
  have hs_125 : 0 < σ * Split.det3 e1 e2 e5 :=
    hprop 0 e1 e2 h10 h20 6 5 (by decide) (by decide) (by decide) hσD
  have hs_251 : 0 < σ * Split.det3 e2 e5 e1 := by
    have : Split.det3 e2 e5 e1 = Split.det3 e1 e2 e5 := by simp only [Split.det3]; ring
    rw [this]; exact hs_125
  have hs_256 : 0 < σ * Split.det3 e2 e5 e6 :=
    hprop 2 e2 e5 h22 h52 1 6 (by decide) (by decide) (by decide) hs_251
  have hs_254 : 0 < σ * Split.det3 e2 e5 e4 :=
    hprop 2 e2 e5 h22 h52 1 4 (by decide) (by decide) (by decide) hs_251
  have hs_615 : 0 < σ * Split.det3 e6 e1 e5 :=
    hprop 1 e6 e1 h61 h11 2 5 (by decide) (by decide) (by decide) hs_612
  have hs_614 : 0 < σ * Split.det3 e6 e1 e4 :=
    hprop 1 e6 e1 h61 h11 2 4 (by decide) (by decide) (by decide) hs_612
  have hs_461 : 0 < σ * Split.det3 e4 e6 e1 := by
    have : Split.det3 e4 e6 e1 = Split.det3 e6 e1 e4 := by simp only [Split.det3]; ring
    rw [this]; exact hs_614
  have hs_465 : 0 < σ * Split.det3 e4 e6 e5 :=
    hprop 4 e4 e6 h44 h64 1 5 (by decide) (by decide) (by decide) hs_461
  have hs_541 : 0 < σ * Split.det3 e5 e4 e1 := by
    have hid : Split.det3 e2 e5 e6 * Split.det3 e5 e4 e1 =
        Split.det3 e6 e1 e5 * Split.det3 e2 e5 e4 + Split.det3 e1 e2 e5 * Split.det3 e4 e6 e5 := by
      simp only [Split.det3]; ring
    have hmul' : (σ * Split.det3 e2 e5 e6) * (σ * Split.det3 e5 e4 e1) =
        (σ * Split.det3 e6 e1 e5) * (σ * Split.det3 e2 e5 e4) +
        (σ * Split.det3 e1 e2 e5) * (σ * Split.det3 e4 e6 e5) := by
      calc (σ * Split.det3 e2 e5 e6) * (σ * Split.det3 e5 e4 e1)
          = σ ^ 2 * (Split.det3 e2 e5 e6 * Split.det3 e5 e4 e1) := by ring
        _ = σ ^ 2 * (Split.det3 e6 e1 e5 * Split.det3 e2 e5 e4 +
              Split.det3 e1 e2 e5 * Split.det3 e4 e6 e5) := by rw [hid]
        _ = (σ * Split.det3 e6 e1 e5) * (σ * Split.det3 e2 e5 e4) +
              (σ * Split.det3 e1 e2 e5) * (σ * Split.det3 e4 e6 e5) := by ring
    have hpos_rhs : 0 < (σ * Split.det3 e6 e1 e5) * (σ * Split.det3 e2 e5 e4) +
        (σ * Split.det3 e1 e2 e5) * (σ * Split.det3 e4 e6 e5) := by
      nlinarith [mul_pos hs_615 hs_254, mul_pos hs_125 hs_465]
    rw [← hmul'] at hpos_rhs
    exact (mul_pos_iff.mp hpos_rhs).elim (fun h => h.2) (fun h => absurd h.1 (not_lt_of_gt hs_256))
  -- Now all 5 cyclic edge determinants against `w'` have sign `σ`:
  have hw_12 : 0 < σ * Split.det3 e1 e2 w' :=
    hplane_pos 0 (by decide) e1 e2 h10 h20 6 (hf_lt 0 6 (by decide) (by decide)) σ hσD
  have hw_25 : 0 < σ * Split.det3 e2 e5 w' :=
    hplane_pos 2 (by decide) e2 e5 h22 h52 1 (hf_lt 2 1 (by decide) (by decide)) σ hs_251
  have hw_54 : 0 < σ * Split.det3 e5 e4 w' :=
    hplane_pos 3 (by decide) e5 e4 h53 h43 1 (hf_lt 3 1 (by decide) (by decide)) σ hs_541
  have hw_46 : 0 < σ * Split.det3 e4 e6 w' :=
    hplane_pos 4 (by decide) e4 e6 h44 h64 1 (hf_lt 4 1 (by decide) (by decide)) σ hs_461
  have hw_61 : 0 < σ * Split.det3 e6 e1 w' :=
    hplane_pos 1 (by decide) e6 e1 h61 h11 2 (hf_lt 1 2 (by decide) (by decide)) σ hs_612
  -- Extract a strict triangle containing `0` in `w'^⊥`
  have htri : ∃ a b c : ℝ³,
      (a ∈ ({e1, e2, e5, e4, e6} : Finset ℝ³) ∧
       b ∈ ({e1, e2, e5, e4, e6} : Finset ℝ³) ∧
       c ∈ ({e1, e2, e5, e4, e6} : Finset ℝ³)) ∧
      0 < Split.det3 (b - a) (c - a) w' ∧
      0 < Split.det3 (b - a) (-a) w' ∧
      0 < Split.det3 (c - b) (-b) w' ∧
      0 < Split.det3 (a - c) (-c) w' := by
    dsimp only [σ] at hw_12 hw_25 hw_54 hw_46 hw_61
    split_ifs at hw_12 hw_25 hw_54 hw_46 hw_61
    · exact triangle_of_five_ccw e1 e2 e5 e4 e6 w'
        (by simpa using hw_12) (by simpa using hw_25) (by simpa using hw_54)
        (by simpa using hw_46) (by simpa using hw_61)
    · have flip : ∀ u v : ℝ³, -1 * Split.det3 u v w' = Split.det3 v u w' := fun u v => by
        simp only [Split.det3]; ring
      rw [flip] at hw_12 hw_25 hw_54 hw_46 hw_61
      obtain ⟨a, b, c, ⟨ha, hb, hc⟩, t1, t2, t3, t4⟩ :=
        triangle_of_five_ccw e1 e6 e4 e5 e2 w' hw_61 hw_46 hw_54 hw_25 hw_12
      refine ⟨a, b, c, ⟨?_, ?_, ?_⟩, t1, t2, t3, t4⟩
      · rcases Finset.mem_insert.mp ha with rfl | ha <;> [simp; rcases Finset.mem_insert.mp ha with rfl | ha <;> [simp; rcases Finset.mem_insert.mp ha with rfl | ha <;> [simp; rcases Finset.mem_insert.mp ha with rfl | ha <;> [simp; (have := Finset.mem_singleton.mp ha; subst this; simp)]]]]
      · rcases Finset.mem_insert.mp hb with rfl | hb <;> [simp; rcases Finset.mem_insert.mp hb with rfl | hb <;> [simp; rcases Finset.mem_insert.mp hb with rfl | hb <;> [simp; rcases Finset.mem_insert.mp hb with rfl | hb <;> [simp; (have := Finset.mem_singleton.mp hb; subst this; simp)]]]]
      · rcases Finset.mem_insert.mp hc with rfl | hc <;> [simp; rcases Finset.mem_insert.mp hc with rfl | hc <;> [simp; rcases Finset.mem_insert.mp hc with rfl | hc <;> [simp; rcases Finset.mem_insert.mp hc with rfl | hc <;> [simp; (have := Finset.mem_singleton.mp hc; subst this; simp)]]]]
  rcases htri with ⟨a, b, c, ⟨ha, hb, hc⟩, t1, t2, t3, t4⟩
  have hmem_base : ∀ e : ℝ³, e ∈ ({e1, e2, e5, e4, e6} : Finset ℝ³) →
      e + x 0 ∈ univ.image (x ∘ (0 : Fin 7).succAbove) := by
    intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl | rfl | rfl
    · exact mem_image.mpr ⟨0, mem_univ _, by simp [e1]⟩
    · exact mem_image.mpr ⟨1, mem_univ _, by simp [e2]⟩
    · exact mem_image.mpr ⟨4, mem_univ _, by simp [e5]⟩
    · exact mem_image.mpr ⟨3, mem_univ _, by simp [e4]⟩
    · exact mem_image.mpr ⟨5, mem_univ _, by simp [e6]⟩
  refine edgePlaneAt_of_hidden x 0 w' hEP'
    ⟨a + x 0, b + x 0, c + x 0, hmem_base a ha, hmem_base b hb, hmem_base c hc, ?_, ?_, ?_, ?_⟩
  · simpa [sub_eq_add_neg, add_assoc] using t1
  · have : x 0 - (a + x 0) = -a := by abel
    simpa [this, sub_eq_add_neg, add_assoc] using t2
  · have : x 0 - (b + x 0) = -b := by abel
    simpa [this, sub_eq_add_neg, add_assoc] using t3
  · have : x 0 - (c + x 0) = -c := by abel
    simpa [this, sub_eq_add_neg, add_assoc] using t4

end Minimality.T24.DeepC
