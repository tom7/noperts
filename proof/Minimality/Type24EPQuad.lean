module

public import Minimality.Type24EPFacet

/-!
# A quadrilateral facet cell is an Edge-Plane view (generic case)

Job LQF.  `QuadFacetEP` of `Type24EPFacet` for the facet `0345` of a type-24 solid, when no two opposite edges of
the quadrilateral are parallel (`QuadNoParallel`).  The strict rim of a view of the cell is the planar quad; its
depths are cyclically unimodal (planarity), so one of the four patterns "monotone / monotone reversed / `1243` /
`1342`" occurs after a rotation, and in each pattern one of two options `(a, c, σ)` satisfies the separation rows
of `splitRows_of_unimodal_separated`, the option being decided by the sign of `det3` of the two opposite edges
(an affine-invariant "which end the lines converge").  `Split.split_core_ep` turns `SplitRows` into
`Gen.EdgePlaneAny`.
-/

@[expose] public section

set_option autoImplicit false

open scoped RealInnerProductSpace Topology
open Finset Filter
open Minimality Minimality.H21 Minimality.T24.SAT Minimality.T24.NC Minimality.T24.Z0

namespace Minimality.T24.EPQ

theorem four_cases (j : ZMod 4) : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by revert j; decide

theorem det3_sub_left (A B C w : ℝ³) : Split.det3 (A - B) C w = Split.det3 A C w - Split.det3 B C w := by
  simp only [Split.det3, PiLp.sub_apply]; ring

theorem det3_sub_right (A B C w : ℝ³) : Split.det3 A (B - C) w = Split.det3 A B w - Split.det3 A C w := by
  simp only [Split.det3, PiLp.sub_apply]; ring

theorem det3_swap (A B w : ℝ³) : Split.det3 A B w = - Split.det3 B A w := by
  simp only [Split.det3]; ring

/-- No alternation of the depths of a planar convex quadrilateral (`z2 - z0 = al (z3 - z0) + be (z1 - z0)`). -/
theorem noalt1 {z0 z1 z2 z3 al be : ℝ} (hal : 0 < al) (hbe : 0 < be) (hab : 1 < al + be)
    (hr : z2 - z0 = al * (z3 - z0) + be * (z1 - z0)) :
    ¬ (z0 < z1 ∧ z0 < z3 ∧ z2 < z1 ∧ z2 < z3) := by
  rintro ⟨h1, h2, h3, h4⟩
  have hA : 0 < z3 - z0 := by linarith
  have hB : 0 < z1 - z0 := by linarith
  have e1 : al * (z3 - z0) < (1 - be) * (z1 - z0) := by nlinarith
  have e2 : be * (z1 - z0) < (1 - al) * (z3 - z0) := by nlinarith
  nlinarith [mul_pos hA hB, mul_pos hal hbe, mul_lt_mul'' e1 e2 (by positivity) (by positivity)]

theorem noalt2 {z0 z1 z2 z3 al be : ℝ} (hal : 0 < al) (hbe : 0 < be) (hab : 1 < al + be)
    (hr : z2 - z0 = al * (z3 - z0) + be * (z1 - z0)) :
    ¬ (z1 < z0 ∧ z1 < z2 ∧ z3 < z0 ∧ z3 < z2) := by
  rintro ⟨h1, h2, h3, h4⟩
  have hA : 0 < z0 - z3 := by linarith
  have hB : 0 < z0 - z1 := by linarith
  have e1 : al * (z0 - z3) < (1 - be) * (z0 - z1) := by nlinarith
  have e2 : be * (z0 - z1) < (1 - al) * (z0 - z3) := by nlinarith
  nlinarith [mul_pos hA hB, mul_pos hal hbe, mul_lt_mul'' e1 e2 (by positivity) (by positivity)]

/-- Pattern of four depths with the minimum first and no alternation. -/
def Pat (p q r s : ℝ) : Prop :=
  (p < q ∧ q < r ∧ r < s) ∨ (p < q ∧ q < s ∧ s < r) ∨ (p < s ∧ s < q ∧ q < r) ∨ (p < s ∧ s < r ∧ r < q)

theorem pat_exists {a b c d : ℝ} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
    (hcd : c ≠ d) (n1 : ¬ (a < b ∧ a < d ∧ c < b ∧ c < d)) (n2 : ¬ (b < a ∧ b < c ∧ d < a ∧ d < c)) :
    Pat a b c d ∨ Pat b c d a ∨ Pat c d a b ∨ Pat d a b c := by
  unfold Pat
  rcases lt_or_gt_of_ne hab with h1 | h1 <;> rcases lt_or_gt_of_ne hac with h2 | h2 <;>
  rcases lt_or_gt_of_ne had with h3 | h3 <;> rcases lt_or_gt_of_ne hbc with h4 | h4 <;>
  rcases lt_or_gt_of_ne hbd with h5 | h5 <;> rcases lt_or_gt_of_ne hcd with h6 | h6 <;>
  first
  | (exfalso; linarith)
  | (exfalso; exact n1 ⟨by linarith, by linarith, by linarith, by linarith⟩)
  | (exfalso; exact n2 ⟨by linarith, by linarith, by linarith, by linarith⟩)
  | exact Or.inl (Or.inl ⟨by linarith, by linarith, by linarith⟩)
  | exact Or.inl (Or.inr (Or.inl ⟨by linarith, by linarith, by linarith⟩))
  | exact Or.inl (Or.inr (Or.inr (Or.inl ⟨by linarith, by linarith, by linarith⟩)))
  | exact Or.inl (Or.inr (Or.inr (Or.inr ⟨by linarith, by linarith, by linarith⟩)))
  | exact Or.inr (Or.inl (Or.inl ⟨by linarith, by linarith, by linarith⟩))
  | exact Or.inr (Or.inl (Or.inr (Or.inl ⟨by linarith, by linarith, by linarith⟩)))
  | exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inl ⟨by linarith, by linarith, by linarith⟩))))
  | exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr ⟨by linarith, by linarith, by linarith⟩))))
  | exact Or.inr (Or.inr (Or.inl (Or.inl ⟨by linarith, by linarith, by linarith⟩)))
  | exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inl ⟨by linarith, by linarith, by linarith⟩))))
  | exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inl ⟨by linarith, by linarith, by linarith⟩)))))
  | exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr ⟨by linarith, by linarith, by linarith⟩)))))
  | exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by linarith, by linarith, by linarith⟩)))
  | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by linarith, by linarith, by linarith⟩))))
  | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by linarith, by linarith, by linarith⟩)))))
  | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by linarith, by linarith, by linarith⟩)))))


theorem z4add : ((0 : ZMod 4) + 1 = 1) ∧ ((1 : ZMod 4) + 1 = 2) ∧ ((2 : ZMod 4) + 1 = 3) ∧
    ((3 : ZMod 4) + 1 = 0) := by decide

set_option hygiene false in
/-- The three row goals of `splitRows_of_unimodal_separated` for explicit `(a, c, σ)` on four points. -/
macro "sr4_rows " a:term:max c:term:max sg:term:max : tactic => `(tactic| (
  obtain ⟨e0, e1, e2, e3⟩ := z4add
  refine ⟨$a, $c, $sg, by decide, by decide, Minimality.Split.splitRows_of_unimodal_separated (ρ := 1) (by norm_num)
    (fun i j h1 h2 => by simpa using hcyc i j h1 h2) (by decide) (by decide) ?_ ?_ ?_⟩
  · intro j hj1 hj2 hj3
    rcases four_cases j with rfl | rfl | rfl | rfl <;>
    first
    | exact (hj1 (by decide)).elim
    | exact (hj2 (by decide)).elim
    | exact (hj3 (by decide)).elim
    | (simp only [e0, e1, e2, e3, one_mul]
       simp only [Split.det3, PiLp.sub_apply] at hTS ⊢
       linarith)
  · intro j hj
    rcases four_cases j with rfl | rfl | rfl | rfl <;>
    first
    | (exfalso; revert hj; decide)
    | linarith
  · intro j hj
    rcases four_cases j with rfl | rfl | rfl | rfl <;>
    first
    | (exfalso; revert hj; decide)
    | linarith))

/-- Core: minimum of the depths at `0`. -/
theorem sr4_core {X : ZMod 4 → ℝ³} {w : ℝ³}
    (hcyc : ∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 → 0 < Split.det3 (X (i + 1) - X i) (X j - X i) w)
    (hT : Split.det3 (X 2 - X 1) (X 0 - X 3) w ≠ 0) (hS : Split.det3 (X 3 - X 2) (X 1 - X 0) w ≠ 0)
    (hp : Pat ⟪X 0, w⟫ ⟪X 1, w⟫ ⟪X 2, w⟫ ⟪X 3, w⟫) :
    ∃ a c : ZMod 4, ∃ σ : ℝ, c ≠ a ∧ c ≠ a + 1 ∧ Split.SplitRows X w a c σ := by
  unfold Pat at hp
  rcases hp with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · rcases lt_or_gt_of_ne hT with hTS | hTS
    · sr4_rows 3 2 1
    · sr4_rows 3 1 1
  · rcases lt_or_gt_of_ne hT with hTS | hTS
    · sr4_rows 1 3 (-1)
    · sr4_rows 3 1 1
  · rcases lt_or_gt_of_ne hS with hTS | hTS
    · sr4_rows 0 3 (-1)
    · sr4_rows 2 1 1
  · rcases lt_or_gt_of_ne hS with hTS | hTS
    · sr4_rows 0 3 (-1)
    · sr4_rows 0 2 (-1)

theorem splitRows_rot {X : ZMod 4 → ℝ³} {w : ℝ³} {r a c : ZMod 4} {σ : ℝ}
    (h : Split.SplitRows (fun i => X (i + r)) w a c σ) : Split.SplitRows X w (a + r) (c + r) σ := by
  intro i j hi hj hjc
  have := h (i - r) (j - r) (fun e => hi (by rw [← e]; ring))
    (by rcases hj with rfl | rfl
        · left; rfl
        · right; ring) (fun e => hjc (by rw [← e]; ring))
  have e1 : j - r + r = j := sub_add_cancel j r
  have e2 : i - r + r = i := sub_add_cancel i r
  have e3 : i - r + 1 + r = i + 1 := by ring
  have e4 : a + 1 + r = a + r + 1 := by ring
  simp only [e1, e2, e3, e4] at this
  exact this

/-- The edge-pair determinant of the rotation by `r`. -/
noncomputable def Tr (X : ZMod 4 → ℝ³) (w : ℝ³) (r : ZMod 4) : ℝ :=
  Split.det3 (X (2 + r) - X (1 + r)) (X (0 + r) - X (3 + r)) w

theorem sr4_exists {X : ZMod 4 → ℝ³} {w : ℝ³}
    (hcyc : ∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 → 0 < Split.det3 (X (i + 1) - X i) (X j - X i) w)
    (hT : ∀ r, Tr X w r ≠ 0)
    (hp : Pat ⟪X 0, w⟫ ⟪X 1, w⟫ ⟪X 2, w⟫ ⟪X 3, w⟫ ∨ Pat ⟪X 1, w⟫ ⟪X 2, w⟫ ⟪X 3, w⟫ ⟪X 0, w⟫ ∨
      Pat ⟪X 2, w⟫ ⟪X 3, w⟫ ⟪X 0, w⟫ ⟪X 1, w⟫ ∨ Pat ⟪X 3, w⟫ ⟪X 0, w⟫ ⟪X 1, w⟫ ⟪X 2, w⟫) :
    ∃ a c : ZMod 4, ∃ σ : ℝ, c ≠ a ∧ c ≠ a + 1 ∧ Split.SplitRows X w a c σ := by
  have key : ∀ r : ZMod 4, Pat ⟪X (0 + r), w⟫ ⟪X (1 + r), w⟫ ⟪X (2 + r), w⟫ ⟪X (3 + r), w⟫ →
      ∃ a c : ZMod 4, ∃ σ : ℝ, c ≠ a ∧ c ≠ a + 1 ∧ Split.SplitRows X w a c σ := by
    intro r hr
    have hS : Split.det3 ((fun i => X (i + r)) 3 - (fun i => X (i + r)) 2)
        ((fun i => X (i + r)) 1 - (fun i => X (i + r)) 0) w ≠ 0 := by
      have h := hT (1 + r)
      have q1 : ∀ r : ZMod 4, 2 + (1 + r) = 3 + r := by decide
      have q2 : ∀ r : ZMod 4, 1 + (1 + r) = 2 + r := by decide
      have q3 : ∀ r : ZMod 4, 0 + (1 + r) = 1 + r := by decide
      have q4 : ∀ r : ZMod 4, 3 + (1 + r) = 0 + r := by decide
      simp only [Tr, q1, q2, q3, q4] at h
      exact h
    obtain ⟨a, c, σ, h1, h2, h3⟩ := sr4_core (X := fun i => X (i + r)) (w := w)
      (fun i j hj1 hj2 => by
        have := hcyc (i + r) (j + r) (fun e => hj1 (add_right_cancel e))
          (fun e => hj2 (by have : j + r = i + 1 + r := by rw [e]; ring
                            exact add_right_cancel this))
        have e : i + r + 1 = i + 1 + r := by ring
        simp only [e] at this
        exact this)
      (by simpa [Tr] using hT r) hS hr
    refine ⟨a + r, c + r, σ, fun e => h1 (add_right_cancel e), fun e => h2 ?_, splitRows_rot h3⟩
    have : c + r = a + 1 + r := by rw [e]; ring
    exact add_right_cancel this
  rcases hp with h | h | h | h
  · exact key 0 h
  · exact key 1 h
  · exact key 2 h
  · exact key 3 h

theorem zmod4_ne_cases : ∀ i j : ZMod 4, i ≠ j → j = i + 1 ∨ j = i + 2 ∨ i = j + 1 := by decide

/-- **Generic strict quadrilateral rim.**  A strict planar quadrilateral rim of a view, no two opposite edges
parallel: `Gen.EdgePlaneAny x`. -/
theorem edgePlaneAny_of_strictRim4 (x : Fin 7 → ℝ³) (hseg : Split.NoBetween x)
    (hx : Function.Injective x) (lab : ZMod 4 → Fin 7)
    (hinj : Function.Injective lab) (w₀ : ℝ³) (hR : Split.StrictRimN x w₀ lab) (al be : ℝ)
    (hal : 0 < al) (hbe : 0 < be) (hab : 1 < al + be)
    (hrel : x (lab 2) - x (lab 0) = al • (x (lab 3) - x (lab 0)) + be • (x (lab 1) - x (lab 0)))
    (hnp : ∀ r : ZMod 4, cross (x (lab (2 + r)) - x (lab (1 + r))) (x (lab (0 + r)) - x (lab (3 + r))) ≠ 0) :
    Gen.EdgePlaneAny x := by
  have hcyc0 : ∀ w : ℝ³, Split.StrictRimN x w lab → ∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
      0 < Split.det3 (x (lab (i + 1)) - x (lab i)) (x (lab j) - x (lab i)) w :=
    fun w hw i j h1 h2 => hw (lab j) i (fun h => h1 (hinj h)) (fun h => h2 (hinj h))
  have n1 : ∀ i : ZMod 4, i + 2 ≠ i := by decide
  have n2 : ∀ i : ZMod 4, i + 2 ≠ i + 1 := by decide
  have n3 : ∀ i : ZMod 4, i + 1 ≠ i := by decide
  have hd1 : ∀ i : ZMod 4, x (lab (i + 1)) - x (lab i) ≠ 0 := by
    intro i h0
    have := hcyc0 w₀ hR i (i + 2) (n1 i) (n2 i)
    rw [h0] at this
    simp [Split.det3] at this
  have hd2 : ∀ i : ZMod 4, x (lab (i + 2)) - x (lab i) ≠ 0 := by
    intro i h0
    have := hcyc0 w₀ hR i (i + 2) (n1 i) (n2 i)
    rw [h0] at this
    simp [Split.det3] at this
  let vec : ZMod 4 × Fin 3 → ℝ³ := fun p =>
    ![cross (x (lab (2 + p.1)) - x (lab (1 + p.1))) (x (lab (0 + p.1)) - x (lab (3 + p.1))),
      x (lab (p.1 + 1)) - x (lab p.1), x (lab (p.1 + 2)) - x (lab p.1)] p.2
  have hvec : ∀ p, vec p ≠ 0 := by
    rintro ⟨r, k⟩
    fin_cases k
    · exact hnp r
    · exact hd1 r
    · exact hd2 r
  obtain ⟨v, -, hv⟩ := Minimality.exists_avoid_kernels (ι := ZMod 4 × Fin 3)
    (fun p => innerₗ ℝ³ (vec p))
    (fun p hy => by
      have h1 := LinearMap.congr_fun hy (vec p)
      simp only [innerₗ_apply_apply, LinearMap.zero_apply, inner_self_eq_zero] at h1
      exact hvec p h1) isOpen_univ Set.univ_nonempty
  have hK : ∀ᶠ s in 𝓝[>] (0 : ℝ), ∀ p, ⟪vec p, w₀⟫ + s * ⟪vec p, v⟫ ≠ 0 :=
    eventually_all.2 fun p => Minimality.eventually_affine_ne fun _ => by simpa using hv p
  obtain ⟨s, hs1, hs2⟩ := ((Split.strictRim_ev hR v).and hK).exists
  have key : ∀ (y : ℝ³), ⟪y, w₀⟫ + s * ⟪y, v⟫ = ⟪y, w₀ + s • v⟫ := by
    intro y; rw [inner_add_right, real_inner_smul_right]
  set w := w₀ + s • v with hw
  have hw' : ∀ p, ⟪vec p, w⟫ ≠ 0 := fun p => by rw [← key]; exact hs2 p
  -- distinct depths
  have hz : ∀ i j : ZMod 4, i ≠ j → ⟪x (lab i), w⟫ ≠ ⟪x (lab j), w⟫ := by
    intro i j hij h
    have hsub : ∀ a b : ZMod 4, ⟪x (lab a), w⟫ = ⟪x (lab b), w⟫ →
        ⟪x (lab a) - x (lab b), w⟫ = 0 := fun a b h => by rw [inner_sub_left, h, sub_self]
    rcases zmod4_ne_cases i j hij with e | e | e
    · apply hw' (i, 1)
      have := hsub _ _ h
      rw [e] at this
      show ⟪x (lab (i + 1)) - x (lab i), w⟫ = 0
      rw [← neg_sub, inner_neg_left, this, neg_zero]
    · apply hw' (i, 2)
      have := hsub _ _ h
      rw [e] at this
      show ⟪x (lab (i + 2)) - x (lab i), w⟫ = 0
      rw [← neg_sub, inner_neg_left, this, neg_zero]
    · apply hw' (j, 1)
      have := hsub _ _ h
      rw [e] at this
      show ⟪x (lab (j + 1)) - x (lab j), w⟫ = 0
      exact this
  have hrelz : ⟪x (lab 2), w⟫ - ⟪x (lab 0), w⟫ =
      al * (⟪x (lab 3), w⟫ - ⟪x (lab 0), w⟫) + be * (⟪x (lab 1), w⟫ - ⟪x (lab 0), w⟫) := by
    have := congrArg (fun v => ⟪v, w⟫) hrel
    simpa [inner_sub_left, inner_add_left, real_inner_smul_left] using this
  have hpat := pat_exists (hz 0 1 (by decide)) (hz 0 2 (by decide)) (hz 0 3 (by decide))
    (hz 1 2 (by decide)) (hz 1 3 (by decide)) (hz 2 3 (by decide))
    (noalt1 hal hbe hab hrelz) (noalt2 hal hbe hab hrelz)
  have hT : ∀ r, Tr (fun i => x (lab i)) w r ≠ 0 := by
    intro r
    have := hw' (r, 0)
    simp only [vec, Matrix.cons_val_zero] at this
    rw [← Split.det3_eq_inner_cross] at this
    exact this
  obtain ⟨a, c, σ, hca, hca1, hrows⟩ := sr4_exists (X := fun i => x (lab i)) (w := w)
    (hcyc0 w hs1) hT hpat
  exact Split.EV.split_core_ep (k := 4) (by norm_num) x hx hseg lab hinj w hs1 a c σ hca hca1 hrows

variable {x : Fin 7 → ℝ³}

theorem cross_swap' (a b : ℝ³) : cross a b = -cross b a := by
  ext i
  fin_cases i <;> simp [cross] <;> ring

/-- The residual special position: two opposite edges of the quadrilateral `0345` (rim `0 4 3 5`) are
parallel (edges `04 ∥ 35` or `43 ∥ 50`). -/
def QuadNoParallel (x : Fin 7 → ℝ³) : Prop :=
  cross (x 4 - x 0) (x 5 - x 3) ≠ 0 ∧ cross (x 3 - x 4) (x 0 - x 5) ≠ 0

private theorem s24_sep' :
    ∀ i j : Fin 7, j ≠ i → ∃ t : Fin 9, i ∈ s0x_S24 t ∧ j ∉ s0x_S24 t := by decide

/-- **`QuadFacetEP`, generic case.**  A view in the open cell of the quadrilateral facet `0345` of a type-24 solid
whose quadrilateral has no two parallel opposite edges gives `Gen.EdgePlaneAny x`. -/
theorem quadFacetEP_of_noParallel (F : S0xFac 9 s0x_S24 x) (hnp : QuadNoParallel x) {u : ℝ³}
    (hu : CellAt F {3} (nb 3) u) : Gen.EdgePlaneAny x := by
  have hx := Minimality.H24.SAT.inj_of_fac F
  have hc : Function.Injective rimG := by decide
  obtain ⟨D⟩ := silL_of_cell F rimG_cyc hu.cellLe hu
  choose μ hμ0 hμ using fun i => h21b_exists_mu (by norm_num) hx hc D i
  have hsign := h21b_sign_agree (by norm_num) hx hc D μ hμ0 hμ
  have Q : ∀ i m, m ≠ rimG i → m ≠ rimG (i + 1) →
      0 < D.fA i (x m) * ⟪D.B i, u⟫ - D.fB i (x m) * ⟪D.A i, u⟫ := by
    intro i m h0 h1
    have := h21b_Q_pos D i m h0 h1
    rcases this with h | ⟨h0', h⟩
    · exact h
    · rw [h0'] at h; exact absurd h (lt_irrefl _)
  have key : ∀ (i : ZMod 4) (m : Fin 7),
      Split.det3 (x (rimG (i + 1)) - x (rimG i)) (x m - x (rimG i)) u =
        μ i * (D.fA i (x m) * ⟪D.B i, u⟫ - D.fB i (x m) * ⟪D.A i, u⟫) := by
    intro i m
    rw [Split.det3_eq_minimality]
    exact h21b_det_eq D i (μ i) (hμ i) m u
  obtain ⟨al, be, hal, hbe, hab, hq⟩ := Minimality.T24.Par.par2546_quad F
  have hrel : x (rimG 2) - x (rimG 0) =
      al • (x (rimG 3) - x (rimG 0)) + be • (x (rimG 1) - x (rimG 0)) := by
    simpa [rimG] using hq
  have hseg := Split.noBetween_of_fac F s24_sep'
  have hnp' : ∀ r : ZMod 4, cross (x (rimG (2 + r)) - x (rimG (1 + r)))
      (x (rimG (0 + r)) - x (rimG (3 + r))) ≠ 0 := by
    obtain ⟨h1, h2⟩ := hnp
    intro r
    have hr : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := four_cases r
    rcases hr with rfl | rfl | rfl | rfl
    · simpa [rimG] using h2
    · have : cross (x 5 - x 3) (x 4 - x 0) = -cross (x 4 - x 0) (x 5 - x 3) := cross_swap' _ _
      intro h; apply h1
      simp only [show (2 : ZMod 4) + 1 = 3 from rfl, show (1 : ZMod 4) + 1 = 2 from rfl,
        show (0 : ZMod 4) + 1 = 1 from rfl, show (3 : ZMod 4) + 1 = 0 from rfl] at h
      simp [rimG] at h
      rw [this] at h
      simpa using h
    · have := cross_swap' (x 3 - x 4) (x 0 - x 5)
      intro h; apply h2
      simp only [show (2 : ZMod 4) + 2 = 0 from rfl, show (1 : ZMod 4) + 2 = 3 from rfl,
        show (0 : ZMod 4) + 2 = 2 from rfl, show (3 : ZMod 4) + 2 = 1 from rfl] at h
      simp [rimG] at h
      rw [this] at *
      simpa using h
    · intro h; apply h1
      simp only [show (2 : ZMod 4) + 3 = 1 from rfl, show (1 : ZMod 4) + 3 = 0 from rfl,
        show (0 : ZMod 4) + 3 = 3 from rfl, show (3 : ZMod 4) + 3 = 2 from rfl] at h
      simpa [rimG] using h
  rcases hsign with h | h
  · refine edgePlaneAny_of_strictRim4 x hseg hx rimG hc u ?_ al be hal hbe hab hrel hnp'
    intro m i h0 h1
    rw [key i m]
    exact mul_pos (h i) (Q i m h0 h1)
  · refine edgePlaneAny_of_strictRim4 x hseg hx rimG hc (-u) ?_ al be hal hbe hab hrel hnp'
    intro m i h0 h1
    have e : Split.det3 (x (rimG (i + 1)) - x (rimG i)) (x m - x (rimG i)) (-u) =
        -Split.det3 (x (rimG (i + 1)) - x (rimG i)) (x m - x (rimG i)) u := by
      rw [Split.det3_eq_inner_cross, Split.det3_eq_inner_cross, inner_neg_right]
    rw [e, key i m]
    have := Q i m h0 h1
    nlinarith [h i]

/-- The residual: a facet cell on `0345` whose quadrilateral has two parallel opposite edges. -/
def QuadFacetEPPar : Prop :=
  ∀ (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) (u : ℝ³), CellAt F {3} (nb 3) u → ¬ QuadNoParallel x →
    Gen.EdgePlaneAny x

/-- `QuadFacetEP` up to the parallel special position. -/
theorem quadFacetEP (h : QuadFacetEPPar) : EPF.QuadFacetEP := by
  intro x F u hu
  by_cases hn : QuadNoParallel x
  · exact quadFacetEP_of_noParallel F hn hu
  · exact h x F u hu hn

theorem openEP_iff_openEP'_par (h : QuadFacetEPPar) : Stmt.OpenEP ↔ EPF.OpenEP' :=
  EPF.openEP_iff_openEP' (quadFacetEP h)

end Minimality.T24.EPQ
