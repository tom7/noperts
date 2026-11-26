module

public import Minimality.Type24HoleStatement
public import Minimality.HiddenCapFree
public import Minimality.EdgePlane

/-!
# Type 24: `DeepC` (Edge-Plane part) and its reduction to `OpenDeep`

Prepares the Edge-Plane piece of the deep-obtuse reduction (`DeepCEP`) and proves
`openDeep_of_deepCEP : DeepCEP d0 → OpenDeep d0`.

* `EdgePlaneAt`: `Gen.EdgePlaneAny` with the view `w` fixed (`edgePlaneAny_iff_exists_at`,
  `freeAt_of_edgePlaneAt`).
* `base`: the `Fin 6 → ℝ³` configuration obtained by removing vertex `1` from `x : Fin 7 → ℝ³`
  (`univ.image x = insert (x 1) (univ.image (base x))`).
* `freeAt_of_base_cone` (and `isRupert_of_base_cone`): `EdgePlaneAt (base x) w` at a cone view
  `w = ca • (x 0 - x 1) + cb • (x 2 - x 1) + cc • (x 6 - x 1)` (all coefficients of one sign,
  `det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) ≠ 0`) lifts to `Split.FreeAt (univ.image x) w`
  (via `freeAt_insert_of_cone`), hence `IsRupert (univ.image x)`, and in fact lifts to
  `EdgePlaneAt x w` (`edgePlaneAt_of_base_cone`), hence `Gen.EdgePlaneAny x`.
* `DeepCEP` (**[OPEN]**): every `CbarIn` deep-obtuse type-24 configuration has a cone view `w`
  (all coefficients of one sign) at which `EdgePlaneAt (base x) w` holds.
  (`openDeep_of_deepCEP` reduces `OpenDeep d0` to `DeepCEP d0` via `edgePlaneAt_of_base_cone`
  and `holeLeaf_not_edgePlaneAny`.)
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21 Minimality.T24.SAT Minimality.RimCell Minimality.T24.HC

namespace Minimality.T24.DeepC

/-! ## EZ1: `EdgePlaneAt` -/

/-- `Gen.EdgePlaneAny x` with the view `w` fixed. -/
def EdgePlaneAt {n : ℕ} (x : Fin n → ℝ³) (w : ℝ³) : Prop :=
  ∃ (k : ℕ) (_ : NeZero k) (lab : ZMod k → Fin n) (a : ZMod k) (s α μ : ℝ),
    3 ≤ k ∧ Function.Injective lab ∧ Split.StrictRimN x w lab ∧
    Split.HiddenInTriangles x w lab ∧
    ⟪x (lab (a + 1)) - x (lab a), w⟫ ≠ 0 ∧
    ∀ i j : ZMod k, i ≠ a → (j = i ∨ j = i + 1) →
      0 < (α + μ * ⟪x (lab j) - x (lab a), w⟫) *
          Split.det3 (x (lab (i + 1)) - x (lab i)) (x (lab (a + 1)) - x (lab a)) w +
        s * Split.edgePlaneSpin (fun i => x (lab i)) w a i j

/-- `Gen.EdgePlaneAny x` holds iff `EdgePlaneAt x w` holds for some view `w`. -/
theorem edgePlaneAny_iff_exists_at {n : ℕ} (x : Fin n → ℝ³) :
    Gen.EdgePlaneAny x ↔ ∃ w : ℝ³, EdgePlaneAt x w :=
  ⟨fun ⟨k, hne, lab, w, a, s, α, μ, h⟩ => ⟨w, k, hne, lab, a, s, α, μ, h⟩,
   fun ⟨w, k, hne, lab, a, s, α, μ, h⟩ => ⟨k, hne, lab, w, a, s, α, μ, h⟩⟩

/-- `EdgePlaneAt x w` gives `Split.FreeAt (univ.image x) w`. -/
theorem freeAt_of_edgePlaneAt {n : ℕ} {x : Fin n → ℝ³} {w : ℝ³} (h : EdgePlaneAt x w) :
    Split.FreeAt (univ.image x) w := by
  rcases h with ⟨k, hne, lab, a, s, α, μ, hk, hinj, hrim, hhid, hD, hrows⟩
  exact Split.freeAt_of_edgePlane hk x w lab hinj hrim hhid a s α μ hD hrows

/-! ## EZ2: Removing vertex `1` and lifting from `base x` at a cone view -/

/-- `x : Fin 7 → ℝ³` with vertex `1` removed (`0 ↦ 0, 1 ↦ 2, 2 ↦ 3, 3 ↦ 4, 4 ↦ 5, 5 ↦ 6`). -/
def base (x : Fin 7 → ℝ³) : Fin 6 → ℝ³ := fun i => x (Fin.succAbove 1 i)

theorem image_eq_insert_base (x : Fin 7 → ℝ³) :
    univ.image x = insert (x 1) (univ.image (base x)) := by
  ext y
  simp only [mem_image, mem_univ, true_and, mem_insert, base]
  constructor
  · rintro ⟨j, rfl⟩
    fin_cases j
    · right; exact ⟨0, congrArg x (by decide)⟩
    · left; rfl
    · right; exact ⟨1, congrArg x (by decide)⟩
    · right; exact ⟨2, congrArg x (by decide)⟩
    · right; exact ⟨3, congrArg x (by decide)⟩
    · right; exact ⟨4, congrArg x (by decide)⟩
    · right; exact ⟨5, congrArg x (by decide)⟩
  · rintro (rfl | ⟨i, rfl⟩)
    · exact ⟨1, rfl⟩
    · exact ⟨Fin.succAbove 1 i, rfl⟩

theorem base_zero (x : Fin 7 → ℝ³) : base x 0 = x 0 := congrArg x (by decide)

theorem base_one (x : Fin 7 → ℝ³) : base x 1 = x 2 := congrArg x (by decide)

theorem base_five (x : Fin 7 → ℝ³) : base x 5 = x 6 := congrArg x (by decide)

/-- At a cone view `w = ca (x 0 - x 1) + cb (x 2 - x 1) + cc (x 6 - x 1)` with all
coefficients of one sign and `det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) ≠ 0`,
`EdgePlaneAt (base x) w` gives `Split.FreeAt (univ.image x) w`. -/
theorem freeAt_of_base_cone (x : Fin 7 → ℝ³) (ca cb cc : ℝ)
    (hs : (0 < ca ∧ 0 < cb ∧ 0 < cc) ∨ (ca < 0 ∧ cb < 0 ∧ cc < 0))
    (hD : Split.det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) ≠ 0)
    (hEP : EdgePlaneAt (base x) (ca • (x 0 - x 1) + cb • (x 2 - x 1) + cc • (x 6 - x 1))) :
    Split.FreeAt (univ.image x) (ca • (x 0 - x 1) + cb • (x 2 - x 1) + cc • (x 6 - x 1)) := by
  rw [image_eq_insert_base]
  refine Split.freeAt_insert_of_cone (univ.image (base x)) (x 1) (x 0) (x 2) (x 6) ?_ ?_ ?_
    hD ca cb cc hs (freeAt_of_edgePlaneAt hEP)
  · exact mem_image.2 ⟨0, mem_univ _, base_zero x⟩
  · exact mem_image.2 ⟨1, mem_univ _, base_one x⟩
  · exact mem_image.2 ⟨5, mem_univ _, base_five x⟩

/-- `IsRupert (univ.image x)` from `freeAt_of_base_cone` (since `EdgePlaneAt` forces `w ≠ 0`). -/
theorem isRupert_of_base_cone (x : Fin 7 → ℝ³) (ca cb cc : ℝ)
    (hs : (0 < ca ∧ 0 < cb ∧ 0 < cc) ∨ (ca < 0 ∧ cb < 0 ∧ cc < 0))
    (hD : Split.det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) ≠ 0)
    (hEP : EdgePlaneAt (base x) (ca • (x 0 - x 1) + cb • (x 2 - x 1) + cc • (x 6 - x 1))) :
    IsRupert (univ.image x) := by
  have hw : ca • (x 0 - x 1) + cb • (x 2 - x 1) + cc • (x 6 - x 1) ≠ 0 := by
    rcases hEP with ⟨_, _, lab, a, _, _, _, _, _, _, _, hne, _⟩
    rintro h0
    rw [h0, inner_zero_right] at hne
    exact hne rfl
  exact Split.FreeAt.isRupert hw (freeAt_of_base_cone x ca cb cc hs hD hEP)

/-- Lifting `EdgePlaneAt (base x) w` at a cone view `w` directly to `EdgePlaneAt x w` (by
re-indexing `lab' := Fin.succAbove 1 ∘ lab`, since `x 1` is strictly inside `conv {x 0, x 2, x 6}`
in the projection along `w`). -/
theorem edgePlaneAt_of_base_cone (x : Fin 7 → ℝ³) (ca cb cc : ℝ)
    (hs : (0 < ca ∧ 0 < cb ∧ 0 < cc) ∨ (ca < 0 ∧ cb < 0 ∧ cc < 0))
    (hD : Split.det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) ≠ 0)
    (hEP : EdgePlaneAt (base x) (ca • (x 0 - x 1) + cb • (x 2 - x 1) + cc • (x 6 - x 1))) :
    EdgePlaneAt x (ca • (x 0 - x 1) + cb • (x 2 - x 1) + cc • (x 6 - x 1)) := by
  set w := ca • (x 0 - x 1) + cb • (x 2 - x 1) + cc • (x 6 - x 1)
  rcases hEP with ⟨k, hne, lab, a, s, α, μ, hk, hinj, hrim, hhid, hDw, hrows⟩
  let lab' : ZMod k → Fin 7 := fun i => Fin.succAbove 1 (lab i)
  have hinj' : Function.Injective lab' := (Fin.succAbove_right_injective).comp hinj
  have hx_eq : ∀ i, x (lab' i) = base x (lab i) := fun _ => rfl
  have hrim' : Split.StrictRimN x w lab' := by
    intro m i hm1 hm2
    by_cases hm : m = 1
    · subst hm
      let p := base x (lab i)
      let q := base x (lab (i + 1))
      have hge : ∀ j : Fin 6, 0 ≤ Split.det3 (q - p) (base x j - p) w := by
        intro j
        by_cases hj1 : j = lab i
        · subst hj1; simp [p, Split.det3]
        by_cases hj2 : j = lab (i + 1)
        · subst hj2; have h0 : Split.det3 (q - p) (q - p) w = 0 := by simp [Split.det3]; ring
          exact h0.ge
        exact (hrim j i hj1 hj2).le
      have hne_pair : ∃ j ∈ ({0, 1, 5} : Finset (Fin 6)), j ≠ lab i ∧ j ≠ lab (i + 1) := by
        by_contra hcon
        push Not at hcon
        have hsub : ({0, 1, 5} : Finset (Fin 6)) ⊆ {lab i, lab (i + 1)} := by
          intro j hj
          rcases eq_or_ne j (lab i) with rfl | h1
          · simp
          · simp [hcon j hj h1]
        have hcard := Finset.card_le_card hsub
        have h3 : ({0, 1, 5} : Finset (Fin 6)).card = 3 := by decide
        have h2 : ({lab i, lab (i + 1)} : Finset (Fin 6)).card ≤ 2 := Finset.card_le_two
        omega
      have hsum_pos :
          0 < (ca / (ca + cb + cc)) * Split.det3 (q - p) (x 0 - p) w +
              (cb / (ca + cb + cc)) * Split.det3 (q - p) (x 2 - p) w +
              (cc / (ca + cb + cc)) * Split.det3 (q - p) (x 6 - p) w := by
        have hS_ne : ca + cb + cc ≠ 0 := by
          rcases hs with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;> linarith
        have hw0 : 0 < ca / (ca + cb + cc) := by
          rcases hs with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
          · positivity
          · exact div_pos_of_neg_of_neg h1 (by linarith)
        have hw1 : 0 < cb / (ca + cb + cc) := by
          rcases hs with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
          · positivity
          · exact div_pos_of_neg_of_neg h2 (by linarith)
        have hw2 : 0 < cc / (ca + cb + cc) := by
          rcases hs with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
          · positivity
          · exact div_pos_of_neg_of_neg h3 (by linarith)
        have hg0 : 0 ≤ Split.det3 (q - p) (x 0 - p) w := by rw [← base_zero x]; exact hge 0
        have hg1 : 0 ≤ Split.det3 (q - p) (x 2 - p) w := by rw [← base_one x]; exact hge 1
        have hg2 : 0 ≤ Split.det3 (q - p) (x 6 - p) w := by rw [← base_five x]; exact hge 5
        rcases hne_pair with ⟨j, hjmem, hj1, hj2⟩
        have hjpos : 0 < Split.det3 (q - p) (base x j - p) w := hrim j i hj1 hj2
        rcases Finset.mem_insert.mp hjmem with rfl | hjmem
        · rw [base_zero] at hjpos
          nlinarith [mul_pos hw0 hjpos, mul_nonneg hw1.le hg1, mul_nonneg hw2.le hg2]
        rcases Finset.mem_insert.mp hjmem with rfl | hjmem
        · rw [base_one] at hjpos
          nlinarith [mul_nonneg hw0.le hg0, mul_pos hw1 hjpos, mul_nonneg hw2.le hg2]
        · have hj5 : j = 5 := Finset.mem_singleton.mp hjmem
          subst hj5
          rw [base_five] at hjpos
          nlinarith [mul_nonneg hw0.le hg0, mul_nonneg hw1.le hg1, mul_pos hw2 hjpos]
      have heq : Split.det3 (x (lab' (i + 1)) - x (lab' i)) (x 1 - x (lab' i)) w =
          (ca / (ca + cb + cc)) * Split.det3 (q - p) (x 0 - p) w +
          (cb / (ca + cb + cc)) * Split.det3 (q - p) (x 2 - p) w +
          (cc / (ca + cb + cc)) * Split.det3 (q - p) (x 6 - p) w := by
        have hS_ne : ca + cb + cc ≠ 0 := by
          rcases hs with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;> linarith
        dsimp only [p, q, lab', base, w]
        simp only [Split.det3, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
        field_simp [hS_ne]
        ring
      rw [heq]
      exact hsum_pos
    · obtain ⟨m', rfl⟩ : ∃ m' : Fin 6, Fin.succAbove 1 m' = m := by
        fin_cases m
        · exact ⟨0, by decide⟩
        · exact absurd rfl hm
        · exact ⟨1, by decide⟩
        · exact ⟨2, by decide⟩
        · exact ⟨3, by decide⟩
        · exact ⟨4, by decide⟩
        · exact ⟨5, by decide⟩
      have hm1' : m' ≠ lab i := fun h => hm1 (congrArg (Fin.succAbove 1) h)
      have hm2' : m' ≠ lab (i + 1) := fun h => hm2 (congrArg (Fin.succAbove 1) h)
      exact hrim m' i hm1' hm2'
  have hhid' : Split.HiddenInTriangles x w lab' := by
    intro m hm
    by_cases hm1 : m = 1
    · subst hm1
      have h0 : x 0 ∈ univ.image x := mem_image_of_mem x (mem_univ 0)
      have h2 : x 2 ∈ univ.image x := mem_image_of_mem x (mem_univ 2)
      have h6 : x 6 ∈ univ.image x := mem_image_of_mem x (mem_univ 6)
      rcases Split.det3_pos_triangle_of_cone (x 1) (x 0) (x 2) (x 6) ca cb cc hD hs with
        ⟨t1, t2, t3, t4⟩ | ⟨t1, t2, t3, t4⟩
      · exact ⟨x 0, h0, x 2, h2, x 6, h6, t1, t2, t3, t4⟩
      · exact ⟨x 0, h0, x 6, h6, x 2, h2, t1, t2, t3, t4⟩
    · obtain ⟨m', rfl⟩ : ∃ m' : Fin 6, Fin.succAbove 1 m' = m := by
        fin_cases m
        · exact ⟨0, by decide⟩
        · exact absurd rfl hm1
        · exact ⟨1, by decide⟩
        · exact ⟨2, by decide⟩
        · exact ⟨3, by decide⟩
        · exact ⟨4, by decide⟩
        · exact ⟨5, by decide⟩
      have hm' : ∀ i, m' ≠ lab i := fun i h => hm i (congrArg (Fin.succAbove 1) h)
      obtain ⟨p, hp, q, hq, r, hr, t1, t2, t3, t4⟩ := hhid m' hm'
      have hsub : univ.image (base x) ⊆ univ.image x := by
        rw [image_eq_insert_base]; exact subset_insert _ _
      exact ⟨p, hsub hp, q, hsub hq, r, hsub hr, t1, t2, t3, t4⟩
  refine ⟨k, hne, lab', a, s, α, μ, hk, hinj', hrim', hhid', ?_, ?_⟩
  · simpa [hx_eq] using hDw
  · intro i j hia hj
    simpa [hx_eq] using hrows i j hia hj

/-! ## EZ3: `DeepCEP` and reduction to `OpenDeep` -/

/-- At any type-24 facet family `F : S0xFac 9 s0x_S24 x`, the cone determinant
`det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1)` is nonzero (from `Type24.det_ne`). -/
theorem cone_det3_ne {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    Split.det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) ≠ 0 := by
  have hne : det24 x ≠ 0 := (M4.type24OfFac F).det_ne
  intro h0
  apply hne
  have heq : det24 x = Split.det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) := by
    simp only [det24, vol3, Split.det3]; ring
  rw [heq, h0]

/-- **[OPEN]** `DeepC` (Edge-Plane part): every `CbarIn` deep-obtuse type-24 configuration has a
cone view `w = ca (x 0 - x 1) + cb (x 2 - x 1) + cc (x 6 - x 1)` (all coefficients of one sign)
at which `EdgePlaneAt (base x) w` holds.  (See `notes/HOLE24-ROUTES-1126.md` sections 6.2 and 7.) -/
def DeepCEP (d0 : ℝ) : Prop :=
  ∀ (x : Fin 7 → ℝ³) (_ : S0xFac 9 s0x_S24 x), CbarIn x → Stmt.DeepObtuse d0 x →
    ∃ ca cb cc : ℝ,
      ((0 < ca ∧ 0 < cb ∧ 0 < cc) ∨ (ca < 0 ∧ cb < 0 ∧ cc < 0)) ∧
      EdgePlaneAt (base x) (ca • (x 0 - x 1) + cb • (x 2 - x 1) + cc • (x 6 - x 1))

/-- Reduction `DeepCEP d0 → OpenDeep d0`: at a `HoleFull` point `x`, `HoleLeaf` gives `CbarIn x`
and `¬ Gen.EdgePlaneAny x`, while `DeepCEP d0` and `cone_det3_ne F` produce `EdgePlaneAt x w` via
`edgePlaneAt_of_base_cone`, hence `Gen.EdgePlaneAny x`, contradiction. -/
theorem openDeep_of_deepCEP (d0 : ℝ) (h : DeepCEP d0) : Stmt.OpenDeep d0 := by
  intro x F hD hF
  obtain ⟨ca, cb, cc, hs, hEP⟩ := h x F hF.1.1 hD
  have hEP' := edgePlaneAt_of_base_cone x ca cb cc hs (cone_det3_ne F) hEP
  exact Atlas.holeLeaf_not_edgePlaneAny hF.1 ((edgePlaneAny_iff_exists_at x).2 ⟨_, hEP'⟩)

end Minimality.T24.DeepC
