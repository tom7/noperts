module

public import Minimality.EdgePair
public import Minimality.Type10
public import Minimality.FewVertices

@[expose] public section

/-!
# Type 24 outside `C̄` (§15)

`FEWER-FACES-PROOFS.md` §15.  Type 24 has the faces `012, 016, 126` (the cap `1`, of degree
3, with neighbours `0, 2, 6`), the side faces `236, 046, 025`, the quadrilateral `0345`, and
`235, 346`.  The proofs here use only the three cap faces and the three side faces
(`Type24`).

**Oblique coordinates at `1`** (`oblX0`, `oblX2`, `oblX6`, by Cramer's rule): `x v = x 1 +
X0 (x 0 − x 1) + X2 (x 2 − x 1) + X6 (x 6 − x 1)` (`Type24.rep`; the frame determinant
`det24` is nonzero, `Type24.det_ne`).  The cap faces make `X0, X2, X6 > 0` at `3, 4, 5`.
The side face `G_xc` through the axis vertices `x, c`, with apex `g` and third axis vertex
`y`, is the plane `X_x + X_c − ω_xc X_y = 1`, `ω_xc = (X_x(g) + X_c(g) − 1) / X_y(g)`, as in
§15.0: `omega3` (`236`), `omega4` (`046`), `omega5` (`025`); every point satisfies
`X_x + X_c − ω_xc X_y ≤ 1`, strictly off the face (`Type24.side236` and relatives: the face
functional is `f(x 1) (1 − (X_x + X_c − ω X_y))`).  `Δ = ω3 ω4 ω5 − ω3 − ω4 − ω5 − 2`
(`Delta24`); so all `ω > 0` with `Δ ≥ 0` force every product above 1
(`omega_prod_gt_one`).

* **Lemma CV, the corner view** (`isRupert_obliqueView_frame`, `isRupert_cornerView_frame`): if
  `1 + ω_ac, 1 + ω_bc, 1 + ω_ab > 0` and `Δ < 0`, the oblique view
  `((1 + ω_ac)(1 + ω_ab), (1 + ω_bc)(1 + ω_ab), (1 + ω_ac)(1 + ω_bc))` has the triangle `a b c`
  as silhouette with every other vertex strictly inside (`isRupert_obliqueView_frame`: any view
  coefficients with positive sum and the three inside conditions).  Metric-free: no depth
  condition, no horizontal double normal.
* The window triangle (Theorem 15.4) and Corollary 15.8 are now one generic frame lemma,
  `Minimality.isRupert_outsideCbar_frame` with the type-24 corollary
  `isRupert_type24_outside_Cbar''` (Type24OutsideCbar.lean); the window frame, `exists_window_t`,
  `window6 / 2 / 0`, `isRupert_type24_corner` and `isRupert_type24_outside_Cbar'` were deleted (pass 2, 11-24).
  `sideView` and the views `view0 / view2 / view6` are still used by Type24Corner.

Not formalized here: Lemma 15.2 at ties, §§15.4–15.5 (crossing certificates near the corner,
region `C̄`; the `C̄` region itself is the hole of `Minimality.T24.Hole24`).
-/

namespace Minimality

open Finset
open scoped RealInnerProductSpace

/-! ### Frames: Cramer's rule, determinants in oblique coordinates -/

/-- Cramer's rule as a vector identity. -/
theorem vol3_smul_cramer (e1 e2 e3 v : ℝ³) :
    vol3 e1 e2 e3 • v = vol3 v e2 e3 • e1 + vol3 e1 v e3 • e2 + vol3 e1 e2 v • e3 := by
  ext i
  fin_cases i <;> simp [vol3] <;> ring

/-- **Oblique coordinates** of `w` in the frame `o; a, b, c` (Cramer's rule). -/
theorem cramer_vec (o a b c w : ℝ³) (hD : vol3 (a - o) (b - o) (c - o) ≠ 0) :
    w = o + (vol3 (w - o) (b - o) (c - o) / vol3 (a - o) (b - o) (c - o)) • (a - o) +
      (vol3 (a - o) (w - o) (c - o) / vol3 (a - o) (b - o) (c - o)) • (b - o) +
      (vol3 (a - o) (b - o) (w - o) / vol3 (a - o) (b - o) (c - o)) • (c - o) := by
  have h := vol3_smul_cramer (a - o) (b - o) (c - o) (w - o)
  set D := vol3 (a - o) (b - o) (c - o)
  have h2 : w - o = D⁻¹ • (D • (w - o)) := by rw [smul_smul, inv_mul_cancel₀ hD, one_smul]
  rw [h, smul_add, smul_add, smul_smul, smul_smul, smul_smul] at h2
  rw [div_eq_inv_mul, div_eq_inv_mul, div_eq_inv_mul]
  conv_lhs => rw [← sub_add_cancel w o, h2]
  abel

/-- The triple product of three combinations of a frame. -/
theorem det3_comb (ea eb ec : ℝ³) (a0 a1 a2 b0 b1 b2 c0 c1 c2 : ℝ) :
    det3 (a0 • ea + a1 • eb + a2 • ec) (b0 • ea + b1 • eb + b2 • ec)
        (c0 • ea + c1 • eb + c2 • ec) =
      (a0 * (b1 * c2 - b2 * c1) - a1 * (b0 * c2 - b2 * c0) + a2 * (b0 * c1 - b1 * c0)) *
        vol3 ea eb ec := by
  simp only [det3_expand, vol3, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring

/-- Cauchy–Binet for `3 × 3`: the determinant of the matrix `⟪N_i, e_j⟫`. -/
theorem vol3_mul_inner (N1 N2 N3 e1 e2 e3 : ℝ³) :
    vol3 N1 N2 N3 * vol3 e1 e2 e3 =
      ⟪N1, e1⟫ * (⟪N2, e2⟫ * ⟪N3, e3⟫ - ⟪N2, e3⟫ * ⟪N3, e2⟫) -
        ⟪N1, e2⟫ * (⟪N2, e1⟫ * ⟪N3, e3⟫ - ⟪N2, e3⟫ * ⟪N3, e1⟫) +
        ⟪N1, e3⟫ * (⟪N2, e1⟫ * ⟪N3, e2⟫ - ⟪N2, e2⟫ * ⟪N3, e1⟫) := by
  simp only [vol3, PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, conj_trivial]
  ring

/-! ### The side crossings in a frame (Lemma 15.5, Theorem 15.7) -/

/-- The view of the side crossing at the axis vertex `pc` between the side faces
`G_ac` (coefficient `ω_ac`) and `G_bc` (`ω_bc`): oblique direction
`(1 + ω_ac, 1 + ω_bc, ω_ac ω_bc − 1)` in the frame `o; pa, pb, pc`. -/
def sideView (o pa pb pc : ℝ³) (wac wbc : ℝ) : ℝ³ :=
  (1 + wac) • (pa - o) + (1 + wbc) • (pb - o) + (wac * wbc - 1) • (pc - o)

/-! ### Type 24 -/

/-- A face of `x` from a set of labels (`Face16`): two labels on different sides of it give
different points. -/
theorem Face16.mem_iff {x : Fin 7 → ℝ³} {S : Finset (Fin 7)} (F : Face16 x S) {i j : Fin 7}
    (h : x i = x j) : i ∈ S ↔ j ∈ S := by
  constructor
  · intro hi; by_contra hj
    have := F.neg j hj; rw [← h, F.zero i hi] at this; exact lt_irrefl _ this
  · intro hj; by_contra hi
    have := F.neg i hi; rw [h, F.zero j hj] at this; exact lt_irrefl _ this

/-- **Type 24**, the faces used in §15: the cap faces `012`, `016`, `126` at the vertex `1`
and the side faces `236`, `046`, `025` (the quadrilateral `0345` and the faces `235`, `346`
are not needed), each given by an affine function vanishing on it and negative at the
other points. -/
structure Type24 (x : Fin 7 → ℝ³) where
  t012 : Face16 x {0, 1, 2}
  t016 : Face16 x {0, 1, 6}
  t126 : Face16 x {1, 2, 6}
  t236 : Face16 x {2, 3, 6}
  t046 : Face16 x {0, 4, 6}
  t025 : Face16 x {0, 2, 5}

/-- Type 24 from affine functionals. -/
noncomputable def Type24.ofAffine (x : Fin 7 → ℝ³) (fA fB fC fD fE fF : ℝ³ →ᵃ[ℝ] ℝ)
    (hA : ∀ i, (i ∈ ({0, 1, 2} : Finset (Fin 7)) → fA (x i) = 0) ∧
      (i ∉ ({0, 1, 2} : Finset (Fin 7)) → fA (x i) < 0))
    (hB : ∀ i, (i ∈ ({0, 1, 6} : Finset (Fin 7)) → fB (x i) = 0) ∧
      (i ∉ ({0, 1, 6} : Finset (Fin 7)) → fB (x i) < 0))
    (hC : ∀ i, (i ∈ ({1, 2, 6} : Finset (Fin 7)) → fC (x i) = 0) ∧
      (i ∉ ({1, 2, 6} : Finset (Fin 7)) → fC (x i) < 0))
    (hD : ∀ i, (i ∈ ({2, 3, 6} : Finset (Fin 7)) → fD (x i) = 0) ∧
      (i ∉ ({2, 3, 6} : Finset (Fin 7)) → fD (x i) < 0))
    (hE : ∀ i, (i ∈ ({0, 4, 6} : Finset (Fin 7)) → fE (x i) = 0) ∧
      (i ∉ ({0, 4, 6} : Finset (Fin 7)) → fE (x i) < 0))
    (hF : ∀ i, (i ∈ ({0, 2, 5} : Finset (Fin 7)) → fF (x i) = 0) ∧
      (i ∉ ({0, 2, 5} : Finset (Fin 7)) → fF (x i) < 0)) : Type24 x :=
  ⟨Face16.ofAffine fA hA, Face16.ofAffine fB hB, Face16.ofAffine fC hC, Face16.ofAffine fD hD,
    Face16.ofAffine fE hE, Face16.ofAffine fF hF⟩

/-- The six faces separate the seven points. -/
theorem Type24.inj {x : Fin 7 → ℝ³} (T : Type24 x) : Function.Injective x := by
  intro i j h
  have key : ∀ i j : Fin 7,
      (i ∈ ({0, 1, 2} : Finset (Fin 7)) ↔ j ∈ ({0, 1, 2} : Finset (Fin 7))) →
      (i ∈ ({0, 1, 6} : Finset (Fin 7)) ↔ j ∈ ({0, 1, 6} : Finset (Fin 7))) →
      (i ∈ ({1, 2, 6} : Finset (Fin 7)) ↔ j ∈ ({1, 2, 6} : Finset (Fin 7))) →
      (i ∈ ({2, 3, 6} : Finset (Fin 7)) ↔ j ∈ ({2, 3, 6} : Finset (Fin 7))) →
      (i ∈ ({0, 4, 6} : Finset (Fin 7)) ↔ j ∈ ({0, 4, 6} : Finset (Fin 7))) →
      (i ∈ ({0, 2, 5} : Finset (Fin 7)) ↔ j ∈ ({0, 2, 5} : Finset (Fin 7))) → i = j := by
    decide
  exact key i j (T.t012.mem_iff h) (T.t016.mem_iff h) (T.t126.mem_iff h) (T.t236.mem_iff h)
    (T.t046.mem_iff h) (T.t025.mem_iff h)

/-- The frame determinant at `1`: `[x 0 − x 1, x 2 − x 1, x 6 − x 1]`. -/
noncomputable def det24 (x : Fin 7 → ℝ³) : ℝ := vol3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1)

/-- The oblique coordinate along `x 0 − x 1` (axis `a`), by Cramer's rule. -/
noncomputable def oblX0 (x : Fin 7 → ℝ³) (v : Fin 7) : ℝ :=
  vol3 (x v - x 1) (x 2 - x 1) (x 6 - x 1) / det24 x

/-- The oblique coordinate along `x 2 − x 1` (axis `b`). -/
noncomputable def oblX2 (x : Fin 7 → ℝ³) (v : Fin 7) : ℝ :=
  vol3 (x 0 - x 1) (x v - x 1) (x 6 - x 1) / det24 x

/-- The oblique coordinate along `x 6 − x 1` (axis `c`). -/
noncomputable def oblX6 (x : Fin 7 → ℝ³) (v : Fin 7) : ℝ :=
  vol3 (x 0 - x 1) (x 2 - x 1) (x v - x 1) / det24 x

/-- `ω3 = ω_26` of the side face `236` (apex `3`): `(X2(3) + X6(3) − 1) / X0(3)`. -/
noncomputable def omega3 (x : Fin 7 → ℝ³) : ℝ := (oblX2 x 3 + oblX6 x 3 - 1) / oblX0 x 3

/-- `ω4 = ω_06` of the side face `046` (apex `4`): `(X0(4) + X6(4) − 1) / X2(4)`. -/
noncomputable def omega4 (x : Fin 7 → ℝ³) : ℝ := (oblX0 x 4 + oblX6 x 4 - 1) / oblX2 x 4

/-- `ω5 = ω_02` of the side face `025` (apex `5`): `(X0(5) + X2(5) − 1) / X6(5)`. -/
noncomputable def omega5 (x : Fin 7 → ℝ³) : ℝ := (oblX0 x 5 + oblX2 x 5 - 1) / oblX6 x 5

/-- `Δ = ω3 ω4 ω5 − ω3 − ω4 − ω5 − 2`. -/
noncomputable def Delta24 (x : Fin 7 → ℝ³) : ℝ :=
  omega3 x * omega4 x * omega5 x - omega3 x - omega4 x - omega5 x - 2

/-- If all `ω > 0` and `Δ ≥ 0`, every product `ω_g ω_h` exceeds 1. -/
theorem omega_prod_gt_one {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hΔ : 0 ≤ a * b * c - a - b - c - 2) : 1 < a * b := by
  by_contra h; push Not at h
  nlinarith [mul_nonneg hc.le (show 0 ≤ 1 - a * b by linarith)]

namespace Type24

theorem f_eq_inner {x : Fin 7 → ℝ³} {S : Finset (Fin 7)} (F : Face16 x S) (i j : Fin 7) :
    ⟪F.N, x i - x j⟫ = F.f (x i) - F.f (x j) := (F.hN (x i) (x j)).symm

theorem f_le {x : Fin 7 → ℝ³} {S : Finset (Fin 7)} (F : Face16 x S) (v : Fin 7) :
    F.f (x v) ≤ 0 := by
  by_cases h : v ∈ S
  · exact (F.zero v h).le
  · exact (F.neg v h).le

theorem mem {x : Fin 7 → ℝ³} (i : Fin 7) : x i ∈ univ.image x := mem_image_of_mem x (mem_univ i)

variable {x : Fin 7 → ℝ³} (T : Type24 x)
include T

/-- The frame at `1` is nondegenerate: the cap faces give the matrix `⟪N_i, e_j⟫` a
nonzero diagonal and zeros elsewhere (Cauchy–Binet). -/
theorem det_ne : det24 x ≠ 0 := by
  have e := vol3_mul_inner T.t126.N T.t016.N T.t012.N (x 0 - x 1) (x 2 - x 1) (x 6 - x 1)
  simp only [f_eq_inner] at e
  have z := fun {S : Finset (Fin 7)} (F : Face16 x S) (i : Fin 7) (h : i ∈ S) => F.zero i h
  rw [z T.t126 1 (by decide), z T.t126 2 (by decide), z T.t126 6 (by decide),
    z T.t016 0 (by decide), z T.t016 1 (by decide), z T.t016 6 (by decide),
    z T.t012 0 (by decide), z T.t012 1 (by decide), z T.t012 2 (by decide)] at e
  have h1 := T.t126.neg 0 (by decide)
  have h2 := T.t016.neg 2 (by decide)
  have h3 := T.t012.neg 6 (by decide)
  intro h0
  rw [det24] at h0
  rw [h0, mul_zero] at e
  have : T.t126.f (x 0) * (T.t016.f (x 2) * T.t012.f (x 6)) = 0 := by linear_combination -e
  rcases mul_eq_zero.mp this with h | h
  · linarith
  rcases mul_eq_zero.mp h with h | h <;> linarith

/-- The oblique coordinates at `1`. -/
theorem rep (v : Fin 7) : x v = x 1 + oblX0 x v • (x 0 - x 1) + oblX2 x v • (x 2 - x 1) +
    oblX6 x v • (x 6 - x 1) :=
  cramer_vec (x 1) (x 0) (x 2) (x 6) (x v) T.det_ne

/-- A face functional in oblique coordinates. -/
theorem eval {S : Finset (Fin 7)} (F : Face16 x S) (v : Fin 7) :
    F.f (x v) = F.f (x 1) + oblX0 x v * (F.f (x 0) - F.f (x 1)) +
      oblX2 x v * (F.f (x 2) - F.f (x 1)) + oblX6 x v * (F.f (x 6) - F.f (x 1)) := by
  conv_lhs => rw [T.rep v]
  exact affine_frame3 F.hN _ _ _ _ _ _ _

/-- Off the cap face `126`, `X0 > 0`. -/
theorem X0_pos {v : Fin 7} (hv : v ∉ ({1, 2, 6} : Finset (Fin 7))) : 0 < oblX0 x v := by
  have e := T.eval T.t126 v
  rw [T.t126.zero 1 (by decide), T.t126.zero 2 (by decide), T.t126.zero 6 (by decide)] at e
  have h0 := T.t126.neg 0 (by decide)
  have hv' := T.t126.neg v hv
  nlinarith

/-- Off the cap face `016`, `X2 > 0`. -/
theorem X2_pos {v : Fin 7} (hv : v ∉ ({0, 1, 6} : Finset (Fin 7))) : 0 < oblX2 x v := by
  have e := T.eval T.t016 v
  rw [T.t016.zero 0 (by decide), T.t016.zero 1 (by decide), T.t016.zero 6 (by decide)] at e
  have h0 := T.t016.neg 2 (by decide)
  have hv' := T.t016.neg v hv
  nlinarith

/-- Off the cap face `012`, `X6 > 0`. -/
theorem X6_pos {v : Fin 7} (hv : v ∉ ({0, 1, 2} : Finset (Fin 7))) : 0 < oblX6 x v := by
  have e := T.eval T.t012 v
  rw [T.t012.zero 0 (by decide), T.t012.zero 1 (by decide), T.t012.zero 2 (by decide)] at e
  have h0 := T.t012.neg 6 (by decide)
  have hv' := T.t012.neg v hv
  nlinarith

/-- The apex `3` lies on `X2 + X6 − ω3 X0 = 1`. -/
theorem eq3 : oblX2 x 3 + oblX6 x 3 - omega3 x * oblX0 x 3 = 1 := by
  have h := T.X0_pos (v := 3) (by decide)
  rw [omega3, div_mul_cancel₀ _ h.ne']; ring

/-- The apex `4` lies on `X0 + X6 − ω4 X2 = 1`. -/
theorem eq4 : oblX0 x 4 + oblX6 x 4 - omega4 x * oblX2 x 4 = 1 := by
  have h := T.X2_pos (v := 4) (by decide)
  rw [omega4, div_mul_cancel₀ _ h.ne']; ring

/-- The apex `5` lies on `X0 + X2 − ω5 X6 = 1`. -/
theorem eq5 : oblX0 x 5 + oblX2 x 5 - omega5 x * oblX6 x 5 = 1 := by
  have h := T.X6_pos (v := 5) (by decide)
  rw [omega5, div_mul_cancel₀ _ h.ne']; ring

/-- **The side face `236` in oblique coordinates**: its functional is
`f(x 1) (1 − (X2 + X6 − ω3 X0))`. -/
theorem side236 (v : Fin 7) :
    T.t236.f (x v) = T.t236.f (x 1) * (1 - (oblX2 x v + oblX6 x v - omega3 x * oblX0 x v)) := by
  have e := T.eval T.t236 v
  have e3 := T.eval T.t236 3
  rw [T.t236.zero 2 (by decide), T.t236.zero 6 (by decide)] at e e3
  rw [T.t236.zero 3 (by decide)] at e3
  have h3 := T.eq3
  have hX := T.X0_pos (v := 3) (by decide)
  have k : (T.t236.f (x 0) - T.t236.f (x 1) - omega3 x * T.t236.f (x 1)) * oblX0 x 3 = 0 := by
    linear_combination -e3 + T.t236.f (x 1) * h3
  have k' : T.t236.f (x 0) - T.t236.f (x 1) - omega3 x * T.t236.f (x 1) = 0 := by
    rcases mul_eq_zero.mp k with h | h
    · exact h
    · exact absurd h hX.ne'
  rw [e]; linear_combination oblX0 x v * k'

/-- The side face `046`: `f(x 1) (1 − (X0 + X6 − ω4 X2))`. -/
theorem side046 (v : Fin 7) :
    T.t046.f (x v) = T.t046.f (x 1) * (1 - (oblX0 x v + oblX6 x v - omega4 x * oblX2 x v)) := by
  have e := T.eval T.t046 v
  have e4 := T.eval T.t046 4
  rw [T.t046.zero 0 (by decide), T.t046.zero 6 (by decide)] at e e4
  rw [T.t046.zero 4 (by decide)] at e4
  have h4 := T.eq4
  have hX := T.X2_pos (v := 4) (by decide)
  have k : (T.t046.f (x 2) - T.t046.f (x 1) - omega4 x * T.t046.f (x 1)) * oblX2 x 4 = 0 := by
    linear_combination -e4 + T.t046.f (x 1) * h4
  have k' : T.t046.f (x 2) - T.t046.f (x 1) - omega4 x * T.t046.f (x 1) = 0 := by
    rcases mul_eq_zero.mp k with h | h
    · exact h
    · exact absurd h hX.ne'
  rw [e]; linear_combination oblX2 x v * k'

/-- The side face `025`: `f(x 1) (1 − (X0 + X2 − ω5 X6))`. -/
theorem side025 (v : Fin 7) :
    T.t025.f (x v) = T.t025.f (x 1) * (1 - (oblX0 x v + oblX2 x v - omega5 x * oblX6 x v)) := by
  have e := T.eval T.t025 v
  have e5 := T.eval T.t025 5
  rw [T.t025.zero 0 (by decide), T.t025.zero 2 (by decide)] at e e5
  rw [T.t025.zero 5 (by decide)] at e5
  have h5 := T.eq5
  have hX := T.X6_pos (v := 5) (by decide)
  have k : (T.t025.f (x 6) - T.t025.f (x 1) - omega5 x * T.t025.f (x 1)) * oblX6 x 5 = 0 := by
    linear_combination -e5 + T.t025.f (x 1) * h5
  have k' : T.t025.f (x 6) - T.t025.f (x 1) - omega5 x * T.t025.f (x 1) = 0 := by
    rcases mul_eq_zero.mp k with h | h
    · exact h
    · exact absurd h hX.ne'
  rw [e]; linear_combination oblX6 x v * k'

/-- Every point is beneath the plane of `236`. -/
theorem le236 (v : Fin 7) : oblX2 x v + oblX6 x v - omega3 x * oblX0 x v ≤ 1 := by
  have e := T.side236 v
  have h1 := T.t236.neg 1 (by decide)
  have h := f_le T.t236 v
  nlinarith

theorem lt236 {v : Fin 7} (hv : v ∉ ({2, 3, 6} : Finset (Fin 7))) :
    oblX2 x v + oblX6 x v - omega3 x * oblX0 x v < 1 := by
  have e := T.side236 v
  have h1 := T.t236.neg 1 (by decide)
  have h := T.t236.neg v hv
  nlinarith

theorem le046 (v : Fin 7) : oblX0 x v + oblX6 x v - omega4 x * oblX2 x v ≤ 1 := by
  have e := T.side046 v
  have h1 := T.t046.neg 1 (by decide)
  have h := f_le T.t046 v
  nlinarith

theorem lt046 {v : Fin 7} (hv : v ∉ ({0, 4, 6} : Finset (Fin 7))) :
    oblX0 x v + oblX6 x v - omega4 x * oblX2 x v < 1 := by
  have e := T.side046 v
  have h1 := T.t046.neg 1 (by decide)
  have h := T.t046.neg v hv
  nlinarith

theorem le025 (v : Fin 7) : oblX0 x v + oblX2 x v - omega5 x * oblX6 x v ≤ 1 := by
  have e := T.side025 v
  have h1 := T.t025.neg 1 (by decide)
  have h := f_le T.t025 v
  nlinarith

theorem lt025 {v : Fin 7} (hv : v ∉ ({0, 2, 5} : Finset (Fin 7))) :
    oblX0 x v + oblX2 x v - omega5 x * oblX6 x v < 1 := by
  have e := T.side025 v
  have h1 := T.t025.neg 1 (by decide)
  have h := T.t025.neg v hv
  nlinarith

/-- The oblique coordinates in the frame `x 1; x 0, x 6, x 2`. -/
theorem rep062 (v : Fin 7) : x v = x 1 + oblX0 x v • (x 0 - x 1) + oblX6 x v • (x 6 - x 1) +
    oblX2 x v • (x 2 - x 1) := by
  conv_lhs => rw [T.rep v]
  abel

/-- The oblique coordinates in the frame `x 1; x 2, x 6, x 0`. -/
theorem rep260 (v : Fin 7) : x v = x 1 + oblX2 x v • (x 2 - x 1) + oblX6 x v • (x 6 - x 1) +
    oblX0 x v • (x 0 - x 1) := by
  conv_lhs => rw [T.rep v]
  abel

end Type24

theorem fin7_cases (i : Fin 7) :
    i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by
  fin_cases i <;> simp

/-! ### Theorem 15.7, case B: the three side crossings -/

/-- The view of `S_6 = 046/236`: oblique `(1 + ω4, 1 + ω3, ω3 ω4 − 1)`. -/
noncomputable def view6 (x : Fin 7 → ℝ³) : ℝ³ :=
  sideView (x 1) (x 0) (x 2) (x 6) (omega4 x) (omega3 x)

/-- The view of `S_2 = 025/236`: oblique `(1 + ω5, ω3 ω5 − 1, 1 + ω3)`. -/
noncomputable def view2 (x : Fin 7 → ℝ³) : ℝ³ :=
  sideView (x 1) (x 0) (x 6) (x 2) (omega5 x) (omega3 x)

/-- The view of `S_0 = 025/046`: oblique `(ω4 ω5 − 1, 1 + ω5, 1 + ω4)`. -/
noncomputable def view0 (x : Fin 7 → ℝ³) : ℝ³ :=
  sideView (x 1) (x 2) (x 6) (x 0) (omega5 x) (omega4 x)

/-- Generic oblique-view frame lemma (the window frame's `key`, factored for any view coefficients
`da, db, dc` with `0 < da + db + dc`). -/
theorem isRupert_obliqueView_frame (V : Finset ℝ³) (o pa pb pc : ℝ³)
    (ha : pa ∈ V) (hb : pb ∈ V) (hc : pc ∈ V)
    (hD : vol3 (pa - o) (pb - o) (pc - o) ≠ 0) {da db dc : ℝ}
    (hS : 0 < da + db + dc)
    (hV : ∀ v ∈ V, v ≠ pa → v ≠ pb → v ≠ pc → ∃ A B C : ℝ,
      v = o + A • (pa - o) + B • (pb - o) + C • (pc - o) ∧
      0 < A * (db + dc) + da * (1 - B - C) ∧
      0 < B * (da + dc) + db * (1 - A - C) ∧
      0 < C * (da + db) + dc * (1 - A - B)) :
    IsRupert V := by
  classical
  obtain ⟨S, hS_eq⟩ : ∃ S : ℝ, S = da + db + dc := ⟨_, rfl⟩
  have hS0 : 0 < S := by rw [hS_eq]; exact hS
  obtain ⟨u, hu⟩ : ∃ u : ℝ³, u = da • (pa - o) + db • (pb - o) + dc • (pc - o) := ⟨_, rfl⟩
  obtain ⟨N, hN⟩ : ∃ N : ℝ³, N = cross (pb - pa) (pc - pa) := ⟨_, rfl⟩
  have hNu : ⟪N, u⟫ = S * vol3 (pa - o) (pb - o) (pc - o) := by
    rw [hN, hu, hS_eq]
    change det3 _ _ _ = _
    simp only [det3_expand, vol3, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  have hNu0 : ⟪N, u⟫ ≠ 0 := by rw [hNu]; exact mul_ne_zero hS0.ne' hD
  have hN0 : N ≠ 0 := by intro h0; apply hNu0; rw [h0, inner_zero_left]
  have hind : AffineIndependent ℝ ![pa, pb, pc] := by
    rw [hN] at hN0; exact affineIndependent_of_cross_ne_zero hN0
  have hinj := hind.injective
  have hab : pa ≠ pb := fun h => by
    have := @hinj 0 1 (by simp [h]); exact absurd this (by decide)
  have hac : pa ≠ pc := fun h => by
    have := @hinj 0 2 (by simp [h]); exact absurd this (by decide)
  have hbc : pb ≠ pc := fun h => by
    have := @hinj 1 2 (by simp [h]); exact absurd this (by decide)
  have hNb : ⟪N, pb⟫ = ⟪N, pa⟫ := by
    have := inner_cross_left (pb - pa) (pc - pa); rw [← hN, inner_sub_right] at this; linarith
  have hNc : ⟪N, pc⟫ = ⟪N, pa⟫ := by
    have := inner_cross_right (pb - pa) (pc - pa); rw [← hN, inner_sub_right] at this; linarith
  have hWN : ∀ w ∈ ({pa, pb, pc} : Finset ℝ³), ⟪N, w⟫ = ⟪N, pa⟫ := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl
    · rfl
    · exact hNb
    · exact hNc
  have hpa_b : pa ∉ ({pb, pc} : Finset ℝ³) := by simp [hab, hac]
  have hpb_c : pb ∉ ({pc} : Finset ℝ³) := by simp [hbc]
  have hsum : ∀ g : ℝ³ → ℝ, ∑ w ∈ ({pa, pb, pc} : Finset ℝ³), g w = g pa + g pb + g pc := by
    intro g; rw [Finset.sum_insert hpa_b, Finset.sum_insert hpb_c, Finset.sum_singleton,
      add_assoc]
  have hsumv : ∀ g : ℝ³ → ℝ, ∑ w ∈ ({pa, pb, pc} : Finset ℝ³), g w • w =
      g pa • pa + g pb • pb + g pc • pc := by
    intro g; rw [Finset.sum_insert hpa_b, Finset.sum_insert hpb_c, Finset.sum_singleton,
      add_assoc]
  refine isRupert_of_crossing V {pa, pb, pc}
    (fun w hw => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl | rfl <;> assumption)
    N ⟪N, pa⟫ hWN (by simp) (by simp) (by simp) hind u hNu0 ?_
  intro v hv hvW
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hvW
  obtain ⟨h1, h2, h3⟩ := hvW
  obtain ⟨A, B, C, rfl, n1, n2, n3⟩ := hV v hv h1 h2 h3
  obtain ⟨τ, hτ⟩ : ∃ τ : ℝ, τ = (1 - A - B - C) / S := ⟨_, rfl⟩
  obtain ⟨ma, hma⟩ : ∃ m : ℝ, m = A + τ * da := ⟨_, rfl⟩
  obtain ⟨mb, hmb⟩ : ∃ m : ℝ, m = B + τ * db := ⟨_, rfl⟩
  obtain ⟨mc, hmc⟩ : ∃ m : ℝ, m = C + τ * dc := ⟨_, rfl⟩
  have pa' : 0 < ma := by
    have e : ma = (A * (db + dc) + da * (1 - B - C)) / S := by
      rw [hma, hτ, hS_eq]; field_simp; ring
    rw [e]; exact div_pos n1 hS0
  have pb' : 0 < mb := by
    have e : mb = (B * (da + dc) + db * (1 - A - C)) / S := by
      rw [hmb, hτ, hS_eq]; field_simp; ring
    rw [e]; exact div_pos n2 hS0
  have pc' : 0 < mc := by
    have e : mc = (C * (da + db) + dc * (1 - A - B)) / S := by
      rw [hmc, hτ, hS_eq]; field_simp; ring
    rw [e]; exact div_pos n3 hS0
  have hm1 : 1 = ma + mb + mc := by
    rw [hma, hmb, hmc, hτ, hS_eq]; field_simp; ring
  refine ⟨τ, fun w => if w = pa then ma else if w = pb then mb else mc, ?_, ?_, ?_⟩
  · intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl
    · simp only [ite_true]; exact pa'
    · simp only [Ne.symm hab, ite_true, ite_false]; exact pb'
    · simp only [Ne.symm hac, Ne.symm hbc, ite_false]; exact pc'
  · rw [hsum]
    simp only [ite_true, Ne.symm hab, Ne.symm hac, Ne.symm hbc, ite_false]
    linarith
  · rw [hsumv]
    simp only [ite_true, Ne.symm hab, Ne.symm hac, Ne.symm hbc, ite_false]
    rw [hu, hma, hmb, hmc]
    rw [hma, hmb, hmc] at hm1
    linear_combination (norm := module) hm1 • o

/-- **Lemma CV (corner view) in a frame.**  If `1 + ω_ac, 1 + ω_bc, 1 + ω_ab > 0` and `Δ < 0`,
then along the oblique direction `((1 + ω_ac)(1 + ω_ab), (1 + ω_bc)(1 + ω_ab), (1 + ω_ac)(1 + ω_bc))`
from `o`, every other vertex projects strictly inside triangle `pa pb pc`. -/
theorem isRupert_cornerView_frame (V : Finset ℝ³) (o pa pb pc : ℝ³)
    (ha : pa ∈ V) (hb : pb ∈ V) (hc : pc ∈ V)
    (hD : vol3 (pa - o) (pb - o) (pc - o) ≠ 0) {wac wbc wab : ℝ}
    (h1 : 0 < 1 + wac) (h2 : 0 < 1 + wbc) (h3 : 0 < 1 + wab)
    (hΔ : wac * wbc * wab - wac - wbc - wab - 2 < 0)
    (hV : ∀ v ∈ V, v ≠ pa → v ≠ pb → v ≠ pc → v = o ∨ ∃ A B C : ℝ,
      v = o + A • (pa - o) + B • (pb - o) + C • (pc - o) ∧ 0 < A ∧ 0 < B ∧
      0 < C ∧ B + C - wbc * A ≤ 1 ∧ A + C - wac * B ≤ 1 ∧
      A + B - wab * C ≤ 1) :
    IsRupert V := by
  set da := (1 + wac) * (1 + wab)
  set db := (1 + wbc) * (1 + wab)
  set dc := (1 + wac) * (1 + wbc)
  have hda : 0 < da := mul_pos h1 h3
  have hdb : 0 < db := mul_pos h2 h3
  have hdc : 0 < dc := mul_pos h1 h2
  have hnΔ : 0 < -(wac * wbc * wab - wac - wbc - wab - 2) := neg_pos.mpr hΔ
  refine isRupert_obliqueView_frame V o pa pb pc ha hb hc hD (da := da) (db := db) (dc := dc)
    (by linarith) ?_
  intro v hv hpa hpb hpc
  rcases hV v hv hpa hpb hpc with rfl | ⟨A, B, C, rfl, hA, hB, hC, s1, s2, s3⟩
  · refine ⟨0, 0, 0, by simp, ?_, ?_, ?_⟩ <;> linarith
  · refine ⟨A, B, C, rfl, ?_, ?_, ?_⟩
    · have hid : A * (db + dc) + da * (1 - B - C) =
          -(wac * wbc * wab - wac - wbc - wab - 2) * A + da * (1 - (B + C - wbc * A)) := by
        simp only [da, db, dc]; ring
      rw [hid]
      nlinarith [mul_pos hnΔ hA, mul_nonneg hda.le (sub_nonneg.mpr s1)]
    · have hid : B * (da + dc) + db * (1 - A - C) =
          -(wac * wbc * wab - wac - wbc - wab - 2) * B + db * (1 - (A + C - wac * B)) := by
        simp only [da, db, dc]; ring
      rw [hid]
      nlinarith [mul_pos hnΔ hB, mul_nonneg hdb.le (sub_nonneg.mpr s2)]
    · have hid : C * (da + db) + dc * (1 - A - B) =
          -(wac * wbc * wab - wac - wbc - wab - 2) * C + dc * (1 - (A + B - wab * C)) := by
        simp only [da, db, dc]; ring
      rw [hid]
      nlinarith [mul_pos hnΔ hC, mul_nonneg hdc.le (sub_nonneg.mpr s3)]

end Minimality

end
