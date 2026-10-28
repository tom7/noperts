module

public import Minimality.Type08S.G3_Limit
public import Minimality.Type08S.G4p
public import Minimality.Type08S.G5a
public import Minimality.Type08S.G6Z
public import Minimality.Generic.LimitSeq
public import Minimality.Generic.TwoTie
public import Minimality.Type16Metric
public import Minimality.CaseC18M
public import Minimality.EdgeClassD

@[expose] public section

set_option autoImplicit true

/-!
# Group G3': the limit theorem for type 08, weaker HDN hypothesis (phase 1: statements)

Plan: `../consolidation.md` §2, §4.2; generic layer `genlean/LimitSeq.lean` (L-SEQ) and
`genlean/TwoTie.lean` (L-2T).  Replaces `G3_Limit.isRupert_type08_limit_norm`; keeps `Named08`,
`Touch` from `G3_Limit`.

Conclusion: **Rupert, or an HDN at the view of a single-circle closing** (N2's `K_c`, T4's `K_b`,
`K_2`), not `NoHDNAt` at all 18 named views.  The closings realized on both face circles (N2's
`K_{a'}`, Q) are closed by A(U) at the limit, whatever the HDNs (consolidation §1.5 (1)).

Index conventions: `pts08 a a' b b' c c' d = ![a,a',b,b',c,c',d]` (indices 0..6).
N2 (view `c - a'`): `K_c = (c, b, c', b')`, `K_{a'} = (a', b, c', b')`.
T4 (view `b - d`): `K_b = (b, c', b', c)`, `K_2 = K_d = (d, c', b', c)`.
Q (view `b - d`, CHECK): `K_d = (d, a, b', c)` (the face `Q_ac`).
-/

set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

/-! ### The seven points as a shape; the tests -/

def pts08 (a a' b b' c c' d : ℝ³) : Fin 7 → ℝ³ := ![a, a', b, b', c, c', d]

theorem image_pts08 (a a' b b' c c' d : ℝ³) :
    univ.image (pts08 a a' b b' c c' d) = insert d ({a, a', b, b', c, c'} : Finset ℝ³) := by
  ext p; simp [pts08, Fin.exists_fin_succ]; tauto

/-- Closings realized on one face circle only (HDN matters): N2 `K_c`, T4 `K_b`, `K_2`. -/
def SC08 : Set (Fin 3 × Bool × Bool) := {t | t.1 = 0 ∧ t.2.2 = true ∨ t.1 = 1}





/-- The type-08 shape in the frame `o; E₁, E₂, E₃` (culJ normal form, `d = o`, `a = o + E₁`, `b = o + E₂`,
`c = o + E₃`), with `θ = (α₁, β₁, α₄, γ₄, β₆, γ₆)`:
`c' = o + α₁E₁ + β₁E₂`, `b' = o + α₄E₁ + γ₄E₃`, `a' = o + β₆E₂ + γ₆E₃`. -/
noncomputable def nfShape08 (o E₁ E₂ E₃ : ℝ³) (θ : Fin 6 → ℝ) : Fin 7 → ℝ³ :=
  ![o + E₁, o + θ 4 • E₂ + θ 5 • E₃, o + E₂, o + θ 2 • E₁ + θ 3 • E₃, o + E₃,
    o + θ 0 • E₁ + θ 1 • E₂, o]

/-- The coordinates of the seven points in the frame. -/
def cp08 (θ : Fin 6 → ℝ) : Fin 7 → (Fin 3 → ℝ) :=
  ![![1, 0, 0], ![0, θ 4, θ 5], ![0, 1, 0], ![θ 2, 0, θ 3], ![0, 0, 1], ![θ 0, θ 1, 0], ![0, 0, 0]]

/-- Orientation of the tetrahedron `P Q R W` in coordinates. -/
def cdet (P Q R W : Fin 3 → ℝ) : ℝ :=
  ((Q 1 - P 1) * (R 2 - P 2) - (Q 2 - P 2) * (R 1 - P 1)) * (W 0 - P 0) +
  ((Q 2 - P 2) * (R 0 - P 0) - (Q 0 - P 0) * (R 2 - P 2)) * (W 1 - P 1) +
  ((Q 0 - P 0) * (R 1 - P 1) - (Q 1 - P 1) * (R 0 - P 0)) * (W 2 - P 2)

/-- `cdet` of the points `i j k w` of the normal form. -/
def fc08 (θ : Fin 6 → ℝ) (i j k w : Fin 7) : ℝ := cdet (cp08 θ i) (cp08 θ j) (cp08 θ k) (cp08 θ w)

/-- The Gale quantities of the normal form (up to the common factor `μ`): `κ_a = μ Wa`, `κ_b = μ Wb`,
`κ_c = μ Wc`, `[b c] = μ WU`; they are polynomials in the dual coordinates `ν`. -/
def gWa (θ : Fin 6 → ℝ) : ℝ := θ 2 * (1 - θ 0 - θ 1) - θ 0 * (1 - θ 2 - θ 3)
def gWb (θ : Fin 6 → ℝ) : ℝ := θ 1 * (1 - θ 4 - θ 5) - θ 4 * (1 - θ 0 - θ 1)
def gWc (θ : Fin 6 → ℝ) : ℝ := θ 5 * (1 - θ 2 - θ 3) - θ 3 * (1 - θ 4 - θ 5)
def gWU (θ : Fin 6 → ℝ) : ℝ := θ 4 * θ 3 * (1 - θ 0 - θ 1) + θ 1 * θ 5 * (1 - θ 2 - θ 3) -
  θ 1 * θ 3 * (1 - θ 4 - θ 5)

/-- The region inequalities of type 08 in the used labelling, as 24 positive quantities of `θ`:
0-5 coordinates of the cap quadrilaterals (`α, β > 0`), 6-8 their convexity (`α + β > 1`), 9-11 the
Gale signs (`κ_a, κ_b > 0`, `κ_c ≠ 0`, `[bc] < 0` up to the common factor), 12-23 the four
facets `ab'c'`, `a'bc'`, `a'b'c`, `a'b'c'` (each other vertex on the side of `d`). -/
def ineq08 (θ : Fin 6 → ℝ) : Fin 24 → ℝ :=
  ![θ 0, θ 1, θ 2, θ 3, θ 4, θ 5, θ 0 + θ 1 - 1, θ 2 + θ 3 - 1, θ 4 + θ 5 - 1,
    -(gWa θ * gWU θ), -(gWb θ * gWU θ), gWc θ ^ 2,
    fc08 θ 0 3 5 1 * fc08 θ 0 3 5 6, fc08 θ 0 3 5 2 * fc08 θ 0 3 5 6, fc08 θ 0 3 5 4 * fc08 θ 0 3 5 6,
    fc08 θ 1 2 5 0 * fc08 θ 1 2 5 6, fc08 θ 1 2 5 3 * fc08 θ 1 2 5 6, fc08 θ 1 2 5 4 * fc08 θ 1 2 5 6,
    fc08 θ 1 3 4 0 * fc08 θ 1 3 4 6, fc08 θ 1 3 4 2 * fc08 θ 1 3 4 6, fc08 θ 1 3 4 5 * fc08 θ 1 3 4 6,
    fc08 θ 1 3 5 0 * fc08 θ 1 3 5 6, fc08 θ 1 3 5 2 * fc08 θ 1 3 5 6, fc08 θ 1 3 5 4 * fc08 θ 1 3 5 6]

/-- Genericity: the special-position hypersurfaces `T` (`γ₆ = 1`), `T'` (`α₁ = 1`), `α₄ = 1`, `α₁ = α₄`,
`β₁ = γ₄`, `β₆ = 1` (the factors collected so far; B1 may append more: only `genPoly08_ne_zero` matters). -/
noncomputable def genPoly08 : MvPolynomial (Fin 6) ℝ :=
  (MvPolynomial.X 5 - 1) * (MvPolynomial.X 0 - 1) * (MvPolynomial.X 2 - 1) *
    (MvPolynomial.X 0 - MvPolynomial.X 2) * (MvPolynomial.X 1 - MvPolynomial.X 3) *
    (MvPolynomial.X 4 - 1)

theorem genPoly08_ne_zero : genPoly08 ≠ 0 := by
  intro h
  have := congrArg (MvPolynomial.eval ![2, 3, 5, 7, 11, 13]) h
  simp [genPoly08] at this
  norm_num at this

/-- Every point of the normal form in the frame. -/
theorem nf08_coord (o E₁ E₂ E₃ : ℝ³) (θ : Fin 6 → ℝ) (i : Fin 7) :
    nfShape08 o E₁ E₂ E₃ θ i = o + cp08 θ i 0 • E₁ + cp08 θ i 1 • E₂ + cp08 θ i 2 • E₃ := by
  fin_cases i <;> simp [nfShape08, cp08]

theorem det3_frame08 (o E₁ E₂ E₃ : ℝ³) (P Q R W : Fin 3 → ℝ) :
    det3 ((o + Q 0 • E₁ + Q 1 • E₂ + Q 2 • E₃) - (o + P 0 • E₁ + P 1 • E₂ + P 2 • E₃))
      ((o + R 0 • E₁ + R 1 • E₂ + R 2 • E₃) - (o + P 0 • E₁ + P 1 • E₂ + P 2 • E₃))
      ((o + W 0 • E₁ + W 1 • E₂ + W 2 • E₃) - (o + P 0 • E₁ + P 1 • E₂ + P 2 • E₃)) =
    det3 E₁ E₂ E₃ * cdet P Q R W := by
  simp only [det3_expand, cdet, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  ring

theorem det3_nf08 (o E₁ E₂ E₃ : ℝ³) (θ : Fin 6 → ℝ) (i j k w : Fin 7) :
    det3 (nfShape08 o E₁ E₂ E₃ θ j - nfShape08 o E₁ E₂ E₃ θ i)
      (nfShape08 o E₁ E₂ E₃ θ k - nfShape08 o E₁ E₂ E₃ θ i)
      (nfShape08 o E₁ E₂ E₃ θ w - nfShape08 o E₁ E₂ E₃ θ i) =
    det3 E₁ E₂ E₃ * fc08 θ i j k w := by
  simp only [nf08_coord, fc08]; exact det3_frame08 o E₁ E₂ E₃ _ _ _ _

theorem mapShape_nfShape08 (L : ℝ³ →L[ℝ] ℝ³) (o E₁ E₂ E₃ : ℝ³) (θ : Fin 6 → ℝ) :
    mapShape L (nfShape08 o E₁ E₂ E₃ θ) = nfShape08 (L o) (L E₁) (L E₂) (L E₃) θ := by
  funext i
  simp only [mapShape, nf08_coord, map_add, map_smul]

/-! ### Facet functions and orientation -/

theorem facet_prop08 {V : Finset ℝ³} {P Q R : ℝ³} (F : FacetFn V P Q R) (v w : ℝ³) :
    F.f w * det3 (Q - P) (R - P) (v - P) = F.f v * det3 (Q - P) (R - P) (w - P) := by
  have hx : ⟪F.N, Q - P⟫ = 0 := by rw [← F.hN, F.hQ, F.hP]; ring
  have hy : ⟪F.N, R - P⟫ = 0 := by rw [← F.hN, F.hR, F.hP]; ring
  have hw : F.f w = ⟪F.N, w - P⟫ := by rw [← F.hN, F.hP]; ring
  have hv : F.f v = ⟪F.N, v - P⟫ := by rw [← F.hN, F.hP]; ring
  rw [hw, hv]
  simp only [det3_expand, PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, conj_trivial,
    PiLp.sub_apply] at hx hy ⊢
  linear_combination (((w 1 - P 1) * (R 2 - P 2) - (w 2 - P 2) * (R 1 - P 1)) * (v 0 - P 0) + ((w 2 - P 2) * (R 0 - P 0) - (w 0 - P 0) * (R 2 - P 2)) * (v 1 - P 1) + ((w 0 - P 0) * (R 1 - P 1) - (w 1 - P 1) * (R 0 - P 0)) * (v 2 - P 2)) * hx + (((Q 1 - P 1) * (w 2 - P 2) - (Q 2 - P 2) * (w 1 - P 1)) * (v 0 - P 0) + ((Q 2 - P 2) * (w 0 - P 0) - (Q 0 - P 0) * (w 2 - P 2)) * (v 1 - P 1) + ((Q 0 - P 0) * (w 1 - P 1) - (Q 1 - P 1) * (w 0 - P 0)) * (v 2 - P 2)) * hy

theorem facet_sign08 {V : Finset ℝ³} {P Q R : ℝ³} (F : FacetFn V P Q R) {v w : ℝ³}
    (hv : F.f v < 0) (hw : F.f w < 0) (hD : det3 (Q - P) (R - P) (v - P) ≠ 0) :
    0 < det3 (Q - P) (R - P) (v - P) * det3 (Q - P) (R - P) (w - P) := by
  have h := facet_prop08 F v w
  have hp : 0 < F.f v * F.f w := mul_pos_of_neg_of_neg hv hw
  have hD2 : 0 < det3 (Q - P) (R - P) (v - P) ^ 2 := by positivity
  have : F.f v * (det3 (Q - P) (R - P) (v - P) * det3 (Q - P) (R - P) (w - P)) =
      F.f w * det3 (Q - P) (R - P) (v - P) ^ 2 := by
    linear_combination (det3 (Q - P) (R - P) (v - P)) * h.symm
  by_contra hc
  push_neg at hc
  nlinarith [mul_nonneg_of_nonpos_of_nonpos hv.le hc, mul_pos_of_neg_of_neg hv hw]

/-! ### Gale brackets in the normal form -/

theorem coef_zero08 {w u v : ℝ³} (hd : det3 w u v ≠ 0) {x y z : ℝ}
    (h : x • w + y • u + z • v = 0) : x = 0 ∧ y = 0 ∧ z = 0 := by
  by_contra hn
  exact hd (det3_eq_zero_of_lin h hn)

theorem dep_rel08 {a a' b b' c c' d : ℝ³} {l : ℝ³ → ℝ} (hl : IsDep a a' b b' c c' l)
    {p q r s t u : ℝ} (hdet : det3 (a - d) (b - d) (c - d) ≠ 0)
    (hc' : c' = d + p • (a - d) + q • (b - d)) (hb' : b' = d + r • (a - d) + s • (c - d))
    (ha' : a' = d + t • (b - d) + u • (c - d)) :
    l a = -r * l b' - p * l c' ∧ l b = -t * l a' - q * l c' ∧ l c = -u * l a' - s * l b' ∧
    (1 - t - u) * l a' + (1 - r - s) * l b' + (1 - p - q) * l c' = 0 := by
  have h0 : (l a + r * l b' + p * l c') • (a - d) + (l b + t * l a' + q * l c') • (b - d) +
      (l c + u * l a' + s * l b') • (c - d) = 0 := by
    have hv := hl.vsum
    have hs := hl.sum
    have e : l a • (a - d) + l a' • (a' - d) + l b • (b - d) + l b' • (b' - d) + l c • (c - d) +
        l c' • (c' - d) = 0 := by
      have : l a • (a - d) + l a' • (a' - d) + l b • (b - d) + l b' • (b' - d) + l c • (c - d) +
        l c' • (c' - d) = (l a • a + l a' • a' + l b • b + l b' • b' + l c • c + l c' • c') -
          (l a + l a' + l b + l b' + l c + l c') • d := by
        simp only [smul_sub, add_smul]; abel
      rw [this, hv, hs]; simp
    have ha'd : a' - d = t • (b - d) + u • (c - d) := by rw [ha']; abel
    have hb'd : b' - d = r • (a - d) + s • (c - d) := by rw [hb']; abel
    have hc'd : c' - d = p • (a - d) + q • (b - d) := by rw [hc']; abel
    rw [ha'd, hb'd, hc'd] at e
    rw [← e]
    module
  obtain ⟨h1, h2, h3⟩ := coef_zero08 hdet h0
  refine ⟨by linarith, by linarith, by linarith, ?_⟩
  have := hl.sum
  nlinarith [this, h1, h2, h3]

theorem gale_nf08 {a a' b b' c c' d : ℝ³} (G : GaleData a a' b b' c c')
    {p q r s t u : ℝ} (hdet : det3 (a - d) (b - d) (c - d) ≠ 0)
    (hc' : c' = d + p • (a - d) + q • (b - d)) (hb' : b' = d + r • (a - d) + s • (c - d))
    (ha' : a' = d + t • (b - d) + u • (c - d)) (hνc : 1 - p - q ≠ 0) :
    ∃ μ : ℝ, galeD G.l G.m a a' = μ * gWa ![p, q, r, s, t, u] ∧
      galeD G.l G.m b b' = μ * gWb ![p, q, r, s, t, u] ∧
      galeD G.l G.m c c' = μ * gWc ![p, q, r, s, t, u] ∧
      galeD G.l G.m b c = μ * gWU ![p, q, r, s, t, u] := by
  obtain ⟨la, lb, lc, ls⟩ := dep_rel08 G.hl hdet hc' hb' ha'
  obtain ⟨ma, mb, mc, ms⟩ := dep_rel08 G.hm hdet hc' hb' ha'
  set A1 := G.l a' * G.m b' - G.m a' * G.l b' with hA1
  set B1 := G.l b' * G.m c' - G.m b' * G.l c' with hB1
  set C1 := G.l c' * G.m a' - G.m c' * G.l a' with hC1
  obtain ⟨μ, hμ⟩ : ∃ μ, μ * (1 - p - q) = A1 := ⟨A1 / (1 - p - q), div_mul_cancel₀ _ hνc⟩
  have hB : B1 * (1 - p - q) = (1 - t - u) * A1 := by
    rw [hB1, hA1]
    linear_combination (G.l b') * ms - (G.m b') * ls
  have hC : C1 * (1 - p - q) = (1 - r - s) * A1 := by
    rw [hC1, hA1]
    linear_combination (G.m a') * ls - (G.l a') * ms
  have hB' : B1 = μ * (1 - t - u) := mul_right_cancel₀ hνc (by linear_combination hB - (1 - t - u) * hμ)
  have hC' : C1 = μ * (1 - r - s) := mul_right_cancel₀ hνc (by linear_combination hC - (1 - r - s) * hμ)
  have hA' : A1 = μ * (1 - p - q) := hμ.symm
  refine ⟨μ, ?_, ?_, ?_, ?_⟩
  · have e : galeD G.l G.m a a' = r * A1 - p * C1 := by
      unfold galeD; rw [la, ma, hA1, hC1]; ring
    rw [e, hA', hC']; simp [gWa]; ring
  · have e : galeD G.l G.m b b' = -t * A1 + q * B1 := by
      unfold galeD; rw [lb, mb, hA1, hB1]; ring
    rw [e, hA', hB']; simp [gWb]; ring
  · have e : galeD G.l G.m c c' = u * C1 - s * B1 := by
      unfold galeD; rw [lc, mc, hC1, hB1]; ring
    rw [e, hC', hB']; simp [gWc]; ring
  · have e : galeD G.l G.m b c = t * s * A1 + q * u * C1 - q * s * B1 := by
      unfold galeD; rw [lb, mb, lc, mc, hA1, hB1, hC1]; ring
    rw [e, hA', hB', hC']; simp [gWU]; ring

/-! ### The normal form of a `Norm08` shape -/

macro "ne_tac" : tactic => `(tactic| first | assumption | (apply Ne.symm; assumption))


theorem fc08_d (θ : Fin 6 → ℝ) :
    fc08 θ 0 3 5 6 = θ 3 * θ 1 ∧ fc08 θ 1 2 5 6 = θ 0 * θ 5 ∧ fc08 θ 1 3 4 6 = θ 2 * θ 4 ∧
      fc08 θ 1 3 5 6 = -(θ 4 * θ 3 * θ 0 + θ 5 * θ 2 * θ 1) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [fc08, cdet, cp08] <;> ring

theorem fac08 {a a' b b' c c' d : ℝ³} {θ : Fin 6 → ℝ} {o E₁ E₂ E₃ : ℝ³}
    (hE : det3 E₁ E₂ E₃ ≠ 0)
    (hpts : pts08 a a' b b' c c' d = nfShape08 o E₁ E₂ E₃ θ)
    {V : Finset ℝ³} {P Q R : ℝ³} (F : FacetFn V P Q R) (i j k w : Fin 7)
    (hP : P = pts08 a a' b b' c c' d i) (hQ : Q = pts08 a a' b b' c c' d j)
    (hR : R = pts08 a a' b b' c c' d k)
    (hv : F.f (pts08 a a' b b' c c' d 6) < 0) (hw : F.f (pts08 a a' b b' c c' d w) < 0)
    (hne : fc08 θ i j k 6 ≠ 0) : 0 < fc08 θ i j k w * fc08 θ i j k 6 := by
  have key : ∀ w, det3 (Q - P) (R - P) (pts08 a a' b b' c c' d w - P) = det3 E₁ E₂ E₃ * fc08 θ i j k w := by
    intro w
    rw [hP, hQ, hR, hpts]
    exact det3_nf08 o E₁ E₂ E₃ θ i j k w
  have h := facet_sign08 F hv hw (by rw [key]; exact mul_ne_zero hE hne)
  rw [key, key] at h
  have hsq : 0 < det3 E₁ E₂ E₃ ^ 2 := by positivity
  have e : det3 E₁ E₂ E₃ * fc08 θ i j k 6 * (det3 E₁ E₂ E₃ * fc08 θ i j k w) =
      det3 E₁ E₂ E₃ ^ 2 * (fc08 θ i j k w * fc08 θ i j k 6) := by ring
  rw [e] at h
  exact (mul_pos_iff_of_pos_left hsq).mp h

/-- Every `Norm08` shape is a frame-image of `nfShape08` with inequalities holding. -/
theorem exists_nf08 {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) :
    ∃ (o E₁ E₂ E₃ : ℝ³) (θ : Fin 6 → ℝ), det3 E₁ E₂ E₃ ≠ 0 ∧ (∀ k, 0 < ineq08 θ k) ∧
      pts08 a a' b b' c c' d = nfShape08 o E₁ E₂ E₃ θ := by
  have hd := N.hd
  have hdet : det3 (a - d) (b - d) (c - d) ≠ 0 := by
    have := hd.det_Qac_ne
    intro h; apply this
    simp only [det3_expand, PiLp.sub_apply] at h ⊢
    linarith
  obtain ⟨p, q, hp, hq, hpq, hc'⟩ := hd.Qab_coords
  obtain ⟨r, s, hr, hs, hrs, hb'⟩ := hd.Qac_coords
  obtain ⟨t, u, ht, hu, htu, ha'⟩ := hd.Qbc_coords
  have hpts : pts08 a a' b b' c c' d = nfShape08 d (a - d) (b - d) (c - d) ![p, q, r, s, t, u] := by
    funext i
    fin_cases i <;> simp [pts08, nfShape08]
    all_goals assumption
  refine ⟨d, a - d, b - d, c - d, ![p, q, r, s, t, u], hdet, ?_, hpts⟩
  have hF := N.F
  have hnd := N.F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨haa', hab, hab', hac, hac'⟩, ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩,
    ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd
  obtain ⟨μ, h1, h2, h3, h4⟩ := gale_nf08 N.G hdet hc' hb' ha' (by linarith)
  have hκa := N.hκa; have hκb := N.hκb; have hκc := N.hκc; have hU := N.hU
  rw [h1] at hκa; rw [h2] at hκb; rw [h3] at hκc; rw [h4] at hU
  have hμ : μ ≠ 0 := by rintro rfl; simp at hκa
  have hμ2 : 0 < μ ^ 2 := by positivity
  have hWc : gWc ![p, q, r, s, t, u] ≠ 0 := by intro h; rw [h] at hκc; simp at hκc
  have hE := hdet
  obtain ⟨f1, f2, f3, f4⟩ := fc08_d ![p, q, r, s, t, u]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Matrix.head_cons] at f1 f2 f3 f4
  have n1 : fc08 ![p, q, r, s, t, u] 0 3 5 6 ≠ 0 := by rw [f1]; positivity
  have n2 : fc08 ![p, q, r, s, t, u] 1 2 5 6 ≠ 0 := by rw [f2]; positivity
  have n3 : fc08 ![p, q, r, s, t, u] 1 3 4 6 ≠ 0 := by rw [f3]; positivity
  have n4 : fc08 ![p, q, r, s, t, u] 1 3 5 6 ≠ 0 := by
    rw [f4]; have : 0 < t * s * p + u * r * q := by positivity
    linarith
  have g12 := fac08 hdet hpts N.F.ab'c' 0 3 5 1 rfl rfl rfl hd.ab'c' (N.F.ab'c'.neg a' (by simp) (by ne_tac) (by ne_tac) (by ne_tac)) n1
  have g13 := fac08 hdet hpts N.F.ab'c' 0 3 5 2 rfl rfl rfl hd.ab'c' (N.F.ab'c'.neg b (by simp) (by ne_tac) (by ne_tac) (by ne_tac)) n1
  have g14 := fac08 hdet hpts N.F.ab'c' 0 3 5 4 rfl rfl rfl hd.ab'c' (N.F.ab'c'.neg c (by simp) (by ne_tac) (by ne_tac) (by ne_tac)) n1
  have g15 := fac08 hdet hpts N.F.a'bc' 1 2 5 0 rfl rfl rfl hd.a'bc' (N.F.a'bc'.neg a (by simp) (by ne_tac) (by ne_tac) (by ne_tac)) n2
  have g16 := fac08 hdet hpts N.F.a'bc' 1 2 5 3 rfl rfl rfl hd.a'bc' (N.F.a'bc'.neg b' (by simp) (by ne_tac) (by ne_tac) (by ne_tac)) n2
  have g17 := fac08 hdet hpts N.F.a'bc' 1 2 5 4 rfl rfl rfl hd.a'bc' (N.F.a'bc'.neg c (by simp) (by ne_tac) (by ne_tac) (by ne_tac)) n2
  have g18 := fac08 hdet hpts N.F.a'b'c 1 3 4 0 rfl rfl rfl hd.a'b'c (N.F.a'b'c.neg a (by simp) (by ne_tac) (by ne_tac) (by ne_tac)) n3
  have g19 := fac08 hdet hpts N.F.a'b'c 1 3 4 2 rfl rfl rfl hd.a'b'c (N.F.a'b'c.neg b (by simp) (by ne_tac) (by ne_tac) (by ne_tac)) n3
  have g20 := fac08 hdet hpts N.F.a'b'c 1 3 4 5 rfl rfl rfl hd.a'b'c (N.F.a'b'c.neg c' (by simp) (by ne_tac) (by ne_tac) (by ne_tac)) n3
  have g21 := fac08 hdet hpts N.F.a'b'c' 1 3 5 0 rfl rfl rfl hd.a'b'c' (N.F.a'b'c'.neg a (by simp) (by ne_tac) (by ne_tac) (by ne_tac)) n4
  have g22 := fac08 hdet hpts N.F.a'b'c' 1 3 5 2 rfl rfl rfl hd.a'b'c' (N.F.a'b'c'.neg b (by simp) (by ne_tac) (by ne_tac) (by ne_tac)) n4
  have g23 := fac08 hdet hpts N.F.a'b'c' 1 3 5 4 rfl rfl rfl hd.a'b'c' (N.F.a'b'c'.neg c (by simp) (by ne_tac) (by ne_tac) (by ne_tac)) n4
  have gA : 0 < -(gWa ![p, q, r, s, t, u] * gWU ![p, q, r, s, t, u]) := by
    have := mul_pos hκa (neg_pos.mpr hU)
    have e : μ * gWa ![p, q, r, s, t, u] * -(μ * gWU ![p, q, r, s, t, u]) =
      μ ^ 2 * -(gWa ![p, q, r, s, t, u] * gWU ![p, q, r, s, t, u]) := by ring
    rw [e] at this
    exact (mul_pos_iff_of_pos_left hμ2).mp this
  have gB : 0 < -(gWb ![p, q, r, s, t, u] * gWU ![p, q, r, s, t, u]) := by
    have := mul_pos hκb (neg_pos.mpr hU)
    have e : μ * gWb ![p, q, r, s, t, u] * -(μ * gWU ![p, q, r, s, t, u]) =
      μ ^ 2 * -(gWb ![p, q, r, s, t, u] * gWU ![p, q, r, s, t, u]) := by ring
    rw [e] at this
    exact (mul_pos_iff_of_pos_left hμ2).mp this
  have gC : 0 < gWc ![p, q, r, s, t, u] ^ 2 := by positivity
  have h6 : 0 < p + q - 1 := by linarith
  have h7 : 0 < r + s - 1 := by linarith
  have h8 : 0 < t + u - 1 := by linarith
  intro k
  fin_cases k
  exacts [hp, hq, hr, hs, ht, hu, h6, h7, h8, gA, gB, gC, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23]

/-! ### Tests and views -/

def grp08 : Fin 3 → ViewGroup 7
  | 0 => .edge (fun y => y 4 - y 1) 4 1 2 5 3
  | 1 => .edge (fun y => y 2 - y 6) 2 6 5 3 4
  | 2 => .single (LabTest.quad (fun y => y 2 - y 6) 6 0 3 4)

def test08 (i : Fin 3) (s j : Bool) : LabTest 7 :=
  let L := (grp08 i).tests
  let T := L.getD (if j then 0 else 1) (L.getD 0 (LabTest.quad (fun _ => 0) 0 0 0 0))
  if s then T else T.neg

theorem covView_diff08 (p q : Fin 7) : CovView (fun y : Fin 7 → ℝ³ => y p - y q) := by
  refine ⟨(continuous_apply p).sub (continuous_apply q), ?_⟩
  intro L y _
  simp [mapShape]

theorem covView_neg08 {view : (Fin 7 → ℝ³) → ℝ³} (h : CovView view) : CovView (fun y => -view y) := by
  refine ⟨h.1.neg, ?_⟩
  intro L y hL
  simp [h.2 L y hL]

theorem covView_zero08 : CovView (fun _ : Fin 7 → ℝ³ => (0 : ℝ³)) :=
  ⟨continuous_const, fun L y _ => by simp⟩

theorem covView_test08 (i : Fin 3) (s j : Bool) : CovView (test08 i s j).view := by
  fin_cases i <;> cases s <;> cases j <;>
    simp [test08, grp08, ViewGroup.tests, LabTest.neg, LabTest.quad] <;>
    first | exact covView_diff08 _ _ | exact covView_neg08 (covView_diff08 _ _) | exact covView_zero08

/-! ### Convex position -/

theorem facet_aff08 {V : Finset ℝ³} {P Q R : ℝ³} (F : FacetFn V P Q R) (y z : ℝ³) (s : ℝ) :
    F.f (y + s • (z - y)) = (1 - s) * F.f y + s * F.f z := by
  have h1 := F.hN (y + s • (z - y)) y
  have h2 := F.hN z y
  have : y + s • (z - y) - y = s • (z - y) := by abel
  rw [this, inner_smul_right, ← h2] at h1
  linarith

theorem noSeg_of_aff08 {x : Fin 7 → ℝ³} (G : Fin 7 → ℝ³ → ℝ)
    (hG : ∀ m y z (s : ℝ), G m (y + s • (z - y)) = (1 - s) * G m y + s * G m z)
    (h : ∀ m w, w ≠ m → G m (x w) < G m (x m)) :
    ∀ i j m : Fin 7, x m ≠ x i → x m ≠ x j → ∀ s : ℝ, 0 < s → s < 1 →
      x m ≠ x i + s • (x j - x i) := by
  intro i j m hmi hmj s hs0 hs1 he
  have hi := h m i (fun e => hmi (by rw [e]))
  have hj := h m j (fun e => hmj (by rw [e]))
  have := hG m (x i) (x j) s
  rw [← he] at this
  nlinarith

theorem det_nf08 {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) :
    det3 (a - d) (b - d) (c - d) ≠ 0 := by
  have := N.hd.det_Qac_ne
  intro h; apply this
  simp only [det3_expand, PiLp.sub_apply] at h ⊢
  linarith

set_option maxHeartbeats 4000000 in
theorem seg08 {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) :
    let x := pts08 a a' b b' c c' d
    (∀ i j m : Fin 7, x m ≠ x i → x m ≠ x j → ∀ s : ℝ, 0 < s → s < 1 → x m ≠ x i + s • (x j - x i)) ∧
    ∃ i j l m : Fin 7, det3 (x j - x i) (x l - x i) (x m - x i) ≠ 0 := by
  intro x
  refine ⟨?_, 6, 0, 2, 4, by simpa [x, pts08] using det_nf08 N⟩
  have hd := N.hd
  have hnd := N.F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨haa', hab, hab', hac, hac'⟩, ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩,
    ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd
  have f1_0 : N.F.abc'.f a = 0 := N.F.abc'.hP
  have f1_1 : N.F.abc'.f a' < 0 := N.F.abc'.neg a' (by simp) (by ne_tac) (by ne_tac) (by ne_tac)
  have f1_2 : N.F.abc'.f b = 0 := N.F.abc'.hQ
  have f1_3 : N.F.abc'.f b' < 0 := N.F.abc'.neg b' (by simp) (by ne_tac) (by ne_tac) (by ne_tac)
  have f1_4 : N.F.abc'.f c < 0 := N.F.abc'.neg c (by simp) (by ne_tac) (by ne_tac) (by ne_tac)
  have f1_5 : N.F.abc'.f c' = 0 := N.F.abc'.hR
  have f1_6 : N.F.abc'.f d = 0 := hd.abc'
  have f2_0 : N.F.ab'c.f a = 0 := N.F.ab'c.hP
  have f2_1 : N.F.ab'c.f a' < 0 := N.F.ab'c.neg a' (by simp) (by ne_tac) (by ne_tac) (by ne_tac)
  have f2_2 : N.F.ab'c.f b < 0 := N.F.ab'c.neg b (by simp) (by ne_tac) (by ne_tac) (by ne_tac)
  have f2_3 : N.F.ab'c.f b' = 0 := N.F.ab'c.hQ
  have f2_4 : N.F.ab'c.f c = 0 := N.F.ab'c.hR
  have f2_5 : N.F.ab'c.f c' < 0 := N.F.ab'c.neg c' (by simp) (by ne_tac) (by ne_tac) (by ne_tac)
  have f2_6 : N.F.ab'c.f d = 0 := hd.ab'c
  have f3_0 : N.F.a'bc.f a < 0 := N.F.a'bc.neg a (by simp) (by ne_tac) (by ne_tac) (by ne_tac)
  have f3_1 : N.F.a'bc.f a' = 0 := N.F.a'bc.hP
  have f3_2 : N.F.a'bc.f b = 0 := N.F.a'bc.hQ
  have f3_3 : N.F.a'bc.f b' < 0 := N.F.a'bc.neg b' (by simp) (by ne_tac) (by ne_tac) (by ne_tac)
  have f3_4 : N.F.a'bc.f c = 0 := N.F.a'bc.hR
  have f3_5 : N.F.a'bc.f c' < 0 := N.F.a'bc.neg c' (by simp) (by ne_tac) (by ne_tac) (by ne_tac)
  have f3_6 : N.F.a'bc.f d = 0 := hd.a'bc
  have f4_0 : N.F.ab'c'.f a = 0 := N.F.ab'c'.hP
  have f4_1 : N.F.ab'c'.f a' < 0 := N.F.ab'c'.neg a' (by simp) (by ne_tac) (by ne_tac) (by ne_tac)
  have f4_2 : N.F.ab'c'.f b < 0 := N.F.ab'c'.neg b (by simp) (by ne_tac) (by ne_tac) (by ne_tac)
  have f4_3 : N.F.ab'c'.f b' = 0 := N.F.ab'c'.hQ
  have f4_4 : N.F.ab'c'.f c < 0 := N.F.ab'c'.neg c (by simp) (by ne_tac) (by ne_tac) (by ne_tac)
  have f4_5 : N.F.ab'c'.f c' = 0 := N.F.ab'c'.hR
  have f4_6 : N.F.ab'c'.f d < 0 := hd.ab'c'
  have f5_0 : N.F.a'bc'.f a < 0 := N.F.a'bc'.neg a (by simp) (by ne_tac) (by ne_tac) (by ne_tac)
  have f5_1 : N.F.a'bc'.f a' = 0 := N.F.a'bc'.hP
  have f5_2 : N.F.a'bc'.f b = 0 := N.F.a'bc'.hQ
  have f5_3 : N.F.a'bc'.f b' < 0 := N.F.a'bc'.neg b' (by simp) (by ne_tac) (by ne_tac) (by ne_tac)
  have f5_4 : N.F.a'bc'.f c < 0 := N.F.a'bc'.neg c (by simp) (by ne_tac) (by ne_tac) (by ne_tac)
  have f5_5 : N.F.a'bc'.f c' = 0 := N.F.a'bc'.hR
  have f5_6 : N.F.a'bc'.f d < 0 := hd.a'bc'
  have f6_0 : N.F.a'b'c.f a < 0 := N.F.a'b'c.neg a (by simp) (by ne_tac) (by ne_tac) (by ne_tac)
  have f6_1 : N.F.a'b'c.f a' = 0 := N.F.a'b'c.hP
  have f6_2 : N.F.a'b'c.f b < 0 := N.F.a'b'c.neg b (by simp) (by ne_tac) (by ne_tac) (by ne_tac)
  have f6_3 : N.F.a'b'c.f b' = 0 := N.F.a'b'c.hQ
  have f6_4 : N.F.a'b'c.f c = 0 := N.F.a'b'c.hR
  have f6_5 : N.F.a'b'c.f c' < 0 := N.F.a'b'c.neg c' (by simp) (by ne_tac) (by ne_tac) (by ne_tac)
  have f6_6 : N.F.a'b'c.f d < 0 := hd.a'b'c
  have f7_0 : N.F.a'b'c'.f a < 0 := N.F.a'b'c'.neg a (by simp) (by ne_tac) (by ne_tac) (by ne_tac)
  have f7_1 : N.F.a'b'c'.f a' = 0 := N.F.a'b'c'.hP
  have f7_2 : N.F.a'b'c'.f b < 0 := N.F.a'b'c'.neg b (by simp) (by ne_tac) (by ne_tac) (by ne_tac)
  have f7_3 : N.F.a'b'c'.f b' = 0 := N.F.a'b'c'.hQ
  have f7_4 : N.F.a'b'c'.f c < 0 := N.F.a'b'c'.neg c (by simp) (by ne_tac) (by ne_tac) (by ne_tac)
  have f7_5 : N.F.a'b'c'.f c' = 0 := N.F.a'b'c'.hR
  have f7_6 : N.F.a'b'c'.f d < 0 := hd.a'b'c'
  refine noSeg_of_aff08 (![fun y => N.F.abc'.f y + N.F.ab'c.f y + N.F.ab'c'.f y, fun y => N.F.a'bc.f y + N.F.a'bc'.f y + N.F.a'b'c.f y + N.F.a'b'c'.f y, fun y => N.F.abc'.f y + N.F.a'bc.f y + N.F.a'bc'.f y, fun y => N.F.ab'c.f y + N.F.ab'c'.f y + N.F.a'b'c.f y + N.F.a'b'c'.f y, fun y => N.F.ab'c.f y + N.F.a'bc.f y + N.F.a'b'c.f y, fun y => N.F.abc'.f y + N.F.ab'c'.f y + N.F.a'bc'.f y + N.F.a'b'c'.f y, fun y => N.F.abc'.f y + N.F.ab'c.f y + N.F.a'bc.f y]) ?_ ?_
  · intro m y z s
    fin_cases m <;> simp [facet_aff08] <;> ring
  · intro m w hw
    fin_cases m <;> fin_cases w <;> first | exact absurd rfl hw | (simp only [x, pts08]; simp; linarith)


/-- **Doubt 5 resolved:** a straddling far triple of a group is a touching (so `hnoStraddle` follows from
`¬ Touch`, no extra hypothesis).  N2: `z_b = z_c' = z_b'` along `c - a'`; T4: `z_c' = z_b' = z_c`
along `b - d`; the single group never straddles. -/
theorem straddle_touch08 {a a' b b' c c' d : ℝ³} (i : Fin 3)
    (h : (grp08 i).Straddle (pts08 a a' b b' c c' d)) : Touch a a' b b' c c' d := by
  fin_cases i
  · simp only [grp08, ViewGroup.Straddle, pts08] at h
    obtain ⟨h1, h2, -, -⟩ := h
    left
    exact ⟨h1, h2.symm⟩
  · simp only [grp08, ViewGroup.Straddle, pts08] at h
    obtain ⟨h1, h2, -, -⟩ := h
    right
    exact ⟨h2.symm, h1⟩
  · exact h.elim

/-! ### Region ⇒ `Norm08` (converse of `exists_nf08`) -/


/-- A facet function from a reference vertex: `f y = - D(ref) * D(y)` with `D y = det3 (Q-P) (R-P) (y-P)`. -/
noncomputable def mkF08 (V : Finset ℝ³) (P Q R ref : ℝ³)
    (hneg : ∀ w ∈ V, w ≠ P → w ≠ Q → w ≠ R →
      0 < det3 (Q - P) (R - P) (ref - P) * det3 (Q - P) (R - P) (w - P)) : FacetFn V P Q R where
  f := fun y => -(det3 (Q - P) (R - P) (ref - P)) * det3 (Q - P) (R - P) (y - P)
  N := -(det3 (Q - P) (R - P) (ref - P)) • cross (Q - P) (R - P)
  hN := by
    intro y z
    simp only [det3, real_inner_smul_left]
    rw [← mul_sub, ← inner_sub_right]
    congr 2; abel
  hP := by simp [det3]
  hQ := by simp only [det3_expand]; simp only [PiLp.sub_apply]; ring
  hR := by simp only [det3_expand]; simp only [PiLp.sub_apply]; ring
  neg := fun w hw h1 h2 h3 => by
    have := hneg w hw h1 h2 h3
    nlinarith

theorem prod_pos08 {S : Finset (Fin 7)} {f : Fin 7 → ℝ} {g : ℝ} (h : ∀ w ∈ S, 0 < f w * g) :
    ∀ u ∈ S, ∀ v ∈ S, 0 < f u * f v := by
  intro u hu v hv
  have h1 := h u hu
  have h2 := h v hv
  have hg : g ≠ 0 := by rintro rfl; simp at h1
  have hg2 : 0 < g ^ 2 := by positivity
  have : 0 < g ^ 2 * (f u * f v) := by nlinarith [mul_pos h1 h2]
  exact (mul_pos_iff_of_pos_left hg2).mp this

theorem fc08_coord (θ : Fin 6 → ℝ) :
    (fc08 θ 0 2 4 1 = θ 4 + θ 5 - 1 ∧ fc08 θ 0 2 4 3 = θ 2 + θ 3 - 1 ∧ fc08 θ 0 2 4 5 = θ 0 + θ 1 - 1) ∧
    (fc08 θ 0 2 5 1 = (1 - θ 0 - θ 1) * θ 5 ∧ fc08 θ 0 2 5 3 = (1 - θ 0 - θ 1) * θ 3 ∧
      fc08 θ 0 2 5 4 = (1 - θ 0 - θ 1) * 1) ∧
    (fc08 θ 0 3 4 1 = (1 - θ 2 - θ 3) * θ 4 ∧ fc08 θ 0 3 4 2 = (1 - θ 2 - θ 3) * 1 ∧
      fc08 θ 0 3 4 5 = (1 - θ 2 - θ 3) * θ 1) ∧
    (fc08 θ 1 2 4 0 = (1 - θ 4 - θ 5) * 1 ∧ fc08 θ 1 2 4 3 = (1 - θ 4 - θ 5) * θ 2 ∧
      fc08 θ 1 2 4 5 = (1 - θ 4 - θ 5) * θ 0) := by
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩ <;>
    (simp only [fc08, cdet, cp08]; simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Matrix.head_cons]; ring)

set_option maxHeartbeats 2000000 in
theorem fpos08 (θ : Fin 6 → ℝ) (hθ : ∀ k, 0 < ineq08 θ k) :
    (∀ u ∈ ({1, 3, 5} : Finset (Fin 7)), ∀ v ∈ ({1, 3, 5} : Finset (Fin 7)), 0 < fc08 θ 0 2 4 u * fc08 θ 0 2 4 v) ∧
    (∀ u ∈ ({1, 3, 4} : Finset (Fin 7)), ∀ v ∈ ({1, 3, 4} : Finset (Fin 7)), 0 < fc08 θ 0 2 5 u * fc08 θ 0 2 5 v) ∧
    (∀ u ∈ ({1, 2, 5} : Finset (Fin 7)), ∀ v ∈ ({1, 2, 5} : Finset (Fin 7)), 0 < fc08 θ 0 3 4 u * fc08 θ 0 3 4 v) ∧
    (∀ u ∈ ({1, 2, 4} : Finset (Fin 7)), ∀ v ∈ ({1, 2, 4} : Finset (Fin 7)), 0 < fc08 θ 0 3 5 u * fc08 θ 0 3 5 v) ∧
    (∀ u ∈ ({0, 3, 5} : Finset (Fin 7)), ∀ v ∈ ({0, 3, 5} : Finset (Fin 7)), 0 < fc08 θ 1 2 4 u * fc08 θ 1 2 4 v) ∧
    (∀ u ∈ ({0, 3, 4} : Finset (Fin 7)), ∀ v ∈ ({0, 3, 4} : Finset (Fin 7)), 0 < fc08 θ 1 2 5 u * fc08 θ 1 2 5 v) ∧
    (∀ u ∈ ({0, 2, 5} : Finset (Fin 7)), ∀ v ∈ ({0, 2, 5} : Finset (Fin 7)), 0 < fc08 θ 1 3 4 u * fc08 θ 1 3 4 v) ∧
    (∀ u ∈ ({0, 2, 4} : Finset (Fin 7)), ∀ v ∈ ({0, 2, 4} : Finset (Fin 7)), 0 < fc08 θ 1 3 5 u * fc08 θ 1 3 5 v) := by
  obtain ⟨⟨c1, c2, c3⟩, ⟨c4, c5, c6⟩, ⟨c7, c8, c9⟩, ⟨c10, c11, c12⟩⟩ := fc08_coord θ
  have p0 := hθ 0; have p1 := hθ 1; have p2 := hθ 2; have p3 := hθ 3; have p4 := hθ 4; have p5 := hθ 5
  have p6 : 0 < θ 0 + θ 1 - 1 := hθ 6
  have p7 : 0 < θ 2 + θ 3 - 1 := hθ 7
  have p8 : 0 < θ 4 + θ 5 - 1 := hθ 8
  simp only [ineq08, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Matrix.head_cons] at p0 p1 p2 p3 p4 p5
  have nc : (1 - θ 0 - θ 1) ≠ 0 := by intro h; linarith
  have nb : (1 - θ 2 - θ 3) ≠ 0 := by intro h; linarith
  have na : (1 - θ 4 - θ 5) ≠ 0 := by intro h; linarith
  have sc := sq_pos_of_ne_zero nc
  have sb := sq_pos_of_ne_zero nb
  have sa := sq_pos_of_ne_zero na
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine prod_pos08 (g := 1) ?_
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl <;> simp only [c1, c2, c3] <;> linarith
  · refine prod_pos08 (g := 1 - θ 0 - θ 1) ?_
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl <;> simp only [c4, c5, c6] <;> nlinarith [mul_pos sc p5, mul_pos sc p3]
  · refine prod_pos08 (g := 1 - θ 2 - θ 3) ?_
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl <;> simp only [c7, c8, c9] <;> nlinarith [mul_pos sb p4, mul_pos sb p1]
  · refine prod_pos08 (g := fc08 θ 0 3 5 6) ?_
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl
    · exact hθ 12
    · exact hθ 13
    · exact hθ 14
  · refine prod_pos08 (g := 1 - θ 4 - θ 5) ?_
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl <;> simp only [c10, c11, c12] <;> nlinarith [mul_pos sa p2, mul_pos sa p0]
  · refine prod_pos08 (g := fc08 θ 1 2 5 6) ?_
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl
    · exact hθ 15
    · exact hθ 16
    · exact hθ 17
  · refine prod_pos08 (g := fc08 θ 1 3 4 6) ?_
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl
    · exact hθ 18
    · exact hθ 19
    · exact hθ 20
  · refine prod_pos08 (g := fc08 θ 1 3 5 6) ?_
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl
    · exact hθ 21
    · exact hθ 22
    · exact hθ 23

theorem fc08_d0 (θ : Fin 6 → ℝ) :
    fc08 θ 0 2 5 6 = 0 ∧ fc08 θ 0 3 4 6 = 0 ∧ fc08 θ 1 2 4 6 = 0 ∧ fc08 θ 0 2 4 6 = -1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    (simp only [fc08, cdet, cp08]; simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Matrix.head_cons]; ring)

theorem hneg08 {o E₁ E₂ E₃ : ℝ³} (hE : det3 E₁ E₂ E₃ ≠ 0) {θ : Fin 6 → ℝ} (i j k r : Fin 7) (S : Finset (Fin 7))
    (hS : ∀ u ∈ S, ∀ v ∈ S, 0 < fc08 θ i j k u * fc08 θ i j k v) (hr : r ∈ S)
    (hcov : ∀ m : Fin 7, m.val < 6 → m ≠ i → m ≠ j → m ≠ k → m ∈ S) :
    ∀ w ∈ ({nfShape08 o E₁ E₂ E₃ θ 0, nfShape08 o E₁ E₂ E₃ θ 1, nfShape08 o E₁ E₂ E₃ θ 2,
      nfShape08 o E₁ E₂ E₃ θ 3, nfShape08 o E₁ E₂ E₃ θ 4, nfShape08 o E₁ E₂ E₃ θ 5} : Finset ℝ³),
      w ≠ nfShape08 o E₁ E₂ E₃ θ i → w ≠ nfShape08 o E₁ E₂ E₃ θ j → w ≠ nfShape08 o E₁ E₂ E₃ θ k →
      0 < det3 (nfShape08 o E₁ E₂ E₃ θ j - nfShape08 o E₁ E₂ E₃ θ i)
          (nfShape08 o E₁ E₂ E₃ θ k - nfShape08 o E₁ E₂ E₃ θ i)
          (nfShape08 o E₁ E₂ E₃ θ r - nfShape08 o E₁ E₂ E₃ θ i) *
        det3 (nfShape08 o E₁ E₂ E₃ θ j - nfShape08 o E₁ E₂ E₃ θ i)
          (nfShape08 o E₁ E₂ E₃ θ k - nfShape08 o E₁ E₂ E₃ θ i)
          (w - nfShape08 o E₁ E₂ E₃ θ i) := by
  intro w hw h1 h2 h3
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  obtain ⟨m, hm, rfl⟩ : ∃ m : Fin 7, m.val < 6 ∧ w = nfShape08 o E₁ E₂ E₃ θ m := by
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [⟨0, by decide, rfl⟩, ⟨1, by decide, rfl⟩, ⟨2, by decide, rfl⟩, ⟨3, by decide, rfl⟩,
      ⟨4, by decide, rfl⟩, ⟨5, by decide, rfl⟩]
  have hmi : m ≠ i := fun h => h1 (by rw [h])
  have hmj : m ≠ j := fun h => h2 (by rw [h])
  have hmk : m ≠ k := fun h => h3 (by rw [h])
  rw [det3_nf08, det3_nf08]
  have hsq : 0 < det3 E₁ E₂ E₃ ^ 2 := by positivity
  have := hS r hr m (hcov m hm hmi hmj hmk)
  have e : det3 E₁ E₂ E₃ * fc08 θ i j k r * (det3 E₁ E₂ E₃ * fc08 θ i j k m) =
      det3 E₁ E₂ E₃ ^ 2 * (fc08 θ i j k r * fc08 θ i j k m) := by ring
  rw [e]; positivity

theorem nfinj08 {o E₁ E₂ E₃ : ℝ³} (hE : det3 E₁ E₂ E₃ ≠ 0) {θ : Fin 6 → ℝ} (i j : Fin 7)
    (h : nfShape08 o E₁ E₂ E₃ θ i = nfShape08 o E₁ E₂ E₃ θ j) : ∀ m, cp08 θ i m = cp08 θ j m := by
  have h0 : (cp08 θ i 0 - cp08 θ j 0) • E₁ + (cp08 θ i 1 - cp08 θ j 1) • E₂ +
      (cp08 θ i 2 - cp08 θ j 2) • E₃ = 0 := by
    calc _ = nfShape08 o E₁ E₂ E₃ θ i - nfShape08 o E₁ E₂ E₃ θ j := by
          rw [nf08_coord, nf08_coord]; module
      _ = 0 := sub_eq_zero.mpr h
  obtain ⟨h1, h2, h3⟩ := coef_zero08 hE h0
  intro m
  fin_cases m
  · exact sub_eq_zero.mp h1
  · exact sub_eq_zero.mp h2
  · exact sub_eq_zero.mp h3

/-- Lookup: the value `v i` at the point `x i` (and `0` elsewhere). -/
noncomputable def lk08 (x : Fin 6 → ℝ³) (v : Fin 6 → ℝ) (y : ℝ³) : ℝ :=
  if h : ∃ i, x i = y then v h.choose else 0

theorem lk08_eq {x : Fin 6 → ℝ³} (hx : Function.Injective x) (v : Fin 6 → ℝ) (i : Fin 6) :
    lk08 x v (x i) = v i := by
  have h : ∃ j, x j = x i := ⟨i, rfl⟩
  unfold lk08
  rw [dif_pos h]
  congr 1
  exact hx h.choose_spec

/-- dependency values from `(a', b', c')` values. -/
def dv08 (θ : Fin 6 → ℝ) (X Y Z : ℝ) : Fin 6 → ℝ :=
  ![-θ 2 * Y - θ 0 * Z, X, -θ 4 * X - θ 1 * Z, Y, -θ 5 * X - θ 3 * Y, Z]

theorem dv08_sum (θ : Fin 6 → ℝ) (X Y Z : ℝ)
    (h : (1 - θ 4 - θ 5) * X + (1 - θ 2 - θ 3) * Y + (1 - θ 0 - θ 1) * Z = 0) :
    dv08 θ X Y Z 0 + dv08 θ X Y Z 1 + dv08 θ X Y Z 2 + dv08 θ X Y Z 3 + dv08 θ X Y Z 4 +
      dv08 θ X Y Z 5 = 0 := by
  simp only [dv08, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val]
  linarith

theorem dv08_vsum (o E₁ E₂ E₃ : ℝ³) (θ : Fin 6 → ℝ) (X Y Z : ℝ)
    (h : (1 - θ 4 - θ 5) * X + (1 - θ 2 - θ 3) * Y + (1 - θ 0 - θ 1) * Z = 0) :
    dv08 θ X Y Z 0 • nfShape08 o E₁ E₂ E₃ θ 0 + dv08 θ X Y Z 1 • nfShape08 o E₁ E₂ E₃ θ 1 +
      dv08 θ X Y Z 2 • nfShape08 o E₁ E₂ E₃ θ 2 + dv08 θ X Y Z 3 • nfShape08 o E₁ E₂ E₃ θ 3 +
      dv08 θ X Y Z 4 • nfShape08 o E₁ E₂ E₃ θ 4 + dv08 θ X Y Z 5 • nfShape08 o E₁ E₂ E₃ θ 5 = 0 := by
  have hs := dv08_sum θ X Y Z h
  have e : ((dv08 θ X Y Z 0 + dv08 θ X Y Z 1 + dv08 θ X Y Z 2 + dv08 θ X Y Z 3 + dv08 θ X Y Z 4 +
      dv08 θ X Y Z 5) • o) = 0 := by rw [hs, zero_smul]
  have c : ∀ i : Fin 7, nfShape08 o E₁ E₂ E₃ θ i = o + cp08 θ i 0 • E₁ + cp08 θ i 1 • E₂ + cp08 θ i 2 • E₃ :=
    nf08_coord o E₁ E₂ E₃ θ
  rw [c 0, c 1, c 2, c 3, c 4, c 5]
  simp only [dv08, cp08, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val] at e ⊢
  linear_combination (norm := module) e

theorem nf_inj6 {o E₁ E₂ E₃ : ℝ³} (hE : det3 E₁ E₂ E₃ ≠ 0) {θ : Fin 6 → ℝ}
    (hθ : ∀ k, 0 < ineq08 θ k) :
    Function.Injective (fun i : Fin 6 => nfShape08 o E₁ E₂ E₃ θ i.castSucc) := by
  have p0 := hθ 0; have p1 := hθ 1; have p2 := hθ 2; have p3 := hθ 3; have p4 := hθ 4; have p5 := hθ 5
  simp only [ineq08, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Matrix.head_cons] at p0 p1 p2 p3 p4 p5
  intro i j h
  by_contra hne
  have key := nfinj08 hE (θ := θ) i.castSucc j.castSucc h
  have h0 := key 0; have h1 := key 1; have h2 := key 2
  fin_cases i <;> fin_cases j <;> first | exact hne rfl | (revert h0 h1 h2; norm_num [cp08] <;> (intros; linarith))

/-- **Gale data of the normal form** (PLAN): the dependency space of the six octahedron points is spanned
by `l, m` with `(l a', l b', l c') = (ν_b, -ν_a, 0)`, `(m a', m b', m c') = (0, ν_c, -ν_b)`
(`ν_a = 1 - t - u`, ...), the other values from `dep_rel08`; then `κ_a = ν_b W_a`, ... (`gale_nf08`'s
computation), and the sign is fixed by swapping `l, m` if needed. -/
theorem gale_of_nf08 {o E₁ E₂ E₃ : ℝ³} (hE : det3 E₁ E₂ E₃ ≠ 0) {θ : Fin 6 → ℝ}
    (hθ : ∀ k, 0 < ineq08 θ k) :
    ∃ G : GaleData (nfShape08 o E₁ E₂ E₃ θ 0) (nfShape08 o E₁ E₂ E₃ θ 1) (nfShape08 o E₁ E₂ E₃ θ 2)
        (nfShape08 o E₁ E₂ E₃ θ 3) (nfShape08 o E₁ E₂ E₃ θ 4) (nfShape08 o E₁ E₂ E₃ θ 5),
      0 < galeD G.l G.m (nfShape08 o E₁ E₂ E₃ θ 0) (nfShape08 o E₁ E₂ E₃ θ 1) ∧
      0 < galeD G.l G.m (nfShape08 o E₁ E₂ E₃ θ 2) (nfShape08 o E₁ E₂ E₃ θ 3) ∧
      galeD G.l G.m (nfShape08 o E₁ E₂ E₃ θ 4) (nfShape08 o E₁ E₂ E₃ θ 5) ≠ 0 ∧
      galeD G.l G.m (nfShape08 o E₁ E₂ E₃ θ 2) (nfShape08 o E₁ E₂ E₃ θ 4) < 0 := by
  have hinj := nf_inj6 (o := o) hE hθ
  set xs : Fin 6 → ℝ³ := fun i => nfShape08 o E₁ E₂ E₃ θ i.castSucc with hxs
  have q6 := hθ 6; have q7 := hθ 7; have q8 := hθ 8; have q9 := hθ 9; have q10 := hθ 10; have q11 := hθ 11
  simp only [ineq08, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Matrix.head_cons]
    at q6 q7 q8 q9 q10 q11
  have hnb : 1 - θ 2 - θ 3 < 0 := by linarith
  have hnc : 1 - θ 0 - θ 1 < 0 := by linarith
  set X1 : ℝ := 1 - θ 2 - θ 3 with hX1
  -- dependencies
  have hl : ∀ (X Y Z : ℝ), (1 - θ 4 - θ 5) * X + (1 - θ 2 - θ 3) * Y + (1 - θ 0 - θ 1) * Z = 0 →
      IsDep (nfShape08 o E₁ E₂ E₃ θ 0) (nfShape08 o E₁ E₂ E₃ θ 1) (nfShape08 o E₁ E₂ E₃ θ 2)
        (nfShape08 o E₁ E₂ E₃ θ 3) (nfShape08 o E₁ E₂ E₃ θ 4) (nfShape08 o E₁ E₂ E₃ θ 5)
        (lk08 xs (dv08 θ X Y Z)) := by
    intro X Y Z h
    have e0 := lk08_eq hinj (dv08 θ X Y Z) 0; have e1 := lk08_eq hinj (dv08 θ X Y Z) 1
    have e2 := lk08_eq hinj (dv08 θ X Y Z) 2; have e3 := lk08_eq hinj (dv08 θ X Y Z) 3
    have e4 := lk08_eq hinj (dv08 θ X Y Z) 4; have e5 := lk08_eq hinj (dv08 θ X Y Z) 5
    refine ⟨?_, ?_⟩
    · change lk08 xs _ (xs 0) + lk08 xs _ (xs 1) + lk08 xs _ (xs 2) + lk08 xs _ (xs 3) +
        lk08 xs _ (xs 4) + lk08 xs _ (xs 5) = 0
      rw [e0, e1, e2, e3, e4, e5]; exact dv08_sum θ X Y Z h
    · change lk08 xs _ (xs 0) • xs 0 + lk08 xs _ (xs 1) • xs 1 + lk08 xs _ (xs 2) • xs 2 +
        lk08 xs _ (xs 3) • xs 3 + lk08 xs _ (xs 4) • xs 4 + lk08 xs _ (xs 5) • xs 5 = 0
      rw [e0, e1, e2, e3, e4, e5]; exact dv08_vsum o E₁ E₂ E₃ θ X Y Z h
  set na : ℝ := 1 - θ 4 - θ 5 with hna
  set nc : ℝ := 1 - θ 0 - θ 1 with hnc'
  have hL := hl X1 (-na) 0 (by simp only [hX1, hna]; ring)
  have hM := hl 0 nc (-X1) (by simp only [hX1, hnc']; ring)
  have hind : ∀ α β : ℝ, α * lk08 xs (dv08 θ X1 (-na) 0) (nfShape08 o E₁ E₂ E₃ θ 0) +
        β * lk08 xs (dv08 θ 0 nc (-X1)) (nfShape08 o E₁ E₂ E₃ θ 0) = 0 →
      α * lk08 xs (dv08 θ X1 (-na) 0) (nfShape08 o E₁ E₂ E₃ θ 1) +
        β * lk08 xs (dv08 θ 0 nc (-X1)) (nfShape08 o E₁ E₂ E₃ θ 1) = 0 →
      α * lk08 xs (dv08 θ X1 (-na) 0) (nfShape08 o E₁ E₂ E₃ θ 2) +
        β * lk08 xs (dv08 θ 0 nc (-X1)) (nfShape08 o E₁ E₂ E₃ θ 2) = 0 →
      α * lk08 xs (dv08 θ X1 (-na) 0) (nfShape08 o E₁ E₂ E₃ θ 3) +
        β * lk08 xs (dv08 θ 0 nc (-X1)) (nfShape08 o E₁ E₂ E₃ θ 3) = 0 →
      α * lk08 xs (dv08 θ X1 (-na) 0) (nfShape08 o E₁ E₂ E₃ θ 4) +
        β * lk08 xs (dv08 θ 0 nc (-X1)) (nfShape08 o E₁ E₂ E₃ θ 4) = 0 →
      α * lk08 xs (dv08 θ X1 (-na) 0) (nfShape08 o E₁ E₂ E₃ θ 5) +
        β * lk08 xs (dv08 θ 0 nc (-X1)) (nfShape08 o E₁ E₂ E₃ θ 5) = 0 → α = 0 ∧ β = 0 := by
    intro α β h0 h1 h2 h3 h4 h5
    have a1 := lk08_eq hinj (dv08 θ X1 (-na) 0) 1; have a5 := lk08_eq hinj (dv08 θ X1 (-na) 0) 5
    have b3 := lk08_eq hinj (dv08 θ 0 nc (-X1)) 3
    have b5 := lk08_eq hinj (dv08 θ 0 nc (-X1)) 5
    have a3 := lk08_eq hinj (dv08 θ X1 (-na) 0) 3
    have b1 := lk08_eq hinj (dv08 θ 0 nc (-X1)) 1
    change α * lk08 xs _ (xs 1) + β * lk08 xs _ (xs 1) = 0 at h1
    change α * lk08 xs _ (xs 5) + β * lk08 xs _ (xs 5) = 0 at h5
    rw [a1, b1] at h1; rw [a5, b5] at h5
    simp only [dv08, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val] at h1 h5
    have hα : α * X1 = 0 := by linarith
    have hβ : β * X1 = 0 := by linarith
    exact ⟨(mul_eq_zero.mp hα).resolve_right hnb.ne, (mul_eq_zero.mp hβ).resolve_right hnb.ne⟩
  have gd : ∀ (Lv Mv : Fin 6 → ℝ) (i j : Fin 6),
      galeD (lk08 xs Lv) (lk08 xs Mv) (xs i) (xs j) = Lv i * Mv j - Mv i * Lv j := by
    intro Lv Mv i j
    unfold galeD
    rw [lk08_eq hinj, lk08_eq hinj, lk08_eq hinj, lk08_eq hinj]
  have kA := gd (dv08 θ X1 (-na) 0) (dv08 θ 0 nc (-X1)) 0 1
  have kB := gd (dv08 θ X1 (-na) 0) (dv08 θ 0 nc (-X1)) 2 3
  have kC := gd (dv08 θ X1 (-na) 0) (dv08 θ 0 nc (-X1)) 4 5
  have kU := gd (dv08 θ X1 (-na) 0) (dv08 θ 0 nc (-X1)) 2 4
  simp only [dv08, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val] at kA kB kC kU
  set Lf := lk08 xs (dv08 θ X1 (-na) 0) with hLf
  set Mf := lk08 xs (dv08 θ 0 nc (-X1)) with hMf
  have wA : galeD Lf Mf (nfShape08 o E₁ E₂ E₃ θ 0) (nfShape08 o E₁ E₂ E₃ θ 1) = X1 * gWa θ :=
    kA.trans (by simp only [gWa, hX1, hnc']; ring)
  have wB : galeD Lf Mf (nfShape08 o E₁ E₂ E₃ θ 2) (nfShape08 o E₁ E₂ E₃ θ 3) = X1 * gWb θ :=
    kB.trans (by simp only [gWb, hX1, hnc', hna]; ring)
  have wC : galeD Lf Mf (nfShape08 o E₁ E₂ E₃ θ 4) (nfShape08 o E₁ E₂ E₃ θ 5) = X1 * gWc θ :=
    kC.trans (by simp only [gWc, hX1, hnc', hna]; ring)
  have wU : galeD Lf Mf (nfShape08 o E₁ E₂ E₃ θ 2) (nfShape08 o E₁ E₂ E₃ θ 4) = X1 * gWU θ :=
    kU.trans (by simp only [gWU, hX1, hnc', hna]; ring)
  have swp : ∀ s t, galeD Mf Lf s t = -galeD Lf Mf s t := fun s t => by unfold galeD; ring
  have hU0 : gWU θ ≠ 0 := by intro h; rw [h] at q9; simp at q9
  have hc0 : gWc θ ≠ 0 := by intro h; rw [h] at q11; simp at q11
  rcases lt_or_gt_of_ne hU0 with hn | hp
  · have hWa : 0 < gWa θ := by
      rcases lt_trichotomy (gWa θ) 0 with h | h | h
      · exact absurd (mul_pos_of_neg_of_neg h hn) (by linarith)
      · rw [h] at q9; simp at q9
      · exact h
    have hWb : 0 < gWb θ := by
      rcases lt_trichotomy (gWb θ) 0 with h | h | h
      · exact absurd (mul_pos_of_neg_of_neg h hn) (by linarith)
      · rw [h] at q10; simp at q10
      · exact h
    have sA : 0 < galeD Mf Lf (nfShape08 o E₁ E₂ E₃ θ 0) (nfShape08 o E₁ E₂ E₃ θ 1) := by
      rw [swp, wA]; exact neg_pos.mpr (mul_neg_of_neg_of_pos hnb hWa)
    have sB : 0 < galeD Mf Lf (nfShape08 o E₁ E₂ E₃ θ 2) (nfShape08 o E₁ E₂ E₃ θ 3) := by
      rw [swp, wB]; exact neg_pos.mpr (mul_neg_of_neg_of_pos hnb hWb)
    have sC : galeD Mf Lf (nfShape08 o E₁ E₂ E₃ θ 4) (nfShape08 o E₁ E₂ E₃ θ 5) ≠ 0 := by
      rw [swp, wC]; exact neg_ne_zero.mpr (mul_ne_zero hnb.ne hc0)
    have sU : galeD Mf Lf (nfShape08 o E₁ E₂ E₃ θ 2) (nfShape08 o E₁ E₂ E₃ θ 4) < 0 := by
      rw [swp, wU]; exact neg_lt_zero.mpr (mul_pos_of_neg_of_neg hnb hn)
    exact ⟨⟨Mf, Lf, hM, hL, fun α β h0 h1 h2 h3 h4 h5 => by
      have r := hind β α (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
      exact ⟨r.2, r.1⟩⟩, sA, sB, sC, sU⟩
  · have hWa : gWa θ < 0 := by
      rcases lt_trichotomy (gWa θ) 0 with h | h | h
      · exact h
      · rw [h] at q9; simp at q9
      · exact absurd (mul_pos h hp) (by linarith)
    have hWb : gWb θ < 0 := by
      rcases lt_trichotomy (gWb θ) 0 with h | h | h
      · exact h
      · rw [h] at q10; simp at q10
      · exact absurd (mul_pos h hp) (by linarith)
    have sA : 0 < galeD Lf Mf (nfShape08 o E₁ E₂ E₃ θ 0) (nfShape08 o E₁ E₂ E₃ θ 1) := by rw [wA]; exact mul_pos_of_neg_of_neg hnb hWa
    have sB : 0 < galeD Lf Mf (nfShape08 o E₁ E₂ E₃ θ 2) (nfShape08 o E₁ E₂ E₃ θ 3) := by rw [wB]; exact mul_pos_of_neg_of_neg hnb hWb
    have sC : galeD Lf Mf (nfShape08 o E₁ E₂ E₃ θ 4) (nfShape08 o E₁ E₂ E₃ θ 5) ≠ 0 := by rw [wC]; exact mul_ne_zero hnb.ne hc0
    have sU : galeD Lf Mf (nfShape08 o E₁ E₂ E₃ θ 2) (nfShape08 o E₁ E₂ E₃ θ 4) < 0 := by rw [wU]; exact mul_neg_of_neg_of_pos hnb hp
    exact ⟨⟨Lf, Mf, hL, hM, hind⟩, sA, sB, sC, sU⟩

set_option maxHeartbeats 4000000 in
/-- **Region ⇒ `Norm08`** (the converse of `exists_nf08`; the openness of the region is what the limit
argument needs, and `B1`/`cert08_pre` applies the old lemmas through it).  Only `gale_of_nf08` is open. -/
theorem norm08_of_nf {o E₁ E₂ E₃ : ℝ³} (hE : det3 E₁ E₂ E₃ ≠ 0) {θ : Fin 6 → ℝ}
    (hθ : ∀ k, 0 < ineq08 θ k) :
    Nonempty (Norm08 (nfShape08 o E₁ E₂ E₃ θ 0) (nfShape08 o E₁ E₂ E₃ θ 1) (nfShape08 o E₁ E₂ E₃ θ 2)
      (nfShape08 o E₁ E₂ E₃ θ 3) (nfShape08 o E₁ E₂ E₃ θ 4) (nfShape08 o E₁ E₂ E₃ θ 5)
      (nfShape08 o E₁ E₂ E₃ θ 6)) := by
  set x := nfShape08 o E₁ E₂ E₃ θ with hx
  obtain ⟨G, g1, g2, g3, g4⟩ := gale_of_nf08 (o := o) hE hθ
  have hinj := fun i j (h : x i = x j) => nfinj08 hE (θ := θ) i j h
  have p0 := hθ 0; have p1 := hθ 1; have p2 := hθ 2; have p3 := hθ 3; have p4 := hθ 4; have p5 := hθ 5
  simp only [ineq08, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Matrix.head_cons] at p0 p1 p2 p3 p4 p5
  have n01 : x 0 ≠ x 1 := fun h => by have := hinj 0 1 h 0; simp [cp08] at this; try linarith
  have n02 : x 0 ≠ x 2 := fun h => by have := hinj 0 2 h 0; simp [cp08] at this; try linarith
  have n03 : x 0 ≠ x 3 := fun h => by have := hinj 0 3 h 2; simp [cp08] at this; try linarith
  have n04 : x 0 ≠ x 4 := fun h => by have := hinj 0 4 h 0; simp [cp08] at this; try linarith
  have n05 : x 0 ≠ x 5 := fun h => by have := hinj 0 5 h 1; simp [cp08] at this; try linarith
  have n12 : x 1 ≠ x 2 := fun h => by have := hinj 1 2 h 2; simp [cp08] at this; try linarith
  have n13 : x 1 ≠ x 3 := fun h => by have := hinj 1 3 h 0; simp [cp08] at this; try linarith
  have n14 : x 1 ≠ x 4 := fun h => by have := hinj 1 4 h 1; simp [cp08] at this; try linarith
  have n15 : x 1 ≠ x 5 := fun h => by have := hinj 1 5 h 0; simp [cp08] at this; try linarith
  have n23 : x 2 ≠ x 3 := fun h => by have := hinj 2 3 h 0; simp [cp08] at this; try linarith
  have n24 : x 2 ≠ x 4 := fun h => by have := hinj 2 4 h 1; simp [cp08] at this; try linarith
  have n25 : x 2 ≠ x 5 := fun h => by have := hinj 2 5 h 0; simp [cp08] at this; try linarith
  have n34 : x 3 ≠ x 4 := fun h => by have := hinj 3 4 h 0; simp [cp08] at this; try linarith
  have n35 : x 3 ≠ x 5 := fun h => by have := hinj 3 5 h 1; simp [cp08] at this; try linarith
  have n45 : x 4 ≠ x 5 := fun h => by have := hinj 4 5 h 0; simp [cp08] at this; try linarith
  obtain ⟨fp1, fp2, fp3, fp4, fp5, fp6, fp7, fp8⟩ := fpos08 θ hθ
  have nd : [x 0, x 1, x 2, x 3, x 4, x 5].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true]
    exact ⟨⟨n01, n02, n03, n04, n05⟩, ⟨n12.symm.symm, n13, n14, n15⟩, ⟨n23, n24, n25⟩, ⟨n34, n35⟩, n45, not_false⟩
  let F : OctFacets (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) := ⟨nd,
      (mkF08 _ (x 0) (x 2) (x 4) (x 1) (hneg08 hE 0 2 4 1 ({1, 3, 5} : Finset (Fin 7)) fp1 (by decide) (by decide))),
      (mkF08 _ (x 0) (x 2) (x 5) (x 1) (hneg08 hE 0 2 5 1 ({1, 3, 4} : Finset (Fin 7)) fp2 (by decide) (by decide))),
      (mkF08 _ (x 0) (x 3) (x 4) (x 1) (hneg08 hE 0 3 4 1 ({1, 2, 5} : Finset (Fin 7)) fp3 (by decide) (by decide))),
      (mkF08 _ (x 0) (x 3) (x 5) (x 1) (hneg08 hE 0 3 5 1 ({1, 2, 4} : Finset (Fin 7)) fp4 (by decide) (by decide))),
      (mkF08 _ (x 1) (x 2) (x 4) (x 0) (hneg08 hE 1 2 4 0 ({0, 3, 5} : Finset (Fin 7)) fp5 (by decide) (by decide))),
      (mkF08 _ (x 1) (x 2) (x 5) (x 0) (hneg08 hE 1 2 5 0 ({0, 3, 4} : Finset (Fin 7)) fp6 (by decide) (by decide))),
      (mkF08 _ (x 1) (x 3) (x 4) (x 0) (hneg08 hE 1 3 4 0 ({0, 2, 5} : Finset (Fin 7)) fp7 (by decide) (by decide))),
      (mkF08 _ (x 1) (x 3) (x 5) (x 0) (hneg08 hE 1 3 5 0 ({0, 2, 4} : Finset (Fin 7)) fp8 (by decide) (by decide)))⟩
  have hsq : 0 < det3 E₁ E₂ E₃ ^ 2 := by positivity
  obtain ⟨d1, d2, d3, d4⟩ := fc08_d0 θ
  obtain ⟨⟨c1, -, -⟩, -⟩ := fc08_coord θ
  have h8 : 0 < θ 4 + θ 5 - 1 := hθ 8
  have h12 : 0 < fc08 θ 0 3 5 1 * fc08 θ 0 3 5 6 := hθ 12
  have h15 : 0 < fc08 θ 1 2 5 0 * fc08 θ 1 2 5 6 := hθ 15
  have h18 : 0 < fc08 θ 1 3 4 0 * fc08 θ 1 3 4 6 := hθ 18
  have h21 : 0 < fc08 θ 1 3 5 0 * fc08 θ 1 3 5 6 := hθ 21
  refine ⟨⟨F, ?_, G, g1, g2, g3, g4⟩⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change -(det3 (x 2 - x 0) (x 5 - x 0) (x 1 - x 0)) * det3 (x 2 - x 0) (x 5 - x 0) (x 6 - x 0) = 0
    rw [hx, det3_nf08, det3_nf08, d1]; ring
  · change -(det3 (x 3 - x 0) (x 4 - x 0) (x 1 - x 0)) * det3 (x 3 - x 0) (x 4 - x 0) (x 6 - x 0) = 0
    rw [hx, det3_nf08, det3_nf08, d2]; ring
  · change -(det3 (x 2 - x 1) (x 4 - x 1) (x 0 - x 1)) * det3 (x 2 - x 1) (x 4 - x 1) (x 6 - x 1) = 0
    rw [hx, det3_nf08, det3_nf08, d3]; ring
  · change 0 < -(det3 (x 2 - x 0) (x 4 - x 0) (x 1 - x 0)) * det3 (x 2 - x 0) (x 4 - x 0) (x 6 - x 0)
    rw [hx, det3_nf08, det3_nf08, d4, c1]; nlinarith [mul_pos hsq h8]
  · change -(det3 (x 3 - x 0) (x 5 - x 0) (x 1 - x 0)) * det3 (x 3 - x 0) (x 5 - x 0) (x 6 - x 0) < 0
    rw [hx, det3_nf08, det3_nf08]; nlinarith [mul_pos hsq h12]
  · change -(det3 (x 2 - x 1) (x 5 - x 1) (x 0 - x 1)) * det3 (x 2 - x 1) (x 5 - x 1) (x 6 - x 1) < 0
    rw [hx, det3_nf08, det3_nf08]; nlinarith [mul_pos hsq h15]
  · change -(det3 (x 3 - x 1) (x 4 - x 1) (x 0 - x 1)) * det3 (x 3 - x 1) (x 4 - x 1) (x 6 - x 1) < 0
    rw [hx, det3_nf08, det3_nf08]; nlinarith [mul_pos hsq h18]
  · change -(det3 (x 3 - x 1) (x 5 - x 1) (x 0 - x 1)) * det3 (x 3 - x 1) (x 5 - x 1) (x 6 - x 1) < 0
    rw [hx, det3_nf08, det3_nf08]; nlinarith [mul_pos hsq h21]


/-! ### Part B: the certificates of generic shapes -/

/-- The affine polygon part of a rim certificate (`RimCertAt` without robustness). -/
def RimGeom {n k : ℕ} (x : Fin n → ℝ³) (u : ℝ³) (lab : ZMod k → Fin n) : Prop :=
  3 ≤ k ∧ (∀ i j : ZMod k, j ≠ i → j ≠ i + 1 →
    0 < det3 (x (lab (i + 1)) - x (lab i)) (x (lab j) - x (lab i)) u) ∧
  ∀ (m : Fin n) (i : ZMod k), 0 ≤ det3 (x (lab (i + 1)) - x (lab i)) (x m - x (lab i)) u

/-- Coordinate form of `RimGeom`: edge `l i → l (i+1)`, other corners strictly left, all points weakly
left, where the view is `x p - x q` (scaled by `σ`). -/
def CRim (θ : Fin 6 → ℝ) {k : ℕ} (lab : ZMod k → Fin 7) (p q : Fin 7) (σ : ℝ) : Prop :=
  (∀ i j : ZMod k, j ≠ i → j ≠ i + 1 →
    0 < σ * (fc08 θ (lab i) (lab (i + 1)) (lab j) p - fc08 θ (lab i) (lab (i + 1)) (lab j) q)) ∧
  ∀ (m : Fin 7) (i : ZMod k),
    0 ≤ σ * (fc08 θ (lab i) (lab (i + 1)) m p - fc08 θ (lab i) (lab (i + 1)) m q)

/-- The sign facts of the region, in polynomial form. -/
theorem facts08 (θ : Fin 6 → ℝ) (hθ : ∀ k, 0 < ineq08 θ k) :
    0 < θ 0 ∧ 0 < θ 1 ∧ 0 < θ 2 ∧ 0 < θ 3 ∧ 0 < θ 4 ∧ 0 < θ 5 ∧ 1 < θ 0 + θ 1 ∧ 1 < θ 2 + θ 3 ∧ 1 < θ 4 + θ 5 ∧
    0 < fc08 θ 0 3 5 1 ∧ 0 < fc08 θ 0 3 5 2 ∧ 0 < fc08 θ 0 3 5 4 ∧
    0 < fc08 θ 1 2 5 0 ∧ 0 < fc08 θ 1 2 5 3 ∧ 0 < fc08 θ 1 2 5 4 ∧
    0 < fc08 θ 1 3 4 0 ∧ 0 < fc08 θ 1 3 4 2 ∧ 0 < fc08 θ 1 3 4 5 ∧
    fc08 θ 1 3 5 0 < 0 ∧ fc08 θ 1 3 5 2 < 0 ∧ fc08 θ 1 3 5 4 < 0 := by
  have p0 := hθ 0; have p1 := hθ 1; have p2 := hθ 2; have p3 := hθ 3; have p4 := hθ 4; have p5 := hθ 5
  have p6 := hθ 6; have p7 := hθ 7; have p8 := hθ 8
  have h12 := hθ 12; have h13 := hθ 13; have h14 := hθ 14
  have h15 := hθ 15; have h16 := hθ 16; have h17 := hθ 17
  have h18 := hθ 18; have h19 := hθ 19; have h20 := hθ 20
  have h21 := hθ 21; have h22 := hθ 22; have h23 := hθ 23
  simp only [ineq08, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Matrix.head_cons] at p0 p1 p2 p3 p4 p5 p6 p7 p8 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23
  have d1 : fc08 θ 0 3 5 6 = θ 1 * θ 3 := by
    simp only [fc08, cdet, cp08]; simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Matrix.head_cons]; ring
  have d2 : fc08 θ 1 2 5 6 = θ 0 * θ 5 := by
    simp only [fc08, cdet, cp08]; simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Matrix.head_cons]; ring
  have d3 : fc08 θ 1 3 4 6 = θ 2 * θ 4 := by
    simp only [fc08, cdet, cp08]; simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Matrix.head_cons]; ring
  have d4 : fc08 θ 1 3 5 6 = -(θ 0 * θ 3 * θ 4 + θ 1 * θ 2 * θ 5) := by
    simp only [fc08, cdet, cp08]; simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Matrix.head_cons]; ring
  have e1 : 0 < fc08 θ 0 3 5 6 := by rw [d1]; positivity
  have e2 : 0 < fc08 θ 1 2 5 6 := by rw [d2]; positivity
  have e3 : 0 < fc08 θ 1 3 4 6 := by rw [d3]; positivity
  have e4 : fc08 θ 1 3 5 6 < 0 := by rw [d4]; have : 0 < θ 0 * θ 3 * θ 4 + θ 1 * θ 2 * θ 5 := by positivity
                                     linarith
  refine ⟨p0, p1, p2, p3, p4, p5, by linarith, by linarith, by linarith, ?_⟩
  refine ⟨(pos_iff_pos_of_mul_pos h12).mpr e1, (pos_iff_pos_of_mul_pos h13).mpr e1,
    (pos_iff_pos_of_mul_pos h14).mpr e1, (pos_iff_pos_of_mul_pos h15).mpr e2,
    (pos_iff_pos_of_mul_pos h16).mpr e2, (pos_iff_pos_of_mul_pos h17).mpr e2,
    (pos_iff_pos_of_mul_pos h18).mpr e3, (pos_iff_pos_of_mul_pos h19).mpr e3,
    (pos_iff_pos_of_mul_pos h20).mpr e3, (neg_iff_neg_of_mul_pos h21).mpr e4,
    (neg_iff_neg_of_mul_pos h22).mpr e4, (neg_iff_neg_of_mul_pos h23).mpr e4⟩


theorem polyA (a1 b1 a4 g4 b6 g6 : ℝ) (p0 : 0 < a1) (p1 : 0 < b1) (p2 : 0 < a4) (p3 : 0 < g4) (p4 : 0 < b6) (p5 : 0 < g6) (e1 : 0 < a1 + b1 - 1) (e2 : 0 < a4 + g4 - 1) (e3 : 0 < b6 + g6 - 1) (dA : 0 < -1 + g6) (dB : 0 < -1 + a1) (ga : 0 < -a1 + a1 * g4 - b1 * a4 + a4) (gb : 0 < a1 * b6 + b1 - b1 * g6 - b6) (f1 : 0 < a1 * g4 * b6 + b1 * a4 * g6 + b1 * g4 - b1 * g6 - g4 * b6) (f2 : 0 < a1 * g4 + b1 * g4 - g4) (f3 : 0 < -b1 + b1 * a4 + b1 * g4) (f4 : 0 < a1 * g6 + b1 * g6 - g6) (f5 : 0 < -a1 * g4 + a1 * g4 * b6 + a1 * g6 + b1 * a4 * g6 - a4 * g6) (f6 : 0 < -a1 + a1 * b6 + a1 * g6) (f7 : 0 < a4 * b6 + g4 * b6 - b6) (f8 : 0 < -a4 + a4 * b6 + a4 * g6) (f9 : 0 < a1 * g4 * b6 - a1 * b6 - b1 * a4 + b1 * a4 * g6 + a4 * b6) (f10 : 0 < a1 * g4 * b6 + b1 * a4 * g6 + b1 * g4 - b1 * g6 - g4 * b6) (f11 : 0 < -a1 * g4 + a1 * g4 * b6 + a1 * g6 + b1 * a4 * g6 - a4 * g6) (f12 : 0 < a1 * g4 * b6 - a1 * b6 - b1 * a4 + b1 * a4 * g6 + a4 * b6) :
    0 < -a1 + a1 * b6 + a1 * g6 ∧ 0 < -a4 + a4 * b6 + a4 * g6 ∧ 0 < -1 + b6 + g6 ∧ 0 < -a1 + a1 * g4 * b6 + a1 * g6 - b1 * a4 + b1 * a4 * g6 + a4 - a4 * g6 ∧ 0 < 1 - a1 + a1 * g6 - b1 + b1 * g6 - g6 ∧ 0 < -a1 + a1 * g6 ∧ 0 < a1 * g4 * b6 - a1 * b6 - b1 * a4 + b1 * a4 * g6 + a4 * b6 ∧ 0 < a1 * g4 * b6 + b1 - b1 * a4 + b1 * a4 * g6 - b1 * g6 - g4 * b6 ∧ 0 < a1 * g4 * b6 - b1 * a4 + b1 * a4 * g6 ∧ 0 < a4 * b6 + g4 * b6 - b6 ∧ 0 < a4 * b6 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · first | linarith [mul_pos p0 p4, mul_pos p0 dA] | nlinarith [mul_pos p0 p4, mul_pos p0 dA]
  · first | linarith [mul_pos p2 dA, mul_pos p2 p4] | nlinarith [mul_pos p2 dA, mul_pos p2 p4]
  · first | linarith [p4, dA] | nlinarith [p4, dA]
  · first | linarith [ga, f11] | nlinarith [ga, f11]
  · first | linarith [mul_pos dA dB, mul_pos p1 dA] | nlinarith [mul_pos dA dB, mul_pos p1 dA]
  · first | linarith [mul_pos p0 dA] | nlinarith [mul_pos p0 dA]
  · first | linarith [mul_pos p4 ga, mul_pos (mul_pos p1 p2) p4, mul_pos (mul_pos p1 p2) dA] | nlinarith [mul_pos p4 ga, mul_pos (mul_pos p1 p2) p4, mul_pos (mul_pos p1 p2) dA]
  · first | linarith [mul_pos f3 dA, mul_pos p3 gb] | nlinarith [mul_pos f3 dA, mul_pos p3 gb]
  · first | linarith [mul_pos (mul_pos p0 p3) p4, mul_pos (mul_pos p1 p2) dA] | nlinarith [mul_pos (mul_pos p0 p3) p4, mul_pos (mul_pos p1 p2) dA]
  · first | linarith [mul_pos p4 e2] | nlinarith [mul_pos p4 e2]
  · first | linarith [mul_pos p2 p4] | nlinarith [mul_pos p2 p4]

theorem polyB (a1 b1 a4 g4 b6 g6 : ℝ) (p0 : 0 < a1) (p1 : 0 < b1) (p2 : 0 < a4) (p3 : 0 < g4) (p4 : 0 < b6) (p5 : 0 < g6) (e1 : 0 < a1 + b1 - 1) (e2 : 0 < a4 + g4 - 1) (e3 : 0 < b6 + g6 - 1) (dA : 0 < 1 - g6) (dB : 0 < -1 + a1) (ga : 0 < -a1 + a1 * g4 - b1 * a4 + a4) (gb : 0 < a1 * b6 + b1 - b1 * g6 - b6) (f1 : 0 < a1 * g4 * b6 + b1 * a4 * g6 + b1 * g4 - b1 * g6 - g4 * b6) (f2 : 0 < a1 * g4 + b1 * g4 - g4) (f3 : 0 < -b1 + b1 * a4 + b1 * g4) (f4 : 0 < a1 * g6 + b1 * g6 - g6) (f5 : 0 < -a1 * g4 + a1 * g4 * b6 + a1 * g6 + b1 * a4 * g6 - a4 * g6) (f6 : 0 < -a1 + a1 * b6 + a1 * g6) (f7 : 0 < a4 * b6 + g4 * b6 - b6) (f8 : 0 < -a4 + a4 * b6 + a4 * g6) (f9 : 0 < a1 * g4 * b6 - a1 * b6 - b1 * a4 + b1 * a4 * g6 + a4 * b6) (f10 : 0 < a1 * g4 * b6 + b1 * a4 * g6 + b1 * g4 - b1 * g6 - g4 * b6) (f11 : 0 < -a1 * g4 + a1 * g4 * b6 + a1 * g6 + b1 * a4 * g6 - a4 * g6) (f12 : 0 < a1 * g4 * b6 - a1 * b6 - b1 * a4 + b1 * a4 * g6 + a4 * b6) :
    0 < a1 * g4 ∧ 0 < a1 ∧ 0 < a1 * g6 ∧ 0 < -a1 + a1 * g4 + a4 ∧ 0 < a1 * g4 - g4 ∧ 0 < a1 * g4 - a1 * g6 + a4 * g6 ∧ 0 < a4 ∧ 0 < -1 + a4 + g4 ∧ 0 < a4 - a4 * g6 ∧ 0 < 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · first | linarith [mul_pos p0 p3] | nlinarith [mul_pos p0 p3]
  · first | linarith [p0] | nlinarith [p0]
  · first | linarith [mul_pos p0 p5] | nlinarith [mul_pos p0 p5]
  · first | linarith [mul_pos (mul_pos p5 p5) ga, mul_pos p1 p2, mul_pos (mul_pos dA dA) ga, mul_pos (mul_pos p5 dA) ga] | nlinarith [mul_pos (mul_pos p5 p5) ga, mul_pos p1 p2, mul_pos (mul_pos dA dA) ga, mul_pos (mul_pos p5 dA) ga]
  · first | linarith [mul_pos p3 dB] | nlinarith [mul_pos p3 dB]
  · first | linarith [mul_pos p5 ga, mul_pos (mul_pos p0 p3) dA, mul_pos (mul_pos p1 p2) p5] | nlinarith [mul_pos p5 ga, mul_pos (mul_pos p0 p3) dA, mul_pos (mul_pos p1 p2) p5]
  · first | linarith [p2] | nlinarith [p2]
  · first | linarith [e2] | nlinarith [e2]
  · first | linarith [mul_pos p2 dA] | nlinarith [mul_pos p2 dA]
  · first | linarith [p5, dA] | nlinarith [p5, dA]

theorem polyC (a1 b1 a4 g4 b6 g6 : ℝ) (p0 : 0 < a1) (p1 : 0 < b1) (p2 : 0 < a4) (p3 : 0 < g4) (p4 : 0 < b6) (p5 : 0 < g6) (e1 : 0 < a1 + b1 - 1) (e2 : 0 < a4 + g4 - 1) (e3 : 0 < b6 + g6 - 1) (dA : 0 < 1 - g6) (dB : 0 < 1 - a1) (ga : 0 < -a1 + a1 * g4 - b1 * a4 + a4) (gb : 0 < a1 * b6 + b1 - b1 * g6 - b6) (f1 : 0 < a1 * g4 * b6 + b1 * a4 * g6 + b1 * g4 - b1 * g6 - g4 * b6) (f2 : 0 < a1 * g4 + b1 * g4 - g4) (f3 : 0 < -b1 + b1 * a4 + b1 * g4) (f4 : 0 < a1 * g6 + b1 * g6 - g6) (f5 : 0 < -a1 * g4 + a1 * g4 * b6 + a1 * g6 + b1 * a4 * g6 - a4 * g6) (f6 : 0 < -a1 + a1 * b6 + a1 * g6) (f7 : 0 < a4 * b6 + g4 * b6 - b6) (f8 : 0 < -a4 + a4 * b6 + a4 * g6) (f9 : 0 < a1 * g4 * b6 - a1 * b6 - b1 * a4 + b1 * a4 * g6 + a4 * b6) (f10 : 0 < a1 * g4 * b6 + b1 * a4 * g6 + b1 * g4 - b1 * g6 - g4 * b6) (f11 : 0 < -a1 * g4 + a1 * g4 * b6 + a1 * g6 + b1 * a4 * g6 - a4 * g6) (f12 : 0 < a1 * g4 * b6 - a1 * b6 - b1 * a4 + b1 * a4 * g6 + a4 * b6) :
    0 < g4 ∧ 0 < 1 ∧ 0 < g6 ∧ 0 < -1 + a4 + g4 ∧ 0 < a4 * g6 + g4 - g6 ∧ 0 < -a1 * g4 + g4 ∧ 0 < a4 ∧ 0 < a4 - a4 * g6 ∧ 0 < -a1 + a1 * g4 + a4 ∧ 0 < a1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · first | linarith [p3] | nlinarith [p3]
  · first | linarith [p5, dA] | nlinarith [p5, dA]
  · first | linarith [p5] | nlinarith [p5]
  · first | linarith [mul_pos (mul_pos (mul_pos p0 e2) dA) dB, mul_pos (mul_pos (mul_pos e2 dA) dB) dB, mul_pos (mul_pos (mul_pos p5 p5) e2) dB, mul_pos p0 e2, mul_pos (mul_pos (mul_pos p5 e2) dA) dB] | nlinarith [mul_pos (mul_pos (mul_pos p0 e2) dA) dB, mul_pos (mul_pos (mul_pos e2 dA) dB) dB, mul_pos (mul_pos (mul_pos p5 p5) e2) dB, mul_pos p0 e2, mul_pos (mul_pos (mul_pos p5 e2) dA) dB]
  · first | linarith [mul_pos (mul_pos (mul_pos p3 dA) dB) dB, mul_pos (mul_pos (mul_pos p0 p3) dA) dB, mul_pos (mul_pos p5 p5) e2, mul_pos (mul_pos p5 e2) dA, mul_pos (mul_pos p0 p3) dA] | nlinarith [mul_pos (mul_pos (mul_pos p3 dA) dB) dB, mul_pos (mul_pos (mul_pos p0 p3) dA) dB, mul_pos (mul_pos p5 p5) e2, mul_pos (mul_pos p5 e2) dA, mul_pos (mul_pos p0 p3) dA]
  · first | linarith [mul_pos p3 dB] | nlinarith [mul_pos p3 dB]
  · first | linarith [p2] | nlinarith [p2]
  · first | linarith [mul_pos p2 dA] | nlinarith [mul_pos p2 dA]
  · first | linarith [mul_pos (mul_pos (mul_pos p0 p0) e2) dB, mul_pos (mul_pos (mul_pos p0 e2) dB) dB, mul_pos (mul_pos (mul_pos p0 p0) p0) e2, mul_pos (mul_pos (mul_pos p2 dA) dB) dB, mul_pos (mul_pos (mul_pos p0 p2) dA) dB, mul_pos (mul_pos p2 p5) dB] | nlinarith [mul_pos (mul_pos (mul_pos p0 p0) e2) dB, mul_pos (mul_pos (mul_pos p0 e2) dB) dB, mul_pos (mul_pos (mul_pos p0 p0) p0) e2, mul_pos (mul_pos (mul_pos p2 dA) dB) dB, mul_pos (mul_pos (mul_pos p0 p2) dA) dB, mul_pos (mul_pos p2 p5) dB]
  · first | linarith [p0] | nlinarith [p0]


theorem common08 (θ : Fin 6 → ℝ) (hθ : ∀ k, 0 < ineq08 θ k) :
    0 < (θ 0) ∧ 0 < (θ 1) ∧ 0 < (θ 2) ∧ 0 < (θ 3) ∧ 0 < (θ 4) ∧ 0 < (θ 5) ∧ 0 < (θ 0) + (θ 1) - 1 ∧ 0 < (θ 2) + (θ 3) - 1 ∧ 0 < (θ 4) + (θ 5) - 1 ∧ 0 < -(θ 0) + (θ 0) * (θ 3) - (θ 1) * (θ 2) + (θ 2) ∧ 0 < (θ 0) * (θ 4) + (θ 1) - (θ 1) * (θ 5) - (θ 4) ∧ 0 < (θ 0) * (θ 3) * (θ 4) + (θ 1) * (θ 2) * (θ 5) + (θ 1) * (θ 3) - (θ 1) * (θ 5) - (θ 3) * (θ 4) ∧ 0 < (θ 0) * (θ 3) + (θ 1) * (θ 3) - (θ 3) ∧ 0 < -(θ 1) + (θ 1) * (θ 2) + (θ 1) * (θ 3) ∧ 0 < (θ 0) * (θ 5) + (θ 1) * (θ 5) - (θ 5) ∧ 0 < -(θ 0) * (θ 3) + (θ 0) * (θ 3) * (θ 4) + (θ 0) * (θ 5) + (θ 1) * (θ 2) * (θ 5) - (θ 2) * (θ 5) ∧ 0 < -(θ 0) + (θ 0) * (θ 4) + (θ 0) * (θ 5) ∧ 0 < (θ 2) * (θ 4) + (θ 3) * (θ 4) - (θ 4) ∧ 0 < -(θ 2) + (θ 2) * (θ 4) + (θ 2) * (θ 5) ∧ 0 < (θ 0) * (θ 3) * (θ 4) - (θ 0) * (θ 4) - (θ 1) * (θ 2) + (θ 1) * (θ 2) * (θ 5) + (θ 2) * (θ 4) ∧ 0 < (θ 0) * (θ 3) * (θ 4) + (θ 1) * (θ 2) * (θ 5) + (θ 1) * (θ 3) - (θ 1) * (θ 5) - (θ 3) * (θ 4) ∧ 0 < -(θ 0) * (θ 3) + (θ 0) * (θ 3) * (θ 4) + (θ 0) * (θ 5) + (θ 1) * (θ 2) * (θ 5) - (θ 2) * (θ 5) ∧ 0 < (θ 0) * (θ 3) * (θ 4) - (θ 0) * (θ 4) - (θ 1) * (θ 2) + (θ 1) * (θ 2) * (θ 5) + (θ 2) * (θ 4) := by
  obtain ⟨p0, p1, p2, p3, p4, p5, q6, q7, q8, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12⟩ :=
    facts08 θ hθ
  have h9 := hθ 9
  simp only [ineq08, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Matrix.head_cons] at h9
  simp only [fc08, cdet, cp08, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    Matrix.head_cons] at f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12
  have hU : gWU θ < 0 := by unfold gWU; nlinarith [f10]
  have hga : 0 < gWa θ := (pos_iff_pos_of_mul_pos (show 0 < gWa θ * (-gWU θ) by linarith)).mpr (by linarith)
  have h10 := hθ 10
  simp only [ineq08, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Matrix.head_cons] at h10
  have hgb : 0 < gWb θ := (pos_iff_pos_of_mul_pos (show 0 < gWb θ * (-gWU θ) by linarith)).mpr (by linarith)
  unfold gWa at hga; unfold gWb at hgb
  refine ⟨p0, p1, p2, p3, p4, p5, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩


set_option maxHeartbeats 4000000 in
theorem crimA1 (θ : Fin 6 → ℝ) (hθ : ∀ k, 0 < ineq08 θ k) (h6 : 1 < θ 5) :
    CRim θ (fun i : ZMod 4 => (![4, 2, 5, 3] : Fin 4 → Fin 7) i) 4 1 (1) := by
  obtain ⟨p0, p1, p2, p3, p4, p5, e1, e2, e3, ga, gb, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12⟩ :=
    common08 θ hθ
  have dA : 0 < -1 + (θ 5) := by linarith
  have dB : 0 < -1 + (θ 0) := by
    have h : 0 < θ 4 * (θ 0 - 1) := by nlinarith [mul_pos p1 dA, gb]
    linarith [(pos_iff_pos_of_mul_pos h).mp p4]
  obtain ⟨t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10⟩ := polyA (θ 0) (θ 1) (θ 2) (θ 3) (θ 4) (θ 5) p0 p1 p2 p3 p4 p5 e1 e2 e3 dA dB ga gb
    f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12
  constructor
  · intro i j hi hj
    rcases zmod4_cases i with rfl | rfl | rfl | rfl <;> rcases zmod4_cases j with rfl | rfl | rfl | rfl <;>
      first | exact absurd rfl hi | exact absurd (by decide) hj | skip
    all_goals
      norm_num [fc08, cdet, cp08]
      try linarith
  · intro m i
    fin_cases m <;> rcases zmod4_cases i with rfl | rfl | rfl | rfl
    all_goals
      norm_num [fc08, cdet, cp08]
      try linarith

set_option maxHeartbeats 4000000 in
theorem crimA2 (θ : Fin 6 → ℝ) (hθ : ∀ k, 0 < ineq08 θ k) (h6 : 1 < θ 5) :
    CRim θ (fun i : ZMod 4 => (![1, 2, 5, 3] : Fin 4 → Fin 7) i) 4 1 (1) := by
  obtain ⟨p0, p1, p2, p3, p4, p5, e1, e2, e3, ga, gb, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12⟩ :=
    common08 θ hθ
  have dA : 0 < -1 + (θ 5) := by linarith
  have dB : 0 < -1 + (θ 0) := by
    have h : 0 < θ 4 * (θ 0 - 1) := by nlinarith [mul_pos p1 dA, gb]
    linarith [(pos_iff_pos_of_mul_pos h).mp p4]
  obtain ⟨t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10⟩ := polyA (θ 0) (θ 1) (θ 2) (θ 3) (θ 4) (θ 5) p0 p1 p2 p3 p4 p5 e1 e2 e3 dA dB ga gb
    f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12
  constructor
  · intro i j hi hj
    rcases zmod4_cases i with rfl | rfl | rfl | rfl <;> rcases zmod4_cases j with rfl | rfl | rfl | rfl <;>
      first | exact absurd rfl hi | exact absurd (by decide) hj | skip
    all_goals
      norm_num [fc08, cdet, cp08]
      try linarith
  · intro m i
    fin_cases m <;> rcases zmod4_cases i with rfl | rfl | rfl | rfl
    all_goals
      norm_num [fc08, cdet, cp08]
      try linarith

set_option maxHeartbeats 4000000 in
theorem crimB1 (θ : Fin 6 → ℝ) (hθ : ∀ k, 0 < ineq08 θ k) (h6 : θ 5 < 1) (h0 : 1 < θ 0) :
    CRim θ (fun i : ZMod 4 => (![2, 5, 3, 4] : Fin 4 → Fin 7) i) 2 6 (-1) := by
  obtain ⟨p0, p1, p2, p3, p4, p5, e1, e2, e3, ga, gb, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12⟩ :=
    common08 θ hθ
  have dA : 0 < 1 - (θ 5) := by linarith
  have dB : 0 < -1 + (θ 0) := by
    linarith
  obtain ⟨t0, t1, t2, t3, t4, t5, t6, t7, t8, t9⟩ := polyB (θ 0) (θ 1) (θ 2) (θ 3) (θ 4) (θ 5) p0 p1 p2 p3 p4 p5 e1 e2 e3 dA dB ga gb
    f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12
  constructor
  · intro i j hi hj
    rcases zmod4_cases i with rfl | rfl | rfl | rfl <;> rcases zmod4_cases j with rfl | rfl | rfl | rfl <;>
      first | exact absurd rfl hi | exact absurd (by decide) hj | skip
    all_goals
      norm_num [fc08, cdet, cp08]
      try linarith
  · intro m i
    fin_cases m <;> rcases zmod4_cases i with rfl | rfl | rfl | rfl
    all_goals
      norm_num [fc08, cdet, cp08]
      try linarith

set_option maxHeartbeats 4000000 in
theorem crimB2 (θ : Fin 6 → ℝ) (hθ : ∀ k, 0 < ineq08 θ k) (h6 : θ 5 < 1) (h0 : 1 < θ 0) :
    CRim θ (fun i : ZMod 4 => (![6, 5, 3, 4] : Fin 4 → Fin 7) i) 2 6 (-1) := by
  obtain ⟨p0, p1, p2, p3, p4, p5, e1, e2, e3, ga, gb, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12⟩ :=
    common08 θ hθ
  have dA : 0 < 1 - (θ 5) := by linarith
  have dB : 0 < -1 + (θ 0) := by
    linarith
  obtain ⟨t0, t1, t2, t3, t4, t5, t6, t7, t8, t9⟩ := polyB (θ 0) (θ 1) (θ 2) (θ 3) (θ 4) (θ 5) p0 p1 p2 p3 p4 p5 e1 e2 e3 dA dB ga gb
    f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12
  constructor
  · intro i j hi hj
    rcases zmod4_cases i with rfl | rfl | rfl | rfl <;> rcases zmod4_cases j with rfl | rfl | rfl | rfl <;>
      first | exact absurd rfl hi | exact absurd (by decide) hj | skip
    all_goals
      norm_num [fc08, cdet, cp08]
      try linarith
  · intro m i
    fin_cases m <;> rcases zmod4_cases i with rfl | rfl | rfl | rfl
    all_goals
      norm_num [fc08, cdet, cp08]
      try linarith

set_option maxHeartbeats 4000000 in
theorem crimC1 (θ : Fin 6 → ℝ) (hθ : ∀ k, 0 < ineq08 θ k) (h6 : θ 5 < 1) (h0 : θ 0 < 1) :
    CRim θ (fun i : ZMod 4 => (![6, 0, 3, 4] : Fin 4 → Fin 7) i) 2 6 (-1) := by
  obtain ⟨p0, p1, p2, p3, p4, p5, e1, e2, e3, ga, gb, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12⟩ :=
    common08 θ hθ
  have dA : 0 < 1 - (θ 5) := by linarith
  have dB : 0 < 1 - (θ 0) := by
    linarith
  obtain ⟨t0, t1, t2, t3, t4, t5, t6, t7, t8, t9⟩ := polyC (θ 0) (θ 1) (θ 2) (θ 3) (θ 4) (θ 5) p0 p1 p2 p3 p4 p5 e1 e2 e3 dA dB ga gb
    f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12
  constructor
  · intro i j hi hj
    rcases zmod4_cases i with rfl | rfl | rfl | rfl <;> rcases zmod4_cases j with rfl | rfl | rfl | rfl <;>
      first | exact absurd rfl hi | exact absurd (by decide) hj | skip
    all_goals
      norm_num [fc08, cdet, cp08]
      try linarith
  · intro m i
    fin_cases m <;> rcases zmod4_cases i with rfl | rfl | rfl | rfl
    all_goals
      norm_num [fc08, cdet, cp08]
      try linarith


/-! ### From coordinates to `RimGeom` -/

theorem det3_view08 (o E₁ E₂ E₃ : ℝ³) (θ : Fin 6 → ℝ) (i j k p q : Fin 7) (ε : ℝ) :
    det3 (nfShape08 o E₁ E₂ E₃ θ j - nfShape08 o E₁ E₂ E₃ θ i)
      (nfShape08 o E₁ E₂ E₃ θ k - nfShape08 o E₁ E₂ E₃ θ i)
      (ε • (nfShape08 o E₁ E₂ E₃ θ p - nfShape08 o E₁ E₂ E₃ θ q)) =
    ε * (det3 E₁ E₂ E₃ * (fc08 θ i j k p - fc08 θ i j k q)) := by
  have e : nfShape08 o E₁ E₂ E₃ θ p - nfShape08 o E₁ E₂ E₃ θ q =
      (nfShape08 o E₁ E₂ E₃ θ p - nfShape08 o E₁ E₂ E₃ θ i) +
        (-1 : ℝ) • (nfShape08 o E₁ E₂ E₃ θ q - nfShape08 o E₁ E₂ E₃ θ i) := by
    simp only [neg_smul, one_smul]; abel
  rw [e, det3_smul_right, det3_add_right, det3_smul_right, det3_nf08, det3_nf08]
  ring

theorem rimGeom_of_crim {o E₁ E₂ E₃ : ℝ³} {θ : Fin 6 → ℝ} {k : ℕ} [NeZero k] (hk : 3 ≤ k)
    {lab : ZMod k → Fin 7} {p q : Fin 7} {σ c ε : ℝ} (hc : CRim θ lab p q σ) (hc0 : 0 < c)
    (hsign : ε * det3 E₁ E₂ E₃ = σ * c) {u : ℝ³}
    (hu : u = ε • (nfShape08 o E₁ E₂ E₃ θ p - nfShape08 o E₁ E₂ E₃ θ q)) :
    RimGeom (nfShape08 o E₁ E₂ E₃ θ) u lab := by
  subst hu
  refine ⟨hk, ?_, ?_⟩
  · intro i j hj hj'
    rw [det3_view08]
    have := mul_pos hc0 (hc.1 i j hj hj')
    have e : ε * (det3 E₁ E₂ E₃ * (fc08 θ (lab i) (lab (i + 1)) (lab j) p - fc08 θ (lab i) (lab (i + 1)) (lab j) q)) =
        c * (σ * (fc08 θ (lab i) (lab (i + 1)) (lab j) p - fc08 θ (lab i) (lab (i + 1)) (lab j) q)) := by
      rw [← mul_assoc, hsign]; ring
    rw [e]; exact this
  · intro m i
    rw [det3_view08]
    have := mul_nonneg hc0.le (hc.2 m i)
    have e : ε * (det3 E₁ E₂ E₃ * (fc08 θ (lab i) (lab (i + 1)) m p - fc08 θ (lab i) (lab (i + 1)) m q)) =
        c * (σ * (fc08 θ (lab i) (lab (i + 1)) m p - fc08 θ (lab i) (lab (i + 1)) m q)) := by
      rw [← mul_assoc, hsign]; ring
    rw [e]; exact this

/-- Sign choice: for `σ = ±1` and `det3 E ≠ 0` there is `s` with `ε * det = σ * c`, `c > 0`. -/
theorem exists_sign08 {d : ℝ} (hd : d ≠ 0) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) :
    ∃ s : Bool, ∃ c : ℝ, 0 < c ∧ (if s then (1 : ℝ) else -1) * d = σ * c := by
  rcases lt_or_gt_of_ne hd with h | h <;> rcases hσ with rfl | rfl
  · exact ⟨false, -d, by linarith, by simp⟩
  · exact ⟨true, -d, by linarith, by simp⟩
  · exact ⟨true, d, h, by simp⟩
  · exact ⟨false, d, h, by simp⟩


theorem sel08 (θ : Fin 6 → ℝ) (hg : MvPolynomial.eval θ genPoly08 ≠ 0) : θ 5 ≠ 1 ∧ θ 0 ≠ 1 := by
  simp only [genPoly08, map_mul, map_sub, MvPolynomial.eval_X, map_one, ne_eq, mul_eq_zero, not_or] at hg
  obtain ⟨⟨⟨⟨⟨h5, h0⟩, -⟩, -⟩, -⟩, -⟩ := hg
  exact ⟨fun h => h5 (by rw [h]; ring), fun h => h0 (by rw [h]; ring)⟩

/-- The polygon part: chosen group and sign, by the three cases `γ₆ > 1`, `γ₆ < 1 < α₁`,
`γ₆, α₁ < 1`. -/
theorem poly08 (o E₁ E₂ E₃ : ℝ³) (hE : det3 E₁ E₂ E₃ ≠ 0) (θ : Fin 6 → ℝ)
    (hθ : ∀ k, 0 < ineq08 θ k) (hg : MvPolynomial.eval θ genPoly08 ≠ 0) :
    ∃ (i : Fin 3) (s : Bool),
      ((i = 0 ∧ 1 < θ 5) ∨ (i = 1 ∧ θ 5 < 1 ∧ 1 < θ 0) ∨ (i = 2 ∧ θ 5 < 1 ∧ θ 0 < 1)) ∧
      ∀ j, RimGeom (nfShape08 o E₁ E₂ E₃ θ) ((test08 i s j).view (nfShape08 o E₁ E₂ E₃ θ))
        (test08 i s j).lab := by
  obtain ⟨n5, n0⟩ := sel08 θ hg
  rcases lt_or_gt_of_ne n5 with h5 | h5
  · rcases lt_or_gt_of_ne n0 with h0 | h0
    · obtain ⟨s, c, hc0, hsg⟩ := exists_sign08 hE (-1) (Or.inr rfl)
      refine ⟨2, s, Or.inr (Or.inr ⟨rfl, h5, h0⟩), ?_⟩
      intro j
      cases s <;> cases j <;> simp only [Bool.false_eq_true, if_false, if_true] at hsg <;>
        exact rimGeom_of_crim (by norm_num) (crimC1 θ hθ h5 h0) hc0 hsg (by simp [test08, grp08, ViewGroup.tests, LabTest.quad, LabTest.neg])
    · obtain ⟨s, c, hc0, hsg⟩ := exists_sign08 hE (-1) (Or.inr rfl)
      refine ⟨1, s, Or.inr (Or.inl ⟨rfl, h5, h0⟩), ?_⟩
      intro j
      cases s <;> cases j <;> simp only [Bool.false_eq_true, if_false, if_true] at hsg
      · exact rimGeom_of_crim (by norm_num) (crimB2 θ hθ h5 h0) hc0 hsg (by simp [test08, grp08, ViewGroup.tests, LabTest.quad, LabTest.neg])
      · exact rimGeom_of_crim (by norm_num) (crimB1 θ hθ h5 h0) hc0 hsg (by simp [test08, grp08, ViewGroup.tests, LabTest.quad, LabTest.neg])
      · exact rimGeom_of_crim (by norm_num) (crimB2 θ hθ h5 h0) hc0 hsg (by simp [test08, grp08, ViewGroup.tests, LabTest.quad, LabTest.neg])
      · exact rimGeom_of_crim (by norm_num) (crimB1 θ hθ h5 h0) hc0 hsg (by simp [test08, grp08, ViewGroup.tests, LabTest.quad, LabTest.neg])
  · obtain ⟨s, c, hc0, hsg⟩ := exists_sign08 hE 1 (Or.inl rfl)
    refine ⟨0, s, Or.inl ⟨rfl, h5⟩, ?_⟩
    intro j
    cases s <;> cases j <;> simp only [Bool.false_eq_true, if_false, if_true] at hsg
    · exact rimGeom_of_crim (by norm_num) (crimA2 θ hθ h5) hc0 hsg (by simp [test08, grp08, ViewGroup.tests, LabTest.quad, LabTest.neg])
    · exact rimGeom_of_crim (by norm_num) (crimA1 θ hθ h5) hc0 hsg (by simp [test08, grp08, ViewGroup.tests, LabTest.quad, LabTest.neg])
    · exact rimGeom_of_crim (by norm_num) (crimA2 θ hθ h5) hc0 hsg (by simp [test08, grp08, ViewGroup.tests, LabTest.quad, LabTest.neg])
    · exact rimGeom_of_crim (by norm_num) (crimA1 θ hθ h5) hc0 hsg (by simp [test08, grp08, ViewGroup.tests, LabTest.quad, LabTest.neg])


theorem inner_lt08 {v w : ℝ³} (h : v ≠ w) : ⟪w, v - w⟫ < ⟪v, v - w⟫ := by
  rw [← sub_pos, ← inner_sub_left, real_inner_self_eq_norm_sq]
  have : 0 < ‖v - w‖ := norm_pos_iff.mpr (sub_ne_zero.mpr h)
  positivity

theorem ord08 {o E₁ E₂ E₃ : ℝ³} (hE : det3 E₁ E₂ E₃ ≠ 0) {θ : Fin 6 → ℝ}
    (hθ : ∀ k, 0 < ineq08 θ k) (i : Fin 3) :
    (grp08 i).Ordered (nfShape08 o E₁ E₂ E₃ θ) := by
  have hinj := nf_inj6 (o := o) hE hθ
  have p1 := hθ 1; have p5 := hθ 5
  simp only [ineq08, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Matrix.head_cons] at p1 p5
  fin_cases i
  · exact inner_lt08 (fun h => absurd (hinj (a₁ := 4) (a₂ := 1) h) (by decide))
  · refine inner_lt08 (fun h => ?_)
    have := nfinj08 hE (θ := θ) 2 6 h 1
    simp [cp08] at this
  · trivial

theorem nws_Q {zd za zb zc a g : ℝ} (ha : 0 < a) (hg : 0 < g) (hag : 1 < a + g)
    (hb : zb = zd + a * (za - zd) + g * (zc - zd)) (h1 : zd ≠ za) (h2 : zd ≠ zc) :
    NWS4 (quad zd za zb zc) := by
  simp only [NWS4, quad_0, quad_1, quad_2, quad_3]
  have key : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → (a - 1) * x + g * y ≤ 0 → a * x + (g - 1) * y ≤ 0 → x = 0 := by
    intro x y hx hy e1 e2
    rcases le_or_gt 1 g with hg1 | hg1
    · nlinarith [mul_nonneg hx hy, mul_nonneg ha.le hx, mul_nonneg hg.le hy]
    · nlinarith [mul_nonneg hx hy, mul_nonneg ha.le hx, mul_nonneg hg.le hy]
  constructor
  · by_contra h
    push_neg at h
    obtain ⟨h1', h2', h3', h4'⟩ := h
    apply h1
    have := key (zd - za) (zd - zc) (by linarith) (by linarith) (by nlinarith) (by nlinarith)
    linarith
  · by_contra h
    push_neg at h
    obtain ⟨h1', h2', h3', h4'⟩ := h
    apply h1
    have := key (za - zd) (zc - zd) (by linarith) (by linarith) (by nlinarith) (by nlinarith)
    linarith

theorem mf08_Q (o E₁ E₂ E₃ : ℝ³) (θ : Fin 6 → ℝ) (hθ : ∀ k, 0 < ineq08 θ k) (s : Bool)
    (L : ℝ³ →L[ℝ] ℝ³) (hinj : ∀ j, Function.Injective
      ((test08 2 s j).depth (mapShape L (nfShape08 o E₁ E₂ E₃ θ)))) :
    ∃ j, IsCyclicUnimodal ((test08 2 s j).depth (mapShape L (nfShape08 o E₁ E₂ E₃ θ))) := by
  have p2 := hθ 2; have p3 := hθ 3; have p7 := hθ 7
  simp only [ineq08, Matrix.cons_val_one, Matrix.cons_val, Matrix.head_cons] at p2 p3 p7
  set y := mapShape L (nfShape08 o E₁ E₂ E₃ θ) with hy
  have rel : y 3 = y 6 + θ 2 • (y 0 - y 6) + θ 3 • (y 4 - y 6) := by
    simp only [hy, mapShape, nfShape08, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
      Matrix.head_cons, map_add, map_smul]
    module
  have hQ : ∀ u : ℝ³, Function.Injective (fun i : ZMod 4 => ⟪y ((![6, 0, 3, 4] : Fin 4 → Fin 7) i), u⟫) →
      IsCyclicUnimodal (fun i : ZMod 4 => ⟪y ((![6, 0, 3, 4] : Fin 4 → Fin 7) i), u⟫) := by
    intro u hi
    have h01 : ⟪y 6, u⟫ ≠ ⟪y 0, u⟫ := fun h => by
      have := hi (a₁ := (0 : ZMod 4)) (a₂ := 1) (by simpa using h); exact absurd this (by decide)
    have h03 : ⟪y 6, u⟫ ≠ ⟪y 4, u⟫ := fun h => by
      have := hi (a₁ := (0 : ZMod 4)) (a₂ := 3) (by simpa using h); exact absurd this (by decide)
    have hb : ⟪y 3, u⟫ = ⟪y 6, u⟫ + θ 2 * (⟪y 0, u⟫ - ⟪y 6, u⟫) + θ 3 * (⟪y 4, u⟫ - ⟪y 6, u⟫) := by
      rw [rel]; simp only [inner_add_left, inner_smul_left, inner_sub_left]; simp
    have hN := nws_Q p2 p3 (by linarith) hb h01 h03
    have e : (fun i : ZMod 4 => ⟪y ((![6, 0, 3, 4] : Fin 4 → Fin 7) i), u⟫) =
        quad ⟪y 6, u⟫ ⟪y 0, u⟫ ⟪y 3, u⟫ ⟪y 4, u⟫ := by
      funext i
      rcases zmod4_cases i with rfl | rfl | rfl | rfl <;> simp [quad_0, quad_1, quad_2, quad_3]
    rw [e] at hi ⊢
    exact isCyclicUnimodal_of_NWS4 hi hN
  refine ⟨true, ?_⟩
  cases s
  · have h := hinj true
    rw [show test08 2 false true = (LabTest.quad (fun y => y 2 - y 6) 6 0 3 4).neg from rfl] at h ⊢
    exact hQ _ h
  · have h := hinj true
    rw [show test08 2 true true = LabTest.quad (fun y => y 2 - y 6) 6 0 3 4 from rfl] at h ⊢
    exact hQ _ h


theorem detMap_eq08 (L : ℝ³ →L[ℝ] ℝ³) : detMap L = LinearMap.det (L : ℝ³ →ₗ[ℝ] ℝ³) := by
  rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis, Matrix.det_fin_three]
  simp only [detMap, det3_expand, LinearMap.toMatrix_apply]
  simp [EuclideanSpace.basisFun_apply]
  ring

theorem depth_neg08 (i : Fin 3) (j : Bool) (y : Fin 7 → ℝ³) :
    (test08 i false j).depth y = fun k => -(test08 i true j).depth y k := by
  funext k
  simp [test08, LabTest.depth, LabTest.neg]



theorem N2_core (o E₁ E₂ E₃ : ℝ³) (hE : det3 E₁ E₂ E₃ ≠ 0) (θ : Fin 6 → ℝ)
    (hθ : ∀ k, 0 < ineq08 θ k) (h6 : 1 < θ 5) (L : ℝ³ →L[ℝ] ℝ³)
    (hL : LinearMap.det (L : ℝ³ →ₗ[ℝ] ℝ³) = 1)
    (hinj : ∀ j, Function.Injective ((test08 0 true j).depth (nfShape08 (L o) (L E₁) (L E₂) (L E₃) θ))) :
    ∃ j, IsCyclicUnimodal ((test08 0 true j).depth (nfShape08 (L o) (L E₁) (L E₂) (L E₃) θ)) := by
  have hE' : det3 (L E₁) (L E₂) (L E₃) ≠ 0 := by
    rw [det3_map, detMap_eq08, hL, one_mul]; exact hE
  obtain ⟨N⟩ := norm08_of_nf (o := L o) hE' hθ
  set x := nfShape08 (L o) (L E₁) (L E₂) (L E₃) θ with hx
  have hnd := N.F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨haa', hab, hab', hac, hac'⟩, ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩,
    ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd
  have hfc : N.F.abc'.f (x 4) < 0 := N.F.abc'.neg _ (by simp) (Ne.symm hac) (Ne.symm hbc) hcc'
  have hfar : N.F.abc'.f (x 1) < N.F.abc'.f (x 4) := by
    have hp := facet_prop08 N.F.abc' (x 4) (x 1)
    have d1 : det3 (x 2 - x 0) (x 5 - x 0) (x 4 - x 0) = _ := det3_nf08 (L o) (L E₁) (L E₂) (L E₃) θ 0 2 5 4
    have d2 : det3 (x 2 - x 0) (x 5 - x 0) (x 1 - x 0) = _ := det3_nf08 (L o) (L E₁) (L E₂) (L E₃) θ 0 2 5 1
    rw [d1, d2] at hp
    have hA : fc08 θ 0 2 5 4 = 1 - θ 0 - θ 1 := by simp only [fc08, cdet, cp08]; simp; ring
    have hB : fc08 θ 0 2 5 1 = θ 5 * (1 - θ 0 - θ 1) := by simp only [fc08, cdet, cp08]; simp; ring
    have e1 : 0 < θ 0 + θ 1 - 1 := hθ 6
    have hD : det3 (L E₁) (L E₂) (L E₃) * (1 - θ 0 - θ 1) ≠ 0 := mul_ne_zero hE' (by linarith)
    rw [hA, hB] at hp
    have : N.F.abc'.f (x 1) = θ 5 * N.F.abc'.f (x 4) := by
      apply mul_right_cancel₀ hD; linear_combination hp
    rw [this]; nlinarith
  have e0 : (test08 0 true true).depth x = quad ⟪x 4, x 4 - x 1⟫ ⟪x 2, x 4 - x 1⟫ ⟪x 5, x 4 - x 1⟫ ⟪x 3, x 4 - x 1⟫ := by
    funext i; rcases zmod4_cases i with rfl | rfl | rfl | rfl <;> rfl
  have e1 : (test08 0 true false).depth x = quad ⟪x 1, x 4 - x 1⟫ ⟪x 2, x 4 - x 1⟫ ⟪x 5, x 4 - x 1⟫ ⟪x 3, x 4 - x 1⟫ := by
    funext i; rcases zmod4_cases i with rfl | rfl | rfl | rfl <;> rfl
  have hi0 := hinj true
  have hi1 := hinj false
  rw [e0] at hi0
  rw [e1] at hi1
  by_cases hc : IsCyclicUnimodal (quad ⟪x 4, x 4 - x 1⟫ ⟪x 2, x 4 - x 1⟫ ⟪x 5, x 4 - x 1⟫ ⟪x 3, x 4 - x 1⟫)
  · exact ⟨true, by rw [e0]; exact hc⟩
  refine ⟨false, ?_⟩
  rw [e1]
  have hN : ¬ NWS4 (quad ⟪x 4, x 4 - x 1⟫ ⟪x 2, x 4 - x 1⟫ ⟪x 5, x 4 - x 1⟫ ⟪x 3, x 4 - x 1⟫) :=
    fun h => hc (isCyclicUnimodal_of_NWS4 hi0 h)
  obtain ⟨hq₂, hgood⟩ := type08_lemma7 N.F N.G N.hκa N.hκb N.hκc N.hU hfar
  have htouch : ¬ (⟪x 2, x 4 - x 1⟫ = ⟪x 5, x 4 - x 1⟫ ∧ ⟪x 3, x 4 - x 1⟫ = ⟪x 5, x 4 - x 1⟫) := fun h => by
    have := hi0 (a₁ := (1 : ZMod 4)) (a₂ := 2) (by simpa [quad] using h.1)
    exact absurd this (by decide : ¬ ((1 : ZMod 4) = 2))
  exact isCyclicUnimodal_of_NWS4 hi1 (nws4_closing_oct N.F.swap₁.perm₂₃ hfar hq₂ hN hgood htouch)



theorem T4_core (o E₁ E₂ E₃ : ℝ³) (hE : det3 E₁ E₂ E₃ ≠ 0) (θ : Fin 6 → ℝ)
    (hθ : ∀ k, 0 < ineq08 θ k) (L : ℝ³ →L[ℝ] ℝ³)
    (hL : LinearMap.det (L : ℝ³ →ₗ[ℝ] ℝ³) = 1)
    (hinj : ∀ j, Function.Injective ((test08 1 true j).depth (nfShape08 (L o) (L E₁) (L E₂) (L E₃) θ))) :
    ∃ j, IsCyclicUnimodal ((test08 1 true j).depth (nfShape08 (L o) (L E₁) (L E₂) (L E₃) θ)) := by
  have hE' : det3 (L E₁) (L E₂) (L E₃) ≠ 0 := by
    rw [det3_map, detMap_eq08, hL, one_mul]; exact hE
  obtain ⟨N⟩ := norm08_of_nf (o := L o) hE' hθ
  set x := nfShape08 (L o) (L E₁) (L E₂) (L E₃) θ with hx
  obtain ⟨p0, p1, p2, p3, p4, p5, -, -, -, hga, -⟩ := common08 θ hθ
  have hb' : x 3 = x 6 + θ 2 • (x 0 - x 6) + θ 3 • (x 4 - x 6) := by
    simp only [hx, nfShape08, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
      Matrix.head_cons]; module
  have hc' : x 5 = x 6 + θ 0 • (x 0 - x 6) + θ 1 • (x 2 - x 6) := by
    simp only [hx, nfShape08, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
      Matrix.head_cons]; module
  have ha' : x 1 = x 6 + θ 4 • (x 2 - x 6) + θ 5 • (x 4 - x 6) := by
    simp only [hx, nfShape08, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
      Matrix.head_cons]; module
  have hEd : det3 (x 0 - x 6) (x 4 - x 6) (x 2 - x 6) ≠ 0 := by
    have d : det3 (x 0 - x 6) (x 4 - x 6) (x 2 - x 6) = _ := det3_nf08 (L o) (L E₁) (L E₂) (L E₃) θ 6 0 4 2
    rw [d]
    have : fc08 θ 6 0 4 2 = -1 := by simp only [fc08, cdet, cp08]; simp <;> ring
    rw [this]; simpa using hE'
  have hopp : det3 (x 2 - x 6) (x 3 - x 6) (x 4 - x 6) * det3 (x 2 - x 6) (x 3 - x 6) (x 5 - x 6) < 0 := by
    have d1 : det3 (x 2 - x 6) (x 3 - x 6) (x 4 - x 6) = _ := det3_nf08 (L o) (L E₁) (L E₂) (L E₃) θ 6 2 3 4
    have d2 : det3 (x 2 - x 6) (x 3 - x 6) (x 5 - x 6) = _ := det3_nf08 (L o) (L E₁) (L E₂) (L E₃) θ 6 2 3 5
    have c1 : fc08 θ 6 2 3 4 = -θ 2 := by simp only [fc08, cdet, cp08]; simp <;> ring
    have c2 : fc08 θ 6 2 3 5 = θ 0 * θ 3 := by simp only [fc08, cdet, cp08]; simp; ring
    rw [d1, d2, c1, c2]
    have := mul_pos (mul_pos p2 p0) p3
    have := mul_self_pos.mpr hE'
    nlinarith
  have hgood := type08_t4_not_bad N.F.isOctahedron N.F N.hd N.G N.hκa N.hκb N.hκc N.hU hopp
  have e0 : (test08 1 true true).depth x = quad ⟪x 2, x 2 - x 6⟫ ⟪x 5, x 2 - x 6⟫ ⟪x 3, x 2 - x 6⟫ ⟪x 4, x 2 - x 6⟫ := by
    funext i; rcases zmod4_cases i with rfl | rfl | rfl | rfl <;> rfl
  have e1 : (test08 1 true false).depth x = quad ⟪x 6, x 2 - x 6⟫ ⟪x 5, x 2 - x 6⟫ ⟪x 3, x 2 - x 6⟫ ⟪x 4, x 2 - x 6⟫ := by
    funext i; rcases zmod4_cases i with rfl | rfl | rfl | rfl <;> rfl
  have hi0 := hinj true
  have hi1 := hinj false
  rw [e0] at hi0
  rw [e1] at hi1
  by_cases hc : IsCyclicUnimodal (quad ⟪x 2, x 2 - x 6⟫ ⟪x 5, x 2 - x 6⟫ ⟪x 3, x 2 - x 6⟫ ⟪x 4, x 2 - x 6⟫)
  · exact ⟨true, by rw [e0]; exact hc⟩
  refine ⟨false, ?_⟩
  rw [e1]
  have hN : ¬ NWS4 (quad ⟪x 2, x 2 - x 6⟫ ⟪x 5, x 2 - x 6⟫ ⟪x 3, x 2 - x 6⟫ ⟪x 4, x 2 - x 6⟫) :=
    fun h => hc (isCyclicUnimodal_of_NWS4 hi0 h)
  have htouch : ¬ (⟪x 4, x 2 - x 6⟫ = ⟪x 3, x 2 - x 6⟫ ∧ ⟪x 5, x 2 - x 6⟫ = ⟪x 3, x 2 - x 6⟫) := fun h => by
    have := hi0 (a₁ := (3 : ZMod 4)) (a₂ := 2) (by simpa [quad] using h.1)
    exact absurd this (by decide : ¬ ((3 : ZMod 4) = 2))
  have hκ : 0 < θ 2 + θ 0 * (θ 3 - 1) := by nlinarith [mul_pos p1 p2]
  exact isCyclicUnimodal_of_NWS4 hi1 (t4_closing hb' hc' ha' N.hd.ne.2.2.1 hEd p2 p3 p0 p1 hκ hgood htouch hN)


/-- **MF for N2** (proved: `N2_core`): `norm08_of_nf` on `mapShape L (nfShape08 ..)` (frame `L o, L E_i`),
`type08_lemma7` + `nws4_closing_oct`, and NWS4 ⇔ unimodal for distinct depths. -/
theorem mf08_N2 (o E₁ E₂ E₃ : ℝ³) (hE : det3 E₁ E₂ E₃ ≠ 0) (θ : Fin 6 → ℝ)
    (hθ : ∀ k, 0 < ineq08 θ k) (hg : MvPolynomial.eval θ genPoly08 ≠ 0) (s : Bool)
    (h6 : 1 < θ 5) :
    ∀ L : ℝ³ →L[ℝ] ℝ³, LinearMap.det (L : ℝ³ →ₗ[ℝ] ℝ³) = 1 →
      (∀ j, Function.Injective ((test08 0 s j).depth (mapShape L (nfShape08 o E₁ E₂ E₃ θ)))) →
        ∃ j, IsCyclicUnimodal ((test08 0 s j).depth (mapShape L (nfShape08 o E₁ E₂ E₃ θ))) := by
  intro L hL hinj
  rw [mapShape_nfShape08] at hinj ⊢
  cases s
  · have hinj' : ∀ j, Function.Injective ((test08 0 true j).depth (nfShape08 (L o) (L E₁) (L E₂) (L E₃) θ)) := by
      intro j a b h
      have := hinj j
      rw [depth_neg08] at this
      exact this (by simpa using h)
    obtain ⟨j, hj⟩ := N2_core o E₁ E₂ E₃ hE θ hθ h6 L hL hinj'
    refine ⟨j, ?_⟩
    rw [depth_neg08]
    exact IsCyclicUnimodal.neg' (by cases j <;> (show 2 ≤ 4; norm_num)) hj
  · exact N2_core o E₁ E₂ E₃ hE θ hθ h6 L hL hinj

/-- **MF for T4** (proved: `T4_core`): `t4_closing` in the frame coordinates. -/
theorem mf08_T4 (o E₁ E₂ E₃ : ℝ³) (hE : det3 E₁ E₂ E₃ ≠ 0) (θ : Fin 6 → ℝ)
    (hθ : ∀ k, 0 < ineq08 θ k) (hg : MvPolynomial.eval θ genPoly08 ≠ 0) (s : Bool)
    (h6 : θ 5 < 1) (h0 : 1 < θ 0) :
    ∀ L : ℝ³ →L[ℝ] ℝ³, LinearMap.det (L : ℝ³ →ₗ[ℝ] ℝ³) = 1 →
      (∀ j, Function.Injective ((test08 1 s j).depth (mapShape L (nfShape08 o E₁ E₂ E₃ θ)))) →
        ∃ j, IsCyclicUnimodal ((test08 1 s j).depth (mapShape L (nfShape08 o E₁ E₂ E₃ θ))) := by
  intro L hL hinj
  rw [mapShape_nfShape08] at hinj ⊢
  cases s
  · have hinj' : ∀ j, Function.Injective ((test08 1 true j).depth (nfShape08 (L o) (L E₁) (L E₂) (L E₃) θ)) := by
      intro j a b h
      have := hinj j
      rw [depth_neg08] at this
      exact this (by simpa using h)
    obtain ⟨j, hj⟩ := T4_core o E₁ E₂ E₃ hE θ hθ L hL hinj'
    refine ⟨j, ?_⟩
    rw [depth_neg08]
    exact IsCyclicUnimodal.neg' (by cases j <;> (show 2 ≤ 4; norm_num)) hj
  · exact T4_core o E₁ E₂ E₃ hE θ hθ L hL hinj

/-- **The MF part of B1** (RESIDUAL): at every unimodular metric, distinct depths of the rims of the
chosen group give a unimodal rim.  N2 (`i = 0`): `type08_lemma7` + `nws4_closing_oct` through
`norm08_of_nf` on `mapShape L (nfShape08 ..)`; T4 (`i = 1`): `t4_closing`; Q (`i = 2`): the rim is a
planar convex quadrilateral. -/
theorem mf08 (o E₁ E₂ E₃ : ℝ³) (hE : det3 E₁ E₂ E₃ ≠ 0) (θ : Fin 6 → ℝ)
    (hθ : ∀ k, 0 < ineq08 θ k) (hg : MvPolynomial.eval θ genPoly08 ≠ 0) (i : Fin 3) (s : Bool)
    (hcase : (i = 0 ∧ 1 < θ 5) ∨ (i = 1 ∧ θ 5 < 1 ∧ 1 < θ 0) ∨ (i = 2 ∧ θ 5 < 1 ∧ θ 0 < 1)) :
    ∀ L : ℝ³ →L[ℝ] ℝ³, LinearMap.det (L : ℝ³ →ₗ[ℝ] ℝ³) = 1 →
      (∀ j, Function.Injective ((test08 i s j).depth (mapShape L (nfShape08 o E₁ E₂ E₃ θ)))) →
        ∃ j, IsCyclicUnimodal ((test08 i s j).depth (mapShape L (nfShape08 o E₁ E₂ E₃ θ))) := by
  rcases hcase with ⟨rfl, h6⟩ | ⟨rfl, h6, h0⟩ | ⟨rfl, h6, h0⟩
  · exact mf08_N2 o E₁ E₂ E₃ hE θ hθ hg s h6
  · exact mf08_T4 o E₁ E₂ E₃ hE θ hθ hg s h6 h0
  · intro L _ hinj
    exact mf08_Q o E₁ E₂ E₃ θ hθ s L hinj

/-- **B1 (MF + polygon part, affine).**  A generic type-08 shape (`θ` in the region, `genPoly08 θ ≠ 0`,
any frame) has a group `i` and sign `s` such that all tests of the group have the polygon part at the
sign-`s` view, and MF holds at every unimodular metric (every `mapShape L y`): if all rims of the
group have distinct depths one of them is unimodal; moreover edge groups are ordered `z_w < z_v`.
Wiring of `type08_lemma6/7`, `nws4_closing_oct`, `t4_closing`, `Type08Cases`; MF is automatic because
those lemmas hold at every shape in ℝ³, and `mapShape L y` is again a type-08 shape. -/
theorem cert08_pre (o E₁ E₂ E₃ : ℝ³) (hE : det3 E₁ E₂ E₃ ≠ 0) (θ : Fin 6 → ℝ)
    (hθ : ∀ k, 0 < ineq08 θ k) (hg : MvPolynomial.eval θ genPoly08 ≠ 0) :
    ∃ (i : Fin 3) (s : Bool),
      (∀ j, RimGeom (nfShape08 o E₁ E₂ E₃ θ) ((test08 i s j).view (nfShape08 o E₁ E₂ E₃ θ))
        (test08 i s j).lab) ∧
      (∀ L : ℝ³ →L[ℝ] ℝ³, LinearMap.det (L : ℝ³ →ₗ[ℝ] ℝ³) = 1 →
        (∀ j, Function.Injective ((test08 i s j).depth (mapShape L (nfShape08 o E₁ E₂ E₃ θ)))) →
          ∃ j, IsCyclicUnimodal ((test08 i s j).depth (mapShape L (nfShape08 o E₁ E₂ E₃ θ)))) ∧
      (grp08 i).Ordered (nfShape08 o E₁ E₂ E₃ θ) := by
  obtain ⟨i, s, hc, hp⟩ := poly08 o E₁ E₂ E₃ hE θ hθ hg
  exact ⟨i, s, hp, mf08 o E₁ E₂ E₃ hE θ hθ hg i s hc, ord08 hE hθ i⟩

/-- The group `i` with the sign `s` absorbed into the view (for `s = false` the roles of `v, w` are
swapped, so that `Ordered` and `Straddle` are those of the unsigned group). -/
def grpS : Fin 3 → Bool → ViewGroup 7
  | 0, true => grp08 0
  | 0, false => .edge (fun y => -(y 4 - y 1)) 1 4 2 5 3
  | 1, true => grp08 1
  | 1, false => .edge (fun y => -(y 2 - y 6)) 6 2 5 3 4
  | 2, true => grp08 2
  | 2, false => .single (LabTest.quad (fun y => -(y 2 - y 6)) 6 0 3 4)

theorem grpS_view (i : Fin 3) (s : Bool) : (grpS i s).view = (test08 i s true).view := by
  fin_cases i <;> cases s <;> rfl

theorem test_mem_grpS (i : Fin 3) (s : Bool) (j : Bool) : test08 i s j ∈ (grpS i s).tests := by
  fin_cases i <;> cases s <;> cases j <;>
    (simp only [grpS, grp08, ViewGroup.tests, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false]
     first | exact Or.inl rfl | exact Or.inr rfl | exact Or.inr (Or.inl rfl) | rfl)

theorem grpS_tests (i : Fin 3) (s : Bool) : ∀ T ∈ (grpS i s).tests, ∃ j, T = test08 i s j := by
  intro T hT
  fin_cases i <;> cases s <;>
    (simp only [grpS, grp08, ViewGroup.tests, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hT
     first
       | (rcases hT with rfl | rfl
          · first | exact ⟨true, rfl⟩ | exact ⟨false, rfl⟩
          · first | exact ⟨true, rfl⟩ | exact ⟨false, rfl⟩)
       | (subst hT; exact ⟨true, rfl⟩))

theorem grpS_true (i : Fin 3) : grpS i true = grp08 i := by fin_cases i <;> rfl

theorem grpS_false_view (i : Fin 3) (y : Fin 7 → ℝ³) : (grpS i false).view y = -(grp08 i).view y := by
  fin_cases i <;> rfl

theorem test08_neg (i : Fin 3) (j : Bool) : test08 i false j = (test08 i true j).neg := by
  simp [test08]

theorem test_mem_grp08 (i : Fin 3) (j : Bool) : test08 i true j ∈ (grp08 i).tests := by
  have := test_mem_grpS i true j
  rwa [grpS_true] at this

theorem grpS_ordered {y : Fin 7 → ℝ³} (i : Fin 3) (s : Bool) (h : (grp08 i).Ordered y) :
    (grpS i s).Ordered y := by
  cases s
  · fin_cases i
    · simp only [grpS, ViewGroup.Ordered, grp08] at h ⊢
      simp only [inner_neg_right]; linarith
    · simp only [grpS, ViewGroup.Ordered, grp08] at h ⊢
      simp only [inner_neg_right]; linarith
    · trivial
  · rwa [grpS_true]

theorem grpS_straddle {y : Fin 7 → ℝ³} (i : Fin 3) (s : Bool) (h : (grpS i s).Straddle y) :
    (grp08 i).Straddle y := by
  cases s
  · fin_cases i
    · simp only [grpS, ViewGroup.Straddle, grp08, inner_neg_right] at h ⊢
      obtain ⟨h1, h2, h3, h4⟩ := h
      exact ⟨by linarith, by linarith, by linarith, by linarith⟩
    · simp only [grpS, ViewGroup.Straddle, grp08, inner_neg_right] at h ⊢
      obtain ⟨h1, h2, h3, h4⟩ := h
      exact ⟨by linarith, by linarith, by linarith, by linarith⟩
    · exact absurd h (by simp [grpS, ViewGroup.Straddle])
  · rwa [grpS_true] at h

theorem grpS_hk (i : Fin 3) (s : Bool) : ∀ T, grpS i s = ViewGroup.single T → 4 ≤ T.k := by
  intro T h
  fin_cases i <;> cases s <;> simp [grpS, grp08] at h <;> (subst h; exact le_refl 4)

theorem grpS_lab_inj (i : Fin 3) (s : Bool) : ∀ T ∈ (grpS i s).tests, Function.Injective T.lab := by
  intro T hT
  obtain ⟨j, rfl⟩ := grpS_tests i s T hT
  fin_cases i <;> cases s <;> cases j <;>
    (intro a b h; revert a b; decide)

theorem grpS_cover {y : Fin 7 → ℝ³} (i : Fin 3) (s : Bool) {R : Fin 7 → Fin 7 → Prop}
    (hc : ∀ T ∈ (grp08 i).tests, ∀ a b : ZMod T.k, T.depth y a = T.depth y b →
      Relation.EqvGen R (T.lab a) (T.lab b)) :
    ∀ T ∈ (grpS i s).tests, ∀ a b : ZMod T.k, T.depth y a = T.depth y b →
      Relation.EqvGen R (T.lab a) (T.lab b) := by
  intro T hT
  obtain ⟨j, rfl⟩ := grpS_tests i s T hT
  cases s
  · intro a b h
    refine hc (test08 i true j) (test_mem_grp08 i j) a b ?_
    have h' : ⟪y ((test08 i true j).lab a), -(test08 i true j).view y⟫ =
        ⟪y ((test08 i true j).lab b), -(test08 i true j).view y⟫ := h
    simpa [LabTest.depth] using h'
  · exact hc _ (test_mem_grp08 i j)

theorem tieIndep_comp08 {q q' : ℕ} {d u : Fin q → ℝ³} (h : TieIndep d u) (e : Fin q' → Fin q)
    (he : Function.Injective e) : TieIndep (fun k => d (e k)) (fun k => u (e k)) := by
  classical
  intro lam' hl
  have key := h (Function.extend e lam' 0) (by
    intro G
    have := hl G
    rw [← this]
    calc _ = ∑ t ∈ Finset.univ.image e, Function.extend e lam' 0 t * (⟪d t, G (u t)⟫ + ⟪u t, G (d t)⟫) := by
          symm
          apply Finset.sum_subset (Finset.subset_univ _)
          intro t _ ht
          have : ¬ ∃ k, e k = t := by simpa using ht
          rw [Function.extend_apply' _ _ _ this]; simp
      _ = ∑ k, Function.extend e lam' 0 (e k) * (⟪d (e k), G (u (e k))⟫ + ⟪u (e k), G (d (e k))⟫) :=
          Finset.sum_image (fun a _ b _ hab => he hab)
      _ = _ := Finset.sum_congr rfl (fun k _ => by rw [he.extend_apply]))
  funext k
  have := congrFun key (e k)
  rwa [he.extend_apply] at this

theorem tieIndep_neg08 {q : ℕ} {d u : Fin q → ℝ³} (h : TieIndep d u) : TieIndep d (fun t => -u t) := by
  intro lam hl
  apply h lam
  intro G
  have := hl G
  simp only [map_neg, inner_neg_right, inner_neg_left] at this
  rw [← neg_eq_zero, ← this, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl (fun t _ => by ring)


/-- **B2 (certificate of a generic shape with ≤ 2 ties).**  Combine B1 with R2T
(`robust_corner_rim_of_MF`, applied to the group `i`, signs absorbed): the polygon part plus a robust
rim gives `RimCertAt`.  `ties` are the listed ties (≤ 2, independent, covering the group's rim ties);
the straddling far triple at `y` is excluded by `hnoStraddle` (it is a tie at the limit by
closedness, i.e. a touching: `Touch`, which `isRupert_type08_limit_hdn` assumes absent). -/
theorem cert08_generic (o E₁ E₂ E₃ : ℝ³) (hE : det3 E₁ E₂ E₃ ≠ 0) (θ : Fin 6 → ℝ)
    (hθ : ∀ k, 0 < ineq08 θ k) (hg : MvPolynomial.eval θ genPoly08 ≠ 0)
    {q : ℕ} (hq : q ≤ 2) (ties : Fin q → Fin 3 × Fin 7 × Fin 7)
    (hties : ∀ t, ⟪nfShape08 o E₁ E₂ E₃ θ (ties t).2.1 - nfShape08 o E₁ E₂ E₃ θ (ties t).2.2,
      (grp08 (ties t).1).view (nfShape08 o E₁ E₂ E₃ θ)⟫ = 0)
    (hind : TieIndep (fun t => nfShape08 o E₁ E₂ E₃ θ (ties t).2.1 - nfShape08 o E₁ E₂ E₃ θ (ties t).2.2)
      (fun t => (grp08 (ties t).1).view (nfShape08 o E₁ E₂ E₃ θ)))
    (hcover : ∀ i, ∀ T ∈ (grp08 i).tests, ∀ a b : ZMod T.k,
      T.depth (nfShape08 o E₁ E₂ E₃ θ) a = T.depth (nfShape08 o E₁ E₂ E₃ θ) b →
      Relation.EqvGen (fun p p' => ∃ t, (ties t).1 = i ∧ (ties t).2 = (p, p')) (T.lab a) (T.lab b))
    (hnoStraddle : ∀ i, ¬ (grp08 i).Straddle (nfShape08 o E₁ E₂ E₃ θ)) :
    ∃ i s j, (test08 i s j).Cert (nfShape08 o E₁ E₂ E₃ θ) := by
  classical
  obtain ⟨i, s, hgeom, hMF, hord⟩ := cert08_pre o E₁ E₂ E₃ hE θ hθ hg
  let S := {t : Fin q // (ties t).1 = i}
  let n := Fintype.card S
  let e : Fin n ≃ S := (Fintype.equivFin S).symm
  let t' : Fin n → Fin q := fun k => (e k).1
  have ht'inj : Function.Injective t' := fun a b h => e.injective (Subtype.ext h)
  have hn : n ≤ 2 := by
    have := Fintype.card_subtype_le (fun t : Fin q => (ties t).1 = i)
    simp only [Fintype.card_fin] at this
    exact this.trans hq
  have ht'i : ∀ k, (ties (t' k)).1 = i := fun k => (e k).2
  let ties' : Fin n → Unit × Fin 7 × Fin 7 := fun k => ((), (ties (t' k)).2)
  have hview : ∀ y : Fin 7 → ℝ³, ∀ (v : ℝ³), ⟪v, (grp08 i).view y⟫ = 0 → ⟪v, (grpS i s).view y⟫ = 0 := by
    intro y v hv
    cases s
    · rw [grpS_false_view, inner_neg_right, hv, neg_zero]
    · rw [grpS_true]; exact hv
  have hties' : ∀ k, ⟪nfShape08 o E₁ E₂ E₃ θ (ties' k).2.1 - nfShape08 o E₁ E₂ E₃ θ (ties' k).2.2,
      ((fun _ : Unit => grpS i s) (ties' k).1).view (nfShape08 o E₁ E₂ E₃ θ)⟫ = 0 := by
    intro k
    apply hview
    have := hties (t' k)
    rw [ht'i k] at this
    exact this
  have hind' : TieIndep (fun k => nfShape08 o E₁ E₂ E₃ θ (ties' k).2.1 - nfShape08 o E₁ E₂ E₃ θ (ties' k).2.2)
      (fun k => ((fun _ : Unit => grpS i s) (ties' k).1).view (nfShape08 o E₁ E₂ E₃ θ)) := by
    have h1 := tieIndep_comp08 hind t' ht'inj
    have eq1 : (fun k => (grp08 (ties (t' k)).1).view (nfShape08 o E₁ E₂ E₃ θ)) =
        fun _ => (grp08 i).view (nfShape08 o E₁ E₂ E₃ θ) := funext (fun k => by rw [ht'i k])
    rw [eq1] at h1
    cases s
    · have h2 := tieIndep_neg08 h1
      have eq2 : (fun _ : Fin n => -(grp08 i).view (nfShape08 o E₁ E₂ E₃ θ)) =
          fun _ => (grpS i false).view (nfShape08 o E₁ E₂ E₃ θ) := funext (fun k => (grpS_false_view i _).symm)
      rw [eq2] at h2
      exact h2
    · rw [grpS_true]; exact h1
  have hcover' : ∀ a : Unit, ∀ T ∈ ((fun _ : Unit => grpS i s) a).tests, ∀ a' b' : ZMod T.k,
      T.depth (nfShape08 o E₁ E₂ E₃ θ) a' = T.depth (nfShape08 o E₁ E₂ E₃ θ) b' →
      Relation.EqvGen (fun p p' => ∃ k, (ties' k).1 = a ∧ (ties' k).2 = (p, p')) (T.lab a') (T.lab b') := by
    intro a T hT a' b' hab
    have := grpS_cover i s (hcover i) T hT a' b' hab
    refine Relation.EqvGen.mono ?_ _ _ this
    intro p p' ⟨t, ht1, ht2⟩
    refine ⟨e.symm ⟨t, ht1⟩, rfl, ?_⟩
    simp only [ties', t']
    rw [Equiv.apply_symm_apply]; exact ht2
  have hMF' : ∀ᶠ L : ℝ³ →L[ℝ] ℝ³ in 𝓝 1, LinearMap.det (L : ℝ³ →ₗ[ℝ] ℝ³) = 1 →
      (∀ a : Unit, ∀ T ∈ ((fun _ : Unit => grpS i s) a).tests,
        Function.Injective (T.depth (mapShape L (nfShape08 o E₁ E₂ E₃ θ)))) →
      ∃ a : Unit, ∃ T ∈ ((fun _ : Unit => grpS i s) a).tests,
        IsCyclicUnimodal (T.depth (mapShape L (nfShape08 o E₁ E₂ E₃ θ))) := by
    refine Filter.Eventually.of_forall (fun L hL hinjall => ?_)
    obtain ⟨j, hj⟩ := hMF L hL (fun j => hinjall () _ (test_mem_grpS i s j))
    exact ⟨(), _, test_mem_grpS i s j, hj⟩
  have R := robust_corner_rim_of_MF (A := Unit) (n := 7) (q := n) (nfShape08 o E₁ E₂ E₃ θ)
    (fun _ => grpS i s) (fun _ => by rw [grpS_view]; exact covView_test08 i s true)
    (fun _ => grpS_ordered i s hord) (fun _ T h => grpS_hk i s T h) (fun _ => grpS_lab_inj i s)
    hn ties' hties' hind' hcover' hMF'
  rcases R with ⟨a, T, hT, hrob⟩ | ⟨a, hst⟩
  · obtain ⟨j, rfl⟩ := grpS_tests i s T hT
    exact ⟨i, s, j, ⟨(hgeom j).1, (hgeom j).2.1, (hgeom j).2.2, hrob⟩⟩
  · exact absurd (grpS_straddle i s hst) (hnoStraddle i)

/-! ### Part C: free closings (dependency on G5a) -/

theorem nws4_of_W (q : Fin 4 → ℝ) (r0 e : Fin 4) (he : e = 1 ∨ e = 3)
    (A0 : ¬ (q (r0 + 1 * e) ≤ q (r0 + 0 * e) ∧ q (r0 + 1 * e) ≤ q (r0 + 2 * e) ∧
      q (r0 + 3 * e) ≤ q (r0 + 0 * e) ∧ q (r0 + 3 * e) ≤ q (r0 + 2 * e)))
    (A1 : ¬ (q (r0 + 2 * e) ≤ q (r0 + 1 * e) ∧ q (r0 + 2 * e) ≤ q (r0 + 3 * e) ∧
      q (r0 + 0 * e) ≤ q (r0 + 1 * e) ∧ q (r0 + 0 * e) ≤ q (r0 + 3 * e))) :
    NWS4 (quad (q 0) (q 1) (q 2) (q 3)) := by
  simp only [NWS4, quad_0, quad_1, quad_2, quad_3]
  rcases he with rfl | rfl <;> fin_cases r0 <;>
  · simp at A0 A1
    by_contra hc
    simp only [not_and, not_or, not_lt] at hc
    grind

theorem step4 (S : ZMod 4 → ZMod 4 → ZMod 4 → ℝ) (hcyc : ∀ a b c, S a b c = S b c a)
    (hsw : ∀ a b c, S a b c = - S a c b)
    (hPS : ∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 → 0 < S i (i + 1) j) (ς : ℝ) (hς : ς = 1 ∨ ς = -1)
    (r r' : ZMod 4) (hne : r' ≠ r) (hl : ∀ j, 0 ≤ ς * S r r' j) :
    (ς = 1 ∧ r' = r + 1) ∨ (ς = -1 ∧ r' = r + 3) := by
  have p02 : 0 < S 0 1 2 := hPS 0 2 (by decide) (by decide)
  have p03 : 0 < S 0 1 3 := hPS 0 3 (by decide) (by decide)
  have p13 : 0 < S 1 2 3 := hPS 1 3 (by decide) (by decide)
  have p10 : 0 < S 1 2 0 := hPS 1 0 (by decide) (by decide)
  have p20 : 0 < S 2 3 0 := hPS 2 0 (by decide) (by decide)
  have p21 : 0 < S 2 3 1 := hPS 2 1 (by decide) (by decide)
  have p31 : 0 < S 3 0 1 := hPS 3 1 (by decide) (by decide)
  have p32 : 0 < S 3 0 2 := hPS 3 2 (by decide) (by decide)
  have c012 := hcyc 0 1 2
  have s012 := hsw 0 1 2
  have c013 := hcyc 0 1 3
  have s013 := hsw 0 1 3
  have c021 := hcyc 0 2 1
  have s021 := hsw 0 2 1
  have c023 := hcyc 0 2 3
  have s023 := hsw 0 2 3
  have c031 := hcyc 0 3 1
  have s031 := hsw 0 3 1
  have c032 := hcyc 0 3 2
  have s032 := hsw 0 3 2
  have c102 := hcyc 1 0 2
  have s102 := hsw 1 0 2
  have c103 := hcyc 1 0 3
  have s103 := hsw 1 0 3
  have c120 := hcyc 1 2 0
  have s120 := hsw 1 2 0
  have c123 := hcyc 1 2 3
  have s123 := hsw 1 2 3
  have c130 := hcyc 1 3 0
  have s130 := hsw 1 3 0
  have c132 := hcyc 1 3 2
  have s132 := hsw 1 3 2
  have c201 := hcyc 2 0 1
  have s201 := hsw 2 0 1
  have c203 := hcyc 2 0 3
  have s203 := hsw 2 0 3
  have c210 := hcyc 2 1 0
  have s210 := hsw 2 1 0
  have c213 := hcyc 2 1 3
  have s213 := hsw 2 1 3
  have c230 := hcyc 2 3 0
  have s230 := hsw 2 3 0
  have c231 := hcyc 2 3 1
  have s231 := hsw 2 3 1
  have c301 := hcyc 3 0 1
  have s301 := hsw 3 0 1
  have c302 := hcyc 3 0 2
  have s302 := hsw 3 0 2
  have c310 := hcyc 3 1 0
  have s310 := hsw 3 1 0
  have c312 := hcyc 3 1 2
  have s312 := hsw 3 1 2
  have c320 := hcyc 3 2 0
  have s320 := hsw 3 2 0
  have c321 := hcyc 3 2 1
  have s321 := hsw 3 2 1
  rcases hς with rfl | rfl <;> rcases zmod4_cases r with rfl | rfl | rfl | rfl <;>
    rcases zmod4_cases r' with rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl hne
    | exact Or.inl ⟨rfl, by decide⟩
    | (exfalso; linarith [hl 0, hl 1, hl 2, hl 3])
    | exact Or.inr ⟨by norm_num, by decide⟩

theorem nws4_of_W' (q : ZMod 4 → ℝ) (r0 e : ZMod 4) (he : e = 1 ∨ e = 3)
    (A0 : ¬ (q (r0 + 1 * e) ≤ q (r0 + 0 * e) ∧ q (r0 + 1 * e) ≤ q (r0 + 2 * e) ∧
      q (r0 + 3 * e) ≤ q (r0 + 0 * e) ∧ q (r0 + 3 * e) ≤ q (r0 + 2 * e)))
    (A1 : ¬ (q (r0 + 2 * e) ≤ q (r0 + 1 * e) ∧ q (r0 + 2 * e) ≤ q (r0 + 3 * e) ∧
      q (r0 + 0 * e) ≤ q (r0 + 1 * e) ∧ q (r0 + 0 * e) ≤ q (r0 + 3 * e))) :
    NWS4 (quad (q 0) (q 1) (q 2) (q 3)) :=
  nws4_of_W (fun i => q i) r0 e he A0 A1

theorem tri_cyc (p q r u : ℝ³) : det3 (q - p) (r - p) u = det3 (r - q) (p - q) u := by
  simp only [det3_expand, PiLp.sub_apply]; ring

theorem tri_sw (p q r u : ℝ³) : det3 (q - p) (r - p) u = - det3 (r - p) (q - p) u := by
  simp only [det3_expand, PiLp.sub_apply]; ring

theorem rim_nws4 {n : ℕ} {x : Fin n → ℝ³} {u : ℝ³} (nat : ZMod 4 → Fin n) (κ : ℝ) (hκ : κ ≠ 0)
    (hPS : ∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
      0 < κ * det3 (x (nat (i + 1)) - x (nat i)) (x (nat j) - x (nat i)) u)
    {k : ℕ} [NeZero k] (σ : ZMod k → ZMod 4) (h : RimCertAt x u (nat ∘ σ)) :
    NWS4 (quad ⟪x (nat 0), u⟫ ⟪x (nat 1), u⟫ ⟪x (nat 2), u⟫ ⟪x (nat 3), u⟫) := by
  classical
  let T : ZMod 4 → ZMod 4 → ZMod 4 → ℝ :=
    fun a b c => det3 (x (nat b) - x (nat a)) (x (nat c) - x (nat a)) u
  let S : ZMod 4 → ZMod 4 → ZMod 4 → ℝ := fun a b c => κ * T a b c
  have hcyc : ∀ a b c, S a b c = S b c a := fun a b c => by simp only [S, T]; rw [tri_cyc]
  have hsw : ∀ a b c, S a b c = - S a c b := fun a b c => by
    simp only [S, T]; rw [tri_sw]; ring
  obtain ⟨ς, hς, hςκ⟩ : ∃ ς : ℝ, (ς = 1 ∨ ς = -1) ∧ ∀ t : ℝ, 0 ≤ t → 0 ≤ ς * (κ * t) := by
    rcases lt_or_gt_of_ne hκ with hk | hk
    · exact ⟨-1, Or.inr rfl, fun t ht => by nlinarith⟩
    · exact ⟨1, Or.inl rfl, fun t ht => by nlinarith⟩
  have hstep : ∀ i : ZMod k, (ς = 1 ∧ σ (i + 1) = σ i + 1) ∨ (ς = -1 ∧ σ (i + 1) = σ i + 3) := by
    intro i
    refine step4 S hcyc hsw hPS ς hς (σ i) (σ (i + 1)) ?_ ?_
    · intro heq
      have := h.lab_injective (a₁ := i + 1) (a₂ := i) (by simp only [Function.comp]; rw [heq])
      exact zmod_sub_one_ne h.three (i + 1) (by simpa using this.symm)
    · intro j
      exact hςκ _ (h.left (nat j) i)
  obtain ⟨e, he, hσe⟩ : ∃ e : ZMod 4, (e = 1 ∨ e = 3) ∧ ∀ i, σ (i + 1) = σ i + e := by
    rcases hς with h1 | h1
    · refine ⟨1, Or.inl rfl, fun i => (hstep i).elim (fun h => h.2) (fun h => ?_)⟩
      exact absurd (h.1.symm.trans h1) (by norm_num)
    · refine ⟨3, Or.inr rfl, fun i => (hstep i).elim (fun h => ?_) (fun h => h.2)⟩
      exact absurd (h.1.symm.trans h1) (by norm_num)
  have hσn : ∀ m : ℕ, σ (m : ZMod k) = σ 0 + (m : ZMod 4) * e := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [Nat.cast_succ, hσe, ih]; push_cast; ring
  have hk4 : 4 ≤ k := by
    by_contra hk
    have hk3 : k = 3 := by have := h.three; omega
    subst hk3
    have h1 := hσn 3
    have h3 : ((3 : ℕ) : ZMod 3) = 0 := by decide
    rw [h3] at h1
    have h3' : ((3 : ℕ) : ZMod 4) * e = 0 := by linear_combination -h1
    rcases he with rfl | rfl <;> revert h3' <;> decide
  have hrob := h.robust
  let q : ZMod 4 → ℝ := fun j => ⟪x (nat j), u⟫
  have hz : ∀ s j : ℕ, ⟪x ((nat ∘ σ) ((s : ZMod k) + (j : ZMod k))), u⟫ =
      q (σ 0 + ((s + j : ℕ) : ZMod 4) * e) := by
    intro s j
    rw [← Nat.cast_add]; simp only [Function.comp, hσn, q]
  have key : ∀ s : ℕ, ¬ (q (σ 0 + ((s + 1 : ℕ) : ZMod 4) * e) ≤ q (σ 0 + ((s + 0 : ℕ) : ZMod 4) * e) ∧
      q (σ 0 + ((s + 1 : ℕ) : ZMod 4) * e) ≤ q (σ 0 + ((s + 2 : ℕ) : ZMod 4) * e) ∧
      q (σ 0 + ((s + 3 : ℕ) : ZMod 4) * e) ≤ q (σ 0 + ((s + 0 : ℕ) : ZMod 4) * e) ∧
      q (σ 0 + ((s + 3 : ℕ) : ZMod 4) * e) ≤ q (σ 0 + ((s + 2 : ℕ) : ZMod 4) * e)) := by
    rintro s ⟨h1, h2, h3, h4⟩
    refine Minimality.CaseC18.rob_weak4 hrob (P0 := (s : ZMod k) + ((0 : ℕ) : ZMod k)) (P1 := (s : ZMod k) + ((1 : ℕ) : ZMod k))
      (P2 := (s : ZMod k) + ((2 : ℕ) : ZMod k)) (P3 := (s : ZMod k) + ((3 : ℕ) : ZMod k))
      ⟨(s : ZMod k), 0, 1, 2, 3, by omega, by omega, by omega, by omega, rfl, rfl, rfl, rfl⟩ ?_ ?_ ?_ ?_
    · show ⟪x ((nat ∘ σ) _), u⟫ ≤ ⟪x ((nat ∘ σ) _), u⟫
      rw [hz, hz]; exact h1
    · show ⟪x ((nat ∘ σ) _), u⟫ ≤ ⟪x ((nat ∘ σ) _), u⟫
      rw [hz, hz]; exact h2
    · show ⟪x ((nat ∘ σ) _), u⟫ ≤ ⟪x ((nat ∘ σ) _), u⟫
      rw [hz, hz]; exact h3
    · show ⟪x ((nat ∘ σ) _), u⟫ ≤ ⟪x ((nat ∘ σ) _), u⟫
      rw [hz, hz]; exact h4
  have A0 := key 0
  have A1 := key 1
  have n1 : ((0 + 1 : ℕ) : ZMod 4) = 1 := by decide
  have n2 : ((0 + 0 : ℕ) : ZMod 4) = 0 := by decide
  have n3 : ((0 + 2 : ℕ) : ZMod 4) = 2 := by decide
  have n4 : ((0 + 3 : ℕ) : ZMod 4) = 3 := by decide
  have m1 : ((1 + 0 : ℕ) : ZMod 4) = 1 := by decide
  have m2 : ((1 + 1 : ℕ) : ZMod 4) = 2 := by decide
  have m3 : ((1 + 2 : ℕ) : ZMod 4) = 3 := by decide
  have m4 : ((1 + 3 : ℕ) : ZMod 4) = 0 := by decide
  rw [n1, n2, n3, n4] at A0
  rw [m1, m2, m3, m4] at A1
  exact nws4_of_W' q (σ 0) e he A0 A1

/-! ### Separating functionals in the frame -/

noncomputable def wv08 (E₁ E₂ E₃ : ℝ³) (α β γ : ℝ) : ℝ³ :=
  (det3 E₁ E₂ E₃ * α) • cross E₂ E₃ + (det3 E₁ E₂ E₃ * β) • cross E₃ E₁ +
    (det3 E₁ E₂ E₃ * γ) • cross E₁ E₂

theorem inner_wv08 (o E₁ E₂ E₃ : ℝ³) (θ : Fin 6 → ℝ) (α β γ : ℝ) (i : Fin 7) :
    ⟪wv08 E₁ E₂ E₃ α β γ, nfShape08 o E₁ E₂ E₃ θ i⟫ = ⟪wv08 E₁ E₂ E₃ α β γ, o⟫ +
      det3 E₁ E₂ E₃ ^ 2 * (α * cp08 θ i 0 + β * cp08 θ i 1 + γ * cp08 θ i 2) := by
  have h1 : ⟪cross E₂ E₃, E₁⟫ = det3 E₁ E₂ E₃ := by
    show det3 E₂ E₃ E₁ = _; simp only [det3_expand]; ring
  have h2 : ⟪cross E₃ E₁, E₂⟫ = det3 E₁ E₂ E₃ := by
    show det3 E₃ E₁ E₂ = _; simp only [det3_expand]; ring
  have h3 : ⟪cross E₁ E₂, E₃⟫ = det3 E₁ E₂ E₃ := rfl
  have z1 := inner_cross_left E₂ E₃
  have z2 := inner_cross_right E₂ E₃
  have z3 := inner_cross_left E₃ E₁
  have z4 := inner_cross_right E₃ E₁
  have z5 := inner_cross_left E₁ E₂
  have z6 := inner_cross_right E₁ E₂
  rw [nf08_coord]
  simp only [wv08, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, h1, h2, h3,
    z1, z2, z3, z4, z5, z6, conj_trivial]
  ring

theorem noRim_of_sep {y : Fin 7 → ℝ³} {u w : ℝ³} (hw : ⟪w, u⟫ = 0) {k : ℕ} [NeZero k]
    {lab : ZMod k → Fin 7} (h : RimCertAt y u lab) (m : Fin 7)
    (hs : ∀ l, ⟪w, y (lab l)⟫ < ⟪w, y m⟫) : False := by
  obtain ⟨i, hi⟩ := h.suppIn m w hw
  exact absurd hi (not_le.2 (hs i))

theorem forall_lab2 (s j : Bool) (P : Fin 7 → Prop) (h6 : P 6) (h0 : P 0) (h3 : P 3) (h4 : P 4) :
    ∀ l, P ((test08 2 s j).lab l) := by
  cases s <;> cases j <;>
  · intro l
    rcases zmod4_cases l with rfl | rfl | rfl | rfl
    exacts [h6, h0, h3, h4]

theorem forall_lab0 (s : Bool) (P : Fin 7 → Prop) (h1 : P 1) (h2 : P 2) (h5 : P 5) (h3 : P 3) :
    ∀ l, P ((test08 0 s false).lab l) := by
  cases s <;>
  · intro l
    rcases zmod4_cases l with rfl | rfl | rfl | rfl
    exacts [h1, h2, h5, h3]

theorem view2 (s j : Bool) (y : Fin 7 → ℝ³) :
    (test08 2 s j).view y = (if s then (1 : ℝ) else -1) • (y 2 - y 6) := by
  cases s <;> cases j <;> simp [test08, grp08, ViewGroup.tests, LabTest.quad, LabTest.neg]

theorem view0 (s j : Bool) (y : Fin 7 → ℝ³) :
    (test08 0 s j).view y = (if s then (1 : ℝ) else -1) • (y 4 - y 1) := by
  cases s <;> cases j <;> simp [test08, grp08, ViewGroup.tests, LabTest.quad, LabTest.neg]

/-! ### Impossibility of the free rims in the wrong regions -/

theorem perp_diff08 (o E₁ E₂ E₃ : ℝ³) (θ : Fin 6 → ℝ) (α β γ : ℝ) (p q : Fin 7)
    (h : α * (cp08 θ p 0 - cp08 θ q 0) + β * (cp08 θ p 1 - cp08 θ q 1) + γ * (cp08 θ p 2 - cp08 θ q 2) = 0)
    (ε : ℝ) :
    ⟪wv08 E₁ E₂ E₃ α β γ, ε • (nfShape08 o E₁ E₂ E₃ θ p - nfShape08 o E₁ E₂ E₃ θ q)⟫ = 0 := by
  rw [inner_smul_right, inner_sub_right, inner_wv08, inner_wv08]
  have : det3 E₁ E₂ E₃ ^ 2 * (α * cp08 θ p 0 + β * cp08 θ p 1 + γ * cp08 θ p 2) -
      det3 E₁ E₂ E₃ ^ 2 * (α * cp08 θ q 0 + β * cp08 θ q 1 + γ * cp08 θ q 2) = 0 := by
    rw [← mul_sub]; convert mul_zero (det3 E₁ E₂ E₃ ^ 2) using 2; linarith
  rw [show ⟪wv08 E₁ E₂ E₃ α β γ, o⟫ + det3 E₁ E₂ E₃ ^ 2 * (α * cp08 θ p 0 + β * cp08 θ p 1 + γ * cp08 θ p 2) -
    (⟪wv08 E₁ E₂ E₃ α β γ, o⟫ + det3 E₁ E₂ E₃ ^ 2 * (α * cp08 θ q 0 + β * cp08 θ q 1 + γ * cp08 θ q 2)) = 0 by linarith]
  simp

theorem impQ_N2 {o E₁ E₂ E₃ : ℝ³} (hE : det3 E₁ E₂ E₃ ≠ 0) {θ : Fin 6 → ℝ}
    (hθ : ∀ k, 0 < ineq08 θ k) (h6 : 1 < θ 5) (s j : Bool) {k' : ℕ} [NeZero k']
    (σ : ZMod k' → ZMod (test08 2 s j).k)
    (h : RimCertAt (nfShape08 o E₁ E₂ E₃ θ) ((test08 2 s j).view (nfShape08 o E₁ E₂ E₃ θ))
      ((test08 2 s j).lab ∘ σ)) : False := by
  obtain ⟨p0, p1, p2, p3, p4, p5, -⟩ := common08 θ hθ
  have hD2 : 0 < det3 E₁ E₂ E₃ ^ 2 := by positivity
  refine noRim_of_sep (w := wv08 E₁ E₂ E₃ (-(θ 3 / θ 2)) 0 1) ?_ h 1 ?_
  · rw [view2]; apply perp_diff08; simp [cp08]
  · intro l
    refine forall_lab2 s j (fun i => ⟪wv08 E₁ E₂ E₃ (-(θ 3 / θ 2)) 0 1, nfShape08 o E₁ E₂ E₃ θ i⟫ <
      ⟪wv08 E₁ E₂ E₃ (-(θ 3 / θ 2)) 0 1, nfShape08 o E₁ E₂ E₃ θ 1⟫) ?_ ?_ ?_ ?_ (σ l)
    all_goals
      simp only [inner_wv08]
      simp [cp08]
      have hq : θ 3 / θ 2 * θ 2 = θ 3 := div_mul_cancel₀ _ p2.ne'
      have hq0 : 0 < θ 3 / θ 2 := div_pos p3 p2
      nlinarith [mul_pos hD2 (show 0 < θ 5 - 1 by linarith), mul_pos hD2 hq0, mul_pos hD2 (show 0 < θ 5 by linarith)]

theorem impQ_T4 {o E₁ E₂ E₃ : ℝ³} (hE : det3 E₁ E₂ E₃ ≠ 0) {θ : Fin 6 → ℝ}
    (hθ : ∀ k, 0 < ineq08 θ k) (h0 : 1 < θ 0) (s j : Bool) {k' : ℕ} [NeZero k']
    (σ : ZMod k' → ZMod (test08 2 s j).k)
    (h : RimCertAt (nfShape08 o E₁ E₂ E₃ θ) ((test08 2 s j).view (nfShape08 o E₁ E₂ E₃ θ))
      ((test08 2 s j).lab ∘ σ)) : False := by
  obtain ⟨p0, p1, p2, p3, p4, p5, -⟩ := common08 θ hθ
  have hD2 : 0 < det3 E₁ E₂ E₃ ^ 2 := by positivity
  refine noRim_of_sep (w := wv08 E₁ E₂ E₃ 1 0 (-(θ 2 / θ 3))) ?_ h 5 ?_
  · rw [view2]; apply perp_diff08; simp [cp08]
  · intro l
    refine forall_lab2 s j (fun i => ⟪wv08 E₁ E₂ E₃ 1 0 (-(θ 2 / θ 3)), nfShape08 o E₁ E₂ E₃ θ i⟫ <
      ⟪wv08 E₁ E₂ E₃ 1 0 (-(θ 2 / θ 3)), nfShape08 o E₁ E₂ E₃ θ 5⟫) ?_ ?_ ?_ ?_ (σ l)
    all_goals
      simp only [inner_wv08]
      simp [cp08]
      have hq : θ 2 / θ 3 * θ 3 = θ 2 := div_mul_cancel₀ _ p3.ne'
      have hq0 : 0 < θ 2 / θ 3 := div_pos p2 p3
      nlinarith [mul_pos hD2 (show 0 < θ 0 - 1 by linarith), mul_pos hD2 hq0, mul_pos hD2 (show 0 < θ 0 by linarith)]

theorem impK_T4 {o E₁ E₂ E₃ : ℝ³} (hE : det3 E₁ E₂ E₃ ≠ 0) {θ : Fin 6 → ℝ}
    (hθ : ∀ k, 0 < ineq08 θ k) (h6 : θ 5 < 1) (s : Bool) {k' : ℕ} [NeZero k']
    (σ : ZMod k' → ZMod (test08 0 s false).k)
    (h : RimCertAt (nfShape08 o E₁ E₂ E₃ θ) ((test08 0 s false).view (nfShape08 o E₁ E₂ E₃ θ))
      ((test08 0 s false).lab ∘ σ)) : False := by
  obtain ⟨p0, p1, p2, p3, p4, p5, -⟩ := common08 θ hθ
  have hD2 : 0 < det3 E₁ E₂ E₃ ^ 2 := by positivity
  refine noRim_of_sep (w := wv08 E₁ E₂ E₃ 0 (θ 5 - 1) (-(θ 4))) ?_ h 6 ?_
  · rw [view0]; apply perp_diff08; simp [cp08]; ring
  · intro l
    refine forall_lab0 s (fun i => ⟪wv08 E₁ E₂ E₃ 0 (θ 5 - 1) (-(θ 4)), nfShape08 o E₁ E₂ E₃ θ i⟫ <
      ⟪wv08 E₁ E₂ E₃ 0 (θ 5 - 1) (-(θ 4)), nfShape08 o E₁ E₂ E₃ θ 6⟫) ?_ ?_ ?_ ?_ (σ l)
    all_goals
      simp only [inner_wv08]
      simp [cp08]
      nlinarith [mul_pos hD2 (show 0 < 1 - θ 5 by linarith), mul_pos hD2 p4, mul_pos hD2 (mul_pos p4 p5),
        mul_pos hD2 (mul_pos p1 (show 0 < 1 - θ 5 by linarith)), mul_pos hD2 (mul_pos p4 p3)]

/-! ### N2: the `K_{a'}` rim -/

theorem nfN2_nws4 {o E₁ E₂ E₃ : ℝ³} (hE : det3 E₁ E₂ E₃ ≠ 0) {θ : Fin 6 → ℝ}
    (hθ : ∀ k, 0 < ineq08 θ k) (h6 : 1 < θ 5) (ε : ℝ) (hε : ε ≠ 0) {k' : ℕ} [NeZero k']
    (σ : ZMod k' → ZMod 4)
    (h : RimCertAt (nfShape08 o E₁ E₂ E₃ θ)
      (ε • (nfShape08 o E₁ E₂ E₃ θ 4 - nfShape08 o E₁ E₂ E₃ θ 1))
      ((fun i : ZMod 4 => (![1, 2, 5, 3] : Fin 4 → Fin 7) i) ∘ σ)) :
    NWS4 (quad ⟪nfShape08 o E₁ E₂ E₃ θ 1, nfShape08 o E₁ E₂ E₃ θ 4 - nfShape08 o E₁ E₂ E₃ θ 1⟫
      ⟪nfShape08 o E₁ E₂ E₃ θ 2, nfShape08 o E₁ E₂ E₃ θ 4 - nfShape08 o E₁ E₂ E₃ θ 1⟫
      ⟪nfShape08 o E₁ E₂ E₃ θ 5, nfShape08 o E₁ E₂ E₃ θ 4 - nfShape08 o E₁ E₂ E₃ θ 1⟫
      ⟪nfShape08 o E₁ E₂ E₃ θ 3, nfShape08 o E₁ E₂ E₃ θ 4 - nfShape08 o E₁ E₂ E₃ θ 1⟫) := by
  have hc := crimA2 θ hθ h6
  have hκ : ε * det3 E₁ E₂ E₃ ≠ 0 := mul_ne_zero hε hE
  have hpos : 0 < (ε * det3 E₁ E₂ E₃) ^ 2 := by positivity
  have key := rim_nws4 (x := nfShape08 o E₁ E₂ E₃ θ) (fun i : ZMod 4 => (![1, 2, 5, 3] : Fin 4 → Fin 7) i)
    (ε * det3 E₁ E₂ E₃) hκ ?_ σ h
  · simp only [inner_smul_right] at key
    have := nws4_quad_scale (inv_ne_zero hε) key
    simpa [← mul_assoc, inv_mul_cancel₀ hε] using this
  · intro i j hi hj
    rw [det3_view08]
    have := hc.1 i j hi hj
    have e : ε * det3 E₁ E₂ E₃ * (ε * (det3 E₁ E₂ E₃ * (fc08 θ ((fun i : ZMod 4 => (![1, 2, 5, 3] : Fin 4 → Fin 7) i) i)
        ((fun i : ZMod 4 => (![1, 2, 5, 3] : Fin 4 → Fin 7) i) (i + 1)) ((fun i : ZMod 4 => (![1, 2, 5, 3] : Fin 4 → Fin 7) i) j) 4 -
        fc08 θ ((fun i : ZMod 4 => (![1, 2, 5, 3] : Fin 4 → Fin 7) i) i)
        ((fun i : ZMod 4 => (![1, 2, 5, 3] : Fin 4 → Fin 7) i) (i + 1)) ((fun i : ZMod 4 => (![1, 2, 5, 3] : Fin 4 → Fin 7) i) j) 1))) =
        (ε * det3 E₁ E₂ E₃) ^ 2 * (1 * (fc08 θ ((fun i : ZMod 4 => (![1, 2, 5, 3] : Fin 4 → Fin 7) i) i)
        ((fun i : ZMod 4 => (![1, 2, 5, 3] : Fin 4 → Fin 7) i) (i + 1)) ((fun i : ZMod 4 => (![1, 2, 5, 3] : Fin 4 → Fin 7) i) j) 4 -
        fc08 θ ((fun i : ZMod 4 => (![1, 2, 5, 3] : Fin 4 → Fin 7) i) i)
        ((fun i : ZMod 4 => (![1, 2, 5, 3] : Fin 4 → Fin 7) i) (i + 1)) ((fun i : ZMod 4 => (![1, 2, 5, 3] : Fin 4 → Fin 7) i) j) 1)) := by ring
    rw [e]; exact mul_pos hpos this

/-! ### Regions from the facets -/

theorem region_gamma6 {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) {o E₁ E₂ E₃ : ℝ³}
    {θ : Fin 6 → ℝ} (hE : det3 E₁ E₂ E₃ ≠ 0) (hθ : ∀ k, 0 < ineq08 θ k)
    (hpts : pts08 a a' b b' c c' d = nfShape08 o E₁ E₂ E₃ θ) :
    N.F.abc'.f a' = θ 5 * N.F.abc'.f c := by
  have hnd := N.F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨haa', hab, hab', hac, hac'⟩, ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩,
    ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd
  have hp := facet_prop08 N.F.abc' c a'
  have d1 : det3 (b - a) (c' - a) (c - a) = det3 E₁ E₂ E₃ * fc08 θ 0 2 5 4 := by
    have := det3_nf08 o E₁ E₂ E₃ θ 0 2 5 4; rw [← hpts] at this; exact this
  have d2 : det3 (b - a) (c' - a) (a' - a) = det3 E₁ E₂ E₃ * fc08 θ 0 2 5 1 := by
    have := det3_nf08 o E₁ E₂ E₃ θ 0 2 5 1; rw [← hpts] at this; exact this
  rw [d1, d2] at hp
  have hA : fc08 θ 0 2 5 4 = 1 - θ 0 - θ 1 := by simp only [fc08, cdet, cp08]; simp; ring
  have hB : fc08 θ 0 2 5 1 = θ 5 * (1 - θ 0 - θ 1) := by simp only [fc08, cdet, cp08]; simp; ring
  have e1 : 0 < θ 0 + θ 1 - 1 := hθ 6
  have hD : det3 E₁ E₂ E₃ * (1 - θ 0 - θ 1) ≠ 0 := mul_ne_zero hE (by linarith)
  rw [hA, hB] at hp
  apply mul_right_cancel₀ hD; linear_combination hp

theorem region_alpha1 {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) {o E₁ E₂ E₃ : ℝ³}
    {θ : Fin 6 → ℝ} (hE : det3 E₁ E₂ E₃ ≠ 0) (hθ : ∀ k, 0 < ineq08 θ k)
    (hpts : pts08 a a' b b' c c' d = nfShape08 o E₁ E₂ E₃ θ) :
    N.F.a'bc.f c' = θ 0 * N.F.a'bc.f a := by
  have hp := facet_prop08 N.F.a'bc a c'
  have d1 : det3 (b - a') (c - a') (a - a') = det3 E₁ E₂ E₃ * fc08 θ 1 2 4 0 := by
    have := det3_nf08 o E₁ E₂ E₃ θ 1 2 4 0; rw [← hpts] at this; exact this
  have d2 : det3 (b - a') (c - a') (c' - a') = det3 E₁ E₂ E₃ * fc08 θ 1 2 4 5 := by
    have := det3_nf08 o E₁ E₂ E₃ θ 1 2 4 5; rw [← hpts] at this; exact this
  rw [d1, d2] at hp
  have hA : fc08 θ 1 2 4 0 = 1 - θ 4 - θ 5 := by simp only [fc08, cdet, cp08]; simp; ring
  have hB : fc08 θ 1 2 4 5 = θ 0 * (1 - θ 4 - θ 5) := by simp only [fc08, cdet, cp08]; simp; ring
  have e1 : 0 < θ 4 + θ 5 - 1 := hθ 8
  have hD : det3 E₁ E₂ E₃ * (1 - θ 4 - θ 5) ≠ 0 := mul_ne_zero hE (by linarith)
  rw [hA, hB] at hp
  apply mul_right_cancel₀ hD; linear_combination hp

theorem nfN2_of_rim {o E₁ E₂ E₃ : ℝ³} (hE : det3 E₁ E₂ E₃ ≠ 0) {θ : Fin 6 → ℝ}
    (hθ : ∀ k, 0 < ineq08 θ k) (h6 : 1 < θ 5) (s : Bool) {k' : ℕ} [NeZero k']
    (σ : ZMod k' → ZMod (test08 0 s false).k)
    (h : RimCertAt (nfShape08 o E₁ E₂ E₃ θ) ((test08 0 s false).view (nfShape08 o E₁ E₂ E₃ θ))
      ((test08 0 s false).lab ∘ σ)) :
    NWS4 (quad ⟪nfShape08 o E₁ E₂ E₃ θ 1, nfShape08 o E₁ E₂ E₃ θ 4 - nfShape08 o E₁ E₂ E₃ θ 1⟫
      ⟪nfShape08 o E₁ E₂ E₃ θ 2, nfShape08 o E₁ E₂ E₃ θ 4 - nfShape08 o E₁ E₂ E₃ θ 1⟫
      ⟪nfShape08 o E₁ E₂ E₃ θ 5, nfShape08 o E₁ E₂ E₃ θ 4 - nfShape08 o E₁ E₂ E₃ θ 1⟫
      ⟪nfShape08 o E₁ E₂ E₃ θ 3, nfShape08 o E₁ E₂ E₃ θ 4 - nfShape08 o E₁ E₂ E₃ θ 1⟫) := by
  cases s
  · exact nfN2_nws4 hE hθ h6 (-1) (by norm_num) σ (by rw [neg_one_smul]; exact h)
  · exact nfN2_nws4 hE hθ h6 1 one_ne_zero σ (by rw [one_smul]; exact h)


/-- **Free closings need no HDN hypothesis** (consolidation §1.5 (1); this is the core of G5a's
`slideN2a'`/`slideQ`, stated at a rim certificate of the limit): if the limit has a robust corner
rim of N2's `K_{a'}` or Q's `K_d` (polygon + robust depths, labels a cyclic subsequence), then the
shape is Rupert, with any HDNs and ties. -/
theorem rupert_of_free_limit_rim {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d)
    (hT : ¬ IsT a' b c d) (hT' : ¬ IsT' a b c' d)
    (t : Fin 3 × Bool × Bool) (ht : t ∉ SC08) {k' : ℕ} [NeZero k'] (σ : ZMod k' → ZMod (test08 t.1 t.2.1 t.2.2).k)
    (hrim : RimCertAt (pts08 a a' b b' c c' d) ((test08 t.1 t.2.1 t.2.2).view (pts08 a a' b b' c c' d))
      ((test08 t.1 t.2.1 t.2.2).lab ∘ σ)) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  classical
  have hnd' := N.F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd'
  obtain ⟨⟨haa', hab, hab', hac, hac'⟩, ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩,
    ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd'
  obtain ⟨hda, hda', hdb, hdb', hdc, hdc'⟩ := N.hd.ne
  obtain ⟨o, E₁, E₂, E₃, θ, hE, hθ, hpts⟩ := exists_nf08 N
  have hFc := N.F.abc'.neg c (by simp) (Ne.symm hac) (Ne.symm hbc) hcc'
  have hFa := N.F.a'bc.neg a (by simp) haa' hab hac
  have hg6 := region_gamma6 N hE hθ hpts
  have hg0 := region_alpha1 N hE hθ hpts
  by_cases htie₁ : N.F.abc'.f a' = N.F.abc'.f c
  · exact absurd (N.hd.tieT_geom htie₁) hT
  by_cases htie₂ : N.F.a'bc.f c' = N.F.a'bc.f a
  · exact absurd (N.hd.tieT'_geom htie₂) hT'
  obtain ⟨i, s, j⟩ := t
  rw [hpts] at hrim
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> simp
  rcases lt_or_gt_of_ne htie₁ with hfar | hfc
  · -- N2 region: `γ₆ > 1`
    have h6 : 1 < θ 5 := by
      rw [hg6] at hfar; nlinarith
    rcases hi with rfl | rfl | rfl
    · cases j
      · have hN := nfN2_of_rim hE hθ h6 s σ hrim
        rw [← hpts] at hN
        have hNx : NWS4 (quad ⟪a', c - a'⟫ ⟪b, c - a'⟫ ⟪c', c - a'⟫ ⟪b', c - a'⟫) := hN
        obtain ⟨hq₂, hgood⟩ := type08_lemma7 N.F N.G N.hκa N.hκb N.hκc N.hU hfar
        obtain ⟨s', δ, hs0, hs1, hδ, hdmid⟩ := N.hd.middle_Qbc hfar
        have e : (insert d ({a', a, c, c', b, b'} : Finset ℝ³)) = insert d {a, a', b, b', c, c'} :=
          (type08_set_perm a a' b b' c c' d).1
        rw [← e]
        exact isRupert_quad_edge_middle_x_formU (m := d) N.F.swap₁.perm₂₃ hfar hq₂
          ⟨s', δ, hs0, hs1, hδ, hdmid⟩ ⟨hda', hda, hdc, hdc', hdb, hdb'⟩ hNx
      · exact absurd (Or.inl ⟨rfl, rfl⟩) ht
    · exact absurd (Or.inr rfl) ht
    · exact (impQ_N2 hE hθ h6 s j σ hrim).elim
  · by_cases hfa : N.F.a'bc.f a < N.F.a'bc.f c'
    · exact close_caseQ N.F N.hd hfc hfa
    · have hfc' : N.F.a'bc.f c' < N.F.a'bc.f a := lt_of_le_of_ne (not_lt.mp hfa) htie₂
      have h6 : θ 5 < 1 := by
        rw [hg6] at hfc; nlinarith
      have h0 : 1 < θ 0 := by
        rw [hg0] at hfc'; nlinarith
      rcases hi with rfl | rfl | rfl
      · cases j
        · exact (impK_T4 hE hθ h6 s σ hrim).elim
        · exact absurd (Or.inl ⟨rfl, rfl⟩) ht
      · exact absurd (Or.inr rfl) ht
      · exact (impQ_T4 hE hθ h0 s j σ hrim).elim


/-! ### Part D: the theorem -/

/-- `isRupert_or_hdn_of_generic_cert`, refined: the "free" tests need no HDN hypothesis. -/
theorem isRupert_or_hdn_of_generic_cert_free {m n q : ℕ} {ι : Type*} [Finite ι] (free : ι → Prop)
    (shape : (Fin m → ℝ) → Fin n → ℝ³) (hshape : Continuous shape)
    (P : MvPolynomial (Fin m) ℝ) (hP : P ≠ 0) (θ : Fin m → ℝ)
    (T : ι → LabTest n) (hT : ∀ c, CovView (T c).view)
    (hseg : ∀ i j m' : Fin n, shape θ m' ≠ shape θ i → shape θ m' ≠ shape θ j →
      ∀ s : ℝ, 0 < s → s < 1 → shape θ m' ≠ shape θ i + s • (shape θ j - shape θ i))
    (hsp : ∃ i j l m' : Fin n,
      det3 (shape θ j - shape θ i) (shape θ l - shape θ i) (shape θ m' - shape θ i) ≠ 0)
    (hview0 : ∀ c, (T c).view (shape θ) ≠ 0)
    (ties : Fin q → ι × Fin n × Fin n)
    (hties : ∀ t, ⟪shape θ (ties t).2.1 - shape θ (ties t).2.2, (T (ties t).1).view (shape θ)⟫ = 0)
    (hind : TieIndep (fun t => shape θ (ties t).2.1 - shape θ (ties t).2.2)
      (fun t => (T (ties t).1).view (shape θ)))
    -- every tie of every test's rim at the limit follows from the listed ties, at any shape
    (hcover : ∀ y : Fin n → ℝ³, (∀ t, ⟪y (ties t).2.1 - y (ties t).2.2, (T (ties t).1).view y⟫ = 0) →
      ∀ c (i j : ZMod (T c).k),
        ⟪shape θ ((T c).lab i), (T c).view (shape θ)⟫ = ⟪shape θ ((T c).lab j), (T c).view (shape θ)⟫ →
        ⟪y ((T c).lab i), (T c).view y⟫ = ⟪y ((T c).lab j), (T c).view y⟫)
    -- generic certificates (the geometry; MF + R2T inside)
    (hcert : ∀ᶠ p in 𝓝 (θ, (1 : ℝ³ →L[ℝ] ℝ³)), MvPolynomial.eval p.1 P ≠ 0 →
      LinearMap.det (p.2 : ℝ³ →ₗ[ℝ] ℝ³) = 1 →
      -- the listed ties stay independent at `p` (open condition, `TieIndep.eventually`)
      TieIndep (fun t => mapShape p.2 (shape p.1) (ties t).2.1 - mapShape p.2 (shape p.1) (ties t).2.2)
        (fun t => (T (ties t).1).view (mapShape p.2 (shape p.1))) →
      -- no new rim ties: a tie of a rim at `p` is a tie of the limit (closed condition; the proof
      -- of this theorem gets it eventually along the sequence from continuity)
      (∀ c (i j : ZMod (T c).k),
        ⟪mapShape p.2 (shape p.1) ((T c).lab i), (T c).view (mapShape p.2 (shape p.1))⟫ =
          ⟪mapShape p.2 (shape p.1) ((T c).lab j), (T c).view (mapShape p.2 (shape p.1))⟫ →
        ⟪shape θ ((T c).lab i), (T c).view (shape θ)⟫ = ⟪shape θ ((T c).lab j), (T c).view (shape θ)⟫) →
      (∀ t, ⟪mapShape p.2 (shape p.1) (ties t).2.1 - mapShape p.2 (shape p.1) (ties t).2.2,
        (T (ties t).1).view (mapShape p.2 (shape p.1))⟫ = 0) →
      ∃ c, (T c).Cert (mapShape p.2 (shape p.1)))
    (hfreeR : ∀ c, free c → (∃ (k' : ℕ) (_ : NeZero k') (σ : ZMod k' → ZMod (T c).k),
      RimCertAt (shape θ) ((T c).view (shape θ)) ((T c).lab ∘ σ)) → IsRupert (univ.image (shape θ))) :
    IsRupert (univ.image (shape θ)) ∨ ∃ c, ¬ free c ∧ ¬ NoHDNAt (univ.image (shape θ)) ((T c).view (shape θ)) := by
  obtain ⟨θs, L, hθs, hL, hPs, hdet, hrest⟩ := exists_seq_restore_ties shape hshape P hP θ
    (fun t => (ties t).2) (fun t => (T (ties t).1).view) (fun t => hT _) hties hind
  let K : ℕ → Fin n → ℝ³ := fun j => mapShape (L j) (shape (θs j))
  have hev : Continuous (fun p : (ℝ³ →L[ℝ] ℝ³) × ℝ³ => p.1 p.2) := continuous_fst.clm_apply continuous_snd
  have hKt : ∀ i, Tendsto (fun j => K j i) atTop (𝓝 (shape θ i)) := by
    intro i
    have h1 : Tendsto (fun j => shape (θs j) i) atTop (𝓝 (shape θ i)) :=
      ((continuous_apply i).comp hshape |>.tendsto θ).comp hθs
    have := (hev.tendsto (1, shape θ i)).comp (hL.prodMk_nhds h1)
    exact this
  have hvt : ∀ c, Tendsto (fun j => (T c).view (K j)) atTop (𝓝 ((T c).view (shape θ))) := by
    intro c
    have h1 : Tendsto (fun j => (T c).view (shape (θs j))) atTop (𝓝 ((T c).view (shape θ))) :=
      (((hT c).1.comp hshape).tendsto θ).comp hθs
    have := (hev.tendsto (1, (T c).view (shape θ))).comp (hL.prodMk_nhds h1)
    exact Tendsto.congr (fun j => ((hT c).2 (L j) (shape (θs j)) (hdet j)).symm) this
  have hpt : Tendsto (fun j => (θs j, L j)) atTop (𝓝 (θ, (1 : ℝ³ →L[ℝ] ℝ³))) :=
    hθs.prodMk_nhds hL
  have hcert' := hpt.eventually hcert
  -- independence along the sequence
  have hdv : Tendsto (fun j => ((fun t => K j (ties t).2.1 - K j (ties t).2.2),
      (fun t => (T (ties t).1).view (K j)))) atTop
      (𝓝 ((fun t => shape θ (ties t).2.1 - shape θ (ties t).2.2),
        (fun t => (T (ties t).1).view (shape θ)))) := by
    refine Tendsto.prodMk_nhds ?_ ?_
    · exact tendsto_pi_nhds.2 fun t => (hKt _).sub (hKt _)
    · exact tendsto_pi_nhds.2 fun t => hvt _
  have hind' := hdv.eventually hind.eventually
  -- no new rim ties along the sequence
  have hnew : ∀ᶠ j in atTop, ∀ c (i j' : ZMod (T c).k),
      ⟪K j ((T c).lab i), (T c).view (K j)⟫ = ⟪K j ((T c).lab j'), (T c).view (K j)⟫ →
      ⟪shape θ ((T c).lab i), (T c).view (shape θ)⟫ = ⟪shape θ ((T c).lab j'), (T c).view (shape θ)⟫ := by
    rw [Filter.eventually_all]; intro c
    rw [Filter.eventually_all]; intro i
    rw [Filter.eventually_all]; intro j'
    by_cases h : ⟪shape θ ((T c).lab i), (T c).view (shape θ)⟫ =
        ⟪shape θ ((T c).lab j'), (T c).view (shape θ)⟫
    · exact Filter.Eventually.of_forall fun _ _ => h
    · have t1 := Tendsto.inner' (hKt ((T c).lab i)) (hvt c)
      have t2 := Tendsto.inner' (hKt ((T c).lab j')) (hvt c)
      have := (t1.sub t2).eventually_ne (sub_ne_zero.2 h)
      exact this.mono fun j hj heq => absurd (sub_eq_zero.2 heq) hj
  have hfreq : ∃ᶠ j in atTop, ∃ c, (T c).Cert (K j) ∧
      ∀ i j' : ZMod (T c).k, ⟪shape θ ((T c).lab i), (T c).view (shape θ)⟫ =
        ⟪shape θ ((T c).lab j'), (T c).view (shape θ)⟫ →
        ⟪K j ((T c).lab i), (T c).view (K j)⟫ = ⟪K j ((T c).lab j'), (T c).view (K j)⟫ := by
    refine ((hcert'.and (hind'.and hnew)).frequently).mono ?_
    rintro j ⟨hc, hi, hn⟩
    have hties' := hrest j
    obtain ⟨c, hcC⟩ := hc (hPs j) (hdet j) hi hn hties'
    exact ⟨c, hcC, fun i j' h => hcover (K j) hties' c i j' h⟩
  obtain ⟨c, hcf⟩ := frequently_exists_of_finite hfreq
  by_cases hf : free c
  · left
    obtain ⟨k', hk, σ, hrim⟩ := exists_limit_rimCert T (shape θ) hsp (hview0) K hKt hvt c hcf
    exact hfreeR c hf ⟨k', hk, σ, hrim⟩
  · by_cases hN : NoHDNAt (univ.image (shape θ)) ((T c).view (shape θ))
    · left
      exact isRupert_of_tendsto_rimCert (shape θ) hseg hsp (T c).lab (hview0 c) hN
        K (fun j => (T c).view (K j)) hKt (hvt c) hcf
    · right; exact ⟨c, hf, hN⟩




theorem grp_tests_view (i : Fin 3) : ∀ T ∈ (grp08 i).tests, T.view = (grp08 i).view := by
  intro T hT
  fin_cases i <;>
    (simp only [grp08, ViewGroup.tests, ViewGroup.view, List.mem_cons, List.mem_singleton,
      List.not_mem_nil, or_false] at hT ⊢
     first | (rcases hT with rfl | rfl <;> rfl) | (subst hT; rfl))

theorem test08_eq (i : Fin 3) (s j : Bool) : ∃ T ∈ (grp08 i).tests,
    test08 i s j = T ∨ test08 i s j = T.neg := by
  refine ⟨test08 i true j, ?_, ?_⟩
  · have := test_mem_grpS i true j
    rwa [grpS_true] at this
  · cases s
    · right; rfl
    · left; rfl

theorem continuous_nf08 (o E₁ E₂ E₃ : ℝ³) : Continuous (nfShape08 o E₁ E₂ E₃) := by
  refine continuous_pi fun i => ?_
  fin_cases i <;> simp [nfShape08] <;> fun_prop

theorem continuous_ineq08 (k : Fin 24) : Continuous (fun θ : Fin 6 → ℝ => ineq08 θ k) := by
  fin_cases k <;>
    simp [ineq08, fc08, cdet, cp08, gWa, gWb, gWc, gWU] <;> fun_prop


theorem view_test08_true (i : Fin 3) : (test08 i true true).view = (grp08 i).view := by
  have := grpS_view i true
  rw [grpS_true] at this
  exact this.symm

theorem eqv_depth {q : ℕ} {ties : Fin q → Fin 3 × Fin 7 × Fin 7} {y : Fin 7 → ℝ³} {i : Fin 3}
    (hy : ∀ t, ⟪y (ties t).2.1 - y (ties t).2.2, (grp08 (ties t).1).view y⟫ = 0) {p p' : Fin 7}
    (h : Relation.EqvGen (fun p p' => ∃ t, (ties t).1 = i ∧ (ties t).2 = (p, p')) p p') :
    ⟪y p, (grp08 i).view y⟫ = ⟪y p', (grp08 i).view y⟫ := by
  induction h with
  | rel p p' h =>
    obtain ⟨t, ht1, ht2⟩ := h
    have := hy t
    rw [ht1] at this
    obtain ⟨e1, e2⟩ := Prod.mk.inj ht2
    rw [← e1, ← e2]
    rw [inner_sub_left] at this; linarith
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2

theorem cover_transfer {q : ℕ} {ties : Fin q → Fin 3 × Fin 7 × Fin 7} {x y : Fin 7 → ℝ³}
    (hcover : ∀ i, ∀ T ∈ (grp08 i).tests, ∀ u v : ZMod T.k, T.depth x u = T.depth x v →
      Relation.EqvGen (fun p p' => ∃ t, (ties t).1 = i ∧ (ties t).2 = (p, p')) (T.lab u) (T.lab v))
    (hy : ∀ t, ⟪y (ties t).2.1 - y (ties t).2.2, (grp08 (ties t).1).view y⟫ = 0)
    {i : Fin 3} {T0 T : LabTest 7} (hT : T ∈ (grp08 i).tests) (hT0 : T = T0 ∨ T.neg = T0)
    (a b : ZMod T0.k) (hab : ⟪x (T0.lab a), T0.view x⟫ = ⟪x (T0.lab b), T0.view x⟫) :
    ⟪y (T0.lab a), T0.view y⟫ = ⟪y (T0.lab b), T0.view y⟫ := by
  have hv := grp_tests_view i T hT
  rcases hT0 with rfl | rfl
  · have h := hcover i T hT a b hab
    have := eqv_depth hy h
    rwa [hv]
  · have hab' : ⟪x (T.lab a), T.view x⟫ = ⟪x (T.lab b), T.view x⟫ := by
      simpa [LabTest.neg] using hab
    have h := hcover i T hT a b hab'
    have := eqv_depth hy h
    simp only [LabTest.neg, hv, inner_neg_right, this]


theorem grp_view_ne {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) (i : Fin 3) :
    (grp08 i).view (pts08 a a' b b' c c' d) ≠ 0 := by
  have hnd := N.F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨haa', hab, hab', hac, hac'⟩, ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩,
    ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd
  obtain ⟨hda, hda', hdb, hdb', hdc, hdc'⟩ := N.hd.ne
  fin_cases i <;> simp [grp08, ViewGroup.view, LabTest.quad, pts08, sub_eq_zero]
  · exact Ne.symm ha'c
  · exact hdb.symm
  · exact hdb.symm

theorem view0_test08 {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) (c0 : Fin 3 × Bool × Bool) :
    (test08 c0.1 c0.2.1 c0.2.2).view (pts08 a a' b b' c c' d) ≠ 0 := by
  obtain ⟨T, hT, h | h⟩ := test08_eq c0.1 c0.2.1 c0.2.2
  · rw [h, grp_tests_view _ T hT]; exact grp_view_ne N _
  · rw [h]; simp only [LabTest.neg, grp_tests_view _ T hT, neg_ne_zero]; exact grp_view_ne N _



theorem noHDN_SC08 {a a' b b' c c' d : ℝ³} (t : Fin 3 × Bool × Bool) (ht : t ∈ SC08)
    (hhdn : ∀ u, Named08 a a' b b' c c' d u →
      NoHDNAt (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) u) :
    NoHDNAt (insert d ({a, a', b, b', c, c'} : Finset ℝ³))
      ((test08 t.1 t.2.1 t.2.2).view (pts08 a a' b b' c c' d)) := by
  have h0 : Named08 a a' b b' c c' d (c - a') := Or.inl ⟨2, 0, true, false, by decide, by simp⟩
  have h1 : Named08 a a' b b' c c' d (b - d) := Or.inr ⟨1, true, by simp⟩
  obtain ⟨i, s, j⟩ := t
  have hi : (i = 0 ∧ j = true) ∨ i = 1 := ht
  obtain ⟨T, hT, h | h⟩ := test08_eq i s j
  · rw [h, grp_tests_view _ T hT]
    rcases hi with ⟨rfl, -⟩ | rfl
    · exact hhdn _ h0
    · exact hhdn _ h1
  · rw [h]; simp only [LabTest.neg, grp_tests_view _ T hT]
    rcases hi with ⟨rfl, -⟩ | rfl
    · have := (hhdn _ h0).neg
      simpa [grp08, ViewGroup.view, pts08] using this
    · have := (hhdn _ h1).neg
      simpa [grp08, ViewGroup.view, pts08] using this



/-- **Theorem 29.1, Lean form G3'.**  A type-08 shape in the used labelling with at most two
independent ties at the certificate views (`ties`, which cover all rim ties of N2, T4 and Q), no
touching, is Rupert unless a **single-circle closing** (N2's `K_c`, T4's `K_b` or `K_2`) has an HDN
at its view.  No `NoHDNAt` at the other named views, no `FewTies` at all 18 named views.

Proof: `exists_nf08`, `isRupert_or_hdn_of_generic_cert` with `shape = nfShape08 o E` in the frame
parameters `θ` (the linear maps `L` of the lemma are absorbed in the frame by
`mapShape_nfShape08`; so `hcert` is `cert08_generic` at `(L o, L E)`), `seg08`; if the HDN
disjunct is for a closing `t ∉ SC08`, use `exists_limit_rimCert` and `rupert_of_free_limit_rim`. -/
theorem isRupert_type08_limit_hdn {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d)
    {q : ℕ} (hq : q ≤ 2) (ties : Fin q → Fin 3 × Fin 7 × Fin 7)
    (hties : ∀ t, ⟪pts08 a a' b b' c c' d (ties t).2.1 - pts08 a a' b b' c c' d (ties t).2.2,
      (grp08 (ties t).1).view (pts08 a a' b b' c c' d)⟫ = 0)
    (hind : TieIndep (fun t => pts08 a a' b b' c c' d (ties t).2.1 - pts08 a a' b b' c c' d (ties t).2.2)
      (fun t => (grp08 (ties t).1).view (pts08 a a' b b' c c' d)))
    (hcover : ∀ i, ∀ T ∈ (grp08 i).tests, ∀ u v : ZMod T.k,
      T.depth (pts08 a a' b b' c c' d) u = T.depth (pts08 a a' b b' c c' d) v →
      Relation.EqvGen (fun p p' => ∃ t, (ties t).1 = i ∧ (ties t).2 = (p, p')) (T.lab u) (T.lab v))
    (hnt : ¬ Touch a a' b b' c c' d)
    (hTco : IsT a' b c d → ¬ CoT2 a a' b b' c c' d)
    (hT'co : IsT' a b c' d → ¬ CoT'2 a a' b b' c c' d) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) ∨
      ∃ t ∈ SC08, ¬ NoHDNAt (insert d ({a, a', b, b', c, c'} : Finset ℝ³))
        ((test08 t.1 t.2.1 t.2.2).view (pts08 a a' b b' c c' d)) := by
  classical
  have hnR : ¬ RTouch a a' b b' c c' d := by
    rintro (h | h | h)
    · exact h (fun ht => absurd (Or.inl ht) hnt)
    · exact h (fun ht => absurd (Or.inr ht) hnt)
    · exact h (fun ht => absurd (Or.inr ht) hnt)
  by_cases hT : IsT a' b c d
  · exact Or.inl (close_T2_final N hT (hTco hT) hnR)
  by_cases hT' : IsT' a b c' d
  · exact Or.inl (close_T'2_final N hT' (hT'co hT') hnR)
  obtain ⟨o, E₁, E₂, E₃, θ, hE, hθ, hpts⟩ := exists_nf08 N
  obtain ⟨hseg, hsp⟩ := seg08 N
  have hview0 := view0_test08 N
  simp only [hpts] at hseg hsp hview0 hties hind hcover
  rw [← image_pts08, hpts]
  let tI : Fin q → (Fin 3 × Bool × Bool) × Fin 7 × Fin 7 := fun t => (((ties t).1, true, true), (ties t).2)
  have hvt : ∀ i y, (test08 i true true).view y = (grp08 i).view y := fun i y => by rw [view_test08_true]
  have key : IsRupert (univ.image (nfShape08 o E₁ E₂ E₃ θ)) ∨ ∃ c : Fin 3 × Bool × Bool, ¬ (c ∉ SC08) ∧
      ¬ NoHDNAt (univ.image (nfShape08 o E₁ E₂ E₃ θ))
        ((test08 c.1 c.2.1 c.2.2).view (nfShape08 o E₁ E₂ E₃ θ)) := by
    refine isRupert_or_hdn_of_generic_cert_free (m := 6) (n := 7) (q := q)
      (ι := Fin 3 × Bool × Bool) (fun c => c ∉ SC08) (nfShape08 o E₁ E₂ E₃) (continuous_nf08 o E₁ E₂ E₃)
      genPoly08 genPoly08_ne_zero θ (fun c => test08 c.1 c.2.1 c.2.2) (fun c => covView_test08 _ _ _)
      hseg hsp hview0 tI (by simpa [tI, hvt] using hties) (by simpa [tI, hvt] using hind)
      ?_ ?_ ?_
    · intro y hy c i j hij
      obtain ⟨T, hT, h⟩ := test08_eq c.1 c.2.1 c.2.2
      refine cover_transfer hcover ?_ hT (h.imp Eq.symm Eq.symm) i j hij
      intro t
      simpa [tI, hvt] using hy t
    · have hineq : ∀ᶠ p in 𝓝 (θ, (1 : ℝ³ →L[ℝ] ℝ³)), ∀ k, 0 < ineq08 p.1 k := by
        rw [Filter.eventually_all]
        intro k
        exact ((continuous_ineq08 k).comp continuous_fst).continuousAt.eventually (lt_mem_nhds (hθ k))
      filter_upwards [hineq] with p hp hg hdet hind' hnew hties'
      simp only [mapShape_nfShape08] at hind' hnew hties' ⊢
      have hE' : det3 (p.2 E₁) (p.2 E₂) (p.2 E₃) ≠ 0 := by
        rw [det3_map, detMap_eq08, hdet, one_mul]; exact hE
      set Y := nfShape08 (p.2 o) (p.2 E₁) (p.2 E₂) (p.2 E₃) p.1 with hY
      have hnew' : ∀ c : Fin 3 × Bool × Bool, ∀ i j : ZMod (test08 c.1 c.2.1 c.2.2).k,
          ⟪Y ((test08 c.1 c.2.1 c.2.2).lab i), (test08 c.1 c.2.1 c.2.2).view Y⟫ =
            ⟪Y ((test08 c.1 c.2.1 c.2.2).lab j), (test08 c.1 c.2.1 c.2.2).view Y⟫ →
          ⟪nfShape08 o E₁ E₂ E₃ θ ((test08 c.1 c.2.1 c.2.2).lab i),
            (test08 c.1 c.2.1 c.2.2).view (nfShape08 o E₁ E₂ E₃ θ)⟫ =
          ⟪nfShape08 o E₁ E₂ E₃ θ ((test08 c.1 c.2.1 c.2.2).lab j),
            (test08 c.1 c.2.1 c.2.2).view (nfShape08 o E₁ E₂ E₃ θ)⟫ := hnew
      have hties'' : ∀ t, ⟪Y (ties t).2.1 - Y (ties t).2.2, (grp08 (ties t).1).view Y⟫ = 0 := by
        intro t; simpa [tI, hvt] using hties' t
      have hind'' : TieIndep (fun t => Y (ties t).2.1 - Y (ties t).2.2)
          (fun t => (grp08 (ties t).1).view Y) := by simpa [tI, hvt] using hind'
      have hcov : ∀ i, ∀ T ∈ (grp08 i).tests, ∀ u v : ZMod T.k, T.depth Y u = T.depth Y v →
          Relation.EqvGen (fun p p' => ∃ t, (ties t).1 = i ∧ (ties t).2 = (p, p')) (T.lab u) (T.lab v) := by
        intro i T hT u v huv
        have hT' := hT
        rw [← grpS_true] at hT'
        obtain ⟨j, rfl⟩ := grpS_tests i true T hT'
        exact hcover i _ hT u v (hnew' (i, true, j) u v huv)
      have hno : ∀ i, ¬ (grp08 i).Straddle Y := by
        intro i hst
        fin_cases i
        all_goals first | exact hst.elim | skip
        all_goals apply hnt
        · simp only [grp08, ViewGroup.Straddle] at hst
          obtain ⟨h1, h2, -, -⟩ := hst
          have e1 := hnew' (0, true, true) 1 2 h1
          have e2 := hnew' (0, true, true) 2 3 h2
          rw [← hpts] at e1 e2
          exact Or.inl ⟨e1, e2.symm⟩
        · simp only [grp08, ViewGroup.Straddle] at hst
          obtain ⟨h1, h2, -, -⟩ := hst
          have e1 := hnew' (1, true, true) 1 2 h1
          have e2 := hnew' (1, true, true) 2 3 h2
          rw [← hpts] at e1 e2
          exact Or.inr ⟨e2.symm, e1⟩
      obtain ⟨i, s, j, hC⟩ := cert08_generic (p.2 o) (p.2 E₁) (p.2 E₂) (p.2 E₃) hE' p.1 hp hg hq ties
        hties'' hind'' hcov hno
      exact ⟨(i, s, j), hC⟩
    · intro c hc hrim
      obtain ⟨k', hk, σ, hr⟩ := hrim
      rw [← hpts] at hr
      rw [← hpts, image_pts08]
      exact rupert_of_free_limit_rim N hT hT' c hc σ hr
  exact key.imp id (fun ⟨c, hc, hn⟩ => ⟨c, not_not.1 hc, hn⟩)

/-- The old G3 conclusion follows (all named views `NoHDNAt`): the new statement with `hhdn`. -/
theorem isRupert_type08_limit_norm_of_hdn {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d)
    {q : ℕ} (hq : q ≤ 2) (ties : Fin q → Fin 3 × Fin 7 × Fin 7)
    (hties : ∀ t, ⟪pts08 a a' b b' c c' d (ties t).2.1 - pts08 a a' b b' c c' d (ties t).2.2,
      (grp08 (ties t).1).view (pts08 a a' b b' c c' d)⟫ = 0)
    (hind : TieIndep (fun t => pts08 a a' b b' c c' d (ties t).2.1 - pts08 a a' b b' c c' d (ties t).2.2)
      (fun t => (grp08 (ties t).1).view (pts08 a a' b b' c c' d)))
    (hcover : ∀ i, ∀ T ∈ (grp08 i).tests, ∀ u v : ZMod T.k,
      T.depth (pts08 a a' b b' c c' d) u = T.depth (pts08 a a' b b' c c' d) v →
      Relation.EqvGen (fun p p' => ∃ t, (ties t).1 = i ∧ (ties t).2 = (p, p')) (T.lab u) (T.lab v))
    (hnt : ¬ Touch a a' b b' c c' d)
    (hTco : IsT a' b c d → ¬ CoT2 a a' b b' c c' d)
    (hT'co : IsT' a b c' d → ¬ CoT'2 a a' b b' c c' d)
    (hhdn : ∀ u, Named08 a a' b b' c c' d u →
      NoHDNAt (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) u) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  rcases isRupert_type08_limit_hdn N hq ties hties hind hcover hnt hTco hT'co with h | ⟨t, ht, hn⟩
  · exact h
  · exact absurd (noHDN_SC08 t ht hhdn) hn

end Type08Sp
end Minimality
