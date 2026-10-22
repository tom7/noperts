module

public import Minimality.EdgePair
public import Minimality.RobustEdge
public import Minimality.RimCert

@[expose] public section

/-!
# Type 16: the normal form (`FEWER-FACES-PROOFS.md` §19.0)

The affine normal form of §19.0: `3 = 0`, `0 = e₁`, `5 = e₂`, `6 = e₃`, `2 = (a, b, 0)`,
`1 = (0, g, d)`, `4 = (p, q, r)`.  Rupertness is not affine-invariant, so the frame is kept:
`nfP o E₁ E₂ E₃ α β γ = o + α E₁ + β E₂ + γ E₃` with `o = x 3`, `E₁ = x 0 − x 3`,
`E₂ = x 5 − x 3`, `E₃ = x 6 − x 3`.  Every orientation test of the cover is a determinant of
differences of such points, hence the determinant of the coefficients times
`D = det3 E₁ E₂ E₃` (`det3_nfV`); depths are inner products, kept as they are (the paper's
"every metric").

* `NF16`: the normal form with the type inequalities of the table of §19.0 (all strict).
* `Type16.toNF`: every type-16 point set (`Type16`) has a normal form; each inequality is the
  sign of one facet function at one vertex.
* `NF16.sigma`: the normal form of `x ∘ σ`, `σ = (06)(12)` (`x ↔ z`,
  `(a, b, g, d, p, q, r) ↦ (d, g, b, a, r, q, p)`).
* **R1 and R2** (`NF16.R1`, `NF16.R2`; §19.0): the two never hold together
  (`NF16.not_R1_R2`: `(p + r) [B125] + a r R1 + d p R2 = 0`).
-/

namespace Minimality

open scoped RealInnerProductSpace
open Finset

/-! ### Frames -/

/-- A point `o + α E₁ + β E₂ + γ E₃` of the frame `o; E₁, E₂, E₃`. -/
def nfP (o E₁ E₂ E₃ : ℝ³) (α β γ : ℝ) : ℝ³ := o + α • E₁ + β • E₂ + γ • E₃

/-- A vector `α E₁ + β E₂ + γ E₃` of the frame. -/
def nfV (E₁ E₂ E₃ : ℝ³) (α β γ : ℝ) : ℝ³ := α • E₁ + β • E₂ + γ • E₃

/-- The determinant of a 3 × 3 matrix of coefficients (rows `(x, y, z)`). -/
def det3c (x₁ y₁ z₁ x₂ y₂ z₂ x₃ y₃ z₃ : ℝ) : ℝ :=
  x₁ * (y₂ * z₃ - z₂ * y₃) - y₁ * (x₂ * z₃ - z₂ * x₃) + z₁ * (x₂ * y₃ - y₂ * x₃)

theorem nfP_sub (o E₁ E₂ E₃ : ℝ³) (α β γ α' β' γ' : ℝ) :
    nfP o E₁ E₂ E₃ α β γ - nfP o E₁ E₂ E₃ α' β' γ' = nfV E₁ E₂ E₃ (α - α') (β - β') (γ - γ') := by
  simp only [nfP, nfV]; module

theorem det3_nfV (E₁ E₂ E₃ : ℝ³) (x₁ y₁ z₁ x₂ y₂ z₂ x₃ y₃ z₃ : ℝ) :
    det3 (nfV E₁ E₂ E₃ x₁ y₁ z₁) (nfV E₁ E₂ E₃ x₂ y₂ z₂) (nfV E₁ E₂ E₃ x₃ y₃ z₃) =
      det3c x₁ y₁ z₁ x₂ y₂ z₂ x₃ y₃ z₃ * det3 E₁ E₂ E₃ := by
  simp only [nfV, det3c, det3_expand, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring

theorem inner_nfP (o E₁ E₂ E₃ u : ℝ³) (α β γ : ℝ) :
    ⟪nfP o E₁ E₂ E₃ α β γ, u⟫ = ⟪o, u⟫ + α * ⟪E₁, u⟫ + β * ⟪E₂, u⟫ + γ * ⟪E₃, u⟫ := by
  simp only [nfP, inner_add_left, real_inner_smul_left]

theorem inner_nfV (E₁ E₂ E₃ u : ℝ³) (α β γ : ℝ) :
    ⟪nfV E₁ E₂ E₃ α β γ, u⟫ = α * ⟪E₁, u⟫ + β * ⟪E₂, u⟫ + γ * ⟪E₃, u⟫ := by
  simp only [nfV, inner_add_left, real_inner_smul_left]

theorem inner_nfV_right (E₁ E₂ E₃ u : ℝ³) (α β γ : ℝ) :
    ⟪u, nfV E₁ E₂ E₃ α β γ⟫ = α * ⟪u, E₁⟫ + β * ⟪u, E₂⟫ + γ * ⟪u, E₃⟫ := by
  simp only [nfV, inner_add_right, real_inner_smul_right]

/-- An affine function at a point of the frame. -/
theorem affine_nfP {f : ℝ³ → ℝ} {N : ℝ³} (hf : ∀ y z, f y - f z = ⟪N, y - z⟫)
    (o E₁ E₂ E₃ : ℝ³) (α β γ : ℝ) :
    f (nfP o E₁ E₂ E₃ α β γ) = f o + α * (f (o + E₁) - f o) + β * (f (o + E₂) - f o) +
      γ * (f (o + E₃) - f o) := by
  have h := hf (nfP o E₁ E₂ E₃ α β γ) o
  rw [hf, hf, hf, add_sub_cancel_left, add_sub_cancel_left, add_sub_cancel_left]
  rw [show nfP o E₁ E₂ E₃ α β γ - o = α • E₁ + β • E₂ + γ • E₃ by simp only [nfP]; abel,
    inner_add_right, inner_add_right, real_inner_smul_right, real_inner_smul_right,
    real_inner_smul_right] at h
  linarith

/-- The sign of a product with a positive factor `σ D`: the tool for every orientation test. -/
theorem nf_pos {σ D X P : ℝ} (hσD : 0 < σ * D) (hP : 0 < P) (e : X = P) : 0 < σ * (X * D) := by
  rw [e, show σ * (P * D) = P * (σ * D) by ring]; exact mul_pos hP hσD

theorem nf_neg {σ D X P : ℝ} (hσD : 0 < σ * D) (hP : 0 < P) (e : X = -P) : σ * (X * D) < 0 := by
  rw [e, show σ * (-P * D) = -(P * (σ * D)) by ring]; linarith [mul_pos hP hσD]

/-! ### The normal form -/

/-- **The normal form of type 16** (§19.0) in the frame `o; E₁, E₂, E₃` (`D ≠ 0`):
`x 3 = o`, `x 0 = o + E₁`, `x 5 = o + E₂`, `x 6 = o + E₃`, `x 2 = (a, b, 0)`,
`x 1 = (0, g, d)`, `x 4 = (p, q, r)`, with the type inequalities (each strict).  The names
follow the table of §19.0: `t046_5` is "5 beneath 046", and so on. -/
structure NF16 (x : Fin 7 → ℝ³) where
  o : ℝ³
  E₁ : ℝ³
  E₂ : ℝ³
  E₃ : ℝ³
  inj : Function.Injective x
  a : ℝ
  b : ℝ
  g : ℝ
  d : ℝ
  p : ℝ
  q : ℝ
  r : ℝ
  x0 : x 0 = nfP o E₁ E₂ E₃ 1 0 0
  x1 : x 1 = nfP o E₁ E₂ E₃ 0 g d
  x2 : x 2 = nfP o E₁ E₂ E₃ a b 0
  x3 : x 3 = nfP o E₁ E₂ E₃ 0 0 0
  x4 : x 4 = nfP o E₁ E₂ E₃ p q r
  x5 : x 5 = nfP o E₁ E₂ E₃ 0 1 0
  x6 : x 6 = nfP o E₁ E₂ E₃ 0 0 1
  hD : det3 E₁ E₂ E₃ ≠ 0
  ha : 0 < a
  hb : 0 < b
  hg : 0 < g
  hd : 0 < d
  hp : 0 < p
  hq : 0 < q
  hr : 0 < r
  hab : 0 < a + b - 1
  hgd : 0 < g + d - 1
  t046_5 : 0 < p + q + r - 1
  t0246 : 0 < b * (p + r - 1) - q * (a - 1)
  t0146 : 0 < g * (p + r - 1) - q * (d - 1)
  t024_1 : 0 < b * r + (a - 1) * r * g - d * ((a - 1) * q - b * (p - 1))
  t146_2 : 0 < g * p + (d - 1) * p * b - a * ((d - 1) * q - g * (r - 1))
  t245_6 : 0 < a * (q + r - 1) - (b - 1) * p
  t145_0 : 0 < d * (p + q - 1) - (g - 1) * r
  tB125 : 0 < a * d * (q - 1) - d * p * (b - 1) - a * r * (g - 1)

namespace NF16

variable {x : Fin 7 → ℝ³}

/-- `R1`: `1` is a shadow corner at the view along `06` (`145` faces toward `6`). -/
def R1 (N : NF16 x) : ℝ := (N.g - 1) * (N.p + N.r) - N.d * (N.q - 1)

/-- `R2 = σ R1`: `2` is a shadow corner at the view along `06`. -/
def R2 (N : NF16 x) : ℝ := (N.b - 1) * (N.p + N.r) - N.a * (N.q - 1)

/-- **R1 and R2 exclude each other** (§19.0): `(p + r) [B125] + a r R1 + d p R2 = 0`. -/
theorem R2_neg_of_R1 (N : NF16 x) (h : 0 ≤ N.R1) : N.R2 < 0 := by
  have e : (N.p + N.r) * (N.a * N.d * (N.q - 1) - N.d * N.p * (N.b - 1) -
      N.a * N.r * (N.g - 1)) + N.a * N.r * N.R1 + N.d * N.p * N.R2 = 0 := by
    simp only [R1, R2]; ring
  have h1 := mul_pos (add_pos N.hp N.hr) N.tB125
  have h2 := mul_nonneg (mul_pos N.ha N.hr).le h
  have h3 := mul_pos N.hd N.hp
  by_contra hc; push Not at hc
  nlinarith [mul_nonneg h3.le hc]

theorem not_R1_R2 (N : NF16 x) : ¬ (0 ≤ N.R1 ∧ 0 ≤ N.R2) := fun h =>
  absurd h.2 (not_le.mpr (N.R2_neg_of_R1 h.1))

/-- The orientation of the frame. -/
noncomputable def D (N : NF16 x) : ℝ := det3 N.E₁ N.E₂ N.E₃

/-- **The normal form of `x ∘ σ`**, `σ = (06)(12)`: the frame `o; E₃, E₂, E₁` and the
parameters `(d, g, b, a, r, q, p)`. -/
def sigma (N : NF16 x) : NF16 (x ∘ sigma16) where
  o := N.o
  E₁ := N.E₃
  E₂ := N.E₂
  E₃ := N.E₁
  inj := N.inj.comp (by intro i j h; revert i j; decide)
  a := N.d
  b := N.g
  g := N.b
  d := N.a
  p := N.r
  q := N.q
  r := N.p
  x0 := by
    show x 6 = _; rw [N.x6]; simp only [nfP]; module
  x1 := by
    show x 2 = _; rw [N.x2]; simp only [nfP]; module
  x2 := by
    show x 1 = _; rw [N.x1]; simp only [nfP]; module
  x3 := by
    show x 3 = _; rw [N.x3]; simp only [nfP]; module
  x4 := by
    show x 4 = _; rw [N.x4]; simp only [nfP]; module
  x5 := by
    show x 5 = _; rw [N.x5]; simp only [nfP]; module
  x6 := by
    show x 0 = _; rw [N.x0]; simp only [nfP]; module
  hD := by
    have e : det3 N.E₃ N.E₂ N.E₁ = -det3 N.E₁ N.E₂ N.E₃ := by
      simp only [det3_expand]; ring
    rw [e]; exact neg_ne_zero.mpr N.hD
  ha := N.hd
  hb := N.hg
  hg := N.hb
  hd := N.ha
  hp := N.hr
  hq := N.hq
  hr := N.hp
  hab := by linarith [N.hgd]
  hgd := by linarith [N.hab]
  t046_5 := by linarith [N.t046_5]
  t0246 := by linarith [N.t0146]
  t0146 := by linarith [N.t0246]
  t024_1 := by linarith [N.t146_2]
  t146_2 := by linarith [N.t024_1]
  t245_6 := by linarith [N.t145_0]
  t145_0 := by linarith [N.t245_6]
  tB125 := by linarith [N.tB125]

theorem sigma_R1 (N : NF16 x) : N.sigma.R1 = N.R2 := by
  simp only [R1, R2, sigma]; ring

theorem sigma_D (N : NF16 x) : N.sigma.D = -N.D := by
  simp only [D, sigma, det3_expand]; ring

end NF16

/-! ### From the facets -/

/-- Coordinates of a point in a frame with `det3 E₁ E₂ E₃ ≠ 0` (Cramer). -/
theorem eq_nfP_cramer {o E₁ E₂ E₃ : ℝ³} (hD : det3 E₁ E₂ E₃ ≠ 0) (v : ℝ³) :
    v = nfP o E₁ E₂ E₃ (det3 (v - o) E₂ E₃ / det3 E₁ E₂ E₃)
      (det3 E₁ (v - o) E₃ / det3 E₁ E₂ E₃) (det3 E₁ E₂ (v - o) / det3 E₁ E₂ E₃) := by
  have hc := cramer E₁ E₂ E₃ (v - o)
  have : v - o = (det3 (v - o) E₂ E₃ / det3 E₁ E₂ E₃) • E₁ +
      (det3 E₁ (v - o) E₃ / det3 E₁ E₂ E₃) • E₂ + (det3 E₁ E₂ (v - o) / det3 E₁ E₂ E₃) • E₃ := by
    rw [div_eq_inv_mul, div_eq_inv_mul, div_eq_inv_mul, mul_smul, mul_smul, mul_smul,
      ← smul_add, ← smul_add, ← hc, smul_smul, inv_mul_cancel₀ hD, one_smul]
  simp only [nfP]
  rw [add_assoc, add_assoc, ← add_assoc (_ • E₁), ← this]; abel

/-- An affine function at a point given in the frame `x 3; x 0 − x 3, x 5 − x 3, x 6 − x 3`. -/
theorem face_nf {x : Fin 7 → ℝ³} {S : Finset (Fin 7)} (F : Face16 x S) {v : ℝ³} {α β γ : ℝ}
    (h : v = nfP (x 3) (x 0 - x 3) (x 5 - x 3) (x 6 - x 3) α β γ) :
    F.f v = F.f (x 3) + α * (F.f (x 0) - F.f (x 3)) + β * (F.f (x 5) - F.f (x 3)) +
      γ * (F.f (x 6) - F.f (x 3)) := by
  rw [h, affine_nfP F.hN, add_sub_cancel, add_sub_cancel, add_sub_cancel]

/-- The facts of the normal form, for coordinates given abstractly: `x 2`, `x 1` lie on the
planes of `0235`, `1356`, and the type inequalities hold. -/
theorem Type16.nf_core {x : Fin 7 → ℝ³} (T : Type16 x) {a b γ₂ α₁ g d p q r : ℝ}
    (c2 : x 2 = nfP (x 3) (x 0 - x 3) (x 5 - x 3) (x 6 - x 3) a b γ₂)
    (c1 : x 1 = nfP (x 3) (x 0 - x 3) (x 5 - x 3) (x 6 - x 3) α₁ g d)
    (c4 : x 4 = nfP (x 3) (x 0 - x 3) (x 5 - x 3) (x 6 - x 3) p q r) :
    γ₂ = 0 ∧ α₁ = 0 ∧ 0 < a ∧ 0 < b ∧ 0 < g ∧ 0 < d ∧ 0 < p ∧ 0 < q ∧ 0 < r ∧
      0 < a + b - 1 ∧ 0 < g + d - 1 ∧ 0 < p + q + r - 1 ∧
      0 < b * (p + r - 1) - q * (a - 1) ∧ 0 < g * (p + r - 1) - q * (d - 1) ∧
      0 < b * r + (a - 1) * r * g - d * ((a - 1) * q - b * (p - 1)) ∧
      0 < g * p + (d - 1) * p * b - a * ((d - 1) * q - g * (r - 1)) ∧
      0 < a * (q + r - 1) - (b - 1) * p ∧ 0 < d * (p + q - 1) - (g - 1) * r ∧
      0 < a * d * (q - 1) - d * p * (b - 1) - a * r * (g - 1) := by
  have fv : ∀ {S : Finset (Fin 7)} (F : Face16 x S),
      F.f (x 2) = F.f (x 3) + a * (F.f (x 0) - F.f (x 3)) + b * (F.f (x 5) - F.f (x 3)) +
        γ₂ * (F.f (x 6) - F.f (x 3)) ∧
      F.f (x 1) = F.f (x 3) + α₁ * (F.f (x 0) - F.f (x 3)) + g * (F.f (x 5) - F.f (x 3)) +
        d * (F.f (x 6) - F.f (x 3)) ∧
      F.f (x 4) = F.f (x 3) + p * (F.f (x 0) - F.f (x 3)) + q * (F.f (x 5) - F.f (x 3)) +
        r * (F.f (x 6) - F.f (x 3)) :=
    fun F => ⟨face_nf F c2, face_nf F c1, face_nf F c4⟩
  -- `2` on `0235`, `1` on `1356`
  have hγ₂ : γ₂ = 0 := by
    have e := (fv T.q0235).1
    rw [T.q0235.zero 2 (by decide), T.q0235.zero 3 (by decide), T.q0235.zero 0 (by decide),
      T.q0235.zero 5 (by decide)] at e
    have n := (T.q0235.neg 6 (by decide)).ne
    have : γ₂ * T.q0235.f (x 6) = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_right n
  have hα₁ : α₁ = 0 := by
    have e := (fv T.q1356).2.1
    rw [T.q1356.zero 1 (by decide), T.q1356.zero 3 (by decide), T.q1356.zero 6 (by decide),
      T.q1356.zero 5 (by decide)] at e
    have n := (T.q1356.neg 0 (by decide)).ne
    have : α₁ * T.q1356.f (x 0) = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_right n
  subst hγ₂ hα₁
  have pos_of : ∀ {t F : ℝ}, t * F < 0 → F < 0 → 0 < t := fun h hF => by
    by_contra hc; push Not at hc; linarith [mul_nonneg_of_nonpos_of_nonpos hc hF.le]
  -- the facets through `3`
  obtain ⟨A2, A1, A4⟩ := fv T.q0235
  obtain ⟨B2, B1, B4⟩ := fv T.q1356
  obtain ⟨C2, C1, C4⟩ := fv T.t036
  rw [T.q0235.zero 0 (by decide), T.q0235.zero 3 (by decide), T.q0235.zero 5 (by decide)]
    at A1 A4
  rw [T.q1356.zero 5 (by decide), T.q1356.zero 3 (by decide), T.q1356.zero 6 (by decide)]
    at B2 B4
  rw [T.t036.zero 0 (by decide), T.t036.zero 3 (by decide), T.t036.zero 6 (by decide)] at C2 C1 C4
  have ha : 0 < a := pos_of (t := a) (F := T.q1356.f (x 0)) (by
    have := T.q1356.neg 2 (by decide); linarith) (T.q1356.neg 0 (by decide))
  have hb : 0 < b := pos_of (t := b) (F := T.t036.f (x 5)) (by
    have := T.t036.neg 2 (by decide); linarith) (T.t036.neg 5 (by decide))
  have hg : 0 < g := pos_of (t := g) (F := T.t036.f (x 5)) (by
    have := T.t036.neg 1 (by decide); linarith) (T.t036.neg 5 (by decide))
  have hd : 0 < d := pos_of (t := d) (F := T.q0235.f (x 6)) (by
    have := T.q0235.neg 1 (by decide); linarith) (T.q0235.neg 6 (by decide))
  have hp : 0 < p := pos_of (t := p) (F := T.q1356.f (x 0)) (by
    have := T.q1356.neg 4 (by decide); linarith) (T.q1356.neg 0 (by decide))
  have hq : 0 < q := pos_of (t := q) (F := T.t036.f (x 5)) (by
    have := T.t036.neg 4 (by decide); linarith) (T.t036.neg 5 (by decide))
  have hr : 0 < r := pos_of (t := r) (F := T.q0235.f (x 6)) (by
    have := T.q0235.neg 4 (by decide); linarith) (T.q0235.neg 6 (by decide))
  -- the triangles: `f (x 3) < 0`
  obtain ⟨G2, G1, G4⟩ := fv T.t024
  have G0 := T.t024.zero 0 (by decide); have G3 := T.t024.neg 3 (by decide)
  have G5 := T.t024.neg 5 (by decide); have G6 := T.t024.neg 6 (by decide)
  have G1' := T.t024.neg 1 (by decide)
  rw [T.t024.zero 2 (by decide), G0] at G2
  rw [T.t024.zero 4 (by decide), G0] at G4
  rw [G0] at G1
  obtain ⟨H2, H1, H4⟩ := fv T.t146
  have H6 := T.t146.zero 6 (by decide); have H3 := T.t146.neg 3 (by decide)
  have H5 := T.t146.neg 5 (by decide); have H0 := T.t146.neg 0 (by decide)
  have H2' := T.t146.neg 2 (by decide)
  rw [T.t146.zero 1 (by decide), H6] at H1
  rw [T.t146.zero 4 (by decide), H6] at H4
  rw [H6] at H2
  obtain ⟨-, -, I4⟩ := fv T.t046
  have I3 := T.t046.neg 3 (by decide); have I5 := T.t046.neg 5 (by decide)
  rw [T.t046.zero 4 (by decide), T.t046.zero 0 (by decide), T.t046.zero 6 (by decide)] at I4
  obtain ⟨J2, J1, J4⟩ := fv T.t245
  have J5 := T.t245.zero 5 (by decide); have J3 := T.t245.neg 3 (by decide)
  have J0 := T.t245.neg 0 (by decide); have J6 := T.t245.neg 6 (by decide)
  have J1' := T.t245.neg 1 (by decide)
  rw [T.t245.zero 2 (by decide), J5] at J2
  rw [T.t245.zero 4 (by decide), J5] at J4
  rw [J5] at J1
  obtain ⟨-, K1, K4⟩ := fv T.t145
  have K5 := T.t145.zero 5 (by decide); have K3 := T.t145.neg 3 (by decide)
  have K0 := T.t145.neg 0 (by decide); have K6 := T.t145.neg 6 (by decide)
  rw [T.t145.zero 1 (by decide), K5] at K1
  rw [T.t145.zero 4 (by decide), K5] at K4
  -- `b F5 = F3 (a + b − 1)`, `b r F6 = F3 [0246]`
  have g5 : b * T.t024.f (x 5) = T.t024.f (x 3) * (a + b - 1) := by linear_combination -G2
  have g6 : b * r * T.t024.f (x 6) = T.t024.f (x 3) * (b * (p + r - 1) - q * (a - 1)) := by
    linear_combination -b * G4 + q * G2
  have hab : 0 < a + b - 1 := pos_of (F := T.t024.f (x 3))
      (by linarith [g5, mul_neg_of_pos_of_neg hb G5]) G3
  have t0246 : 0 < b * (p + r - 1) - q * (a - 1) :=
    pos_of (F := T.t024.f (x 3)) (by linarith [g6, mul_neg_of_pos_of_neg (mul_pos hb hr) G6]) G3
  have t024_1 : 0 < b * r + (a - 1) * r * g - d * ((a - 1) * q - b * (p - 1)) := by
    have e : b * r * T.t024.f (x 1) =
        T.t024.f (x 3) * (b * r + (a - 1) * r * g - d * ((a - 1) * q - b * (p - 1))) := by
      linear_combination b * r * G1 + g * r * g5 + d * g6
    exact pos_of (F := T.t024.f (x 3)) (by linarith [e, mul_neg_of_pos_of_neg (mul_pos hb hr) G1'])
        G3
  have h5 : g * T.t146.f (x 5) = T.t146.f (x 3) * (g + d - 1) := by linear_combination -H1
  have h0 : p * g * T.t146.f (x 0) = T.t146.f (x 3) * (g * (p + r - 1) - q * (d - 1)) := by
    linear_combination -g * H4 + q * H1
  have hgd : 0 < g + d - 1 := pos_of (F := T.t146.f (x 3))
      (by linarith [h5, mul_neg_of_pos_of_neg hg H5]) H3
  have t0146 : 0 < g * (p + r - 1) - q * (d - 1) :=
    pos_of (F := T.t146.f (x 3)) (by linarith [h0, mul_neg_of_pos_of_neg (mul_pos hp hg) H0]) H3
  have t146_2 : 0 < g * p + (d - 1) * p * b - a * ((d - 1) * q - g * (r - 1)) := by
    have e : p * g * T.t146.f (x 2) =
        T.t146.f (x 3) * (g * p + (d - 1) * p * b - a * ((d - 1) * q - g * (r - 1))) := by
      linear_combination p * g * H2 + a * h0 + b * p * h5
    exact pos_of (F := T.t146.f (x 3)) (by linarith [e, mul_neg_of_pos_of_neg (mul_pos hp hg) H2'])
        H3
  have t046_5 : 0 < p + q + r - 1 := by
    have e : q * T.t046.f (x 5) = T.t046.f (x 3) * (p + q + r - 1) := by linear_combination -I4
    exact pos_of (F := T.t046.f (x 3)) (by linarith [e, mul_neg_of_pos_of_neg hq I5]) I3
  have j0 : a * T.t245.f (x 0) = T.t245.f (x 3) * (a + b - 1) := by linear_combination -J2
  have j6 : a * r * T.t245.f (x 6) = T.t245.f (x 3) * (a * (q + r - 1) - (b - 1) * p) := by
    linear_combination -a * J4 + p * J2
  have t245_6 : 0 < a * (q + r - 1) - (b - 1) * p :=
    pos_of (F := T.t245.f (x 3)) (by linarith [j6, mul_neg_of_pos_of_neg (mul_pos ha hr) J6]) J3
  have tB125 : 0 < a * d * (q - 1) - d * p * (b - 1) - a * r * (g - 1) := by
    have e : a * r * T.t245.f (x 1) =
        T.t245.f (x 3) * (a * d * (q - 1) - d * p * (b - 1) - a * r * (g - 1)) := by
      linear_combination a * r * J1 + d * j6
    exact pos_of (F := T.t245.f (x 3)) (by linarith [e, mul_neg_of_pos_of_neg (mul_pos ha hr) J1'])
        J3
  have k6 : d * T.t145.f (x 6) = T.t145.f (x 3) * (g + d - 1) := by linear_combination -K1
  have t145_0 : 0 < d * (p + q - 1) - (g - 1) * r := by
    have e : d * p * T.t145.f (x 0) = T.t145.f (x 3) * (d * (p + q - 1) - (g - 1) * r) := by
      linear_combination -d * K4 - r * k6
    exact pos_of (F := T.t145.f (x 3)) (by linarith [e, mul_neg_of_pos_of_neg (mul_pos hd hp) K0])
        K3
  exact ⟨rfl, rfl, ha, hb, hg, hd, hp, hq, hr, hab, hgd, t046_5, t0246, t0146, t024_1, t146_2,
    t245_6, t145_0, tB125⟩

/-- The frame determinant of type 16 is nonzero: the facets `1356`, `036`, `0235` each vanish on
three of the four points `3, 0, 5, 6`. -/
theorem Type16.det_ne {x : Fin 7 → ℝ³} (T : Type16 x) :
    det3 (x 0 - x 3) (x 5 - x 3) (x 6 - x 3) ≠ 0 := by
  refine det3_ne_zero_of_affine3 T.q1356.hN T.t036.hN T.q0235.hN (x 3) (x 0) (x 5) (x 6) ?_
  rw [T.q1356.zero 3 (by decide), T.q1356.zero 5 (by decide), T.q1356.zero 6 (by decide),
    T.t036.zero 3 (by decide), T.t036.zero 0 (by decide), T.t036.zero 6 (by decide),
    T.q0235.zero 3 (by decide), T.q0235.zero 0 (by decide), T.q0235.zero 5 (by decide)]
  have := mul_ne_zero (T.q1356.neg 0 (by decide)).ne
    (mul_ne_zero (T.t036.neg 5 (by decide)).ne (T.q0235.neg 6 (by decide)).ne)
  simp only [sub_zero, mul_zero, sub_self, zero_mul, add_zero]
  exact this

/-- **Every type-16 point set has a normal form** (§19.0).  The frame is `x 3; x 0 − x 3,
x 5 − x 3, x 6 − x 3` (a basis, `Type16.det_ne`); the coordinates of `x 2`, `x 1`, `x 4` are
Cramer ratios, `x 2`, `x 1` lie on the planes of `0235`, `1356`, and each type inequality is the
sign of a facet function at a vertex (`Type16.nf_core`). -/
noncomputable def Type16.toNF {x : Fin 7 → ℝ³} (T : Type16 x) : NF16 x :=
  let D := det3 (x 0 - x 3) (x 5 - x 3) (x 6 - x 3)
  have c2 := eq_nfP_cramer (o := x 3) T.det_ne (x 2)
  have c1 := eq_nfP_cramer (o := x 3) T.det_ne (x 1)
  have c4 := eq_nfP_cramer (o := x 3) T.det_ne (x 4)
  have H := T.nf_core c2 c1 c4
  { o := x 3, E₁ := x 0 - x 3, E₂ := x 5 - x 3, E₃ := x 6 - x 3, inj := T.inj,
    a := det3 (x 2 - x 3) (x 5 - x 3) (x 6 - x 3) / D,
    b := det3 (x 0 - x 3) (x 2 - x 3) (x 6 - x 3) / D,
    g := det3 (x 0 - x 3) (x 1 - x 3) (x 6 - x 3) / D,
    d := det3 (x 0 - x 3) (x 5 - x 3) (x 1 - x 3) / D,
    p := det3 (x 4 - x 3) (x 5 - x 3) (x 6 - x 3) / D,
    q := det3 (x 0 - x 3) (x 4 - x 3) (x 6 - x 3) / D,
    r := det3 (x 0 - x 3) (x 5 - x 3) (x 4 - x 3) / D,
    x0 := by simp only [nfP]; module
    x1 := by rw [← H.2.1]; exact c1
    x2 := by rw [← H.1]; exact c2
    x3 := by simp only [nfP]; module
    x4 := c4
    x5 := by simp only [nfP]; module
    x6 := by simp only [nfP]; module
    hD := T.det_ne
    ha := H.2.2.1, hb := H.2.2.2.1, hg := H.2.2.2.2.1, hd := H.2.2.2.2.2.1,
    hp := H.2.2.2.2.2.2.1, hq := H.2.2.2.2.2.2.2.1, hr := H.2.2.2.2.2.2.2.2.1,
    hab := H.2.2.2.2.2.2.2.2.2.1, hgd := H.2.2.2.2.2.2.2.2.2.2.1,
    t046_5 := H.2.2.2.2.2.2.2.2.2.2.2.1, t0246 := H.2.2.2.2.2.2.2.2.2.2.2.2.1,
    t0146 := H.2.2.2.2.2.2.2.2.2.2.2.2.2.1, t024_1 := H.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    t146_2 := H.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, t245_6 := H.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    t145_0 := H.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    tB125 := H.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 }


/-! ### Certificates in either orientation

The frame orientation `σ = sign D` is not fixed, so each certificate is stated with the sign
`σ = ±1` on every determinant test: for `σ = −1` the rims are read in the other order (edge
pairs) or at the view `−u` (single rims). -/

/-- `z` strictly inside the 4-corner shadow `(v, a, c, b)` at the view `u`, with the sign `σ`. -/
def EdgeHiddenσ (σ : ℝ) (u v a c b z : ℝ³) : Prop :=
  0 < σ * det3 (a - v) (z - v) u ∧ 0 < σ * det3 (c - a) (z - a) u ∧
    0 < σ * det3 (b - c) (z - c) u ∧ 0 < σ * det3 (v - b) (z - b) u

/-- `z` strictly inside the triangular shadow `(v, a, b)` at the view `u`, with the sign `σ`. -/
def TriHiddenσ (σ : ℝ) (u v a b z : ℝ³) : Prop :=
  0 < σ * det3 (a - v) (z - v) u ∧ 0 < σ * det3 (b - a) (z - a) u ∧ 0 < σ * det3 (v - b) (z - b) u

theorem EdgeMid.swap {v w a b m : ℝ³} (h : EdgeMid v w a b m) : EdgeMid v w b a m := by
  obtain ⟨s, δ, hs0, hs1, hδ, h | h | h | h⟩ := h
  · exact ⟨1 - s, δ, by linarith, by linarith, hδ, Or.inr (Or.inl (by rw [h]; module))⟩
  · exact ⟨1 - s, δ, by linarith, by linarith, hδ, Or.inl (by rw [h]; module)⟩
  · exact ⟨1 - s, δ, by linarith, by linarith, hδ, Or.inr (Or.inr (Or.inr (by rw [h]; module)))⟩
  · exact ⟨1 - s, δ, by linarith, by linarith, hδ, Or.inr (Or.inr (Or.inl (by rw [h]; module)))⟩

theorem nodup4_rev {z₀ z₁ z₂ z₃ : ℝ} (h : [z₀, z₁, z₂, z₃].Nodup) : [z₀, z₃, z₂, z₁].Nodup := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at h ⊢
  obtain ⟨⟨h1, h2, h3⟩, ⟨h4, h5⟩, h6, -⟩ := h
  exact ⟨⟨h3, h2, h1⟩, ⟨Ne.symm h6, Ne.symm h5⟩, Ne.symm h4, not_false⟩

theorem nodup3_rev {z₀ z₁ z₂ : ℝ} (h : [z₀, z₁, z₂].Nodup) : [z₀, z₂, z₁].Nodup := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at h ⊢
  obtain ⟨⟨h1, h2⟩, h3, -⟩ := h
  exact ⟨⟨h2, h1⟩, Ne.symm h3, not_false⟩

/-- A unimodal cyclic sequence stays unimodal when negated. -/
theorem IsCyclicUnimodal.neg16 {k : ℕ} [NeZero k] (hk : 2 ≤ k) {z : ZMod k → ℝ}
    (hz : IsCyclicUnimodal z) : IsCyclicUnimodal (fun i => -z i) := by
  classical
  refine isCyclicUnimodal_of_localMin_unique hk _ (fun a b e => hz.1 (neg_injective e)) ?_
  intro a b h1 h2 h3 h4
  have hc := Finset.card_le_one.mp hz.2.le
  exact hc a (by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; constructor <;> linarith)
    b (by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; constructor <;> linarith)

/-- **Corollary 14.1 in either orientation** (`isRupert_edgePair` with the far path read
`a, c, b` for `σ = 1` and `b, c, a` for `σ = −1`). -/
theorem isRupert_edgePairσ {v w a b c : ℝ³} (V : Finset ℝ³) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hvV : v ∈ V) (hwV : w ∈ V) (haV : a ∈ V) (hbV : b ∈ V) (hcV : c ∈ V)
    (q₁ : 0 < σ * det3 (a - v) (c - v) (w - v)) (q₂ : 0 < σ * det3 (c - a) (b - a) (w - v))
    (q₃ : 0 < σ * det3 (b - c) (v - c) (w - v)) (q₄ : 0 < σ * det3 (v - b) (a - b) (w - v))
    (hE : det3 (b - a) (c - a) (v - a) * det3 (b - a) (c - a) (w - a) ≤ 0)
    (hz₁ : [⟪v, w - v⟫, ⟪a, w - v⟫, ⟪c, w - v⟫, ⟪b, w - v⟫].Nodup)
    (hz₂ : [⟪w, w - v⟫, ⟪a, w - v⟫, ⟪c, w - v⟫, ⟪b, w - v⟫].Nodup)
    (hV : ∀ z ∈ V, z = v ∨ z = w ∨ z = a ∨ z = b ∨ z = c ∨ EdgeMid v w a b z ∨
      EdgeHiddenσ σ (w - v) v a c b z)
    (hnd₁ : NoHDNAt (V.erase w) (w - v)) (hnd₂ : NoHDNAt (V.erase v) (w - v)) :
    IsRupert V := by
  rcases hσ with rfl | rfl
  · simp only [one_mul] at q₁ q₂ q₃ q₄
    refine isRupert_edgePair V hvV hwV haV hbV hcV q₁ q₂ q₃ q₄ hE hz₁ hz₂ (fun z hz => ?_)
      hnd₁ hnd₂
    rcases hV z hz with h | h | h | h | h | h | ⟨h1, h2, h3, h4⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    · simp only [one_mul] at h1 h2 h3 h4
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h1, h2, h3, h4⟩)))))
  · have e1 : det3 (b - v) (c - v) (w - v) = -det3 (b - c) (v - c) (w - v) := by
      simp only [det3_expand, PiLp.sub_apply]; ring
    have e2 : det3 (c - b) (a - b) (w - v) = -det3 (c - a) (b - a) (w - v) := by
      simp only [det3_expand, PiLp.sub_apply]; ring
    have e3 : det3 (a - c) (v - c) (w - v) = -det3 (a - v) (c - v) (w - v) := by
      simp only [det3_expand, PiLp.sub_apply]; ring
    have e4 : det3 (v - a) (b - a) (w - v) = -det3 (v - b) (a - b) (w - v) := by
      simp only [det3_expand, PiLp.sub_apply]; ring
    have eE : ∀ y, det3 (a - b) (c - b) (y - b) = -det3 (b - a) (c - a) (y - a) := by
      intro y; simp only [det3_expand, PiLp.sub_apply]; ring
    refine isRupert_edgePair (a := b) (b := a) V hvV hwV hbV haV hcV (by rw [e1]; linarith)
      (by rw [e2]; linarith) (by rw [e3]; linarith) (by rw [e4]; linarith)
      (by rw [eE, eE]; linarith) ?_ ?_ (fun z hz => ?_) hnd₁ hnd₂
    · exact nodup4_rev hz₁
    · exact nodup4_rev hz₂
    rcases hV z hz with h | h | h | h | h | h | ⟨h1, h2, h3, h4⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h.swap)))))
    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨?_, ?_, ?_, ?_⟩)))))
      · rw [det3_rev]; linarith
      · rw [det3_rev]; linarith
      · rw [det3_rev]; linarith
      · rw [det3_rev]; linarith

/-- **A triangle closing in either orientation** (`isRupert_edgeTri`). -/
theorem isRupert_edgeTriσ {v w a b : ℝ³} (V : Finset ℝ³) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hvV : v ∈ V) (hwV : w ∈ V) (haV : a ∈ V) (hbV : b ∈ V)
    (hT : 0 < σ * det3 (a - v) (b - v) (w - v))
    (hz : [⟪v, w - v⟫, ⟪a, w - v⟫, ⟪b, w - v⟫].Nodup)
    (hV : ∀ z ∈ V, z = v ∨ z = w ∨ z = a ∨ z = b ∨ EdgeMid v w a b z ∨
      TriHiddenσ σ (w - v) v a b z)
    (hnd : NoHDNAt (V.erase w) (w - v)) : IsRupert V := by
  rcases hσ with rfl | rfl
  · simp only [one_mul] at hT
    refine isRupert_edgeTri V hvV hwV haV hbV hT hz (fun z hz' => ?_) hnd
    rcases hV z hz' with h | h | h | h | h | ⟨h1, h2, h3⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · simp only [one_mul] at h1 h2 h3
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h1, h2, h3⟩))))
  · have e : det3 (b - v) (a - v) (w - v) = -det3 (a - v) (b - v) (w - v) := by
      simp only [det3_expand, PiLp.sub_apply]; ring
    refine isRupert_edgeTri (a := b) (b := a) V hvV hwV hbV haV (by rw [e]; linarith) ?_
      (fun z hz' => ?_) hnd
    · exact nodup3_rev hz
    rcases hV z hz' with h | h | h | h | h | ⟨h1, h2, h3⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h.swap))))
    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨?_, ?_, ?_⟩))))
      · rw [det3_rev]; linarith
      · rw [det3_rev]; linarith
      · rw [det3_rev]; linarith

/-- **`isRupert_edgePairσ` with ties** (Lemma E with ties): only the three far depths not all
equal. -/
theorem isRupert_edgePairσ_robust {v w a b c : ℝ³} (V : Finset ℝ³) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hvV : v ∈ V) (hwV : w ∈ V) (haV : a ∈ V) (hbV : b ∈ V) (hcV : c ∈ V)
    (q₁ : 0 < σ * det3 (a - v) (c - v) (w - v)) (q₂ : 0 < σ * det3 (c - a) (b - a) (w - v))
    (q₃ : 0 < σ * det3 (b - c) (v - c) (w - v)) (q₄ : 0 < σ * det3 (v - b) (a - b) (w - v))
    (hE : det3 (b - a) (c - a) (v - a) * det3 (b - a) (c - a) (w - a) ≤ 0)
    (h3 : ¬ (⟪a, w - v⟫ = ⟪c, w - v⟫ ∧ ⟪c, w - v⟫ = ⟪b, w - v⟫))
    (hV : ∀ z ∈ V, z = v ∨ z = w ∨ z = a ∨ z = b ∨ z = c ∨ EdgeMid v w a b z ∨
      EdgeHiddenσ σ (w - v) v a c b z)
    (hnd₁ : NoHDNAt (V.erase w) (w - v)) (hnd₂ : NoHDNAt (V.erase v) (w - v)) :
    IsRupert V := by
  rcases hσ with rfl | rfl
  · simp only [one_mul] at q₁ q₂ q₃ q₄
    refine isRupert_edgePair_robust V hvV hwV haV hbV hcV q₁ q₂ q₃ q₄ hE h3 (fun z hz => ?_)
      hnd₁ hnd₂
    rcases hV z hz with h | h | h | h | h | h | ⟨h1, h2, h3, h4⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    · simp only [one_mul] at h1 h2 h3 h4
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h1, h2, h3, h4⟩)))))
  · have e1 : det3 (b - v) (c - v) (w - v) = -det3 (b - c) (v - c) (w - v) := by
      simp only [det3_expand, PiLp.sub_apply]; ring
    have e2 : det3 (c - b) (a - b) (w - v) = -det3 (c - a) (b - a) (w - v) := by
      simp only [det3_expand, PiLp.sub_apply]; ring
    have e3 : det3 (a - c) (v - c) (w - v) = -det3 (a - v) (c - v) (w - v) := by
      simp only [det3_expand, PiLp.sub_apply]; ring
    have e4 : det3 (v - a) (b - a) (w - v) = -det3 (v - b) (a - b) (w - v) := by
      simp only [det3_expand, PiLp.sub_apply]; ring
    have eE : ∀ y, det3 (a - b) (c - b) (y - b) = -det3 (b - a) (c - a) (y - a) := by
      intro y; simp only [det3_expand, PiLp.sub_apply]; ring
    refine isRupert_edgePair_robust (a := b) (b := a) V hvV hwV hbV haV hcV (by rw [e1]; linarith)
      (by rw [e2]; linarith) (by rw [e3]; linarith) (by rw [e4]; linarith)
      (by rw [eE, eE]; linarith) (fun h => h3 ⟨h.2.symm, h.1.symm⟩) (fun z hz => ?_) hnd₁ hnd₂
    rcases hV z hz with h | h | h | h | h | h | ⟨h1, h2, h3, h4⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h.swap)))))
    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨?_, ?_, ?_, ?_⟩)))))
      · rw [det3_rev]; linarith
      · rw [det3_rev]; linarith
      · rw [det3_rev]; linarith
      · rw [det3_rev]; linarith

/-- **`isRupert_edgeTriσ` with ties**: only the three depths of the rim not all equal. -/
theorem isRupert_edgeTriσ_robust {v w a b : ℝ³} (V : Finset ℝ³) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hvV : v ∈ V) (hwV : w ∈ V) (haV : a ∈ V) (hbV : b ∈ V)
    (hT : 0 < σ * det3 (a - v) (b - v) (w - v))
    (hz : ¬ (⟪v, w - v⟫ = ⟪a, w - v⟫ ∧ ⟪a, w - v⟫ = ⟪b, w - v⟫))
    (hV : ∀ z ∈ V, z = v ∨ z = w ∨ z = a ∨ z = b ∨ EdgeMid v w a b z ∨
      TriHiddenσ σ (w - v) v a b z)
    (hnd : NoHDNAt (V.erase w) (w - v)) : IsRupert V := by
  rcases hσ with rfl | rfl
  · simp only [one_mul] at hT
    refine isRupert_edgeTri_robust V hvV hwV haV hbV hT hz (fun z hz' => ?_) hnd
    rcases hV z hz' with h | h | h | h | h | ⟨h1, h2, h3⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · simp only [one_mul] at h1 h2 h3
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h1, h2, h3⟩))))
  · have e : det3 (b - v) (a - v) (w - v) = -det3 (a - v) (b - v) (w - v) := by
      simp only [det3_expand, PiLp.sub_apply]; ring
    refine isRupert_edgeTri_robust (a := b) (b := a) V hvV hwV hbV haV (by rw [e]; linarith)
      (fun h => hz ⟨h.1.trans h.2, h.2.symm⟩) (fun z hz' => ?_) hnd
    rcases hV z hz' with h | h | h | h | h | ⟨h1, h2, h3⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h.swap))))
    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨?_, ?_, ?_⟩))))
      · rw [det3_rev]; linarith
      · rw [det3_rev]; linarith
      · rw [det3_rev]; linarith

/-- **Theorem 8.9 with Theorem 7.3 at an edge view, in either orientation**
(`isRupert_of_edgeView`, at `u` or `−u`). -/
theorem isRupert_of_edgeViewσ (V M : Finset ℝ³) (u : ℝ³) (hu : u ≠ 0) {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) {k : ℕ} [NeZero k] (hk : 3 ≤ k) (x : ZMod k → ℝ³) (i₀ : ZMod k)
    (w : ℝ³) (h : ℝ) (hwV : w ∈ V) (hw : w = x i₀ - h • u) (hh : h ≠ 0) (hxV : ∀ i, x i ∈ V)
    (hxM : ∀ i, x i ∉ M)
    (hcyc : ∀ i j, j ≠ i → j ≠ i + 1 → 0 < σ * det3 (x (i + 1) - x i) (x j - x i) u)
    (hrest : ∀ y ∈ V, y ∉ M → y ≠ w → (∀ j, y ≠ x j) → ∀ i,
      0 < σ * det3 (x (i + 1) - x i) (y - x i) u)
    (hz : IsRobustUnimodal (fun i => ⟪x i, u⟫)) (hnd : NoHDNAt (V.erase w) u)
    (hM : ∀ m ∈ M, EdgeMiddle u (x i₀) w (x (i₀ + 1)) (x (i₀ - 1)) h m) : IsRupert V := by
  rcases hσ with rfl | rfl
  · simp only [one_mul] at hcyc hrest
    exact isRupert_of_edgeView_robust V M u hu hk x i₀ w h hwV hw hh hxV hxM hcyc hrest hz hnd hM
  · refine isRupert_of_edgeView_robust V M (-u) (neg_ne_zero.mpr hu) hk x i₀ w (-h) hwV
      (by rw [hw, neg_smul_neg]) (neg_ne_zero.mpr hh) hxV hxM (fun i j hi hj => ?_)
      (fun y hy hyM hyw hyx i => ?_) ?_ hnd.neg (fun m hm => ?_)
    · have := hcyc i j hi hj; rw [det3_neg_right]; linarith
    · have := hrest y hy hyM hyw hyx i; rw [det3_neg_right]; linarith
    · simp only [inner_neg_right]; exact hz.neg
    · obtain ⟨c, s, δ, hc, hs0, hs1, hδ, hm'⟩ := hM m hm
      refine ⟨c, s, -δ, ?_, hs0, hs1, neg_ne_zero.mpr hδ, ?_⟩
      · rcases hc with hc | ⟨hc, hδh⟩
        · exact Or.inl hc
        · exact Or.inr ⟨hc, by linarith [show -δ * -h = δ * h by ring]⟩
      · rcases hm' with hm' | hm'
        · exact Or.inl (by rw [hm', neg_smul_neg])
        · exact Or.inr (by rw [hm', neg_smul_neg])

/-- **Proposition 8.8 with Theorem 18.3 at a vertex view, in either orientation**
(`isRupert_of_vertexView`, at `u` or `−u`). -/
theorem isRupert_of_vertexViewσ (V M : Finset ℝ³) (u : ℝ³) (hu : u ≠ 0) {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) {k : ℕ} [NeZero k] (hk : 3 ≤ k) (x : ZMod k → ℝ³)
    (hxV : ∀ i, x i ∈ V) (hxM : ∀ i, x i ∉ M)
    (hcyc : ∀ i j, j ≠ i → j ≠ i + 1 → 0 < σ * det3 (x (i + 1) - x i) (x j - x i) u)
    (hrest : ∀ y ∈ V, y ∉ M → (∀ j, y ≠ x j) → ∀ i,
      0 < σ * det3 (x (i + 1) - x i) (y - x i) u)
    (hz : IsRobustUnimodal (fun i => ⟪x i, u⟫)) (hnd : NoHDNAt V u)
    (hM : ∀ m ∈ M, ∃ i : ZMod k, ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
      m = x i + s • (x (i + 1) - x i) + δ • u) : IsRupert V := by
  rcases hσ with rfl | rfl
  · simp only [one_mul] at hcyc hrest
    exact isRupert_of_vertexView_robust V M u hu hk x hxV hxM hcyc hrest hz hnd hM
  · refine isRupert_of_vertexView_robust V M (-u) (neg_ne_zero.mpr hu) hk x hxV hxM
      (fun i j hi hj => ?_) (fun y hy hyM hyx i => ?_) ?_ hnd.neg (fun m hm => ?_)
    · have := hcyc i j hi hj; rw [det3_neg_right]; linarith
    · have := hrest y hy hyM hyx i; rw [det3_neg_right]; linarith
    · simp only [inner_neg_right]; exact hz.neg
    · obtain ⟨i, s, δ, hs0, hs1, hδ, hm'⟩ := hM m hm
      exact ⟨i, s, -δ, hs0, hs1, neg_ne_zero.mpr hδ, by rw [hm', neg_smul_neg]⟩


/-! ### Tools for the certificates -/

theorem exists_sign {D : ℝ} (hD : D ≠ 0) : ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ 0 < σ * D := by
  rcases lt_or_gt_of_ne hD with h | h
  · exact ⟨-1, Or.inr rfl, by linarith⟩
  · exact ⟨1, Or.inl rfl, by linarith⟩

theorem pos_of_mul_pos_r {T m : ℝ} (hm : 0 < m) (h : 0 < T * m) : 0 < T := by
  by_contra hc; push Not at hc; linarith [mul_nonpos_of_nonpos_of_nonneg hc hm.le]

theorem nfV_ne_zero {E₁ E₂ E₃ : ℝ³} {α β γ : ℝ} (hD : det3 E₁ E₂ E₃ ≠ 0)
    (h : α ≠ 0 ∨ β ≠ 0 ∨ γ ≠ 0) : nfV E₁ E₂ E₃ α β γ ≠ 0 := by
  intro h0
  apply hD
  refine det3_eq_zero_of_lin (α := α) (β := β) (γ := γ) h0 ?_
  rintro ⟨h1, h2, h3⟩
  rcases h with h | h | h <;> contradiction

/-- A point given by a combination with a common denominator. -/
theorem eq_comb_div {m X Y U : ℝ³} {D₀ α β : ℝ} (hD : D₀ ≠ 0)
    (h : D₀ • (m - X) = α • (Y - X) + β • U) : m = X + (α / D₀) • (Y - X) + (β / D₀) • U := by
  have : m - X = (α / D₀) • (Y - X) + (β / D₀) • U := by
    rw [div_eq_inv_mul, div_eq_inv_mul, mul_smul, mul_smul, ← smul_add, ← h, smul_smul,
      inv_mul_cancel₀ hD, one_smul]
  rw [add_assoc, ← this]; abel

set_option linter.unnecessarySeqFocus false in
/-- A crossing of two segments with a common denominator. -/
theorem meet_of_smul {d₀ d₁ e₀ e₁ v : ℝ³} {K s t l : ℝ} (hK : K ≠ 0)
    (h : K • (e₀ - d₀) + t • (e₁ - e₀) - s • (d₁ - d₀) = l • v) :
    (e₀ + (t / K) • (e₁ - e₀)) - (d₀ + (s / K) • (d₁ - d₀)) = (l / K) • v := by
  have h2 : (e₀ + (t / K) • (e₁ - e₀)) - (d₀ + (s / K) • (d₁ - d₀)) - (l / K) • v =
      K⁻¹ • (K • (e₀ - d₀) + t • (e₁ - e₀) - s • (d₁ - d₀) - l • v) := by
    match_scalars <;> field_simp <;> ring
  rw [h, sub_self, smul_zero] at h2
  exact sub_eq_zero.mp h2

theorem nf_E_le {D X₁ X₂ P₁ P₂ : ℝ} (e₁ : X₁ = P₁) (e₂ : X₂ = P₂) (h : P₁ * P₂ ≤ 0) :
    X₁ * D * (X₂ * D) ≤ 0 := by
  rw [e₁, e₂, show P₁ * D * (P₂ * D) = (P₁ * P₂) * (D * D) by ring]
  exact mul_nonpos_of_nonpos_of_nonneg h (mul_self_nonneg D)

/-- Distinct depths along an edge `v w` of seven points in general position. -/
theorem depth_ne {x : Fin 7 → ℝ³} (hx : Function.Injective x) (hg : GenPos (univ.image x))
    {i j v w : Fin 7} (hij : i ≠ j) (hvw : v ≠ w) (h : (j ≠ v ∧ j ≠ w) ∨ (i ≠ w ∧ j ≠ w)) :
    ⟪x i, x w - x v⟫ ≠ ⟪x j, x w - x v⟫ := by
  have hm : ∀ k, x k ∈ univ.image x := fun k => mem_image_of_mem x (mem_univ k)
  refine hg.inner_ne_of_ne (hm i) (hm j) (hm v) (hm w) (hx.ne hij) (hx.ne hvw) ?_
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨hx.ne h1, hx.ne h2⟩
  · exact Or.inr ⟨hx.ne h1, hx.ne h2⟩

/-- The depth lists of the two closings at an edge `v w` with far path `a, c, b`. -/
theorem depth_nodup4 {x : Fin 7 → ℝ³} (hx : Function.Injective x) (hg : GenPos (univ.image x))
    {v w a b c : Fin 7} (h : [v, w, a, b, c].Nodup) :
    [⟪x v, x w - x v⟫, ⟪x a, x w - x v⟫, ⟪x c, x w - x v⟫, ⟪x b, x w - x v⟫].Nodup ∧
      [⟪x w, x w - x v⟫, ⟪x a, x w - x v⟫, ⟪x c, x w - x v⟫, ⟪x b, x w - x v⟫].Nodup := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at h ⊢
  obtain ⟨⟨h1, h2, h3, h4⟩, ⟨h5, h6, h7⟩, ⟨h8, h9⟩, h10, -⟩ := h
  have D := fun {i j : Fin 7} (hij : i ≠ j) (hh : (j ≠ v ∧ j ≠ w) ∨ (i ≠ w ∧ j ≠ w)) =>
    depth_ne (v := v) (w := w) hx hg hij h1 hh
  refine ⟨⟨⟨D h2 (Or.inr ⟨h1, Ne.symm h5⟩), D h4 (Or.inr ⟨h1, Ne.symm h7⟩),
    D h3 (Or.inr ⟨h1, Ne.symm h6⟩)⟩, ⟨D h9 (Or.inr ⟨Ne.symm h5, Ne.symm h7⟩),
    D h8 (Or.inr ⟨Ne.symm h5, Ne.symm h6⟩)⟩, D (Ne.symm h10) (Or.inr ⟨Ne.symm h7, Ne.symm h6⟩),
    not_false⟩, ⟨⟨D h5 (Or.inl ⟨Ne.symm h2, Ne.symm h5⟩), D h7 (Or.inl ⟨Ne.symm h4, Ne.symm h7⟩),
    D h6 (Or.inl ⟨Ne.symm h3, Ne.symm h6⟩)⟩, ⟨D h9 (Or.inr ⟨Ne.symm h5, Ne.symm h7⟩),
    D h8 (Or.inr ⟨Ne.symm h5, Ne.symm h6⟩)⟩, D (Ne.symm h10) (Or.inr ⟨Ne.symm h7, Ne.symm h6⟩),
    not_false⟩⟩

/-- The depth list of a triangle closing at an edge `v w`. -/
theorem depth_nodup3 {x : Fin 7 → ℝ³} (hx : Function.Injective x) (hg : GenPos (univ.image x))
    {v w a b : Fin 7} (h : [v, w, a, b].Nodup) :
    [⟪x v, x w - x v⟫, ⟪x a, x w - x v⟫, ⟪x b, x w - x v⟫].Nodup := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at h ⊢
  obtain ⟨⟨h1, h2, h3⟩, ⟨h5, h6⟩, h8, -⟩ := h
  have D := fun {i j : Fin 7} (hij : i ≠ j) (hh : (j ≠ v ∧ j ≠ w) ∨ (i ≠ w ∧ j ≠ w)) =>
    depth_ne (v := v) (w := w) hx hg hij h1 hh
  exact ⟨⟨D h2 (Or.inr ⟨h1, Ne.symm h5⟩), D h3 (Or.inr ⟨h1, Ne.symm h6⟩)⟩,
    D h8 (Or.inr ⟨Ne.symm h5, Ne.symm h6⟩), not_false⟩

/-- The far depths of an edge pair at an edge `v w` (far path `a, c, b`) are not all equal
(`GenPosTie`: two ties at one edge view). -/
theorem depth_far3 {x : Fin 7 → ℝ³} (hx : Function.Injective x) (hg : TieSeg (univ.image x))
    {v w a b c : Fin 7} (h : [v, w, a, b, c].Nodup) :
    ¬ (⟪x a, x w - x v⟫ = ⟪x c, x w - x v⟫ ∧ ⟪x c, x w - x v⟫ = ⟪x b, x w - x v⟫) := by
  have hm : ∀ k, x k ∈ univ.image x := fun k => mem_image_of_mem x (mem_univ k)
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at h
  obtain ⟨⟨h1, h2, h3, h4⟩, ⟨h5, h6, h7⟩, ⟨h8, h9⟩, h10, -⟩ := h
  exact hg.noTriple (hm v) (hm w) (hm a) (hm c) (hm b) (hx.ne h1) (hx.ne h9) (hx.ne (Ne.symm h10))
    (hx.ne h8)

/-- The depths of a triangle closing `v, a, b` at an edge `v w` are not all equal. -/
theorem depth_tri3 {x : Fin 7 → ℝ³} (hx : Function.Injective x) (hg : TieSeg (univ.image x))
    {v w a b : Fin 7} (h : [v, w, a, b].Nodup) :
    ¬ (⟪x v, x w - x v⟫ = ⟪x a, x w - x v⟫ ∧ ⟪x a, x w - x v⟫ = ⟪x b, x w - x v⟫) := by
  have hm : ∀ k, x k ∈ univ.image x := fun k => mem_image_of_mem x (mem_univ k)
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at h
  obtain ⟨⟨h1, h2, h3⟩, ⟨h5, h6⟩, h8, -⟩ := h
  exact hg.noTriple (hm v) (hm w) (hm v) (hm a) (hm b) (hx.ne h1) (hx.ne h2) (hx.ne h8) (hx.ne h3)


/-! ### Certificates (§18.2): named views and rim certificates -/

/-- The direction of the line of two planes, through `p₀ p₁ p₂` and through `q₀ q₁ q₂`: the
cross product of the normals, `[A B D] C − [A B C] D` (`A = p₁ − p₀`, `B = p₂ − p₀`,
`C = q₁ − q₀`, `D = q₂ − q₀`). -/
noncomputable def planeLine (p₀ p₁ p₂ q₀ q₁ q₂ : ℝ³) : ℝ³ :=
  det3 (p₁ - p₀) (p₂ - p₀) (q₂ - q₀) • (q₁ - q₀) - det3 (p₁ - p₀) (p₂ - p₀) (q₁ - q₀) • (q₂ - q₀)

/-- The six vertex crossings of the cover (§19.3–19.5), each by three labels on either plane:
`046/145`, `036/146`, `0235/046`, and their `σ`-images `046/245`, `036/024`, `1356/046`. -/
def vtx16 : Fin 6 → (Fin 7 × Fin 7 × Fin 7) × (Fin 7 × Fin 7 × Fin 7) :=
  ![((0, 4, 6), (1, 4, 5)), ((0, 3, 6), (1, 4, 6)), ((0, 3, 5), (0, 4, 6)),
    ((6, 4, 0), (2, 4, 5)), ((6, 3, 0), (2, 4, 0)), ((6, 3, 5), (6, 4, 0))]

/-- The view along the `t`-th vertex crossing. -/
noncomputable def vtxView16 (x : Fin 7 → ℝ³) (t : Fin 6) : ℝ³ :=
  planeLine (x (vtx16 t).1.1) (x (vtx16 t).1.2.1) (x (vtx16 t).1.2.2) (x (vtx16 t).2.1)
    (x (vtx16 t).2.2.1) (x (vtx16 t).2.2.2)

/-- **The named views of type 16**: the segments and the six vertex crossings. -/
noncomputable def view16 (x : Fin 7 → ℝ³) : (Fin 7 × Fin 7) ⊕ Fin 6 → ℝ³
  | .inl ij => x ij.2 - x ij.1
  | .inr t => vtxView16 x t

/-- `u` is a nonzero multiple of a named view. -/
def Named16 (x : Fin 7 → ℝ³) (u : ℝ³) : Prop :=
  ∃ v : (Fin 7 × Fin 7) ⊕ Fin 6, ∃ c : ℝ, c ≠ 0 ∧ u = c • view16 x v

/-- **A rim certificate at a named view** (3, 4 or 5 corners); every type-16 certificate
(`Cert16`) gives one (`Cert16.toN`).  With no horizontal double normal at its view it makes the
shape Rupert, and it passes to limits (`isRupert_of_tendsto_rimCert`). -/
def CertN16 (x : Fin 7 → ℝ³) : Prop := ∃ u, Named16 x u ∧ RimCert (univ.image x) u

theorem named16_seg {x : Fin 7 → ℝ³} (i j : Fin 7) : Named16 x (x j - x i) :=
  ⟨.inl (i, j), 1, one_ne_zero, (one_smul _ _).symm⟩

theorem Named16.smul {x : Fin 7 → ℝ³} {u : ℝ³} (h : Named16 x u) {c : ℝ} (hc : c ≠ 0) :
    Named16 x (c • u) := by
  obtain ⟨v, d, hd, rfl⟩ := h
  exact ⟨v, c * d, mul_ne_zero hc hd, by rw [smul_smul]⟩

theorem vtxView16_sigma (x : Fin 7 → ℝ³) (t : Fin 6) :
    vtxView16 (x ∘ sigma16) t = vtxView16 x (t + 3) := by
  fin_cases t <;> rfl

theorem Named16.sigma {x : Fin 7 → ℝ³} {u : ℝ³} (h : Named16 (x ∘ sigma16) u) : Named16 x u := by
  obtain ⟨v, c, hc, rfl⟩ := h
  rcases v with ⟨i, j⟩ | t
  · exact ⟨.inl (sigma16 i, sigma16 j), c, hc, rfl⟩
  · exact ⟨.inr (t + 3), c, hc, by simp only [view16, vtxView16_sigma]⟩

theorem CertN16.sigma {x : Fin 7 → ℝ³} (h : CertN16 (x ∘ sigma16)) : CertN16 x := by
  obtain ⟨u, hn, hc⟩ := h
  rw [image_sigma16] at hc
  exact ⟨u, hn.sigma, hc⟩

/-- **`rimCert_edgePair_robust` in either orientation** (as `isRupert_edgePairσ_robust`). -/
theorem rimCert_edgePairσ_robust {v w a b c : ℝ³} (V : Finset ℝ³) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hvV : v ∈ V) (hwV : w ∈ V) (haV : a ∈ V) (hbV : b ∈ V) (hcV : c ∈ V)
    (q₁ : 0 < σ * det3 (a - v) (c - v) (w - v)) (q₂ : 0 < σ * det3 (c - a) (b - a) (w - v))
    (q₃ : 0 < σ * det3 (b - c) (v - c) (w - v)) (q₄ : 0 < σ * det3 (v - b) (a - b) (w - v))
    (hE : det3 (b - a) (c - a) (v - a) * det3 (b - a) (c - a) (w - a) ≤ 0)
    (h3 : ¬ (⟪a, w - v⟫ = ⟪c, w - v⟫ ∧ ⟪c, w - v⟫ = ⟪b, w - v⟫))
    (hV : ∀ z ∈ V, z = v ∨ z = w ∨ z = a ∨ z = b ∨ z = c ∨ EdgeMid v w a b z ∨
      EdgeHiddenσ σ (w - v) v a c b z) : RimCert V (w - v) := by
  rcases hσ with rfl | rfl
  · simp only [one_mul] at q₁ q₂ q₃ q₄
    refine rimCert_edgePair_robust V hvV hwV haV hbV hcV q₁ q₂ q₃ q₄ hE h3 (fun z hz => ?_)
    rcases hV z hz with h | h | h | h | h | h | ⟨h1, h2, h3, h4⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    · simp only [one_mul] at h1 h2 h3 h4
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h1, h2, h3, h4⟩)))))
  · have e1 : det3 (b - v) (c - v) (w - v) = -det3 (b - c) (v - c) (w - v) := by
      simp only [det3_expand, PiLp.sub_apply]; ring
    have e2 : det3 (c - b) (a - b) (w - v) = -det3 (c - a) (b - a) (w - v) := by
      simp only [det3_expand, PiLp.sub_apply]; ring
    have e3 : det3 (a - c) (v - c) (w - v) = -det3 (a - v) (c - v) (w - v) := by
      simp only [det3_expand, PiLp.sub_apply]; ring
    have e4 : det3 (v - a) (b - a) (w - v) = -det3 (v - b) (a - b) (w - v) := by
      simp only [det3_expand, PiLp.sub_apply]; ring
    have eE : ∀ y, det3 (a - b) (c - b) (y - b) = -det3 (b - a) (c - a) (y - a) := by
      intro y; simp only [det3_expand, PiLp.sub_apply]; ring
    refine rimCert_edgePair_robust (a := b) (b := a) V hvV hwV hbV haV hcV (by rw [e1]; linarith)
      (by rw [e2]; linarith) (by rw [e3]; linarith) (by rw [e4]; linarith)
      (by rw [eE, eE]; linarith) (fun h => h3 ⟨h.2.symm, h.1.symm⟩) (fun z hz => ?_)
    rcases hV z hz with h | h | h | h | h | h | ⟨h1, h2, h3, h4⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h.swap)))))
    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨?_, ?_, ?_, ?_⟩)))))
      · rw [det3_rev]; linarith
      · rw [det3_rev]; linarith
      · rw [det3_rev]; linarith
      · rw [det3_rev]; linarith

/-- **`rimCert_edgeTri_robust` in either orientation**. -/
theorem rimCert_edgeTriσ_robust {v w a b : ℝ³} (V : Finset ℝ³) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hvV : v ∈ V) (hwV : w ∈ V) (haV : a ∈ V) (hbV : b ∈ V)
    (hT : 0 < σ * det3 (a - v) (b - v) (w - v))
    (hz : ¬ (⟪v, w - v⟫ = ⟪a, w - v⟫ ∧ ⟪a, w - v⟫ = ⟪b, w - v⟫))
    (hV : ∀ z ∈ V, z = v ∨ z = w ∨ z = a ∨ z = b ∨ EdgeMid v w a b z ∨
      TriHiddenσ σ (w - v) v a b z) : RimCert V (w - v) := by
  rcases hσ with rfl | rfl
  · simp only [one_mul] at hT
    refine rimCert_edgeTri_robust V hvV hwV haV hbV hT hz (fun z hz' => ?_)
    rcases hV z hz' with h | h | h | h | h | ⟨h1, h2, h3⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · simp only [one_mul] at h1 h2 h3
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h1, h2, h3⟩))))
  · have e : det3 (b - v) (a - v) (w - v) = -det3 (a - v) (b - v) (w - v) := by
      simp only [det3_expand, PiLp.sub_apply]; ring
    refine rimCert_edgeTri_robust (a := b) (b := a) V hvV hwV hbV haV (by rw [e]; linarith)
      (fun h => hz ⟨h.1.trans h.2, h.2.symm⟩) (fun z hz' => ?_)
    rcases hV z hz' with h | h | h | h | h | ⟨h1, h2, h3⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h.swap))))
    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨?_, ?_, ?_⟩))))
      · rw [det3_rev]; linarith
      · rw [det3_rev]; linarith
      · rw [det3_rev]; linarith

/-! ### The certificates of the cover, by family -/

/-- The labelled edge pairs `(v, w, a, b, c)` of the cover (Theorem 19.2: `06`, `14`, `35`,
`02`, `25`, `03`, `36`) and their images under `σ = (06)(12)`. -/
def ePairList16 : Finset (Fin 7 × Fin 7 × Fin 7 × Fin 7 × Fin 7) :=
  {(0, 6, 4, 3, 5), (1, 4, 6, 5, 3), (3, 5, 1, 2, 4), (3, 5, 1, 0, 4), (3, 5, 6, 2, 4),
    (0, 2, 3, 4, 6), (2, 5, 3, 4, 6), (0, 3, 6, 2, 4), (3, 6, 0, 1, 4),
    (6, 0, 4, 3, 5), (2, 4, 0, 5, 3), (3, 5, 2, 1, 4), (3, 5, 2, 6, 4), (3, 5, 0, 1, 4),
    (6, 1, 3, 4, 0), (1, 5, 3, 4, 0), (6, 3, 0, 1, 4), (3, 0, 6, 2, 4)}

/-- The labelled triangle closings `(v, w, a, b)` of the cover (D5 at `16`, D6 at `15`, D7 at
`35`) and their images under `σ`. -/
def eTriList16 : Finset (Fin 7 × Fin 7 × Fin 7 × Fin 7) :=
  {(1, 6, 5, 4), (3, 5, 6, 0), (1, 5, 4, 6), (2, 0, 5, 4), (3, 5, 0, 6), (2, 5, 4, 0)}

/-- The named views of the pair certificates of Lemmas 19.3–19.5 (`35`, `15`, `36`, the three
vertex crossings) and their images under `σ`. -/
def pairsViews16 : Finset ((Fin 7 × Fin 7) ⊕ Fin 6) :=
  {.inl (3, 5), .inl (1, 5), .inl (2, 5), .inl (3, 6), .inl (3, 0), .inr 0, .inr 1, .inr 2,
    .inr 3, .inr 4, .inr 5}

/-- The hypotheses of `rimCert_edgePairσ_robust` (an edge pair of Lemma E). -/
def EPairData (V : Finset ℝ³) (σ : ℝ) (v w a b c : ℝ³) : Prop :=
  (σ = 1 ∨ σ = -1) ∧ 0 < σ * det3 (a - v) (c - v) (w - v) ∧
    0 < σ * det3 (c - a) (b - a) (w - v) ∧ 0 < σ * det3 (b - c) (v - c) (w - v) ∧
    0 < σ * det3 (v - b) (a - b) (w - v) ∧
    det3 (b - a) (c - a) (v - a) * det3 (b - a) (c - a) (w - a) ≤ 0 ∧
    ¬ (⟪a, w - v⟫ = ⟪c, w - v⟫ ∧ ⟪c, w - v⟫ = ⟪b, w - v⟫) ∧
    ∀ z ∈ V, z = v ∨ z = w ∨ z = a ∨ z = b ∨ z = c ∨ EdgeMid v w a b z ∨
      EdgeHiddenσ σ (w - v) v a c b z

/-- The hypotheses of `rimCert_edgeTriσ_robust` (a triangle closing). -/
def ETriData (V : Finset ℝ³) (σ : ℝ) (v w a b : ℝ³) : Prop :=
  (σ = 1 ∨ σ = -1) ∧ 0 < σ * det3 (a - v) (b - v) (w - v) ∧
    ¬ (⟪v, w - v⟫ = ⟪a, w - v⟫ ∧ ⟪a, w - v⟫ = ⟪b, w - v⟫) ∧
    ∀ z ∈ V, z = v ∨ z = w ∨ z = a ∨ z = b ∨ EdgeMid v w a b z ∨ TriHiddenσ σ (w - v) v a b z

/-- An edge-pair certificate of the cover. -/
def CertE16 (x : Fin 7 → ℝ³) : Prop :=
  ∃ v w a b c : Fin 7, (v, w, a, b, c) ∈ ePairList16 ∧
    ∃ σ : ℝ, EPairData (univ.image x) σ (x v) (x w) (x a) (x b) (x c)

/-- A triangle-closing certificate of the cover. -/
def CertT16 (x : Fin 7 → ℝ³) : Prop :=
  ∃ v w a b : Fin 7, (v, w, a, b) ∈ eTriList16 ∧
    ∃ σ : ℝ, ETriData (univ.image x) σ (x v) (x w) (x a) (x b)

/-- The labelled four-corner pair certificates of Lemmas 19.3–19.5 (view, rim) and their images
under `σ`. -/
def pQuadLabels16 : Finset (((Fin 7 × Fin 7) ⊕ Fin 6) × (Fin 7 × Fin 7 × Fin 7 × Fin 7)) :=
  {(.inl (3, 5), (3, 1, 4, 2)), (.inl (3, 5), (3, 1, 4, 0)), (.inr 0, (4, 6, 3, 5)),
    (.inr 1, (6, 3, 5, 4)), (.inl (1, 5), (1, 4, 0, 6)), (.inr 2, (0, 5, 1, 6)),
    (.inl (3, 5), (3, 2, 4, 1)), (.inl (3, 5), (3, 2, 4, 6)), (.inr 3, (4, 0, 3, 5)),
    (.inr 4, (0, 3, 5, 4)), (.inl (2, 5), (2, 4, 6, 0)), (.inr 5, (6, 5, 2, 0))}

/-- The labelled five-corner pair certificates of Lemmas 19.4, 19.5 and their images. -/
def pQuintLabels16 :
    Finset (((Fin 7 × Fin 7) ⊕ Fin 6) × (Fin 7 × Fin 7 × Fin 7 × Fin 7 × Fin 7)) :=
  {(.inl (3, 6), (6, 0, 2, 4, 1)), (.inr 1, (6, 3, 5, 2, 4)), (.inl (1, 5), (1, 4, 2, 0, 6)),
    (.inl (3, 0), (0, 6, 1, 4, 2)), (.inr 4, (0, 3, 5, 1, 4)), (.inl (2, 5), (2, 4, 1, 6, 0))}

/-- A pair certificate of Lemmas 19.3–19.5: a labelled rim certificate (four or five corners) at
one of their views. -/
def CertP16 (x : Fin 7 → ℝ³) : Prop :=
  (∃ v l, (v, l) ∈ pQuadLabels16 ∧ ∃ c : ℝ, c ≠ 0 ∧ RimCertPts (univ.image x)
    (c • view16 x v) (quad (x l.1) (x l.2.1) (x l.2.2.1) (x l.2.2.2))) ∨
  (∃ v l, (v, l) ∈ pQuintLabels16 ∧ ∃ c : ℝ, c ≠ 0 ∧ RimCertPts (univ.image x)
    (c • view16 x v) (quint (x l.1) (x l.2.1) (x l.2.2.1) (x l.2.2.2.1) (x l.2.2.2.2)))

/-- **A type-16 certificate**: an edge pair (Lemma E), a triangle closing, or a pair certificate
of Lemmas 19.3–19.5.  Every step of the cover (§19.2–19.5) ends in one; each is a rim certificate
at a named view (`Cert16.toN`), and the families record the data that §22 uses at the limit. -/
def Cert16 (x : Fin 7 → ℝ³) : Prop := CertE16 x ∨ CertT16 x ∨ CertP16 x

theorem cert16_ePair {x : Fin 7 → ℝ³} (v w a b c : Fin 7) (ht : (v, w, a, b, c) ∈ ePairList16)
    {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (q₁ : 0 < σ * det3 (x a - x v) (x c - x v) (x w - x v))
    (q₂ : 0 < σ * det3 (x c - x a) (x b - x a) (x w - x v))
    (q₃ : 0 < σ * det3 (x b - x c) (x v - x c) (x w - x v))
    (q₄ : 0 < σ * det3 (x v - x b) (x a - x b) (x w - x v))
    (hE : det3 (x b - x a) (x c - x a) (x v - x a) * det3 (x b - x a) (x c - x a) (x w - x a) ≤ 0)
    (h3 : ¬ (⟪x a, x w - x v⟫ = ⟪x c, x w - x v⟫ ∧ ⟪x c, x w - x v⟫ = ⟪x b, x w - x v⟫))
    (hV : ∀ z ∈ univ.image x, z = x v ∨ z = x w ∨ z = x a ∨ z = x b ∨ z = x c ∨
      EdgeMid (x v) (x w) (x a) (x b) z ∨ EdgeHiddenσ σ (x w - x v) (x v) (x a) (x c) (x b) z) :
    Cert16 x :=
  Or.inl ⟨v, w, a, b, c, ht, σ, hσ, q₁, q₂, q₃, q₄, hE, h3, hV⟩

theorem cert16_eTri {x : Fin 7 → ℝ³} (v w a b : Fin 7) (ht : (v, w, a, b) ∈ eTriList16)
    {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (hT : 0 < σ * det3 (x a - x v) (x b - x v) (x w - x v))
    (hz : ¬ (⟪x v, x w - x v⟫ = ⟪x a, x w - x v⟫ ∧ ⟪x a, x w - x v⟫ = ⟪x b, x w - x v⟫))
    (hV : ∀ z ∈ univ.image x, z = x v ∨ z = x w ∨ z = x a ∨ z = x b ∨
      EdgeMid (x v) (x w) (x a) (x b) z ∨ TriHiddenσ σ (x w - x v) (x v) (x a) (x b) z) :
    Cert16 x :=
  Or.inr (Or.inl ⟨v, w, a, b, ht, σ, hσ, hT, hz, hV⟩)

theorem Cert16.mkPQ {x : Fin 7 → ℝ³} (v : (Fin 7 × Fin 7) ⊕ Fin 6) (i₀ i₁ i₂ i₃ : Fin 7)
    (hm : (v, (i₀, i₁, i₂, i₃)) ∈ pQuadLabels16) {u : ℝ³}
    (hn : ∃ c : ℝ, c ≠ 0 ∧ u = c • view16 x v)
    (h : RimCertPts (univ.image x) u (quad (x i₀) (x i₁) (x i₂) (x i₃))) : Cert16 x := by
  obtain ⟨c, hc, rfl⟩ := hn
  exact Or.inr (Or.inr (Or.inl ⟨v, (i₀, i₁, i₂, i₃), hm, c, hc, h⟩))

theorem Cert16.mkPQ5 {x : Fin 7 → ℝ³} (v : (Fin 7 × Fin 7) ⊕ Fin 6) (i₀ i₁ i₂ i₃ i₄ : Fin 7)
    (hm : (v, (i₀, i₁, i₂, i₃, i₄)) ∈ pQuintLabels16) {u : ℝ³}
    (hn : ∃ c : ℝ, c ≠ 0 ∧ u = c • view16 x v)
    (h : RimCertPts (univ.image x) u (quint (x i₀) (x i₁) (x i₂) (x i₃) (x i₄))) : Cert16 x := by
  obtain ⟨c, hc, rfl⟩ := hn
  exact Or.inr (Or.inr (Or.inr ⟨v, (i₀, i₁, i₂, i₃, i₄), hm, c, hc, h⟩))

theorem namedAt16_seg {x : Fin 7 → ℝ³} (i j : Fin 7) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) :
    ∃ c : ℝ, c ≠ 0 ∧ σ • (x j - x i) = c • view16 x (.inl (i, j)) :=
  ⟨σ, by rcases hσ with rfl | rfl <;> norm_num, rfl⟩

theorem mem_image7 {x : Fin 7 → ℝ³} (i : Fin 7) : x i ∈ univ.image x :=
  Finset.mem_image_of_mem x (mem_univ i)

/-- Every type-16 certificate is a rim certificate at a named view. -/
theorem Cert16.toN {x : Fin 7 → ℝ³} (h : Cert16 x) : CertN16 x := by
  rcases h with ⟨v, w, a, b, c, -, σ, hσ, q₁, q₂, q₃, q₄, hE, h3, hV⟩ |
    ⟨v, w, a, b, -, σ, hσ, hT, hz, hV⟩ | ⟨v, l, -, c, hc, hr⟩ | ⟨v, l, -, c, hc, hr⟩
  · exact ⟨_, named16_seg v w, rimCert_edgePairσ_robust _ hσ (mem_image7 v) (mem_image7 w)
      (mem_image7 a) (mem_image7 b) (mem_image7 c) q₁ q₂ q₃ q₄ hE h3 hV⟩
  · exact ⟨_, named16_seg v w, rimCert_edgeTriσ_robust _ hσ (mem_image7 v) (mem_image7 w)
      (mem_image7 a) (mem_image7 b) hT hz hV⟩
  · exact ⟨_, ⟨v, c, hc, rfl⟩, hr.rimCert (Or.inr (Or.inl rfl))⟩
  · exact ⟨_, ⟨v, c, hc, rfl⟩, hr.rimCert (Or.inr (Or.inr rfl))⟩

set_option maxRecDepth 20000 in
theorem ePairList16_sigma : ∀ t ∈ ePairList16,
    (sigma16 t.1, sigma16 t.2.1, sigma16 t.2.2.1, sigma16 t.2.2.2.1, sigma16 t.2.2.2.2) ∈
      ePairList16 := by decide

set_option maxRecDepth 20000 in
theorem eTriList16_sigma : ∀ t ∈ eTriList16,
    (sigma16 t.1, sigma16 t.2.1, sigma16 t.2.2.1, sigma16 t.2.2.2) ∈ eTriList16 := by decide

/-- The views under `σ`. -/
def sigmaView16 : (Fin 7 × Fin 7) ⊕ Fin 6 → (Fin 7 × Fin 7) ⊕ Fin 6
  | .inl (i, j) => .inl (sigma16 i, sigma16 j)
  | .inr t => .inr (t + 3)

theorem view16_sigma (x : Fin 7 → ℝ³) (v : (Fin 7 × Fin 7) ⊕ Fin 6) :
    view16 (x ∘ sigma16) v = view16 x (sigmaView16 v) := by
  rcases v with ⟨i, j⟩ | t
  · rfl
  · simp only [view16, sigmaView16, vtxView16_sigma]

set_option maxRecDepth 20000 in
theorem pQuadLabels16_sigma : ∀ q ∈ pQuadLabels16, (sigmaView16 q.1, (sigma16 q.2.1,
    sigma16 q.2.2.1, sigma16 q.2.2.2.1, sigma16 q.2.2.2.2)) ∈ pQuadLabels16 := by decide

set_option maxRecDepth 20000 in
theorem pQuintLabels16_sigma : ∀ q ∈ pQuintLabels16, (sigmaView16 q.1, (sigma16 q.2.1,
    sigma16 q.2.2.1, sigma16 q.2.2.2.1, sigma16 q.2.2.2.2.1, sigma16 q.2.2.2.2.2)) ∈
      pQuintLabels16 := by
  intro q hq
  simp only [pQuintLabels16, Finset.mem_insert, Finset.mem_singleton] at hq ⊢
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [sigmaView16, sigma16, Prod.mk.injEq, Sum.inl.injEq, reduceCtorEq, and_false,
      false_or, or_false] <;> decide

theorem Cert16.sigma {x : Fin 7 → ℝ³} (h : Cert16 (x ∘ sigma16)) : Cert16 x := by
  rcases h with ⟨v, w, a, b, c, ht, σ, hd⟩ | ⟨v, w, a, b, ht, σ, hd⟩ |
    ⟨v, l, hl, c, hc, hr⟩ | ⟨v, l, hl, c, hc, hr⟩
  · rw [image_sigma16] at hd
    exact Or.inl ⟨_, _, _, _, _, ePairList16_sigma _ ht, σ, hd⟩
  · rw [image_sigma16] at hd
    exact Or.inr (Or.inl ⟨_, _, _, _, eTriList16_sigma _ ht, σ, hd⟩)
  · rw [image_sigma16, view16_sigma] at hr
    exact Or.inr (Or.inr (Or.inl ⟨_, _, pQuadLabels16_sigma (v, l) hl, c, hc, hr⟩))
  · rw [image_sigma16, view16_sigma] at hr
    exact Or.inr (Or.inr (Or.inr ⟨_, _, pQuintLabels16_sigma (v, l) hl, c, hc, hr⟩))

/-- Rewrite the points of a normal form and the frame determinants: every test becomes
`σ * (det3c … * D)`. -/
macro "nf_simp " N:term:max : tactic =>
  `(tactic| simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue,
    NF16.x0 $N, NF16.x1 $N, NF16.x2 $N, NF16.x3 $N, NF16.x4 $N, NF16.x5 $N,
    NF16.x6 $N, nfP_sub, det3_nfV])

/-- A vector identity of a normal form, checked coordinatewise. -/
macro "nf_vec " N:term:max : tactic =>
  `(tactic| (nf_simp $N; ext; simp only [nfP, nfV, PiLp.add_apply, PiLp.sub_apply,
    PiLp.smul_apply, PiLp.neg_apply, smul_eq_mul]; ring))

/-- An orientation test of a normal form from the sign of its polynomial. -/
macro "nf_test " N:term:max hσD:term:max h:term : tactic =>
  `(tactic| (nf_simp $N; exact nf_pos $hσD $h (by simp only [det3c]; ring)))

end Minimality

end
