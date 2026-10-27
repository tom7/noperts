module

public import Minimality.Type08Slide

@[expose] public section

namespace Minimality
open scoped RealInnerProductSpace Topology
open Filter

/-- The determinant of three rows. -/
def hdet (x1 y1 z1 x2 y2 z2 x3 y3 z3 : ℝ) : ℝ :=
  x1 * (y2 * z3 - z2 * y3) - y1 * (x2 * z3 - z2 * x3) + z1 * (x2 * y3 - y2 * x3)

/-- **Coordinate silhouette lemma.**  Two planes with normals `n₁ = (a₁,b₁,c₁)`, `n₂ = (a₂,b₂,c₂)`
meet in a line of direction `t` (`n₁·t = n₂·t = 0`); `p` lies in the plane `2` and `q` in the
plane `1`.  Then `(n₁·p)(n₂·q) det(t,y,u) = (n₁·y n₂·u − n₂·y n₁·u) det(t,p,q)`. -/
theorem csl_identity (a1 b1 c1 a2 b2 c2 t1 t2 t3 p1 p2 p3 q1 q2 q3 y1 y2 y3 u1 u2 u3 : ℝ)
    (h1 : a1 * t1 + b1 * t2 + c1 * t3 = 0) (h2 : a2 * t1 + b2 * t2 + c2 * t3 = 0)
    (h3 : a2 * p1 + b2 * p2 + c2 * p3 = 0) (h4 : a1 * q1 + b1 * q2 + c1 * q3 = 0) :
    (a1 * p1 + b1 * p2 + c1 * p3) * (a2 * q1 + b2 * q2 + c2 * q3) *
        hdet t1 t2 t3 y1 y2 y3 u1 u2 u3 =
      ((a1 * y1 + b1 * y2 + c1 * y3) * (a2 * u1 + b2 * u2 + c2 * u3) -
        (a2 * y1 + b2 * y2 + c2 * y3) * (a1 * u1 + b1 * u2 + c1 * u3)) *
        hdet t1 t2 t3 p1 p2 p3 q1 q2 q3 := by
  -- w = n₁ × n₂
  set w1 := b1 * c2 - c1 * b2 with hw1
  set w2 := c1 * a2 - a1 * c2 with hw2
  set w3 := a1 * b2 - b1 * a2 with hw3
  have hd : t1 * t1 + t2 * t2 + t3 * t3 = 0 ∨ 0 < t1 * t1 + t2 * t2 + t3 * t3 := by
    rcases (by nlinarith [mul_self_nonneg t1, mul_self_nonneg t2, mul_self_nonneg t3] : 0 ≤ t1 * t1 + t2 * t2 + t3 * t3).eq_or_lt with h | h
    · exact Or.inl h.symm
    · exact Or.inr h
  rcases hd with h0 | hpos
  · have ht1 : t1 = 0 := by nlinarith [sq_nonneg t1, sq_nonneg t2, sq_nonneg t3]
    have ht2 : t2 = 0 := by nlinarith [sq_nonneg t1, sq_nonneg t2, sq_nonneg t3]
    have ht3 : t3 = 0 := by nlinarith [sq_nonneg t1, sq_nonneg t2, sq_nonneg t3]
    subst ht1 ht2 ht3
    simp [hdet]
  -- w × t = 0
  have hx1 : w2 * t3 - w3 * t2 = 0 := by
    simp only [hw2, hw3]; linear_combination a2 * h1 - a1 * h2
  have hx2 : w3 * t1 - w1 * t3 = 0 := by
    simp only [hw3, hw1]; linear_combination b2 * h1 - b1 * h2
  have hx3 : w1 * t2 - w2 * t1 = 0 := by
    simp only [hw1, hw2]; linear_combination c2 * h1 - c1 * h2
  -- |t|² w = (w·t) t
  have hs1 : (t1 * t1 + t2 * t2 + t3 * t3) * w1 = (w1 * t1 + w2 * t2 + w3 * t3) * t1 := by
    linear_combination t2 * hx3 - t3 * hx2
  have hs2 : (t1 * t1 + t2 * t2 + t3 * t3) * w2 = (w1 * t1 + w2 * t2 + w3 * t3) * t2 := by
    linear_combination t3 * hx1 - t1 * hx3
  have hs3 : (t1 * t1 + t2 * t2 + t3 * t3) * w3 = (w1 * t1 + w2 * t2 + w3 * t3) * t3 := by
    linear_combination t1 * hx2 - t2 * hx1
  -- Binet–Cauchy
  have bc : ∀ y1 y2 y3 u1 u2 u3 : ℝ,
      (a1 * y1 + b1 * y2 + c1 * y3) * (a2 * u1 + b2 * u2 + c2 * u3) -
        (a2 * y1 + b2 * y2 + c2 * y3) * (a1 * u1 + b1 * u2 + c1 * u3) =
      w1 * (y2 * u3 - y3 * u2) + w2 * (y3 * u1 - y1 * u3) + w3 * (y1 * u2 - y2 * u1) := by
    intro y1 y2 y3 u1 u2 u3; simp only [hw1, hw2, hw3]; ring
  have key : ∀ y1 y2 y3 u1 u2 u3 : ℝ,
      (t1 * t1 + t2 * t2 + t3 * t3) *
        ((a1 * y1 + b1 * y2 + c1 * y3) * (a2 * u1 + b2 * u2 + c2 * u3) -
          (a2 * y1 + b2 * y2 + c2 * y3) * (a1 * u1 + b1 * u2 + c1 * u3)) =
      (w1 * t1 + w2 * t2 + w3 * t3) * hdet t1 t2 t3 y1 y2 y3 u1 u2 u3 := by
    intro y1 y2 y3 u1 u2 u3
    rw [bc]
    simp only [hdet]
    linear_combination (y2 * u3 - y3 * u2) * hs1 + (y3 * u1 - y1 * u3) * hs2 +
      (y1 * u2 - y2 * u1) * hs3
  have kp := key p1 p2 p3 q1 q2 q3
  have e3 : (a2 * p1 + b2 * p2 + c2 * p3) = 0 := h3
  have e4 : (a1 * q1 + b1 * q2 + c1 * q3) = 0 := h4
  rw [e3, zero_mul, sub_zero] at kp
  have ky := key y1 y2 y3 u1 u2 u3
  apply mul_left_cancel₀ hpos.ne'
  calc (t1 * t1 + t2 * t2 + t3 * t3) *
        ((a1 * p1 + b1 * p2 + c1 * p3) * (a2 * q1 + b2 * q2 + c2 * q3) *
          hdet t1 t2 t3 y1 y2 y3 u1 u2 u3)
      = ((t1 * t1 + t2 * t2 + t3 * t3) *
        ((a1 * p1 + b1 * p2 + c1 * p3) * (a2 * q1 + b2 * q2 + c2 * q3))) *
          hdet t1 t2 t3 y1 y2 y3 u1 u2 u3 := by ring
    _ = ((w1 * t1 + w2 * t2 + w3 * t3) * hdet t1 t2 t3 p1 p2 p3 q1 q2 q3) *
          hdet t1 t2 t3 y1 y2 y3 u1 u2 u3 := by rw [kp]
    _ = hdet t1 t2 t3 p1 p2 p3 q1 q2 q3 *
          ((w1 * t1 + w2 * t2 + w3 * t3) * hdet t1 t2 t3 y1 y2 y3 u1 u2 u3) := by ring
    _ = hdet t1 t2 t3 p1 p2 p3 q1 q2 q3 * ((t1 * t1 + t2 * t2 + t3 * t3) *
        ((a1 * y1 + b1 * y2 + c1 * y3) * (a2 * u1 + b2 * u2 + c2 * u3) -
          (a2 * y1 + b2 * y2 + c2 * y3) * (a1 * u1 + b1 * u2 + c1 * u3))) := by rw [ky]
    _ = _ := by ring


/-! ### Coordinates: points and affine functions -/

/-- A point in the horizontal-end frame `(x, y, z)`. -/
structure V3 where
  x : ℝ
  y : ℝ
  z : ℝ

/-- An affine function `a x + b y + c z + d`. -/
structure Fc where
  a : ℝ
  b : ℝ
  c : ℝ
  d : ℝ

def Fc.ev (F : Fc) (p : V3) : ℝ := F.a * p.x + F.b * p.y + F.c * p.z + F.d

def Fc.lin (F : Fc) (u : V3) : ℝ := F.a * u.x + F.b * u.y + F.c * u.z

/-- The orientation test of the triangle `P Q S` at the view `u`. -/
def tst (u P Q S : V3) : ℝ :=
  hdet (Q.x - P.x) (Q.y - P.y) (Q.z - P.z) (S.x - P.x) (S.y - P.y) (S.z - P.z) u.x u.y u.z

/-- The view `(E, 0, −δ U)` of the horizontal end. -/
def vw (E U δ : ℝ) : V3 := ⟨E, 0, -(δ * U)⟩

/-- **The silhouette sign lemma.**  `F₁`, `F₂` vanish at `P`, `Q`; `Y₁` lies on `F₂` and
strictly beneath `F₁`; `Y₂` lies on `F₁` and strictly beneath `F₂`; `Y` is exposed strictly
(`hS`).  Then the test of `Y` against the edge `P Q` has the sign of `λ = det(Q−P, Y₁−P, Y₂−P)`. -/
theorem csl_pos (F₁ F₂ : Fc) (P Q Y₁ Y₂ Y u : V3) (hPQ : P ≠ Q)
    (hP1 : F₁.ev P = 0) (hQ1 : F₁.ev Q = 0) (hP2 : F₂.ev P = 0) (hQ2 : F₂.ev Q = 0)
    (hY1 : F₂.ev Y₁ = 0) (hY1' : F₁.ev Y₁ < 0) (hY2 : F₁.ev Y₂ = 0) (hY2' : F₂.ev Y₂ < 0)
    (hS : 0 < F₁.ev Y * F₂.lin u - F₂.ev Y * F₁.lin u) :
    0 < tst u P Q Y * hdet (Q.x - P.x) (Q.y - P.y) (Q.z - P.z) (Y₁.x - P.x) (Y₁.y - P.y)
      (Y₁.z - P.z) (Y₂.x - P.x) (Y₂.y - P.y) (Y₂.z - P.z) := by
  have key := fun y1 y2 y3 u1 u2 u3 =>
    csl_identity F₁.a F₁.b F₁.c F₂.a F₂.b F₂.c (Q.x - P.x) (Q.y - P.y) (Q.z - P.z)
      (Y₁.x - P.x) (Y₁.y - P.y) (Y₁.z - P.z) (Y₂.x - P.x) (Y₂.y - P.y) (Y₂.z - P.z) y1 y2 y3
      u1 u2 u3 (by simp only [Fc.ev] at hP1 hQ1; linarith) (by simp only [Fc.ev] at hP2 hQ2; linarith)
      (by simp only [Fc.ev] at hP2 hY1; linarith) (by simp only [Fc.ev] at hP1 hY2; linarith)
  set L := (F₁.a * (Y₁.x - P.x) + F₁.b * (Y₁.y - P.y) + F₁.c * (Y₁.z - P.z)) *
    (F₂.a * (Y₂.x - P.x) + F₂.b * (Y₂.y - P.y) + F₂.c * (Y₂.z - P.z)) with hL
  have hLpos : 0 < L := by
    have e1 : F₁.a * (Y₁.x - P.x) + F₁.b * (Y₁.y - P.y) + F₁.c * (Y₁.z - P.z) = F₁.ev Y₁ := by
      simp only [Fc.ev] at hP1 ⊢; linarith
    have e2 : F₂.a * (Y₂.x - P.x) + F₂.b * (Y₂.y - P.y) + F₂.c * (Y₂.z - P.z) = F₂.ev Y₂ := by
      simp only [Fc.ev] at hP2 ⊢; linarith
    rw [hL, e1, e2]; exact mul_pos_of_neg_of_neg hY1' hY2'
  set Z := hdet (Q.x - P.x) (Q.y - P.y) (Q.z - P.z) (Y₁.x - P.x) (Y₁.y - P.y)
      (Y₁.z - P.z) (Y₂.x - P.x) (Y₂.y - P.y) (Y₂.z - P.z) with hZ
  have hZne : Z ≠ 0 := by
    intro hZ0
    have k1 := key 1 0 0 0 1 0
    have k2 := key 0 1 0 0 0 1
    have k3 := key 0 0 1 1 0 0
    rw [hZ0, mul_zero] at k1 k2 k3
    have d1 := (mul_eq_zero.mp k1).resolve_left hLpos.ne'
    have d2 := (mul_eq_zero.mp k2).resolve_left hLpos.ne'
    have d3 := (mul_eq_zero.mp k3).resolve_left hLpos.ne'
    simp only [hdet] at d1 d2 d3
    apply hPQ
    have h1 : Q.x - P.x = 0 := by linarith
    have h2 : Q.y - P.y = 0 := by linarith
    have h3 : Q.z - P.z = 0 := by linarith
    cases P; cases Q; simp only at h1 h2 h3; simp only [V3.mk.injEq]; refine ⟨?_, ?_, ?_⟩ <;> linarith
  have hk := key (Y.x - P.x) (Y.y - P.y) (Y.z - P.z) u.x u.y u.z
  have eY : F₁.a * (Y.x - P.x) + F₁.b * (Y.y - P.y) + F₁.c * (Y.z - P.z) = F₁.ev Y := by
    simp only [Fc.ev] at hP1 ⊢; linarith
  have eY2 : F₂.a * (Y.x - P.x) + F₂.b * (Y.y - P.y) + F₂.c * (Y.z - P.z) = F₂.ev Y := by
    simp only [Fc.ev] at hP2 ⊢; linarith
  rw [eY, eY2] at hk
  have hX : tst u P Q Y = hdet (Q.x - P.x) (Q.y - P.y) (Q.z - P.z) (Y.x - P.x) (Y.y - P.y)
      (Y.z - P.z) u.x u.y u.z := rfl
  rw [← hX] at hk
  have : 0 < L * (tst u P Q Y * Z) := by
    have h1 : L * (tst u P Q Y * Z) = (F₁.ev Y * F₂.lin u - F₂.ev Y * F₁.lin u) * (Z * Z) := by
      have := hk; simp only [Fc.lin] at this ⊢; linear_combination Z * this
    rw [h1]; exact mul_pos hS (mul_self_pos.mpr hZne)
  exact pos_of_mul_pos_right this hLpos.le


/-- `tst` is invariant under rotating the triangle. -/
theorem tst_rot (u P Q S : V3) : tst u Q S P = tst u P Q S := by
  simp only [tst, hdet]; ring

theorem eventually_lin_pos (E U : ℝ) (F : Fc) (hE : 0 < E) (ha : 0 < F.a) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < F.lin (vw E U δ) := by
  have := eventually_pos_affine (A := E * F.a) (B := -(U * F.c)) (Or.inl (mul_pos hE ha))
  filter_upwards [this] with δ hδ
  simp only [Fc.lin, vw]; linarith

theorem eventually_lin_neg (E U : ℝ) (F : Fc) (hE : 0 < E) (ha : F.a < 0) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ), F.lin (vw E U δ) < 0 := by
  have := eventually_pos_affine (A := -(E * F.a)) (B := U * F.c)
    (Or.inl (by nlinarith))
  filter_upwards [this] with δ hδ
  simp only [Fc.lin, vw]; linarith

theorem sigma_pos {f₁ f₂ μ₁ μ₂ : ℝ} (h1 : f₁ ≤ 0) (h2 : f₂ ≤ 0) (hμ₁ : 0 ≤ μ₁) (hμ₂ : μ₂ < 0)
    (h : f₁ < 0 ∨ (f₂ < 0 ∧ 0 < μ₁)) : 0 < f₁ * μ₂ - f₂ * μ₁ := by
  rcases h with h | ⟨h, h'⟩
  · nlinarith [mul_pos_of_neg_of_neg h hμ₂, mul_nonneg (neg_nonneg.mpr h2) hμ₁]
  · nlinarith [mul_nonneg_of_nonpos_of_nonpos h1 hμ₂.le, mul_pos (neg_pos.mpr h) h']

/-- The tests of one silhouette edge, for small `δ`: all `Y` in `Ys` have the sign of `λ`. -/
theorem edge_tests (E U : ℝ) (F₁ F₂ : Fc) (P Q Y₁ Y₂ : V3) {k : ℕ} (Ys : Fin k → V3)
    (hPQ : P ≠ Q)
    (hP1 : F₁.ev P = 0) (hQ1 : F₁.ev Q = 0) (hP2 : F₂.ev P = 0) (hQ2 : F₂.ev Q = 0)
    (hY1 : F₂.ev Y₁ = 0) (hY1' : F₁.ev Y₁ < 0) (hY2 : F₁.ev Y₂ = 0) (hY2' : F₂.ev Y₂ < 0)
    (hμ₁ : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 ≤ F₁.lin (vw E U δ))
    (hμ₂ : ∀ᶠ δ in 𝓝[>] (0 : ℝ), F₂.lin (vw E U δ) < 0)
    (hYs : ∀ i, F₁.ev (Ys i) ≤ 0 ∧ F₂.ev (Ys i) ≤ 0 ∧ (F₁.ev (Ys i) < 0 ∨
      (F₂.ev (Ys i) < 0 ∧ ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < F₁.lin (vw E U δ)))) :
    ∃ l : ℝ, ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ i, 0 < l * tst (vw E U δ) P Q (Ys i) := by
  refine ⟨hdet (Q.x - P.x) (Q.y - P.y) (Q.z - P.z) (Y₁.x - P.x) (Y₁.y - P.y)
      (Y₁.z - P.z) (Y₂.x - P.x) (Y₂.y - P.y) (Y₂.z - P.z), ?_⟩
  have hall : ∀ i, ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < F₁.ev (Ys i) * F₂.lin (vw E U δ) -
      F₂.ev (Ys i) * F₁.lin (vw E U δ) := by
    intro i
    obtain ⟨a1, a2, a3⟩ := hYs i
    rcases a3 with a3 | ⟨a3, a4⟩
    · filter_upwards [hμ₁, hμ₂] with δ h1 h2
      exact sigma_pos a1 a2 h1 h2 (Or.inl a3)
    · filter_upwards [hμ₁, hμ₂, a4] with δ h1 h2 h4
      exact sigma_pos a1 a2 h1 h2 (Or.inr ⟨a3, h4⟩)
  filter_upwards [eventually_all.mpr hall] with δ hδ i
  rw [mul_comm]
  exact csl_pos F₁ F₂ P Q Y₁ Y₂ (Ys i) (vw E U δ) hPQ hP1 hQ1 hP2 hQ2 hY1 hY1' hY2 hY2' (hδ i)

theorem ne_of_ev {F : Fc} {P Q : V3} (hP : F.ev P = 0) (hQ : F.ev Q < 0) : P ≠ Q := by
  rintro rfl; linarith

/-- Positive adjacent products give a common sign. -/
theorem chain_pos {k : ℕ} [NeZero k] (l : ZMod k → ℝ) (hadj : ∀ i, 0 < l i * l (i + 1)) :
    ∀ i, 0 < l 0 * l i := by
  have h0 : 0 < l 0 * l 0 := by
    have := hadj 0
    have hne : l 0 ≠ 0 := fun h => by rw [h, zero_mul] at this; exact lt_irrefl _ this
    exact mul_self_pos.mpr hne
  have hn : ∀ n : ℕ, 0 < l 0 * l (n : ZMod k) := by
    intro n
    induction n with
    | zero => simpa using h0
    | succ n ih =>
      have h2 := hadj (n : ZMod k)
      have hne : l (n : ZMod k) ≠ 0 := fun h => by rw [h, mul_zero] at ih; exact lt_irrefl _ ih
      have h3 : 0 < (l 0 * l (n : ZMod k)) * (l (n : ZMod k) * l ((n : ZMod k) + 1)) :=
        mul_pos ih h2
      have h4 : 0 < l (n : ZMod k) * l (n : ZMod k) := mul_self_pos.mpr hne
      have h5 : (l 0 * l (n : ZMod k)) * (l (n : ZMod k) * l ((n : ZMod k) + 1)) =
          (l (n : ZMod k) * l (n : ZMod k)) * (l 0 * l ((n : ZMod k) + 1)) := by ring
      rw [h5] at h3
      push_cast
      exact pos_of_mul_pos_right h3 h4.le
  intro i
  have := hn i.val
  rwa [ZMod.natCast_zmod_val] at this

/-- **Assembling a rim from its edge tests** (two further points `q₁`, `q₂`). -/
theorem rim_assemble {k : ℕ} [NeZero k] (hk : 3 ≤ k) (E U : ℝ) (x : ZMod k → V3) (q₁ q₂ : V3)
    (h : ∀ i : ZMod k, ∃ l : ℝ, ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      (∀ j : ZMod k, j ≠ i → j ≠ i + 1 → 0 < l * tst (vw E U δ) (x i) (x (i + 1)) (x j)) ∧
        0 < l * tst (vw E U δ) (x i) (x (i + 1)) q₁ ∧
        0 < l * tst (vw E U δ) (x i) (x (i + 1)) q₂) :
    ∃ σ : ℝ, ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      (∀ i j : ZMod k, j ≠ i → j ≠ i + 1 → 0 < σ * tst (vw E U δ) (x i) (x (i + 1)) (x j)) ∧
        (∀ i, 0 < σ * tst (vw E U δ) (x i) (x (i + 1)) q₁) ∧
        ∀ i, 0 < σ * tst (vw E U δ) (x i) (x (i + 1)) q₂ := by
  choose l hl using h
  have hall : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ i : ZMod k,
      (∀ j : ZMod k, j ≠ i → j ≠ i + 1 → 0 < l i * tst (vw E U δ) (x i) (x (i + 1)) (x j)) ∧
        0 < l i * tst (vw E U δ) (x i) (x (i + 1)) q₁ ∧
        0 < l i * tst (vw E U δ) (x i) (x (i + 1)) q₂ := eventually_all.mpr hl
  obtain ⟨δ0, hδ0⟩ := hall.exists
  have h2ne : ∀ i : ZMod k, i + 1 + 1 ≠ i := by
    intro i hi
    have : (2 : ZMod k) = 0 := by linear_combination hi
    have h2 : ((2 : ℕ) : ZMod k) = 0 := by exact_mod_cast this
    rw [ZMod.natCast_eq_zero_iff] at h2
    have := Nat.le_of_dvd (by norm_num) h2
    omega
  have h1ne : ∀ i : ZMod k, i + 1 ≠ i := by
    intro i hi
    have : (1 : ZMod k) = 0 := by linear_combination hi
    have h2 : ((1 : ℕ) : ZMod k) = 0 := by exact_mod_cast this
    rw [ZMod.natCast_eq_zero_iff] at h2
    have := Nat.le_of_dvd (by norm_num) h2
    omega
  have hadj : ∀ i, 0 < l i * l (i + 1) := by
    intro i
    obtain ⟨a1, -⟩ := hδ0 i
    obtain ⟨b1, -⟩ := hδ0 (i + 1)
    have t1 := a1 (i + 1 + 1) (h2ne i) (fun h => h1ne (i + 1) h)
    have t2 := b1 i (fun h => h1ne i h.symm) (fun h => h2ne i h.symm)
    rw [tst_rot] at t2
    have := mul_pos t1 t2
    set T := tst (vw E U δ0) (x i) (x (i + 1)) (x (i + 1 + 1))
    by_contra hc; push Not at hc
    nlinarith [mul_self_nonneg T, mul_nonneg_of_nonpos_of_nonpos hc (neg_nonpos.mpr (mul_self_nonneg T))]
  have hch := chain_pos l hadj
  refine ⟨l 0, ?_⟩
  filter_upwards [hall] with δ hδ
  have sg : ∀ (a b T : ℝ), 0 < a * b → 0 < b * T → 0 < a * T := by
    intro a b T h1 h2
    have h3 : 0 < (a * T) * (b * b) := by
      have := mul_pos h1 h2
      have e : (a * T) * (b * b) = (a * b) * (b * T) := by ring
      rw [e]; exact this
    have hb : 0 < b * b := by
      rcases (mul_self_nonneg b).eq_or_lt with h | h
      · rw [← h] at h3; simp at h3
      · exact h
    exact pos_of_mul_pos_left h3 hb.le
  refine ⟨fun i j hi hj => ?_, fun i => ?_, fun i => ?_⟩
  · exact sg _ _ _ (hch i) ((hδ i).1 j hi hj)
  · exact sg _ _ _ (hch i) (hδ i).2.1
  · exact sg _ _ _ (hch i) (hδ i).2.2

/-- The exposure data of `Y` against the pair of faces `F₁` (front), `F₂` (back). -/
def YOk (E U : ℝ) (F₁ F₂ : Fc) (Y : V3) : Prop :=
  F₁.ev Y ≤ 0 ∧ F₂.ev Y ≤ 0 ∧ (F₁.ev Y < 0 ∨
    (F₂.ev Y < 0 ∧ ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < F₁.lin (vw E U δ)))

theorem zmod5_cover (i j : ZMod 5) (h1 : j ≠ i) (h2 : j ≠ i + 1) :
    j = i + 2 ∨ j = i + 3 ∨ j = i + 4 := by
  revert i j; decide

theorem zmod4_cover (i j : ZMod 4) (h1 : j ≠ i) (h2 : j ≠ i + 1) :
    j = i + 2 ∨ j = i + 3 := by
  revert i j; decide

/-- The edge `x i → x (i+1)` of a 5-cycle: all other corners and two more points. -/
theorem edge5 (E U : ℝ) (F₁ F₂ : Fc) (x : ZMod 5 → V3) (q₁ q₂ : V3) (i : ZMod 5) (Y₁ Y₂ : V3)
    (hPQ : x i ≠ x (i + 1))
    (hP1 : F₁.ev (x i) = 0) (hQ1 : F₁.ev (x (i + 1)) = 0) (hP2 : F₂.ev (x i) = 0)
    (hQ2 : F₂.ev (x (i + 1)) = 0)
    (hY1 : F₂.ev Y₁ = 0) (hY1' : F₁.ev Y₁ < 0) (hY2 : F₁.ev Y₂ = 0) (hY2' : F₂.ev Y₂ < 0)
    (hμ₁ : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 ≤ F₁.lin (vw E U δ))
    (hμ₂ : ∀ᶠ δ in 𝓝[>] (0 : ℝ), F₂.lin (vw E U δ) < 0)
    (h2 : YOk E U F₁ F₂ (x (i + 2))) (h3 : YOk E U F₁ F₂ (x (i + 3)))
    (h4 : YOk E U F₁ F₂ (x (i + 4))) (hq₁ : YOk E U F₁ F₂ q₁) (hq₂ : YOk E U F₁ F₂ q₂) :
    ∃ l : ℝ, ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      (∀ j : ZMod 5, j ≠ i → j ≠ i + 1 → 0 < l * tst (vw E U δ) (x i) (x (i + 1)) (x j)) ∧
        0 < l * tst (vw E U δ) (x i) (x (i + 1)) q₁ ∧
        0 < l * tst (vw E U δ) (x i) (x (i + 1)) q₂ := by
  obtain ⟨l, hl⟩ := edge_tests E U F₁ F₂ (x i) (x (i + 1)) Y₁ Y₂
    (![x (i + 2), x (i + 3), x (i + 4), q₁, q₂] : Fin 5 → V3) hPQ hP1 hQ1 hP2 hQ2 hY1 hY1' hY2 hY2'
    hμ₁ hμ₂ (by
      intro k; fin_cases k
      · exact h2
      · exact h3
      · exact h4
      · exact hq₁
      · exact hq₂)
  refine ⟨l, ?_⟩
  filter_upwards [hl] with δ hδ
  refine ⟨fun j hj1 hj2 => ?_, hδ 3, hδ 4⟩
  rcases zmod5_cover i j hj1 hj2 with rfl | rfl | rfl
  · exact hδ 0
  · exact hδ 1
  · exact hδ 2

/-- The edge `x i → x (i+1)` of a 4-cycle. -/
theorem edge4 (E U : ℝ) (F₁ F₂ : Fc) (x : ZMod 4 → V3) (q₁ q₂ : V3) (i : ZMod 4) (Y₁ Y₂ : V3)
    (hPQ : x i ≠ x (i + 1))
    (hP1 : F₁.ev (x i) = 0) (hQ1 : F₁.ev (x (i + 1)) = 0) (hP2 : F₂.ev (x i) = 0)
    (hQ2 : F₂.ev (x (i + 1)) = 0)
    (hY1 : F₂.ev Y₁ = 0) (hY1' : F₁.ev Y₁ < 0) (hY2 : F₁.ev Y₂ = 0) (hY2' : F₂.ev Y₂ < 0)
    (hμ₁ : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 ≤ F₁.lin (vw E U δ))
    (hμ₂ : ∀ᶠ δ in 𝓝[>] (0 : ℝ), F₂.lin (vw E U δ) < 0)
    (h2 : YOk E U F₁ F₂ (x (i + 2))) (h3 : YOk E U F₁ F₂ (x (i + 3)))
    (hq₁ : YOk E U F₁ F₂ q₁) (hq₂ : YOk E U F₁ F₂ q₂) :
    ∃ l : ℝ, ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      (∀ j : ZMod 4, j ≠ i → j ≠ i + 1 → 0 < l * tst (vw E U δ) (x i) (x (i + 1)) (x j)) ∧
        0 < l * tst (vw E U δ) (x i) (x (i + 1)) q₁ ∧
        0 < l * tst (vw E U δ) (x i) (x (i + 1)) q₂ := by
  obtain ⟨l, hl⟩ := edge_tests E U F₁ F₂ (x i) (x (i + 1)) Y₁ Y₂
    (![x (i + 2), x (i + 3), q₁, q₂] : Fin 4 → V3) hPQ hP1 hQ1 hP2 hQ2 hY1 hY1' hY2 hY2'
    hμ₁ hμ₂ (by
      intro k; fin_cases k
      · exact h2
      · exact h3
      · exact hq₁
      · exact hq₂)
  refine ⟨l, ?_⟩
  filter_upwards [hl] with δ hδ
  refine ⟨fun j hj1 hj2 => ?_, hδ 2, hδ 3⟩
  rcases zmod4_cover i j hj1 hj2 with rfl | rfl
  · exact hδ 0
  · exact hδ 1

/-- A cyclic sequence in which every index except `t` has a larger neighbour is unimodal
(given distinct values). -/
theorem isCyclicUnimodal_of_top {k : ℕ} [NeZero k] (hk : 2 ≤ k) {z : ZMod k → ℝ}
    (hinj : Function.Injective z) (t : ZMod k)
    (h : ∀ i, i ≠ t → z i < z (i - 1) ∨ z i < z (i + 1)) : IsCyclicUnimodal z := by
  refine isCyclicUnimodal_of_atMostOne hk hinj fun i j hi hj => ?_
  have hi' : i = t := by
    by_contra hne
    rcases h i hne with h1 | h1 <;> linarith [hi.1, hi.2]
  have hj' : j = t := by
    by_contra hne
    rcases h j hne with h1 | h1 <;> linarith [hj.1, hj.2]
  rw [hi', hj']

theorem injective5 {z : ZMod 5 → ℝ} (h01 : z 0 ≠ z 1) (h02 : z 0 ≠ z 2) (h03 : z 0 ≠ z 3)
    (h04 : z 0 ≠ z 4) (h12 : z 1 ≠ z 2) (h13 : z 1 ≠ z 3) (h14 : z 1 ≠ z 4) (h23 : z 2 ≠ z 3)
    (h24 : z 2 ≠ z 4) (h34 : z 3 ≠ z 4) : Function.Injective z := by
  intro i j hij
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases zmod5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    first
    | rfl
    | exact absurd hij h01 | exact absurd hij h02 | exact absurd hij h03 | exact absurd hij h04
    | exact absurd hij h12 | exact absurd hij h13 | exact absurd hij h14 | exact absurd hij h23
    | exact absurd hij h24 | exact absurd hij h34
    | exact absurd hij.symm h01 | exact absurd hij.symm h02 | exact absurd hij.symm h03
    | exact absurd hij.symm h04 | exact absurd hij.symm h12 | exact absurd hij.symm h13
    | exact absurd hij.symm h14 | exact absurd hij.symm h23 | exact absurd hij.symm h24
    | exact absurd hij.symm h34

theorem injective4 {z : ZMod 4 → ℝ} (h01 : z 0 ≠ z 1) (h02 : z 0 ≠ z 2) (h03 : z 0 ≠ z 3)
    (h12 : z 1 ≠ z 2) (h13 : z 1 ≠ z 3) (h23 : z 2 ≠ z 3) : Function.Injective z := by
  intro i j hij
  have c : ∀ i : ZMod 4, i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by decide
  rcases c i with rfl | rfl | rfl | rfl <;> rcases c j with rfl | rfl | rfl | rfl <;>
    first
    | rfl
    | exact absurd hij h01 | exact absurd hij h02 | exact absurd hij h03
    | exact absurd hij h12 | exact absurd hij h13 | exact absurd hij h23
    | exact absurd hij.symm h01 | exact absurd hij.symm h02 | exact absurd hij.symm h03
    | exact absurd hij.symm h12 | exact absurd hij.symm h13 | exact absurd hij.symm h23

/-- Two depths `p − δ P ≠ q − δ Q` for small `δ > 0`, unless both coordinates tie. -/
theorem eventually_depth_ne {p P q Q : ℝ} (h : ¬ (p = q ∧ P = Q)) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ), p - δ * P ≠ q - δ * Q := by
  by_cases hpq : p = q
  · have hPQ : P ≠ Q := fun e => h ⟨hpq, e⟩
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    intro e
    have : δ * (Q - P) = 0 := by rw [hpq] at e; linarith
    rcases mul_eq_zero.mp this with h0 | h0
    · exact absurd h0 (ne_of_gt hδ)
    · exact hPQ (by linarith)
  · rcases lt_or_gt_of_ne hpq with hlt | hgt
    · filter_upwards [eventually_pos_affine (A := q - p) (B := P - Q) (Or.inl (by linarith))] with δ hδ
      intro e; linarith
    · filter_upwards [eventually_pos_affine (A := p - q) (B := Q - P) (Or.inl (by linarith))] with δ hδ
      intro e; linarith

/-- Unimodality of a 5-cycle with the top at `0` and a monotone chain `0 > 1 > 2 > 4 > 3`. -/
theorem uni5_chain {z : ZMod 5 → ℝ} (h1 : z 1 < z 0) (h2 : z 2 < z 1) (h4 : z 4 < z 2)
    (h3 : z 3 < z 4) : IsCyclicUnimodal z := by
  obtain ⟨a0, a1, a2, a3, a4⟩ := zmod5_add_one
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_sub_one
  refine isCyclicUnimodal_of_top (by norm_num) (injective5 (by linarith) (by linarith)
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    (by linarith) (by linarith)) 0 ?_
  intro i hi
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl
  · exact absurd rfl hi
  · left; rw [b1]; exact h1
  · left; rw [b2]; exact h2
  · right; rw [a3]; linarith
  · right; rw [a4]; linarith

/-- Unimodality of a 5-cycle with the top at `0`, the chain `0 > 1`, and `2 < 3 < 4 < 0`. -/
theorem uni5_valley {z : ZMod 5 → ℝ} (hinj : Function.Injective z) (h1 : z 1 < z 0)
    (h23 : z 2 < z 3) (h34 : z 3 < z 4) (h40 : z 4 < z 0) : IsCyclicUnimodal z := by
  obtain ⟨a0, a1, a2, a3, a4⟩ := zmod5_add_one
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_sub_one
  refine isCyclicUnimodal_of_top (by norm_num) hinj 0 ?_
  intro i hi
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl
  · exact absurd rfl hi
  · left; rw [b1]; exact h1
  · right; rw [a2]; exact h23
  · right; rw [a3]; exact h34
  · right; rw [a4]; exact h40

theorem zmod4_sub_one : (0 : ZMod 4) - 1 = 3 ∧ (1 : ZMod 4) - 1 = 0 ∧ (2 : ZMod 4) - 1 = 1 ∧
    (3 : ZMod 4) - 1 = 2 := by decide

/-- A 4-cycle with the top at `0` and the chain `0 > 1 > 3 > 2`. -/
theorem uni4_down {z : ZMod 4 → ℝ} (h1 : z 1 < z 0) (h3 : z 3 < z 1) (h2 : z 2 < z 3) :
    IsCyclicUnimodal z := by
  obtain ⟨a0, a1, a2, a3⟩ := zmod4_add_one
  obtain ⟨b0, b1, b2, b3⟩ := zmod4_sub_one
  refine isCyclicUnimodal_of_top (by norm_num) (injective4 (by linarith) (by linarith)
    (by linarith) (by linarith) (by linarith) (by linarith)) 0 ?_
  intro i hi
  rcases zmod4_cases i with rfl | rfl | rfl | rfl
  · exact absurd rfl hi
  · left; rw [b1]; exact h1
  · right; rw [a2]; exact h2
  · right; rw [a3]; linarith

/-- A 4-cycle with the top at `3` and the chain `0 < 1 < 2 < 3`. -/
theorem uni4_up {z : ZMod 4 → ℝ} (h1 : z 0 < z 1) (h2 : z 1 < z 2) (h3 : z 2 < z 3) :
    IsCyclicUnimodal z := by
  obtain ⟨a0, a1, a2, a3⟩ := zmod4_add_one
  obtain ⟨b0, b1, b2, b3⟩ := zmod4_sub_one
  refine isCyclicUnimodal_of_top (by norm_num) (injective4 (by linarith) (by linarith)
    (by linarith) (by linarith) (by linarith) (by linarith)) 3 ?_
  intro i hi
  rcases zmod4_cases i with rfl | rfl | rfl | rfl
  · right; rw [a0]; exact h1
  · right; rw [a1]; exact h2
  · right; rw [a2]; exact h3
  · exact absurd rfl hi

/-- The depth of a rim corner at the view `e − δ u₀`, up to a constant. -/
def dep {k : ℕ} (x : ZMod k → V3) (δ : ℝ) (i : ZMod k) : ℝ := (x i).x - δ * (x i).z

/-- The test of a point against a chord `P Q` of the plane `y = 0` (the facet `G` seen edge-on). -/
theorem tst_chord (E U δ : ℝ) (P Q Y : V3) (hP : P.y = 0) (hQ : Q.y = 0) :
    tst (vw E U δ) P Q Y = Y.y * (-(E * (Q.z - P.z)) - δ * (U * (Q.x - P.x))) := by
  simp only [tst, hdet, vw, hP, hQ]; ring

/-- The side `x i → x (i+1)` of a 4-cycle that is a chord of the face `G` (`y = 0`) going down. -/
theorem edge4_chord (E U : ℝ) (x : ZMod 4 → V3) (q₁ q₂ : V3) (i : ZMod 4)
    (hP : (x i).y = 0) (hQ : (x (i + 1)).y = 0) (hdown : (x (i + 1)).z < (x i).z)
    (hE : 0 < E) (hy : ∀ j : ZMod 4, j ≠ i → j ≠ i + 1 → 0 < (x j).y)
    (hq₁ : 0 < q₁.y) (hq₂ : 0 < q₂.y) :
    ∃ l : ℝ, ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      (∀ j : ZMod 4, j ≠ i → j ≠ i + 1 → 0 < l * tst (vw E U δ) (x i) (x (i + 1)) (x j)) ∧
        0 < l * tst (vw E U δ) (x i) (x (i + 1)) q₁ ∧
        0 < l * tst (vw E U δ) (x i) (x (i + 1)) q₂ := by
  refine ⟨1, ?_⟩
  have h := eventually_pos_affine (A := -(E * ((x (i + 1)).z - (x i).z)))
    (B := -(U * ((x (i + 1)).x - (x i).x))) (Or.inl (by nlinarith))
  filter_upwards [h] with δ hδ
  have e : ∀ Y : V3, tst (vw E U δ) (x i) (x (i + 1)) Y = Y.y *
      (-(E * ((x (i + 1)).z - (x i).z)) + δ * -(U * ((x (i + 1)).x - (x i).x))) := by
    intro Y; rw [tst_chord E U δ _ _ Y hP hQ]; ring
  refine ⟨fun j hj1 hj2 => ?_, ?_, ?_⟩
  · rw [one_mul, e]; exact mul_pos (hy j hj1 hj2) hδ
  · rw [one_mul, e]; exact mul_pos hq₁ hδ
  · rw [one_mul, e]; exact mul_pos hq₂ hδ

/-- A 4-cycle in which neither `2` nor `3` is a local maximum is unimodal (`0` and `1` are
adjacent). -/
theorem uni4_B {z : ZMod 4 → ℝ} (hinj : Function.Injective z) (h12 : z 2 < z 1)
    (h3 : z 3 < z 0 ∨ z 3 < z 2) : IsCyclicUnimodal z := by
  obtain ⟨a0, a1, a2, a3⟩ := zmod4_add_one
  obtain ⟨b0, b1, b2, b3⟩ := zmod4_sub_one
  refine isCyclicUnimodal_of_atMostOne (by norm_num) hinj fun i j hi hj => ?_
  have key : ∀ k : ZMod 4, z (k - 1) < z k ∧ z (k + 1) < z k → k = 0 ∨ k = 1 := by
    intro k hk
    rcases zmod4_cases k with rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
    · rw [b2, a2] at hk; linarith [hk.1]
    · rw [b3, a3] at hk; rcases h3 with h | h <;> linarith [hk.1, hk.2]
  rcases key i hi with rfl | rfl <;> rcases key j hj with rfl | rfl
  · rfl
  · rw [b0, a0] at hi; rw [b1, a1] at hj; linarith [hi.2, hj.1]
  · rw [b1, a1] at hi; rw [b0, a0] at hj; linarith [hi.1, hj.2]
  · rfl

end Minimality
end
