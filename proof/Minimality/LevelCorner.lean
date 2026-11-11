module

public import Mathlib
public import Minimality.CornerSlide

@[expose] public section

/-!
# The Level Corner Slide Lemma (normal form and Euclidean form)

Sibling of the Corner Slide Lemma
(`Minimality.Split.Corner.corner_euclid`).

Normal form (as for the CSL): the corner `c = 0`; `J = (0, L, 0)`, `M = (0, 0, H)`; coordinates
`(p₀, p₁, p₂) = (h, x, y)`; every point in the octant `x, y ≥ 0`.

* (T)  every point other than `c, J, M` is deep: `h > 0`;
* (L)  one point `P` has `x = L` and `y > 0` (level with `J`, off the floor wall `y = 0`); every
  point other than `J, P` has `x < L`;
* (W)  one point `W` has `x = 0` and `y > H` (on the wall `x = 0`, beyond `M`); every other point
  with `x = 0` has `y ≤ H`.

View `U s = (1, -s, -s²)` (the CSL's view).  Motion `ω = (s (1 - e), 1, s A)` (a rotation about
`e_j`, plus the small in-plane turn `G = 1 - e` and the small tilt `A`), `τ = (0, s² t₁, s Tm)`.
Screen coordinates `S p = (x + s h, y + s² h)`; the screen velocity of `p` is
`(s (A h + e y) + s² (t₁ - A x),  -h + s ((1 - e) x + Tm) + s² y - s³ A x)`.

Rows (`TiltCert`; every determinant is `s^m q(s)` with `q 0 > 0`):

* `c`: angle `(J, c, M)`;  `J`: angle `(P, J, c)`;  `M`: angle `(c, M, W)`;
* `P`: angle `(c, P, J)` (needs `A h₀ y₀ + h₀² + e y₀² < 0`);
* `W`: angle `(M, W, J)` (needs `h₁² + (y₁ - H)(A h₁ + e y₁) > 0`);
* deep `p` inside the limit triangle (`H x + L y < L H`): the triangle `c J M` (`Corner.row_A`);
* deep `p` beyond it with `0 < x < L`: angle `(c, p, J)` (order `s⁰`: `p` slides straight down);
* deep `p` beyond it with `x = 0`: then `y = H` by (W); the triangle `J W M`.

The window for `(e, A)` is nonempty (`exists_window`), so no slope condition.  No convexity,
no general-position hypothesis.
-/

set_option autoImplicit false
open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality.Split.LevelCorner
open Minimality.Split
open Minimality.Split.Corner (U U_ne row_A)
open Minimality (pt pt_zero pt_one pt_two cross)

/-- `s^m q(s)` with `q` continuous and `q 0 = q₀ > 0` is eventually positive. -/
theorem evp {f : ℝ → ℝ} (m : ℕ) (q : ℝ → ℝ) (q0 : ℝ) (hq : Continuous q) (hq0 : q 0 = q0)
    (h0 : 0 < q0) (hf : ∀ s, f s = s ^ m * q s) : ∀ᶠ s in 𝓝[>] (0:ℝ), 0 < f s := by
  filter_upwards [AcuteEdge.ev_pos hq (hq0 ▸ h0), self_mem_nhdsWithin] with s hs hs0
  rw [hf]; exact mul_pos (pow_pos (Set.mem_Ioi.1 hs0) m) hs

/-- The angular velocity `(s (1 - e), 1, s A)`. -/
noncomputable def Om (e A s : ℝ) : ℝ³ := pt (s * (1 - e)) 1 (s * A)
/-- The translation `s² t₁ e_j + s Tm e_m`. -/
noncomputable def Tau (t1 Tm s : ℝ) : ℝ³ := pt 0 (s ^ 2 * t1) (s * Tm)

syntax "lc_simp" : tactic
macro_rules
  | `(tactic| lc_simp) => `(tactic| simp only [det3, U, Om, Tau, cross_0, cross_1, cross_2,
      PiLp.add_apply, PiLp.sub_apply, pt_zero, pt_one, pt_two])

/-! ### Rows -/

/-- Row of `c`: `y₀ = M`, `y₁ = J`. -/
theorem row_c (L H e A t1 Tm : ℝ) (hL : 0 < L) (hH : 0 < H) (ht1 : 0 < t1) (hTm : 0 < Tm) :
    ∀ᶠ s in 𝓝[>] (0:ℝ), 0 < det3 (pt 0 L 0 - pt 0 0 0) (pt 0 0 H - pt 0 0 0) (U s) ∧
      0 < det3 (pt 0 L 0 - pt 0 0 0) (cross (Om e A s) (pt 0 0 0) + Tau t1 Tm s) (U s) ∧
      0 < det3 (pt 0 0 0 - pt 0 0 H) (cross (Om e A s) (pt 0 0 0) + Tau t1 Tm s) (U s) :=
  (evp 0 (fun _ => L * H) (L * H) (by fun_prop) rfl (by positivity)
    (fun s => by lc_simp; ring)).and <|
  (evp 1 (fun _ => L * Tm) (L * Tm) (by fun_prop) rfl (by positivity)
    (fun s => by lc_simp; ring)).and
  (evp 2 (fun _ => H * t1) (H * t1) (by fun_prop) rfl (by positivity)
    (fun s => by lc_simp; ring))

/-- Row of `J`: `y₀ = c`, `y₁ = P` (`P = (h₀, L, y₀)`). -/
theorem row_J (L e A t1 Tm : ℝ) (p : ℝ³) (hL : 0 < L) (hp1 : p 1 = L) (hp2 : 0 < p 2)
    (hJ1 : 0 < (1 - e) * L + Tm) (hJ2 : 0 < p 0 * ((1 - e) * L + Tm) - p 2 * (t1 - A * L)) :
    ∀ᶠ s in 𝓝[>] (0:ℝ), 0 < det3 (p - pt 0 L 0) (pt 0 0 0 - pt 0 L 0) (U s) ∧
      0 < det3 (p - pt 0 L 0) (cross (Om e A s) (pt 0 L 0) + Tau t1 Tm s) (U s) ∧
      0 < det3 (pt 0 L 0 - pt 0 0 0) (cross (Om e A s) (pt 0 L 0) + Tau t1 Tm s) (U s) :=
  (evp 0 (fun s => L * (p 2 + s ^ 2 * p 0)) (L * p 2) (by fun_prop) (by ring)
    (by positivity) (fun s => by lc_simp; rw [hp1]; ring)).and <|
  (evp 2 (fun s => p 0 * ((1 - e) * L + Tm) - s ^ 2 * p 0 * A * L -
      (p 2 + s ^ 2 * p 0) * (t1 - A * L)) (p 0 * ((1 - e) * L + Tm) - p 2 * (t1 - A * L))
    (by fun_prop) (by ring) hJ2 (fun s => by lc_simp; rw [hp1]; ring)).and
  (evp 1 (fun s => L * ((1 - e) * L + Tm - s ^ 2 * A * L)) (L * ((1 - e) * L + Tm))
    (by fun_prop) (by ring) (by positivity) (fun s => by lc_simp; ring))

/-- Row of `M`: `y₀ = W` (`W = (h₁, 0, y₁)`, `y₁ > H`), `y₁ = c`. -/
theorem row_M (H e A t1 Tm : ℝ) (q : ℝ³) (hH : 0 < H) (he : 0 < e) (hq0 : 0 < q 0)
    (hq1 : q 1 = 0) (hq2 : H < q 2) :
    ∀ᶠ s in 𝓝[>] (0:ℝ), 0 < det3 (pt 0 0 0 - pt 0 0 H) (q - pt 0 0 H) (U s) ∧
      0 < det3 (pt 0 0 0 - pt 0 0 H) (cross (Om e A s) (pt 0 0 H) + Tau t1 Tm s) (U s) ∧
      0 < det3 (pt 0 0 H - q) (cross (Om e A s) (pt 0 0 H) + Tau t1 Tm s) (U s) :=
  (evp 1 (fun _ => H * q 0) (H * q 0) (by fun_prop) rfl (by positivity)
    (fun s => by lc_simp; rw [hq1]; ring)).and <|
  (evp 1 (fun s => H * (e * H + s * t1)) (e * H ^ 2) (by fun_prop) (by ring)
    (by positivity) (fun s => by lc_simp; ring)).and
  (evp 1 (fun s => -q 0 * (s * Tm + s ^ 2 * H) - (H - q 2 - s ^ 2 * q 0) * (e * H + s * t1))
    ((q 2 - H) * (e * H)) (by fun_prop) (by ring)
    (mul_pos (sub_pos.2 hq2) (by positivity)) (fun s => by lc_simp; rw [hq1]; ring))

/-- Row of the level point `P = (h₀, L, y₀)`: `y₀ = J`, `y₁ = c`. -/
theorem row_P (L e A t1 Tm : ℝ) (p : ℝ³) (hL : 0 < L) (hp0 : 0 < p 0) (hp1 : p 1 = L)
    (hp2 : 0 < p 2) (hAP : 0 < -(p 0 ^ 2) - p 2 * (A * p 0 + e * p 2)) :
    ∀ᶠ s in 𝓝[>] (0:ℝ), 0 < det3 (pt 0 0 0 - p) (pt 0 L 0 - p) (U s) ∧
      0 < det3 (pt 0 0 0 - p) (cross (Om e A s) p + Tau t1 Tm s) (U s) ∧
      0 < det3 (p - pt 0 L 0) (cross (Om e A s) p + Tau t1 Tm s) (U s) :=
  (evp 0 (fun s => L * (p 2 + s ^ 2 * p 0)) (L * p 2) (by fun_prop) (by ring)
    (by positivity) (fun s => by lc_simp; rw [hp1]; ring)).and <|
  (evp 0 (fun s => (-L - s * p 0) *
        (-p 0 + s * ((1 - e) * L + Tm) + s ^ 2 * p 2 - s ^ 3 * A * L) +
      (p 2 + s ^ 2 * p 0) * (s * (A * p 0 + e * p 2) + s ^ 2 * (t1 - A * L)))
    (L * p 0) (by fun_prop) (by ring) (by positivity)
    (fun s => by lc_simp; rw [hp1]; ring)).and
  (evp 1 (fun s => p 0 * (-p 0 + s * ((1 - e) * L + Tm) + s ^ 2 * p 2 - s ^ 3 * A * L) -
      (p 2 + s ^ 2 * p 0) * ((A * p 0 + e * p 2) + s * (t1 - A * L)))
    (-(p 0 ^ 2) - p 2 * (A * p 0 + e * p 2)) (by fun_prop) (by ring) hAP
    (fun s => by lc_simp; rw [hp1]; ring))

/-- Row of the wall point `W = (h₁, 0, y₁)`: `y₀ = J`, `y₁ = M`. -/
theorem row_W (L H e A t1 Tm : ℝ) (p : ℝ³) (hL : 0 < L) (hp0 : 0 < p 0) (hp1 : p 1 = 0)
    (hp2 : H < p 2) (hAW : 0 < p 0 ^ 2 - (H - p 2) * (A * p 0 + e * p 2)) :
    ∀ᶠ s in 𝓝[>] (0:ℝ), 0 < det3 (pt 0 0 H - p) (pt 0 L 0 - p) (U s) ∧
      0 < det3 (pt 0 0 H - p) (cross (Om e A s) p + Tau t1 Tm s) (U s) ∧
      0 < det3 (p - pt 0 L 0) (cross (Om e A s) p + Tau t1 Tm s) (U s) :=
  (evp 0 (fun s => (-s * p 0) * (-p 2 - s ^ 2 * p 0) - (H - p 2 - s ^ 2 * p 0) * (L - s * p 0))
    (L * (p 2 - H)) (by fun_prop) (by ring)
    (mul_pos hL (sub_pos.2 hp2)) (fun s => by lc_simp; rw [hp1]; ring)).and <|
  (evp 1 (fun s => -p 0 * (-p 0 + s * Tm + s ^ 2 * p 2) -
      (H - p 2 - s ^ 2 * p 0) * ((A * p 0 + e * p 2) + s * t1))
    (p 0 ^ 2 - (H - p 2) * (A * p 0 + e * p 2)) (by fun_prop) (by ring) hAW
    (fun s => by lc_simp; rw [hp1]; ring)).and
  (evp 0 (fun s => (s * p 0 - L) * (-p 0 + s * Tm + s ^ 2 * p 2) -
      (p 2 + s ^ 2 * p 0) * (s * ((A * p 0 + e * p 2) + s * t1)))
    (L * p 0) (by fun_prop) (by ring) (by positivity)
    (fun s => by lc_simp; rw [hp1]; ring))

/-- Row of a deep point beyond the limit hypotenuse with `0 < x < L`, `y > 0`: `y₀ = J`, `y₁ = c`.
Its velocity is `(0, -h)` at order `s⁰`. -/
theorem row_D (L e A t1 Tm : ℝ) (p : ℝ³) (hL : 0 < L) (hp0 : 0 < p 0) (hp1 : 0 < p 1)
    (hp1L : p 1 < L) (hp2 : 0 < p 2) :
    ∀ᶠ s in 𝓝[>] (0:ℝ), 0 < det3 (pt 0 0 0 - p) (pt 0 L 0 - p) (U s) ∧
      0 < det3 (pt 0 0 0 - p) (cross (Om e A s) p + Tau t1 Tm s) (U s) ∧
      0 < det3 (p - pt 0 L 0) (cross (Om e A s) p + Tau t1 Tm s) (U s) :=
  (evp 0 (fun s => L * (p 2 + s ^ 2 * p 0)) (L * p 2) (by fun_prop) (by ring)
    (by positivity) (fun s => by lc_simp; ring)).and <|
  (evp 0 (fun s => (-p 1 - s * p 0) *
        (-p 0 + s * ((1 - e) * p 1 + Tm) + s ^ 2 * p 2 - s ^ 3 * A * p 1) +
      (p 2 + s ^ 2 * p 0) * (s * (A * p 0 + e * p 2) + s ^ 2 * (t1 - A * p 1)))
    (p 1 * p 0) (by fun_prop) (by ring) (by positivity)
    (fun s => by lc_simp; ring)).and
  (evp 0 (fun s => (p 1 - L + s * p 0) *
        (-p 0 + s * ((1 - e) * p 1 + Tm) + s ^ 2 * p 2 - s ^ 3 * A * p 1) -
      (p 2 + s ^ 2 * p 0) * (s * (A * p 0 + e * p 2) + s ^ 2 * (t1 - A * p 1)))
    ((L - p 1) * p 0) (by fun_prop) (by ring)
    (mul_pos (sub_pos.2 hp1L) hp0) (fun s => by lc_simp; ring))

/-- Row of a deep wall point at height `H` (`p = (h, 0, H)`): the triangle `J W M`. -/
theorem row_T (L H : ℝ) (p q : ℝ³) (hL : 0 < L) (hH : 0 < H) (hp0 : 0 < p 0) (hp1 : p 1 = 0)
    (hp2 : p 2 = H) (hq1 : q 1 = 0) (hq2 : H < q 2) :
    ∀ᶠ s in 𝓝[>] (0:ℝ), 0 < det3 (q - pt 0 L 0) (pt 0 0 H - pt 0 L 0) (U s) ∧
      0 < det3 (q - pt 0 L 0) (p - pt 0 L 0) (U s) ∧
      0 < det3 (pt 0 0 H - q) (p - q) (U s) ∧
      0 < det3 (pt 0 L 0 - pt 0 0 H) (p - pt 0 0 H) (U s) :=
  (evp 0 (fun s => (s * q 0 - L) * H + L * (q 2 + s ^ 2 * q 0)) (L * (q 2 - H)) (by fun_prop)
    (by ring) (mul_pos hL (sub_pos.2 hq2))
    (fun s => by lc_simp; rw [hq1]; ring)).and <|
  (evp 0 (fun s => (s * q 0 - L) * (H + s ^ 2 * p 0) - (q 2 + s ^ 2 * q 0) * (s * p 0 - L))
    (L * (q 2 - H)) (by fun_prop) (by ring) (mul_pos hL (sub_pos.2 hq2))
    (fun s => by lc_simp; rw [hq1, hp1, hp2]; ring)).and <|
  (evp 1 (fun _ => p 0 * (q 2 - H)) (p 0 * (q 2 - H)) (by fun_prop) rfl
    (mul_pos hp0 (sub_pos.2 hq2)) (fun s => by lc_simp; rw [hq1, hp1, hp2]; ring)).and
  (evp 1 (fun s => p 0 * (H + s * L)) (p 0 * H) (by fun_prop) (by ring)
    (by positivity) (fun s => by lc_simp; rw [hp1, hp2]; ring))

/-! ### Assembly -/

/-- The Level Corner Slide Lemma with the motion parameters `e, A, t₁, Tm` given. -/
theorem level_core_param {n : ℕ} (x : Fin n → ℝ³) (c J M P W : Fin n) (L H e A t1 Tm : ℝ)
    (hL : 0 < L) (hH : 0 < H) (hc : x c = pt 0 0 0) (hJ : x J = pt 0 L 0) (hM : x M = pt 0 0 H)
    (hQ : ∀ i, 0 ≤ x i 1 ∧ 0 ≤ x i 2)
    (hD : ∀ i, i ≠ c → i ≠ J → i ≠ M → 0 < x i 0)
    (hP1 : x P 1 = L) (hP2 : 0 < x P 2) (hNj : ∀ i, i ≠ J → i ≠ P → x i 1 < L)
    (hW1 : x W 1 = 0) (hW2 : H < x W 2) (hWu : ∀ i, i ≠ W → x i 1 = 0 → x i 2 ≤ H)
    (he : 0 < e) (ht1 : 0 < t1) (hTm : 0 < Tm)
    (hAP : 0 < -(x P 0 ^ 2) - x P 2 * (A * x P 0 + e * x P 2))
    (hAW : 0 < x W 0 ^ 2 - (H - x W 2) * (A * x W 0 + e * x W 2))
    (hJ1 : 0 < (1 - e) * L + Tm)
    (hJ2 : 0 < x P 0 * ((1 - e) * L + Tm) - x P 2 * (t1 - A * L)) :
    ∀ᶠ s in 𝓝[>] (0:ℝ), FreeAt (univ.image x) (U s) := by
  classical
  have mem : ∀ j, x j ∈ univ.image x := fun j => mem_image_of_mem x (mem_univ j)
  have hPc : P ≠ c := by rintro rfl; rw [hc] at hP1; simp at hP1; linarith
  have hPJ : P ≠ J := by rintro rfl; rw [hJ] at hP2; simp at hP2
  have hPM : P ≠ M := by rintro rfl; rw [hM] at hP1; simp at hP1; linarith
  have hWc : W ≠ c := by rintro rfl; rw [hc] at hW2; simp at hW2; linarith
  have hWJ : W ≠ J := by rintro rfl; rw [hJ] at hW2; simp at hW2; linarith
  have hWM : W ≠ M := by rintro rfl; rw [hM] at hW2; simp at hW2
  have hP0 := hD P hPc hPJ hPM
  have hW0 := hD W hWc hWJ hWM
  have hrow : ∀ i, ∀ᶠ s in 𝓝[>] (0:ℝ),
      TiltCert (univ.image x) (U s) (Om e A s) (Tau t1 Tm s) (x i) := by
    intro i
    by_cases hic : i = c
    · subst hic
      filter_upwards [row_c L H e A t1 Tm hL hH ht1 hTm] with s hs
      exact Or.inl ⟨x M, mem M, x J, mem J, by rw [hc, hJ, hM]; exact hs⟩
    by_cases hiJ : i = J
    · subst hiJ
      filter_upwards [row_J L e A t1 Tm (x P) hL hP1 hP2 hJ1 hJ2] with s hs
      exact Or.inl ⟨x c, mem c, x P, mem P, by rw [hc, hJ]; exact hs⟩
    by_cases hiM : i = M
    · subst hiM
      filter_upwards [row_M H e A t1 Tm (x W) hH he hW0 hW1 hW2] with s hs
      exact Or.inl ⟨x W, mem W, x c, mem c, by rw [hc, hM]; exact hs⟩
    by_cases hiP : i = P
    · subst hiP
      filter_upwards [row_P L e A t1 Tm (x i) hL hP0 hP1 hP2 hAP] with s hs
      exact Or.inl ⟨x J, mem J, x c, mem c, by rw [hc, hJ]; exact hs⟩
    by_cases hiW : i = W
    · subst hiW
      filter_upwards [row_W L H e A t1 Tm (x i) hL hW0 hW1 hW2 hAW] with s hs
      exact Or.inl ⟨x J, mem J, x M, mem M, by rw [hJ, hM]; exact hs⟩
    have h0 := hD i hic hiJ hiM
    have hiL := hNj i hiJ hiP
    rcases lt_or_ge (H * x i 1 + L * x i 2) (L * H) with hA | hB
    · filter_upwards [row_A L H (x i) hL hH h0 (hQ i).1 (hQ i).2 hA] with s hs
      exact Or.inr ⟨x c, mem c, x J, mem J, x M, mem M, by rw [hc, hJ, hM]; exact hs⟩
    rcases (hQ i).1.lt_or_eq with hx | hx
    · have hy : 0 < x i 2 := by nlinarith [mul_pos hH (sub_pos.2 hiL)]
      filter_upwards [row_D L e A t1 Tm (x i) hL h0 hx hiL hy] with s hs
      exact Or.inl ⟨x J, mem J, x c, mem c, by rw [hc, hJ]; exact hs⟩
    · have hy : x i 2 = H := by
        refine le_antisymm (hWu i hiW hx.symm) ?_
        rw [← hx] at hB; nlinarith
      filter_upwards [row_T L H (x i) (x W) hL hH h0 hx.symm hy hW1 hW2] with s hs
      exact Or.inr ⟨x J, mem J, x W, mem W, x M, mem M, by rw [hJ, hM]; exact hs⟩
  filter_upwards [Filter.eventually_all.2 hrow] with s hs
  refine ⟨Om e A s, Tau t1 Tm s, fun y hy => ?_⟩
  obtain ⟨i, -, rfl⟩ := mem_image.1 hy
  exact hs i

/-- The window for the turn `e = 1 - G` and the tilt `A` is nonempty. -/
theorem exists_window (h0 y0 h1 y1 H : ℝ) (hh0 : 0 < h0) (hy0 : 0 < y0) (hh1 : 0 < h1)
    (hH : 0 < H) (hy1 : H < y1) :
    ∃ e A : ℝ, 0 < e ∧ 0 < -(h0 ^ 2) - y0 * (A * h0 + e * y0) ∧
      0 < h1 ^ 2 - (H - y1) * (A * h1 + e * y1) := by
  have hd0 : 0 < y1 - H := sub_pos.2 hy1
  have hZ : 0 < y0 * (y1 - H) := mul_pos hy0 hd0
  -- `X = h₁ y₀ - h₀ d`, `Y = y₁ h₀ - y₀ h₁`; the window is nonempty iff `h₀ h₁ X + e y₀ d Y > 0`.
  obtain ⟨e, he, hkey⟩ : ∃ e : ℝ, 0 < e ∧ 0 < h0 * h1 * (h1 * y0 - h0 * (y1 - H)) +
      e * (y0 * (y1 - H)) * (y1 * h0 - y0 * h1) := by
    rcases lt_or_ge 0 (y1 * h0 - y0 * h1) with hY | hY
    · refine ⟨(|h0 * h1 * (h1 * y0 - h0 * (y1 - H))| + 1) / (y0 * (y1 - H) * (y1 * h0 - y0 * h1)),
        by positivity, ?_⟩
      have : (|h0 * h1 * (h1 * y0 - h0 * (y1 - H))| + 1) / (y0 * (y1 - H) * (y1 * h0 - y0 * h1)) *
          (y0 * (y1 - H)) * (y1 * h0 - y0 * h1) = |h0 * h1 * (h1 * y0 - h0 * (y1 - H))| + 1 := by
        rw [mul_assoc, div_mul_cancel₀ _ (mul_pos hZ hY).ne']
      rw [this]; linarith [neg_abs_le (h0 * h1 * (h1 * y0 - h0 * (y1 - H)))]
    · have hX : 0 < h1 * y0 - h0 * (y1 - H) := by nlinarith [mul_pos hh0 hH]
      have h1Y : 0 < 1 - (y1 * h0 - y0 * h1) := by linarith
      refine ⟨h0 * h1 * (h1 * y0 - h0 * (y1 - H)) / (y0 * (y1 - H) * (1 - (y1 * h0 - y0 * h1))),
        by positivity, ?_⟩
      set e := h0 * h1 * (h1 * y0 - h0 * (y1 - H)) / (y0 * (y1 - H) * (1 - (y1 * h0 - y0 * h1)))
        with he_def
      have he0 : 0 < e := by positivity
      have key : e * (y0 * (y1 - H)) * (1 - (y1 * h0 - y0 * h1)) =
          h0 * h1 * (h1 * y0 - h0 * (y1 - H)) := by
        rw [he_def, mul_assoc, div_mul_cancel₀ _ (mul_pos hZ h1Y).ne']
      nlinarith [mul_pos he0 hZ]
  have ha1 : 0 < h0 * y0 := mul_pos hh0 hy0
  have ha2 : 0 < h1 * (y1 - H) := mul_pos hh1 hd0
  have hlt : -(h1 ^ 2 + e * y1 * (y1 - H)) / (h1 * (y1 - H)) < -(h0 ^ 2 + e * y0 ^ 2) / (h0 * y0) := by
    rw [div_lt_div_iff₀ ha2 ha1]; nlinarith [hkey]
  obtain ⟨A, hA1, hA2⟩ := exists_between hlt
  have hA1' := (div_lt_iff₀ ha2).1 hA1
  have hA2' := (lt_div_iff₀ ha1).1 hA2
  exact ⟨e, A, he, by nlinarith, by nlinarith⟩

/-- **Level Corner Slide Lemma, normal form.**  The corner `c = 0`, `J = (0, L, 0)`,
`M = (0, 0, H)`; every point in the octant (`x₁, x₂ ≥ 0`); (T) every point other than `c, J, M`
has `x₀ > 0`; (L) `P` has `x₁ = L` and `x₂ > 0`, every point other than `J, P` has `x₁ < L`;
(W) `W` has `x₁ = 0` and `x₂ > H`, every other point with `x₁ = 0` has `x₂ ≤ H`.  Then for all
small `s > 0` the view `U s = (1, -s, -s²)` is free. -/
theorem level_core {n : ℕ} (x : Fin n → ℝ³) (c J M P W : Fin n) (L H : ℝ)
    (hL : 0 < L) (hH : 0 < H) (hc : x c = pt 0 0 0) (hJ : x J = pt 0 L 0) (hM : x M = pt 0 0 H)
    (hQ : ∀ i, 0 ≤ x i 1 ∧ 0 ≤ x i 2)
    (hD : ∀ i, i ≠ c → i ≠ J → i ≠ M → 0 < x i 0)
    (hP1 : x P 1 = L) (hP2 : 0 < x P 2) (hNj : ∀ i, i ≠ J → i ≠ P → x i 1 < L)
    (hW1 : x W 1 = 0) (hW2 : H < x W 2) (hWu : ∀ i, i ≠ W → x i 1 = 0 → x i 2 ≤ H) :
    ∀ᶠ s in 𝓝[>] (0:ℝ), FreeAt (univ.image x) (U s) := by
  have hPc : P ≠ c := by rintro rfl; rw [hc] at hP1; simp at hP1; linarith
  have hPJ : P ≠ J := by rintro rfl; rw [hJ] at hP2; simp at hP2
  have hPM : P ≠ M := by rintro rfl; rw [hM] at hP1; simp at hP1; linarith
  have hWc : W ≠ c := by rintro rfl; rw [hc] at hW2; simp at hW2; linarith
  have hWJ : W ≠ J := by rintro rfl; rw [hJ] at hW2; simp at hW2; linarith
  have hWM : W ≠ M := by rintro rfl; rw [hM] at hW2; simp at hW2
  have hP0 := hD P hPc hPJ hPM
  have hW0 := hD W hWc hWJ hWM
  obtain ⟨e, A, he, hAP, hAW⟩ := exists_window (x P 0) (x P 2) (x W 0) (x W 2) H hP0 hP2 hW0 hH hW2
  set Tm := |(1 - e) * L| + x P 2 * |1 - A * L| / x P 0 + 1 with hTm_def
  have hTm : 0 < Tm := by positivity
  have hq : x P 0 * (x P 2 * |1 - A * L| / x P 0) = x P 2 * |1 - A * L| := by field_simp
  have hJ1 : 0 < (1 - e) * L + Tm := by
    have : 0 ≤ x P 2 * |1 - A * L| / x P 0 := by positivity
    linarith [neg_abs_le ((1 - e) * L)]
  have hJ2 : 0 < x P 0 * ((1 - e) * L + Tm) - x P 2 * (1 - A * L) := by
    have h1 : 0 ≤ x P 0 * ((1 - e) * L + |(1 - e) * L|) :=
      mul_nonneg hP0.le (by linarith [neg_abs_le ((1 - e) * L)])
    have h2 : 0 ≤ x P 2 * (|1 - A * L| - (1 - A * L)) :=
      mul_nonneg hP2.le (sub_nonneg.2 (le_abs_self _))
    have : x P 0 * ((1 - e) * L + Tm) - x P 2 * (1 - A * L) =
        x P 0 * ((1 - e) * L + |(1 - e) * L|) + x P 2 * (|1 - A * L| - (1 - A * L)) + x P 0 := by
      rw [hTm_def]; linear_combination hq
    rw [this]; linarith
  exact level_core_param x c J M P W L H e A 1 Tm hL hH hc hJ hM hQ hD hP1 hP2 hNj hW1 hW2 hWu
    he one_pos hTm hAP hAW hJ1 hJ2

theorem level_core_rupert {n : ℕ} (x : Fin n → ℝ³) (c J M P W : Fin n) (L H : ℝ)
    (hL : 0 < L) (hH : 0 < H) (hc : x c = pt 0 0 0) (hJ : x J = pt 0 L 0) (hM : x M = pt 0 0 H)
    (hQ : ∀ i, 0 ≤ x i 1 ∧ 0 ≤ x i 2)
    (hD : ∀ i, i ≠ c → i ≠ J → i ≠ M → 0 < x i 0)
    (hP1 : x P 1 = L) (hP2 : 0 < x P 2) (hNj : ∀ i, i ≠ J → i ≠ P → x i 1 < L)
    (hW1 : x W 1 = 0) (hW2 : H < x W 2) (hWu : ∀ i, i ≠ W → x i 1 = 0 → x i 2 ≤ H) :
    IsRupert (univ.image x) := by
  obtain ⟨s, hs⟩ :=
    (level_core x c J M P W L H hL hH hc hJ hM hQ hD hP1 hP2 hNj hW1 hW2 hWu).exists
  exact FreeAt.isRupert (U_ne s) hs

end Minimality.Split.LevelCorner


/-! ### Euclidean form -/

namespace Minimality.Split.LevelCorner
open Minimality (pt pt_zero pt_one pt_two IsFrame orthoFrameMat orthoFrameMat_apply
  isRupert_of_frame_image)

/-- **Level Corner Slide Lemma, Euclidean form.**  `c, J, M` the corner and two of its edge ends
(`e = x J - x c ⟂ f = x M - x c`, both nonzero), `g ≠ 0` orthogonal to both (normal of the face
`c J M`, pointing into the polytope).  Coordinates `⟪x i - x c, g⟫` (depth), `⟪·, e⟫`, `⟪·, f⟫`:
(hD) every point other than `c, J, M` is deep; (hQ) `⟪·,e⟫, ⟪·,f⟫ ≥ 0`;
(hPe, hPf, hNj) `P` is level with `J` (`⟪x P - x c, e⟫ = ⟪e,e⟫`) and off the wall `⟪·,f⟫ = 0`,
and every point other than `J, P` is short of `J`;
(hWe, hWf, hWu) `W` lies on the wall `⟪·,e⟫ = 0` beyond `M` (`⟪x W - x c, f⟫ > ⟪f,f⟫`), and every
other point on that wall is not beyond `M`. -/
theorem level_corner_euclid {n : ℕ} (x : Fin n → ℝ³) (c J M P W : Fin n) (e f g : ℝ³)
    (he : x J - x c = e) (hf : x M - x c = f)
    (he0 : e ≠ 0) (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hef : ⟪e, f⟫ = 0) (heg : ⟪e, g⟫ = 0) (hfg : ⟪f, g⟫ = 0)
    (hD : ∀ i, i ≠ c → i ≠ J → i ≠ M → 0 < ⟪x i - x c, g⟫)
    (hQ : ∀ i, 0 ≤ ⟪x i - x c, e⟫ ∧ 0 ≤ ⟪x i - x c, f⟫)
    (hPe : ⟪x P - x c, e⟫ = ⟪e, e⟫) (hPf : 0 < ⟪x P - x c, f⟫)
    (hNj : ∀ i, i ≠ J → i ≠ P → ⟪x i - x c, e⟫ < ⟪e, e⟫)
    (hWe : ⟪x W - x c, e⟫ = 0) (hWf : ⟪f, f⟫ < ⟪x W - x c, f⟫)
    (hWu : ∀ i, i ≠ W → ⟪x i - x c, e⟫ = 0 → ⟪x i - x c, f⟫ ≤ ⟪f, f⟫) :
    IsRupert (univ.image x) := by
  classical
  have hL : 0 < ‖e‖ := norm_pos_iff.2 he0
  have hH : 0 < ‖f‖ := norm_pos_iff.2 hf0
  have hG : 0 < ‖g‖ := norm_pos_iff.2 hg0
  have hee : ⟪e, e⟫ = ‖e‖ ^ 2 := real_inner_self_eq_norm_sq e
  have hff : ⟪f, f⟫ = ‖f‖ ^ 2 := real_inner_self_eq_norm_sq f
  have hfe : ⟪f, e⟫ = 0 := by rw [real_inner_comm]; exact hef
  set A : ℝ³ := ‖g‖⁻¹ • g with hA
  set B : ℝ³ := ‖e‖⁻¹ • e with hB
  set C : ℝ³ := ‖f‖⁻¹ • f with hC
  have hFr : IsFrame A B C := by
    refine ⟨AcuteEdge.frame_unit hg0, AcuteEdge.frame_unit he0, AcuteEdge.frame_unit hf0, ?_, ?_, ?_⟩
    · rw [hA, hB, real_inner_smul_left, real_inner_smul_right, real_inner_comm, heg]; ring
    · rw [hA, hC, real_inner_smul_left, real_inner_smul_right, real_inner_comm, hfg]; ring
    · rw [hB, hC, real_inner_smul_left, real_inner_smul_right, hef]; ring
  set d : Fin n → ℝ³ := fun i => pt (‖g‖⁻¹ * ⟪x i - x c, g⟫) (‖e‖⁻¹ * ⟪x i - x c, e⟫)
    (‖f‖⁻¹ * ⟪x i - x c, f⟫) with hd
  have hcR : IsRupert (univ.image d) := by
    refine level_core_rupert d c J M P W ‖e‖ ‖f‖ hL hH ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · simp [hd]
    · simp only [hd, he, hee, heg, hef, mul_zero]
      congr 1; field_simp
    · simp only [hd, hf, hff, hfg, hfe, mul_zero]
      congr 1; field_simp
    · intro i
      simp only [hd, pt_one, pt_two]
      exact ⟨mul_nonneg (inv_nonneg.2 hL.le) (hQ i).1, mul_nonneg (inv_nonneg.2 hH.le) (hQ i).2⟩
    · intro i h1 h2 h3
      simp only [hd, pt_zero]
      exact mul_pos (inv_pos.2 hG) (hD i h1 h2 h3)
    · simp only [hd, pt_one, hPe, hee]
      field_simp
    · simp only [hd, pt_two]
      exact mul_pos (inv_pos.2 hH) hPf
    · intro i hi hi'
      simp only [hd, pt_one]
      have := hNj i hi hi'
      rw [hee] at this
      rw [inv_mul_lt_iff₀ hL]; nlinarith
    · simp only [hd, pt_one, hWe, mul_zero]
    · simp only [hd, pt_two]
      rw [lt_inv_mul_iff₀ hH]; nlinarith
    · intro i hi h0
      simp only [hd, pt_one, pt_two] at h0 ⊢
      have h0' : ⟪x i - x c, e⟫ = 0 := by
        rcases mul_eq_zero.1 h0 with h | h
        · exact absurd h (inv_ne_zero hL.ne')
        · exact h
      have := hWu i hi h0'
      rw [hff] at this
      rw [inv_mul_le_iff₀ hH]; nlinarith
  apply isRupert_of_frame_image (univ.image x) (v := x c) hFr
  rw [Finset.image_image]
  convert hcR using 2
  funext i
  simp only [Function.comp_apply, orthoFrameMat_apply, hd, hA, hB, hC, real_inner_smul_right]

end Minimality.Split.LevelCorner
