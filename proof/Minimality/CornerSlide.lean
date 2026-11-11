module

public import Mathlib
public import Minimality.AcuteEdge

@[expose] public section

/-!
# The Corner Slide Lemma (normal form)


Normal form: the corner `c = 0`; the corner edges along the axes, `J = (0, L, 0)`,
`M = (0, 0, H)` (coordinates `(p_k, p_j, p_m)`; the third corner end `K` on the `x₀` axis is not
used); every point lies in the octant (`x₁ ≥ 0`, `x₂ ≥ 0`, and `x₀ > 0` off `c, J, M`).

* (T)  every point other than `c, J, M` is *deep*: `x₀ > 0` (the face in `x₀ = 0` is `c J M`);
* (Nj) every point other than `J` has `x₁ < L` (nothing at or beyond `J` along `cJ`);
* (Om) some point has `x₂ > H` (something beyond `M` along `cM`).

View `U s = (1, -s, -s²)` (`u = e_k - ψ e_j - ψ² e_m`, `ψ = s`), motion `ω = (0, κ, 1)` (rotation
about an axis in the plane of `cJM`), `τ = (0, s L / 2, 2 s² L)`.  The screen coordinates of the
oblique projection along `U s` are `S p = (p₁ + s p₀, p₂ + s² p₀)`, and
`det3 a b (U s) = S a × S b`.  The slope `κ` is any number with `x₂ < κ (L - x₁)` off `J` and
`H < κ x₁` wherever `x₁ > 0` (`exists_kappa`: always exists).  Rows (`TiltCert`):

* `c`: angle `(J, c, M)`;  `J`: angle `(M, J, c)`;  `M`: angle `(c, M, q)`, `q` a point beyond `M`;
* deep `p` with `H p₁ + L p₂ < L H` (inside the limit triangle): the triangle `c J M`;
* deep `p` with `H p₁ + L p₂ ≥ L H`: the angle `(M, p, J)`; its velocity `p₀ (1, -κ) + O(s)`
  points into it at order `s⁰` (for `p₁ = 0`, `p₂ = H` at order `s¹`).

Every determinant is `g₀ + s^m (g₁ + s g₂(s))` with `g₀ ≥ 0` and `g₁ > 0`, or `s^m (g₁ + s g₂(s))`
with `g₁ > 0`.  No generic-position hypothesis.
-/

set_option autoImplicit false
open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality.Split.Corner
open Minimality.Split
open Minimality (pt pt_zero pt_one pt_two cross)

/-! ### Small-parameter tools -/

/-- `s^m (g₀ + s g₁ s)` with `g₀ > 0` is eventually positive (as `Slide.ev_pos_pow`). -/
theorem ev_pos_pow {f : ℝ → ℝ} (m : ℕ) (g0 : ℝ) (g1 : ℝ → ℝ) (hg : Continuous g1) (h0 : 0 < g0)
    (hfg : ∀ s, f s = s ^ m * (g0 + s * g1 s)) : ∀ᶠ s in 𝓝[>] (0:ℝ), 0 < f s := by
  filter_upwards [AcuteEdge.ev_pos (f := fun s => g0 + s * g1 s) (by fun_prop) (by simpa using h0),
    self_mem_nhdsWithin] with s hs hs0
  rw [hfg]; exact mul_pos (pow_pos (Set.mem_Ioi.1 hs0) m) hs

/-- `c₀ + s^m (g₁ + s g₂ s)` with `c₀ ≥ 0`, `g₁ > 0` is eventually positive. -/
theorem ev_pos_add {f : ℝ → ℝ} (c0 : ℝ) (m : ℕ) (g1 : ℝ) (g2 : ℝ → ℝ) (hg : Continuous g2)
    (hc : 0 ≤ c0) (h1 : 0 < g1) (hfg : ∀ s, f s = c0 + s ^ m * (g1 + s * g2 s)) :
    ∀ᶠ s in 𝓝[>] (0:ℝ), 0 < f s := by
  filter_upwards [ev_pos_pow (f := fun s => s ^ m * (g1 + s * g2 s)) m g1 g2 hg h1 (fun _ => rfl)]
    with s hs
  rw [hfg]; linarith

/-! ### The certificate -/

/-- The view `e_k - s e_j - s² e_m`. -/
noncomputable def U (s : ℝ) : ℝ³ := pt 1 (-s) (-(s ^ 2))
/-- The angular velocity `κ e_j + e_m` (an axis in the plane of `cJM`). -/
noncomputable def Om (κ : ℝ) : ℝ³ := pt 0 κ 1
/-- The translation: screen velocity of `c` is `(s L / 2, 2 s² L)`. -/
noncomputable def Tau (L s : ℝ) : ℝ³ := pt 0 (s * L / 2) (2 * s ^ 2 * L)

theorem U_ne (s : ℝ) : U s ≠ 0 := by
  intro h
  have := congrArg (fun v : ℝ³ => v 0) h
  simp [U] at this

syntax "corner_simp" : tactic
macro_rules
  | `(tactic| corner_simp) => `(tactic| simp only [det3, U, Om, Tau, cross_0, cross_1, cross_2,
      PiLp.add_apply, PiLp.sub_apply, pt_zero, pt_one, pt_two])

/-! ### Rows (TiltCert shape: `y₀`, `y₁` and the point) -/

/-- Row of `c`: `y₀ = M`, `y₁ = J` (quadrant). -/
theorem row_c (L H κ : ℝ) (hL : 0 < L) (hH : 0 < H) :
    ∀ᶠ s in 𝓝[>] (0:ℝ), 0 < det3 (pt 0 L 0 - pt 0 0 0) (pt 0 0 H - pt 0 0 0) (U s) ∧
      0 < det3 (pt 0 L 0 - pt 0 0 0) (cross (Om κ) (pt 0 0 0) + Tau L s) (U s) ∧
      0 < det3 (pt 0 0 0 - pt 0 0 H) (cross (Om κ) (pt 0 0 0) + Tau L s) (U s) :=
  (ev_pos_pow 0 (L * H) (fun _ => 0) (by fun_prop) (by positivity)
    (fun s => by corner_simp; ring)).and <|
  (ev_pos_pow 2 (2 * L ^ 2) (fun _ => 0) (by fun_prop) (by positivity)
    (fun s => by corner_simp; ring)).and
  (ev_pos_pow 1 (L * H / 2) (fun _ => 0) (by fun_prop) (by positivity)
    (fun s => by corner_simp; ring))

/-- Row of `J`: `y₀ = c`, `y₁ = M`. -/
theorem row_J (L H κ : ℝ) (hL : 0 < L) (hH : 0 < H) :
    ∀ᶠ s in 𝓝[>] (0:ℝ), 0 < det3 (pt 0 0 H - pt 0 L 0) (pt 0 0 0 - pt 0 L 0) (U s) ∧
      0 < det3 (pt 0 0 H - pt 0 L 0) (cross (Om κ) (pt 0 L 0) + Tau L s) (U s) ∧
      0 < det3 (pt 0 L 0 - pt 0 0 0) (cross (Om κ) (pt 0 L 0) + Tau L s) (U s) :=
  (ev_pos_pow 0 (L * H) (fun _ => 0) (by fun_prop) (by positivity)
    (fun s => by corner_simp; ring)).and <|
  (ev_pos_pow 1 (L * H / 2) (fun _ => -L ^ 2) (by fun_prop) (by positivity)
    (fun s => by corner_simp; ring)).and
  (ev_pos_pow 2 (L ^ 2) (fun _ => 0) (by fun_prop) (by positivity)
    (fun s => by corner_simp; ring))

/-- Row of `M`: `y₀ = q` (a point beyond `M`, uses (Om)), `y₁ = c`. -/
theorem row_M (L H κ : ℝ) (q : ℝ³) (hL : 0 < L) (hH : 0 < H) (hκ : 0 < κ) (hq0 : 0 < q 0)
    (hq1 : 0 ≤ q 1) (hq2 : H < q 2) :
    ∀ᶠ s in 𝓝[>] (0:ℝ), 0 < det3 (pt 0 0 0 - pt 0 0 H) (q - pt 0 0 H) (U s) ∧
      0 < det3 (pt 0 0 0 - pt 0 0 H) (cross (Om κ) (pt 0 0 H) + Tau L s) (U s) ∧
      0 < det3 (pt 0 0 H - q) (cross (Om κ) (pt 0 0 H) + Tau L s) (U s) :=
  (ev_pos_add (H * q 1) 1 (H * q 0) (fun _ => 0) (by fun_prop) (by positivity) (by positivity)
    (fun s => by corner_simp; ring)).and <|
  (ev_pos_pow 1 (H * (L / 2 + κ * H)) (fun _ => 0) (by fun_prop) (by positivity)
    (fun s => by corner_simp; ring)).and
  (ev_pos_pow 1 ((q 2 - H) * (L / 2 + κ * H))
    (fun s => -(q 1 + s * q 0) * (2 * L + κ * H) + s * q 0 * (L / 2 + κ * H)) (by fun_prop)
    (mul_pos (sub_pos.2 hq2) (by positivity)) (fun s => by corner_simp; ring))

/-- Row of a deep point inside the limit triangle (`H p₁ + L p₂ < L H`): the triangle `c J M`. -/
theorem row_A (L H : ℝ) (p : ℝ³) (hL : 0 < L) (hH : 0 < H) (h0 : 0 < p 0) (h1 : 0 ≤ p 1)
    (h2 : 0 ≤ p 2) (hA : H * p 1 + L * p 2 < L * H) :
    ∀ᶠ s in 𝓝[>] (0:ℝ), 0 < det3 (pt 0 L 0 - pt 0 0 0) (pt 0 0 H - pt 0 0 0) (U s) ∧
      0 < det3 (pt 0 L 0 - pt 0 0 0) (p - pt 0 0 0) (U s) ∧
      0 < det3 (pt 0 0 H - pt 0 L 0) (p - pt 0 L 0) (U s) ∧
      0 < det3 (pt 0 0 0 - pt 0 0 H) (p - pt 0 0 H) (U s) :=
  (ev_pos_pow 0 (L * H) (fun _ => 0) (by fun_prop) (by positivity)
    (fun s => by corner_simp; ring)).and <|
  (ev_pos_add (L * p 2) 2 (L * p 0) (fun _ => 0) (by fun_prop) (by positivity) (by positivity)
    (fun s => by corner_simp; ring)).and <|
  (ev_pos_pow 0 (L * H - H * p 1 - L * p 2) (fun s => -H * p 0 - s * L * p 0) (by fun_prop)
    (by linarith) (fun s => by corner_simp; ring)).and
  (ev_pos_add (H * p 1) 1 (H * p 0) (fun _ => 0) (by fun_prop) (by positivity) (by positivity)
    (fun s => by corner_simp; ring))

/-- The second determinant of the row of a deep point beyond the hypotenuse, `H < κ p₁`
(the case `p₁ > 0`). -/
theorem rowB_mid_pos (L H κ : ℝ) (p : ℝ³) (h0 : 0 < p 0) (h2 : 0 ≤ p 2)
    (hK2 : H < κ * p 1) :
    ∀ᶠ s in 𝓝[>] (0:ℝ), 0 < det3 (pt 0 0 H - p) (cross (Om κ) p + Tau L s) (U s) :=
  ev_pos_pow 0 (p 0 * (κ * p 1 + p 2 - H))
    (fun s => (κ * p 0 ^ 2 - (H - p 2) * (L / 2 + κ * p 2 - p 1)) +
      s * (p 0 ^ 2 - p 1 * (2 * L + κ * p 2 - p 1)) + s ^ 2 * p 0 * (-(3 * L / 2)))
    (by fun_prop) (mul_pos h0 (by linarith)) (fun s => by corner_simp; ring)

/-- The same, `p₁ = 0` (then `p₂ ≥ H`; the order `s⁰` term vanishes at `p₂ = H`). -/
theorem rowB_mid_zero (L H κ : ℝ) (p : ℝ³) (hL : 0 < L) (hκ : 0 < κ) (h0 : 0 < p 0)
    (h1 : p 1 = 0) (h2 : H ≤ p 2) (hH : 0 < H) :
    ∀ᶠ s in 𝓝[>] (0:ℝ), 0 < det3 (pt 0 0 H - p) (cross (Om κ) p + Tau L s) (U s) := by
  have hp2 : 0 < p 2 := lt_of_lt_of_le hH h2
  exact ev_pos_add (p 0 * (p 2 - H)) 1 (κ * p 0 ^ 2 + (p 2 - H) * (L / 2 + κ * p 2))
    (fun s => p 0 ^ 2 + s * p 0 * (-(3 * L / 2))) (by fun_prop)
    (mul_nonneg h0.le (by linarith))
    (by nlinarith [mul_nonneg (sub_nonneg.2 h2) (show 0 ≤ L / 2 + κ * p 2 by positivity),
      mul_pos hκ (mul_pos h0 h0)])
    (fun s => by corner_simp; simp only [h1]; ring)

/-- Row of a deep point beyond the hypotenuse (`H p₁ + L p₂ ≥ L H`): `y₀ = J`, `y₁ = M`. -/
theorem row_B (L H κ : ℝ) (p : ℝ³) (hL : 0 < L) (hH : 0 < H) (hκ : 0 < κ) (h0 : 0 < p 0)
    (h1 : 0 ≤ p 1) (h2 : 0 ≤ p 2) (hB : L * H ≤ H * p 1 + L * p 2)
    (hK1 : p 2 < κ * (L - p 1)) (hK2 : 0 < p 1 → H < κ * p 1) :
    ∀ᶠ s in 𝓝[>] (0:ℝ), 0 < det3 (pt 0 0 H - p) (pt 0 L 0 - p) (U s) ∧
      0 < det3 (pt 0 0 H - p) (cross (Om κ) p + Tau L s) (U s) ∧
      0 < det3 (p - pt 0 L 0) (cross (Om κ) p + Tau L s) (U s) := by
  have hmid : ∀ᶠ s in 𝓝[>] (0:ℝ), 0 < det3 (pt 0 0 H - p) (cross (Om κ) p + Tau L s) (U s) := by
    rcases h1.lt_or_eq with h1 | h1
    · exact rowB_mid_pos L H κ p h0 h2 (hK2 h1)
    · refine rowB_mid_zero L H κ p hL hκ h0 h1.symm ?_ hH
      rw [← h1] at hB; nlinarith
  exact (ev_pos_add (H * p 1 + L * p 2 - L * H) 1 (H * p 0) (fun _ => L * p 0) (by fun_prop)
      (by linarith) (by positivity) (fun s => by corner_simp; ring)).and <| hmid.and
    (ev_pos_pow 0 (p 0 * (κ * (L - p 1) - p 2))
      (fun s => (-(L / 2 + κ * p 2 - p 1) * p 2 - κ * p 0 ^ 2) +
        s * (-p 0 ^ 2 - (2 * L + κ * p 2 - p 1) * (L - p 1)) + s ^ 2 * p 0 * (3 * L / 2))
      (by fun_prop) (mul_pos h0 (by linarith)) (fun s => by corner_simp; ring))

/-! ### Assembly -/

/-- The corner lemma with the slope `κ` given. -/
theorem corner_core_kappa {n : ℕ} (x : Fin n → ℝ³) (c J M : Fin n) (L H κ : ℝ) (hL : 0 < L)
    (hH : 0 < H) (hc : x c = pt 0 0 0) (hJ : x J = pt 0 L 0) (hM : x M = pt 0 0 H)
    (hQ : ∀ i, 0 ≤ x i 1 ∧ 0 ≤ x i 2)
    (hD : ∀ i, i ≠ c → i ≠ J → i ≠ M → 0 < x i 0)
    (hOm : ∃ q, H < x q 2)
    (hκ : 0 < κ) (hK1 : ∀ i, i ≠ J → x i 2 < κ * (L - x i 1))
    (hK2 : ∀ i, 0 < x i 1 → H < κ * x i 1) :
    ∀ᶠ s in 𝓝[>] (0:ℝ), FreeAt (univ.image x) (U s) := by
  classical
  obtain ⟨q, hq2⟩ := hOm
  have hqc : q ≠ c := by rintro rfl; rw [hc] at hq2; simp at hq2; linarith
  have hqJ : q ≠ J := by rintro rfl; rw [hJ] at hq2; simp at hq2; linarith
  have hqM : q ≠ M := by rintro rfl; rw [hM] at hq2; simp at hq2
  have hq0 := hD q hqc hqJ hqM
  have mem : ∀ j, x j ∈ univ.image x := fun j => mem_image_of_mem x (mem_univ j)
  have hrow : ∀ i, ∀ᶠ s in 𝓝[>] (0:ℝ),
      TiltCert (univ.image x) (U s) (Om κ) (Tau L s) (x i) := by
    intro i
    by_cases hic : i = c
    · subst hic
      filter_upwards [row_c L H κ hL hH] with s hs
      left
      refine ⟨x M, mem M, x J, mem J, ?_⟩
      rw [hc, hJ, hM]; exact hs
    by_cases hiJ : i = J
    · subst hiJ
      filter_upwards [row_J L H κ hL hH] with s hs
      left
      refine ⟨x c, mem c, x M, mem M, ?_⟩
      rw [hc, hJ, hM]; exact hs
    by_cases hiM : i = M
    · subst hiM
      filter_upwards [row_M L H κ (x q) hL hH hκ hq0 (hQ q).1 hq2] with s hs
      left
      refine ⟨x q, mem q, x c, mem c, ?_⟩
      rw [hc, hM]; exact hs
    have h0 := hD i hic hiJ hiM
    rcases lt_or_ge (H * x i 1 + L * x i 2) (L * H) with hA | hB
    · filter_upwards [row_A L H (x i) hL hH h0 (hQ i).1 (hQ i).2 hA] with s hs
      right
      refine ⟨x c, mem c, x J, mem J, x M, mem M, ?_⟩
      rw [hc, hJ, hM]; exact hs
    · filter_upwards [row_B L H κ (x i) hL hH hκ h0 (hQ i).1 (hQ i).2 hB (hK1 i hiJ) (hK2 i)]
        with s hs
      left
      refine ⟨x J, mem J, x M, mem M, ?_⟩
      rw [hJ, hM]; exact hs
  filter_upwards [Filter.eventually_all.2 hrow] with s hs
  refine ⟨Om κ, Tau L s, fun y hy => ?_⟩
  obtain ⟨i, -, rfl⟩ := mem_image.1 hy
  exact hs i

/-- A slope `κ` as in `corner_core_kappa` always exists (finitely many points). -/
theorem exists_kappa {n : ℕ} (x : Fin n → ℝ³) (J : Fin n) (L H : ℝ) (hH : 0 < H)
    (hJ1 : x J 1 = L) (hQ : ∀ i, 0 ≤ x i 1 ∧ 0 ≤ x i 2) (hNj : ∀ i, i ≠ J → x i 1 < L) :
    ∃ κ : ℝ, 0 < κ ∧ (∀ i, i ≠ J → x i 2 < κ * (L - x i 1)) ∧
      (∀ i, 0 < x i 1 → H < κ * x i 1) := by
  classical
  set t : Fin n → ℝ := fun i => x i 2 / (L - x i 1) + H / x i 1 with ht
  have hLi : ∀ i, 0 ≤ L - x i 1 := by
    intro i
    by_cases hi : i = J
    · subst hi; rw [hJ1, sub_self]
    · exact (sub_pos.2 (hNj i hi)).le
  have hd1 : ∀ i, 0 ≤ x i 2 / (L - x i 1) := fun i => div_nonneg (hQ i).2 (hLi i)
  have hd2 : ∀ i, 0 ≤ H / x i 1 := fun i => div_nonneg hH.le (hQ i).1
  have ht0 : ∀ i, 0 ≤ t i := fun i => add_nonneg (hd1 i) (hd2 i)
  have hle : ∀ i, t i ≤ ∑ j, t j := fun i =>
    Finset.single_le_sum (fun j _ => ht0 j) (mem_univ i)
  have hsum : 0 ≤ ∑ j, t j := Finset.sum_nonneg fun j _ => ht0 j
  refine ⟨1 + ∑ j, t j, by linarith, fun i hi => ?_, fun i hi => ?_⟩
  · have hp := sub_pos.2 (hNj i hi)
    have : x i 2 / (L - x i 1) < 1 + ∑ j, t j := by
      have := hle i; have := hd2 i; simp only [ht] at *; linarith
    exact (div_lt_iff₀ hp).1 this
  · have : H / x i 1 < 1 + ∑ j, t j := by
      have := hle i; have := hd1 i; simp only [ht] at *; linarith
    exact (div_lt_iff₀ hi).1 this

/-- **Corner Slide Lemma, normal form.**  The corner `c = 0`, `J = (0, L, 0)`, `M = (0, 0, H)`;
every point lies in the octant (`x₁, x₂ ≥ 0`); (T) every point other than `c, J, M` has `x₀ > 0`;
(Nj) every point other than `J` has `x₁ < L`; (Om) some point has `x₂ > H`.  Then for all small
`s > 0` the view `U s = (1, -s, -s²)` is free. -/
theorem corner_core {n : ℕ} (x : Fin n → ℝ³) (c J M : Fin n) (L H : ℝ) (hL : 0 < L)
    (hH : 0 < H) (hc : x c = pt 0 0 0) (hJ : x J = pt 0 L 0) (hM : x M = pt 0 0 H)
    (hQ : ∀ i, 0 ≤ x i 1 ∧ 0 ≤ x i 2)
    (hD : ∀ i, i ≠ c → i ≠ J → i ≠ M → 0 < x i 0)
    (hNj : ∀ i, i ≠ J → x i 1 < L)
    (hOm : ∃ q, H < x q 2) :
    ∀ᶠ s in 𝓝[>] (0:ℝ), FreeAt (univ.image x) (U s) := by
  obtain ⟨κ, hκ, hK1, hK2⟩ :=
    exists_kappa x J L H hH (by rw [hJ]; simp) hQ hNj
  exact corner_core_kappa x c J M L H κ hL hH hc hJ hM hQ hD hOm hκ hK1 hK2

theorem corner_core_rupert {n : ℕ} (x : Fin n → ℝ³) (c J M : Fin n) (L H : ℝ) (hL : 0 < L)
    (hH : 0 < H) (hc : x c = pt 0 0 0) (hJ : x J = pt 0 L 0) (hM : x M = pt 0 0 H)
    (hQ : ∀ i, 0 ≤ x i 1 ∧ 0 ≤ x i 2)
    (hD : ∀ i, i ≠ c → i ≠ J → i ≠ M → 0 < x i 0)
    (hNj : ∀ i, i ≠ J → x i 1 < L)
    (hOm : ∃ q, H < x q 2) :
    IsRupert (univ.image x) := by
  obtain ⟨s, hs⟩ := (corner_core x c J M L H hL hH hc hJ hM hQ hD hNj hOm).exists
  exact FreeAt.isRupert (U_ne s) hs

end Minimality.Split.Corner


/-! ### Euclidean form -/

set_option autoImplicit false
open Finset

namespace Minimality.Split.Corner
open Minimality (pt pt_zero pt_one pt_two IsFrame orthoFrameMat orthoFrameMat_apply
  isRupert_of_frame_image)

/-- **Corner Slide Lemma, Euclidean form.**  `c, J, M` the corner and two of its edge ends
(`e = x J - x c ⟂ f = x M - x c`, both nonzero), `g ≠ 0` orthogonal to both (normal of the
face `c J M`, pointing into the polytope).  Coordinates `⟪x i - x c, g⟫` (depth), `⟪·, e⟫`,
`⟪·, f⟫`: (hD) every point other than `c, J, M` is deep; (hQ) `⟪·,e⟫, ⟪·,f⟫ ≥ 0`;
(hNj) nothing but `J` reaches `⟪·,e⟫ = ⟪e,e⟫`; (hOm) some point has `⟪·,f⟫ > ⟪f,f⟫`. -/
theorem corner_euclid {n : ℕ} (x : Fin n → ℝ³) (c J M : Fin n) (e f g : ℝ³)
    (he : x J - x c = e) (hf : x M - x c = f)
    (he0 : e ≠ 0) (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hef : ⟪e, f⟫ = 0) (heg : ⟪e, g⟫ = 0) (hfg : ⟪f, g⟫ = 0)
    (hD : ∀ i, i ≠ c → i ≠ J → i ≠ M → 0 < ⟪x i - x c, g⟫)
    (hQ : ∀ i, 0 ≤ ⟪x i - x c, e⟫ ∧ 0 ≤ ⟪x i - x c, f⟫)
    (hNj : ∀ i, i ≠ J → ⟪x i - x c, e⟫ < ⟪e, e⟫)
    (hOm : ∃ q, ⟪f, f⟫ < ⟪x q - x c, f⟫) :
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
    obtain ⟨q, hq⟩ := hOm
    refine corner_core_rupert d c J M ‖e‖ ‖f‖ hL hH ?_ ?_ ?_ ?_ ?_ ?_ ⟨q, ?_⟩
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
    · intro i hi
      simp only [hd, pt_one]
      have := hNj i hi
      rw [hee] at this
      rw [inv_mul_lt_iff₀ hL]; nlinarith
    · simp only [hd, pt_two]
      rw [lt_inv_mul_iff₀ hH]; nlinarith
  apply isRupert_of_frame_image (univ.image x) (v := x c) hFr
  rw [Finset.image_image]
  convert hcR using 2
  funext i
  simp only [Function.comp_apply, orthoFrameMat_apply, hd, hA, hB, hC, real_inner_smul_right]

end Minimality.Split.Corner

