module

public import Minimality.AcuteEdge

@[expose] public section

/-!
# The Slide Lemma (normal form)

The analogue of the Acute Edge Lemma (`Minimality.AcuteEdge`) at a right dihedral: there the rotation about
the edge fails, and the first-order motion slides the rectangle `Q` along the edge instead.  Proved for
`σ = +1` and, by the reflection `x₀ ↦ L - x₀`, for `σ = -1`.

Normal form: `a = 0`, `b = (L,0,0)`, `a' = (0,0,-h)`, `b' = (L,0,-h)`; `F ⊂ {z = 0}`,
`Q = F' ⊂ {y = 0}` is the rectangle `a b b' a'`, `H ⊂ {z = -h}`; every point lies in the slab
`-h ≤ z ≤ 0`; every point other than the four corners is *deep* (`y > 0`).

* (Sl₊) every deep point has `x > 0`;
* (R) some deep point lies on `H` (`z = -h`);
* (K₊) some `κ` with `y < κ x` for every deep point of `H` and `κ (x - L) < y` for every deep
  point of `F` beyond `b` (`x > L`).

View `U s = (s, 1, s²)` (`u = w + s t + c s n` with `c = s`), motion
`ω = (κ s², -s², 1)` (`= κ δ t - δ w + n`, `δ = s²`), `τ = (s L / 2, 0, -s⁴)` (`ζ = s⁴`).
Every row is `s^m (g₀ + s g₁(s))` with `g₀ > 0`.
-/

set_option autoImplicit false
open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality.Split.Slide
open Minimality.Split
open Minimality (pt pt_zero pt_one pt_two cross IsFrame orthoFrameMat orthoFrameMat_apply
  isRupert_of_frame_image)

/-- Small-parameter tool: `s^m (g₀ + s g₁ s)` with `g₀ > 0` is eventually positive. -/
theorem ev_pos_pow {f : ℝ → ℝ} (m : ℕ) (g0 : ℝ) (g1 : ℝ → ℝ) (hg : Continuous g1) (h0 : 0 < g0)
    (hfg : ∀ s, f s = s ^ m * (g0 + s * g1 s)) : ∀ᶠ s in 𝓝[>] (0:ℝ), 0 < f s := by
  filter_upwards [AcuteEdge.ev_pos (f := fun s => g0 + s * g1 s) (by fun_prop) (by simpa using h0),
    self_mem_nhdsWithin] with s hs hs0
  rw [hfg]; exact mul_pos (pow_pos (Set.mem_Ioi.1 hs0) m) hs

/-- The view. -/
noncomputable def U (s : ℝ) : ℝ³ := pt s 1 (s ^ 2)
/-- The angular velocity `κ δ t - δ w + n`, `δ = s²`. -/
noncomputable def Om (κ s : ℝ) : ℝ³ := pt (κ * s ^ 2) (-(s ^ 2)) 1
/-- The translation: screen velocity of `a` is `(s L / 2, -s⁴)`. -/
noncomputable def Tau (L s : ℝ) : ℝ³ := pt (s * L / 2) 0 (-(s ^ 4))

theorem U_ne (s : ℝ) : U s ≠ 0 := by
  intro h
  have := congrArg (fun v : ℝ³ => v 1) h
  simp [U] at this

syntax "slide_simp" : tactic
macro_rules
  | `(tactic| slide_simp) => `(tactic| simp only [det3, U, Om, Tau, cross_0, cross_1, cross_2,
      PiLp.add_apply, PiLp.sub_apply, pt_zero, pt_one, pt_two])

/-! ### Rows (TiltCert shape: `y₀`, `y₁` and the point) -/

/-- Row of `a`: `y₀ = a'`, `y₁ = b` (quadrant cone). -/
theorem row_a (L h κ : ℝ) (hL : 0 < L) (hh : 0 < h) :
    ∀ᶠ s in 𝓝[>] (0:ℝ), 0 < det3 (pt L 0 0 - pt 0 0 0) (pt 0 0 (-h) - pt 0 0 0) (U s) ∧
      0 < det3 (pt L 0 0 - pt 0 0 0) (cross (Om κ s) (pt 0 0 0) + Tau L s) (U s) ∧
      0 < det3 (pt 0 0 0 - pt 0 0 (-h)) (cross (Om κ s) (pt 0 0 0) + Tau L s) (U s) :=
  (ev_pos_pow 0 (L * h) (fun _ => 0) (by fun_prop) (by positivity)
    (fun s => by slide_simp; ring)).and <|
  (ev_pos_pow 4 L (fun _ => 0) (by fun_prop) hL (fun s => by slide_simp; ring)).and
  (ev_pos_pow 1 (L * h / 2) (fun _ => 0) (by fun_prop) (by positivity)
    (fun s => by slide_simp; ring))

/-- Row of `b`: `y₀ = a`, `y₁ = b'`. -/
theorem row_b (L h κ : ℝ) (hL : 0 < L) (hh : 0 < h) :
    ∀ᶠ s in 𝓝[>] (0:ℝ), 0 < det3 (pt L 0 (-h) - pt L 0 0) (pt 0 0 0 - pt L 0 0) (U s) ∧
      0 < det3 (pt L 0 (-h) - pt L 0 0) (cross (Om κ s) (pt L 0 0) + Tau L s) (U s) ∧
      0 < det3 (pt L 0 0 - pt 0 0 0) (cross (Om κ s) (pt L 0 0) + Tau L s) (U s) :=
  (ev_pos_pow 0 (L * h) (fun _ => 0) (by fun_prop) (by positivity)
    (fun s => by slide_simp; ring)).and <|
  (ev_pos_pow 1 (L * h / 2) (fun _ => 0) (by fun_prop) (by positivity)
    (fun s => by slide_simp; ring)).and
  (ev_pos_pow 4 L (fun _ => 0) (by fun_prop) hL (fun s => by slide_simp; ring))

/-- Row of `a'`: `y₀ = q` (a deep point of `H`), `y₁ = a`. -/
theorem row_a' (L h κ : ℝ) (q : ℝ³) (hL : 0 < L) (hh : 0 < h) (hqX : 0 < q 0) (hqY : 0 < q 1)
    (hqZ : q 2 = -h) :
    ∀ᶠ s in 𝓝[>] (0:ℝ), 0 < det3 (pt 0 0 0 - pt 0 0 (-h)) (q - pt 0 0 (-h)) (U s) ∧
      0 < det3 (pt 0 0 0 - pt 0 0 (-h)) (cross (Om κ s) (pt 0 0 (-h)) + Tau L s) (U s) ∧
      0 < det3 (pt 0 0 (-h) - q) (cross (Om κ s) (pt 0 0 (-h)) + Tau L s) (U s) :=
  (ev_pos_pow 0 (h * q 0) (fun _ => -h * q 1) (by fun_prop) (by positivity)
    (fun s => by slide_simp; simp only [hqZ]; ring)).and <|
  (ev_pos_pow 1 (L * h / 2) (fun s => h ^ 2 - κ * h ^ 2 * s) (by fun_prop) (by positivity)
    (fun s => by slide_simp; ring)).and
  (ev_pos_pow 3 (L * q 1 / 2) (fun s => -q 0 + h * q 1 - κ * h * q 0 + q 1 * s) (by fun_prop)
    (by positivity) (fun s => by slide_simp; simp only [hqZ]; ring))

/-- Row of `b'`: `y₀ = a'`, `y₁ = q` (a deep point of `H`). -/
theorem row_b' (L h κ : ℝ) (q : ℝ³) (hL : 0 < L) (hh : 0 < h) (hκ : 0 < κ) (hqY : 0 < q 1)
    (hqZ : q 2 = -h) :
    ∀ᶠ s in 𝓝[>] (0:ℝ), 0 < det3 (q - pt L 0 (-h)) (pt 0 0 (-h) - pt L 0 (-h)) (U s) ∧
      0 < det3 (q - pt L 0 (-h)) (cross (Om κ s) (pt L 0 (-h)) + Tau L s) (U s) ∧
      0 < det3 (pt L 0 (-h) - pt 0 0 (-h)) (cross (Om κ s) (pt L 0 (-h)) + Tau L s) (U s) :=
  (ev_pos_pow 2 (L * q 1) (fun _ => 0) (by fun_prop) (by positivity)
    (fun s => by slide_simp; simp only [hqZ]; ring)).and <|
  (ev_pos_pow 3 (L * q 1 / 2)
    (fun s => q 0 - h * q 1 - L + κ * h * q 0 - κ * L * h - q 1 * s) (by fun_prop)
    (by positivity) (fun s => by slide_simp; simp only [hqZ]; ring)).and
  (ev_pos_pow 4 (L + κ * L * h) (fun _ => 0) (by fun_prop) (by positivity)
    (fun s => by slide_simp; ring))

/-- Row of a deep point of `H` (`z = -h`): `y₀ = b`, `y₁ = a'`; uses `y < κ x`. -/
theorem row_H (L h κ : ℝ) (p : ℝ³) (hh : 0 < h) (hX : 0 < p 0) (hY : 0 < p 1)
    (hZ : p 2 = -h) (hK : p 1 < κ * p 0) :
    ∀ᶠ s in 𝓝[>] (0:ℝ), 0 < det3 (pt 0 0 (-h) - p) (pt L 0 0 - p) (U s) ∧
      0 < det3 (pt 0 0 (-h) - p) (cross (Om κ s) p + Tau L s) (U s) ∧
      0 < det3 (p - pt L 0 0) (cross (Om κ s) p + Tau L s) (U s) :=
  (ev_pos_pow 0 (h * p 0) (fun s => -h * p 1 + L * p 1 * s) (by fun_prop) (by positivity)
    (fun s => by slide_simp; simp only [hZ]; ring)).and <|
  (ev_pos_pow 2 (-p 1 ^ 2 + κ * p 0 * p 1)
    (fun s => -p 0 * p 1 + L * p 1 / 2 - κ * p 1 ^ 2 - p 0 * s + h * p 1 * s -
      κ * h * p 0 * s + p 1 * s ^ 2) (by fun_prop)
    (by nlinarith [mul_pos hY (sub_pos.2 hK)]) (fun s => by slide_simp; simp only [hZ]; ring)).and
  (ev_pos_pow 0 (h * p 1)
    (fun s => h * p 0 - L * h / 2 + p 1 ^ 2 * s - h ^ 2 * s - κ * p 0 * p 1 * s +
      κ * L * p 1 * s + p 0 * p 1 * s ^ 2 - L * p 1 * s ^ 2 / 2 + κ * p 1 ^ 2 * s ^ 2 +
      κ * h ^ 2 * s ^ 2 + p 0 * s ^ 3 - h * p 1 * s ^ 3 - L * s ^ 3 + κ * h * p 0 * s ^ 3 -
      κ * L * h * s ^ 3 - p 1 * s ^ 4) (by fun_prop) (by positivity)
    (fun s => by slide_simp; simp only [hZ]; ring))

/-- Row of a deep point strictly between the walls (`-h < z < 0`): `y₀ = a`, `y₁ = a'`. -/
theorem row_mid (L h κ : ℝ) (p : ℝ³) (hh : 0 < h) (hX : 0 < p 0) (hY : 0 < p 1)
    (hZ0 : p 2 < 0) (hZh : -h < p 2) :
    ∀ᶠ s in 𝓝[>] (0:ℝ), 0 < det3 (pt 0 0 (-h) - p) (pt 0 0 0 - p) (U s) ∧
      0 < det3 (pt 0 0 (-h) - p) (cross (Om κ s) p + Tau L s) (U s) ∧
      0 < det3 (p - pt 0 0 0) (cross (Om κ s) p + Tau L s) (U s) :=
  (ev_pos_pow 0 (h * p 0) (fun _ => -h * p 1) (by fun_prop) (by positivity)
    (fun s => by slide_simp; ring)).and <|
  (ev_pos_pow 0 (p 1 * p 2 + h * p 1)
    (fun s => p 0 * p 2 + h * p 0 - L * p 2 / 2 - L * h / 2 + p 2 ^ 2 * s - p 1 ^ 2 * s +
      h * p 2 * s + κ * p 0 * p 1 * s - p 0 * p 1 * s ^ 2 + L * p 1 * s ^ 2 / 2 -
      κ * p 2 ^ 2 * s ^ 2 - κ * p 1 ^ 2 * s ^ 2 - κ * h * p 2 * s ^ 2 - p 1 * p 2 * s ^ 3 -
      p 0 * s ^ 3 + κ * p 0 * p 2 * s ^ 3 + p 1 * s ^ 4) (by fun_prop)
    (by nlinarith [mul_pos hY (show 0 < p 2 + h by linarith)])
    (fun s => by slide_simp; ring)).and
  (ev_pos_pow 0 (-p 1 * p 2)
    (fun s => -p 0 * p 2 + L * p 2 / 2 - p 2 ^ 2 * s + p 1 ^ 2 * s - κ * p 0 * p 1 * s +
      p 0 * p 1 * s ^ 2 - L * p 1 * s ^ 2 / 2 + κ * p 2 ^ 2 * s ^ 2 + κ * p 1 ^ 2 * s ^ 2 +
      p 1 * p 2 * s ^ 3 + p 0 * s ^ 3 - κ * p 0 * p 2 * s ^ 3 - p 1 * s ^ 4) (by fun_prop)
    (by nlinarith [mul_pos hY (neg_pos.2 hZ0)]) (fun s => by slide_simp; ring))

/-- Row of a deep point of `F` beyond `b` (`z = 0`, `x > L`): `y₀ = b`, `y₁ = a'`;
uses `κ (x - L) < y`. -/
theorem row_Fbeyond (L h κ : ℝ) (p : ℝ³) (hh : 0 < h) (hX : L < p 0) (hY : 0 < p 1)
    (hZ : p 2 = 0) (hK : κ * (p 0 - L) < p 1) :
    ∀ᶠ s in 𝓝[>] (0:ℝ), 0 < det3 (pt 0 0 (-h) - p) (pt L 0 0 - p) (U s) ∧
      0 < det3 (pt 0 0 (-h) - p) (cross (Om κ s) p + Tau L s) (U s) ∧
      0 < det3 (p - pt L 0 0) (cross (Om κ s) p + Tau L s) (U s) :=
  (ev_pos_pow 0 (h * p 0 - L * h) (fun s => -h * p 1 + L * p 1 * s) (by fun_prop)
    (by nlinarith) (fun s => by slide_simp; simp only [hZ]; ring)).and <|
  (ev_pos_pow 0 (h * p 1)
    (fun s => h * p 0 - L * h / 2 - p 1 ^ 2 * s + κ * p 0 * p 1 * s - p 0 * p 1 * s ^ 2 +
      L * p 1 * s ^ 2 / 2 - κ * p 1 ^ 2 * s ^ 2 - p 0 * s ^ 3 + p 1 * s ^ 4) (by fun_prop)
    (by positivity) (fun s => by slide_simp; simp only [hZ]; ring)).and
  (ev_pos_pow 2 (p 1 ^ 2 - κ * p 0 * p 1 + κ * L * p 1)
    (fun s => p 0 * p 1 - L * p 1 / 2 + κ * p 1 ^ 2 + p 0 * s - L * s - p 1 * s ^ 2)
    (by fun_prop) (by nlinarith [mul_pos hY (sub_pos.2 hK)])
    (fun s => by slide_simp; simp only [hZ]; ring))

/-- Row of a deep point of `F` over the edge (`z = 0`, `0 < x ≤ L`): inside the projected
triangle `(a, b, a')`. -/
theorem row_Fover (L h : ℝ) (p : ℝ³) (hL : 0 < L) (hh : 0 < h) (hX0 : 0 < p 0) (hXL : p 0 ≤ L)
    (hY : 0 < p 1) (hZ : p 2 = 0) :
    ∀ᶠ s in 𝓝[>] (0:ℝ), 0 < det3 (pt L 0 0 - pt 0 0 0) (pt 0 0 (-h) - pt 0 0 0) (U s) ∧
      0 < det3 (pt L 0 0 - pt 0 0 0) (p - pt 0 0 0) (U s) ∧
      0 < det3 (pt 0 0 (-h) - pt L 0 0) (p - pt L 0 0) (U s) ∧
      0 < det3 (pt 0 0 0 - pt 0 0 (-h)) (p - pt 0 0 (-h)) (U s) := by
  have h3 : ∀ᶠ s in 𝓝[>] (0:ℝ), 0 < det3 (pt 0 0 (-h) - pt L 0 0) (p - pt L 0 0) (U s) := by
    rcases hXL.lt_or_eq with hlt | heq
    · exact ev_pos_pow 0 (-h * p 0 + L * h) (fun s => h * p 1 - L * p 1 * s) (by fun_prop)
        (by nlinarith) (fun s => by slide_simp; simp only [hZ]; ring)
    · exact ev_pos_pow 1 (h * p 1) (fun _ => -L * p 1) (by fun_prop) (by positivity)
        (fun s => by slide_simp; simp only [hZ, heq]; ring)
  exact (ev_pos_pow 0 (L * h) (fun _ => 0) (by fun_prop) (by positivity)
    (fun s => by slide_simp; ring)).and <|
    (ev_pos_pow 2 (L * p 1) (fun _ => 0) (by fun_prop) (by positivity)
      (fun s => by slide_simp; simp only [hZ]; ring)).and <| h3.and
    (ev_pos_pow 0 (h * p 0) (fun _ => -h * p 1) (by fun_prop) (by positivity)
      (fun s => by slide_simp; simp only [hZ]; ring))

/-! ### Assembly -/

/-- **Slide Lemma, normal form (σ = +1).**  `a = 0`, `b = (L,0,0)`, `a' = (0,0,-h)`,
`b' = (L,0,-h)`; every point other than the four corners is deep (`y > 0`); every point lies in
the slab `-h ≤ z ≤ 0` (the planes of `F` and `H` support); (Sl₊) deep points have `x > 0`;
(R) some deep point lies on `H`; (K₊) some `κ` lies strictly above every slope `y / x` of a
deep point of `H` and strictly below every slope `y / (x - L)` of a deep point of `F` beyond `b`.
Then for all small `s > 0` the view `U s = (s, 1, s²)` is free. -/
theorem slide_core {n : ℕ} (x : Fin n → ℝ³) (a b a' b' : Fin n) (L h : ℝ) (hL : 0 < L)
    (hh : 0 < h) (ha : x a = pt 0 0 0) (hb : x b = pt L 0 0) (ha' : x a' = pt 0 0 (-h))
    (hb' : x b' = pt L 0 (-h))
    (hD : ∀ i, i ≠ a → i ≠ b → i ≠ a' → i ≠ b' → 0 < x i 1)
    (hZ : ∀ i, -h ≤ x i 2 ∧ x i 2 ≤ 0)
    (hSl : ∀ i, 0 < x i 1 → 0 < x i 0)
    (hR : ∃ q, 0 < x q 1 ∧ x q 2 = -h)
    (hK : ∃ κ : ℝ, (∀ i, 0 < x i 1 → x i 2 = -h → x i 1 < κ * x i 0) ∧
      (∀ i, 0 < x i 1 → x i 2 = 0 → L < x i 0 → κ * (x i 0 - L) < x i 1)) :
    ∀ᶠ s in 𝓝[>] (0:ℝ), FreeAt (univ.image x) (U s) := by
  classical
  obtain ⟨q, hqY, hqZ⟩ := hR
  obtain ⟨κ, hKH, hKF⟩ := hK
  have hqX := hSl q hqY
  have hκ : 0 < κ := by
    have := hKH q hqY hqZ
    by_contra hc
    nlinarith [le_of_not_gt hc]
  have mem : ∀ j, x j ∈ univ.image x := fun j => mem_image_of_mem x (mem_univ j)
  have hrow : ∀ i, ∀ᶠ s in 𝓝[>] (0:ℝ),
      TiltCert (univ.image x) (U s) (Om κ s) (Tau L s) (x i) := by
    intro i
    by_cases hia : i = a
    · subst hia
      filter_upwards [row_a L h κ hL hh] with s hs
      left
      refine ⟨x a', mem a', x b, mem b, ?_⟩
      rw [ha, ha', hb]; exact hs
    by_cases hib : i = b
    · subst hib
      filter_upwards [row_b L h κ hL hh] with s hs
      left
      refine ⟨x a, mem a, x b', mem b', ?_⟩
      rw [ha, hb, hb']; exact hs
    by_cases hia' : i = a'
    · subst hia'
      filter_upwards [row_a' L h κ (x q) hL hh hqX hqY hqZ] with s hs
      left
      refine ⟨x q, mem q, x a, mem a, ?_⟩
      rw [ha, ha']; exact hs
    by_cases hib' : i = b'
    · subst hib'
      filter_upwards [row_b' L h κ (x q) hL hh hκ hqY hqZ] with s hs
      left
      refine ⟨x a', mem a', x q, mem q, ?_⟩
      rw [ha', hb']; exact hs
    have hY := hD i hia hib hia' hib'
    have hX := hSl i hY
    rcases (hZ i).2.lt_or_eq with hz0 | hz0
    · rcases (hZ i).1.lt_or_eq with hzh | hzh
      · filter_upwards [row_mid L h κ (x i) hh hX hY hz0 hzh] with s hs
        left
        refine ⟨x a, mem a, x a', mem a', ?_⟩
        rw [ha, ha']; exact hs
      · filter_upwards [row_H L h κ (x i) hh hX hY hzh.symm (hKH i hY hzh.symm)] with s hs
        left
        refine ⟨x b, mem b, x a', mem a', ?_⟩
        rw [hb, ha']; exact hs
    · by_cases hxL : x i 0 ≤ L
      · filter_upwards [row_Fover L h (x i) hL hh hX hxL hY hz0] with s hs
        right
        refine ⟨x a, mem a, x b, mem b, x a', mem a', ?_⟩
        rw [ha, hb, ha']; exact hs
      · replace hxL := lt_of_not_ge hxL
        filter_upwards [row_Fbeyond L h κ (x i) hh hxL hY hz0 (hKF i hY hz0 hxL)] with s hs
        left
        refine ⟨x b, mem b, x a', mem a', ?_⟩
        rw [hb, ha']; exact hs
  filter_upwards [Filter.eventually_all.2 hrow] with s hs
  refine ⟨Om κ s, Tau L s, fun y hy => ?_⟩
  obtain ⟨i, -, rfl⟩ := mem_image.1 hy
  exact hs i

theorem slide_core_rupert {n : ℕ} (x : Fin n → ℝ³) (a b a' b' : Fin n) (L h : ℝ) (hL : 0 < L)
    (hh : 0 < h) (ha : x a = pt 0 0 0) (hb : x b = pt L 0 0) (ha' : x a' = pt 0 0 (-h))
    (hb' : x b' = pt L 0 (-h))
    (hD : ∀ i, i ≠ a → i ≠ b → i ≠ a' → i ≠ b' → 0 < x i 1)
    (hZ : ∀ i, -h ≤ x i 2 ∧ x i 2 ≤ 0)
    (hSl : ∀ i, 0 < x i 1 → 0 < x i 0)
    (hR : ∃ q, 0 < x q 1 ∧ x q 2 = -h)
    (hK : ∃ κ : ℝ, (∀ i, 0 < x i 1 → x i 2 = -h → x i 1 < κ * x i 0) ∧
      (∀ i, 0 < x i 1 → x i 2 = 0 → L < x i 0 → κ * (x i 0 - L) < x i 1)) :
    IsRupert (univ.image x) := by
  obtain ⟨s, hs⟩ := (slide_core x a b a' b' L h hL hh ha hb ha' hb' hD hZ hSl hR hK).exists
  exact FreeAt.isRupert (U_ne s) hs


/-! ### The mirror σ = -1 -/

/-- **Slide Lemma, normal form (σ = -1).**  As `slide_core_rupert` with (Sl₋) deep points have
`x < L` and (K₋) some `κ` with `y < κ (L - x)` for every deep point of `H` and `κ (-x) < y` for
every deep point of `F` beyond `a` (`x < 0`).  Reduction: the reflection `x ↦ L - x`. -/
theorem slide_core_rupert_neg {n : ℕ} (x : Fin n → ℝ³) (a b a' b' : Fin n) (L h : ℝ)
    (hL : 0 < L) (hh : 0 < h) (ha : x a = pt 0 0 0) (hb : x b = pt L 0 0)
    (ha' : x a' = pt 0 0 (-h)) (hb' : x b' = pt L 0 (-h))
    (hD : ∀ i, i ≠ a → i ≠ b → i ≠ a' → i ≠ b' → 0 < x i 1)
    (hZ : ∀ i, -h ≤ x i 2 ∧ x i 2 ≤ 0)
    (hSl : ∀ i, 0 < x i 1 → x i 0 < L)
    (hR : ∃ q, 0 < x q 1 ∧ x q 2 = -h)
    (hK : ∃ κ : ℝ, (∀ i, 0 < x i 1 → x i 2 = -h → x i 1 < κ * (L - x i 0)) ∧
      (∀ i, 0 < x i 1 → x i 2 = 0 → x i 0 < 0 → κ * (-x i 0) < x i 1)) :
    IsRupert (univ.image x) := by
  classical
  set c : Fin n → ℝ³ := fun i => pt (L - x i 0) (x i 1) (x i 2) with hc
  have hcR : IsRupert (univ.image c) := by
    obtain ⟨κ, hKH, hKF⟩ := hK
    refine slide_core_rupert c b a b' a' L h hL hh ?_ ?_ ?_ ?_ (fun i h1 h2 h3 h4 =>
      hD i h2 h1 h4 h3) (fun i => hZ i)
      (fun i hi => by simp only [hc, pt_zero]; linarith [hSl i hi])
      hR ⟨κ, fun i h1 h2 => ?_, fun i h1 h2 h3 => ?_⟩
    · simp only [hc, hb, pt_zero, pt_one, pt_two]; ext j; fin_cases j <;> simp
    · simp only [hc, ha, pt_zero, pt_one, pt_two]; ext j; fin_cases j <;> simp
    · simp only [hc, hb', pt_zero, pt_one, pt_two]; ext j; fin_cases j <;> simp
    · simp only [hc, ha', pt_zero, pt_one, pt_two]; ext j; fin_cases j <;> simp
    · simp only [hc, pt_zero, pt_one, pt_two] at h1 h2 ⊢; exact hKH i h1 h2
    · simp only [hc, pt_zero, pt_one, pt_two] at h1 h2 h3 ⊢
      have := hKF i h1 h2 (by linarith); linarith
  have hFr : IsFrame (pt (-1) 0 0) (pt 0 1 0) (pt 0 0 1) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [inner3, pt_zero, pt_one, pt_two] <;> norm_num
  apply isRupert_of_frame_image (univ.image x) (v := pt L 0 0) hFr
  rw [Finset.image_image]
  convert hcR using 2
  funext i
  simp only [Function.comp_apply, orthoFrameMat_apply, hc, inner3, PiLp.sub_apply, pt_zero,
    pt_one, pt_two]
  congr 1 <;> ring

end Minimality.Split.Slide

#print axioms Minimality.Split.Slide.slide_core_rupert
#print axioms Minimality.Split.Slide.slide_core_rupert_neg
