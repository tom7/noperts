module

public import Minimality.AcuteEdge

@[expose] public section

/-!
# The Slide Lemma (normal form)

The analogue of the Acute Edge Lemma (`Minimality.AcuteEdge`) at a right dihedral: there the rotation about
the edge fails, and the first-order motion slides the rectangle `Q` along the edge instead.  Proved for
`σ = +1`; the case `σ = -1` is the reflection `x₀ ↦ L - x₀` (the Slide Lemma callers use the mirrored corner labels).

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

Further down: `slide_tab` / `slide_euclid` (the same in any Euclidean position, with coordinate
tables), `kdich` (the (K) dichotomy between the two walls) and `slide_walls` (rectangle between two
parallel walls, one deep point per wall, slab at one end: Rupert with no slope hypothesis).
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


/-- **Slide Lemma (σ = +1), Euclidean form with coordinate tables.**  `a, b, a', b'` the corners
of the rectangle `Q` (`e = x b - x a ⟂ g = x a' - x a`, `x b' - x a = e + g`), `nQ ≠ 0` a normal
of `Q`.  With `X i = ⟪x i - x a, e⟫`, `Y i = ⟪x i - x a, nQ⟫`, `G i = ⟪x i - x a, g⟫`:
(hD) every point other than the corners is deep (`Y > 0`); (hZ) `0 ≤ G ≤ ⟪g, g⟫` (the planes of
`F ∋ a, b` and `H ∋ a', b'`, both orthogonal to `g`, support); (Sl₊) deep points have `X > 0`;
(R) a deep point lies on `H`; (K₊) some `κ` with `Y < κ X` on the deep points of `H` and
`κ (X - ⟪e, e⟫) < Y` on the deep points of `F` beyond `b`. -/
theorem slide_tab {n : ℕ} (x : Fin n → ℝ³) (a b a' b' : Fin n) (e g nQ : ℝ³)
    (X Y G : Fin n → ℝ)
    (hX : ∀ i, ⟪x i - x a, e⟫ = X i) (hY : ∀ i, ⟪x i - x a, nQ⟫ = Y i)
    (hG : ∀ i, ⟪x i - x a, g⟫ = G i)
    (he : x b - x a = e) (hg : x a' - x a = g) (hb' : x b' - x a = e + g)
    (he0 : e ≠ 0) (hg0 : g ≠ 0) (hn0 : nQ ≠ 0)
    (heg : ⟪e, g⟫ = 0) (hen : ⟪e, nQ⟫ = 0) (hgn : ⟪g, nQ⟫ = 0)
    (hD : ∀ i, i ≠ a → i ≠ b → i ≠ a' → i ≠ b' → 0 < Y i)
    (hZ : ∀ i, 0 ≤ G i ∧ G i ≤ ⟪g, g⟫)
    (hSl : ∀ i, 0 < Y i → 0 < X i)
    (hR : ∃ q, 0 < Y q ∧ G q = ⟪g, g⟫)
    (hK : ∃ κ : ℝ, (∀ i, 0 < Y i → G i = ⟪g, g⟫ → Y i < κ * X i) ∧
      (∀ i, 0 < Y i → G i = 0 → ⟪e, e⟫ < X i → κ * (X i - ⟪e, e⟫) < Y i)) :
    IsRupert (univ.image x) := by
  classical
  have hL : 0 < ‖e‖ := norm_pos_iff.2 he0
  have hh : 0 < ‖g‖ := norm_pos_iff.2 hg0
  have hn : 0 < ‖nQ‖ := norm_pos_iff.2 hn0
  have hee : ⟪e, e⟫ = ‖e‖ ^ 2 := real_inner_self_eq_norm_sq e
  have hgg : ⟪g, g⟫ = ‖g‖ ^ 2 := real_inner_self_eq_norm_sq g
  have hLn : ‖e‖ ≠ 0 := hL.ne'
  have hhn : ‖g‖ ≠ 0 := hh.ne'
  have hnn : ‖nQ‖ ≠ 0 := hn.ne'
  set S : ℝ³ := ‖e‖⁻¹ • e with hS
  set T : ℝ³ := ‖nQ‖⁻¹ • nQ with hT
  set Nn : ℝ³ := ‖-g‖⁻¹ • (-g) with hN
  have hFr : IsFrame S T Nn := by
    refine ⟨AcuteEdge.frame_unit he0, AcuteEdge.frame_unit hn0,
      AcuteEdge.frame_unit (neg_ne_zero.2 hg0), ?_, ?_, ?_⟩
    · rw [hS, hT, real_inner_smul_left, real_inner_smul_right, hen]; ring
    · rw [hS, hN, real_inner_smul_left, real_inner_smul_right, inner_neg_right, heg]; ring
    · rw [hT, hN, real_inner_smul_left, real_inner_smul_right, inner_neg_right,
        real_inner_comm, hgn]; ring
  set c : Fin n → ℝ³ := fun i => pt (‖e‖⁻¹ * X i) (‖nQ‖⁻¹ * Y i) (-(‖g‖⁻¹ * G i)) with hc
  have hXa : X a = 0 := by rw [← hX a, sub_self, inner_zero_left]
  have hYa : Y a = 0 := by rw [← hY a, sub_self, inner_zero_left]
  have hGa : G a = 0 := by rw [← hG a, sub_self, inner_zero_left]
  have hcR : IsRupert (univ.image c) := by
    obtain ⟨q, hqY, hqG⟩ := hR
    obtain ⟨κ, hKH, hKF⟩ := hK
    refine slide_core_rupert c a b a' b' ‖e‖ ‖g‖ hL hh ?_ ?_ ?_ ?_ ?_ ?_ ?_ ⟨q, ?_, ?_⟩
      ⟨κ * ‖e‖ / ‖nQ‖, ?_, ?_⟩
    · simp only [hc, hXa, hYa, hGa, mul_zero, neg_zero]
    · simp only [hc, ← hX, ← hY, ← hG, he, hen, heg, hee, mul_zero, neg_zero]
      congr 1; field_simp
    · simp only [hc, ← hX, ← hY, ← hG, hg, real_inner_comm e g, heg, hgn, hgg, mul_zero]
      congr 1; field_simp
    · simp only [hc, ← hX, ← hY, ← hG, hb', inner_add_left, hen, hgn, heg,
        real_inner_comm e g, hee, hgg, add_zero, zero_add, mul_zero]
      congr 1 <;> field_simp
    · intro i h1 h2 h3 h4
      simp only [hc, pt_one]
      exact mul_pos (inv_pos.2 hn) (hD i h1 h2 h3 h4)
    · intro i
      simp only [hc, pt_two]
      obtain ⟨h1, h2⟩ := hZ i
      rw [hgg] at h2
      constructor
      · have : ‖g‖⁻¹ * G i ≤ ‖g‖ := by
          rw [inv_mul_le_iff₀ hh]; nlinarith
        linarith
      · have : 0 ≤ ‖g‖⁻¹ * G i := mul_nonneg (inv_nonneg.2 hh.le) h1
        linarith
    · intro i hi
      simp only [hc, pt_zero, pt_one] at hi ⊢
      have hYi : 0 < Y i := (mul_pos_iff_of_pos_left (inv_pos.2 hn)).1 hi
      exact mul_pos (inv_pos.2 hL) (hSl i hYi)
    · simp only [hc, pt_one]; exact mul_pos (inv_pos.2 hn) hqY
    · simp only [hc, pt_two, hqG, hgg]; field_simp
    · intro i h1 h2
      simp only [hc, pt_zero, pt_one, pt_two] at h1 h2 ⊢
      have hYi : 0 < Y i := (mul_pos_iff_of_pos_left (inv_pos.2 hn)).1 h1
      have hGi : G i = ⟪g, g⟫ := by
        rw [hgg]; field_simp at h2; linarith
      have hk := hKH i hYi hGi
      have : κ * ‖e‖ / ‖nQ‖ * (‖e‖⁻¹ * X i) = ‖nQ‖⁻¹ * (κ * X i) := by field_simp
      rw [this]; exact mul_lt_mul_of_pos_left hk (inv_pos.2 hn)
    · intro i h1 h2 h3
      simp only [hc, pt_zero, pt_one, pt_two] at h1 h2 h3 ⊢
      have hYi : 0 < Y i := (mul_pos_iff_of_pos_left (inv_pos.2 hn)).1 h1
      have hGi : G i = 0 := by
        have : ‖g‖⁻¹ * G i = 0 := by linarith
        rcases mul_eq_zero.1 this with h | h
        · exact absurd h (inv_ne_zero hhn)
        · exact h
      have hXi : ⟪e, e⟫ < X i := by
        rw [hee]; rw [lt_inv_mul_iff₀ hL] at h3; nlinarith
      have hk := hKF i hYi hGi hXi
      have : κ * ‖e‖ / ‖nQ‖ * (‖e‖⁻¹ * X i - ‖e‖) = ‖nQ‖⁻¹ * (κ * (X i - ⟪e, e⟫)) := by
        rw [hee]; field_simp
      rw [this]; exact mul_lt_mul_of_pos_left hk (inv_pos.2 hn)
  apply isRupert_of_frame_image (univ.image x) (v := x a) hFr
  rw [Finset.image_image]
  convert hcR using 2
  funext i
  simp only [Function.comp_apply, orthoFrameMat_apply, hc, hS, hT, hN, real_inner_smul_right,
    inner_neg_right, norm_neg, hX, hY, hG]
  congr 1; ring

/-- **Slide Lemma (σ = +1), Euclidean form.**  `slide_tab` with the coordinates spelled out. -/
theorem slide_euclid {n : ℕ} (x : Fin n → ℝ³) (a b a' b' : Fin n) (e g nQ : ℝ³)
    (he : x b - x a = e) (hg : x a' - x a = g) (hb' : x b' - x a = e + g)
    (he0 : e ≠ 0) (hg0 : g ≠ 0) (hn0 : nQ ≠ 0)
    (heg : ⟪e, g⟫ = 0) (hen : ⟪e, nQ⟫ = 0) (hgn : ⟪g, nQ⟫ = 0)
    (hD : ∀ i, i ≠ a → i ≠ b → i ≠ a' → i ≠ b' → 0 < ⟪x i - x a, nQ⟫)
    (hZ : ∀ i, 0 ≤ ⟪x i - x a, g⟫ ∧ ⟪x i - x a, g⟫ ≤ ⟪g, g⟫)
    (hSl : ∀ i, 0 < ⟪x i - x a, nQ⟫ → 0 < ⟪x i - x a, e⟫)
    (hR : ∃ q, 0 < ⟪x q - x a, nQ⟫ ∧ ⟪x q - x a, g⟫ = ⟪g, g⟫)
    (hK : ∃ κ : ℝ, (∀ i, 0 < ⟪x i - x a, nQ⟫ → ⟪x i - x a, g⟫ = ⟪g, g⟫ →
        ⟪x i - x a, nQ⟫ < κ * ⟪x i - x a, e⟫) ∧
      (∀ i, 0 < ⟪x i - x a, nQ⟫ → ⟪x i - x a, g⟫ = 0 → ⟪e, e⟫ < ⟪x i - x a, e⟫ →
        κ * (⟪x i - x a, e⟫ - ⟪e, e⟫) < ⟪x i - x a, nQ⟫)) :
    IsRupert (univ.image x) :=
  slide_tab x a b a' b' e g nQ _ _ _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) he hg hb' he0
    hg0 hn0 heg hen hgn hD hZ hSl hR hK

/-- **The (K) dichotomy**.  Two walls share the slab `X > 0` (lengths along the
edge, `ℓ` the edge length squared in the units of `X`) and the depth `Y > 0`; the deep point of `H`
is `3` at wall `B` and `0` at wall `H`, and conversely on `F`.  Then (K₊) holds at one of the two
walls.  If it failed at both, `Y₃ (X₀ - ℓ) ≥ Y₀ X₃ > Y₀ (X₃ - ℓ) ≥ Y₃ X₀ > Y₃ (X₀ - ℓ)`. -/
theorem kdich {ℓ X0 X3 Y0 Y3 : ℝ} (hℓ : 0 < ℓ) (hX0 : 0 < X0) (hX3 : 0 < X3) (hY0 : 0 < Y0)
    (hY3 : 0 < Y3) :
    (∃ κ : ℝ, Y3 < κ * X3 ∧ (ℓ < X0 → κ * (X0 - ℓ) < Y0)) ∨
      (∃ κ : ℝ, Y0 < κ * X0 ∧ (ℓ < X3 → κ * (X3 - ℓ) < Y3)) := by
  by_cases h0 : X0 ≤ ℓ
  · left
    refine ⟨(Y3 + 1) / X3, ?_, fun h => absurd h (not_lt.2 h0)⟩
    rw [div_mul_cancel₀ _ hX3.ne']; linarith
  by_cases h3 : X3 ≤ ℓ
  · right
    refine ⟨(Y0 + 1) / X0, ?_, fun h => absurd h (not_lt.2 h3)⟩
    rw [div_mul_cancel₀ _ hX0.ne']; linarith
  rw [not_le] at h0 h3
  have p0 : 0 < X0 - ℓ := sub_pos.2 h0
  have p3 : 0 < X3 - ℓ := sub_pos.2 h3
  by_cases hc : Y3 * (X0 - ℓ) < Y0 * X3
  · left
    obtain ⟨κ, h1, h2⟩ := exists_between
      (show Y3 / X3 < Y0 / (X0 - ℓ) by rw [div_lt_div_iff₀ hX3 p0]; linarith)
    exact ⟨κ, (div_lt_iff₀ hX3).1 h1, fun _ => (lt_div_iff₀ p0).1 h2⟩
  · right
    rw [not_lt] at hc
    have hc' : Y0 * (X3 - ℓ) < Y3 * X0 := by nlinarith [mul_pos hY0 hℓ, mul_pos hY3 hℓ]
    obtain ⟨κ, h1, h2⟩ := exists_between
      (show Y0 / X0 < Y3 / (X3 - ℓ) by rw [div_lt_div_iff₀ hX0 p3]; linarith)
    exact ⟨κ, (div_lt_iff₀ hX0).1 h1, fun _ => (lt_div_iff₀ p3).1 h2⟩

/-- **Slide Lemma between two walls, the case `X > 0` on the deep points.**  The rectangle data of
`slide_tab` with the coordinate tables `X Y G`; each wall (`G = 0`, `G = ⟪g, g⟫`) has exactly one
deep point (`p`, `q`).  Then Rupert: `kdich` gives (K₊) at one of the two walls, and the other wall
is the first after the swap `g ↦ -g`, `G ↦ ⟪g, g⟫ - G`, with the corners `a' b' a b`. -/
theorem slide_walls_pos {n : ℕ} (x : Fin n → ℝ³) (a b a' b' p q : Fin n) (e g nQ : ℝ³)
    (X Y G : Fin n → ℝ)
    (hX : ∀ i, ⟪x i - x a, e⟫ = X i) (hY : ∀ i, ⟪x i - x a, nQ⟫ = Y i)
    (hG : ∀ i, ⟪x i - x a, g⟫ = G i)
    (he : x b - x a = e) (hg : x a' - x a = g) (hb' : x b' - x a = e + g)
    (he0 : e ≠ 0) (hg0 : g ≠ 0) (hn0 : nQ ≠ 0)
    (heg : ⟪e, g⟫ = 0) (hen : ⟪e, nQ⟫ = 0) (hgn : ⟪g, nQ⟫ = 0)
    (hD : ∀ i, i ≠ a → i ≠ b → i ≠ a' → i ≠ b' → 0 < Y i)
    (hZ : ∀ i, 0 ≤ G i ∧ G i ≤ ⟪g, g⟫)
    (hp : 0 < Y p) (hpG : G p = 0) (hpu : ∀ i, 0 < Y i → G i = 0 → i = p)
    (hq : 0 < Y q) (hqG : G q = ⟪g, g⟫) (hqu : ∀ i, 0 < Y i → G i = ⟪g, g⟫ → i = q)
    (hSl : ∀ i, 0 < Y i → 0 < X i) :
    IsRupert (univ.image x) := by
  have hee : 0 < ⟪e, e⟫ := by
    rw [real_inner_self_eq_norm_sq]; have := norm_pos_iff.2 he0; positivity
  have hgeg : ⟪g, e⟫ = 0 := by rw [real_inner_comm]; exact heg
  rcases kdich hee (hSl p hp) (hSl q hq) hp hq with ⟨κ, k1, k2⟩ | ⟨κ, k1, k2⟩
  · refine slide_tab x a b a' b' e g nQ X Y G hX hY hG he hg hb' he0 hg0 hn0 heg hen hgn hD hZ hSl
      ⟨q, hq, hqG⟩ ⟨κ, fun i hi hGi => ?_, fun i hi hGi hl => ?_⟩
    · have h := hqu i hi hGi; subst h; exact k1
    · have h := hpu i hi hGi; subst h; exact k2 hl
  · have hb1 := hb'
    have hg1 := hg
    have he1 := he
    rw [sub_eq_iff_eq_add] at hb1 hg1 he1
    have hsub : ∀ i, x i - x a' = (x i - x a) - g := fun i => by rw [← hg]; abel
    refine slide_tab x a' b' a b e (-g) nQ X Y (fun i => ⟪g, g⟫ - G i) ?_ ?_ ?_ ?_ ?_ ?_
      he0 (neg_ne_zero.2 hg0) hn0 (by rw [inner_neg_right, heg, neg_zero]) hen
      (by rw [inner_neg_left, hgn, neg_zero])
      (fun i h1 h2 h3 h4 => hD i h3 h4 h1 h2) ?_ hSl ⟨p, hp, ?_⟩ ⟨κ, ?_, ?_⟩
    · intro i; rw [hsub, inner_sub_left, hgeg, hX]; ring
    · intro i; rw [hsub, inner_sub_left, hgn, hY]; ring
    · intro i
      rw [hsub, inner_neg_right, inner_sub_left, hG]; ring
    · rw [hb1, hg1]; abel
    · rw [hg1]; abel
    · rw [he1, hg1]; abel
    · intro i
      obtain ⟨h1, h2⟩ := hZ i
      simp only [inner_neg_neg]; constructor <;> linarith
    · show ⟪g, g⟫ - G p = ⟪-g, -g⟫
      rw [inner_neg_neg]; linarith
    · intro i hi h
      have h' : G i = 0 := by
        try simp only [inner_neg_neg] at h
        linarith
      have h'' := hpu i hi h'; subst h''; exact k1
    · intro i hi h hl
      have h' : G i = ⟪g, g⟫ := by linarith
      have h'' := hqu i hi h'; subst h''; exact k2 hl

/-- **The Slide Lemma between two parallel walls** (`g ⟂ e, nQ`; the rectangle `Q = a b b' a'` of
`slide_tab`, the walls `F ∋ a, b` (`G = 0`) and `H ∋ a', b'` (`G = ⟪g, g⟫`), all points in the slab
`0 ≤ G ≤ ⟪g, g⟫`, deep points `Y > 0` off the corners).  Each wall has exactly one deep point (`p`
on `F`, `q` on `H`), and the deep points all lie beyond the plane through `a` orthogonal to `e`
(`X > 0`) or all before the plane through `b` (`X < ⟪e, e⟫`).  Then Rupert, with no slope
hypothesis: `kdich` supplies (K₊) at one of the two walls, and `slide_tab` is applied at the
corner labellings `(a, b, a', b')`, `(a', b', a, b)` for the first slab case and, by the edge
reversal `e ↦ -e`, `X ↦ ⟪e, e⟫ - X`, at `(b, a, b', a')`, `(b', a', b, a)` for the second. -/
theorem slide_walls {n : ℕ} (x : Fin n → ℝ³) (a b a' b' p q : Fin n) (e g nQ : ℝ³)
    (X Y G : Fin n → ℝ)
    (hX : ∀ i, ⟪x i - x a, e⟫ = X i) (hY : ∀ i, ⟪x i - x a, nQ⟫ = Y i)
    (hG : ∀ i, ⟪x i - x a, g⟫ = G i)
    (he : x b - x a = e) (hg : x a' - x a = g) (hb' : x b' - x a = e + g)
    (he0 : e ≠ 0) (hg0 : g ≠ 0) (hn0 : nQ ≠ 0)
    (heg : ⟪e, g⟫ = 0) (hen : ⟪e, nQ⟫ = 0) (hgn : ⟪g, nQ⟫ = 0)
    (hD : ∀ i, i ≠ a → i ≠ b → i ≠ a' → i ≠ b' → 0 < Y i)
    (hZ : ∀ i, 0 ≤ G i ∧ G i ≤ ⟪g, g⟫)
    (hp : 0 < Y p) (hpG : G p = 0) (hpu : ∀ i, 0 < Y i → G i = 0 → i = p)
    (hq : 0 < Y q) (hqG : G q = ⟪g, g⟫) (hqu : ∀ i, 0 < Y i → G i = ⟪g, g⟫ → i = q)
    (hSl : (∀ i, 0 < Y i → 0 < X i) ∨ (∀ i, 0 < Y i → X i < ⟪e, e⟫)) :
    IsRupert (univ.image x) := by
  rcases hSl with hSl | hSl
  · exact slide_walls_pos x a b a' b' p q e g nQ X Y G hX hY hG he hg hb' he0 hg0 hn0 heg hen hgn
      hD hZ hp hpG hpu hq hqG hqu hSl
  · have hb1 := hb'
    have hg1 := hg
    have he1 := he
    rw [sub_eq_iff_eq_add] at hb1 hg1 he1
    have hsub : ∀ i, x i - x b = (x i - x a) - e := fun i => by rw [← he]; abel
    refine slide_walls_pos x b a b' a' p q (-e) g nQ (fun i => ⟪e, e⟫ - X i) Y G ?_ ?_ ?_ ?_ ?_ ?_
      (neg_ne_zero.2 he0) hg0 hn0 (by rw [inner_neg_left, heg, neg_zero])
      (by rw [inner_neg_left, hen, neg_zero]) hgn
      (fun i h1 h2 h3 h4 => hD i h2 h1 h4 h3) hZ hp hpG hpu hq hqG hqu
      (fun i hi => sub_pos.2 (hSl i hi))
    · intro i; rw [hsub, inner_neg_right, inner_sub_left, hX]; ring
    · intro i; rw [hsub, inner_sub_left, hen, hY]; ring
    · intro i; rw [hsub, inner_sub_left, heg, hG]; ring
    · rw [he1]; abel
    · rw [hb1, he1]; abel
    · rw [hg1, he1]; abel

end Minimality.Split.Slide

#print axioms Minimality.Split.Slide.slide_core_rupert
#print axioms Minimality.Split.Slide.slide_tab
#print axioms Minimality.Split.Slide.kdich
#print axioms Minimality.Split.Slide.slide_walls
