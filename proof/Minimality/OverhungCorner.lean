module

public import Mathlib
public import Minimality.CornerSlide

@[expose] public section

/-!
# The Overhung Corner Slide (normal form and Euclidean form)

Sibling of the Corner Slide Lemma (`Minimality.Split.Corner.corner_euclid`) for a corner whose two
edge ends `J`, `M` are both overhung.

Normal form: corner `c = 0`, `J = (0, L, 0)`, `M = (0, 0, H)` (coordinates `(p_K, p_J, p_M)`),
all points in the octant, every point off `c, J, M` deep (`x₀ > 0`).  Instead of the hypothesis (Nj)
of the Corner Slide Lemma, two points `J'` (beyond `J`: `x₁ > L`) and `M'` (beyond `M`: `x₂ > H`,
`x₁ > 0`) are given, and the screen picture at the limit view is
`c, J` on the axes, `J -> J'` of slope `tan lambda = x₂(J') / (x₁(J') - L)`, `M' -> M` of slope
`tan mu = (x₂(M') - H) / x₁(M')`.

View `U s = (1, -s, -s²)` as in the Corner Slide Lemma.  Motion (the one of CORNER24DIRECT 2(C),
with `alpha = -1`, `beta = t`, `A = L`, `B = t H`):
`ω = (s g, t, -1)` (a deep slide `d = (-1, -t)` plus a spin `s g` about the view axis),
`τ = s (0, x, y)`.  Velocities: `c : s (x, y)`, `J : s (x + L, g L + y + s L)`,
`M : s (x + t H - g H, y + s t H)`, deep `p : p₀ (-1, -t) + O(s)`.

Rows: `c` the angle `(J, c, M)`, `J` the angle `(J', J, c)` (corner `y₀ = c`, `y₁ = J'`), `M` the angle
`(c, M, M')`; a deep point inside the triangle `cJM` the triangle row (`Corner.row_A`); a deep point
beyond the hypotenuse the angle `(M, p, J)`, whose velocity `p₀ d` points inside iff
`t (x₁ - L) < x₂ < H + t x₁` (`t` strictly between `tan mu` and `tan lambda`).
-/

set_option autoImplicit false
open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality.Split.Overhung
open Minimality.Split
open Minimality.Split.Corner (U U_ne row_A ev_pos_add)
open Minimality (pt pt_zero pt_one pt_two cross)

/-- `s^m h(s)` with `h` continuous and `h 0 > 0` is eventually positive. -/
theorem ev_mul {f : ℝ → ℝ} (m : ℕ) (h : ℝ → ℝ) (hc : Continuous h) (h0 : 0 < h 0)
    (hfg : ∀ s, f s = s ^ m * h s) : ∀ᶠ s in 𝓝[>] (0:ℝ), 0 < f s := by
  have h1 : ∀ᶠ s in 𝓝 (0:ℝ), 0 < h s := (hc.tendsto 0).eventually_const_lt h0
  filter_upwards [h1.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with s hs hs0
  rw [hfg]; exact mul_pos (pow_pos (Set.mem_Ioi.1 hs0) m) hs

/-- The angular velocity `(s g, t, -1)`. -/
noncomputable def OmO (g t s : ℝ) : ℝ³ := pt (s * g) t (-1)
/-- The translation `s (0, x, y)`. -/
noncomputable def TauO (x y s : ℝ) : ℝ³ := pt 0 (s * x) (s * y)

syntax "ocs_simp" : tactic
macro_rules
  | `(tactic| ocs_simp) => `(tactic| simp only [det3, Corner.U, OmO, TauO, cross_0, cross_1, cross_2,
      PiLp.add_apply, PiLp.sub_apply, pt_zero, pt_one, pt_two])

/-- A determinant `det3 a (ω(s) × p + τ(s)) (U s)` whose value at `s = 0` is positive is eventually
positive (the rows of deep points). -/
theorem ev_det3 (a p : ℝ³) (g t x y : ℝ)
    (h0 : 0 < det3 a (cross (OmO g t 0) p + TauO x y 0) (U 0)) :
    ∀ᶠ s in 𝓝[>] (0:ℝ), 0 < det3 a (cross (OmO g t s) p + TauO x y s) (U s) :=
  ev_mul 0 (fun s => det3 a (cross (OmO g t s) p + TauO x y s) (U s))
    (by ocs_simp; fun_prop) h0 (fun s => by simp)

/-- Positivity of the two velocity inequalities of a deep point beyond the hypotenuse. -/
theorem deep_cond {n : ℕ} (x : Fin n → ℝ³) (L H t : ℝ) (jp mp i : Fin n) (hQ1 : 0 ≤ x i 1) (hQ2 : 0 ≤ x i 2) (hj1 : L < x jp 1) (hm1 : 0 < x mp 1)
    (ht1 : x mp 2 - H < t * x mp 1) (ht2 : t * (x jp 1 - L) < x jp 2) (htp : 0 < t)
    (hJ1 : 0 ≤ (x jp 1 - L) * x i 2 - x jp 2 * (x i 1 - L)) (hJ2 : ¬ (x i 1 = L ∧ x i 2 = 0))
    (hM1 : 0 ≤ (x mp 2 - H) * x i 1 - x mp 1 * (x i 2 - H)) (hM2 : ¬ (x i 1 = 0 ∧ x i 2 = H)) :
    0 < t * x i 1 + H - x i 2 ∧ 0 < x i 2 - t * (x i 1 - L) := by
  have hq : 0 < x jp 1 - L := sub_pos.2 hj1
  constructor
  · rcases hQ1.lt_or_eq with hX | hX
    · have h1 : x mp 1 * (x i 2 - H) < x mp 1 * (t * x i 1) := by
        nlinarith [mul_lt_mul_of_pos_right ht1 hX]
      have := lt_of_mul_lt_mul_left h1 hm1.le
      linarith
    · have hX' : x i 1 = 0 := hX.symm
      have hY : x i 2 ≠ H := fun h => hM2 ⟨hX', h⟩
      have : x i 2 ≤ H := by
        rw [hX'] at hM1
        nlinarith
      have := lt_of_le_of_ne this hY
      rw [hX']; linarith
  · rcases lt_trichotomy (x i 1) L with hX | hX | hX
    · nlinarith
    · have hY : x i 2 ≠ 0 := fun h => hJ2 ⟨hX, h⟩
      have := lt_of_le_of_ne hQ2 (Ne.symm hY)
      rw [hX]; linarith
    · have h1 : t * (x jp 1 - L) * (x i 1 - L) < x jp 2 * (x i 1 - L) :=
        mul_lt_mul_of_pos_right ht2 (sub_pos.2 hX)
      have h2 : (x jp 1 - L) * (t * (x i 1 - L)) < (x jp 1 - L) * x i 2 := by nlinarith
      have := lt_of_mul_lt_mul_left h2 hq.le
      linarith

/-- The certificate with all parameters given. -/
theorem ocs_core_params {n : ℕ} (x : Fin n → ℝ³) (c J M jp mp : Fin n) (L H t xx yy g : ℝ)
    (hL : 0 < L) (hH : 0 < H) (hc : x c = pt 0 0 0) (hJ : x J = pt 0 L 0) (hM : x M = pt 0 0 H)
    (hQ : ∀ i, 0 ≤ x i 1 ∧ 0 ≤ x i 2)
    (hD : ∀ i, i ≠ c → i ≠ J → i ≠ M → 0 < x i 0)
    (hj1 : L < x jp 1) (hm1 : 0 < x mp 1) (hm2 : H < x mp 2)
    (ht1 : x mp 2 - H < t * x mp 1) (ht2 : t * (x jp 1 - L) < x jp 2)
    (hJline : ∀ i, i ≠ c → i ≠ J → i ≠ M → L * H ≤ H * x i 1 + L * x i 2 →
      0 ≤ (x jp 1 - L) * x i 2 - x jp 2 * (x i 1 - L) ∧ ¬ (x i 1 = L ∧ x i 2 = 0))
    (hMline : ∀ i, i ≠ c → i ≠ J → i ≠ M → L * H ≤ H * x i 1 + L * x i 2 →
      0 ≤ (x mp 2 - H) * x i 1 - x mp 1 * (x i 2 - H) ∧ ¬ (x i 1 = 0 ∧ x i 2 = H))
    (hxx : 0 < xx) (hyy : 0 < yy)
    (hG1 : x jp 2 * (xx + L) < (x jp 1 - L) * (g * L + yy))
    (hG2 : x mp 1 * yy < (x mp 2 - H) * (xx - g * H + t * H)) :
    ∀ᶠ s in 𝓝[>] (0:ℝ), FreeAt (univ.image x) (U s) := by
  classical
  have htp : 0 < t := by
    by_contra hneg
    push Not at hneg
    nlinarith [mul_nonpos_of_nonpos_of_nonneg hneg hm1.le]
  have hq : 0 < x jp 1 - L := sub_pos.2 hj1
  have hq2 : 0 < x jp 2 := lt_trans (mul_pos htp hq) ht2
  have hgy : 0 < g * L + yy := by
    by_contra hneg
    push Not at hneg
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hq.le hneg, mul_pos hq2 (add_pos hxx hL)]
  have hw : 0 < xx - g * H + t * H := by
    by_contra hneg
    push Not at hneg
    nlinarith [mul_nonpos_of_nonneg_of_nonpos (sub_pos.2 hm2).le hneg, mul_pos hm1 hyy]
  have hjpc : jp ≠ c := by rintro rfl; rw [hc] at hj1; simp at hj1; linarith
  have hjpJ : jp ≠ J := by rintro rfl; rw [hJ] at hj1; simp at hj1
  have hjpM : jp ≠ M := by rintro rfl; rw [hM] at hj1; simp at hj1; linarith
  have hmpc : mp ≠ c := by rintro rfl; rw [hc] at hm2; simp at hm2; linarith
  have hmpJ : mp ≠ J := by rintro rfl; rw [hJ] at hm2; simp at hm2; linarith
  have hmpM : mp ≠ M := by rintro rfl; rw [hM] at hm2; simp at hm2
  have hjp0 := hD jp hjpc hjpJ hjpM
  have hmp0 := hD mp hmpc hmpJ hmpM
  have mem : ∀ j, x j ∈ univ.image x := fun j => mem_image_of_mem x (mem_univ j)
  have hrow : ∀ i, ∀ᶠ s in 𝓝[>] (0:ℝ),
      TiltCert (univ.image x) (U s) (OmO g t s) (TauO xx yy s) (x i) := by
    intro i
    by_cases hic : i = c
    · subst hic
      have e1 : ∀ᶠ s in 𝓝[>] (0:ℝ), 0 < det3 (pt 0 L 0 - pt 0 0 0) (pt 0 0 H - pt 0 0 0) (U s) :=
        ev_mul 0 (fun _ => L * H) (by fun_prop) (by positivity) (fun s => by ocs_simp; ring)
      have e2 : ∀ᶠ s in 𝓝[>] (0:ℝ), 0 < det3 (pt 0 L 0 - pt 0 0 0)
          (cross (OmO g t s) (pt 0 0 0) + TauO xx yy s) (U s) :=
        ev_mul 1 (fun _ => L * yy) (by fun_prop) (by positivity) (fun s => by ocs_simp; ring)
      have e3 : ∀ᶠ s in 𝓝[>] (0:ℝ), 0 < det3 (pt 0 0 0 - pt 0 0 H)
          (cross (OmO g t s) (pt 0 0 0) + TauO xx yy s) (U s) :=
        ev_mul 1 (fun _ => H * xx) (by fun_prop) (by positivity) (fun s => by ocs_simp; ring)
      filter_upwards [e1.and (e2.and e3)] with s hs
      left
      refine ⟨x M, mem M, x J, mem J, ?_⟩
      rw [hc, hJ, hM]; exact hs
    by_cases hiJ : i = J
    · subst hiJ
      have e1 : ∀ᶠ s in 𝓝[>] (0:ℝ), 0 < det3 (x jp - pt 0 L 0) (pt 0 0 0 - pt 0 L 0) (U s) :=
        ev_mul 0 (fun s => L * (x jp 2 + s ^ 2 * x jp 0)) (by fun_prop)
          (by simpa using mul_pos hL hq2) (fun s => by ocs_simp; ring)
      have e2 : ∀ᶠ s in 𝓝[>] (0:ℝ), 0 < det3 (x jp - pt 0 L 0)
          (cross (OmO g t s) (pt 0 L 0) + TauO xx yy s) (U s) :=
        ev_mul 1 (fun s => (x jp 1 - L + s * x jp 0) * (g * L + yy + s * L)
            - (x jp 2 + s ^ 2 * x jp 0) * (xx + L)) (by fun_prop)
          (by norm_num; linarith) (fun s => by ocs_simp; ring)
      have e3 : ∀ᶠ s in 𝓝[>] (0:ℝ), 0 < det3 (pt 0 L 0 - pt 0 0 0)
          (cross (OmO g t s) (pt 0 L 0) + TauO xx yy s) (U s) :=
        ev_mul 1 (fun s => L * (g * L + yy + s * L)) (by fun_prop)
          (by simpa using mul_pos hL hgy) (fun s => by ocs_simp; ring)
      filter_upwards [e1.and (e2.and e3)] with s hs
      left
      refine ⟨x c, mem c, x jp, mem jp, ?_⟩
      rw [hc, hJ]; exact hs
    by_cases hiM : i = M
    · subst hiM
      have e1 : ∀ᶠ s in 𝓝[>] (0:ℝ), 0 < det3 (pt 0 0 0 - pt 0 0 H) (x mp - pt 0 0 H) (U s) :=
        ev_mul 0 (fun s => H * (x mp 1 + s * x mp 0)) (by fun_prop)
          (by simpa using mul_pos hH hm1) (fun s => by ocs_simp; ring)
      have e2 : ∀ᶠ s in 𝓝[>] (0:ℝ), 0 < det3 (pt 0 0 0 - pt 0 0 H)
          (cross (OmO g t s) (pt 0 0 H) + TauO xx yy s) (U s) :=
        ev_mul 1 (fun _ => H * (xx - g * H + t * H)) (by fun_prop)
          (by simpa using mul_pos hH hw) (fun s => by ocs_simp; ring)
      have e3 : ∀ᶠ s in 𝓝[>] (0:ℝ), 0 < det3 (pt 0 0 H - x mp)
          (cross (OmO g t s) (pt 0 0 H) + TauO xx yy s) (U s) :=
        ev_mul 1 (fun s => (x mp 2 - H) * (xx - g * H + t * H) - x mp 1 * yy
            - s * x mp 0 * yy - s * x mp 1 * t * H + s ^ 2 * x mp 0 * (xx - g * H))
          (by fun_prop) (by norm_num; linarith) (fun s => by ocs_simp; ring)
      filter_upwards [e1.and (e2.and e3)] with s hs
      left
      refine ⟨x mp, mem mp, x c, mem c, ?_⟩
      rw [hc, hM]; exact hs
    have h0 := hD i hic hiJ hiM
    rcases lt_or_ge (H * x i 1 + L * x i 2) (L * H) with hA | hB
    · filter_upwards [row_A L H (x i) hL hH h0 (hQ i).1 (hQ i).2 hA] with s hs
      right
      refine ⟨x c, mem c, x J, mem J, x M, mem M, ?_⟩
      rw [hc, hJ, hM]; exact hs
    · obtain ⟨hJ1, hJ2⟩ := hJline i hic hiJ hiM hB
      obtain ⟨hM1, hM2⟩ := hMline i hic hiJ hiM hB
      obtain ⟨hNM, hNJ⟩ := deep_cond x L H t jp mp i (hQ i).1 (hQ i).2 hj1 hm1 ht1 ht2 htp
        hJ1 hJ2 hM1 hM2
      have e1 : ∀ᶠ s in 𝓝[>] (0:ℝ), 0 < det3 (pt 0 0 H - x i) (pt 0 L 0 - x i) (U s) :=
        ev_pos_add (H * x i 1 + L * x i 2 - L * H) 1 (H * x i 0) (fun _ => L * x i 0)
          (by fun_prop) (by linarith) (by positivity) (fun s => by ocs_simp; ring)
      have e2 : ∀ᶠ s in 𝓝[>] (0:ℝ), 0 < det3 (pt 0 0 H - x i)
          (cross (OmO g t s) (x i) + TauO xx yy s) (U s) := by
        refine ev_det3 _ _ g t xx yy ?_
        have : det3 (pt 0 0 H - x i) (cross (OmO g t 0) (x i) + TauO xx yy 0) (U 0)
            = x i 0 * (t * x i 1 + H - x i 2) := by ocs_simp; ring
        rw [this]; exact mul_pos h0 hNM
      have e3 : ∀ᶠ s in 𝓝[>] (0:ℝ), 0 < det3 (x i - pt 0 L 0)
          (cross (OmO g t s) (x i) + TauO xx yy s) (U s) := by
        refine ev_det3 _ _ g t xx yy ?_
        have : det3 (x i - pt 0 L 0) (cross (OmO g t 0) (x i) + TauO xx yy 0) (U 0)
            = x i 0 * (x i 2 - t * (x i 1 - L)) := by ocs_simp; ring
        rw [this]; exact mul_pos h0 hNJ
      filter_upwards [e1.and (e2.and e3)] with s hs
      left
      refine ⟨x J, mem J, x M, mem M, ?_⟩
      rw [hJ, hM]; exact hs
  filter_upwards [Filter.eventually_all.2 hrow] with s hs
  refine ⟨OmO g t s, TauO xx yy s, fun y hy => ?_⟩
  obtain ⟨i, -, rfl⟩ := mem_image.1 hy
  exact hs i

/-- The parameters `x, y, g` of the motion exist (the feasibility condition of CORNER24DIRECT 2(C)):
`tl`, `tm` the slopes of `J -> J'` and `M' -> M`, `t` strictly between, and
`tan mu > L/H` or `tan lambda < L/H`. -/
theorem ocs_exists_real (L H t tl tm : ℝ) (hL : 0 < L) (hH : 0 < H) (htm : 0 < tm)
    (h2 : t < tl) (hs : L / H < tm ∨ tl < L / H) :
    ∃ xx yy G : ℝ, 0 < xx ∧ 0 < yy ∧ tl * (xx + L) < G + yy ∧
      yy < tm * (xx + t * H - G * H / L) := by
  set q : ℝ := L / H with hqdef
  have hq : 0 < q := div_pos hL hH
  have hqH : q * H = L := by rw [hqdef]; field_simp
  have key : ∀ xx yy : ℝ, 0 < xx → 0 < yy →
      0 < xx * (q - tl) + L * (t - tl) + yy * (1 - q / tm) →
      ∃ xx yy G : ℝ, 0 < xx ∧ 0 < yy ∧ tl * (xx + L) < G + yy ∧
        yy < tm * (xx + t * H - G * H / L) := by
    intro xx yy hx hy hpos
    have e : q * (t * H) = t * L := by rw [← hqH]; ring
    have hlh : tl * (xx + L) - yy < q * (xx + t * H - yy / tm) := by
      have : q * (xx + t * H - yy / tm) = q * xx + q * (t * H) - q * (yy / tm) := by ring
      have h3 : yy * (1 - q / tm) = yy - q * (yy / tm) := by ring
      nlinarith [hpos, e, h3, this]
    set lo := tl * (xx + L) - yy with hlo
    set hi := q * (xx + t * H - yy / tm) with hhi
    refine ⟨xx, yy, (lo + hi) / 2, hx, hy, by linarith, ?_⟩
    have hG : (lo + hi) / 2 < q * (xx + t * H - yy / tm) := by linarith
    have h4 : (lo + hi) / 2 * H / L < xx + t * H - yy / tm := by
      rw [div_lt_iff₀ hL]
      have h6 : q * (xx + t * H - yy / tm) * H = (xx + t * H - yy / tm) * L := by
        rw [← hqH]; ring
      have := mul_lt_mul_of_pos_right hG hH
      linarith
    have := (div_lt_iff₀ htm).1 (by linarith : yy / tm < xx + t * H - (lo + hi) / 2 * H / L)
    linarith
  rcases hs with hs | hs
  · have hv : 0 < 1 - q / tm := by rw [sub_pos, div_lt_one htm]; exact hs
    have hnum : 0 < |q - tl| + L * (tl - t) + 1 := by
      have := abs_nonneg (q - tl); have := mul_pos hL (sub_pos.2 h2); linarith
    have hy : 0 < (|q - tl| + L * (tl - t) + 1) / (1 - q / tm) := div_pos hnum hv
    refine key 1 _ one_pos hy ?_
    rw [div_mul_cancel₀ _ hv.ne']
    have := neg_le_abs (q - tl)
    nlinarith
  · have hqt : 0 < q - tl := sub_pos.2 hs
    have hnum : 0 < L * (tl - t) + |1 - q / tm| + 1 := by
      have := abs_nonneg (1 - q / tm); have := mul_pos hL (sub_pos.2 h2); linarith
    have hx : 0 < (L * (tl - t) + |1 - q / tm| + 1) / (q - tl) := div_pos hnum hqt
    refine key _ 1 hx one_pos ?_
    rw [div_mul_cancel₀ _ hqt.ne']
    have := neg_le_abs (1 - q / tm)
    nlinarith

/-- **Overhung Corner Slide, normal form (free view).**  See `overhung_core_rupert`. -/
theorem overhung_core {n : ℕ} (x : Fin n → ℝ³) (c J M jp mp : Fin n) (L H : ℝ) (hL : 0 < L)
    (hH : 0 < H) (hc : x c = pt 0 0 0) (hJ : x J = pt 0 L 0) (hM : x M = pt 0 0 H)
    (hQ : ∀ i, 0 ≤ x i 1 ∧ 0 ≤ x i 2)
    (hD : ∀ i, i ≠ c → i ≠ J → i ≠ M → 0 < x i 0)
    (hj1 : L < x jp 1) (hm1 : 0 < x mp 1) (hm2 : H < x mp 2)
    (hturn : (x mp 2 - H) * (x jp 1 - L) < x jp 2 * x mp 1)
    (hslope : L * x mp 1 < H * (x mp 2 - H) ∨ H * x jp 2 < L * (x jp 1 - L))
    (hJline : ∀ i, i ≠ c → i ≠ J → i ≠ M → L * H ≤ H * x i 1 + L * x i 2 →
      0 ≤ (x jp 1 - L) * x i 2 - x jp 2 * (x i 1 - L) ∧ ¬ (x i 1 = L ∧ x i 2 = 0))
    (hMline : ∀ i, i ≠ c → i ≠ J → i ≠ M → L * H ≤ H * x i 1 + L * x i 2 →
      0 ≤ (x mp 2 - H) * x i 1 - x mp 1 * (x i 2 - H) ∧ ¬ (x i 1 = 0 ∧ x i 2 = H)) :
    ∀ᶠ s in 𝓝[>] (0:ℝ), FreeAt (univ.image x) (U s) := by
  have hq : 0 < x jp 1 - L := sub_pos.2 hj1
  have hmH : 0 < x mp 2 - H := sub_pos.2 hm2
  set tl : ℝ := x jp 2 / (x jp 1 - L) with htl
  set tm : ℝ := (x mp 2 - H) / x mp 1 with htmdef
  have htm : 0 < tm := div_pos hmH hm1
  have hlt : tm < tl := (div_lt_div_iff₀ hm1 hq).2 hturn
  set t : ℝ := (tl + tm) / 2 with ht
  have hs : L / H < tm ∨ tl < L / H := by
    rcases hslope with h | h
    · left; rw [htmdef, div_lt_div_iff₀ hH hm1]; linarith
    · right; rw [htl, div_lt_div_iff₀ hq hH]; linarith
  obtain ⟨xx, yy, G, hxx, hyy, hG1', hG2'⟩ :=
    ocs_exists_real L H t tl tm hL hH htm (by rw [ht]; linarith) hs
  have ht1 : x mp 2 - H < t * x mp 1 := by
    have : tm < t := by rw [ht]; linarith
    rwa [htmdef, div_lt_iff₀ hm1] at this
  have ht2 : t * (x jp 1 - L) < x jp 2 := by
    have : t < tl := by rw [ht]; linarith
    rwa [htl, lt_div_iff₀ hq] at this
  set g : ℝ := G / L with hg
  have hgL : g * L = G := by rw [hg]; field_simp
  have hgH : g * H = G * H / L := by rw [hg]; ring
  refine ocs_core_params x c J M jp mp L H t xx yy g hL hH hc hJ hM hQ hD hj1 hm1 hm2 ht1 ht2
    hJline hMline hxx hyy ?_ ?_
  · rw [hgL]
    rw [htl, div_mul_eq_mul_div, div_lt_iff₀ hq] at hG1'
    linarith
  · rw [hgH]
    rw [htmdef, div_mul_eq_mul_div, lt_div_iff₀ hm1] at hG2'
    linarith

/-- **Overhung Corner Slide, normal form.**  The corner `c = 0`, `J = (0, L, 0)`, `M = (0, 0, H)`
(coordinates `(p_K, p_J, p_M)`), every point in the octant `x₁, x₂ ≥ 0`, (T) every point other than
`c, J, M` deep (`x₀ > 0`).  `J'` = `jp` lies beyond `J` (`x₁ > L`), `M'` = `mp` beyond `M`
(`x₂ > H`, `x₁ > 0`).
* (i) `hturn`: `tan mu < tan lambda`, where `tan lambda = x₂(J') / (x₁(J') - L)` (slope of `J -> J'`)
  and `tan mu = (x₂(M') - H) / x₁(M')` (slope of `M' -> M`), cleared of denominators;
* (ii) `hslope`: `tan mu > L / H` or `tan lambda < L / H`;
* (hJline, hMline) for every deep point beyond the hypotenuse `H x₁ + L x₂ ≥ L H`: it lies weakly
  left of the line `J J'` (resp. `M' M`), and it is not directly over `J` (resp. `M`).
Then `V` is Rupert. -/
theorem overhung_core_rupert {n : ℕ} (x : Fin n → ℝ³) (c J M jp mp : Fin n) (L H : ℝ)
    (hL : 0 < L) (hH : 0 < H) (hc : x c = pt 0 0 0) (hJ : x J = pt 0 L 0) (hM : x M = pt 0 0 H)
    (hQ : ∀ i, 0 ≤ x i 1 ∧ 0 ≤ x i 2)
    (hD : ∀ i, i ≠ c → i ≠ J → i ≠ M → 0 < x i 0)
    (hj1 : L < x jp 1) (hm1 : 0 < x mp 1) (hm2 : H < x mp 2)
    (hturn : (x mp 2 - H) * (x jp 1 - L) < x jp 2 * x mp 1)
    (hslope : L * x mp 1 < H * (x mp 2 - H) ∨ H * x jp 2 < L * (x jp 1 - L))
    (hJline : ∀ i, i ≠ c → i ≠ J → i ≠ M → L * H ≤ H * x i 1 + L * x i 2 →
      0 ≤ (x jp 1 - L) * x i 2 - x jp 2 * (x i 1 - L) ∧ ¬ (x i 1 = L ∧ x i 2 = 0))
    (hMline : ∀ i, i ≠ c → i ≠ J → i ≠ M → L * H ≤ H * x i 1 + L * x i 2 →
      0 ≤ (x mp 2 - H) * x i 1 - x mp 1 * (x i 2 - H) ∧ ¬ (x i 1 = 0 ∧ x i 2 = H)) :
    IsRupert (univ.image x) := by
  obtain ⟨s, hs⟩ := (overhung_core x c J M jp mp L H hL hH hc hJ hM hQ hD hj1 hm1 hm2 hturn
    hslope hJline hMline).exists
  exact FreeAt.isRupert (Corner.U_ne s) hs

end Minimality.Split.Overhung


/-! ### Euclidean form -/

set_option autoImplicit false
open Finset

namespace Minimality.Split.Overhung
open Minimality (pt pt_zero pt_one pt_two IsFrame orthoFrameMat orthoFrameMat_apply
  isRupert_of_frame_image)

/-- **Overhung Corner Slide, Euclidean form.**  `c, J, M` the corner and two of its edge ends
(`e = x J - x c ⟂ f = x M - x c`, both nonzero), `g ≠ 0` orthogonal to both (normal of the face
`c J M`, pointing into the polytope).  Write `P i = ⟪x i - x c, e⟫`, `R i = ⟪x i - x c, f⟫`
(the corner coordinates times the lengths).  `jp` (= `J'`) lies beyond `J` (`P > ⟪e,e⟫`), `mp` (= `M'`)
beyond `M` (`R > ⟪f,f⟫`, `P > 0`).

* (hD) every point other than `c, J, M` is deep (`⟪·, g⟫ > 0`); (hQ) `P, R ≥ 0`;
* (hturn) the chain turn `tan mu < tan lambda`, `tan lambda` the slope of `J -> J'` and `tan mu` the
  slope of `M' -> M`: `(R m' - ⟪f,f⟫) (P j' - ⟪e,e⟫) < R j' P m'`;
* (hslope) `tan mu > L/H` or `tan lambda < L/H` (`L = |e|`, `H = |f|`), which in the raw coordinates
  `P, R` is the metric-free `P m' < R m' - ⟪f,f⟫` or `R j' < P j' - ⟪e,e⟫`;
* (hJline, hMline) every deep point beyond the hypotenuse `⟪f,f⟫ P + ⟪e,e⟫ R ≥ ⟪e,e⟫ ⟪f,f⟫` lies weakly
  left of the line `J J'` (resp. `M' M`) and is not directly over `J` (resp. `M`).

What changed against the draft in CORNER24DIRECT.md section 4 (which was not provable as written):
the draft states `J J'` and `M' M` as supporting edges of the shadow at the view `g`
(`cross2 >= 0` for all `i`, both weak) and the slope hypotheses via the shadow hull; the proof
needs neither the hull nor the shadow at all: each point carries its own `TiltCert` row, so only the
inequalities of `d = (-1, -t)` (`t` strictly between `tan mu` and `tan lambda`) against each deep
point beyond the hypotenuse enter (`deep_cond`), and `J'`, `M'` are only the two points that serve
as the corner partners of `J` and `M`.  The line hypotheses are needed only for deep points beyond
the hypotenuse; weak is enough on both lines (the tilt pushes a deep point on `J J'` out of the
shadow, but the row of that point does not care); the only generic-position condition that remains
is that no deep point lies exactly over `J` or over `M` (those rows are degenerate at order `s⁰`).
The elevations `lambda, mu in (0, 90)` are implied: `x₁(J') > L`, `x₁(M') > 0`, `x₂(M') > H`, and
`hturn` gives `x₂(J') > 0`. -/
theorem overhung_corner_euclid {n : ℕ} (x : Fin n → ℝ³) (c J M jp mp : Fin n) (e f g : ℝ³)
    (he : x J - x c = e) (hf : x M - x c = f)
    (he0 : e ≠ 0) (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hef : ⟪e, f⟫ = 0) (heg : ⟪e, g⟫ = 0) (hfg : ⟪f, g⟫ = 0)
    (hD : ∀ i, i ≠ c → i ≠ J → i ≠ M → 0 < ⟪x i - x c, g⟫)
    (hQ : ∀ i, 0 ≤ ⟪x i - x c, e⟫ ∧ 0 ≤ ⟪x i - x c, f⟫)
    (hj1 : ⟪e, e⟫ < ⟪x jp - x c, e⟫) (hm1 : 0 < ⟪x mp - x c, e⟫)
    (hm2 : ⟪f, f⟫ < ⟪x mp - x c, f⟫)
    (hturn : (⟪x mp - x c, f⟫ - ⟪f, f⟫) * (⟪x jp - x c, e⟫ - ⟪e, e⟫) <
      ⟪x jp - x c, f⟫ * ⟪x mp - x c, e⟫)
    (hslope : ⟪x mp - x c, e⟫ < ⟪x mp - x c, f⟫ - ⟪f, f⟫ ∨
      ⟪x jp - x c, f⟫ < ⟪x jp - x c, e⟫ - ⟪e, e⟫)
    (hJline : ∀ i, i ≠ c → i ≠ J → i ≠ M →
      ⟪e, e⟫ * ⟪f, f⟫ ≤ ⟪f, f⟫ * ⟪x i - x c, e⟫ + ⟪e, e⟫ * ⟪x i - x c, f⟫ →
      0 ≤ (⟪x jp - x c, e⟫ - ⟪e, e⟫) * ⟪x i - x c, f⟫ -
        ⟪x jp - x c, f⟫ * (⟪x i - x c, e⟫ - ⟪e, e⟫) ∧
      ¬ (⟪x i - x c, e⟫ = ⟪e, e⟫ ∧ ⟪x i - x c, f⟫ = 0))
    (hMline : ∀ i, i ≠ c → i ≠ J → i ≠ M →
      ⟪e, e⟫ * ⟪f, f⟫ ≤ ⟪f, f⟫ * ⟪x i - x c, e⟫ + ⟪e, e⟫ * ⟪x i - x c, f⟫ →
      0 ≤ (⟪x mp - x c, f⟫ - ⟪f, f⟫) * ⟪x i - x c, e⟫ -
        ⟪x mp - x c, e⟫ * (⟪x i - x c, f⟫ - ⟪f, f⟫) ∧
      ¬ (⟪x i - x c, e⟫ = 0 ∧ ⟪x i - x c, f⟫ = ⟪f, f⟫)) :
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
  have hP : ∀ i, ⟪x i - x c, e⟫ = ‖e‖ * d i 1 := by
    intro i; simp only [hd, pt_one]; field_simp
  have hR : ∀ i, ⟪x i - x c, f⟫ = ‖f‖ * d i 2 := by
    intro i; simp only [hd, pt_two]; field_simp
  have hab : 0 < ‖e‖ * ‖f‖ := mul_pos hL hH
  have hcR : IsRupert (univ.image d) := by
    refine overhung_core_rupert d c J M jp mp ‖e‖ ‖f‖ hL hH ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
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
    · have := hj1
      rw [hP, hee] at this
      nlinarith
    · have := hm1
      rw [hP] at this
      exact (mul_pos_iff_of_pos_left hL).1 this
    · have := hm2
      rw [hR, hff] at this
      nlinarith
    · have := hturn
      rw [hP, hP, hR, hR, hee, hff] at this
      have h2 : ‖e‖ * ‖f‖ * ((d mp 2 - ‖f‖) * (d jp 1 - ‖e‖)) <
          ‖e‖ * ‖f‖ * (d jp 2 * d mp 1) := by nlinarith
      exact lt_of_mul_lt_mul_left h2 hab.le
    · have := hslope
      rw [hP, hR, hP, hR, hee, hff] at this
      rcases this with h | h
      · left; nlinarith
      · right; nlinarith
    · intro i h1 h2 h3 hB'
      have hB2 : ⟪e, e⟫ * ⟪f, f⟫ ≤ ⟪f, f⟫ * ⟪x i - x c, e⟫ + ⟪e, e⟫ * ⟪x i - x c, f⟫ := by
        rw [hP, hR, hee, hff]
        nlinarith [mul_le_mul_of_nonneg_left hB' hab.le]
      obtain ⟨k1, k2⟩ := hJline i h1 h2 h3 hB2
      refine ⟨?_, ?_⟩
      · rw [hP, hP, hR, hR, hee] at k1
        by_contra hneg
        push Not at hneg
        nlinarith [mul_neg_of_pos_of_neg hab hneg]
      · rintro ⟨q1, q2⟩
        refine k2 ⟨?_, ?_⟩
        · rw [hP, hee, q1]; ring
        · rw [hR, q2]; ring
    · intro i h1 h2 h3 hB'
      have hB2 : ⟪e, e⟫ * ⟪f, f⟫ ≤ ⟪f, f⟫ * ⟪x i - x c, e⟫ + ⟪e, e⟫ * ⟪x i - x c, f⟫ := by
        rw [hP, hR, hee, hff]
        nlinarith [mul_le_mul_of_nonneg_left hB' hab.le]
      obtain ⟨k1, k2⟩ := hMline i h1 h2 h3 hB2
      refine ⟨?_, ?_⟩
      · rw [hP, hP, hR, hR, hff] at k1
        by_contra hneg
        push Not at hneg
        nlinarith [mul_neg_of_pos_of_neg hab hneg]
      · rintro ⟨q1, q2⟩
        refine k2 ⟨?_, ?_⟩
        · rw [hP, q1]; ring
        · rw [hR, hff, q2]; ring
  apply isRupert_of_frame_image (univ.image x) (v := x c) hFr
  rw [Finset.image_image]
  convert hcR using 2
  funext i
  simp only [Function.comp_apply, orthoFrameMat_apply, hd, hA, hB, hC, real_inner_smul_right]

end Minimality.Split.Overhung
