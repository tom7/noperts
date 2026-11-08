module

public import Mathlib
public import Minimality.SplitRows
public import Minimality.Type08Rd

/-!
# Acute Edge Lemma

The statement in words, why it holds, and why its hypotheses are needed (the general acute-dihedral
statement is false: `ChipM18K5`) are in the docstring of `MinimalityExtra.AcuteEdgeLemma`, which is
proved from `ael_euclid` here. Paper proof: nopert229/out/bottleneck/acute/ael/PROOF.md. Uses
`FreeAt` from Minimality.SplitRows and the orthonormal frame of Minimality.Type08Rd.

## Contents

* `ael_core` (normal form, PROOF.md §2): `x a = 0`, `x b = (L, 0, 0)`, every other point has
  `0 < x₀ < L` (slab) and `x₁ > 0` (depth), every point has `x₂ ≤ 0` (the plane of `F` supports),
  some point has `x₂ < 0`.  Then for all small `s > 0` the view `U s = (s, 1, s³)` is free, with
  the motion `ω = (1, 0, s)`, `τ = (s² L / 2, 0, -s³)`; the row of a point other than `a`, `b` uses
  the angle `(b, p, a)`, the rows of `a` and `b` use a point `q` strictly below the plane of `F`.
  `ael_core_rupert`: hence `IsRupert`.
* `ael_core'`, `ael_core'_rupert` (PROOF.md §4): the same with `0 ≤ x₀` (points over `a` allowed),
  at the mirrored view `U' s = (-s, 1, s³)`, `ω' = (1, 0, -s)`, same `τ`.
* `ael_euclid` (PROOF.md §3): sign-fact form in any Euclidean position: supporting normals
  `nF`, `nF'` of two planes through `a`, `b` with `⟪nF, nF'⟫ < 0`, the slab T-signs (weak at `a`,
  strict at `b`), only `a`, `b` on both planes, a point strictly below `nF`'s plane ⇒ `IsRupert`.
  Reduction to `ael_core'` by an orthonormal frame (`isRupert_of_frame_image`).
  `ael_euclid_strict`: the lemma as stated (strict slab at both ends).
* `ael_cross`: `nF = σ (x b - x a) × (x f - x a)`, `nF' = σ' (x b - x a) × (x g - x a)`: facet
  structure as chirotope signs `det3`, (A) as one sign of a Gram expression.
-/

@[expose] public section

set_option autoImplicit false
open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality.Split.AcuteEdge
open Minimality.Split
open Minimality (pt pt_zero pt_one pt_two cross IsFrame orthoFrameMat orthoFrameMat_apply isRupert_of_frame_image)

/-! ### Small-parameter tools -/

theorem ev_pos {f : ℝ → ℝ} (hf : Continuous f) (h0 : 0 < f 0) :
    ∀ᶠ s in 𝓝[>] (0:ℝ), 0 < f s :=
  ((hf.tendsto 0).eventually (lt_mem_nhds h0)).filter_mono nhdsWithin_le_nhds

theorem ev_pos_sq {f g : ℝ → ℝ} (hg : Continuous g) (h0 : 0 < g 0) (hfg : ∀ s, f s = s ^ 2 * g s) :
    ∀ᶠ s in 𝓝[>] (0:ℝ), 0 < f s := by
  filter_upwards [ev_pos hg h0, self_mem_nhdsWithin] with s hs hs0
  rw [hfg]; exact mul_pos (pow_pos hs0 2) hs

/-! ### The certificate -/

/-- The view. -/
noncomputable def U (s : ℝ) : ℝ³ := pt s 1 (s ^ 3)
/-- The angular velocity: rotation about the edge line plus `s` times rotation about `n_F`. -/
noncomputable def Om (s : ℝ) : ℝ³ := pt 1 0 s
/-- The translation. -/
noncomputable def Tau (L s : ℝ) : ℝ³ := pt (s ^ 2 * L / 2) 0 (-(s ^ 3))

theorem U_ne (s : ℝ) : U s ≠ 0 := by
  intro h
  have := congrArg (fun v : ℝ³ => v 1) h
  simp [U] at this

/-- Row of a point `p` other than `a`, `b`: the angle `(b, p, a)`. -/
theorem row_mid (L : ℝ) (p : ℝ³) (hL : 0 < L) (hX0 : 0 < p 0) (hXL : p 0 < L) (hY : 0 < p 1)
    (hZ : p 2 ≤ 0) :
    ∀ᶠ s in 𝓝[>] (0:ℝ), 0 < det3 (pt 0 0 0 - p) (pt L 0 0 - p) (U s) ∧
      0 < det3 (pt 0 0 0 - p) (cross (Om s) p + Tau L s) (U s) ∧
      0 < det3 (p - pt L 0 0) (cross (Om s) p + Tau L s) (U s) := by
  have e1 : ∀ s, det3 (pt 0 0 0 - p) (pt L 0 0 - p) (U s) = L * (p 1 * s ^ 3 - p 2) := by
    intro s
    simp only [det3, U, PiLp.sub_apply, pt_zero, pt_one, pt_two]; ring
  have c2 : Continuous fun s => det3 (pt 0 0 0 - p) (cross (Om s) p + Tau L s) (U s) := by
    simp only [det3, U, Om, Tau, cross_0, cross_1, cross_2, PiLp.add_apply, PiLp.sub_apply,
      pt_zero, pt_one, pt_two]
    fun_prop
  have v2 : det3 (pt 0 0 0 - p) (cross (Om 0) p + Tau L 0) (U 0) = p 0 * p 1 := by
    simp only [det3, U, Om, Tau, cross_0, cross_1, cross_2, PiLp.add_apply, PiLp.sub_apply,
      pt_zero, pt_one, pt_two]; ring
  have c3 : Continuous fun s => det3 (p - pt L 0 0) (cross (Om s) p + Tau L s) (U s) := by
    simp only [det3, U, Om, Tau, cross_0, cross_1, cross_2, PiLp.add_apply, PiLp.sub_apply,
      pt_zero, pt_one, pt_two]
    fun_prop
  have v3 : det3 (p - pt L 0 0) (cross (Om 0) p + Tau L 0) (U 0) = (L - p 0) * p 1 := by
    simp only [det3, U, Om, Tau, cross_0, cross_1, cross_2, PiLp.add_apply, PiLp.sub_apply,
      pt_zero, pt_one, pt_two]; ring
  filter_upwards [self_mem_nhdsWithin, ev_pos c2 (by rw [v2]; positivity),
    ev_pos c3 (by rw [v3]; exact mul_pos (by linarith) hY)] with s hs h2 h3
  refine ⟨?_, h2, h3⟩
  rw [e1]
  have : 0 < p 1 * s ^ 3 := mul_pos hY (pow_pos (Set.mem_Ioi.1 hs) 3)
  exact mul_pos hL (by linarith)

/-- Row of `a = 0`: the angle `(q, a, b)`, `q` strictly below the plane `x₂ = 0`. -/
theorem row_a (L : ℝ) (q : ℝ³) (hL : 0 < L) (hq : q 2 < 0) :
    ∀ᶠ s in 𝓝[>] (0:ℝ), 0 < det3 (pt L 0 0 - pt 0 0 0) (q - pt 0 0 0) (U s) ∧
      0 < det3 (pt L 0 0 - pt 0 0 0) (cross (Om s) (pt 0 0 0) + Tau L s) (U s) ∧
      0 < det3 (pt 0 0 0 - q) (cross (Om s) (pt 0 0 0) + Tau L s) (U s) := by
  have c1 : Continuous fun s => det3 (pt L 0 0 - pt 0 0 0) (q - pt 0 0 0) (U s) := by
    simp only [det3, U, PiLp.sub_apply, pt_zero, pt_one, pt_two]; fun_prop
  have v1 : det3 (pt L 0 0 - pt 0 0 0) (q - pt 0 0 0) (U 0) = L * (-q 2) := by
    simp only [det3, U, PiLp.sub_apply, pt_zero, pt_one, pt_two]; ring
  have e2 : ∀ s, det3 (pt L 0 0 - pt 0 0 0) (cross (Om s) (pt 0 0 0) + Tau L s) (U s) =
      L * s ^ 3 := by
    intro s
    simp only [det3, U, Om, Tau, cross_0, cross_1, cross_2, PiLp.add_apply, PiLp.sub_apply,
      pt_zero, pt_one, pt_two]; ring
  have e3 : ∀ s, det3 (pt 0 0 0 - q) (cross (Om s) (pt 0 0 0) + Tau L s) (U s) =
      s ^ 2 * (-(q 2) * L / 2 - q 0 * s + q 1 * s ^ 2 + q 1 * L * s ^ 3 / 2) := by
    intro s
    simp only [det3, U, Om, Tau, cross_0, cross_1, cross_2, PiLp.add_apply, PiLp.sub_apply,
      pt_zero, pt_one, pt_two]; ring
  filter_upwards [self_mem_nhdsWithin, ev_pos c1 (by rw [v1]; exact mul_pos hL (by linarith)),
    ev_pos_sq (f := fun s => det3 (pt 0 0 0 - q) (cross (Om s) (pt 0 0 0) + Tau L s) (U s))
      (g := fun s => -(q 2) * L / 2 - q 0 * s + q 1 * s ^ 2 + q 1 * L * s ^ 3 / 2)
      (by fun_prop) (by simp; nlinarith) e3] with s hs h1 h3
  exact ⟨h1, by rw [e2]; exact mul_pos hL (pow_pos (Set.mem_Ioi.1 hs) 3), h3⟩

/-- Row of `b = (L, 0, 0)`: the angle `(a, b, q)`. -/
theorem row_b (L : ℝ) (q : ℝ³) (hL : 0 < L) (hq : q 2 < 0) :
    ∀ᶠ s in 𝓝[>] (0:ℝ), 0 < det3 (q - pt L 0 0) (pt 0 0 0 - pt L 0 0) (U s) ∧
      0 < det3 (q - pt L 0 0) (cross (Om s) (pt L 0 0) + Tau L s) (U s) ∧
      0 < det3 (pt L 0 0 - pt 0 0 0) (cross (Om s) (pt L 0 0) + Tau L s) (U s) := by
  have c1 : Continuous fun s => det3 (q - pt L 0 0) (pt 0 0 0 - pt L 0 0) (U s) := by
    simp only [det3, U, PiLp.sub_apply, pt_zero, pt_one, pt_two]; fun_prop
  have v1 : det3 (q - pt L 0 0) (pt 0 0 0 - pt L 0 0) (U 0) = L * (-q 2) := by
    simp only [det3, U, PiLp.sub_apply, pt_zero, pt_one, pt_two]; ring
  have e2 : ∀ s, det3 (q - pt L 0 0) (cross (Om s) (pt L 0 0) + Tau L s) (U s) =
      s ^ 2 * (-(q 2) * L / 2 + (q 0 - L) * s + (-(q 1) + (q 0 - L) * L) * s ^ 2 -
        q 1 * L * s ^ 3 / 2) := by
    intro s
    simp only [det3, U, Om, Tau, cross_0, cross_1, cross_2, PiLp.add_apply, PiLp.sub_apply,
      pt_zero, pt_one, pt_two]; ring
  have e3 : ∀ s, det3 (pt L 0 0 - pt 0 0 0) (cross (Om s) (pt L 0 0) + Tau L s) (U s) =
      L * s ^ 3 * (1 + L * s) := by
    intro s
    simp only [det3, U, Om, Tau, cross_0, cross_1, cross_2, PiLp.add_apply, PiLp.sub_apply,
      pt_zero, pt_one, pt_two]; ring
  filter_upwards [self_mem_nhdsWithin, ev_pos c1 (by rw [v1]; exact mul_pos hL (by linarith)),
    ev_pos_sq (f := fun s => det3 (q - pt L 0 0) (cross (Om s) (pt L 0 0) + Tau L s) (U s))
      (g := fun s => -(q 2) * L / 2 + (q 0 - L) * s + (-(q 1) + (q 0 - L) * L) * s ^ 2 -
        q 1 * L * s ^ 3 / 2)
      (by fun_prop) (by simp; nlinarith) e2] with s hs h1 h2
  have hs0 : 0 < s := Set.mem_Ioi.1 hs
  exact ⟨h1, h2, by rw [e3]; positivity⟩

/-- **Acute Edge Lemma, normal form.** -/
theorem ael_core {n : ℕ} (x : Fin n → ℝ³) (a b : Fin n) (L : ℝ) (hL : 0 < L)
    (ha : x a = pt 0 0 0) (hb : x b = pt L 0 0)
    (hS : ∀ i, i ≠ a → i ≠ b → 0 < x i 0 ∧ x i 0 < L)
    (hD : ∀ i, i ≠ a → i ≠ b → 0 < x i 1)
    (hF : ∀ i, x i 2 ≤ 0) (hq : ∃ q, x q 2 < 0) :
    ∀ᶠ s in 𝓝[>] (0:ℝ), FreeAt (univ.image x) (U s) := by
  classical
  obtain ⟨q, hq⟩ := hq
  have mem : ∀ j, x j ∈ univ.image x := fun j => mem_image_of_mem x (mem_univ j)
  have hrow : ∀ i, ∀ᶠ s in 𝓝[>] (0:ℝ),
      TiltCert (univ.image x) (U s) (Om s) (Tau L s) (x i) := by
    intro i
    by_cases hia : i = a
    · subst hia
      filter_upwards [row_a L (x q) hL hq] with s h
      left
      refine ⟨x q, mem q, x b, mem b, ?_⟩
      rw [ha, hb]; exact h
    by_cases hib : i = b
    · subst hib
      filter_upwards [row_b L (x q) hL hq] with s h
      left
      refine ⟨x a, mem a, x q, mem q, ?_⟩
      rw [ha, hb]; exact h
    filter_upwards [row_mid L (x i) hL (hS i hia hib).1 (hS i hia hib).2 (hD i hia hib) (hF i)]
      with s h
    left
    refine ⟨x b, mem b, x a, mem a, ?_⟩
    rw [ha, hb]; exact h
  filter_upwards [Filter.eventually_all.2 hrow] with s hs
  refine ⟨Om s, Tau L s, fun y hy => ?_⟩
  obtain ⟨i, -, rfl⟩ := mem_image.1 hy
  exact hs i

theorem ael_core_rupert {n : ℕ} (x : Fin n → ℝ³) (a b : Fin n) (L : ℝ) (hL : 0 < L)
    (ha : x a = pt 0 0 0) (hb : x b = pt L 0 0)
    (hS : ∀ i, i ≠ a → i ≠ b → 0 < x i 0 ∧ x i 0 < L)
    (hD : ∀ i, i ≠ a → i ≠ b → 0 < x i 1)
    (hF : ∀ i, x i 2 ≤ 0) (hq : ∃ q, x q 2 < 0) :
    IsRupert (univ.image x) := by
  obtain ⟨s, hs⟩ := (ael_core x a b L hL ha hb hS hD hF hq).exists
  exact FreeAt.isRupert (U_ne s) hs


/-! ### One-sided equality in (S): points over `a` (PROOF.md §4)

The mirrored family `U' s = (-s, 1, s³)`, `ω' = (1, 0, -s)`, the same `τ`, allows `x₀ = 0`. -/

noncomputable def U' (s : ℝ) : ℝ³ := pt (-s) 1 (s ^ 3)
noncomputable def Om' (s : ℝ) : ℝ³ := pt 1 0 (-s)

theorem U'_ne (s : ℝ) : U' s ≠ 0 := by
  intro h
  have := congrArg (fun v : ℝ³ => v 1) h
  simp [U'] at this

theorem ev_pos_lin {f g : ℝ → ℝ} (hg : Continuous g) (h0 : 0 < g 0) (hfg : ∀ s, f s = s * g s) :
    ∀ᶠ s in 𝓝[>] (0:ℝ), 0 < f s := by
  filter_upwards [ev_pos hg h0, self_mem_nhdsWithin] with s hs hs0
  rw [hfg]; exact mul_pos hs0 hs

theorem row_mid' (L : ℝ) (p : ℝ³) (hL : 0 < L) (hX0 : 0 ≤ p 0) (hXL : p 0 < L) (hY : 0 < p 1)
    (hZ : p 2 ≤ 0) :
    ∀ᶠ s in 𝓝[>] (0:ℝ), 0 < det3 (pt 0 0 0 - p) (pt L 0 0 - p) (U' s) ∧
      0 < det3 (pt 0 0 0 - p) (cross (Om' s) p + Tau L s) (U' s) ∧
      0 < det3 (p - pt L 0 0) (cross (Om' s) p + Tau L s) (U' s) := by
  have e1 : ∀ s, det3 (pt 0 0 0 - p) (pt L 0 0 - p) (U' s) = L * (p 1 * s ^ 3 - p 2) := by
    intro s
    simp only [det3, U', PiLp.sub_apply, pt_zero, pt_one, pt_two]; ring
  have c2 : Continuous fun s => det3 (pt 0 0 0 - p) (cross (Om' s) p + Tau L s) (U' s) := by
    simp only [det3, U', Om', Tau, cross_0, cross_1, cross_2, PiLp.add_apply, PiLp.sub_apply,
      pt_zero, pt_one, pt_two]
    fun_prop
  have v2 : det3 (pt 0 0 0 - p) (cross (Om' 0) p + Tau L 0) (U' 0) = p 0 * p 1 := by
    simp only [det3, U', Om', Tau, cross_0, cross_1, cross_2, PiLp.add_apply, PiLp.sub_apply,
      pt_zero, pt_one, pt_two]; ring
  have c3 : Continuous fun s => det3 (p - pt L 0 0) (cross (Om' s) p + Tau L s) (U' s) := by
    simp only [det3, U', Om', Tau, cross_0, cross_1, cross_2, PiLp.add_apply, PiLp.sub_apply,
      pt_zero, pt_one, pt_two]
    fun_prop
  have v3 : det3 (p - pt L 0 0) (cross (Om' 0) p + Tau L 0) (U' 0) = (L - p 0) * p 1 := by
    simp only [det3, U', Om', Tau, cross_0, cross_1, cross_2, PiLp.add_apply, PiLp.sub_apply,
      pt_zero, pt_one, pt_two]; ring
  have h2 : ∀ᶠ s in 𝓝[>] (0:ℝ), 0 < det3 (pt 0 0 0 - p) (cross (Om' s) p + Tau L s) (U' s) := by
    rcases hX0.lt_or_eq with hX | hX
    · exact ev_pos c2 (by rw [v2]; positivity)
    · refine ev_pos_lin (g := fun s => p 1 ^ 2 + p 2 ^ 2 - p 1 * p 2 - p 1 * s ^ 3 -
        s * p 2 * L / 2 + s ^ 3 * p 1 ^ 2 + s ^ 4 * p 1 * L / 2) (by fun_prop)
        (by simp only; nlinarith) (fun s => ?_)
      simp only [det3, U', Om', Tau, cross_0, cross_1, cross_2, PiLp.add_apply, PiLp.sub_apply,
        pt_zero, pt_one, pt_two, ← hX]; ring
  filter_upwards [self_mem_nhdsWithin, h2,
    ev_pos c3 (by rw [v3]; exact mul_pos (by linarith) hY)] with s hs h2 h3
  refine ⟨?_, h2, h3⟩
  rw [e1]
  have : 0 < p 1 * s ^ 3 := mul_pos hY (pow_pos (Set.mem_Ioi.1 hs) 3)
  exact mul_pos hL (by linarith)

theorem row_a' (L : ℝ) (q : ℝ³) (hL : 0 < L) (hq : q 2 < 0) :
    ∀ᶠ s in 𝓝[>] (0:ℝ), 0 < det3 (pt L 0 0 - pt 0 0 0) (q - pt 0 0 0) (U' s) ∧
      0 < det3 (pt L 0 0 - pt 0 0 0) (cross (Om' s) (pt 0 0 0) + Tau L s) (U' s) ∧
      0 < det3 (pt 0 0 0 - q) (cross (Om' s) (pt 0 0 0) + Tau L s) (U' s) := by
  have c1 : Continuous fun s => det3 (pt L 0 0 - pt 0 0 0) (q - pt 0 0 0) (U' s) := by
    simp only [det3, U', PiLp.sub_apply, pt_zero, pt_one, pt_two]; fun_prop
  have v1 : det3 (pt L 0 0 - pt 0 0 0) (q - pt 0 0 0) (U' 0) = L * (-q 2) := by
    simp only [det3, U', PiLp.sub_apply, pt_zero, pt_one, pt_two]; ring
  have e2 : ∀ s, det3 (pt L 0 0 - pt 0 0 0) (cross (Om' s) (pt 0 0 0) + Tau L s) (U' s) =
      L * s ^ 3 := by
    intro s
    simp only [det3, U', Om', Tau, cross_0, cross_1, cross_2, PiLp.add_apply, PiLp.sub_apply,
      pt_zero, pt_one, pt_two]; ring
  have e3 : ∀ s, det3 (pt 0 0 0 - q) (cross (Om' s) (pt 0 0 0) + Tau L s) (U' s) =
      s ^ 2 * (-(q 2) * L / 2 - q 0 * s - q 1 * s ^ 2 + q 1 * L * s ^ 3 / 2) := by
    intro s
    simp only [det3, U', Om', Tau, cross_0, cross_1, cross_2, PiLp.add_apply, PiLp.sub_apply,
      pt_zero, pt_one, pt_two]; ring
  filter_upwards [self_mem_nhdsWithin, ev_pos c1 (by rw [v1]; exact mul_pos hL (by linarith)),
    ev_pos_sq (f := fun s => det3 (pt 0 0 0 - q) (cross (Om' s) (pt 0 0 0) + Tau L s) (U' s))
      (g := fun s => -(q 2) * L / 2 - q 0 * s - q 1 * s ^ 2 + q 1 * L * s ^ 3 / 2)
      (by fun_prop) (by simp; nlinarith) e3] with s hs h1 h3
  exact ⟨h1, by rw [e2]; exact mul_pos hL (pow_pos (Set.mem_Ioi.1 hs) 3), h3⟩

theorem row_b' (L : ℝ) (q : ℝ³) (hL : 0 < L) (hq : q 2 < 0) :
    ∀ᶠ s in 𝓝[>] (0:ℝ), 0 < det3 (q - pt L 0 0) (pt 0 0 0 - pt L 0 0) (U' s) ∧
      0 < det3 (q - pt L 0 0) (cross (Om' s) (pt L 0 0) + Tau L s) (U' s) ∧
      0 < det3 (pt L 0 0 - pt 0 0 0) (cross (Om' s) (pt L 0 0) + Tau L s) (U' s) := by
  have c1 : Continuous fun s => det3 (q - pt L 0 0) (pt 0 0 0 - pt L 0 0) (U' s) := by
    simp only [det3, U', PiLp.sub_apply, pt_zero, pt_one, pt_two]; fun_prop
  have v1 : det3 (q - pt L 0 0) (pt 0 0 0 - pt L 0 0) (U' 0) = L * (-q 2) := by
    simp only [det3, U', PiLp.sub_apply, pt_zero, pt_one, pt_two]; ring
  have e2 : ∀ s, det3 (q - pt L 0 0) (cross (Om' s) (pt L 0 0) + Tau L s) (U' s) =
      s ^ 2 * (-(q 2) * L / 2 + (q 0 - L) * s + (q 1 - (q 0 - L) * L) * s ^ 2 -
        q 1 * L * s ^ 3 / 2) := by
    intro s
    simp only [det3, U', Om', Tau, cross_0, cross_1, cross_2, PiLp.add_apply, PiLp.sub_apply,
      pt_zero, pt_one, pt_two]; ring
  have e3 : ∀ s, det3 (pt L 0 0 - pt 0 0 0) (cross (Om' s) (pt L 0 0) + Tau L s) (U' s) =
      L * s ^ 3 * (1 - L * s) := by
    intro s
    simp only [det3, U', Om', Tau, cross_0, cross_1, cross_2, PiLp.add_apply, PiLp.sub_apply,
      pt_zero, pt_one, pt_two]; ring
  filter_upwards [self_mem_nhdsWithin, ev_pos c1 (by rw [v1]; exact mul_pos hL (by linarith)),
    ev_pos_sq (f := fun s => det3 (q - pt L 0 0) (cross (Om' s) (pt L 0 0) + Tau L s) (U' s))
      (g := fun s => -(q 2) * L / 2 + (q 0 - L) * s + (q 1 - (q 0 - L) * L) * s ^ 2 -
        q 1 * L * s ^ 3 / 2)
      (by fun_prop) (by simp; nlinarith) e2,
    ev_pos (f := fun s => 1 - L * s) (by fun_prop) (by simp)] with s hs h1 h2 h4
  have hs0 : 0 < s := Set.mem_Ioi.1 hs
  exact ⟨h1, h2, by rw [e3]; exact mul_pos (by positivity) h4⟩

/-- **Acute Edge Lemma, normal form with one-sided equality** (points may lie over `a`). -/
theorem ael_core' {n : ℕ} (x : Fin n → ℝ³) (a b : Fin n) (L : ℝ) (hL : 0 < L)
    (ha : x a = pt 0 0 0) (hb : x b = pt L 0 0)
    (hS : ∀ i, i ≠ a → i ≠ b → 0 ≤ x i 0 ∧ x i 0 < L)
    (hD : ∀ i, i ≠ a → i ≠ b → 0 < x i 1)
    (hF : ∀ i, x i 2 ≤ 0) (hq : ∃ q, x q 2 < 0) :
    ∀ᶠ s in 𝓝[>] (0:ℝ), FreeAt (univ.image x) (U' s) := by
  classical
  obtain ⟨q, hq⟩ := hq
  have mem : ∀ j, x j ∈ univ.image x := fun j => mem_image_of_mem x (mem_univ j)
  have hrow : ∀ i, ∀ᶠ s in 𝓝[>] (0:ℝ),
      TiltCert (univ.image x) (U' s) (Om' s) (Tau L s) (x i) := by
    intro i
    by_cases hia : i = a
    · subst hia
      filter_upwards [row_a' L (x q) hL hq] with s h
      left
      refine ⟨x q, mem q, x b, mem b, ?_⟩
      rw [ha, hb]; exact h
    by_cases hib : i = b
    · subst hib
      filter_upwards [row_b' L (x q) hL hq] with s h
      left
      refine ⟨x a, mem a, x q, mem q, ?_⟩
      rw [ha, hb]; exact h
    filter_upwards [row_mid' L (x i) hL (hS i hia hib).1 (hS i hia hib).2 (hD i hia hib) (hF i)]
      with s h
    left
    refine ⟨x b, mem b, x a, mem a, ?_⟩
    rw [ha, hb]; exact h
  filter_upwards [Filter.eventually_all.2 hrow] with s hs
  refine ⟨Om' s, Tau L s, fun y hy => ?_⟩
  obtain ⟨i, -, rfl⟩ := mem_image.1 hy
  exact hs i

theorem ael_core'_rupert {n : ℕ} (x : Fin n → ℝ³) (a b : Fin n) (L : ℝ) (hL : 0 < L)
    (ha : x a = pt 0 0 0) (hb : x b = pt L 0 0)
    (hS : ∀ i, i ≠ a → i ≠ b → 0 ≤ x i 0 ∧ x i 0 < L)
    (hD : ∀ i, i ≠ a → i ≠ b → 0 < x i 1)
    (hF : ∀ i, x i 2 ≤ 0) (hq : ∃ q, x q 2 < 0) :
    IsRupert (univ.image x) := by
  obtain ⟨s, hs⟩ := (ael_core' x a b L hL ha hb hS hD hF hq).exists
  exact FreeAt.isRupert (U'_ne s) hs

/-! ### Any Euclidean position: sign facts -/

theorem frame_unit {v : ℝ³} (hv : v ≠ 0) : ⟪‖v‖⁻¹ • v, ‖v‖⁻¹ • v⟫ = 1 := by
  rw [real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq]
  have : ‖v‖ ≠ 0 := norm_ne_zero_iff.2 hv
  field_simp

/-- **Acute Edge Lemma, sign-fact form.**  `nF`, `nF'`: normals of two planes through `x a`, `x b`
supporting the points (`⟪nF, x i - x a⟫ ≤ 0`); (A) `⟪nF, nF'⟫ < 0`; (S) the slab T-signs, strict at
`b`, weak at `a` (one-sided equality allowed, PROOF.md §4); only `a`, `b` lie on both planes; some
point lies strictly below the first plane.  The strict (S) of the lemma is the special case
`ael_euclid_strict`. -/
theorem ael_euclid {n : ℕ} (x : Fin n → ℝ³) (a b : Fin n) (nF nF' : ℝ³)
    (hF : ∀ i, ⟪nF, x i - x a⟫ ≤ 0) (hFb : ⟪nF, x b - x a⟫ = 0)
    (hF' : ∀ i, ⟪nF', x i - x a⟫ ≤ 0) (hF'b : ⟪nF', x b - x a⟫ = 0)
    (hA : ⟪nF, nF'⟫ < 0) (hq : ∃ q, ⟪nF, x q - x a⟫ < 0)
    (hSa : ∀ i, i ≠ a → i ≠ b → 0 ≤ ⟪x i - x a, x b - x a⟫)
    (hSb : ∀ i, i ≠ a → i ≠ b → 0 < ⟪x i - x b, x a - x b⟫)
    (hE : ∀ i, i ≠ a → i ≠ b → ⟪nF, x i - x a⟫ < 0 ∨ ⟪nF', x i - x a⟫ < 0) :
    IsRupert (univ.image x) := by
  classical
  obtain ⟨q, hq⟩ := hq
  set e := x b - x a with he_def
  set W : ℝ³ := ⟪nF, nF⟫ • (-nF') + ⟪nF', nF⟫ • nF with hW_def
  have hqa : q ≠ a := by rintro rfl; simp at hq
  have hqb : q ≠ b := by rintro rfl; rw [hFb] at hq; exact lt_irrefl _ hq
  have hnF : nF ≠ 0 := by rintro rfl; simp at hA
  have hnn : 0 < ⟪nF, nF⟫ := real_inner_self_pos.2 hnF
  have he0 : e ≠ 0 := by
    intro h0; have := hSb q hqa hqb
    have h' : x a - x b = -e := by rw [he_def]; abel
    rw [h', h0, neg_zero, inner_zero_right] at this
    exact lt_irrefl _ this
  -- depth along W
  have hdepth : ∀ i, ⟪x i - x a, W⟫ =
      ⟪nF, nF⟫ * (-⟪nF', x i - x a⟫) + (-⟪nF', nF⟫) * (-⟪nF, x i - x a⟫) := by
    intro i
    rw [hW_def, inner_add_right, real_inner_smul_right, real_inner_smul_right, inner_neg_right,
      real_inner_comm nF' (x i - x a), real_inner_comm nF (x i - x a)]; ring
  have hcomm : ⟪nF', nF⟫ = ⟪nF, nF'⟫ := real_inner_comm _ _
  have hpos : ∀ i, i ≠ a → i ≠ b → 0 < ⟪x i - x a, W⟫ := by
    intro i hia hib
    rw [hdepth, hcomm]
    have h1 := hF i; have h2 := hF' i
    rcases hE i hia hib with h | h
    · have : 0 < (-⟪nF, nF'⟫) * (-⟪nF, x i - x a⟫) := mul_pos (by linarith) (by linarith)
      nlinarith
    · have : 0 < ⟪nF, nF⟫ * (-⟪nF', x i - x a⟫) := mul_pos hnn (by linarith)
      nlinarith
  have hW0 : W ≠ 0 := by
    intro h0; have := hpos q hqa hqb; rw [h0, inner_zero_right] at this; exact lt_irrefl _ this
  -- orthogonality
  have heW : ⟪e, W⟫ = 0 := by
    have := hdepth b; simp only [← he_def] at this; rw [this, hFb, hF'b]; ring
  have hen : ⟪e, nF⟫ = 0 := by rw [real_inner_comm]; exact hFb
  have hWn : ⟪W, nF⟫ = 0 := by
    rw [hW_def, inner_add_left, real_inner_smul_left, real_inner_smul_left, inner_neg_left]; ring
  set S : ℝ³ := ‖e‖⁻¹ • e with hS_def
  set T : ℝ³ := ‖W‖⁻¹ • W with hT_def
  set N : ℝ³ := ‖nF‖⁻¹ • nF with hN_def
  have hFr : IsFrame S T N := by
    refine ⟨frame_unit he0, frame_unit hW0, frame_unit hnF, ?_, ?_, ?_⟩
    · rw [hS_def, hT_def, real_inner_smul_left, real_inner_smul_right, heW]; ring
    · rw [hS_def, hN_def, real_inner_smul_left, real_inner_smul_right, hen]; ring
    · rw [hT_def, hN_def, real_inner_smul_left, real_inner_smul_right, hWn]; ring
  set c : Fin n → ℝ³ := fun i => pt ⟪x i - x a, S⟫ ⟪x i - x a, T⟫ ⟪x i - x a, N⟫ with hc_def
  have hne : 0 < ‖e‖ := norm_pos_iff.2 he0
  have hnW : 0 < ‖W‖ := norm_pos_iff.2 hW0
  have hnN : 0 < ‖nF‖ := norm_pos_iff.2 hnF
  have hee : ⟪e, e⟫ = ‖e‖ ^ 2 := real_inner_self_eq_norm_sq e
  have hcR : IsRupert (univ.image c) := by
    refine ael_core'_rupert c a b ‖e‖ hne ?_ ?_ ?_ ?_ ?_ ⟨q, ?_⟩
    · simp [hc_def]
    · simp only [hc_def, ← he_def, hS_def, hT_def, hN_def, real_inner_smul_right, heW, hen, hee]
      congr 1 <;> field_simp <;> ring
    · intro i hia hib
      simp only [hc_def, pt_zero, hS_def, real_inner_smul_right]
      have h1 := hSa i hia hib
      have h2 := hSb i hia hib
      have h3 : ⟪x i - x b, x a - x b⟫ = ⟪e, e⟫ - ⟪x i - x a, e⟫ := by
        have : x i - x b = (x i - x a) - e := by rw [he_def]; abel
        have h' : x a - x b = -e := by rw [he_def]; abel
        rw [this, h', inner_neg_right, inner_sub_left, real_inner_comm e (x i - x a)]; ring
      rw [h3, hee] at h2
      constructor
      · exact mul_nonneg (inv_nonneg.2 hne.le) h1
      · rw [inv_mul_lt_iff₀ hne]; nlinarith
    · intro i hia hib
      simp only [hc_def, pt_one, hT_def, real_inner_smul_right]
      exact mul_pos (inv_pos.2 hnW) (hpos i hia hib)
    · intro i
      simp only [hc_def, pt_two, hN_def, real_inner_smul_right, real_inner_comm nF]
      exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.2 hnN.le) (hF i)
    · simp only [hc_def, pt_two, hN_def, real_inner_smul_right]
      exact mul_neg_of_pos_of_neg (inv_pos.2 hnN) (by rwa [real_inner_comm] at hq)
  apply isRupert_of_frame_image (univ.image x) (v := x a) hFr
  rw [Finset.image_image]
  convert hcR using 2
  funext i
  simp only [Function.comp_apply, orthoFrameMat_apply, hc_def]

/-- The Acute Edge Lemma as stated (strict slab at both ends). -/
theorem ael_euclid_strict {n : ℕ} (x : Fin n → ℝ³) (a b : Fin n) (nF nF' : ℝ³)
    (hF : ∀ i, ⟪nF, x i - x a⟫ ≤ 0) (hFb : ⟪nF, x b - x a⟫ = 0)
    (hF' : ∀ i, ⟪nF', x i - x a⟫ ≤ 0) (hF'b : ⟪nF', x b - x a⟫ = 0)
    (hA : ⟪nF, nF'⟫ < 0) (hq : ∃ q, ⟪nF, x q - x a⟫ < 0)
    (hSa : ∀ i, i ≠ a → i ≠ b → 0 < ⟪x i - x a, x b - x a⟫)
    (hSb : ∀ i, i ≠ a → i ≠ b → 0 < ⟪x i - x b, x a - x b⟫)
    (hE : ∀ i, i ≠ a → i ≠ b → ⟪nF, x i - x a⟫ < 0 ∨ ⟪nF', x i - x a⟫ < 0) :
    IsRupert (univ.image x) :=
  ael_euclid x a b nF nF' hF hFb hF' hF'b hA hq (fun i h1 h2 => (hSa i h1 h2).le) hSb hE

/-- **Acute Edge Lemma, chirotope form.**  The facet planes through `a, b, f` and `a, b, g`, with
orientation signs `σ`, `σ'`: (facet) `σ det3(x b - x a, x f - x a, x i - x a) ≤ 0` for all `i`, and
the same for `g`, `σ'`; (A) `σ σ' ⟪(x b - x a) × (x f - x a), (x b - x a) × (x g - x a)⟫ < 0`; (S) the
slab T-signs (weak at `a`); only `a`, `b` on both planes; a point strictly off the first plane. -/
theorem ael_cross {n : ℕ} (x : Fin n → ℝ³) (a b f g : Fin n) (σ σ' : ℝ)
    (hF : ∀ i, σ * det3 (x b - x a) (x f - x a) (x i - x a) ≤ 0)
    (hF' : ∀ i, σ' * det3 (x b - x a) (x g - x a) (x i - x a) ≤ 0)
    (hA : σ * σ' * ⟪cross (x b - x a) (x f - x a), cross (x b - x a) (x g - x a)⟫ < 0)
    (hq : ∃ q, σ * det3 (x b - x a) (x f - x a) (x q - x a) < 0)
    (hSa : ∀ i, i ≠ a → i ≠ b → 0 ≤ ⟪x i - x a, x b - x a⟫)
    (hSb : ∀ i, i ≠ a → i ≠ b → 0 < ⟪x i - x b, x a - x b⟫)
    (hE : ∀ i, i ≠ a → i ≠ b → σ * det3 (x b - x a) (x f - x a) (x i - x a) < 0 ∨
      σ' * det3 (x b - x a) (x g - x a) (x i - x a) < 0) :
    IsRupert (univ.image x) := by
  have key : ∀ (t : ℝ) (p r v : ℝ³), ⟪t • cross p r, v⟫ = t * det3 p r v := by
    intro t p r v; rw [real_inner_smul_left, inner3]; simp only [det3, cross_0, cross_1, cross_2]
  refine ael_euclid x a b (σ • cross (x b - x a) (x f - x a)) (σ' • cross (x b - x a) (x g - x a))
    (fun i => by rw [key]; exact hF i) ?_ (fun i => by rw [key]; exact hF' i) ?_ ?_ ?_ hSa hSb
    (fun i hia hib => by rw [key, key]; exact hE i hia hib)
  · rw [real_inner_smul_left, Minimality.inner_cross_left, mul_zero]
  · rw [real_inner_smul_left, Minimality.inner_cross_left, mul_zero]
  · rw [real_inner_smul_left, real_inner_smul_right, ← mul_assoc, mul_comm σ σ']
    linarith [hA, show σ * σ' = σ' * σ from mul_comm _ _]
  · obtain ⟨q, hq⟩ := hq; exact ⟨q, by rw [key]; exact hq⟩

end Minimality.Split.AcuteEdge

end
