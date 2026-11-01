module

public import Minimality.Type08S.C2K5LA
public import Minimality.Type08S.P2TpSetup
public import Minimality.Type08S.C2K2C

@[expose] public section


/-!
# K5L / B: K5-0 W0 (weak frame, both ties) and W1 (planarity as coordinate equations)

* `norm08w_coords`: `Norm08w` gives the frame `c' = d + α1 p + β1 q`, `b' = d + α4 p + γ4 r`, `a' = d + β6 q + γ6 r`
  (`p = a - d, q = b - d, r = c - d`) with the weak positivity (`Qac_coords'`), and the two far-end implications:
  `F.abc'.f c < F.abc'.f a' → γ6 < 1`, `F.a'bc.f a > F.a'bc.f c' → 1 < α1` (the T4 region).
* `norm08w_coordsT`: with `IsT a' b c d`: `γ6 = 1`.  `norm08w_coordsTp`: with `IsT' a b c' d`: `α1 = 1`.
* `gale_pt` : Gale κ_a, κ_b in the coordinates.
* W1: `planar_a_iff`, `planar_c_iff`, `planar_b_iff` (point-form `det3 = 0` ⇔ coordinate equation).
-/
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

theorem norm08w_coords {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) :
    ∃ α1 α4 β1 γ4 β6 γ6 : ℝ, det3 (a - d) (b - d) (c - d) ≠ 0 ∧
      c' = d + α1 • (a - d) + β1 • (b - d) ∧ b' = d + α4 • (a - d) + γ4 • (c - d) ∧
      a' = d + β6 • (b - d) + γ6 • (c - d) ∧
      0 < α1 ∧ 0 < β1 ∧ 1 < α1 + β1 ∧ 0 < α4 ∧ 0 < γ4 ∧ 1 < α4 + γ4 ∧ 0 < β6 ∧ 0 < γ6 ∧ 1 < β6 + γ6 ∧
      (W.F.abc'.f c < W.F.abc'.f a' → γ6 < 1) ∧ (W.F.a'bc.f c' < W.F.a'bc.f a → 1 < α1) := by
  obtain ⟨F, hd, G, hκa, hκb, hU⟩ := W
  have hnd := F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨haa', hab, hab', hac, hac'⟩, ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩,
    ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd
  obtain ⟨p1, p2, p3, hc'⟩ : 0 < F.a'bc.f c' / F.a'bc.f a ∧ 0 < F.ab'c.f c' / F.ab'c.f b ∧
      1 < F.a'bc.f c' / F.a'bc.f a + F.ab'c.f c' / F.ab'c.f b ∧
      c' = d + (F.a'bc.f c' / F.a'bc.f a) • (a - d) + (F.ab'c.f c' / F.ab'c.f b) • (b - d) :=
    hd.perm₂₃.Qac_coords'
  obtain ⟨q1, q2, q3, hb'⟩ := hd.Qac_coords'
  obtain ⟨hβ6, hγ6, hcv6, ha'⟩ : 0 < F.ab'c.f a' / F.ab'c.f b ∧ 0 < F.abc'.f a' / F.abc'.f c ∧
      1 < F.ab'c.f a' / F.ab'c.f b + F.abc'.f a' / F.abc'.f c ∧
      a' = d + (F.ab'c.f a' / F.ab'c.f b) • (b - d) + (F.abc'.f a' / F.abc'.f c) • (c - d) :=
    hd.perm₁₂.Qac_coords'
  have hFc := F.abc'.neg c (by simp) (Ne.symm hac) (Ne.symm hbc) hcc'
  have hFa := F.a'bc.neg a (by simp) haa' hab hac
  have hdet : det3 (a - d) (b - d) (c - d) ≠ 0 := by
    have := hd.det_Qac_ne
    intro h; apply this
    have e : det3 (a - d) (c - d) (b - d) = - det3 (a - d) (b - d) (c - d) := by
      simp only [det3_expand]; ring
    rw [e, h, neg_zero]
  refine ⟨_, _, _, _, _, _, hdet, hc', hb', ha', p1, p2, p3, q1, q2, q3, hβ6, hγ6, hcv6, ?_, ?_⟩
  · intro h; exact (div_lt_one_of_neg hFc).mpr h
  · intro h; rw [lt_div_iff_of_neg hFa]; linarith

theorem det3_indep {a b c d : ℝ³} (hdet : det3 (a - d) (b - d) (c - d) ≠ 0) {s t u : ℝ}
    (h : s • (a - d) + t • (b - d) + u • (c - d) = 0) : s = 0 ∧ t = 0 ∧ u = 0 := by
  have hs : s * det3 (a - d) (b - d) (c - d) = 0 := by
    have := congrArg (fun v => det3 v (b - d) (c - d)) h
    simp only [det3_expand, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, PiLp.zero_apply] at this ⊢
    linear_combination this
  have ht : t * det3 (a - d) (b - d) (c - d) = 0 := by
    have := congrArg (fun v => det3 (a - d) v (c - d)) h
    simp only [det3_expand, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, PiLp.zero_apply] at this ⊢
    linear_combination this
  have hu : u * det3 (a - d) (b - d) (c - d) = 0 := by
    have := congrArg (fun v => det3 (a - d) (b - d) v) h
    simp only [det3_expand, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, PiLp.zero_apply] at this ⊢
    linear_combination this
  exact ⟨(mul_eq_zero.mp hs).resolve_right hdet, (mul_eq_zero.mp ht).resolve_right hdet,
    (mul_eq_zero.mp hu).resolve_right hdet⟩

theorem isT_gamma6 {a a' b c d : ℝ³} {β6 γ6 : ℝ} (hdet : det3 (a - d) (b - d) (c - d) ≠ 0)
    (ha' : a' = d + β6 • (b - d) + γ6 • (c - d)) (hT : IsT a' b c d) : γ6 = 1 := by
  obtain ⟨r, hr⟩ := hT
  have h : (0 : ℝ) • (a - d) + (-(r + β6)) • (b - d) + (1 - γ6) • (c - d) = 0 := by
    have : c - a' = r • (b - d) := hr
    rw [ha'] at this
    rw [← sub_eq_zero] at this
    rw [← this]; module
  have := (det3_indep hdet h).2.2
  linarith

theorem isTp_alpha1 {a b c' d : ℝ³} {c : ℝ³} {α1 β1 : ℝ} (hdet : det3 (a - d) (b - d) (c - d) ≠ 0)
    (hc' : c' = d + α1 • (a - d) + β1 • (b - d)) (hT : IsT' a b c' d) : α1 = 1 := by
  obtain ⟨r, hr⟩ := hT
  have h : (α1 - 1) • (a - d) + (β1 - r) • (b - d) + (0 : ℝ) • (c - d) = 0 := by
    have : c' - a = r • (b - d) := hr
    rw [hc'] at this
    rw [← sub_eq_zero] at this
    rw [← this]; module
  have := (det3_indep hdet h).1
  linarith

/-- W0 at `T`. -/
theorem norm08w_coordsT {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (hT : IsT a' b c d) :
    ∃ α1 α4 β1 γ4 β6 : ℝ, det3 (a - d) (b - d) (c - d) ≠ 0 ∧
      c' = d + α1 • (a - d) + β1 • (b - d) ∧ b' = d + α4 • (a - d) + γ4 • (c - d) ∧
      a' = d + β6 • (b - d) + (1 : ℝ) • (c - d) ∧
      0 < α1 ∧ 0 < β1 ∧ 1 < α1 + β1 ∧ 0 < α4 ∧ 0 < γ4 ∧ 1 < α4 + γ4 ∧ 0 < β6 ∧
      (W.F.a'bc.f c' < W.F.a'bc.f a → 1 < α1) := by
  obtain ⟨α1, α4, β1, γ4, β6, γ6, hdet, hc', hb', ha', h1, h2, h3, h4, h5, h6, h7, h8, h9, hf, hf'⟩ :=
    norm08w_coords W
  have := isT_gamma6 hdet ha' hT
  subst this
  exact ⟨α1, α4, β1, γ4, β6, hdet, hc', hb', ha', h1, h2, h3, h4, h5, h6, h7, hf'⟩

/-- W0 at `T'`. -/
theorem norm08w_coordsTp {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (hT : IsT' a b c' d) :
    ∃ α4 β1 γ4 β6 γ6 : ℝ, det3 (a - d) (b - d) (c - d) ≠ 0 ∧
      c' = d + (1 : ℝ) • (a - d) + β1 • (b - d) ∧ b' = d + α4 • (a - d) + γ4 • (c - d) ∧
      a' = d + β6 • (b - d) + γ6 • (c - d) ∧
      0 < β1 ∧ 0 < α4 ∧ 0 < γ4 ∧ 1 < α4 + γ4 ∧ 0 < β6 ∧ 0 < γ6 ∧ 1 < β6 + γ6 ∧
      (W.F.abc'.f c < W.F.abc'.f a' → γ6 < 1) := by
  obtain ⟨α1, α4, β1, γ4, β6, γ6, hdet, hc', hb', ha', h1, h2, h3, h4, h5, h6, h7, h8, h9, hf, hf'⟩ :=
    norm08w_coords W
  have := isTp_alpha1 hdet hc' hT
  subst this
  exact ⟨α4, β1, γ4, β6, γ6, hdet, hc', hb', ha', h2, h4, h5, h6, h7, h8, h9, hf⟩

/-- Gale `κ_a, κ_b` in the frame coordinates (any `Norm08w`). -/
theorem gale_pt {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) {α1 α4 β1 γ4 β6 γ6 : ℝ}
    (hdet : det3 (a - d) (b - d) (c - d) ≠ 0)
    (hc' : c' = d + α1 • (a - d) + β1 • (b - d)) (hb' : b' = d + α4 • (a - d) + γ4 • (c - d))
    (ha' : a' = d + β6 • (b - d) + γ6 • (c - d)) (hs : 1 - β6 - γ6 ≠ 0) :
    ∃ μ : ℝ, galeD W.G.l W.G.m a a' = μ * (α4 - α4 * β1 - α1 + α1 * γ4) ∧
      galeD W.G.l W.G.m b b' = μ * (β6 * (α1 - 1) + β1 * (1 - γ6)) :=
  gale_coords_gen W.G hdet hc' hb' ha' hs

/-! ### W1: planarity as coordinate equations -/

theorem planar_a_iff {a b b' c c' d : ℝ³} {α1 α4 β1 γ4 : ℝ}
    (hdet : det3 (a - d) (b - d) (c - d) ≠ 0)
    (hc' : c' = d + α1 • (a - d) + β1 • (b - d)) (hb' : b' = d + α4 • (a - d) + γ4 • (c - d)) :
    det3 (c - b) (b' - b) (c' - b) = 0 ↔ α4 * (1 - β1) = α1 * (1 - γ4) := by
  have e : det3 (c - b) (b' - b) (c' - b) =
      det3 (a - d) (b - d) (c - d) * (α1 * (1 - γ4) - α4 * (1 - β1)) := by
    rw [hc', hb']
    simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; ring
  rw [e, mul_eq_zero]
  constructor
  · rintro (h | h)
    · exact absurd h hdet
    · linarith
  · intro h; right; linarith

theorem planar_c_iff {a a' b b' c d : ℝ³} {α4 γ4 β6 γ6 : ℝ}
    (hdet : det3 (a - d) (b - d) (c - d) ≠ 0)
    (hb' : b' = d + α4 • (a - d) + γ4 • (c - d)) (ha' : a' = d + β6 • (b - d) + γ6 • (c - d)) :
    det3 (b - a) (a' - a) (b' - a) = 0 ↔ γ6 * (1 - α4) = γ4 * (1 - β6) := by
  have e : det3 (b - a) (a' - a) (b' - a) =
      det3 (a - d) (b - d) (c - d) * (γ4 * (1 - β6) - γ6 * (1 - α4)) := by
    rw [ha', hb']
    simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; ring
  rw [e, mul_eq_zero]
  constructor
  · rintro (h | h)
    · exact absurd h hdet
    · linarith
  · intro h; right; linarith

theorem planar_b_iff {a a' b c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ}
    (hdet : det3 (a - d) (b - d) (c - d) ≠ 0)
    (hc' : c' = d + α1 • (a - d) + β1 • (b - d)) (ha' : a' = d + β6 • (b - d) + γ6 • (c - d)) :
    det3 (c - a) (a' - a) (c' - a) = 0 ↔ β1 * (1 - β6 - γ6) = β6 * (1 - α1 - β1) := by
  have e : det3 (c - a) (a' - a) (c' - a) =
      det3 (a - d) (b - d) (c - d) * (β6 * (1 - α1 - β1) - β1 * (1 - β6 - γ6)) := by
    rw [ha', hc']
    simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; ring
  rw [e, mul_eq_zero]
  constructor
  · rintro (h | h)
    · exact absurd h hdet
    · linarith
  · intro h; right; linarith

end C2
end Type08Sp
end Minimality
