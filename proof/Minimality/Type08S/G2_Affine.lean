module

public import Minimality.Type08S.Defs08

@[expose] public section

set_option autoImplicit true

/-!
# Group G2: affine facts in the used labelling

Paper: S4b (`T ∩ T' ⊂ {κ_b = 0}` by (T3), PROOFS §29 table and §29.1), and "a planar equator has
`κ = 0`" (so `flatN2`, `flatT4` are vacuous at `Norm08`).  Lean templates: `IsCap.tieT_geom`,
`IsCap.tieT'_geom` (`Type08Codim.lean:145,161`), `GaleData.planar_of_kappa` and its converse in
`Type08Flat.lean`.  Size: S (< 100 lines).  Risk: low.
-/

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

private theorem det3_mid {p q u : ℝ³} (x y : ℝ) :
    det3 p (x • q + y • u) u = x * det3 p q u := by
  simp only [det3_expand, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring

private theorem det3_first {p q u : ℝ³} (x y : ℝ) :
    det3 (x • p + y • u) q u = x * det3 p q u := by
  simp only [det3_expand, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring

private theorem tie_conv_T {a a' b b' c c' d : ℝ³} {F : OctFacets a a' b b' c c'} (hd : IsCap F d)
    (h : ∃ r : ℝ, c - a' = r • (b - d)) : F.abc'.f a' = F.abc'.f c := by
  obtain ⟨r, hr⟩ := h
  have hnd := F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  have hFc := F.abc'.neg c (by simp) (Ne.symm hnd.1.2.2.2.1) (Ne.symm hnd.2.2.1.2.1) hnd.2.2.2.2.1
  obtain ⟨-, -, -, ha'⟩ : 0 < F.ab'c.f a' / F.ab'c.f b ∧ 0 < F.abc'.f a' / F.abc'.f c ∧
      1 < F.ab'c.f a' / F.ab'c.f b + F.abc'.f a' / F.abc'.f c ∧
      a' = d + (F.ab'c.f a' / F.ab'c.f b) • (b - d) + (F.abc'.f a' / F.abc'.f c) • (c - d) :=
    hd.perm₁₂.Qac_coords'
  generalize F.ab'c.f a' / F.ab'c.f b = k at ha'
  generalize hq : F.abc'.f a' / F.abc'.f c = q at ha'
  have hv : (1 - q) • (c - d) + (-(r + k)) • (b - d) = 0 := by
    have : c - a' = r • (b - d) := hr
    rw [ha'] at this
    rw [← sub_eq_zero] at this
    rw [← this]; module
  have h0 := det3_mid (p := a - d) (q := c - d) (u := b - d) (1 - q) (-(r + k))
  rw [hv] at h0
  have hz : det3 (a - d) 0 (b - d) = 0 := by simp [det3_expand]
  rw [hz] at h0
  have hq1 : q = 1 := by
    have := hd.det_Qac_ne
    rcases mul_eq_zero.mp h0.symm with h | h
    · linarith
    · exact absurd h this
  rw [hq1, div_eq_one_iff_eq hFc.ne] at hq
  exact hq

private theorem tie_conv_T' {a a' b b' c c' d : ℝ³} {F : OctFacets a a' b b' c c'} (hd : IsCap F d)
    (h : ∃ r : ℝ, c' - a = r • (b - d)) : F.a'bc.f c' = F.a'bc.f a := by
  obtain ⟨r, hr⟩ := h
  have hnd := F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  have hFa := F.a'bc.neg a (by simp) hnd.1.1 hnd.1.2.1 hnd.1.2.2.2.1
  obtain ⟨-, -, -, hc'⟩ : 0 < F.a'bc.f c' / F.a'bc.f a ∧ 0 < F.ab'c.f c' / F.ab'c.f b ∧
      1 < F.a'bc.f c' / F.a'bc.f a + F.ab'c.f c' / F.ab'c.f b ∧
      c' = d + (F.a'bc.f c' / F.a'bc.f a) • (a - d) + (F.ab'c.f c' / F.ab'c.f b) • (b - d) :=
    hd.perm₂₃.Qac_coords'
  generalize F.ab'c.f c' / F.ab'c.f b = k at hc'
  generalize hp : F.a'bc.f c' / F.a'bc.f a = p at hc'
  have hv : (p - 1) • (a - d) + (-(r - k)) • (b - d) = 0 := by
    have : c' - a = r • (b - d) := hr
    rw [hc'] at this
    rw [← sub_eq_zero] at this
    rw [← this]; module
  have h0 := det3_first (p := a - d) (q := c - d) (u := b - d) (p - 1) (-(r - k))
  rw [hv] at h0
  have hz : det3 0 (c - d) (b - d) = 0 := by simp [det3_expand]
  rw [hz] at h0
  have hp1 : p = 1 := by
    have := hd.det_Qac_ne
    rcases mul_eq_zero.mp h0.symm with h | h
    · linarith
    · exact absurd h this
  rw [hp1, div_eq_one_iff_eq hFa.ne] at hp
  exact hp

/-- S4b: in the labelling of Lemma 6, `T` and `T'` do not occur together. -/
theorem norm08_tieTT' {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) :
    FP a a' b b' c c' d .tieTT := by
  rintro ⟨h1, h2⟩
  have e1 := tie_conv_T N.hd h1
  have e2 := tie_conv_T' N.hd h2
  obtain ⟨-, ga', -, gc'⟩ := type08_b'_signs N.F N.G N.hκb.ne' N.hκc N.hU
  exact absurd e2 (ne_of_lt (type08_T_far N.F N.G N.hκb N.hκc N.hU e1))

private theorem det3_comb {u v w : ℝ³} (x1 y1 z1 x2 y2 z2 x3 y3 z3 : ℝ) :
    det3 (x1 • u + y1 • v + z1 • w) (x2 • u + y2 • v + z2 • w) (x3 • u + y3 • v + z3 • w) =
      (x1 * (y2 * z3 - z2 * y3) - y1 * (x2 * z3 - z2 * x3) + z1 * (x2 * y3 - y2 * x3)) *
        det3 u v w := by
  simp only [det3_expand, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring

private theorem det3_smul3 {p q r : ℝ³} (k : ℝ) :
    det3 (k • p) (k • q) (k • r) = k ^ 3 * det3 p q r := by
  simp only [det3_expand, PiLp.smul_apply, smul_eq_mul]; ring

private theorem kappa_planar {a a' b b' c c' : ℝ³} {l m : ℝ³ → ℝ}
    (hl : IsDep a a' b b' c c' l) (hm : IsDep a a' b b' c c' m)
    (hD : det3 (a - b) (a' - b) (c - b) ≠ 0)
    (hp : det3 (c - b) (b' - b) (c' - b) = 0) : galeD l m a a' = 0 := by
  have E1 : l a • (a - b) + l a' • (a' - b) + l b' • (b' - b) + l c • (c - b) +
      l c' • (c' - b) = 0 := by
    linear_combination (norm := module) hl.vsum - hl.sum • b
  have E2 : m a • (a - b) + m a' • (a' - b) + m b' • (b' - b) + m c • (c - b) +
      m c' • (c' - b) = 0 := by
    linear_combination (norm := module) hm.vsum - hm.sum • b
  set κ := galeD l m a a' with hκ
  have hA : κ • (a - b) = (-(m a' * l c - l a' * m c)) • (c - b)
      + (-(m a' * l b' - l a' * m b')) • (b' - b) + (-(m a' * l c' - l a' * m c')) • (c' - b) := by
    rw [hκ]; simp only [galeD]
    linear_combination (norm := module) m a' • E1 - l a' • E2
  have hA' : κ • (a' - b) = (-(l a * m c - m a * l c)) • (c - b)
      + (-(l a * m b' - m a * l b')) • (b' - b) + (-(l a * m c' - m a * l c')) • (c' - b) := by
    rw [hκ]; simp only [galeD]
    linear_combination (norm := module) l a • E2 - m a • E1
  have hu : κ • (c - b) = κ • (c - b) + (0:ℝ) • (b' - b) + (0:ℝ) • (c' - b) := by module
  have h3 : det3 (κ • (a - b)) (κ • (a' - b)) (κ • (c - b)) = 0 := by
    rw [hA, hA', hu]
    rw [det3_comb, hp, mul_zero]
  rw [det3_smul3] at h3
  rcases mul_eq_zero.mp h3 with h | h
  · exact pow_eq_zero_iff (by norm_num) |>.mp h
  · exact absurd h hD

/-- `κ_a > 0` gives a non-planar equator `b c b' c'`, so the flat fields are vacuous. -/
theorem norm08_nonplanar {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) :
    det3 (c - b) (b' - b) (c' - b) ≠ 0 := by
  intro hp
  have hD : det3 (a - b) (a' - b) (c - b) ≠ 0 := by
    have := frame_det_ne N.F
    intro h0; apply this
    simp only [det3_expand, PiLp.sub_apply] at h0 ⊢
    nlinarith [h0]
  exact N.hκa.ne' (kappa_planar N.G.hl N.G.hm hD hp)

theorem norm08_flat {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) :
    FP a a' b b' c c' d .flatN2 ∧ FP a a' b b' c c' d .flatT4 :=
  ⟨fun h => absurd h (norm08_nonplanar N), fun h => absurd h (norm08_nonplanar N)⟩

end Type08Sp
end Minimality
