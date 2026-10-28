module

public import Minimality.Type08S.GT_Wrap2

@[expose] public section

set_option autoImplicit true

/-!
# GT wrapper, part 3: the T4 picture data at the far triple tie (zw < 0 <= zv)
-/

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
variable {a a' b b' c c' d : ℝ³}

structure T4Cfg0 (E U zv zw A b1 b2 r1 r2 xa za ua a3 : ℝ)
    (FH FQac FT1 FT2 FT3 FT4 : Fc) : Prop where
  hE : 0 < E
  hU : 0 < U
  hzv : 0 ≤ zv
  hzw : zw < zv
  hA : 0 < A
  hb2 : 0 < b2
  hr2 : 0 < r2
  hxa : 0 < xa
  hxaA : xa < A
  hza : zw < za
  hua0 : 0 < ua
  hua1 : ua < 1
  hDr : (A - r1) * (b2 - r2) + r2 * (b1 - r1) < 0
  -- H = Q_ab: on d, a, c', b; off a', b', c
  H_W : FH.ev ⟨0, 0, zw⟩ = 0
  H_A : FH.ev ⟨ua * b1, ua * b2, a3⟩ = 0
  H_B : FH.ev ⟨b1, b2, 0⟩ = 0
  H_V : FH.ev ⟨0, 0, zv⟩ = 0
  H_P : FH.ev ⟨xa, 0, za⟩ < 0
  H_R : FH.ev ⟨r1, r2, 0⟩ < 0
  H_G : FH.ev ⟨A, 0, 0⟩ < 0
  -- Q_ac: on d, a, b', c; off a', b, c'
  Qac_W : FQac.ev ⟨0, 0, zw⟩ = 0
  Qac_A : FQac.ev ⟨ua * b1, ua * b2, a3⟩ = 0
  Qac_R : FQac.ev ⟨r1, r2, 0⟩ = 0
  Qac_G : FQac.ev ⟨A, 0, 0⟩ = 0
  Qac_P : FQac.ev ⟨xa, 0, za⟩ < 0
  Qac_V : FQac.ev ⟨0, 0, zv⟩ < 0
  Qac_B : FQac.ev ⟨b1, b2, 0⟩ < 0
  -- T1 = (a, c', b'): on a, c', b'; off a', b, c, d
  T1_A : FT1.ev ⟨ua * b1, ua * b2, a3⟩ = 0
  T1_B : FT1.ev ⟨b1, b2, 0⟩ = 0
  T1_R : FT1.ev ⟨r1, r2, 0⟩ = 0
  T1_P : FT1.ev ⟨xa, 0, za⟩ < 0
  T1_V : FT1.ev ⟨0, 0, zv⟩ < 0
  T1_G : FT1.ev ⟨A, 0, 0⟩ < 0
  T1_W : FT1.ev ⟨0, 0, zw⟩ < 0
  -- T2 = (c', b, a'): on c', b, a'; off a, b', c, d
  T2_B : FT2.ev ⟨b1, b2, 0⟩ = 0
  T2_V : FT2.ev ⟨0, 0, zv⟩ = 0
  T2_P : FT2.ev ⟨xa, 0, za⟩ = 0
  T2_A : FT2.ev ⟨ua * b1, ua * b2, a3⟩ < 0
  T2_R : FT2.ev ⟨r1, r2, 0⟩ < 0
  T2_G : FT2.ev ⟨A, 0, 0⟩ < 0
  T2_W : FT2.ev ⟨0, 0, zw⟩ < 0
  -- T3 = (c', b', a'): on c', b', a'; off a, b, c, d
  T3_B : FT3.ev ⟨b1, b2, 0⟩ = 0
  T3_R : FT3.ev ⟨r1, r2, 0⟩ = 0
  T3_P : FT3.ev ⟨xa, 0, za⟩ = 0
  T3_A : FT3.ev ⟨ua * b1, ua * b2, a3⟩ < 0
  T3_V : FT3.ev ⟨0, 0, zv⟩ < 0
  T3_G : FT3.ev ⟨A, 0, 0⟩ < 0
  T3_W : FT3.ev ⟨0, 0, zw⟩ < 0
  -- T4 = (b', c, a'): on b', c, a'; off a, b, c', d
  T4_R : FT4.ev ⟨r1, r2, 0⟩ = 0
  T4_G : FT4.ev ⟨A, 0, 0⟩ = 0
  T4_P : FT4.ev ⟨xa, 0, za⟩ = 0
  T4_A : FT4.ev ⟨ua * b1, ua * b2, a3⟩ < 0
  T4_V : FT4.ev ⟨0, 0, zv⟩ < 0
  T4_B : FT4.ev ⟨b1, b2, 0⟩ < 0
  T4_W : FT4.ev ⟨0, 0, zw⟩ < 0

structure T4Pic (a a' b b' c c' d : ℝ³) (fG : ℝ³ → ℝ)
    (E U zv zw A b1 b2 r1 r2 xa za ua a3 t : ℝ) (FH FQac FT1 FT2 FT3 FT4 : Fc) : Prop where
  Φb : hfΦ b c (b - d) fG b = ⟨0, 0, zv⟩
  Φd : hfΦ b c (b - d) fG d = ⟨0, 0, zw⟩
  Φc : hfΦ b c (b - d) fG c = ⟨A, 0, 0⟩
  Φc' : hfΦ b c (b - d) fG c' = ⟨b1, b2, 0⟩
  Φb' : hfΦ b c (b - d) fG b' = ⟨r1, r2, 0⟩
  Φa' : hfΦ b c (b - d) fG a' = ⟨t * A, 0, za⟩
  Φa : hfΦ b c (b - d) fG a = ⟨ua * b1, ua * b2, a3⟩
  hzw0 : zw < 0
  ht0 : 0 < t
  ht1 : t < 1
  hm : a3 < (1 - ua) * zw
  hmp : (1 - t) * zv < za
  hAE : A = E
  hxt : xa = t * A
  cfg : T4Cfg0 E U zv zw A b1 b2 r1 r2 xa za ua a3 FH FQac FT1 FT2 FT3 FT4

set_option maxHeartbeats 2000000 in
theorem t4_pic (F : OctFacets a a' b b' c c') (hd : IsCap F d)
    (hfc : F.abc'.f c < F.abc'.f a') (hfc' : F.a'bc.f c' < F.a'bc.f a)
    (htouch : ⟪c, b - d⟫ = ⟪b', b - d⟫ ∧ ⟪c', b - d⟫ = ⟪b', b - d⟫)
    (hzw0 : ⟪d, b - d⟫ < ⟪c, b - d⟫) (hzv0 : ⟪c, b - d⟫ ≤ ⟪b, b - d⟫) :
    ∃ (E U zv zw A b1 b2 r1 r2 xa za ua a3 t : ℝ) (FH FQac FT1 FT2 FT3 FT4 : Fc),
      T4Pic a a' b b' c c' d F.a'bc.f E U zv zw A b1 b2 r1 r2 xa za ua a3 t FH FQac FT1 FT2 FT3 FT4 ∧
      E = ⟪hfE b c (b - d), hfE b c (b - d)⟫ := by
  classical
  have hnd := F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨haa', hab, hab', hac, hac'⟩, ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩,
    ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd
  obtain ⟨hda, hda', hdb, hdb', hdc, hdc'⟩ := hd.ne
  -- the coordinates of the cap in the frame `d; a, c, b`
  obtain ⟨hα, hβ, hαβ, hb'⟩ := hd.Qac_coords'
  obtain ⟨hα₁, hβ₁, -, hc'⟩ : 0 < F.a'bc.f c' / F.a'bc.f a ∧ 0 < F.ab'c.f c' / F.ab'c.f b ∧
      1 < F.a'bc.f c' / F.a'bc.f a + F.ab'c.f c' / F.ab'c.f b ∧
      c' = d + (F.a'bc.f c' / F.a'bc.f a) • (a - d) + (F.ab'c.f c' / F.ab'c.f b) • (b - d) :=
    hd.perm₂₃.Qac_coords'
  obtain ⟨hα₂, hβ₂, hαβ₂, ha'⟩ : 0 < F.ab'c.f a' / F.ab'c.f b ∧ 0 < F.abc'.f a' / F.abc'.f c ∧
      1 < F.ab'c.f a' / F.ab'c.f b + F.abc'.f a' / F.abc'.f c ∧
      a' = d + (F.ab'c.f a' / F.ab'c.f b) • (b - d) + (F.abc'.f a' / F.abc'.f c) • (c - d) :=
    hd.perm₁₂.Qac_coords'
  have hFa := F.a'bc.neg a (by simp) haa' hab hac
  have hFc := F.abc'.neg c (by simp) (Ne.symm hac) (Ne.symm hbc) hcc'
  have hα₁1 : 1 < F.a'bc.f c' / F.a'bc.f a := (one_lt_div_of_neg hFa).mpr hfc'
  have hβ₂1 : F.abc'.f a' / F.abc'.f c < 1 := (div_lt_one_of_neg hFc).mpr hfc
  have hκ := t4_kappa_pos hd hb' hc' ha' hα hβ₁ hα₂ hβ₂1.le
  have hEf := hd.det_Qac_ne
  generalize F.a'bc.f c' / F.a'bc.f a = α₁ at *
  generalize F.ab'c.f c' / F.ab'c.f b = β₁ at *
  generalize F.ab'c.f a' / F.ab'c.f b = α₂ at *
  generalize F.abc'.f a' / F.abc'.f c = β₂ at *
  generalize F.a'bc.f b' / F.a'bc.f a = α at *
  generalize F.abc'.f b' / F.abc'.f c = β at *
  have Fr := t4_frame F hd
  set u0 : ℝ³ := b - d with hu0
  set e : ℝ³ := hfE b c u0 with he
  set fG : ℝ³ → ℝ := F.a'bc.f with hfG
  set N : ℝ³ := F.a'bc.N with hN
  -- the real coordinates
  set E : ℝ := ⟪e, e⟫ with hE
  set U : ℝ := ⟪u0, u0⟫ with hU
  set zv : ℝ := ⟪b - c, u0⟫ with hzv
  set zw : ℝ := ⟪d - c, u0⟫ with hzw
  set A : ℝ := ⟪c - b, e⟫ with hA
  set b1 : ℝ := ⟪c' - b, e⟫ with hb1
  set b2 : ℝ := -fG c' with hb2
  set r1 : ℝ := ⟪b' - b, e⟫ with hr1
  set r2 : ℝ := -fG b' with hr2
  set xa : ℝ := ⟪a' - b, e⟫ with hxa
  set za : ℝ := ⟪a' - c, u0⟫ with hza
  set a3 : ℝ := ⟪a - c, u0⟫ with ha3
  have heu : ⟪e, u0⟫ = 0 := Fr.inner_e_u
  have heu' : ⟪u0, e⟫ = 0 := by rw [real_inner_comm]; exact heu
  have hNe : ⟪N, e⟫ = 0 := Fr.inner_N_e
  have hNu : ⟪N, u0⟫ = 0 := Fr.hNu
  have hfGa' : fG a' = 0 := F.a'bc.hP
  have hfGb : fG b = 0 := F.a'bc.hQ
  have hfGc : fG c = 0 := F.a'bc.hR
  have hfGd : fG d = 0 := hd.a'bc
  have hZc' : ⟪c' - c, u0⟫ = 0 := by rw [inner_sub_left]; linarith [htouch.1, htouch.2]
  have hZb' : ⟪b' - c, u0⟫ = 0 := by rw [inner_sub_left]; linarith [htouch.1, htouch.2]
  have hbpc : c - b = e + hfTau b c u0 • u0 := by simp [he, hfE]
  have hAE : A = E := by
    rw [hA, hbpc, inner_add_left, real_inner_smul_left, heu', hE]; ring
  have hΦb : hfΦ b c u0 fG b = ⟨0, 0, zv⟩ := by
    show (⟨⟪b - b, e⟫, -fG b, ⟪b - c, u0⟫⟩ : V3) = ⟨0, 0, zv⟩
    rw [hfGb, sub_self, inner_zero_left]; simp [hzv]
  have hΦd : hfΦ b c u0 fG d = ⟨0, 0, zw⟩ := by
    show (⟨⟪d - b, e⟫, -fG d, ⟪d - c, u0⟫⟩ : V3) = ⟨0, 0, zw⟩
    have : d - b = -u0 := by rw [hu0]; abel
    rw [hfGd, this, inner_neg_left, heu']; simp [hzw]
  have hΦc : hfΦ b c u0 fG c = ⟨A, 0, 0⟩ := by
    show (⟨⟪c - b, e⟫, -fG c, ⟪c - c, u0⟫⟩ : V3) = ⟨A, 0, 0⟩
    rw [hfGc, sub_self, inner_zero_left]; simp [hA]
  have hΦc' : hfΦ b c u0 fG c' = ⟨b1, b2, 0⟩ := by
    show (⟨⟪c' - b, e⟫, -fG c', ⟪c' - c, u0⟫⟩ : V3) = ⟨b1, b2, 0⟩
    rw [hZc']
  have hΦb' : hfΦ b c u0 fG b' = ⟨r1, r2, 0⟩ := by
    show (⟨⟪b' - b, e⟫, -fG b', ⟪b' - c, u0⟫⟩ : V3) = ⟨r1, r2, 0⟩
    rw [hZb']
  have hΦa' : hfΦ b c u0 fG a' = ⟨xa, 0, za⟩ := by
    show (⟨⟪a' - b, e⟫, -fG a', ⟪a' - c, u0⟫⟩ : V3) = ⟨xa, 0, za⟩
    rw [hfGa']; simp [hxa, hza]
  -- the representation of `a` and `a'`
  have hα₁pos : 0 < α₁ := by linarith
  have hXa : ⟪a - b, e⟫ = b1 / α₁ := by
    have h1 : α₁ • (a - d) = (c' - d) - β₁ • u0 := by
      have := hc'; rw [hu0]; rw [eq_sub_iff_add_eq]; rw [hc']; module
    have h2 : a - b = α₁⁻¹ • ((c' - d) - β₁ • u0) - u0 := by
      rw [← h1, smul_smul, inv_mul_cancel₀ hα₁pos.ne', one_smul, hu0]; abel
    rw [h2, inner_sub_left, real_inner_smul_left, inner_sub_left, real_inner_smul_left, heu',
      show c' - d = (c' - b) + u0 by rw [hu0]; abel, inner_add_left, heu', hb1]
    field_simp
    ring
  have hYa : fG a = fG c' / α₁ := by
    have h1 : α₁ • (a - d) = (c' - d) - β₁ • u0 := by
      have := hc'; rw [hu0]; rw [eq_sub_iff_add_eq]; rw [hc']; module
    have h2 : a - d = α₁⁻¹ • ((c' - d) - β₁ • u0) := by
      rw [← h1, smul_smul, inv_mul_cancel₀ hα₁pos.ne', one_smul]
    have h3 : fG a - fG d = ⟪N, a - d⟫ := F.a'bc.hN a d
    have h4 : fG c' - fG d = ⟪N, c' - d⟫ := F.a'bc.hN c' d
    rw [h2, real_inner_smul_right, inner_sub_right, real_inner_smul_right, hNu, ← h4, hfGd] at h3
    rw [div_eq_inv_mul]
    linarith
  have hXa' : xa = β₂ * A := by
    have h1 : a' - b = (α₂ - 1 + β₂) • u0 + β₂ • (c - b) := by
      rw [ha', hu0]; module
    rw [hxa, h1, inner_add_left, real_inner_smul_left, real_inner_smul_left, heu', hA]; ring
  have hZa' : za = (1 - β₂) * zw + α₂ * U := by
    have h1 : a' - c = (1 - β₂) • (d - c) + α₂ • u0 := by
      rw [ha', hu0]; module
    rw [hza, h1, inner_add_left, real_inner_smul_left, real_inner_smul_left, hzw, hU]
  have hΦa : hfΦ b c u0 fG a = ⟨α₁⁻¹ * b1, α₁⁻¹ * b2, a3⟩ := by
    show (⟨⟪a - b, e⟫, -fG a, ⟪a - c, u0⟫⟩ : V3) = ⟨α₁⁻¹ * b1, α₁⁻¹ * b2, a3⟩
    rw [hXa, hYa]
    simp only [V3.mk.injEq, hb2]
    refine ⟨by ring, by ring, rfl⟩
  -- positivity
  have hUpos : 0 < U := Fr.hu
  have hEpos : 0 < E := Fr.hee
  have hApos : 0 < A := by rw [hAE]; exact hEpos
  have hzvw : zv - zw = U := by
    rw [hzv, hzw, ← inner_sub_left]
    have : (b - c) - (d - c) = u0 := by rw [hu0]; abel
    rw [this]
  have hzvnn : 0 ≤ zv := by
    have : zv = ⟪b, u0⟫ - ⟪c, u0⟫ := by rw [hzv, inner_sub_left]
    linarith
  have hb2pos : 0 < b2 := by
    rw [hb2]; have := F.a'bc.neg c' (by simp) (Ne.symm ha'c') (Ne.symm hbc') (Ne.symm hcc'); linarith
  have hr2pos : 0 < r2 := by
    rw [hr2]; have := F.a'bc.neg b' (by simp) (Ne.symm ha'b') (Ne.symm hbb') hb'c; linarith
  have hzwneg : zw < 0 := by
    have : zw = ⟪d, u0⟫ - ⟪c, u0⟫ := by rw [hzw, inner_sub_left]
    linarith
  -- the shadow convexity at `c`
  have hDr : (A - r1) * (b2 - r2) + r2 * (b1 - r1) < 0 := by
    obtain ⟨-, d2, -, -, -, d6, -⟩ := t4_slide_dets hb' hc' ha'
    have hEf2 : 0 < det3 (a - d) (c - d) (b - d) * det3 (a - d) (c - d) (b - d) :=
      mul_self_pos.mpr hEf
    have hprod : 0 < det3 (c - b') (c' - b') (b - d) * det3 (c' - b) (c - b) (b - d) := by
      rw [d6, d2]
      have : (α + β * α₁ - α₁) * det3 (a - d) (c - d) (b - d) * (α₁ * det3 (a - d) (c - d) (b - d)) =
          ((α + α₁ * (β - 1)) * α₁) * (det3 (a - d) (c - d) (b - d) * det3 (a - d) (c - d) (b - d)) := by
        ring
      rw [this]; exact mul_pos (mul_pos hκ hα₁pos) hEf2
    have h2 := Fr.shadow_sign b' c c' b c' c hprod
    rw [hΦb', hΦc, hΦc', hΦb] at h2
    have e1 : crossXY ⟨r1, r2, 0⟩ ⟨A, 0, 0⟩ ⟨b1, b2, 0⟩ =
        (A - r1) * (b2 - r2) + r2 * (b1 - r1) := by simp only [crossXY]; ring
    have e2 : crossXY ⟨0, 0, zv⟩ ⟨b1, b2, 0⟩ ⟨A, 0, 0⟩ = -(b2 * A) := by
      simp only [crossXY]; ring
    rw [e1, e2] at h2
    exact neg_of_mul_pos_left h2 (neg_nonpos.mpr (mul_pos hb2pos hApos).le)
  -- the facets
  have evq0 : ∀ (f : ℝ³ → ℝ) (Nf : ℝ³), (∀ y z, f y - f z = ⟪Nf, y - z⟫) → ∀ (p : ℝ³) (q : V3),
      hfΦ b c u0 fG p = q → f p = 0 → (hfFc b c u0 N f Nf).ev q = 0 := by
    intro f Nf hf p q hq h0
    rw [← hq, Fr.ev_hfΦ hf, h0]
  have evql : ∀ (f : ℝ³ → ℝ) (Nf : ℝ³), (∀ y z, f y - f z = ⟪Nf, y - z⟫) → ∀ (p : ℝ³) (q : V3),
      hfΦ b c u0 fG p = q → f p < 0 → (hfFc b c u0 N f Nf).ev q < 0 := by
    intro f Nf hf p q hq h0
    rw [← hq, Fr.ev_hfΦ hf]; exact h0
  have hxapos : 0 < xa := by rw [hXa']; exact mul_pos hβ₂ hApos
  have hxaA : xa < A := by rw [hXa']; exact mul_lt_of_lt_one_left hApos hβ₂1
  have hzaw : zw < za := by
    have h1 := mul_pos hβ₂ (neg_pos.mpr hzwneg)
    have h2 := mul_pos hα₂ hUpos
    rw [hZa']; linarith
  have hua0 : 0 < α₁⁻¹ := inv_pos.mpr hα₁pos
  have hua1 : α₁⁻¹ < 1 := inv_lt_one_of_one_lt₀ hα₁1
  have cfg : T4Cfg0 E U zv zw A b1 b2 r1 r2 xa za α₁⁻¹ a3
      (hfFc b c u0 N F.abc'.f F.abc'.N) (hfFc b c u0 N F.ab'c.f F.ab'c.N)
      (hfFc b c u0 N F.ab'c'.f F.ab'c'.N) (hfFc b c u0 N F.a'bc'.f F.a'bc'.N)
      (hfFc b c u0 N F.a'b'c'.f F.a'b'c'.N) (hfFc b c u0 N F.a'b'c.f F.a'b'c.N) := by
    refine ⟨hEpos, hUpos, hzvnn, by linarith, hApos, hb2pos, hr2pos, hxapos, hxaA, hzaw, hua0, hua1,
      hDr, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    -- H = Q_ab = abc'
    · exact evq0 _ _ F.abc'.hN d _ hΦd hd.abc'
    · exact evq0 _ _ F.abc'.hN a _ hΦa F.abc'.hP
    · exact evq0 _ _ F.abc'.hN c' _ hΦc' F.abc'.hR
    · exact evq0 _ _ F.abc'.hN b _ hΦb F.abc'.hQ
    · exact evql _ _ F.abc'.hN a' _ hΦa' (F.abc'.neg a' (by simp) (Ne.symm haa') ha'b ha'c')
    · exact evql _ _ F.abc'.hN b' _ hΦb' (F.abc'.neg b' (by simp) (Ne.symm hab') (Ne.symm hbb') hb'c')
    · exact evql _ _ F.abc'.hN c _ hΦc (F.abc'.neg c (by simp) (Ne.symm hac) (Ne.symm hbc) hcc')
    -- Q_ac = ab'c
    · exact evq0 _ _ F.ab'c.hN d _ hΦd hd.ab'c
    · exact evq0 _ _ F.ab'c.hN a _ hΦa F.ab'c.hP
    · exact evq0 _ _ F.ab'c.hN b' _ hΦb' F.ab'c.hQ
    · exact evq0 _ _ F.ab'c.hN c _ hΦc F.ab'c.hR
    · exact evql _ _ F.ab'c.hN a' _ hΦa' (F.ab'c.neg a' (by simp) (Ne.symm haa') ha'b' ha'c)
    · exact evql _ _ F.ab'c.hN b _ hΦb (F.ab'c.neg b (by simp) (Ne.symm hab) hbb' hbc)
    · exact evql _ _ F.ab'c.hN c' _ hΦc' (F.ab'c.neg c' (by simp) (Ne.symm hac') (Ne.symm hb'c') (Ne.symm hcc'))
    -- T1 = ab'c'
    · exact evq0 _ _ F.ab'c'.hN a _ hΦa F.ab'c'.hP
    · exact evq0 _ _ F.ab'c'.hN c' _ hΦc' F.ab'c'.hR
    · exact evq0 _ _ F.ab'c'.hN b' _ hΦb' F.ab'c'.hQ
    · exact evql _ _ F.ab'c'.hN a' _ hΦa' (F.ab'c'.neg a' (by simp) (Ne.symm haa') ha'b' ha'c')
    · exact evql _ _ F.ab'c'.hN b _ hΦb (F.ab'c'.neg b (by simp) (Ne.symm hab) hbb' hbc')
    · exact evql _ _ F.ab'c'.hN c _ hΦc (F.ab'c'.neg c (by simp) (Ne.symm hac) (Ne.symm hb'c) hcc')
    · exact evql _ _ F.ab'c'.hN d _ hΦd hd.ab'c'
    -- T2 = a'bc'
    · exact evq0 _ _ F.a'bc'.hN c' _ hΦc' F.a'bc'.hR
    · exact evq0 _ _ F.a'bc'.hN b _ hΦb F.a'bc'.hQ
    · exact evq0 _ _ F.a'bc'.hN a' _ hΦa' F.a'bc'.hP
    · exact evql _ _ F.a'bc'.hN a _ hΦa (F.a'bc'.neg a (by simp) haa' hab hac')
    · exact evql _ _ F.a'bc'.hN b' _ hΦb' (F.a'bc'.neg b' (by simp) (Ne.symm ha'b') (Ne.symm hbb') hb'c')
    · exact evql _ _ F.a'bc'.hN c _ hΦc (F.a'bc'.neg c (by simp) (Ne.symm ha'c) (Ne.symm hbc) hcc')
    · exact evql _ _ F.a'bc'.hN d _ hΦd hd.a'bc'
    -- T3 = a'b'c'
    · exact evq0 _ _ F.a'b'c'.hN c' _ hΦc' F.a'b'c'.hR
    · exact evq0 _ _ F.a'b'c'.hN b' _ hΦb' F.a'b'c'.hQ
    · exact evq0 _ _ F.a'b'c'.hN a' _ hΦa' F.a'b'c'.hP
    · exact evql _ _ F.a'b'c'.hN a _ hΦa (F.a'b'c'.neg a (by simp) haa' hab' hac')
    · exact evql _ _ F.a'b'c'.hN b _ hΦb (F.a'b'c'.neg b (by simp) (Ne.symm ha'b) hbb' hbc')
    · exact evql _ _ F.a'b'c'.hN c _ hΦc (F.a'b'c'.neg c (by simp) (Ne.symm ha'c) (Ne.symm hb'c) hcc')
    · exact evql _ _ F.a'b'c'.hN d _ hΦd hd.a'b'c'
    -- T4 = a'b'c
    · exact evq0 _ _ F.a'b'c.hN b' _ hΦb' F.a'b'c.hQ
    · exact evq0 _ _ F.a'b'c.hN c _ hΦc F.a'b'c.hR
    · exact evq0 _ _ F.a'b'c.hN a' _ hΦa' F.a'b'c.hP
    · exact evql _ _ F.a'b'c.hN a _ hΦa (F.a'b'c.neg a (by simp) haa' hab' hac)
    · exact evql _ _ F.a'b'c.hN b _ hΦb (F.a'b'c.neg b (by simp) (Ne.symm ha'b) hbb' hbc)
    · exact evql _ _ F.a'b'c.hN c' _ hΦc' (F.a'b'c.neg c' (by simp) (Ne.symm ha'c') (Ne.symm hb'c') (Ne.symm hcc'))
    · exact evql _ _ F.a'b'c.hN d _ hΦd hd.a'b'c

  have ha3eq : a3 = (1 - α₁⁻¹) * zw - α₁⁻¹ * β₁ * U := by
    have h1 : a - d = α₁⁻¹ • ((c' - d) - β₁ • u0) := by
      have h0 : α₁ • (a - d) = (c' - d) - β₁ • u0 := by
        have := hc'; rw [hu0]; rw [eq_sub_iff_add_eq]; rw [hc']; module
      rw [← h0, smul_smul, inv_mul_cancel₀ hα₁pos.ne', one_smul]
    have h2 : a - c = (a - d) + (d - c) := by abel
    have h3 : c' - d = (c' - c) + (c - d) := by abel
    rw [ha3, h2, inner_add_left, h1, real_inner_smul_left, inner_sub_left, real_inner_smul_left, h3,
      inner_add_left, hZc', ← hzw]
    have h4 : ⟪c - d, u0⟫ = -zw := by
      rw [hzw, ← inner_neg_left, neg_sub]
    rw [h4, hU]; ring
  have hmlt : a3 < (1 - α₁⁻¹) * zw := by
    rw [ha3eq]; nlinarith [mul_pos (mul_pos hua0 hβ₁) hUpos]
  have hmp : (1 - β₂) * zv < za := by
    rw [hZa']
    have : zv = zw + U := by linarith
    rw [this]; nlinarith [mul_pos hUpos (show 0 < α₂ + β₂ - 1 by linarith)]
  have hAt : xa = β₂ * A := hXa'
  refine ⟨E, U, zv, zw, A, b1, b2, r1, r2, xa, za, α₁⁻¹, a3, β₂, _, _, _, _, _, _,
    ⟨hΦb, hΦd, hΦc, hΦc', hΦb', ?_, hΦa, hzwneg, hβ₂, hβ₂1, hmlt, hmp, hAE, hXa', cfg⟩, rfl⟩
  rw [← hAt]; exact hΦa'

end Type08Sp
end Minimality
