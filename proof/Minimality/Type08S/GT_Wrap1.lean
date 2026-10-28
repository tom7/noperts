module

public import Minimality.Type08S.GT_Touch
public import Minimality.Type08TouchN2
public import Minimality.Type08TouchT4
public import Minimality.Type08S.Defs08

@[expose] public section

set_option autoImplicit true

/-!
# GT wrapper, part 1: the N2 picture data at the far triple tie (zw < 0 <= zv)

`N2Cfg0` is `N2Cfg` of `HEndN2` with `0 <= zv` (S2 allowed); `N2Pic` bundles the frame images and the
facet signs; `n2_pic` extracts them from `OctFacets`, `IsCap`, the N2 closing hypotheses and the tie.
-/

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
variable {a a' b b' c c' c' d : ℝ³}
structure N2Cfg0 (E U zv zw A b1 b2 r1 r2 s m3 a1 a2 a3 : ℝ)
    (FH FQab FQac FT1 FT2 FT3 : Fc) : Prop where
  hE : 0 < E
  hU : 0 < U
  hzv : 0 ≤ zv
  hzw : zw < zv
  hA : 0 < A
  hb2 : 0 < b2
  hr2 : 0 < r2
  ha2 : 0 < a2
  hs0 : 0 < s
  hs1 : s < 1
  hm3 : 0 < m3
  hDr : (A - r1) * (b2 - r2) + r2 * (b1 - r1) < 0
  hTa1 : (A - r1) * (a2 - r2) + r2 * (a1 - r1) < 0
  hTa2 : (a1 - r1) * (b2 - r2) - (a2 - r2) * (b1 - r1) < 0
  H_M : FH.ev ⟨s * b1, s * b2, m3⟩ = 0
  H_B : FH.ev ⟨b1, b2, 0⟩ = 0
  H_W : FH.ev ⟨0, 0, zw⟩ = 0
  H_C : FH.ev ⟨0, 0, zv⟩ = 0
  H_A : FH.ev ⟨a1, a2, a3⟩ < 0
  H_G : FH.ev ⟨A, 0, 0⟩ < 0
  H_R : FH.ev ⟨r1, r2, 0⟩ < 0
  Qab_M : FQab.ev ⟨s * b1, s * b2, m3⟩ = 0
  Qab_A : FQab.ev ⟨a1, a2, a3⟩ = 0
  Qab_R : FQab.ev ⟨r1, r2, 0⟩ = 0
  Qab_B : FQab.ev ⟨b1, b2, 0⟩ = 0
  Qab_C : FQab.ev ⟨0, 0, zv⟩ < 0
  Qab_W : FQab.ev ⟨0, 0, zw⟩ < 0
  Qab_G : FQab.ev ⟨A, 0, 0⟩ < 0
  Qac_M : FQac.ev ⟨s * b1, s * b2, m3⟩ = 0
  Qac_A : FQac.ev ⟨a1, a2, a3⟩ = 0
  Qac_G : FQac.ev ⟨A, 0, 0⟩ = 0
  Qac_C : FQac.ev ⟨0, 0, zv⟩ = 0
  Qac_W : FQac.ev ⟨0, 0, zw⟩ < 0
  Qac_B : FQac.ev ⟨b1, b2, 0⟩ < 0
  Qac_R : FQac.ev ⟨r1, r2, 0⟩ < 0
  T1_A : FT1.ev ⟨a1, a2, a3⟩ = 0
  T1_R : FT1.ev ⟨r1, r2, 0⟩ = 0
  T1_G : FT1.ev ⟨A, 0, 0⟩ = 0
  T1_W : FT1.ev ⟨0, 0, zw⟩ < 0
  T1_B : FT1.ev ⟨b1, b2, 0⟩ < 0
  T1_C : FT1.ev ⟨0, 0, zv⟩ < 0
  T1_M : FT1.ev ⟨s * b1, s * b2, m3⟩ < 0
  T2_R : FT2.ev ⟨r1, r2, 0⟩ = 0
  T2_B : FT2.ev ⟨b1, b2, 0⟩ = 0
  T2_W : FT2.ev ⟨0, 0, zw⟩ = 0
  T2_A : FT2.ev ⟨a1, a2, a3⟩ < 0
  T2_G : FT2.ev ⟨A, 0, 0⟩ < 0
  T2_C : FT2.ev ⟨0, 0, zv⟩ < 0
  T2_M : FT2.ev ⟨s * b1, s * b2, m3⟩ < 0
  T3_R : FT3.ev ⟨r1, r2, 0⟩ = 0
  T3_G : FT3.ev ⟨A, 0, 0⟩ = 0
  T3_W : FT3.ev ⟨0, 0, zw⟩ = 0
  T3_A : FT3.ev ⟨a1, a2, a3⟩ < 0
  T3_B : FT3.ev ⟨b1, b2, 0⟩ < 0
  T3_C : FT3.ev ⟨0, 0, zv⟩ < 0
  T3_M : FT3.ev ⟨s * b1, s * b2, m3⟩ < 0

structure N2Pic (a a' b b' c c' d : ℝ³) (fG : ℝ³ → ℝ)
    (E U zv zw A b1 b2 r1 r2 s m3 a1 a2 a3 : ℝ) (FH FQab FQac FT1 FT2 FT3 : Fc) : Prop where
  Φc : hfΦ c b' (c - a') fG c = ⟨0, 0, zv⟩
  Φa' : hfΦ c b' (c - a') fG a' = ⟨0, 0, zw⟩
  Φb' : hfΦ c b' (c - a') fG b' = ⟨A, 0, 0⟩
  Φb : hfΦ c b' (c - a') fG b = ⟨b1, b2, 0⟩
  Φc' : hfΦ c b' (c - a') fG c' = ⟨r1, r2, 0⟩
  Φa : hfΦ c b' (c - a') fG a = ⟨a1, a2, a3⟩
  Φd : hfΦ c b' (c - a') fG d = ⟨s * b1, s * b2, m3⟩
  hzw0 : zw < 0
  hm : (1 - s) * zv < m3
  hAE : A = E
  cfg : N2Cfg0 E U zv zw A b1 b2 r1 r2 s m3 a1 a2 a3 FH FQab FQac FT1 FT2 FT3

variable {a a' b b' c c' d : ℝ³}

set_option maxHeartbeats 1000000 in
theorem n2_pic (F : OctFacets a a' b b' c c') (hd : IsCap F d)
    (hfar : F.abc'.f a' < F.abc'.f c) (hq₂ : F.ab'c'.f a' < F.ab'c'.f c)
    (htouch : ⟪b, c - a'⟫ = ⟪c', c - a'⟫ ∧ ⟪b', c - a'⟫ = ⟪c', c - a'⟫)
    (hzw0 : ⟪a', c - a'⟫ < ⟪b', c - a'⟫) (hzv0 : ⟪b', c - a'⟫ ≤ ⟪c, c - a'⟫) :
    ∃ (E U zv zw A b1 b2 r1 r2 s m3 a1 a2 a3 : ℝ) (FH FQab FQac FT1 FT2 FT3 : Fc),
      N2Pic a a' b b' c c' d F.a'b'c.f E U zv zw A b1 b2 r1 r2 s m3 a1 a2 a3 FH FQab FQac FT1 FT2 FT3 ∧
      E = ⟪hfE c b' (c - a'), hfE c b' (c - a')⟫ := by
  classical
  have hnd := F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨haa', hab, hab', hac, hac'⟩, ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩,
    ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd
  obtain ⟨hda, hda', hdb, hdb', hdc, hdc'⟩ := hd.ne
  obtain ⟨s, δ0, hs0, hs1, hδ0, hdeq⟩ := hd.middle_Qbc hfar
  have Fr := n2_frame F
  -- the frame
  set u0 : ℝ³ := c - a' with hu0
  set e : ℝ³ := hfE c b' u0 with he
  set fG : ℝ³ → ℝ := F.a'b'c.f with hfG
  set N : ℝ³ := F.a'b'c.N with hN
  -- the real coordinates
  set E : ℝ := ⟪e, e⟫ with hE
  set U : ℝ := ⟪u0, u0⟫ with hU
  set zv : ℝ := ⟪c - b', u0⟫ with hzv
  set zw : ℝ := ⟪a' - b', u0⟫ with hzw
  set A : ℝ := ⟪b' - c, e⟫ with hA
  set b1 : ℝ := ⟪b - c, e⟫ with hb1
  set b2 : ℝ := -fG b with hb2
  set r1 : ℝ := ⟪c' - c, e⟫ with hr1
  set r2 : ℝ := -fG c' with hr2
  set a1 : ℝ := ⟪a - c, e⟫ with ha1
  set a2 : ℝ := -fG a with ha2
  set a3 : ℝ := ⟪a - b', u0⟫ with ha3
  set m3 : ℝ := ⟪d - b', u0⟫ with hm3
  have heu : ⟪e, u0⟫ = 0 := Fr.inner_e_u
  have heu' : ⟪u0, e⟫ = 0 := by rw [real_inner_comm]; exact heu
  have hNe : ⟪N, e⟫ = 0 := Fr.inner_N_e
  have hNu : ⟪N, u0⟫ = 0 := Fr.hNu
  have hfGa' : fG a' = 0 := F.a'b'c.hP
  have hfGb' : fG b' = 0 := F.a'b'c.hQ
  have hfGc : fG c = 0 := F.a'b'c.hR
  have hZb : ⟪b - b', u0⟫ = 0 := by rw [inner_sub_left]; linarith [htouch.1, htouch.2]
  have hZc' : ⟪c' - b', u0⟫ = 0 := by rw [inner_sub_left]; linarith [htouch.1, htouch.2]
  have hbpc : b' - c = e + hfTau c b' u0 • u0 := by simp [he, hfE]
  have hAE : A = E := by
    rw [hA, hbpc, inner_add_left, real_inner_smul_left, heu', hE]; ring
  have hΦc : hfΦ c b' u0 fG c = ⟨0, 0, zv⟩ := by
    show (⟨⟪c - c, e⟫, -fG c, ⟪c - b', u0⟫⟩ : V3) = ⟨0, 0, zv⟩
    rw [hfGc, sub_self, inner_zero_left]; simp [hzv]
  have hΦa' : hfΦ c b' u0 fG a' = ⟨0, 0, zw⟩ := by
    show (⟨⟪a' - c, e⟫, -fG a', ⟪a' - b', u0⟫⟩ : V3) = ⟨0, 0, zw⟩
    have : a' - c = -u0 := by rw [hu0]; abel
    rw [hfGa', this, inner_neg_left, heu']; simp [hzw]
  have hΦb' : hfΦ c b' u0 fG b' = ⟨A, 0, 0⟩ := by
    show (⟨⟪b' - c, e⟫, -fG b', ⟪b' - b', u0⟫⟩ : V3) = ⟨A, 0, 0⟩
    rw [hfGb', sub_self, inner_zero_left]; simp [hA]
  have hΦb : hfΦ c b' u0 fG b = ⟨b1, b2, 0⟩ := by
    show (⟨⟪b - c, e⟫, -fG b, ⟪b - b', u0⟫⟩ : V3) = ⟨b1, b2, 0⟩
    rw [hZb]
  have hΦc' : hfΦ c b' u0 fG c' = ⟨r1, r2, 0⟩ := by
    show (⟨⟪c' - c, e⟫, -fG c', ⟪c' - b', u0⟫⟩ : V3) = ⟨r1, r2, 0⟩
    rw [hZc']
  have hΦa : hfΦ c b' u0 fG a = ⟨a1, a2, a3⟩ := rfl
  have hdc : d - c = s • (b - c) + δ0 • u0 := by rw [hdeq, hu0]; abel
  have hΦd : hfΦ c b' u0 fG d = ⟨s * b1, s * b2, m3⟩ := by
    show (⟨⟪d - c, e⟫, -fG d, ⟪d - b', u0⟫⟩ : V3) = ⟨s * b1, s * b2, m3⟩
    have h1 : ⟪d - c, e⟫ = s * b1 := by
      rw [hdc, inner_add_left, real_inner_smul_left, real_inner_smul_left, heu', hb1]; ring
    have h2 : fG d = s * fG b := by
      have := F.a'b'c.hN d c
      have h3 := F.a'b'c.hN b c
      rw [hdc, inner_add_right, real_inner_smul_right, real_inner_smul_right, hNu] at this
      rw [← F.a'b'c.hN b c] at this
      have : fG d - fG c = s * (fG b - fG c) := by linarith
      rw [hfGc] at this; linarith
    rw [h1, h2]
    simp [hb2]; ring
  -- positivity
  have hUpos : 0 < U := Fr.hu
  have hEpos : 0 < E := Fr.hee
  have hzvw : zv - zw = U := by
    rw [hzv, hzw, ← inner_sub_left]
    have : (c - b') - (a' - b') = u0 := by rw [hu0]; abel
    rw [this]
  have hzvnn : 0 ≤ zv := by
    have : zv = ⟪c, u0⟫ - ⟪b', u0⟫ := by rw [hzv, inner_sub_left]
    linarith
  have hzwneg : zw < 0 := by
    have : zw = ⟪a', u0⟫ - ⟪b', u0⟫ := by rw [hzw, inner_sub_left]
    linarith
  have hm3eq : m3 = (1 - s) * zv + δ0 * U := by
    have h1 : d - b' = (c - b') + (s • (b - c) + δ0 • u0) := by rw [← hdc]; abel
    have h2 : ⟪b - c, u0⟫ = -zv := by
      have : b - c = (b - b') - (c - b') := by abel
      rw [this, inner_sub_left, hZb, hzv]; ring
    rw [hm3, h1, inner_add_left, inner_add_left, real_inner_smul_left, real_inner_smul_left, h2, hzv, hU]
    ring
  have hm3gt : (1 - s) * zv < m3 := by
    rw [hm3eq]; nlinarith [mul_pos hδ0 hUpos]
  have hm3pos : 0 < m3 := by
    rw [hm3eq]; nlinarith [mul_pos hδ0 hUpos, mul_nonneg (show 0 ≤ 1 - s by linarith) hzvnn]
  have hb2pos : 0 < b2 := by
    rw [hb2]; have := F.a'b'c.neg b (by simp) (Ne.symm ha'b) hbb' hbc; linarith
  have hr2pos : 0 < r2 := by
    rw [hr2]; have := F.a'b'c.neg c' (by simp) (Ne.symm ha'c') (Ne.symm hb'c') (Ne.symm hcc'); linarith
  have ha2pos : 0 < a2 := by
    rw [ha2]; have := F.a'b'c.neg a (by simp) haa' hab' hac; linarith
  have hApos : 0 < A := by rw [hAE]; exact hEpos
  -- the shadow tests
  obtain ⟨E1, E2, E3, E4⟩ := quad_edge_tests_or F.swap₁.perm₂₃ hfar hq₂
  have hρc : crossXY (hfΦ c b' u0 fG c) (hfΦ c b' u0 fG b) (hfΦ c b' u0 fG b') = -(b2 * A) := by
    rw [hΦc, hΦb, hΦb']; simp only [crossXY]; ring
  have hρneg : -(b2 * A) ≤ 0 := neg_nonpos.mpr (mul_pos hb2pos hApos).le
  have hDr : (A - r1) * (b2 - r2) + r2 * (b1 - r1) < 0 := by
    have h := E3 b (by simp) hbc' hbb'
    have h2 := Fr.shadow_sign c b b' c' b' b h
    rw [hρc, hΦc', hΦb', hΦb] at h2
    have e : crossXY ⟨r1, r2, 0⟩ ⟨A, 0, 0⟩ ⟨b1, b2, 0⟩ =
        (A - r1) * (b2 - r2) + r2 * (b1 - r1) := by simp only [crossXY]; ring
    rw [e] at h2
    exact neg_of_mul_pos_right h2 hρneg
  have hTa1 : (A - r1) * (a2 - r2) + r2 * (a1 - r1) < 0 := by
    have h := E3 a (by simp) hac' hab'
    have h2 := Fr.shadow_sign c b b' c' b' a h
    rw [hρc, hΦc', hΦb', hΦa] at h2
    have e : crossXY ⟨r1, r2, 0⟩ ⟨A, 0, 0⟩ ⟨a1, a2, a3⟩ =
        (A - r1) * (a2 - r2) + r2 * (a1 - r1) := by simp only [crossXY]; ring
    rw [e] at h2
    exact neg_of_mul_pos_right h2 hρneg
  have hTa2 : (a1 - r1) * (b2 - r2) - (a2 - r2) * (b1 - r1) < 0 := by
    have h := E2 a (by simp) hab hac'
    have h2 := Fr.shadow_sign c b b' b c' a h
    rw [hρc, hΦb, hΦc', hΦa] at h2
    have e : crossXY ⟨b1, b2, 0⟩ ⟨r1, r2, 0⟩ ⟨a1, a2, a3⟩ =
        (a1 - r1) * (b2 - r2) - (a2 - r2) * (b1 - r1) := by simp only [crossXY]; ring
    rw [e] at h2
    exact neg_of_mul_pos_right h2 hρneg
  -- the facets
  have evq0 : ∀ (f : ℝ³ → ℝ) (Nf : ℝ³), (∀ y z, f y - f z = ⟪Nf, y - z⟫) → ∀ (p : ℝ³) (q : V3),
      hfΦ c b' u0 fG p = q → f p = 0 → (hfFc c b' u0 N f Nf).ev q = 0 := by
    intro f Nf hf p q hq h0
    rw [← hq, Fr.ev_hfΦ hf, h0]
  have evql : ∀ (f : ℝ³ → ℝ) (Nf : ℝ³), (∀ y z, f y - f z = ⟪Nf, y - z⟫) → ∀ (p : ℝ³) (q : V3),
      hfΦ c b' u0 fG p = q → f p < 0 → (hfFc c b' u0 N f Nf).ev q < 0 := by
    intro f Nf hf p q hq h0
    rw [← hq, Fr.ev_hfΦ hf]; exact h0
  have cfg : N2Cfg0 E U zv zw A b1 b2 r1 r2 s m3 a1 a2 a3
      (hfFc c b' u0 N F.a'bc.f F.a'bc.N) (hfFc c b' u0 N F.abc'.f F.abc'.N)
      (hfFc c b' u0 N F.ab'c.f F.ab'c.N) (hfFc c b' u0 N F.ab'c'.f F.ab'c'.N)
      (hfFc c b' u0 N F.a'bc'.f F.a'bc'.N) (hfFc c b' u0 N F.a'b'c'.f F.a'b'c'.N) := by
    refine ⟨hEpos, hUpos, hzvnn, by linarith, hApos, hb2pos, hr2pos, ha2pos, hs0, hs1, hm3pos,
      hDr, hTa1, hTa2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    -- H = a'bc
    · exact evq0 _ _ F.a'bc.hN d _ hΦd hd.a'bc
    · exact evq0 _ _ F.a'bc.hN b _ hΦb F.a'bc.hQ
    · exact evq0 _ _ F.a'bc.hN a' _ hΦa' F.a'bc.hP
    · exact evq0 _ _ F.a'bc.hN c _ hΦc F.a'bc.hR
    · exact evql _ _ F.a'bc.hN a _ hΦa (F.a'bc.neg a (by simp) haa' hab hac)
    · exact evql _ _ F.a'bc.hN b' _ hΦb' (F.a'bc.neg b' (by simp) (Ne.symm ha'b') (Ne.symm hbb') hb'c)
    · exact evql _ _ F.a'bc.hN c' _ hΦc' (F.a'bc.neg c' (by simp) (Ne.symm ha'c') (Ne.symm hbc') (Ne.symm hcc'))
    -- Qab = abc'
    · exact evq0 _ _ F.abc'.hN d _ hΦd hd.abc'
    · exact evq0 _ _ F.abc'.hN a _ hΦa F.abc'.hP
    · exact evq0 _ _ F.abc'.hN c' _ hΦc' F.abc'.hR
    · exact evq0 _ _ F.abc'.hN b _ hΦb F.abc'.hQ
    · exact evql _ _ F.abc'.hN c _ hΦc (F.abc'.neg c (by simp) (Ne.symm hac) (Ne.symm hbc) hcc')
    · exact evql _ _ F.abc'.hN a' _ hΦa' (F.abc'.neg a' (by simp) (Ne.symm haa') ha'b ha'c')
    · exact evql _ _ F.abc'.hN b' _ hΦb' (F.abc'.neg b' (by simp) (Ne.symm hab') (Ne.symm hbb') hb'c')
    -- Qac = ab'c
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
  exact ⟨E, U, zv, zw, A, b1, b2, r1, r2, s, m3, a1, a2, a3, _, _, _, _, _, _,
    ⟨hΦc, hΦa', hΦb', hΦb, hΦc', hΦa, hΦd, hzwneg, hm3gt, hAE, cfg⟩, rfl⟩

end Type08Sp
end Minimality
