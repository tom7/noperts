module

public import Minimality.Type29TwoFace
public import Minimality.VtxLimit

@[expose] public section

/-!
# Type 29: the one-circle vertex closings T1 and T2 (`FEWER-FACES-PROOFS.md` §22.3–22.10, §28)

The vertex lines `012/1456` (T1) and `1456/234` (T2) are seen along a triangle and the quad
`1456`, whose far end (`6` for T1, `5` for T2) is opposite to the apex: the closing is realized on
the quad's circle only.  At the limit it is closed by `isRupert_vtx_limit` (Theorem 22.8,
Lemma 22.10), where the class-d condition `⟪N_Q, c⟫ = ⟪N_Q, b⟫` is excluded by the region facts
carried by the certificate (Lemma 28.8, the paper's K.2).

* `Facets29.toInjNoSeg`: the generic lemmas `quad_offsets`, `quad_middles`, `isRupert_vSector`,
  `isRupert_vTriLim` of type 21's `V` (`Type21Vtx.lean`), stated for `InjNoSeg`, apply to type 29.
* `isRupert_T2quad29`: the four-corner rims `(4, 3, 0, 5)`, `(4, 2, 0, 5)` of T2; the class-d
  condition fails by the carried region facts (Lemma 28.8).
* `isRupert_T2tri29`: the triangle rim `(4, 3, 5)` of T2 (a sector rim, Lemma 22.6 (b)).
* `isRupert_T1_29`, `T1_h4esc`, `T1_esc_P14`, `T1_esc_P11`: the rim `(1, 2, 3, 6)` of T1: (H4)
  for the upper middle and the escape for the lower one (Lemma 28.7).
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000
set_option synthInstance.maxSize 1000

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

variable {x : Fin 7 → ℝ³}

/-- The facets of a type-29 shape give the injectivity and segment facts of `InjNoSeg`. -/
def Facets29.toInjNoSeg (T : Facets29 x) : InjNoSeg x := ⟨T.inj, T.noSeg⟩

/-! ### T2: the four-corner rims `(4, b, 0, 5)` -/

/-- **T2's quadrilateral rims at the limit** (Lemma 18.2 with Theorem 22.8): the rim
`(4, b, 0, 5)` at the vertex line `234/1456` (`b ∈ {3, 2}`, `m` the third vertex of `234`) read
backwards is `(v, a, c, b) = (4, 5, 0, b)`, the quad `1456` with chord `[4, 5]` and the triangle
`234`.  Under `VtxGen` at the view, if `0` and `b` are at different heights over the quad
(`hcb`: the class-d condition of Lemma 28.8 fails) then no (H4)/escape is needed, and the limit
is Rupert. -/
theorem isRupert_T2quad29 (N : NF29 x) {b m : Fin 7}
    (hnd1 : [4, 5, 0, b, 1, 6, m].Nodup) (hnd2 : [4, 5, 0, b, 6, 1, m].Nodup)
    (hSb : ({2, 3, 4} : Finset (Fin 7)) = {4, b, m})
    (hcb : ⟪N.f1456.N, x 0⟫ ≠ ⟪N.f1456.N, x b⟫)
    (K : ℕ → Fin 7 → ℝ³) (hK : ∀ i, Tendsto (fun n => K n i) atTop (𝓝 (x i))) (ε : Bool)
    (hgen : VtxGen (univ.image x) (view29 x (.inr 1)) (({1, 4, 5, 6} : Finset (Fin 7)).image x)
      (({2, 3, 4} : Finset (Fin 7)).image x) N.f1456.N)
    (hc : ∃ᶠ n in atTop, RimCertAt (K n) (sgnB ε • view29 (K n) (.inr 1)) (quad 4 b 0 5) ∧
      TiesAt29 x (K n)) : IsRupert (univ.image x) := by
  have hs := sgnB_ne_zero ε
  have hw0 : view29 x (.inr 1) ≠ 0 := N.view29_ne_zero _ (by simp)
  have hc0 : -sgnB ε ≠ 0 := neg_ne_zero.mpr hs
  have hcε : -sgnB ε = 1 ∨ -sgnB ε = -1 := by
    rcases sgnB_cases ε with h | h <;> simp [h]
  have hg := hgen.sign hcε
  have hu : (-sgnB ε) • view29 x (.inr 1) ≠ 0 := smul_ne_zero hc0 hw0
  have mem : ∀ i, x i ∈ univ.image x := fun i => mem_image_of_mem x (mem_univ i)
  have hwQ : ⟪N.f1456.N, view29 x (.inr 1)⟫ = 0 :=
    inner_planeLine_right (N.f1456.inner_sub (by decide) (by decide))
      (N.f1456.inner_sub (by decide) (by decide))
  have hwT : ⟪N.f234.N, view29 x (.inr 1)⟫ = 0 :=
    inner_planeLine_left (N.f234.inner_sub (by decide) (by decide))
      (N.f234.inner_sub (by decide) (by decide))
  have hNa : ⟪N.f1456.N, (-sgnB ε) • view29 x (.inr 1)⟫ = 0 := by
    rw [real_inner_smul_right, hwQ, mul_zero]
  have hNb : ⟪N.f234.N, (-sgnB ε) • view29 x (.inr 1)⟫ = 0 := by
    rw [real_inner_smul_right, hwT, mul_zero]
  have hfreq : ∃ᶠ n in atTop, RimCertPts (univ.image (K n)) ((-sgnB ε) • view29 (K n) (.inr 1))
      (quad (K n 4) (K n 5) (K n 0) (K n b)) := hc.mono fun n hn => by
    have h1 := hn.1.rev4.toPts
    rw [quad_map, ← neg_smul] at h1
    exact h1
  have hNQ : N.f1456.N ≠ 0 := N.f1456.N_ne (i := 4) (j := 0) (by decide) (by decide)
  have hcu : cross (x 5 - x 4) ((-sgnB ε) • view29 x (.inr 1)) ≠ 0 :=
    hg.par _ (mem 4) _ (mem 5) (N.inj.ne (by decide))
  obtain ⟨s1, δ1, h1⟩ := EdgeConf.exists_coords_of_perp (N.f1456.inner_sub (by decide : 5 ∈
    ({1, 4, 5, 6} : Finset (Fin 7))) (by decide : 4 ∈ ({1, 4, 5, 6} : Finset (Fin 7)))) hNa
    (N.f1456.inner_sub (by decide : 1 ∈ ({1, 4, 5, 6} : Finset (Fin 7)))
      (by decide : 4 ∈ ({1, 4, 5, 6} : Finset (Fin 7)))) hcu hNQ
  obtain ⟨s6, δ6, h6⟩ := EdgeConf.exists_coords_of_perp (N.f1456.inner_sub (by decide : 5 ∈
    ({1, 4, 5, 6} : Finset (Fin 7))) (by decide : 4 ∈ ({1, 4, 5, 6} : Finset (Fin 7)))) hNa
    (N.f1456.inner_sub (by decide : 6 ∈ ({1, 4, 5, 6} : Finset (Fin 7)))
      (by decide : 4 ∈ ({1, 4, 5, 6} : Finset (Fin 7)))) hcu hNQ
  have hx1 : x 1 = x 4 + s1 • (x 5 - x 4) + δ1 • ((-sgnB ε) • view29 x (.inr 1)) := by
    linear_combination (norm := module) h1
  have hx6 : x 6 = x 4 + s6 • (x 5 - x 4) + δ6 • ((-sgnB ε) • view29 x (.inr 1)) := by
    linear_combination (norm := module) h6
  have hδ : δ1 * δ6 < 0 := quad_offsets N.facets.toInjNoSeg N.f1456 N.f124 N.f346
    (v := 4) (a := 5) (b := 0) (m₁ := 1) (m₂ := 6)
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
      by decide, by decide, by decide, by decide, by decide⟩ (by decide) hg.par hx1 hx6
  have hfa := N.f1456.hf (i₀ := 4) (by decide)
  have hfb := N.f234.hf (i₀ := 4) (by decide)
  have hδ1 : δ1 ≠ 0 := by rintro rfl; simp at hδ
  rcases lt_or_gt_of_ne hδ1 with hneg | hpos
  · have hδ6 : 0 < δ6 := pos_of_mul_neg_right hδ hneg.le
    exact isRupert_vtx_limit x N.inj N.noSeg (v := 4) (a := 5) (c := 0) (b := b) (p := 6)
      (q := 1) (m := m) hnd2 (Sa := {1, 4, 5, 6}) (Sb := {2, 3, 4}) (by decide) hSb hfa hfb hu
      hNa hNb ⟨s6, δ6, hδ6, hx6⟩ ⟨s1, δ1, hneg, hx1⟩ K hK
      (fun n => (-sgnB ε) • view29 (K n) (.inr 1)) ((tendsto_view29 hK _).const_smul _) hfreq hg
      (fun _ hcb' => absurd hcb' hcb)
  · have hδ6 : δ6 < 0 := neg_of_mul_neg_right hδ hpos.le
    exact isRupert_vtx_limit x N.inj N.noSeg (v := 4) (a := 5) (c := 0) (b := b) (p := 1)
      (q := 6) (m := m) hnd1 (Sa := {1, 4, 5, 6}) (Sb := {2, 3, 4}) (by decide) hSb hfa hfb hu
      hNa hNb ⟨s1, δ1, hpos, hx1⟩ ⟨s6, δ6, hδ6, hx6⟩ K hK
      (fun n => (-sgnB ε) • view29 (K n) (.inr 1)) ((tendsto_view29 hK _).const_smul _) hfreq hg
      (fun _ hcb' => absurd hcb' hcb)

/-! ### T2: the triangle rim `(4, 3, 5)` -/

/-- **T2's triangle rim at the limit** (Lemma 18.2, Proposition 22.2 for a sector rim, Lemma
22.6 (b)): the rim `(4, 3, 5)` at the vertex line `234/1456`, read backwards `(v, a, b) = (4, 5, 3)`
with the quad `1456` and the triangle `234` (`n = 2`); at the limit, with no two points over one
point, (G1) and distinct depths, the limit is Rupert whatever its horizontal double normals. -/
theorem isRupert_T2tri29 (N : NF29 x) (K : ℕ → Fin 7 → ℝ³)
    (hK : ∀ i, Tendsto (fun n => K n i) atTop (𝓝 (x i))) (ε : Bool)
    (hgen : TwoGen29 (univ.image x) (view29 x (.inr 1)) (({1, 4, 5, 6} : Finset (Fin 7)).image x)
      (({2, 3, 4} : Finset (Fin 7)).image x))
    (hc : ∃ᶠ n in atTop, RimCertAt (K n) (sgnB ε • view29 (K n) (.inr 1)) (tri 4 3 5) ∧
      TiesAt29 x (K n)) : IsRupert (univ.image x) := by
  have hs := sgnB_ne_zero ε
  have hw0 : view29 x (.inr 1) ≠ 0 := N.view29_ne_zero _ (by simp)
  have hc0 : -sgnB ε ≠ 0 := neg_ne_zero.mpr hs
  have hcε : -sgnB ε = 1 ∨ -sgnB ε = -1 := by
    rcases sgnB_cases ε with h | h <;> simp [h]
  have hg := hgen.sign hcε
  have hwQ : ⟪N.f1456.N, view29 x (.inr 1)⟫ = 0 :=
    inner_planeLine_right (N.f1456.inner_sub (by decide) (by decide))
      (N.f1456.inner_sub (by decide) (by decide))
  have hQu : ⟪N.f1456.N, (-sgnB ε) • view29 x (.inr 1)⟫ = 0 := by
    rw [real_inner_smul_right, hwQ, mul_zero]
  have hfreq : ∃ᶠ n in atTop, RimCertPts (univ.image (K n)) ((-sgnB ε) • view29 (K n) (.inr 1))
      (tri (K n 4) (K n 5) (K n 3)) := hc.mono fun n hn => by
    have h1 := hn.1.rev3.toPts
    rw [tri_map, ← neg_smul] at h1
    exact h1
  exact isRupert_vTriLim N.facets.toInjNoSeg N.f1456 N.f234 N.f124 N.f346
    (v := 4) (a := 5) (b := 3) (n := 2) (m₁ := 1) (m₂ := 6)
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
      by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
      by decide, by decide, by decide, by decide, by decide⟩ (by decide)
    (smul_ne_zero hc0 hw0) hQu (fun n => (-sgnB ε) • view29 (K n) (.inr 1))
    ((tendsto_view29 hK _).const_smul _) K hK hfreq hg.par hg.g1 hg.dist

/-! ### T1: the four-corner rim `(1, 2, 3, 6)` at `012/1456` -/

theorem lt_of_neg_mul_lt {k a b : ℝ} (hk : 0 < k) (h : -k * a < -k * b) : b < a := by
  nlinarith

/-- **(H4) and the escape for T1 on `{h2 = 1}`** (Lemma 28.7).  For the view `u = r • vT1`
(`vT1 = u1`), with `h2 = 1`, `l = a2 t − b2 s < 0` and the escape `hesc` at `u1` (the pattern
`z5 < z1`, `z2 < z1`, `z1 < z6`, `z1 < z3` of Lemma 22.9 for the lower middle `5` is impossible):
the upper middle `4` shown in the sense `s` (`s r > 0`) has (H4) (the product of the plane
`6 3 2` at `1` and at `u` is `−l · (a0 b2 − a2 b0) · D² > 0`), and the other middle `5`, shown in
the opposite sense, has the escape. -/
theorem T1_h4esc (N : NF29 x) (hh : N.h2 = 1) (hl : 0 < -N.a2 * N.t + N.b2 * N.s)
    (hesc : ¬ (⟪x 5, N.vT1⟫ < ⟪x 1, N.vT1⟫ ∧ ⟪x 2, N.vT1⟫ < ⟪x 1, N.vT1⟫ ∧
      ⟪x 1, N.vT1⟫ < ⟪x 6, N.vT1⟫ ∧ ⟪x 1, N.vT1⟫ < ⟪x 3, N.vT1⟫))
    {r s : ℝ} (hsr : 0 < s * r) :
    VtxConf.H4orEsc (r • N.vT1) (x 1) (x 6) (x 3) (x 2) (x 4) s ∧
      VtxConf.H4orEsc (r • N.vT1) (x 1) (x 6) (x 3) (x 2) (x 5) (-s) := by
  have key1 : det3 (x 3 - x 6) (x 2 - x 6) (x 1 - x 6) * det3 (x 3 - x 6) (x 2 - x 6) N.vT1 =
      ((-N.a2 * N.t + N.b2 * N.s) * (N.a0 * N.b2 - N.a2 * N.b0)) * N.D ^ 2 := by
    simp only [NF29.vT1]; nf29_simp N; simp only [det3c, NF29.D]; rw [hh]; ring
  have hpos : 0 < det3 (x 3 - x 6) (x 2 - x 6) (x 1 - x 6) *
      det3 (x 3 - x 6) (x 2 - x 6) N.vT1 := by
    rw [key1]
    have hD0 : N.D ≠ 0 := N.hD
    exact mul_pos (mul_pos hl N.hDD) (by positivity : (0:ℝ) < N.D ^ 2)
  refine ⟨Or.inl (Or.inl ?_), Or.inr fun hpat => hesc ?_⟩
  · rw [det3_smul_right]
    have e : det3 (x 3 - x 6) (x 2 - x 6) (x 1 - x 6) *
        (s * (r * det3 (x 3 - x 6) (x 2 - x 6) N.vT1)) =
        (s * r) * (det3 (x 3 - x 6) (x 2 - x 6) (x 1 - x 6) *
          det3 (x 3 - x 6) (x 2 - x 6) N.vT1) := by ring
    rw [e]; exact mul_pos hsr hpos
  · obtain ⟨p1, p2, p3, p4⟩ := hpat
    simp only [real_inner_smul_right] at p1 p2 p3 p4
    have hk : 0 < s * r := hsr
    have q : ∀ {a b : ℝ}, -s * (r * a) < -s * (r * b) → b < a := fun {a b} h =>
      lt_of_neg_mul_lt hk (by
        have e1 : -(s * r) * a = -s * (r * a) := by ring
        have e2 : -(s * r) * b = -s * (r * b) := by ring
        rw [e1, e2]; exact h)
    exact ⟨q p1, q p2, q p3, q p4⟩

/-- **The escape for T1 in P14** (Lemma 28.7 (b)): at `h2 = 1` the view `u2 = vT2` of the partner
is `3 − 2`, so the carried fact `⟪vT1, vT2⟫ ≤ 0` (`0 ≤ ⟪w₀, w₁⟫` for the named views) gives
`z3 ≤ z2` along `vT1`, against the pattern `z2 < z1 < z3` of Lemma 22.9. -/
theorem T1_esc_P14 (N : NF29 x) (hh : N.h2 = 1)
    (hex : 0 ≤ ⟪view29 x (.inr 0), view29 x (.inr 1)⟫) :
    ¬ (⟪x 5, N.vT1⟫ < ⟪x 1, N.vT1⟫ ∧ ⟪x 2, N.vT1⟫ < ⟪x 1, N.vT1⟫ ∧
      ⟪x 1, N.vT1⟫ < ⟪x 6, N.vT1⟫ ∧ ⟪x 1, N.vT1⟫ < ⟪x 3, N.vT1⟫) := by
  rintro ⟨-, h2z, -, h3z⟩
  have w0 : view29 x (.inr 0) = N.D • N.vT1 := by
    rw [show view29 x (.inr 0) = vtxView29 x 0 from rfl, N.vtxView29_0, one_mul]
  have w1 : view29 x (.inr 1) = (-N.D) • N.vT2 := by
    rw [show view29 x (.inr 1) = vtxView29 x 1 from rfl, N.vtxView29_1, neg_one_mul]
  have hv : N.vT2 = x 3 - x 2 := by
    simp only [NF29.vT2]; nf29_simp N; rw [hh]
    ext; simp only [nfP, nfV, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, PiLp.neg_apply,
      PiLp.zero_apply, WithLp.ofLp_zero, Pi.zero_apply, smul_eq_mul]; ring
  rw [w0, w1, real_inner_smul_left, real_inner_smul_right, hv, inner_sub_right,
    real_inner_comm (x 3), real_inner_comm (x 2)] at hex
  have hD2 : 0 < N.D * N.D := mul_self_pos.mpr N.hD
  nlinarith [mul_pos hD2 (sub_pos.mpr (h2z.trans h3z))]

/-- **The escape for T1 in P11**: the view `vT3` of the partner is
`h0 (1 − 2) + α vT1 + β (6 − 1)` with `α, β > 0` (a polynomial identity), so the carried fact
`⟪vT1, vT3⟫ ≤ 0` is incompatible with the pattern `z2 < z1 < z6` of Lemma 22.9. -/
theorem T1_esc_P11 (N : NF29 x) (hex : ⟪view29 x (.inr 0), view29 x (.inr 3)⟫ ≤ 0) :
    ¬ (⟪x 5, N.vT1⟫ < ⟪x 1, N.vT1⟫ ∧ ⟪x 2, N.vT1⟫ < ⟪x 1, N.vT1⟫ ∧
      ⟪x 1, N.vT1⟫ < ⟪x 6, N.vT1⟫ ∧ ⟪x 1, N.vT1⟫ < ⟪x 3, N.vT1⟫) := by
  rintro ⟨-, h2z, h6z, -⟩
  have w0 : view29 x (.inr 0) = N.D • N.vT1 := by
    rw [show view29 x (.inr 0) = vtxView29 x 0 from rfl, N.vtxView29_0, one_mul]
  have w3 : view29 x (.inr 3) = N.D • N.vT3 := by
    rw [show view29 x (.inr 3) = vtxView29 x 3 from rfl, N.vtxView29_3, one_mul]
  have hvec : ((N.h0 * N.a2 - N.h2 * N.a0) * N.t + (N.h2 * N.b0 - N.h0 * N.b2) * N.s) •
      N.vT3 = (((N.h0 * N.a2 - N.h2 * N.a0) * N.t + (N.h2 * N.b0 - N.h0 * N.b2) * N.s) * N.h0) •
        (x 1 - x 2) + ((N.h0 * N.a2 - N.h2 * N.a0) * N.t) • N.vT1 +
        ((N.h2 * N.b0 - N.h0 * N.b2) * (N.h0 * N.a2 - N.h2 * N.a0)) • (x 6 - x 1) := by
    simp only [NF29.vT3, NF29.vT1]; nf29_vec N
  have hF5 := N.hF5
  have hF4 := N.hF4
  have hf : 0 < (N.h0 * N.a2 - N.h2 * N.a0) * N.t + (N.h2 * N.b0 - N.h0 * N.b2) * N.s :=
    add_pos (mul_pos hF5 N.ht) (mul_pos hF4 N.hs)
  have hn : 0 < ⟪N.vT1, N.vT1⟫ :=
    real_inner_self_pos.mpr (nfV_ne_zero N.hD (Or.inl (ne_of_gt N.hF5)))
  rw [w0, w3, real_inner_smul_left, real_inner_smul_right] at hex
  have hD2 : 0 < N.D * N.D := mul_self_pos.mpr N.hD
  have h13 : ⟪N.vT1, N.vT3⟫ ≤ 0 := by
    by_contra h; push Not at h; nlinarith [mul_pos hD2 h]
  have key := congrArg (fun w => ⟪N.vT1, w⟫) hvec
  simp only [inner_add_right, real_inner_smul_right, inner_sub_right] at key
  have h2z' : ⟪N.vT1, x 2⟫ < ⟪N.vT1, x 1⟫ := by
    rw [real_inner_comm (x 2) N.vT1, real_inner_comm (x 1) N.vT1]; exact h2z
  have h6z' : ⟪N.vT1, x 1⟫ < ⟪N.vT1, x 6⟫ := by
    rw [real_inner_comm (x 1) N.vT1, real_inner_comm (x 6) N.vT1]; exact h6z
  have p1 : 0 < ((N.h0 * N.a2 - N.h2 * N.a0) * N.t + (N.h2 * N.b0 - N.h0 * N.b2) * N.s) *
      N.h0 * (⟪N.vT1, x 1⟫ - ⟪N.vT1, x 2⟫) := mul_pos (mul_pos hf N.hh0) (by linarith [h2z'])
  have p2 : 0 < (N.h0 * N.a2 - N.h2 * N.a0) * N.t * ⟪N.vT1, N.vT1⟫ :=
    mul_pos (mul_pos hF5 N.ht) hn
  have p3 : 0 < (N.h2 * N.b0 - N.h0 * N.b2) * (N.h0 * N.a2 - N.h2 * N.a0) *
      (⟪N.vT1, x 6⟫ - ⟪N.vT1, x 1⟫) := mul_pos (mul_pos hF4 hF5) (by linarith [h6z'])
  nlinarith [mul_nonneg hf.le (neg_nonneg.mpr h13)]

/-- **T1's quadrilateral rim at the limit** (Lemma 18.2 with Theorem 22.8, Lemma 28.7).  The rim
`(1, 2, 3, 6)` at the vertex line `012/1456`, read backwards `(v, a, c, b) = (1, 6, 3, 2)`: the
quad `1456` (chord `[1, 6]`, middles `4`, `5` on opposite sides) and the triangle `012`
(`m = 0`).  Where the far edge `[3, 2]` is parallel to the quad (`h2 = 1`), (H4) holds for the
upper middle (`l = a2 t − b2 s < 0`: `hl`) and the lower middle has the escape `hesc`. -/
theorem isRupert_T1_29 (N : NF29 x) (K : ℕ → Fin 7 → ℝ³)
    (hK : ∀ i, Tendsto (fun n => K n i) atTop (𝓝 (x i))) (ε : Bool)
    (hgen : VtxGen (univ.image x) (view29 x (.inr 0)) (({1, 4, 5, 6} : Finset (Fin 7)).image x)
      (({0, 1, 2} : Finset (Fin 7)).image x) N.f1456.N)
    (hl : N.h2 = 1 → 0 < -N.a2 * N.t + N.b2 * N.s)
    (hesc : N.h2 = 1 → ¬ (⟪x 5, N.vT1⟫ < ⟪x 1, N.vT1⟫ ∧ ⟪x 2, N.vT1⟫ < ⟪x 1, N.vT1⟫ ∧
      ⟪x 1, N.vT1⟫ < ⟪x 6, N.vT1⟫ ∧ ⟪x 1, N.vT1⟫ < ⟪x 3, N.vT1⟫))
    (hc : ∃ᶠ n in atTop, RimCertAt (K n) (sgnB ε • view29 (K n) (.inr 0)) (quad 1 2 3 6) ∧
      TiesAt29 x (K n)) : IsRupert (univ.image x) := by
  have hs := sgnB_ne_zero ε
  have hc0 : -sgnB ε ≠ 0 := neg_ne_zero.mpr hs
  have hcε : -sgnB ε = 1 ∨ -sgnB ε = -1 := by
    rcases sgnB_cases ε with h | h <;> simp [h]
  have hD := N.hD
  have hw : view29 x (.inr 0) = N.D • N.vT1 := by
    rw [show view29 x (.inr 0) = vtxView29 x 0 from rfl, N.vtxView29_0, one_mul]
  have hu_eq : (-sgnB ε) • view29 x (.inr 0) = ((-sgnB ε) * N.D) • N.vT1 := by
    rw [hw, smul_smul]
  have hr0 : (-sgnB ε) * N.D ≠ 0 := mul_ne_zero hc0 hD
  have hg0 := hgen.sign hcε
  rw [hu_eq] at hg0
  have hvT : N.vT1 ≠ 0 := nfV_ne_zero N.hD (Or.inl (ne_of_gt N.hF5))
  have hwQ : ⟪N.f1456.N, view29 x (.inr 0)⟫ = 0 :=
    inner_planeLine_right (N.f1456.inner_sub (by decide) (by decide))
      (N.f1456.inner_sub (by decide) (by decide))
  have hwT : ⟪N.f012.N, view29 x (.inr 0)⟫ = 0 :=
    inner_planeLine_left (N.f012.inner_sub (by decide) (by decide))
      (N.f012.inner_sub (by decide) (by decide))
  have hNa : ⟪N.f1456.N, ((-sgnB ε) * N.D) • N.vT1⟫ = 0 := by
    rw [← hu_eq, real_inner_smul_right, hwQ, mul_zero]
  have hNb : ⟪N.f012.N, ((-sgnB ε) * N.D) • N.vT1⟫ = 0 := by
    rw [← hu_eq, real_inner_smul_right, hwT, mul_zero]
  have hu : ((-sgnB ε) * N.D) • N.vT1 ≠ 0 := smul_ne_zero hr0 hvT
  have hfreq : ∃ᶠ n in atTop, RimCertPts (univ.image (K n))
      ((-sgnB ε) • view29 (K n) (.inr 0)) (quad (K n 1) (K n 6) (K n 3) (K n 2)) :=
    hc.mono fun n hn => by
      have h1 := hn.1.rev4.toPts
      rw [quad_map, ← neg_smul] at h1
      exact h1
  have hus : Tendsto (fun n => (-sgnB ε) • view29 (K n) (.inr 0)) atTop
      (𝓝 (((-sgnB ε) * N.D) • N.vT1)) := by
    rw [← hu_eq]; exact (tendsto_view29 hK _).const_smul _
  -- the middles `4`, `5` over the chord `[1, 6]` in the direction `vT1`
  obtain ⟨f, hfdef⟩ : ∃ f : ℝ, f = (N.h0 * N.a2 - N.h2 * N.a0) * N.t +
      (N.h2 * N.b0 - N.h0 * N.b2) * N.s := ⟨_, rfl⟩
  have hf : 0 < f := by
    rw [hfdef]; exact add_pos (mul_pos N.hF5 N.ht) (mul_pos N.hF4 N.hs)
  have e4 : f • (x 4 - x 1) = (N.h2 * N.b0 - N.h0 * N.b2) • (x 6 - x 1) + N.t • N.vT1 := by
    rw [hfdef]; simp only [NF29.vT1]; nf29_vec N
  have e5 : f • (x 5 - x 1) = (N.h0 * N.a2 - N.h2 * N.a0) • (x 6 - x 1) + (-N.s) • N.vT1 := by
    rw [hfdef]; simp only [NF29.vT1]; nf29_vec N
  have hfa := N.f1456.hf (i₀ := 1) (by decide)
  have hfb := N.f012.hf (i₀ := 1) (by decide)
  have hh_of : ⟪N.f1456.N, x 3⟫ = ⟪N.f1456.N, x 2⟫ → N.h2 = 1 := fun hcb => by
    have h01 := N.f1456_eq hcb
    simp only [Matrix.cons_val_zero, Matrix.cons_val] at h01
    linarith
  set r : ℝ := (-sgnB ε) * N.D with hrdef
  have hx4 : x 4 = x 1 + ((N.h2 * N.b0 - N.h0 * N.b2) / f) • (x 6 - x 1) +
      ((N.t / r) / f) • (r • N.vT1) := by
    refine eq_comb_div (D₀ := f) hf.ne' ?_
    rw [e4, smul_smul, div_mul_cancel₀ _ hr0]
  have hx5 : x 5 = x 1 + ((N.h0 * N.a2 - N.h2 * N.a0) / f) • (x 6 - x 1) +
      (((-N.s) / r) / f) • (r • N.vT1) := by
    refine eq_comb_div (D₀ := f) hf.ne' ?_
    rw [e5, smul_smul, div_mul_cancel₀ _ hr0]
  have hF4f : 0 < N.t / f := div_pos N.ht hf
  rcases lt_or_gt_of_ne hr0 with hneg | hpos
  · -- `r < 0`: `5` is above, `4` below
    have hδ5 : 0 < ((-N.s) / r) / f := div_pos (div_pos_of_neg_of_neg (by linarith [N.hs]) hneg) hf
    have hδ4 : (N.t / r) / f < 0 := div_neg_of_neg_of_pos (div_neg_of_pos_of_neg N.ht hneg) hf
    exact isRupert_vtx_limit x N.inj N.noSeg (v := 1) (a := 6) (c := 3) (b := 2) (p := 5)
      (q := 4) (m := 0) (by decide) (Sa := {1, 4, 5, 6}) (Sb := {0, 1, 2}) (by decide)
      (by decide) hfa hfb hu hNa hNb ⟨_, _, hδ5, hx5⟩ ⟨_, _, hδ4, hx4⟩ K hK
      (fun n => (-sgnB ε) • view29 (K n) (.inr 0)) hus hfreq hg0 (fun _ hcb => by
        have hh := hh_of hcb
        obtain ⟨A, B⟩ := T1_h4esc N hh (hl hh) (hesc hh) (r := r) (s := -1) (by linarith)
        exact ⟨by simpa using B, A⟩)
  · -- `r > 0`: `4` is above, `5` below
    have hδ4 : 0 < (N.t / r) / f := div_pos (div_pos N.ht hpos) hf
    have hδ5 : ((-N.s) / r) / f < 0 :=
      div_neg_of_neg_of_pos (div_neg_of_neg_of_pos (by linarith [N.hs]) hpos) hf
    exact isRupert_vtx_limit x N.inj N.noSeg (v := 1) (a := 6) (c := 3) (b := 2) (p := 4)
      (q := 5) (m := 0) (by decide) (Sa := {1, 4, 5, 6}) (Sb := {0, 1, 2}) (by decide)
      (by decide) hfa hfb hu hNa hNb ⟨_, _, hδ4, hx4⟩ ⟨_, _, hδ5, hx5⟩ K hK
      (fun n => (-sgnB ε) • view29 (K n) (.inr 0)) hus hfreq hg0 (fun _ hcb => by
        have hh := hh_of hcb
        obtain ⟨A, B⟩ := T1_h4esc N hh (hl hh) (hesc hh) (r := r) (s := 1) (by linarith)
        exact ⟨by simpa using A, by simpa using B⟩)

end Minimality

end
