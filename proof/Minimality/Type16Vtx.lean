module

public import Minimality.Type16Edge
public import Minimality.VtxLimit

@[expose] public section

/-!
# Type 16: no horizontal-double-normal exception at the lines `0235/046`, `1356/046` (§22.9)

The certificate of the cover at the view along the line of `0235/046` is Lemma 19.5's `T_a`, the
vertex crossing at `0` with the rim `(0, 5, 1, 6)` (and its `σ`-image at `1356/046`, rim
`(6, 5, 2, 0)`).  `0235` is a quadrilateral with `0` and its far end `5` opposite, so its middles
`2`, `3` lie on opposite sides of the chord `[0, 5]`; `046` is a triangle.  The closing is realized
on `0235`'s circle only; at the limit (Lemma 18.2) §22 closes it (`isRupert_vtx_limit`: Lemma
22.3, class `c` by Lemma 22.4, class `d` by Lemma 22.9 with Theorem 22.8 (middle `2`) or Lemma
22.10 (middle `3`)), under the codimension-2 conditions `VtxGen` at the view.  (H4) for the
middle `2` follows from `3` lying on the facet `1356 ∋ 5, 1, 6` (`VtxConf.hD_of_copl`).

* `VtxOK2`, `VtxOK5`: the conditions at the two views.
* `isRupert_pVtx2`, `isRupert_pVtx5`.
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

/-- Normalize the multiple of the view to a sign. -/
theorem freq_sign {ι : Type*} {l : Filter ι} {P : ℝ → ι → Prop}
    (hP : ∀ t c, c ≠ 0 → P c t → P (|c|⁻¹ * c) t)
    (h : ∃ᶠ t in l, ∃ c : ℝ, c ≠ 0 ∧ P c t) :
    ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧ ∃ᶠ t in l, P ε t := by
  have h' : ∃ᶠ t in l, ∃ s : Bool, P (if s then 1 else -1) t := h.mono fun t ⟨c, hc, hct⟩ => by
    have := hP t c hc hct
    rcases lt_or_gt_of_ne hc with hneg | hpos
    · refine ⟨false, ?_⟩
      have e : |c|⁻¹ * c = -1 := by rw [abs_of_neg hneg]; field_simp
      rw [e] at this; simpa using this
    · refine ⟨true, ?_⟩
      have e : |c|⁻¹ * c = 1 := by rw [abs_of_pos hpos]; field_simp
      rw [e] at this; simpa using this
  obtain ⟨s, hs⟩ := frequently_exists_of_finite h'
  cases s
  · exact ⟨-1, Or.inr rfl, by simpa using hs⟩
  · exact ⟨1, Or.inl rfl, by simpa using hs⟩

theorem rimCertPts_normalize {V : Finset ℝ³} {u : ℝ³} {k : ℕ} {y : ZMod k → ℝ³} {c : ℝ}
    (hc : c ≠ 0) (h : RimCertPts V (c • u) y) : RimCertPts V ((|c|⁻¹ * c) • u) y := by
  have := h.smul (inv_pos.mpr (abs_pos.mpr hc))
  rwa [smul_smul] at this

/-- **The codimension-2 conditions at the view along `0235/046`** (`VtxGen` at the named
view; it holds at every nonzero multiple, `VtxGen.smul`, `VtxGen.neg`). -/
def VtxOK2 {x : Fin 7 → ℝ³} (T : Type16 x) : Prop :=
  VtxGen (univ.image x) (vtxView16 x 2) (({0, 2, 3, 5} : Finset (Fin 7)).image x)
    (({0, 4, 6} : Finset (Fin 7)).image x) T.q0235.N

/-- **The codimension-2 conditions at the view along `1356/046`.** -/
def VtxOK5 {x : Fin 7 → ℝ³} (T : Type16 x) : Prop :=
  VtxGen (univ.image x) (vtxView16 x 5) (({1, 3, 5, 6} : Finset (Fin 7)).image x)
    (({0, 4, 6} : Finset (Fin 7)).image x) T.q1356.N

/-- At every view along the line of two planes given by affine face functions: no horizontal
double normal, or the codimension-2 conditions of §22.4 at a vertex view (`VtxGen`, with the
normal of the first plane). -/
def HDNOrVtxGenAff (V : Finset ℝ³) (fP fQ : ℝ³ →ᵃ[ℝ] ℝ) (SA SB : Finset ℝ³) : Prop :=
  ∀ u : ℝ³, u ≠ 0 → fP.linear u = 0 → fQ.linear u = 0 → NoHDNAt V u ∨
    ∀ NA : ℝ³, (∀ y, fP.linear y = ⟪NA, y⟫) → VtxGen V u SA SB NA

/-- `2` and `3` along the view `u_a` of `T_a`: `2` above, `3` below the chord `[0, 5]`. -/
theorem NF16.coords_uA {x : Fin 7 → ℝ³} (N : NF16 x) :
    (∃ s δ : ℝ, 0 < δ ∧ x 2 = x 0 + s • (x 5 - x 0) + δ • N.uA) ∧
      (∃ s δ : ℝ, δ < 0 ∧ x 3 = x 0 + s • (x 5 - x 0) + δ • N.uA) := by
  have hP : 0 < N.p + N.q + N.r - 1 := N.t046_5
  set P := N.p + N.r - 1 with hPdef
  have hPq : P + N.q ≠ 0 := by rw [hPdef]; linarith
  refine ⟨⟨N.b - (N.a + N.b - 1) / (P + N.q) * N.q, (N.a + N.b - 1) / (P + N.q),
    div_pos N.hab (by rw [hPdef]; linarith), ?_⟩,
    ⟨-(-1 / (P + N.q)) * N.q, -1 / (P + N.q), div_neg_of_neg_of_pos (by norm_num)
      (by rw [hPdef]; linarith), ?_⟩⟩
  · rw [N.x2, N.x0, N.x5]
    simp only [NF16.uA, nfP, nfV]
    have e : (N.a + N.b - 1) / (P + N.q) * (P + N.q) = N.a + N.b - 1 := div_mul_cancel₀ _ hPq
    ext k
    simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
    rw [← hPdef]
    linear_combination (-(N.E₁ k)) * e
  · rw [N.x3, N.x0, N.x5]
    simp only [NF16.uA, nfP, nfV]
    have e : -1 / (P + N.q) * (P + N.q) = -1 := div_mul_cancel₀ _ hPq
    ext k
    simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
    rw [← hPdef]
    linear_combination (-(N.E₁ k)) * e

/-- `3` lies on the plane of `5, 1, 6` (the facet `1356`). -/
theorem NF16.copl3 {x : Fin 7 → ℝ³} (N : NF16 x) :
    det3 (x 5 - x 3) (x 1 - x 3) (x 6 - x 3) = 0 := by
  rw [N.x5, N.x3, N.x1, N.x6, nfP_sub, nfP_sub, nfP_sub, det3_nfV]
  simp [det3c]

set_option maxHeartbeats 1000000 in
/-- **`T_a` at the limit** (the view along `0235/046`). -/
theorem isRupert_pVtx2 {x : Fin 7 → ℝ³} (T : Type16 x) (K : ℕ → Fin 7 → ℝ³)
    (hK : ∀ m, Tendsto (fun n => K n m) atTop (𝓝 (x m)))
    (hfreq : ∃ᶠ n in atTop, ∃ c : ℝ, c ≠ 0 ∧ RimCertPts (univ.image (K n))
      (c • view16 (K n) (.inr 2)) (quad (K n 0) (K n 5) (K n 1) (K n 6)))
    (hg : VtxOK2 T) : IsRupert (univ.image x) := by
  obtain ⟨ε, hε, hf⟩ := freq_sign (P := fun c n => RimCertPts (univ.image (K n))
    (c • view16 (K n) (.inr 2)) (quad (K n 0) (K n 5) (K n 1) (K n 6)))
    (fun n c hc h => rimCertPts_normalize hc h) hfreq
  have hε0 : ε ≠ 0 := by rcases hε with rfl | rfl <;> norm_num
  set N := T.toNF with hN
  have hv0 : vtxView16 x 2 ≠ 0 := T.view16_ne_zero (.inr 2) (fun i h => by cases h)
  set u := ε • vtxView16 x 2 with hu_def
  have hu : u ≠ 0 := smul_ne_zero hε0 hv0
  have hvl : vtxView16 x 2 = planeLine (x 0) (x 3) (x 5) (x 0) (x 4) (x 6) := rfl
  have hNa : ⟪T.q0235.N, u⟫ = 0 := by
    rw [hu_def, real_inner_smul_right, hvl,
      inner_planeLine_left (T.q0235.inner_sub (by decide) (by decide))
        (T.q0235.inner_sub (by decide) (by decide)), mul_zero]
  have hNb : ⟪T.t046.N, u⟫ = 0 := by
    rw [hu_def, real_inner_smul_right, hvl,
      inner_planeLine_right (T.t046.inner_sub (by decide) (by decide))
        (T.t046.inner_sub (by decide) (by decide)), mul_zero]
  have huA : u = (ε * -N.D) • N.uA := by rw [hu_def, NF16.vtxView16_uA, smul_smul]
  have hk : ε * -N.D ≠ 0 := mul_ne_zero hε0 (neg_ne_zero.mpr N.hD)
  obtain ⟨⟨s2, δ2, hδ2, h2⟩, ⟨s3, δ3, hδ3, h3⟩⟩ := N.coords_uA
  have conv : ∀ {i : Fin 7} {s δ : ℝ}, x i = x 0 + s • (x 5 - x 0) + δ • N.uA →
      x i = x 0 + s • (x 5 - x 0) + (δ / (ε * -N.D)) • u := by
    intro i s δ h
    rw [h, huA, smul_smul, div_mul_cancel₀ _ hk]
  have hus : Tendsto (fun n => ε • vtxView16 (K n) 2) atTop (𝓝 u) :=
    (tendsto_view16 hK (.inr 2)).const_smul ε
  have hseg := T.noSeg
  have hfa := T.q0235.hf (i₀ := 0) (by decide)
  have hfb := T.t046.hf (i₀ := 0) (by decide)
  have hgen : VtxGen (univ.image x) u _ _ T.q0235.N := hg.sign hε
  rcases lt_or_gt_of_ne hk with hneg | hpos
  · -- `3` above, `2` below the chord along `u`
    refine isRupert_vtx_limit x T.inj hseg (v := 0) (a := 5) (c := 1) (b := 6) (p := 3)
      (q := 2) (m := 4) (by decide) (Sa := {0, 2, 3, 5}) (Sb := {0, 4, 6}) (by decide)
      (by decide) hfa hfb hu hNa hNb
      ⟨s3, δ3 / (ε * -N.D), div_pos_of_neg_of_neg hδ3 hneg, conv h3⟩
      ⟨s2, δ2 / (ε * -N.D), div_neg_of_pos_of_neg hδ2 hneg, conv h2⟩ K hK _ hus hf hgen
      fun E _ => (E.hD_of_copl (Or.inl N.copl3)).imp Or.inl Or.inl
  · refine isRupert_vtx_limit x T.inj hseg (v := 0) (a := 5) (c := 1) (b := 6) (p := 2)
      (q := 3) (m := 4) (by decide) (Sa := {0, 2, 3, 5}) (Sb := {0, 4, 6}) (by decide)
      (by decide) hfa hfb hu hNa hNb
      ⟨s2, δ2 / (ε * -N.D), div_pos hδ2 hpos, conv h2⟩
      ⟨s3, δ3 / (ε * -N.D), div_neg_of_neg_of_pos hδ3 hpos, conv h3⟩ K hK _ hus hf hgen
      fun E _ => (E.hD_of_copl (Or.inr N.copl3)).imp Or.inl Or.inl

theorem image_sigma16_set (x : Fin 7 → ℝ³) (S S' : Finset (Fin 7))
    (h : S.image sigma16 = S') : S.image (x ∘ sigma16) = S'.image x := by
  rw [← h, Finset.image_image]

/-- **`T_a`'s `σ`-image at the limit** (the view along `1356/046`, rim `(6, 5, 2, 0)`). -/
theorem isRupert_pVtx5 {x : Fin 7 → ℝ³} (T : Type16 x) (K : ℕ → Fin 7 → ℝ³)
    (hK : ∀ m, Tendsto (fun n => K n m) atTop (𝓝 (x m)))
    (hfreq : ∃ᶠ n in atTop, ∃ c : ℝ, c ≠ 0 ∧ RimCertPts (univ.image (K n))
      (c • view16 (K n) (.inr 5)) (quad (K n 6) (K n 5) (K n 2) (K n 0)))
    (hg : VtxOK5 T) : IsRupert (univ.image x) := by
  have h := isRupert_pVtx2 T.sigma (fun n => K n ∘ sigma16) (fun m => hK (sigma16 m))
    (hfreq.mono fun n ⟨c, hc, hr⟩ => ⟨c, hc, by
      rw [image_sigma16]
      have e : view16 (K n ∘ sigma16) (.inr 2) = view16 (K n) (.inr 5) :=
        vtxView16_sigma (K n) 2
      rw [e]; exact hr⟩) (by
      have e1 : (({0, 2, 3, 5} : Finset (Fin 7))).image (x ∘ sigma16) =
          (({1, 3, 5, 6} : Finset (Fin 7))).image x := image_sigma16_set x _ _ (by decide)
      have e2 : (({0, 4, 6} : Finset (Fin 7))).image (x ∘ sigma16) =
          (({0, 4, 6} : Finset (Fin 7))).image x := image_sigma16_set x _ _ (by decide)
      unfold VtxOK2
      rw [image_sigma16, e1, e2, vtxView16_sigma]
      exact hg)
  rwa [image_sigma16] at h

end Minimality

end
