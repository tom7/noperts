module

public import Minimality.Type16T2

@[expose] public section

/-!
# Type 16: no horizontal-double-normal exception at the segment `35` (§22.12)

The certificates of the cover at the view along `35` (the edge of the two quadrilaterals `0235`,
`1356`):
* the edge pairs of Theorem 19.2 (`(3, 5, a, b, 4)` with `a, b` the far ends, U1, U2, D2):
  `isRupert_ePair_limit` (§22.3–22.8 with Lemma E);
* the triangle closings D7 (`(3, 5, 6, 0)`): realized on both circles (Proposition 22.2,
  `isRupert_eTri_limit`);
* Lemma 19.3's `T1` (the closing `K_3`, rim `(3, 1, 4, x)`, and its `σ`-image): no Lemma E.  At the
  limit (`isRupert_kv_limit`) only the residual where `K_5` has a weak saddle and `K_3` none needs
  more; there `1` lies above `4` and `5` along `3 − 5`, and Lemma 19.3 (ii) makes `T2 = 046/145`
  unimodal (`isRupert_T2_at`), closed at its own view (no horizontal double normal there, or
  (G1): Proposition 22.2).

The codimension-2 conditions at `35` (`Gen35`): `EdgeGen` for the faces `1356`, `0235`; `3` and
`5` off the planes `124`, `014`, `246` of Lemma E; the shape off the boundary of Lemma 19.3's
region and of its `σ`-image (`Off193`).

* `Gen35`, `EdgeGen.negU`.
* `isRupert_ePair35`, `isRupert_eTri35`, `isRupert_pT1`, `isRupert_pT1σ`.
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

/-- `EdgeGen` at `−u` with the faces in the same order. -/
theorem EdgeGen.negU {V : Finset ℝ³} {u v w : ℝ³} {SA SB : Finset ℝ³} {NA NB : ℝ³}
    (h : EdgeGen V u v w SA SB NA NB) : EdgeGen V (-u) v w SA SB NA NB where
  par := EdgeConf.ParOnly.neg' h.par
  g1 := G1At.swapF (EdgeConf.G1At.neg h.g1)
  dist := fun y hy y' hy' hne e => h.dist y hy y' hy' hne (by
    simp only [inner_neg_right, neg_inj] at e; exact e)
  one := h.one.neg_u
  footA := h.footA
  footB := h.footB

theorem EdgeGen.sgn {V : Finset ℝ³} {u v w : ℝ³} {SA SB : Finset ℝ³} {NA NB : ℝ³}
    (h : EdgeGen V u v w SA SB NA NB) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    EdgeGen V (ε • u) v w SA SB NA NB := by
  rcases hε with rfl | rfl
  · rwa [one_smul]
  · rw [neg_one_smul]; exact h.negU

/-- **The codimension-2 conditions at the view along `35`** (with a horizontal double normal
there): `EdgeGen` for the faces `1356`, `0235`; `3`, `5` off the planes `124`, `014`, `246` of
Lemma E; the shape and its `σ`-image off the boundary of Lemma 19.3's region. -/
def Gen35 {x : Fin 7 → ℝ³} (T : Type16 x) : Prop :=
  EdgeGen (univ.image x) (x 5 - x 3) (x 3) (x 5) (({1, 3, 5, 6} : Finset (Fin 7)).image x)
    (({0, 2, 3, 5} : Finset (Fin 7)).image x) T.q1356.N T.q0235.N ∧
  (det3 (x 2 - x 1) (x 4 - x 1) (x 3 - x 1) ≠ 0 ∧ det3 (x 2 - x 1) (x 4 - x 1) (x 5 - x 1) ≠ 0) ∧
  (det3 (x 0 - x 1) (x 4 - x 1) (x 3 - x 1) ≠ 0 ∧ det3 (x 0 - x 1) (x 4 - x 1) (x 5 - x 1) ≠ 0) ∧
  (det3 (x 2 - x 6) (x 4 - x 6) (x 3 - x 6) ≠ 0 ∧ det3 (x 2 - x 6) (x 4 - x 6) (x 5 - x 6) ≠ 0) ∧
  Off193 x ∧ Off193 (x ∘ sigma16)

theorem det3_lemmaE_ne {a b c X Y : ℝ³}
    (h : det3 (b - a) (c - a) (X - a) ≠ 0 ∧ det3 (b - a) (c - a) (Y - a) ≠ 0) :
    det3 (a - b) (c - b) (X - b) ≠ 0 ∧ det3 (a - b) (c - b) (Y - b) ≠ 0 := by
  rw [det3_lemmaE_ab a b c X, det3_lemmaE_ab a b c Y, neg_ne_zero, neg_ne_zero]; exact h

/-! ### The edge pairs at `35` -/

set_option maxRecDepth 8000 in
theorem ePair35_cases : ∀ a b : Fin 7, (3, 5, a, b, 4) ∈ ePairList16 →
    (a = 1 ∧ b = 2) ∨ (a = 1 ∧ b = 0) ∨ (a = 6 ∧ b = 2) ∨ (a = 2 ∧ b = 1) ∨
      (a = 2 ∧ b = 6) ∨ (a = 0 ∧ b = 1) := by decide

set_option maxRecDepth 8000 in
theorem eTri35_cases : ∀ a b : Fin 7, (3, 5, a, b) ∈ eTriList16 →
    (a = 6 ∧ b = 0) ∨ (a = 0 ∧ b = 6) := by decide

set_option maxRecDepth 8000 in
/-- **The edge pairs of the cover at `35`** at the limit. -/
theorem isRupert_ePair35 {x : Fin 7 → ℝ³} (T : Type16 x) (K : ℕ → Fin 7 → ℝ³)
    (hK : ∀ m, Tendsto (fun n => K n m) atTop (𝓝 (x m))) {a b : Fin 7}
    (hab : (3, 5, a, b, 4) ∈ ePairList16) (s : Bool)
    (hfreq : ∃ᶠ n in atTop,
      EPairData (univ.image (K n)) (sgnB s) (K n 3) (K n 5) (K n a) (K n b) (K n 4))
    (hg : Gen35 T) : IsRupert (univ.image x) := by
  obtain ⟨G, P124, P014, P246, -⟩ := hg
  have hA := T.q1356.hf (i₀ := 3) (by decide)
  have hB := T.q0235.hf (i₀ := 3) (by decide)
  have cases_ab := ePair35_cases a b hab
  cases s
  · rw [sgnB_false] at hfreq
    have hf := hfreq.mono fun n hn => hn.flip
    rcases cases_ab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩
    · exact isRupert_ePair_limit x T.inj T.noSeg (v := 3) (w := 5) (a := 2) (b := 1) (c := 4)
        (by decide) hB hA (by decide) (by decide) K hK hf G.swapF (det3_lemmaE_ne P124)
    · exact isRupert_ePair_limit x T.inj T.noSeg (v := 3) (w := 5) (a := 0) (b := 1) (c := 4)
        (by decide) hB hA (by decide) (by decide) K hK hf G.swapF (det3_lemmaE_ne P014)
    · exact isRupert_ePair_limit x T.inj T.noSeg (v := 3) (w := 5) (a := 2) (b := 6) (c := 4)
        (by decide) hB hA (by decide) (by decide) K hK hf G.swapF (det3_lemmaE_ne P246)
    · exact isRupert_ePair_limit x T.inj T.noSeg (v := 3) (w := 5) (a := 1) (b := 2) (c := 4)
        (by decide) hA hB (by decide) (by decide) K hK hf G P124
    · exact isRupert_ePair_limit x T.inj T.noSeg (v := 3) (w := 5) (a := 6) (b := 2) (c := 4)
        (by decide) hA hB (by decide) (by decide) K hK hf G P246
    · exact isRupert_ePair_limit x T.inj T.noSeg (v := 3) (w := 5) (a := 1) (b := 0) (c := 4)
        (by decide) hA hB (by decide) (by decide) K hK hf G P014
  · rw [sgnB_true] at hfreq
    rcases cases_ab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩
    · exact isRupert_ePair_limit x T.inj T.noSeg (v := 3) (w := 5) (a := 1) (b := 2) (c := 4)
        (by decide) hA hB (by decide) (by decide) K hK hfreq G P124
    · exact isRupert_ePair_limit x T.inj T.noSeg (v := 3) (w := 5) (a := 1) (b := 0) (c := 4)
        (by decide) hA hB (by decide) (by decide) K hK hfreq G P014
    · exact isRupert_ePair_limit x T.inj T.noSeg (v := 3) (w := 5) (a := 6) (b := 2) (c := 4)
        (by decide) hA hB (by decide) (by decide) K hK hfreq G P246
    · exact isRupert_ePair_limit x T.inj T.noSeg (v := 3) (w := 5) (a := 2) (b := 1) (c := 4)
        (by decide) hB hA (by decide) (by decide) K hK hfreq G.swapF (det3_lemmaE_ne P124)
    · exact isRupert_ePair_limit x T.inj T.noSeg (v := 3) (w := 5) (a := 2) (b := 6) (c := 4)
        (by decide) hB hA (by decide) (by decide) K hK hfreq G.swapF (det3_lemmaE_ne P246)
    · exact isRupert_ePair_limit x T.inj T.noSeg (v := 3) (w := 5) (a := 0) (b := 1) (c := 4)
        (by decide) hB hA (by decide) (by decide) K hK hfreq G.swapF (det3_lemmaE_ne P014)

/-! ### The triangle closings at `35` (D7) -/

set_option maxRecDepth 8000 in
/-- **The triangle closings of the cover at `35`** at the limit (realized on both circles). -/
theorem isRupert_eTri35 {x : Fin 7 → ℝ³} (T : Type16 x) (K : ℕ → Fin 7 → ℝ³)
    (hK : ∀ m, Tendsto (fun n => K n m) atTop (𝓝 (x m))) {a b : Fin 7}
    (hab : (3, 5, a, b) ∈ eTriList16) (s : Bool)
    (hfreq : ∃ᶠ n in atTop, ETriData (univ.image (K n)) (sgnB s) (K n 3) (K n 5) (K n a) (K n b))
    (hg : Gen35 T) : IsRupert (univ.image x) := by
  have G := hg.1
  have hA := T.q1356.hf (i₀ := 3) (by decide)
  have hB := T.q0235.hf (i₀ := 3) (by decide)
  have j1 := T.t036.adj (p := 3) (q := 6) (r := 5) (s := 1) (by decide) (by decide) (by decide)
    (by decide)
  have j2 := T.t036.adj (p := 0) (q := 3) (r := 5) (s := 2) (by decide) (by decide) (by decide)
    (by decide)
  have j3 := T.t036.adj (p := 3) (q := 0) (r := 5) (s := 2) (by decide) (by decide) (by decide)
    (by decide)
  have j4 := T.t036.adj (p := 6) (q := 3) (r := 5) (s := 1) (by decide) (by decide) (by decide)
    (by decide)
  -- `(a, b) = (6, 0)`: `S_a = 1356`, `S_b = 0235`; `(0, 6)`: the faces exchanged
  have k60 : ∀ hf : ∃ᶠ n in atTop, ETriData (univ.image (K n)) 1 (K n 3) (K n 5) (K n 6) (K n 0),
      IsRupert (univ.image x) := fun hf => by
    refine isRupert_eTri_limit x T.inj (v := 3) (w := 5) (a := 6) (b := 0) (by decide) hA hB
      (by decide) (by decide) ?_ ?_ K hK hf G.par G.g1 G.dist
    · intro i hi h1 h2 h3
      obtain rfl : i = 1 := by revert hi h1 h2 h3; revert i; decide
      exact ⟨T.t036.N, j1.1, j1.2.1, j1.2.2⟩
    · intro i hi h1 h2 h3
      obtain rfl : i = 2 := by revert hi h1 h2 h3; revert i; decide
      exact ⟨T.t036.N, j2.1, j2.2.1, j2.2.2⟩
  have k06 : ∀ hf : ∃ᶠ n in atTop, ETriData (univ.image (K n)) 1 (K n 3) (K n 5) (K n 0) (K n 6),
      IsRupert (univ.image x) := fun hf => by
    refine isRupert_eTri_limit x T.inj (v := 3) (w := 5) (a := 0) (b := 6) (by decide) hB hA
      (by decide) (by decide) ?_ ?_ K hK hf G.par G.g1.swapF G.dist
    · intro i hi h1 h2 h3
      obtain rfl : i = 2 := by revert hi h1 h2 h3; revert i; decide
      exact ⟨T.t036.N, j3.1, j3.2.1, j3.2.2⟩
    · intro i hi h1 h2 h3
      obtain rfl : i = 1 := by revert hi h1 h2 h3; revert i; decide
      exact ⟨T.t036.N, j4.1, j4.2.1, j4.2.2⟩
  have cases_ab := eTri35_cases a b hab
  cases s
  · rw [sgnB_false] at hfreq
    rcases cases_ab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact k06 (hfreq.mono fun n hn => hn.flip)
    · exact k60 (hfreq.mono fun n hn => hn.flip)
  · rw [sgnB_true] at hfreq
    rcases cases_ab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact k60 hfreq
    · exact k06 hfreq

/-! ### Lemma 19.3's `T1` at `35` -/

/-- No weak saddle is invariant under `±` scaling of the depths. -/
theorem nws4_sgn {z₀ z₁ z₂ z₃ ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    NWS4 (quad (ε * z₀) (ε * z₁) (ε * z₂) (ε * z₃)) ↔ NWS4 (quad z₀ z₁ z₂ z₃) := by
  rcases hε with rfl | rfl
  · simp only [one_mul]
  · simp only [NWS4, quad_0, quad_1, quad_2, quad_3, neg_one_mul, neg_lt_neg_iff]
    tauto

/-- **The depth pattern of `K_5` two-peaked, `K_3` not** (at the view along `35`): `1` lies below
`4` and `5` along `5 − 3`. -/
theorem below_of_kw {z1 z3 z4 z5 zb : ℝ} (h35 : z3 < z5) (h14 : z1 ≠ z4) (h15 : z1 ≠ z5)
    (hKv : NWS4 (quad z3 z1 z4 zb)) (hKw : ¬ NWS4 (quad z5 z1 z4 zb)) : z1 < z4 ∧ z1 < z5 := by
  simp only [NWS4, quad_0, quad_1, quad_2, quad_3, not_and_or, not_or, not_lt] at hKv hKw
  rcases hKw with ⟨k1, k2, k3, k4⟩ | ⟨k1, k2, k3, k4⟩
  · exact ⟨lt_of_le_of_ne k3 h14, lt_of_le_of_ne k1 h15⟩
  · exfalso
    rcases hKv.2 with h | h | h | h
    · linarith
    · linarith
    · linarith
    · linarith

set_option maxRecDepth 8000 in
/-- **Lemma 19.3's `T1` at the limit** (the closing `K_3` at `35`, rim `(3, 1, 4, b)`, `b ∈ {2, 0}`;
the approximants in Lemma 19.3's region).  §22's closing at `35` (no Lemma E is needed:
`isRupert_kv_limit`), and in its residual (`K_5` with a weak saddle) `T2` at its view. -/
theorem isRupert_pT1 {x : Fin 7 → ℝ³} (T : Type16 x) (K : ℕ → Fin 7 → ℝ³)
    (hK : ∀ m, Tendsto (fun n => K n m) atTop (𝓝 (x m))) {b : Fin 7} (hb : b = 2 ∨ b = 0)
    (hfreq : ∃ᶠ n in atTop, (∃ c : ℝ, c ≠ 0 ∧ RimCertPts (univ.image (K n))
      (c • view16 (K n) (.inl (3, 5))) (quad (K n 3) (K n 1) (K n 4) (K n b))) ∧ Reg193 (K n))
    (hgen : EdgeGen (univ.image x) (x 5 - x 3) (x 3) (x 5)
      (({1, 3, 5, 6} : Finset (Fin 7)).image x) (({0, 2, 3, 5} : Finset (Fin 7)).image x)
      T.q1356.N T.q0235.N)
    (hoff : Off193 x) (hV0 : NoHDNAt (univ.image x) (view16 x (.inr 0)) ∨ Sec16 x (.inr 0)) :
    IsRupert (univ.image x) := by
  obtain ⟨ε, hε, hf⟩ := freq_sign (P := fun c n => RimCertPts (univ.image (K n))
    (c • view16 (K n) (.inl (3, 5))) (quad (K n 3) (K n 1) (K n 4) (K n b)))
    (fun n c hc h => rimCertPts_normalize hc h) (hfreq.mono fun n hn => hn.1)
  have hR := reg193_of_limit T hK (hfreq.mono fun n hn => hn.2) hoff
  have hSa : (3 : Fin 7) ∈ ({1, 3, 5, 6} : Finset (Fin 7)) ∧ (5 : Fin 7) ∈ ({1, 3, 5, 6} : Finset (Fin 7)) ∧
      (1 : Fin 7) ∈ ({1, 3, 5, 6} : Finset (Fin 7)) ∧ b ∉ ({1, 3, 5, 6} : Finset (Fin 7)) ∧
      (4 : Fin 7) ∉ ({1, 3, 5, 6} : Finset (Fin 7)) ∧
      ∀ i ∈ ({1, 3, 5, 6} : Finset (Fin 7)), ∀ j ∈ ({1, 3, 5, 6} : Finset (Fin 7)),
        i ≠ 3 → i ≠ 5 → i ≠ 1 → j ≠ 3 → j ≠ 5 → j ≠ 1 → i = j := by
    rcases hb with rfl | rfl <;> decide
  have hSb : (3 : Fin 7) ∈ ({0, 2, 3, 5} : Finset (Fin 7)) ∧ (5 : Fin 7) ∈ ({0, 2, 3, 5} : Finset (Fin 7)) ∧
      b ∈ ({0, 2, 3, 5} : Finset (Fin 7)) ∧ (1 : Fin 7) ∉ ({0, 2, 3, 5} : Finset (Fin 7)) ∧
      (4 : Fin 7) ∉ ({0, 2, 3, 5} : Finset (Fin 7)) ∧
      ∀ i ∈ ({0, 2, 3, 5} : Finset (Fin 7)), ∀ j ∈ ({0, 2, 3, 5} : Finset (Fin 7)),
        i ≠ 3 → i ≠ 5 → i ≠ b → j ≠ 3 → j ≠ 5 → j ≠ b → i = j := by
    rcases hb with rfl | rfl <;> decide
  refine isRupert_kv_limit x T.inj T.noSeg (v := 3) (w := 5) (a := 1) (b := b) (c := 4)
    (by decide) (T.q1356.hf (i₀ := 3) (by decide)) (T.q0235.hf (i₀ := 3) (by decide)) hSa hSb hε
    K hK hf (hgen.sgn hε) fun hKv hKw => ?_
  simp only [real_inner_smul_right] at hKv hKw
  rw [nws4_sgn hε] at hKv hKw
  have mem : ∀ i, x i ∈ univ.image x := fun i => mem_image_of_mem x (mem_univ i)
  have h35 : ⟪x 3, x 5 - x 3⟫ < ⟪x 5, x 5 - x 3⟫ := by
    have : 0 < ⟪x 5 - x 3, x 5 - x 3⟫ :=
      real_inner_self_pos.mpr (sub_ne_zero.mpr (T.inj.ne (by decide)))
    rw [inner_sub_left] at this; linarith
  obtain ⟨h41, h51⟩ := below_of_kw h35 (hgen.dist _ (mem 1) _ (mem 4) (T.inj.ne (by decide)))
    (hgen.dist _ (mem 1) _ (mem 5) (T.inj.ne (by decide))) hKv hKw
  exact isRupert_T2_at T hR h41 h51 hV0

/-- **`T1`'s `σ`-image at the limit** (rim `(3, 2, 4, b)`, `b ∈ {1, 6}`; `T2`'s image `046/245` at
`4`). -/
theorem isRupert_pT1σ {x : Fin 7 → ℝ³} (T : Type16 x) (K : ℕ → Fin 7 → ℝ³)
    (hK : ∀ m, Tendsto (fun n => K n m) atTop (𝓝 (x m))) {b : Fin 7} (hb : b = 1 ∨ b = 6)
    (hfreq : ∃ᶠ n in atTop, (∃ c : ℝ, c ≠ 0 ∧ RimCertPts (univ.image (K n))
      (c • view16 (K n) (.inl (3, 5))) (quad (K n 3) (K n 2) (K n 4) (K n b))) ∧
      Reg193 (K n ∘ sigma16))
    (hgen : EdgeGen (univ.image x) (x 5 - x 3) (x 3) (x 5)
      (({1, 3, 5, 6} : Finset (Fin 7)).image x) (({0, 2, 3, 5} : Finset (Fin 7)).image x)
      T.q1356.N T.q0235.N)
    (hoff : Off193 (x ∘ sigma16))
    (hV3 : NoHDNAt (univ.image x) (vtxView16 x 3) ∨
      G1Vtx (univ.image x) (vtxView16 x 3) (x 6) (x 4) (x 0) (x 2) (x 4) (x 5)) :
    IsRupert (univ.image x) := by
  have e1 : (({1, 3, 5, 6} : Finset (Fin 7))).image (x ∘ sigma16) =
      (({0, 2, 3, 5} : Finset (Fin 7))).image x := image_sigma16_set x _ _ (by decide)
  have e2 : (({0, 2, 3, 5} : Finset (Fin 7))).image (x ∘ sigma16) =
      (({1, 3, 5, 6} : Finset (Fin 7))).image x := image_sigma16_set x _ _ (by decide)
  have ev : vtxView16 (x ∘ sigma16) 0 = vtxView16 x 3 := vtxView16_sigma x 0
  obtain ⟨b', hb', hsb⟩ : ∃ b' : Fin 7, (b' = 2 ∨ b' = 0) ∧ ∀ y : Fin 7 → ℝ³, (y ∘ sigma16) b' = y b := by
    rcases hb with rfl | rfl
    · exact ⟨2, Or.inl rfl, fun y => rfl⟩
    · exact ⟨0, Or.inr rfl, fun y => rfl⟩
  have hV0 : NoHDNAt (univ.image (x ∘ sigma16)) (view16 (x ∘ sigma16) (.inr 0)) ∨
      Sec16 (x ∘ sigma16) (.inr 0) := by
    rcases hV3 with h | h
    · left
      show NoHDNAt (univ.image (x ∘ sigma16)) (vtxView16 (x ∘ sigma16) 0)
      rw [image_sigma16, ev]; exact h
    · right
      refine ⟨Or.inl rfl, ?_⟩
      show G1Vtx (univ.image (x ∘ sigma16)) (vtxView16 (x ∘ sigma16) 0) (x 6) (x 4) (x 0) (x 2)
        (x 4) (x 5)
      rw [image_sigma16, ev]; exact h
  have hg' : EdgeGen (univ.image (x ∘ sigma16)) ((x ∘ sigma16) 5 - (x ∘ sigma16) 3)
      ((x ∘ sigma16) 3) ((x ∘ sigma16) 5)
      (({1, 3, 5, 6} : Finset (Fin 7)).image (x ∘ sigma16))
      (({0, 2, 3, 5} : Finset (Fin 7)).image (x ∘ sigma16)) T.sigma.q1356.N T.sigma.q0235.N := by
    rw [image_sigma16, e1, e2]; exact hgen.swapF
  have h := isRupert_pT1 T.sigma (fun n => K n ∘ sigma16) (fun m => hK (sigma16 m)) hb'
    (hfreq.mono fun n ⟨⟨c, hc, hr⟩, hreg⟩ => ⟨⟨c, hc, by
      rw [image_sigma16, hsb]; exact hr⟩, hreg⟩) hg' hoff hV0
  rwa [image_sigma16] at h

end Minimality

end
