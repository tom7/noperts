module

public import Minimality.Type16Edge

@[expose] public section

/-!
# Type 16: no horizontal-double-normal exception at `15`, `25`, `03`, `36` (§22)

The certificates of the cover at the views along `15`, `25`, `03`, `36` are edge pairs (Lemma E),
the triangle closings D6 and its image, and the pair certificates `T_c` (Lemma 19.5, four or
five corners) and `B` (Lemma 19.4, five corners) with their images.  The edge pairs are closed
by §22 (`isRupert_ePair_limit`), the others are realized on both face circles (their sides on the
faces are edges of the faces) and closed by Proposition 22.2 (`isRupert_eTri_limit`,
`isRupert_twoFace_limit`), under the codimension-2 conditions `Gen15`, `Gen25`, `Gen03`, `Gen36`.
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

/-! ### Helpers -/

/-- A determinant of three points of a face against its normal is nonzero when the points are
not collinear. -/
theorem det3_face_ne {N p q m : ℝ³} (hq : ⟪N, q - p⟫ = 0) (hm : ⟪N, m - p⟫ = 0)
    (hc : cross (q - p) (m - p) ≠ 0) (hN : N ≠ 0) : det3 (q - p) (m - p) N ≠ 0 := by
  have hpar : cross N (cross (q - p) (m - p)) = 0 := by
    have e1 : ⟪q - p, N⟫ = 0 := by rw [real_inner_comm]; exact hq
    have e2 : ⟪m - p, N⟫ = 0 := by rw [real_inner_comm]; exact hm
    have e : cross (cross (q - p) (m - p)) N = 0 := by
      rw [cross_cross_eq, e1, e2, zero_smul, zero_smul, sub_zero]
    have : cross N (cross (q - p) (m - p)) = -cross (cross (q - p) (m - p)) N := by
      ext j; fin_cases j <;> simp [cross] <;> ring
    rw [this, e, neg_zero]
  obtain ⟨t, ht⟩ : ∃ t : ℝ, cross (q - p) (m - p) = t • N :=
    ⟨_, eq_smul_of_cross_eq_zero hN hpar⟩
  have ht0 : t ≠ 0 := by rintro rfl; rw [zero_smul] at ht; exact hc ht
  rw [det3, ht, real_inner_smul_left]
  exact mul_ne_zero ht0 (real_inner_self_pos.mpr hN).ne'

theorem Face16.N_ne {x : Fin 7 → ℝ³} {S : Finset (Fin 7)} (F : Face16 x S) {i j : Fin 7}
    (hi : i ∈ S) (hj : j ∉ S) : F.N ≠ 0 := by
  intro h0
  have := F.hN (x j) (x i)
  rw [h0, inner_zero_left, F.zero i hi, sub_zero] at this
  exact (F.neg j hj).ne this

/-- **The side signs of a face**: the rim has one side `lab i₀ → lab (i₀ + 1)` on the face, and
every other vertex of the face lies on the side of the reference vertex `m₀` (an adjacent facet
through the side). -/
theorem hs_face {x : Fin 7 → ℝ³} (T : Type16 x) {S : Finset (Fin 7)} (F : Face16 x S) {k : ℕ}
    {lab : ZMod k → Fin 7} (i₀ : ZMod k) (m₀ : Fin 7) {j₀ : Fin 7} (hj₀ : j₀ ∉ S)
    (huniq : ∀ i, lab i ∈ S → lab (i + 1) ∈ S → i = i₀) (hp : lab i₀ ∈ S) (hq : lab (i₀ + 1) ∈ S)
    (hm₀ : m₀ ∈ S) (hpq : lab i₀ ≠ lab (i₀ + 1)) (hm₀p : m₀ ≠ lab i₀) (hm₀q : m₀ ≠ lab (i₀ + 1))
    (hother : ∀ m ∈ S, m ≠ lab i₀ → m ≠ lab (i₀ + 1) → m ≠ m₀ → ∃ NG : ℝ³,
      ⟪NG, x (lab (i₀ + 1)) - x (lab i₀)⟫ = 0 ∧ ⟪NG, x m₀ - x (lab i₀)⟫ < 0 ∧
        ⟪NG, x m - x (lab i₀)⟫ < 0) :
    ∃ σ : ℝ, σ ≠ 0 ∧ ∀ i m, lab i ∈ S → lab (i + 1) ∈ S → m ∈ S → m ≠ lab i →
      m ≠ lab (i + 1) → 0 < σ * det3 (x (lab (i + 1)) - x (lab i)) (x m - x (lab i)) F.N := by
  have hN := F.N_ne hp hj₀
  have on : ∀ m ∈ S, ⟪F.N, x m - x (lab i₀)⟫ = 0 := fun m hm => by
    rw [inner_sub_right, (F.hf hp m).1 hm, sub_self]
  have hc : ∀ m, m ≠ lab i₀ → m ≠ lab (i₀ + 1) →
      cross (x (lab (i₀ + 1)) - x (lab i₀)) (x m - x (lab i₀)) ≠ 0 := fun m h1 h2 =>
    cross_ne_zero_of_noSeg T.inj T.noSeg hpq (Ne.symm h1) (Ne.symm h2)
  set σ := det3 (x (lab (i₀ + 1)) - x (lab i₀)) (x m₀ - x (lab i₀)) F.N with hσ
  have hσ0 : σ ≠ 0 := det3_face_ne (on _ hq) (on _ hm₀) (hc m₀ hm₀p hm₀q) hN
  refine ⟨σ, hσ0, fun i m h1 h2 h3 h4 h5 => ?_⟩
  obtain rfl := huniq i h1 h2
  by_cases hmm : m = m₀
  · subst hmm; exact mul_self_pos.mpr hσ0
  · obtain ⟨NG, g1, g2, g3⟩ := hother m h3 h4 h5 hmm
    have := side_sign_of_adj (on _ hq) (on _ hm₀) (on _ h3) (hc m₀ hm₀p hm₀q) hN g1 g2 g3
    rw [mul_comm] at this; exact this

theorem rimCertAt_quad {y : Fin 7 → ℝ³} {u : ℝ³} {a b c d : Fin 7}
    (h : RimCertPts (univ.image y) u (quad (y a) (y b) (y c) (y d))) :
    RimCertAt y u (quad a b c d) := by
  have e : ∀ i, y (quad a b c d i) = quad (y a) (y b) (y c) (y d) i := by
    intro i; rcases zmod4_cases i with rfl | rfl | rfl | rfl <;> rfl
  refine ⟨h.three, fun i j hi hj => ?_, fun m i => ?_, ?_⟩
  · rw [e, e, e]; exact h.cyc i j hi hj
  · rw [e, e]; exact h.left _ (mem_image_of_mem y (mem_univ m)) i
  · simp only [e]; exact h.robust

theorem rimCertAt_quint {y : Fin 7 → ℝ³} {u : ℝ³} {a b c d f : Fin 7}
    (h : RimCertPts (univ.image y) u (quint (y a) (y b) (y c) (y d) (y f))) :
    RimCertAt y u (quint a b c d f) := by
  have e : ∀ i, y (quint a b c d f i) = quint (y a) (y b) (y c) (y d) (y f) i := by
    intro i; rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;> rfl
  refine ⟨h.three, fun i j hi hj => ?_, fun m i => ?_, ?_⟩
  · rw [e, e, e]; exact h.cyc i j hi hj
  · rw [e, e]; exact h.left _ (mem_image_of_mem y (mem_univ m)) i
  · simp only [e]; exact h.robust

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

/-! ### The conditions at `15`, `25`, `03`, `36` -/

/-- **The codimension-2 conditions at the view along `15`**: `EdgeGen` for the faces `1356`,
`145`, and `1`, `5` off the plane `340` of Lemma E. -/
def Gen15 {x : Fin 7 → ℝ³} (T : Type16 x) : Prop :=
  EdgeGen (univ.image x) (x 5 - x 1) (x 1) (x 5) (({1, 3, 5, 6} : Finset (Fin 7)).image x)
    (({1, 4, 5} : Finset (Fin 7)).image x) T.q1356.N T.t145.N ∧
  det3 (x 4 - x 3) (x 0 - x 3) (x 1 - x 3) ≠ 0 ∧ det3 (x 4 - x 3) (x 0 - x 3) (x 5 - x 3) ≠ 0

/-- **The codimension-2 conditions at `25`**: `EdgeGen` for `0235`, `245`, and `2`, `5` off the
plane `346`. -/
def Gen25 {x : Fin 7 → ℝ³} (T : Type16 x) : Prop :=
  EdgeGen (univ.image x) (x 5 - x 2) (x 2) (x 5) (({0, 2, 3, 5} : Finset (Fin 7)).image x)
    (({2, 4, 5} : Finset (Fin 7)).image x) T.q0235.N T.t245.N ∧
  det3 (x 4 - x 3) (x 6 - x 3) (x 2 - x 3) ≠ 0 ∧ det3 (x 4 - x 3) (x 6 - x 3) (x 5 - x 3) ≠ 0

/-- **The codimension-2 conditions at `03`**: `EdgeGen` for `036`, `0235`, and `0`, `3` off the
plane `624`. -/
def Gen03 {x : Fin 7 → ℝ³} (T : Type16 x) : Prop :=
  EdgeGen (univ.image x) (x 3 - x 0) (x 0) (x 3) (({0, 3, 6} : Finset (Fin 7)).image x)
    (({0, 2, 3, 5} : Finset (Fin 7)).image x) T.t036.N T.q0235.N ∧
  det3 (x 2 - x 6) (x 4 - x 6) (x 0 - x 6) ≠ 0 ∧ det3 (x 2 - x 6) (x 4 - x 6) (x 3 - x 6) ≠ 0

/-- **The codimension-2 conditions at `36`**: `EdgeGen` for `036`, `1356`, and `3`, `6` off the
plane `014`. -/
def Gen36 {x : Fin 7 → ℝ³} (T : Type16 x) : Prop :=
  EdgeGen (univ.image x) (x 6 - x 3) (x 3) (x 6) (({0, 3, 6} : Finset (Fin 7)).image x)
    (({1, 3, 5, 6} : Finset (Fin 7)).image x) T.t036.N T.q1356.N ∧
  det3 (x 1 - x 0) (x 4 - x 0) (x 3 - x 0) ≠ 0 ∧ det3 (x 1 - x 0) (x 4 - x 0) (x 6 - x 0) ≠ 0

set_option maxRecDepth 4000 in
theorem isRupert_ePair15 {x : Fin 7 → ℝ³} (T : Type16 x) (K : ℕ → Fin 7 → ℝ³)
    (hK : ∀ m, Tendsto (fun n => K n m) atTop (𝓝 (x m))) (s : Bool)
    (hfreq : ∃ᶠ n in atTop,
      EPairData (univ.image (K n)) (sgnB s) (K n 1) (K n 5) (K n 3) (K n 4) (K n 0))
    (hg : Gen15 T) : IsRupert (univ.image x) := by
  have G := hg.1
  
  cases s
  · rw [sgnB_false] at hfreq
    refine isRupert_ePair_limit x T.inj T.noSeg (v := 1) (w := 5) (a := 4) (b := 3) (c := 0)
      (by decide) (T.t145.hf (i₀ := 1) (by decide)) (T.q1356.hf (i₀ := 1) (by decide))
      (by decide) (by decide) K hK (hfreq.mono fun n hn => hn.flip) G.swapF ⟨?_, ?_⟩
    · rw [det3_lemmaE_ab, neg_ne_zero]; exact hg.2.1
    · rw [det3_lemmaE_ab, neg_ne_zero]; exact hg.2.2
  · rw [sgnB_true] at hfreq
    exact isRupert_ePair_limit x T.inj T.noSeg (v := 1) (w := 5) (a := 3) (b := 4) (c := 0)
      (by decide) (T.q1356.hf (i₀ := 1) (by decide)) (T.t145.hf (i₀ := 1) (by decide))
      (by decide) (by decide) K hK hfreq G hg.2

set_option maxRecDepth 4000 in
theorem isRupert_ePair25 {x : Fin 7 → ℝ³} (T : Type16 x) (K : ℕ → Fin 7 → ℝ³)
    (hK : ∀ m, Tendsto (fun n => K n m) atTop (𝓝 (x m))) (s : Bool)
    (hfreq : ∃ᶠ n in atTop,
      EPairData (univ.image (K n)) (sgnB s) (K n 2) (K n 5) (K n 3) (K n 4) (K n 6))
    (hg : Gen25 T) : IsRupert (univ.image x) := by
  have G := hg.1
  
  cases s
  · rw [sgnB_false] at hfreq
    refine isRupert_ePair_limit x T.inj T.noSeg (v := 2) (w := 5) (a := 4) (b := 3) (c := 6)
      (by decide) (T.t245.hf (i₀ := 2) (by decide)) (T.q0235.hf (i₀ := 2) (by decide))
      (by decide) (by decide) K hK (hfreq.mono fun n hn => hn.flip) G.swapF ⟨?_, ?_⟩
    · rw [det3_lemmaE_ab, neg_ne_zero]; exact hg.2.1
    · rw [det3_lemmaE_ab, neg_ne_zero]; exact hg.2.2
  · rw [sgnB_true] at hfreq
    exact isRupert_ePair_limit x T.inj T.noSeg (v := 2) (w := 5) (a := 3) (b := 4) (c := 6)
      (by decide) (T.q0235.hf (i₀ := 2) (by decide)) (T.t245.hf (i₀ := 2) (by decide))
      (by decide) (by decide) K hK hfreq G hg.2

set_option maxRecDepth 4000 in
theorem isRupert_ePair03 {x : Fin 7 → ℝ³} (T : Type16 x) (K : ℕ → Fin 7 → ℝ³)
    (hK : ∀ m, Tendsto (fun n => K n m) atTop (𝓝 (x m))) (s : Bool)
    (hfreq : ∃ᶠ n in atTop,
      EPairData (univ.image (K n)) (sgnB s) (K n 0) (K n 3) (K n 6) (K n 2) (K n 4))
    (hg : Gen03 T) : IsRupert (univ.image x) := by
  have G := hg.1
  
  cases s
  · rw [sgnB_false] at hfreq
    refine isRupert_ePair_limit x T.inj T.noSeg (v := 0) (w := 3) (a := 2) (b := 6) (c := 4)
      (by decide) (T.q0235.hf (i₀ := 0) (by decide)) (T.t036.hf (i₀ := 0) (by decide))
      (by decide) (by decide) K hK (hfreq.mono fun n hn => hn.flip) G.swapF ⟨?_, ?_⟩
    · rw [det3_lemmaE_ab, neg_ne_zero]; exact hg.2.1
    · rw [det3_lemmaE_ab, neg_ne_zero]; exact hg.2.2
  · rw [sgnB_true] at hfreq
    exact isRupert_ePair_limit x T.inj T.noSeg (v := 0) (w := 3) (a := 6) (b := 2) (c := 4)
      (by decide) (T.t036.hf (i₀ := 0) (by decide)) (T.q0235.hf (i₀ := 0) (by decide))
      (by decide) (by decide) K hK hfreq G hg.2

set_option maxRecDepth 4000 in
theorem isRupert_ePair30 {x : Fin 7 → ℝ³} (T : Type16 x) (K : ℕ → Fin 7 → ℝ³)
    (hK : ∀ m, Tendsto (fun n => K n m) atTop (𝓝 (x m))) (s : Bool)
    (hfreq : ∃ᶠ n in atTop,
      EPairData (univ.image (K n)) (sgnB s) (K n 3) (K n 0) (K n 6) (K n 2) (K n 4))
    (hg : Gen03 T) : IsRupert (univ.image x) := by
  have G := hg.1.rev
  rw [neg_sub] at G
  cases s
  · rw [sgnB_false] at hfreq
    refine isRupert_ePair_limit x T.inj T.noSeg (v := 3) (w := 0) (a := 2) (b := 6) (c := 4)
      (by decide) (T.q0235.hf (i₀ := 3) (by decide)) (T.t036.hf (i₀ := 3) (by decide))
      (by decide) (by decide) K hK (hfreq.mono fun n hn => hn.flip) G.swapF ⟨?_, ?_⟩
    · rw [det3_lemmaE_ab, neg_ne_zero]; exact hg.2.2
    · rw [det3_lemmaE_ab, neg_ne_zero]; exact hg.2.1
  · rw [sgnB_true] at hfreq
    exact isRupert_ePair_limit x T.inj T.noSeg (v := 3) (w := 0) (a := 6) (b := 2) (c := 4)
      (by decide) (T.t036.hf (i₀ := 3) (by decide)) (T.q0235.hf (i₀ := 3) (by decide))
      (by decide) (by decide) K hK hfreq G ⟨hg.2.2, hg.2.1⟩

set_option maxRecDepth 4000 in
theorem isRupert_ePair36 {x : Fin 7 → ℝ³} (T : Type16 x) (K : ℕ → Fin 7 → ℝ³)
    (hK : ∀ m, Tendsto (fun n => K n m) atTop (𝓝 (x m))) (s : Bool)
    (hfreq : ∃ᶠ n in atTop,
      EPairData (univ.image (K n)) (sgnB s) (K n 3) (K n 6) (K n 0) (K n 1) (K n 4))
    (hg : Gen36 T) : IsRupert (univ.image x) := by
  have G := hg.1
  
  cases s
  · rw [sgnB_false] at hfreq
    refine isRupert_ePair_limit x T.inj T.noSeg (v := 3) (w := 6) (a := 1) (b := 0) (c := 4)
      (by decide) (T.q1356.hf (i₀ := 3) (by decide)) (T.t036.hf (i₀ := 3) (by decide))
      (by decide) (by decide) K hK (hfreq.mono fun n hn => hn.flip) G.swapF ⟨?_, ?_⟩
    · rw [det3_lemmaE_ab, neg_ne_zero]; exact hg.2.1
    · rw [det3_lemmaE_ab, neg_ne_zero]; exact hg.2.2
  · rw [sgnB_true] at hfreq
    exact isRupert_ePair_limit x T.inj T.noSeg (v := 3) (w := 6) (a := 0) (b := 1) (c := 4)
      (by decide) (T.t036.hf (i₀ := 3) (by decide)) (T.q1356.hf (i₀ := 3) (by decide))
      (by decide) (by decide) K hK hfreq G hg.2

set_option maxRecDepth 4000 in
theorem isRupert_ePair63 {x : Fin 7 → ℝ³} (T : Type16 x) (K : ℕ → Fin 7 → ℝ³)
    (hK : ∀ m, Tendsto (fun n => K n m) atTop (𝓝 (x m))) (s : Bool)
    (hfreq : ∃ᶠ n in atTop,
      EPairData (univ.image (K n)) (sgnB s) (K n 6) (K n 3) (K n 0) (K n 1) (K n 4))
    (hg : Gen36 T) : IsRupert (univ.image x) := by
  have G := hg.1.rev
  rw [neg_sub] at G
  cases s
  · rw [sgnB_false] at hfreq
    refine isRupert_ePair_limit x T.inj T.noSeg (v := 6) (w := 3) (a := 1) (b := 0) (c := 4)
      (by decide) (T.q1356.hf (i₀ := 6) (by decide)) (T.t036.hf (i₀ := 6) (by decide))
      (by decide) (by decide) K hK (hfreq.mono fun n hn => hn.flip) G.swapF ⟨?_, ?_⟩
    · rw [det3_lemmaE_ab, neg_ne_zero]; exact hg.2.2
    · rw [det3_lemmaE_ab, neg_ne_zero]; exact hg.2.1
  · rw [sgnB_true] at hfreq
    exact isRupert_ePair_limit x T.inj T.noSeg (v := 6) (w := 3) (a := 0) (b := 1) (c := 4)
      (by decide) (T.t036.hf (i₀ := 6) (by decide)) (T.q1356.hf (i₀ := 6) (by decide))
      (by decide) (by decide) K hK hfreq G ⟨hg.2.2, hg.2.1⟩

set_option maxRecDepth 4000 in
theorem isRupert_eTri15 {x : Fin 7 → ℝ³} (T : Type16 x) (K : ℕ → Fin 7 → ℝ³)
    (hK : ∀ m, Tendsto (fun n => K n m) atTop (𝓝 (x m))) (s : Bool)
    (hfreq : ∃ᶠ n in atTop,
      ETriData (univ.image (K n)) (sgnB s) (K n 1) (K n 5) (K n 4) (K n 6))
    (hg : Gen15 T) : IsRupert (univ.image x) := by
  have G := hg.1
  have adj := T.t146.adj (p := 6) (q := 1) (r := 5) (s := 3) (by decide) (by decide) (by decide)
    (by decide)
  have adj' := T.t146.adj (p := 1) (q := 6) (r := 5) (s := 3) (by decide) (by decide) (by decide)
    (by decide)
  cases s
  · rw [sgnB_false] at hfreq
    refine isRupert_eTri_limit x T.inj (v := 1) (w := 5) (a := 6) (b := 4) (by decide)
      (T.q1356.hf (i₀ := 1) (by decide)) (T.t145.hf (i₀ := 1) (by decide)) (by decide)
      (by decide) ?_ ?_ K hK (hfreq.mono fun n hn => hn.flip) G.par G.g1 G.dist
    · intro i hi h1 h2 h3
      obtain rfl : i = 3 := by revert hi h1 h2 h3; revert i; decide
      exact ⟨T.t146.N, adj'.1, adj'.2.1, adj'.2.2⟩
    · intro i hi h1 h2 h3; exfalso; revert hi h1 h2 h3; revert i; decide
  · rw [sgnB_true] at hfreq
    refine isRupert_eTri_limit x T.inj (v := 1) (w := 5) (a := 4) (b := 6) (by decide)
      (T.t145.hf (i₀ := 1) (by decide)) (T.q1356.hf (i₀ := 1) (by decide)) (by decide)
      (by decide) ?_ ?_ K hK hfreq G.par G.g1.swapF G.dist
    · intro i hi h1 h2 h3; exfalso; revert hi h1 h2 h3; revert i; decide
    · intro i hi h1 h2 h3
      obtain rfl : i = 3 := by revert hi h1 h2 h3; revert i; decide
      exact ⟨T.t146.N, adj.1, adj.2.1, adj.2.2⟩

set_option maxRecDepth 4000 in
theorem isRupert_eTri25 {x : Fin 7 → ℝ³} (T : Type16 x) (K : ℕ → Fin 7 → ℝ³)
    (hK : ∀ m, Tendsto (fun n => K n m) atTop (𝓝 (x m))) (s : Bool)
    (hfreq : ∃ᶠ n in atTop,
      ETriData (univ.image (K n)) (sgnB s) (K n 2) (K n 5) (K n 4) (K n 0))
    (hg : Gen25 T) : IsRupert (univ.image x) := by
  have G := hg.1
  have adj := T.t024.adj (p := 0) (q := 2) (r := 5) (s := 3) (by decide) (by decide) (by decide)
    (by decide)
  have adj' := T.t024.adj (p := 2) (q := 0) (r := 5) (s := 3) (by decide) (by decide) (by decide)
    (by decide)
  cases s
  · rw [sgnB_false] at hfreq
    refine isRupert_eTri_limit x T.inj (v := 2) (w := 5) (a := 0) (b := 4) (by decide)
      (T.q0235.hf (i₀ := 2) (by decide)) (T.t245.hf (i₀ := 2) (by decide)) (by decide)
      (by decide) ?_ ?_ K hK (hfreq.mono fun n hn => hn.flip) G.par G.g1 G.dist
    · intro i hi h1 h2 h3
      obtain rfl : i = 3 := by revert hi h1 h2 h3; revert i; decide
      exact ⟨T.t024.N, adj'.1, adj'.2.1, adj'.2.2⟩
    · intro i hi h1 h2 h3; exfalso; revert hi h1 h2 h3; revert i; decide
  · rw [sgnB_true] at hfreq
    refine isRupert_eTri_limit x T.inj (v := 2) (w := 5) (a := 4) (b := 0) (by decide)
      (T.t245.hf (i₀ := 2) (by decide)) (T.q0235.hf (i₀ := 2) (by decide)) (by decide)
      (by decide) ?_ ?_ K hK hfreq G.par G.g1.swapF G.dist
    · intro i hi h1 h2 h3; exfalso; revert hi h1 h2 h3; revert i; decide
    · intro i hi h1 h2 h3
      obtain rfl : i = 3 := by revert hi h1 h2 h3; revert i; decide
      exact ⟨T.t024.N, adj.1, adj.2.1, adj.2.2⟩

set_option maxRecDepth 4000 in
theorem isRupert_pQ15 {x : Fin 7 → ℝ³} (T : Type16 x) (K : ℕ → Fin 7 → ℝ³)
    (hK : ∀ m, Tendsto (fun n => K n m) atTop (𝓝 (x m)))
    (hfreq : ∃ᶠ n in atTop, ∃ c : ℝ, c ≠ 0 ∧ RimCertPts (univ.image (K n))
      (c • view16 (K n) (.inl (1, 5))) (quad (K n 1) (K n 4) (K n 0) (K n 6)))
    (hg : Gen15 T) : IsRupert (univ.image x) := by
  obtain ⟨ε, hε, hf⟩ := freq_sign (P := fun c n => RimCertPts (univ.image (K n))
    (c • view16 (K n) (.inl (1, 5))) (quad (K n 1) (K n 4) (K n 0) (K n 6))) (fun n c hc h => rimCertPts_normalize hc h)
    hfreq
  have hf' : ∃ᶠ n in atTop, RimCertAt (K n) (ε • (K n 5 - K n 1)) (quad 1 4 0 6) :=
    hf.mono fun n hn => rimCertAt_quad hn
  have G := hg.1
  
  obtain ⟨σa, hσa, hsa⟩ := hs_face T T.t145 (lab := quad 1 4 0 6) 0 5 (j₀ := 0) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun m hm h1 h2 h3 => by exfalso; revert hm h1 h2 h3; revert m; decide)
  obtain ⟨σb, hσb, hsb⟩ := hs_face T T.q1356 (lab := quad 1 4 0 6) 3 3 (j₀ := 0) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun m hm h1 h2 h3 => by
      obtain rfl : m = 5 := by revert hm h1 h2 h3; revert m; decide
      have adj := T.t146.adj (p := 6) (q := 1) (r := 3) (s := 5) (by decide) (by decide)
        (by decide) (by decide)
      exact ⟨T.t146.N, adj.1, adj.2.1, adj.2.2⟩)
  have hab : cross T.t145.N T.q1356.N ≠ 0 := by
    have h1 := (T.t145.hf (i₀ := 1) (by decide) 4).1 (by decide)
    have h2 := (T.q1356.hf (i₀ := 1) (by decide) 4).2 (by decide)
    refine cross_normals_ne (T.t145.N_ne (i := 1) (j := 0) (by decide) (by decide))
      (p := x 1) (q := x 4) ?_ ?_
    · rw [inner_sub_right, h1, sub_self]
    · rw [inner_sub_right]; linarith
  exact isRupert_twoFace_limit x T.inj (quad 1 4 0 6) (v := 1) (w := 5) (by decide) ε hε K hK hf'
    (Sa := {1, 4, 5}) (Sb := {1, 3, 5, 6})
    (fun i hi => (T.t145.hf (i₀ := 1) (by decide) i).1 hi)
    (fun i hi => (T.q1356.hf (i₀ := 1) (by decide) i).1 hi) hab G.par G.g1.swapF G.dist
    hσa hσb hsa hsb

set_option maxRecDepth 4000 in
theorem isRupert_pQ25 {x : Fin 7 → ℝ³} (T : Type16 x) (K : ℕ → Fin 7 → ℝ³)
    (hK : ∀ m, Tendsto (fun n => K n m) atTop (𝓝 (x m)))
    (hfreq : ∃ᶠ n in atTop, ∃ c : ℝ, c ≠ 0 ∧ RimCertPts (univ.image (K n))
      (c • view16 (K n) (.inl (2, 5))) (quad (K n 2) (K n 4) (K n 6) (K n 0)))
    (hg : Gen25 T) : IsRupert (univ.image x) := by
  obtain ⟨ε, hε, hf⟩ := freq_sign (P := fun c n => RimCertPts (univ.image (K n))
    (c • view16 (K n) (.inl (2, 5))) (quad (K n 2) (K n 4) (K n 6) (K n 0))) (fun n c hc h => rimCertPts_normalize hc h)
    hfreq
  have hf' : ∃ᶠ n in atTop, RimCertAt (K n) (ε • (K n 5 - K n 2)) (quad 2 4 6 0) :=
    hf.mono fun n hn => rimCertAt_quad hn
  have G := hg.1
  
  obtain ⟨σa, hσa, hsa⟩ := hs_face T T.t245 (lab := quad 2 4 6 0) 0 5 (j₀ := 0) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun m hm h1 h2 h3 => by exfalso; revert hm h1 h2 h3; revert m; decide)
  obtain ⟨σb, hσb, hsb⟩ := hs_face T T.q0235 (lab := quad 2 4 6 0) 3 3 (j₀ := 1) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun m hm h1 h2 h3 => by
      obtain rfl : m = 5 := by revert hm h1 h2 h3; revert m; decide
      have adj := T.t024.adj (p := 0) (q := 2) (r := 3) (s := 5) (by decide) (by decide)
        (by decide) (by decide)
      exact ⟨T.t024.N, adj.1, adj.2.1, adj.2.2⟩)
  have hab : cross T.t245.N T.q0235.N ≠ 0 := by
    have h1 := (T.t245.hf (i₀ := 2) (by decide) 4).1 (by decide)
    have h2 := (T.q0235.hf (i₀ := 2) (by decide) 4).2 (by decide)
    refine cross_normals_ne (T.t245.N_ne (i := 2) (j := 0) (by decide) (by decide))
      (p := x 2) (q := x 4) ?_ ?_
    · rw [inner_sub_right, h1, sub_self]
    · rw [inner_sub_right]; linarith
  exact isRupert_twoFace_limit x T.inj (quad 2 4 6 0) (v := 2) (w := 5) (by decide) ε hε K hK hf'
    (Sa := {2, 4, 5}) (Sb := {0, 2, 3, 5})
    (fun i hi => (T.t245.hf (i₀ := 2) (by decide) i).1 hi)
    (fun i hi => (T.q0235.hf (i₀ := 2) (by decide) i).1 hi) hab G.par G.g1.swapF G.dist
    hσa hσb hsa hsb

set_option maxRecDepth 4000 in
theorem isRupert_pP15 {x : Fin 7 → ℝ³} (T : Type16 x) (K : ℕ → Fin 7 → ℝ³)
    (hK : ∀ m, Tendsto (fun n => K n m) atTop (𝓝 (x m)))
    (hfreq : ∃ᶠ n in atTop, ∃ c : ℝ, c ≠ 0 ∧ RimCertPts (univ.image (K n))
      (c • view16 (K n) (.inl (1, 5))) (quint (K n 1) (K n 4) (K n 2) (K n 0) (K n 6)))
    (hg : Gen15 T) : IsRupert (univ.image x) := by
  obtain ⟨ε, hε, hf⟩ := freq_sign (P := fun c n => RimCertPts (univ.image (K n))
    (c • view16 (K n) (.inl (1, 5))) (quint (K n 1) (K n 4) (K n 2) (K n 0) (K n 6))) (fun n c hc h => rimCertPts_normalize hc h)
    hfreq
  have hf' : ∃ᶠ n in atTop, RimCertAt (K n) (ε • (K n 5 - K n 1)) (quint 1 4 2 0 6) :=
    hf.mono fun n hn => rimCertAt_quint hn
  have G := hg.1
  
  obtain ⟨σa, hσa, hsa⟩ := hs_face T T.t145 (lab := quint 1 4 2 0 6) 0 5 (j₀ := 0) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun m hm h1 h2 h3 => by exfalso; revert hm h1 h2 h3; revert m; decide)
  obtain ⟨σb, hσb, hsb⟩ := hs_face T T.q1356 (lab := quint 1 4 2 0 6) 4 3 (j₀ := 0) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun m hm h1 h2 h3 => by
      obtain rfl : m = 5 := by revert hm h1 h2 h3; revert m; decide
      have adj := T.t146.adj (p := 6) (q := 1) (r := 3) (s := 5) (by decide) (by decide)
        (by decide) (by decide)
      exact ⟨T.t146.N, adj.1, adj.2.1, adj.2.2⟩)
  have hab : cross T.t145.N T.q1356.N ≠ 0 := by
    have h1 := (T.t145.hf (i₀ := 1) (by decide) 4).1 (by decide)
    have h2 := (T.q1356.hf (i₀ := 1) (by decide) 4).2 (by decide)
    refine cross_normals_ne (T.t145.N_ne (i := 1) (j := 0) (by decide) (by decide))
      (p := x 1) (q := x 4) ?_ ?_
    · rw [inner_sub_right, h1, sub_self]
    · rw [inner_sub_right]; linarith
  exact isRupert_twoFace_limit x T.inj (quint 1 4 2 0 6) (v := 1) (w := 5) (by decide) ε hε K hK hf'
    (Sa := {1, 4, 5}) (Sb := {1, 3, 5, 6})
    (fun i hi => (T.t145.hf (i₀ := 1) (by decide) i).1 hi)
    (fun i hi => (T.q1356.hf (i₀ := 1) (by decide) i).1 hi) hab G.par G.g1.swapF G.dist
    hσa hσb hsa hsb

set_option maxRecDepth 4000 in
theorem isRupert_pP25 {x : Fin 7 → ℝ³} (T : Type16 x) (K : ℕ → Fin 7 → ℝ³)
    (hK : ∀ m, Tendsto (fun n => K n m) atTop (𝓝 (x m)))
    (hfreq : ∃ᶠ n in atTop, ∃ c : ℝ, c ≠ 0 ∧ RimCertPts (univ.image (K n))
      (c • view16 (K n) (.inl (2, 5))) (quint (K n 2) (K n 4) (K n 1) (K n 6) (K n 0)))
    (hg : Gen25 T) : IsRupert (univ.image x) := by
  obtain ⟨ε, hε, hf⟩ := freq_sign (P := fun c n => RimCertPts (univ.image (K n))
    (c • view16 (K n) (.inl (2, 5))) (quint (K n 2) (K n 4) (K n 1) (K n 6) (K n 0))) (fun n c hc h => rimCertPts_normalize hc h)
    hfreq
  have hf' : ∃ᶠ n in atTop, RimCertAt (K n) (ε • (K n 5 - K n 2)) (quint 2 4 1 6 0) :=
    hf.mono fun n hn => rimCertAt_quint hn
  have G := hg.1
  
  obtain ⟨σa, hσa, hsa⟩ := hs_face T T.t245 (lab := quint 2 4 1 6 0) 0 5 (j₀ := 0) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun m hm h1 h2 h3 => by exfalso; revert hm h1 h2 h3; revert m; decide)
  obtain ⟨σb, hσb, hsb⟩ := hs_face T T.q0235 (lab := quint 2 4 1 6 0) 4 3 (j₀ := 1) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun m hm h1 h2 h3 => by
      obtain rfl : m = 5 := by revert hm h1 h2 h3; revert m; decide
      have adj := T.t024.adj (p := 0) (q := 2) (r := 3) (s := 5) (by decide) (by decide)
        (by decide) (by decide)
      exact ⟨T.t024.N, adj.1, adj.2.1, adj.2.2⟩)
  have hab : cross T.t245.N T.q0235.N ≠ 0 := by
    have h1 := (T.t245.hf (i₀ := 2) (by decide) 4).1 (by decide)
    have h2 := (T.q0235.hf (i₀ := 2) (by decide) 4).2 (by decide)
    refine cross_normals_ne (T.t245.N_ne (i := 2) (j := 0) (by decide) (by decide))
      (p := x 2) (q := x 4) ?_ ?_
    · rw [inner_sub_right, h1, sub_self]
    · rw [inner_sub_right]; linarith
  exact isRupert_twoFace_limit x T.inj (quint 2 4 1 6 0) (v := 2) (w := 5) (by decide) ε hε K hK hf'
    (Sa := {2, 4, 5}) (Sb := {0, 2, 3, 5})
    (fun i hi => (T.t245.hf (i₀ := 2) (by decide) i).1 hi)
    (fun i hi => (T.q0235.hf (i₀ := 2) (by decide) i).1 hi) hab G.par G.g1.swapF G.dist
    hσa hσb hsa hsb

set_option maxRecDepth 4000 in
theorem isRupert_pP36 {x : Fin 7 → ℝ³} (T : Type16 x) (K : ℕ → Fin 7 → ℝ³)
    (hK : ∀ m, Tendsto (fun n => K n m) atTop (𝓝 (x m)))
    (hfreq : ∃ᶠ n in atTop, ∃ c : ℝ, c ≠ 0 ∧ RimCertPts (univ.image (K n))
      (c • view16 (K n) (.inl (3, 6))) (quint (K n 6) (K n 0) (K n 2) (K n 4) (K n 1)))
    (hg : Gen36 T) : IsRupert (univ.image x) := by
  obtain ⟨ε, hε, hf⟩ := freq_sign (P := fun c n => RimCertPts (univ.image (K n))
    (c • view16 (K n) (.inl (3, 6))) (quint (K n 6) (K n 0) (K n 2) (K n 4) (K n 1))) (fun n c hc h => rimCertPts_normalize hc h)
    hfreq
  have hf' : ∃ᶠ n in atTop, RimCertAt (K n) (ε • (K n 6 - K n 3)) (quint 6 0 2 4 1) :=
    hf.mono fun n hn => rimCertAt_quint hn
  have G := hg.1
  
  obtain ⟨σa, hσa, hsa⟩ := hs_face T T.t036 (lab := quint 6 0 2 4 1) 0 3 (j₀ := 1) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun m hm h1 h2 h3 => by exfalso; revert hm h1 h2 h3; revert m; decide)
  obtain ⟨σb, hσb, hsb⟩ := hs_face T T.q1356 (lab := quint 6 0 2 4 1) 4 3 (j₀ := 0) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun m hm h1 h2 h3 => by
      obtain rfl : m = 5 := by revert hm h1 h2 h3; revert m; decide
      have adj := T.t146.adj (p := 1) (q := 6) (r := 3) (s := 5) (by decide) (by decide)
        (by decide) (by decide)
      exact ⟨T.t146.N, adj.1, adj.2.1, adj.2.2⟩)
  have hab : cross T.t036.N T.q1356.N ≠ 0 := by
    have h1 := (T.t036.hf (i₀ := 6) (by decide) 0).1 (by decide)
    have h2 := (T.q1356.hf (i₀ := 6) (by decide) 0).2 (by decide)
    refine cross_normals_ne (T.t036.N_ne (i := 6) (j := 1) (by decide) (by decide))
      (p := x 6) (q := x 0) ?_ ?_
    · rw [inner_sub_right, h1, sub_self]
    · rw [inner_sub_right]; linarith
  exact isRupert_twoFace_limit x T.inj (quint 6 0 2 4 1) (v := 3) (w := 6) (by decide) ε hε K hK hf'
    (Sa := {0, 3, 6}) (Sb := {1, 3, 5, 6})
    (fun i hi => (T.t036.hf (i₀ := 6) (by decide) i).1 hi)
    (fun i hi => (T.q1356.hf (i₀ := 6) (by decide) i).1 hi) hab G.par G.g1 G.dist
    hσa hσb hsa hsb

set_option maxRecDepth 4000 in
theorem isRupert_pP30 {x : Fin 7 → ℝ³} (T : Type16 x) (K : ℕ → Fin 7 → ℝ³)
    (hK : ∀ m, Tendsto (fun n => K n m) atTop (𝓝 (x m)))
    (hfreq : ∃ᶠ n in atTop, ∃ c : ℝ, c ≠ 0 ∧ RimCertPts (univ.image (K n))
      (c • view16 (K n) (.inl (3, 0))) (quint (K n 0) (K n 6) (K n 1) (K n 4) (K n 2)))
    (hg : Gen03 T) : IsRupert (univ.image x) := by
  obtain ⟨ε, hε, hf⟩ := freq_sign (P := fun c n => RimCertPts (univ.image (K n))
    (c • view16 (K n) (.inl (3, 0))) (quint (K n 0) (K n 6) (K n 1) (K n 4) (K n 2))) (fun n c hc h => rimCertPts_normalize hc h)
    hfreq
  have hf' : ∃ᶠ n in atTop, RimCertAt (K n) (ε • (K n 0 - K n 3)) (quint 0 6 1 4 2) :=
    hf.mono fun n hn => rimCertAt_quint hn
  have G := hg.1.rev
  rw [neg_sub] at G
  obtain ⟨σa, hσa, hsa⟩ := hs_face T T.t036 (lab := quint 0 6 1 4 2) 0 3 (j₀ := 1) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun m hm h1 h2 h3 => by exfalso; revert hm h1 h2 h3; revert m; decide)
  obtain ⟨σb, hσb, hsb⟩ := hs_face T T.q0235 (lab := quint 0 6 1 4 2) 4 3 (j₀ := 1) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun m hm h1 h2 h3 => by
      obtain rfl : m = 5 := by revert hm h1 h2 h3; revert m; decide
      have adj := T.t024.adj (p := 2) (q := 0) (r := 3) (s := 5) (by decide) (by decide)
        (by decide) (by decide)
      exact ⟨T.t024.N, adj.1, adj.2.1, adj.2.2⟩)
  have hab : cross T.t036.N T.q0235.N ≠ 0 := by
    have h1 := (T.t036.hf (i₀ := 0) (by decide) 6).1 (by decide)
    have h2 := (T.q0235.hf (i₀ := 0) (by decide) 6).2 (by decide)
    refine cross_normals_ne (T.t036.N_ne (i := 0) (j := 1) (by decide) (by decide))
      (p := x 0) (q := x 6) ?_ ?_
    · rw [inner_sub_right, h1, sub_self]
    · rw [inner_sub_right]; linarith
  exact isRupert_twoFace_limit x T.inj (quint 0 6 1 4 2) (v := 3) (w := 0) (by decide) ε hε K hK hf'
    (Sa := {0, 3, 6}) (Sb := {0, 2, 3, 5})
    (fun i hi => (T.t036.hf (i₀ := 0) (by decide) i).1 hi)
    (fun i hi => (T.q0235.hf (i₀ := 0) (by decide) i).1 hi) hab G.par G.g1 G.dist
    hσa hσb hsa hsb

/-! ### The limit with the alternatives at the six quadrilateral segments -/

theorem pQuad_noDiag : ∀ q ∈ pQuadLabels16, ∀ i : Fin 7, q.1 ≠ .inl (i, i) := by
  intro q hq i
  simp only [pQuadLabels16, Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [ne_eq, Sum.inl.injEq, Prod.mk.injEq, reduceCtorEq, not_false_eq_true,
      not_and] <;> intro h <;> subst h <;> decide

theorem pQuint_noDiag : ∀ q ∈ pQuintLabels16, ∀ i : Fin 7, q.1 ≠ .inl (i, i) := by
  intro q hq i
  simp only [pQuintLabels16, Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [ne_eq, Sum.inl.injEq, Prod.mk.injEq, reduceCtorEq, not_false_eq_true,
      not_and] <;> intro h <;> subst h <;> decide

/-- **The alternative at the segment views `02`, `16`, `15`, `25`, `03`, `36`** (either
orientation): the codimension-2 conditions at that view. -/
def EdgeOK16 {x : Fin 7 → ℝ³} (T : Type16 x) : (Fin 7 × Fin 7) ⊕ Fin 6 → Prop
  | .inl (i, j) => (({i, j} : Finset (Fin 7)) = {0, 2} ∧ Gen02 T) ∨
      (({i, j} : Finset (Fin 7)) = {1, 6} ∧ Gen16 T) ∨
      (({i, j} : Finset (Fin 7)) = {1, 5} ∧ Gen15 T) ∨
      (({i, j} : Finset (Fin 7)) = {2, 5} ∧ Gen25 T) ∨
      (({i, j} : Finset (Fin 7)) = {0, 3} ∧ Gen03 T) ∨
      (({i, j} : Finset (Fin 7)) = {3, 6} ∧ Gen36 T)
  | .inr _ => False

set_option maxRecDepth 40000 in
theorem ePair_cls : ∀ t ∈ ePairList16,
    (({t.1, t.2.1} : Finset (Fin 7)) = {0, 2} → t = (0, 2, 3, 4, 6)) ∧
    (({t.1, t.2.1} : Finset (Fin 7)) = {1, 6} → t = (6, 1, 3, 4, 0)) ∧
    (({t.1, t.2.1} : Finset (Fin 7)) = {1, 5} → t = (1, 5, 3, 4, 0)) ∧
    (({t.1, t.2.1} : Finset (Fin 7)) = {2, 5} → t = (2, 5, 3, 4, 6)) ∧
    (({t.1, t.2.1} : Finset (Fin 7)) = {0, 3} → t = (0, 3, 6, 2, 4) ∨ t = (3, 0, 6, 2, 4)) ∧
    (({t.1, t.2.1} : Finset (Fin 7)) = {3, 6} → t = (3, 6, 0, 1, 4) ∨ t = (6, 3, 0, 1, 4)) := by
  intro t ht
  simp only [ePairList16, Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl <;> refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

set_option maxRecDepth 40000 in
theorem eTri_cls : ∀ t ∈ eTriList16,
    (({t.1, t.2.1} : Finset (Fin 7)) = {0, 2} → t = (2, 0, 5, 4)) ∧
    (({t.1, t.2.1} : Finset (Fin 7)) = {1, 6} → t = (1, 6, 5, 4)) ∧
    (({t.1, t.2.1} : Finset (Fin 7)) = {1, 5} → t = (1, 5, 4, 6)) ∧
    (({t.1, t.2.1} : Finset (Fin 7)) = {2, 5} → t = (2, 5, 4, 0)) ∧
    ({t.1, t.2.1} : Finset (Fin 7)) ≠ {0, 3} ∧ ({t.1, t.2.1} : Finset (Fin 7)) ≠ {3, 6} := by
  intro t ht
  simp only [eTriList16, Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl <;> refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

set_option maxRecDepth 40000 in
theorem pQuad_cls : ∀ q ∈ pQuadLabels16, ∀ i j : Fin 7, q.1 = .inl (i, j) →
    ({i, j} : Finset (Fin 7)) ≠ {0, 2} ∧ ({i, j} : Finset (Fin 7)) ≠ {1, 6} ∧
    (({i, j} : Finset (Fin 7)) = {1, 5} → q = (.inl (1, 5), (1, 4, 0, 6))) ∧
    (({i, j} : Finset (Fin 7)) = {2, 5} → q = (.inl (2, 5), (2, 4, 6, 0))) ∧
    ({i, j} : Finset (Fin 7)) ≠ {0, 3} ∧ ({i, j} : Finset (Fin 7)) ≠ {3, 6} := by
  intro q hq
  simp only [pQuadLabels16, Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    intro i j h <;> simp only [Sum.inl.injEq, Prod.mk.injEq, reduceCtorEq] at h <;>
    (try obtain ⟨rfl, rfl⟩ := h) <;> decide

theorem pQuint_cls : ∀ q ∈ pQuintLabels16, ∀ i j : Fin 7, q.1 = .inl (i, j) →
    ({i, j} : Finset (Fin 7)) ≠ {0, 2} ∧ ({i, j} : Finset (Fin 7)) ≠ {1, 6} ∧
    (({i, j} : Finset (Fin 7)) = {1, 5} → q = (.inl (1, 5), (1, 4, 2, 0, 6))) ∧
    (({i, j} : Finset (Fin 7)) = {2, 5} → q = (.inl (2, 5), (2, 4, 1, 6, 0))) ∧
    (({i, j} : Finset (Fin 7)) = {0, 3} → q = (.inl (3, 0), (0, 6, 1, 4, 2))) ∧
    (({i, j} : Finset (Fin 7)) = {3, 6} → q = (.inl (3, 6), (6, 0, 2, 4, 1))) := by
  intro q hq
  simp only [pQuintLabels16, Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;>
    intro i j h <;> simp only [Sum.inl.injEq, Prod.mk.injEq, reduceCtorEq] at h <;>
    (try obtain ⟨rfl, rfl⟩ := h) <;> refine ⟨by decide, by decide, ?_, ?_, ?_, ?_⟩ <;>
    intro h' <;> first | rfl | exact absurd h' (by decide)

theorem exists_sgnB {σ : ℝ} (h : σ = 1 ∨ σ = -1) : ∃ s : Bool, σ = sgnB s := by
  rcases h with rfl | rfl
  exacts [⟨true, rfl⟩, ⟨false, rfl⟩]

/-- **Lemma 18.2 over the cover's certificates, with §22**: at every named view of a frequent
certificate, no horizontal double normal, or `Sec16` (two triangles, Proposition 22.2), or the
codimension-2 conditions at the six quadrilateral segments `02`, `16`, `15`, `25`, `03`, `36`
(`EdgeOK16`). -/
theorem isRupert_of_cert_seq_edge {x : Fin 7 → ℝ³} (T : Type16 x)
    (hnd : ∀ v, view16 x v ≠ 0 → NoHDNAt (univ.image x) (view16 x v) ∨ Sec16 x v ∨ EdgeOK16 T v)
    (K : ℕ → Fin 7 → ℝ³) (hK : ∀ m, Tendsto (fun n => K n m) atTop (𝓝 (x m)))
    (hc : ∃ᶠ n in atTop, Cert16 (K n) ∧
      ∀ w a b, TieInst16 x w a b → ⟪K n a - K n b, view16 (K n) w⟫ = 0) :
    IsRupert (univ.image x) := by
  classical
  have h3 := hc.mono fun n hn => (show (CertE16 (K n) ∧ _) ∨ (CertT16 (K n) ∧ _) ∨
    (CertP16 (K n) ∧ _) by
      rcases hn.1 with h | h | h
      exacts [Or.inl ⟨h, hn.2⟩, Or.inr (Or.inl ⟨h, hn.2⟩), Or.inr (Or.inr ⟨h, hn.2⟩)])
  rcases frequently_or_distrib.mp h3 with hE | h3'
  · -- edge pairs
    have hq : ∃ᶠ n in atTop, ∃ q : (Fin 7 × Fin 7 × Fin 7 × Fin 7 × Fin 7) × Bool,
        q.1 ∈ ePairList16 ∧ EPairData (univ.image (K n)) (sgnB q.2) (K n q.1.1) (K n q.1.2.1)
          (K n q.1.2.2.1) (K n q.1.2.2.2.1) (K n q.1.2.2.2.2) ∧
        ∀ w a b, TieInst16 x w a b → ⟪K n a - K n b, view16 (K n) w⟫ = 0 :=
      hE.mono fun n hn => by
        obtain ⟨⟨v, w, a, b, c, ht, σ, hd⟩, hti⟩ := hn
        obtain ⟨s, rfl⟩ := exists_sgnB hd.1
        exact ⟨((v, w, a, b, c), s), ht, hd, hti⟩
    obtain ⟨⟨⟨v, w, a, b, c⟩, s⟩, hq'⟩ := frequently_exists_of_finite hq
    obtain ⟨n₀, ⟨ht, -⟩⟩ := hq'.exists
    have hvw : v ≠ w := by
      intro e; obtain ⟨n₁, -, hd, -⟩ := hq'.exists
      have := hd.2.1; rw [e, sub_self] at this; simp [det3_expand] at this
    have hrc : ∃ᶠ n in atTop, (∃ c : ℝ, c ≠ 0 ∧
        RimCert (univ.image (K n)) (c • view16 (K n) (.inl (v, w)))) ∧
        ∀ w a b, TieInst16 x w a b → ⟪K n a - K n b, view16 (K n) w⟫ = 0 :=
      hq'.mono fun n hn => by
        obtain ⟨-, hd, hti⟩ := hn
        refine ⟨⟨1, one_ne_zero, ?_⟩, hti⟩
        rw [one_smul]
        exact rimCert_edgePairσ_robust _ hd.1 (mem_image7 v) (mem_image7 w) (mem_image7 a)
          (mem_image7 b) (mem_image7 c) hd.2.1 hd.2.2.1 hd.2.2.2.1 hd.2.2.2.2.1 hd.2.2.2.2.2.1
          hd.2.2.2.2.2.2.1 hd.2.2.2.2.2.2.2
    have hd' := hq'.mono fun n hn => hn.2.1
    have cls := ePair_cls _ ht
    rcases hnd (.inl (v, w)) (sub_ne_zero.mpr (T.inj.ne hvw.symm)) with h | h | h
    · exact isRupert_of_rimCert_seq_at T K hK (.inl (v, w)) (fun _ => Or.inl h) hrc
    · exact isRupert_of_rimCert_seq_at T K hK (.inl (v, w)) (fun _ => Or.inr h) hrc
    · rcases h with ⟨h1, hg⟩ | ⟨h1, hg⟩ | ⟨h1, hg⟩ | ⟨h1, hg⟩ | ⟨h1, hg⟩ | ⟨h1, hg⟩
      · have := cls.1 h1
        simp only [Prod.mk.injEq] at this
        obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := this
        exact isRupert_ePair02 T K hK s hd' hg
      · have := cls.2.1 h1
        simp only [Prod.mk.injEq] at this
        obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := this
        exact isRupert_ePair61 T K hK s hd' hg
      · have := cls.2.2.1 h1
        simp only [Prod.mk.injEq] at this
        obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := this
        exact isRupert_ePair15 T K hK s hd' hg
      · have := cls.2.2.2.1 h1
        simp only [Prod.mk.injEq] at this
        obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := this
        exact isRupert_ePair25 T K hK s hd' hg
      · rcases cls.2.2.2.2.1 h1 with this | this <;> simp only [Prod.mk.injEq] at this <;>
          obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := this
        · exact isRupert_ePair03 T K hK s hd' hg
        · exact isRupert_ePair30 T K hK s hd' hg
      · rcases cls.2.2.2.2.2 h1 with this | this <;> simp only [Prod.mk.injEq] at this <;>
          obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := this
        · exact isRupert_ePair36 T K hK s hd' hg
        · exact isRupert_ePair63 T K hK s hd' hg
  rcases frequently_or_distrib.mp h3' with hT' | hP
  · -- triangle closings
    have hq : ∃ᶠ n in atTop, ∃ q : (Fin 7 × Fin 7 × Fin 7 × Fin 7) × Bool,
        q.1 ∈ eTriList16 ∧ ETriData (univ.image (K n)) (sgnB q.2) (K n q.1.1) (K n q.1.2.1)
          (K n q.1.2.2.1) (K n q.1.2.2.2) ∧
        ∀ w a b, TieInst16 x w a b → ⟪K n a - K n b, view16 (K n) w⟫ = 0 :=
      hT'.mono fun n hn => by
        obtain ⟨⟨v, w, a, b, ht, σ, hd⟩, hti⟩ := hn
        obtain ⟨s, rfl⟩ := exists_sgnB hd.1
        exact ⟨((v, w, a, b), s), ht, hd, hti⟩
    obtain ⟨⟨⟨v, w, a, b⟩, s⟩, hq'⟩ := frequently_exists_of_finite hq
    obtain ⟨n₀, ⟨ht, -⟩⟩ := hq'.exists
    have hvw : v ≠ w := by
      intro e; obtain ⟨n₁, -, hd, -⟩ := hq'.exists
      have := hd.2.1; rw [e, sub_self] at this; simp [det3_expand] at this
    have hrc : ∃ᶠ n in atTop, (∃ c : ℝ, c ≠ 0 ∧
        RimCert (univ.image (K n)) (c • view16 (K n) (.inl (v, w)))) ∧
        ∀ w a b, TieInst16 x w a b → ⟪K n a - K n b, view16 (K n) w⟫ = 0 :=
      hq'.mono fun n hn => by
        obtain ⟨-, hd, hti⟩ := hn
        refine ⟨⟨1, one_ne_zero, ?_⟩, hti⟩
        rw [one_smul]
        exact rimCert_edgeTriσ_robust _ hd.1 (mem_image7 v) (mem_image7 w) (mem_image7 a)
          (mem_image7 b) hd.2.1 hd.2.2.1 hd.2.2.2
    have hd' := hq'.mono fun n hn => hn.2.1
    have cls := eTri_cls _ ht
    rcases hnd (.inl (v, w)) (sub_ne_zero.mpr (T.inj.ne hvw.symm)) with h | h | h
    · exact isRupert_of_rimCert_seq_at T K hK (.inl (v, w)) (fun _ => Or.inl h) hrc
    · exact isRupert_of_rimCert_seq_at T K hK (.inl (v, w)) (fun _ => Or.inr h) hrc
    · rcases h with ⟨h1, hg⟩ | ⟨h1, hg⟩ | ⟨h1, hg⟩ | ⟨h1, hg⟩ | ⟨h1, hg⟩ | ⟨h1, hg⟩
      · have := cls.1 h1
        simp only [Prod.mk.injEq] at this
        obtain ⟨rfl, rfl, rfl, rfl⟩ := this
        exact isRupert_eTri20 T K hK s hd' hg
      · have := cls.2.1 h1
        simp only [Prod.mk.injEq] at this
        obtain ⟨rfl, rfl, rfl, rfl⟩ := this
        exact isRupert_eTri16 T K hK s hd' hg
      · have := cls.2.2.1 h1
        simp only [Prod.mk.injEq] at this
        obtain ⟨rfl, rfl, rfl, rfl⟩ := this
        exact isRupert_eTri15 T K hK s hd' hg
      · have := cls.2.2.2.1 h1
        simp only [Prod.mk.injEq] at this
        obtain ⟨rfl, rfl, rfl, rfl⟩ := this
        exact isRupert_eTri25 T K hK s hd' hg
      · exact absurd h1 cls.2.2.2.2.1
      · exact absurd h1 cls.2.2.2.2.2
  · -- the pair certificates of Lemmas 19.3–19.5
    have hP' := hP.mono fun n hn => (show (_ ∧ _) ∨ (_ ∧ _) by
      rcases hn.1 with h | h
      exacts [Or.inl ⟨h, hn.2⟩, Or.inr ⟨h, hn.2⟩])
    rcases frequently_or_distrib.mp hP' with hQ | hQ
    · have hq : ∃ᶠ n in atTop, ∃ q : ((Fin 7 × Fin 7) ⊕ Fin 6) × (Fin 7 × Fin 7 × Fin 7 × Fin 7),
          q ∈ pQuadLabels16 ∧ (∃ c : ℝ, c ≠ 0 ∧ RimCertPts (univ.image (K n))
            (c • view16 (K n) q.1) (quad (K n q.2.1) (K n q.2.2.1) (K n q.2.2.2.1)
              (K n q.2.2.2.2))) ∧
          ∀ w a b, TieInst16 x w a b → ⟪K n a - K n b, view16 (K n) w⟫ = 0 :=
        hQ.mono fun n hn => by
          obtain ⟨⟨v, l, hl, c, hc, hr⟩, hti⟩ := hn
          exact ⟨(v, l), hl, ⟨c, hc, hr⟩, hti⟩
      obtain ⟨⟨v, ⟨l₀, l₁, l₂, l₃⟩⟩, hq'⟩ := frequently_exists_of_finite hq
      obtain ⟨n₀, hl, -⟩ := hq'.exists
      have hrc : ∃ᶠ n in atTop, (∃ c : ℝ, c ≠ 0 ∧
          RimCert (univ.image (K n)) (c • view16 (K n) v)) ∧
          ∀ w a b, TieInst16 x w a b → ⟪K n a - K n b, view16 (K n) w⟫ = 0 :=
        hq'.mono fun n hn => by
          obtain ⟨-, ⟨c, hc, hr⟩, hti⟩ := hn
          exact ⟨⟨c, hc, hr.rimCert (Or.inr (Or.inl rfl))⟩, hti⟩
      have hvv : ∀ i, v ≠ .inl (i, i) := fun i h => pQuad_noDiag _ hl i h
      rcases hnd v (T.view16_ne_zero v hvv) with h | h | h
      · exact isRupert_of_rimCert_seq_at T K hK v (fun _ => Or.inl h) hrc
      · exact isRupert_of_rimCert_seq_at T K hK v (fun _ => Or.inr h) hrc
      · rcases v with ⟨i, j⟩ | t
        · have cls := pQuad_cls _ hl i j rfl
          have hd' := hq'.mono fun n hn => hn.2.1
          rcases h with ⟨h1, hg⟩ | ⟨h1, hg⟩ | ⟨h1, hg⟩ | ⟨h1, hg⟩ | ⟨h1, hg⟩ | ⟨h1, hg⟩
          · exact absurd h1 cls.1
          · exact absurd h1 cls.2.1
          · have := cls.2.2.1 h1
            simp only [Prod.mk.injEq, Sum.inl.injEq] at this
            obtain ⟨⟨rfl, rfl⟩, rfl, rfl, rfl, rfl⟩ := this
            exact isRupert_pQ15 T K hK hd' hg
          · have := cls.2.2.2.1 h1
            simp only [Prod.mk.injEq, Sum.inl.injEq] at this
            obtain ⟨⟨rfl, rfl⟩, rfl, rfl, rfl, rfl⟩ := this
            exact isRupert_pQ25 T K hK hd' hg
          · exact absurd h1 cls.2.2.2.2.1
          · exact absurd h1 cls.2.2.2.2.2
        · exact h.elim
    · have hq : ∃ᶠ n in atTop, ∃ q : ((Fin 7 × Fin 7) ⊕ Fin 6) ×
          (Fin 7 × Fin 7 × Fin 7 × Fin 7 × Fin 7), q ∈ pQuintLabels16 ∧
          (∃ c : ℝ, c ≠ 0 ∧ RimCertPts (univ.image (K n)) (c • view16 (K n) q.1)
            (quint (K n q.2.1) (K n q.2.2.1) (K n q.2.2.2.1) (K n q.2.2.2.2.1)
              (K n q.2.2.2.2.2))) ∧
          ∀ w a b, TieInst16 x w a b → ⟪K n a - K n b, view16 (K n) w⟫ = 0 :=
        hQ.mono fun n hn => by
          obtain ⟨⟨v, l, hl, c, hc, hr⟩, hti⟩ := hn
          exact ⟨(v, l), hl, ⟨c, hc, hr⟩, hti⟩
      obtain ⟨⟨v, ⟨l₀, l₁, l₂, l₃, l₄⟩⟩, hq'⟩ := frequently_exists_of_finite hq
      obtain ⟨n₀, hl, -⟩ := hq'.exists
      have hrc : ∃ᶠ n in atTop, (∃ c : ℝ, c ≠ 0 ∧
          RimCert (univ.image (K n)) (c • view16 (K n) v)) ∧
          ∀ w a b, TieInst16 x w a b → ⟪K n a - K n b, view16 (K n) w⟫ = 0 :=
        hq'.mono fun n hn => by
          obtain ⟨-, ⟨c, hc, hr⟩, hti⟩ := hn
          exact ⟨⟨c, hc, hr.rimCert (Or.inr (Or.inr rfl))⟩, hti⟩
      have hvv : ∀ i, v ≠ .inl (i, i) := fun i h => pQuint_noDiag _ hl i h
      rcases hnd v (T.view16_ne_zero v hvv) with h | h | h
      · exact isRupert_of_rimCert_seq_at T K hK v (fun _ => Or.inl h) hrc
      · exact isRupert_of_rimCert_seq_at T K hK v (fun _ => Or.inr h) hrc
      · rcases v with ⟨i, j⟩ | t
        · have cls := pQuint_cls _ hl i j rfl
          have hd' := hq'.mono fun n hn => hn.2.1
          rcases h with ⟨h1, hg⟩ | ⟨h1, hg⟩ | ⟨h1, hg⟩ | ⟨h1, hg⟩ | ⟨h1, hg⟩ | ⟨h1, hg⟩
          · exact absurd h1 cls.1
          · exact absurd h1 cls.2.1
          · have := cls.2.2.1 h1
            simp only [Prod.mk.injEq, Sum.inl.injEq] at this
            obtain ⟨⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl⟩ := this
            exact isRupert_pP15 T K hK hd' hg
          · have := cls.2.2.2.1 h1
            simp only [Prod.mk.injEq, Sum.inl.injEq] at this
            obtain ⟨⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl⟩ := this
            exact isRupert_pP25 T K hK hd' hg
          · have := cls.2.2.2.2.1 h1
            simp only [Prod.mk.injEq, Sum.inl.injEq] at this
            obtain ⟨⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl⟩ := this
            exact isRupert_pP30 T K hK hd' hg
          · have := cls.2.2.2.2.2 h1
            simp only [Prod.mk.injEq, Sum.inl.injEq] at this
            obtain ⟨⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl⟩ := this
            exact isRupert_pP36 T K hK hd' hg
        · exact h.elim

/-- **Theorem 19.8 with §22 at the six quadrilateral segments**: a type-16 shape with at most one
tie at its named views is Rupert if at each named view there is no horizontal double normal, or
`Sec16` (a two-triangle view with (G1)), or the codimension-2 conditions `EdgeOK16`. -/
theorem isRupert_type16_limit_edge {x : Fin 7 → ℝ³} (T : Type16 x)
    (hnd : ∀ v, view16 x v ≠ 0 → NoHDNAt (univ.image x) (view16 x v) ∨ Sec16 x v ∨ EdgeOK16 T v)
    (htie : OneTie16 x) : IsRupert (univ.image x) := by
  obtain ⟨K, hK, hc⟩ := exists_certSeq16 T htie
  exact isRupert_of_cert_seq_edge T hnd K hK hc

/-! ### The facets form -/

/-- **The codimension-2 conditions at the segment `i j` between the facets `SA`, `SB`**, from
their functions `fA`, `fB`: `EdgeGen` at the view `x j − x i` for the normals of the two facets,
and `i`, `j` off the plane `p q r` of Lemma E. -/
def EdgeGenAff (x : Fin 7 → ℝ³) (fA fB : ℝ³ →ᵃ[ℝ] ℝ) (i j : Fin 7) (SA SB : Finset (Fin 7))
    (p q r : Fin 7) : Prop :=
  (∀ NA NB : ℝ³, (∀ y, fA.linear y = ⟪NA, y⟫) → (∀ y, fB.linear y = ⟪NB, y⟫) →
    EdgeGen (univ.image x) (x j - x i) (x i) (x j) (SA.image x) (SB.image x) NA NB) ∧
  det3 (x q - x p) (x r - x p) (x i - x p) ≠ 0 ∧ det3 (x q - x p) (x r - x p) (x j - x p) ≠ 0

theorem pair_eq_pair16 {a b i j : Fin 7} (h : ({i, j} : Finset (Fin 7)) = {a, b}) :
    (i = a ∧ j = b) ∨ (i = b ∧ j = a) := by
  have h' := congrArg (fun s : Finset (Fin 7) => (s : Set (Fin 7))) h
  simp only [Finset.coe_insert, Finset.coe_singleton] at h'
  exact Set.pair_eq_pair_iff.mp h'

theorem quad_alt16 {x : Fin 7 → ℝ³} (T : Type16 x) {a b i j : Fin 7}
    (hp : ({i, j} : Finset (Fin 7)) = {a, b}) {G : Prop}
    (h : NoHDNAt (univ.image x) (x b - x a) ∨ G) (hG : G → EdgeOK16 T (.inl (i, j))) :
    NoHDNAt (univ.image x) (view16 x (.inl (i, j))) ∨ Sec16 x (.inl (i, j)) ∨
      EdgeOK16 T (.inl (i, j)) := by
  rcases h with h | h
  · left
    show NoHDNAt _ (x j - x i)
    rcases pair_eq_pair16 hp with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]; exact h
    · rw [h1, h2, ← neg_sub]; exact h.neg
  · exact Or.inr (Or.inr (hG h))

/-- The two-triangle edges and the six quadrilateral segments `02`, `16`, `15`, `25`, `03`,
`36`. -/
def edgeSet16 : Finset (Finset (Fin 7)) :=
  {{0, 4}, {0, 6}, {1, 4}, {2, 4}, {4, 5}, {4, 6}, {0, 2}, {1, 6}, {1, 5}, {2, 5}, {0, 3}, {3, 6}}

/-- **Theorem 19.8 with Proposition 22.2 and §22, from the facets**: as
`isRupert_type16_limit_facets_sec`, with each of the segments `02`, `16`, `15`, `25`, `03`, `36`
(each an edge of a quadrilateral and a triangle) asking
only "no horizontal double normal, or the codimension-2 conditions of §22" (`hQ`). -/
theorem isRupert_type16_limit_facets_edge (x : Fin 7 → ℝ³) (hx : Function.Injective x)
    (fA fB fC fD fE fF fG fH : ℝ³ →ᵃ[ℝ] ℝ)
    (hA : ∀ i, (i ∈ ({0, 2, 3, 5} : Finset (Fin 7)) → fA (x i) = 0) ∧
      (i ∉ ({0, 2, 3, 5} : Finset (Fin 7)) → fA (x i) < 0))
    (hB : ∀ i, (i ∈ ({1, 3, 5, 6} : Finset (Fin 7)) → fB (x i) = 0) ∧
      (i ∉ ({1, 3, 5, 6} : Finset (Fin 7)) → fB (x i) < 0))
    (hC : ∀ i, (i ∈ ({0, 2, 4} : Finset (Fin 7)) → fC (x i) = 0) ∧
      (i ∉ ({0, 2, 4} : Finset (Fin 7)) → fC (x i) < 0))
    (hD : ∀ i, (i ∈ ({0, 3, 6} : Finset (Fin 7)) → fD (x i) = 0) ∧
      (i ∉ ({0, 3, 6} : Finset (Fin 7)) → fD (x i) < 0))
    (hE : ∀ i, (i ∈ ({0, 4, 6} : Finset (Fin 7)) → fE (x i) = 0) ∧
      (i ∉ ({0, 4, 6} : Finset (Fin 7)) → fE (x i) < 0))
    (hF : ∀ i, (i ∈ ({1, 4, 5} : Finset (Fin 7)) → fF (x i) = 0) ∧
      (i ∉ ({1, 4, 5} : Finset (Fin 7)) → fF (x i) < 0))
    (hG : ∀ i, (i ∈ ({1, 4, 6} : Finset (Fin 7)) → fG (x i) = 0) ∧
      (i ∉ ({1, 4, 6} : Finset (Fin 7)) → fG (x i) < 0))
    (hH : ∀ i, (i ∈ ({2, 4, 5} : Finset (Fin 7)) → fH (x i) = 0) ∧
      (i ∉ ({2, 4, 5} : Finset (Fin 7)) → fH (x i) < 0))
    (hnd : ∀ i j : Fin 7, i ≠ j → ({i, j} : Finset (Fin 7)) ∉ edgeSet16 →
      NoHDNAt ((univ.image x).erase (x j)) (x j - x i))
    (hEd : HDNOrG1Edge (univ.image x) (x 0) (x 4) (x 2) (x 6) ∧
      HDNOrG1Edge (univ.image x) (x 0) (x 6) (x 3) (x 4) ∧
      HDNOrG1Edge (univ.image x) (x 1) (x 4) (x 5) (x 6) ∧
      HDNOrG1Edge (univ.image x) (x 2) (x 4) (x 0) (x 5) ∧
      HDNOrG1Edge (univ.image x) (x 4) (x 5) (x 1) (x 2) ∧
      HDNOrG1Edge (univ.image x) (x 4) (x 6) (x 0) (x 1))
    (hQ : (NoHDNAt (univ.image x) (x 2 - x 0) ∨
        EdgeGenAff x fA fC 0 2 {0, 2, 3, 5} {0, 2, 4} 3 4 6) ∧
      (NoHDNAt (univ.image x) (x 1 - x 6) ∨
        EdgeGenAff x fB fG 6 1 {1, 3, 5, 6} {1, 4, 6} 3 4 0) ∧
      (NoHDNAt (univ.image x) (x 5 - x 1) ∨
        EdgeGenAff x fB fF 1 5 {1, 3, 5, 6} {1, 4, 5} 3 4 0) ∧
      (NoHDNAt (univ.image x) (x 5 - x 2) ∨
        EdgeGenAff x fA fH 2 5 {0, 2, 3, 5} {2, 4, 5} 3 4 6) ∧
      (NoHDNAt (univ.image x) (x 3 - x 0) ∨
        EdgeGenAff x fD fA 0 3 {0, 3, 6} {0, 2, 3, 5} 6 2 4) ∧
      (NoHDNAt (univ.image x) (x 6 - x 3) ∨
        EdgeGenAff x fD fB 3 6 {0, 3, 6} {1, 3, 5, 6} 0 1 4))
    (hV : HDNOrG1Aff (univ.image x) fE fF (x 0) (x 4) (x 6) (x 1) (x 4) (x 5) ∧
      HDNOrG1Aff (univ.image x) fD fG (x 0) (x 3) (x 6) (x 1) (x 4) (x 6) ∧
      NoHDNAff (univ.image x) fA fE ∧
      HDNOrG1Aff (univ.image x) fE fH (x 6) (x 4) (x 0) (x 2) (x 4) (x 5) ∧
      HDNOrG1Aff (univ.image x) fD fC (x 6) (x 3) (x 0) (x 2) (x 4) (x 0) ∧
      NoHDNAff (univ.image x) fB fE)
    (htie : OneTie16 x) : IsRupert (univ.image x) := by
  let T : Type16 x := ⟨hx, Face16.ofAffine fA hA, Face16.ofAffine fB hB, Face16.ofAffine fC hC,
    Face16.ofAffine fD hD, Face16.ofAffine fE hE, Face16.ofAffine fF hF, Face16.ofAffine fG hG,
    Face16.ofAffine fH hH⟩
  obtain ⟨q02, q16, q15, q25, q03, q36⟩ := hQ
  have g02 : EdgeGenAff x fA fC 0 2 {0, 2, 3, 5} {0, 2, 4} 3 4 6 → Gen02 T := fun h =>
    ⟨h.1 _ _ (fun y => (Face16.ofAffine_inner fA hA y).symm)
      (fun y => (Face16.ofAffine_inner fC hC y).symm), h.2⟩
  have g16 : EdgeGenAff x fB fG 6 1 {1, 3, 5, 6} {1, 4, 6} 3 4 0 → Gen16 T := fun h =>
    ⟨h.1 _ _ (fun y => (Face16.ofAffine_inner fB hB y).symm)
      (fun y => (Face16.ofAffine_inner fG hG y).symm), h.2⟩
  have g15 : EdgeGenAff x fB fF 1 5 {1, 3, 5, 6} {1, 4, 5} 3 4 0 → Gen15 T := fun h =>
    ⟨h.1 _ _ (fun y => (Face16.ofAffine_inner fB hB y).symm)
      (fun y => (Face16.ofAffine_inner fF hF y).symm), h.2⟩
  have g25 : EdgeGenAff x fA fH 2 5 {0, 2, 3, 5} {2, 4, 5} 3 4 6 → Gen25 T := fun h =>
    ⟨h.1 _ _ (fun y => (Face16.ofAffine_inner fA hA y).symm)
      (fun y => (Face16.ofAffine_inner fH hH y).symm), h.2⟩
  have g03 : EdgeGenAff x fD fA 0 3 {0, 3, 6} {0, 2, 3, 5} 6 2 4 → Gen03 T := fun h =>
    ⟨h.1 _ _ (fun y => (Face16.ofAffine_inner fD hD y).symm)
      (fun y => (Face16.ofAffine_inner fA hA y).symm), h.2⟩
  have g36 : EdgeGenAff x fD fB 3 6 {0, 3, 6} {1, 3, 5, 6} 0 1 4 → Gen36 T := fun h =>
    ⟨h.1 _ _ (fun y => (Face16.ofAffine_inner fD hD y).symm)
      (fun y => (Face16.ofAffine_inner fB hB y).symm), h.2⟩
  have hE' : ∀ e : Fin 6, HDNOrG1Edge (univ.image x) (x (triEdge16 e).1) (x (triEdge16 e).2.1)
      (x (triEdge16 e).2.2.1) (x (triEdge16 e).2.2.2) := by
    obtain ⟨e0, e1, e2, e3, e4, e5⟩ := hEd
    intro e; fin_cases e
    exacts [e0, e1, e2, e3, e4, e5]
  refine isRupert_type16_limit_edge T (fun v hv => ?_) htie
  rcases v with ⟨i, j⟩ | t
  · have hij : i ≠ j := fun h => hv (by simp [view16, h])
    by_cases hmem : ({i, j} : Finset (Fin 7)) ∈ triEdgeSet16
    · obtain ⟨e, he⟩ := triEdgeSet16_mem i j hmem
      rcases hE' e with h | h
      · left
        rcases he with ⟨e1, e2⟩ | ⟨e1, e2⟩
        · show NoHDNAt _ (x j - x i)
          rw [← e1, ← e2]; exact h
        · show NoHDNAt _ (x j - x i)
          rw [← e1, ← e2, ← neg_sub]; exact h.neg
      · exact Or.inr (Or.inl ⟨e, he, h⟩)
    by_cases p02 : ({i, j} : Finset (Fin 7)) = {0, 2}
    · exact quad_alt16 T p02 q02 fun h => Or.inl ⟨p02, g02 h⟩
    by_cases p16 : ({i, j} : Finset (Fin 7)) = {6, 1}
    · exact quad_alt16 T p16 q16 fun h =>
        Or.inr (Or.inl ⟨p16.trans (Finset.pair_comm _ _), g16 h⟩)
    by_cases p15 : ({i, j} : Finset (Fin 7)) = {1, 5}
    · exact quad_alt16 T p15 q15 fun h => Or.inr (Or.inr (Or.inl ⟨p15, g15 h⟩))
    by_cases p25 : ({i, j} : Finset (Fin 7)) = {2, 5}
    · exact quad_alt16 T p25 q25 fun h => Or.inr (Or.inr (Or.inr (Or.inl ⟨p25, g25 h⟩)))
    by_cases p03 : ({i, j} : Finset (Fin 7)) = {0, 3}
    · exact quad_alt16 T p03 q03 fun h =>
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p03, g03 h⟩))))
    by_cases p36 : ({i, j} : Finset (Fin 7)) = {3, 6}
    · exact quad_alt16 T p36 q36 fun h =>
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨p36, g36 h⟩))))
    left
    have hmem' : ({i, j} : Finset (Fin 7)) ∉ edgeSet16 := by
      intro hc
      have p16' : ({i, j} : Finset (Fin 7)) ≠ {1, 6} := by rwa [Finset.pair_comm 1 6]
      simp only [edgeSet16, mem_insert, mem_singleton] at hc
      rcases hc with h | h | h | h | h | h | h | h | h | h | h | h
      all_goals first
        | exact hmem (by rw [h]; decide) | exact p02 h | exact p16' h | exact p15 h
        | exact p25 h | exact p03 h | exact p36 h
    have hji : ({j, i} : Finset (Fin 7)) ∉ edgeSet16 := by rwa [Finset.pair_comm]
    exact noHDNAt_of_erase (hx.ne hij) (hnd i j hij hmem')
      (by simpa only [neg_sub] using (hnd j i (Ne.symm hij) hji).neg)
  · obtain ⟨V1, V2, V3, V4, V5, V6⟩ := hV
    fin_cases t
    · rcases V1 _ hv (affine_planeLine_perp fE hE (by decide) (by decide) (by decide))
        (affine_planeLine_perp' fF hF (by decide)
        (by decide) (by decide)) with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl ⟨Or.inl rfl, h⟩)
    · rcases V2 _ hv (affine_planeLine_perp fD hD (by decide) (by decide) (by decide))
        (affine_planeLine_perp' fG hG (by decide)
        (by decide) (by decide)) with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl ⟨Or.inr (Or.inl rfl), h⟩)
    · exact Or.inl (V3 _ hv (affine_planeLine_perp fA hA (by decide) (by decide) (by decide))
        (affine_planeLine_perp' fE hE (by decide)
        (by decide) (by decide)))
    · rcases V4 _ hv (affine_planeLine_perp fE hE (by decide) (by decide) (by decide))
        (affine_planeLine_perp' fH hH (by decide)
        (by decide) (by decide)) with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl ⟨Or.inr (Or.inr (Or.inl rfl)), h⟩)
    · rcases V5 _ hv (affine_planeLine_perp fD hD (by decide) (by decide) (by decide))
        (affine_planeLine_perp' fC hC (by decide)
        (by decide) (by decide)) with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl ⟨Or.inr (Or.inr (Or.inr rfl)), h⟩)
    · exact Or.inl (V6 _ hv (affine_planeLine_perp fB hB (by decide) (by decide) (by decide))
        (affine_planeLine_perp' fE hE (by decide)
        (by decide) (by decide)))

end Minimality

end
