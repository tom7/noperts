module

public import Minimality.Type16Sector
public import Minimality.EdgeTwoFace

@[expose] public section

/-!
# Type 16: no horizontal-double-normal exception at the segments `02` and `16` (§22)

The certificates of the cover at the views along `02` and `16` (and the reversed `20`, `61`)
are the edge pairs `(0, 2, 3, 4, 6)` (U3) and `(6, 1, 3, 4, 0)` (its `σ`-image) and the triangle
closings `(2, 0, 5, 4)`, `(1, 6, 5, 4)` (D5 and its image); no pair certificate of Lemmas
19.3–19.5 uses these views (`pairsViews16`).  At the limit (Lemma 18.2), §22 closes the edge pairs
(`isRupert_ePair_limit`: Proposition 22.2, Lemmas 22.3–22.7, Theorem 22.8 with Lemma E) and the
triangle closings (`isRupert_eTri_limit`: two realizing circles) under the codimension-2
conditions `Gen02`, `Gen16` (`EdgeGen` at the view, and the axle off the plane of Lemma E), so
there no horizontal-double-normal hypothesis is left.

* `isRupert_of_certL_seq_at`, `isRupert_of_rimCert_seq_at`: Lemma 18.2 with the alternative of
  `Sec16` asked only at the certificate's view.
* `Gen02`, `Gen16`, `EdgeOK16`.
* `isRupert_of_cert_seq_edge`, `isRupert_type16_limit_edge`.
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

/-! ### Lemma 18.2 at one view -/

/-- **Lemma 18.2 for one labelled certificate**, with "no horizontal double normal or `Sec16`"
asked only at its view. -/
theorem isRupert_of_certL_seq_at {x : Fin 7 → ℝ³} (T : Type16 x)
    (K : ℕ → Fin 7 → ℝ³) (hK : ∀ m, Tendsto (fun n => K n m) atTop (𝓝 (x m)))
    {k : ℕ} [NeZero k] (v : (Fin 7 × Fin 7) ⊕ Fin 6) (ε : Bool) (lab : ZMod k → Fin 7)
    (hnd : view16 x v ≠ 0 → NoHDNAt (univ.image x) (view16 x v) ∨ Sec16 x v)
    (hc : ∃ᶠ n in atTop, RimCertAt (K n) (sgnB ε • view16 (K n) v) lab ∧
      ∀ w a b, TieInst16 x w a b → ⟪K n a - K n b, view16 (K n) w⟫ = 0) :
    IsRupert (univ.image x) := by
  obtain ⟨n₀, hn₀, -⟩ := hc.exists
  have hv : ∀ i, v ≠ .inl (i, i) := by
    rintro i rfl
    apply hn₀.ne_zero
    simp [view16]
  have hv0 := T.view16_ne_zero v hv
  have hs := sgnB_ne_zero ε
  refine isRupert_of_tendsto_rimCert_or x T.inj T.noSeg ⟨3, 0, 5, 6, T.det_ne⟩ lab
    (smul_ne_zero hs hv0) ?_ K (fun n => sgnB ε • view16 (K n) v) hK
    ((tendsto_view16 hK v).const_smul _) (hc.mono fun n hn => ⟨hn.1, fun i j e => ?_⟩)
  · rcases hnd hv0 with h | h
    · exact Or.inl (h.smul_view hs)
    · exact Or.inr fun hleft => h.tiltHides T hv0 ε hn₀ hleft
  · by_cases hij : lab i = lab j
    · rw [hij]
    · rw [real_inner_smul_right, real_inner_smul_right] at e
      have e' := mul_left_cancel₀ hs e
      have h := hn.2 v (lab i) (lab j) ⟨hij, hv0, by rw [inner_sub_left, e', sub_self]⟩
      rw [inner_sub_left, sub_eq_zero] at h
      simp only [real_inner_smul_right, h]

/-- **A frequent rim certificate at one named view** (any nonzero multiple), with the
alternative of `Sec16` at that view. -/
theorem isRupert_of_rimCert_seq_at {x : Fin 7 → ℝ³} (T : Type16 x)
    (K : ℕ → Fin 7 → ℝ³) (hK : ∀ m, Tendsto (fun n => K n m) atTop (𝓝 (x m)))
    (v : (Fin 7 × Fin 7) ⊕ Fin 6)
    (hnd : view16 x v ≠ 0 → NoHDNAt (univ.image x) (view16 x v) ∨ Sec16 x v)
    (hc : ∃ᶠ n in atTop, (∃ c : ℝ, c ≠ 0 ∧ RimCert (univ.image (K n)) (c • view16 (K n) v)) ∧
      ∀ w a b, TieInst16 x w a b → ⟪K n a - K n b, view16 (K n) w⟫ = 0) :
    IsRupert (univ.image x) := by
  have h : ∃ᶠ n in atTop, ∃ q : Bool ×
      ((ZMod 3 → Fin 7) ⊕ (ZMod 4 → Fin 7) ⊕ (ZMod 5 → Fin 7)),
      CertL16 (K n) v q.1 q.2 ∧
        ∀ w a b, TieInst16 x w a b → ⟪K n a - K n b, view16 (K n) w⟫ = 0 :=
    hc.mono fun n hn => by
      obtain ⟨⟨c, hc0, k, hk, z, hz⟩, ht⟩ := hn
      have hpos : 0 < |c|⁻¹ := inv_pos.mpr (abs_pos.mpr hc0)
      have hz' := hz.smul hpos
      rw [smul_smul] at hz'
      have hsg : |c|⁻¹ * c = sgnB (decide (0 < c)) := by
        rcases lt_or_gt_of_ne hc0 with h | h
        · rw [abs_of_neg h, sgnB, decide_eq_false (not_lt.mpr h.le)]
          field_simp; simp
        · rw [abs_of_pos h, sgnB, decide_eq_true h, inv_mul_cancel₀ h.ne']; simp
      rw [hsg] at hz'
      obtain ⟨lab, -, hat⟩ := hz'.toAt
      rcases hk with rfl | rfl | rfl
      · exact ⟨⟨decide (0 < c), Sum.inl lab⟩, hat, ht⟩
      · exact ⟨⟨decide (0 < c), Sum.inr (Sum.inl lab)⟩, hat, ht⟩
      · exact ⟨⟨decide (0 < c), Sum.inr (Sum.inr lab)⟩, hat, ht⟩
  obtain ⟨⟨ε, L⟩, hq⟩ := frequently_exists_of_finite h
  rcases L with lab | lab | lab
  · exact isRupert_of_certL_seq_at T K hK v ε lab hnd hq
  · exact isRupert_of_certL_seq_at T K hK v ε lab hnd hq
  · exact isRupert_of_certL_seq_at T K hK v ε lab hnd hq

/-! ### The conditions at the views `02` and `16` -/

theorem EdgeGen.swapF {V : Finset ℝ³} {u v w : ℝ³} {SA SB : Finset ℝ³} {NA NB : ℝ³}
    (h : EdgeGen V u v w SA SB NA NB) : EdgeGen V u v w SB SA NB NA :=
  ⟨h.par, h.g1.swapF, h.dist, h.one, h.footB, h.footA⟩

theorem EdgeGen.rev {V : Finset ℝ³} {u v w : ℝ³} {SA SB : Finset ℝ³} {NA NB : ℝ³}
    (h : EdgeGen V u v w SA SB NA NB) : EdgeGen V (-u) w v SA SB NA NB where
  par := EdgeConf.ParOnly.neg' (EdgeConf.ParOnly.symm h.par)
  g1 := (EdgeConf.G1At.neg h.g1).swapF
  dist := fun y hy y' hy' hne e => h.dist y hy y' hy' hne (by
    simp only [inner_neg_right, neg_inj] at e; exact e)
  one := h.one.neg_u
  footA := h.footA
  footB := h.footB

/-- A facet's functional in the form of `isRupert_ePair_limit`. -/
theorem Face16.hf {x : Fin 7 → ℝ³} {S : Finset (Fin 7)} (F : Face16 x S) {i₀ : Fin 7}
    (h₀ : i₀ ∈ S) :
    ∀ i, (i ∈ S → ⟪F.N, x i⟫ = ⟪F.N, x i₀⟫) ∧ (i ∉ S → ⟪F.N, x i⟫ < ⟪F.N, x i₀⟫) := by
  intro i
  have k := F.hN (x i) (x i₀)
  rw [F.zero i₀ h₀, sub_zero, inner_sub_right] at k
  constructor
  · intro hi; rw [F.zero i hi] at k; linarith
  · intro hi; have := F.neg i hi; linarith

/-- An adjacent facet through `p`, `q`, below at `r` and `s`. -/
theorem Face16.adj {x : Fin 7 → ℝ³} {S : Finset (Fin 7)} (F : Face16 x S) {p q r s : Fin 7}
    (hp : p ∈ S) (hq : q ∈ S) (hr : r ∉ S) (hs : s ∉ S) :
    ⟪F.N, x q - x p⟫ = 0 ∧ ⟪F.N, x r - x p⟫ < 0 ∧ ⟪F.N, x s - x p⟫ < 0 := by
  have h := F.hf hp
  refine ⟨?_, ?_, ?_⟩
  · rw [inner_sub_right, (h q).1 hq, sub_self]
  · rw [inner_sub_right]; linarith [(h r).2 hr]
  · rw [inner_sub_right]; linarith [(h s).2 hs]

/-- **The codimension-2 conditions at the view along `02`** (with a horizontal double normal
there): `EdgeGen` for the faces `0235`, `024`, and `0`, `2` off the plane `346` of Lemma E. -/
def Gen02 {x : Fin 7 → ℝ³} (T : Type16 x) : Prop :=
  EdgeGen (univ.image x) (x 2 - x 0) (x 0) (x 2) (({0, 2, 3, 5} : Finset (Fin 7)).image x)
    (({0, 2, 4} : Finset (Fin 7)).image x) T.q0235.N T.t024.N ∧
  det3 (x 4 - x 3) (x 6 - x 3) (x 0 - x 3) ≠ 0 ∧ det3 (x 4 - x 3) (x 6 - x 3) (x 2 - x 3) ≠ 0

/-- **The codimension-2 conditions at the view along `16`**: `EdgeGen` for the faces `1356`,
`146`, and `6`, `1` off the plane `340` of Lemma E. -/
def Gen16 {x : Fin 7 → ℝ³} (T : Type16 x) : Prop :=
  EdgeGen (univ.image x) (x 1 - x 6) (x 6) (x 1) (({1, 3, 5, 6} : Finset (Fin 7)).image x)
    (({1, 4, 6} : Finset (Fin 7)).image x) T.q1356.N T.t146.N ∧
  det3 (x 4 - x 3) (x 0 - x 3) (x 6 - x 3) ≠ 0 ∧ det3 (x 4 - x 3) (x 0 - x 3) (x 1 - x 3) ≠ 0

theorem det3_lemmaE_ab (a b c X : ℝ³) :
    det3 (a - b) (c - b) (X - b) = -det3 (b - a) (c - a) (X - a) := by
  simp only [det3_expand, PiLp.sub_apply]; ring

theorem sgnB_true : sgnB true = 1 := rfl
theorem sgnB_false : sgnB false = -1 := rfl

/-! ### The four certificates at `02` and `16` -/

set_option maxRecDepth 4000 in
theorem isRupert_ePair02 {x : Fin 7 → ℝ³} (T : Type16 x) (K : ℕ → Fin 7 → ℝ³)
    (hK : ∀ m, Tendsto (fun n => K n m) atTop (𝓝 (x m))) (s : Bool)
    (hfreq : ∃ᶠ n in atTop,
      EPairData (univ.image (K n)) (sgnB s) (K n 0) (K n 2) (K n 3) (K n 4) (K n 6))
    (hg : Gen02 T) : IsRupert (univ.image x) := by
  cases s
  · rw [sgnB_false] at hfreq
    refine isRupert_ePair_limit x T.inj T.noSeg (v := 0) (w := 2) (a := 4) (b := 3) (c := 6)
      (by decide) (T.t024.hf (i₀ := 0) (by decide)) (T.q0235.hf (i₀ := 0) (by decide))
      (by decide) (by decide) K hK (hfreq.mono fun n hn => hn.flip) hg.1.swapF ⟨?_, ?_⟩
    · rw [det3_lemmaE_ab, neg_ne_zero]; exact hg.2.1
    · rw [det3_lemmaE_ab, neg_ne_zero]; exact hg.2.2
  · rw [sgnB_true] at hfreq
    exact isRupert_ePair_limit x T.inj T.noSeg (v := 0) (w := 2) (a := 3) (b := 4) (c := 6)
      (by decide) (T.q0235.hf (i₀ := 0) (by decide)) (T.t024.hf (i₀ := 0) (by decide))
      (by decide) (by decide) K hK hfreq hg.1 hg.2

set_option maxRecDepth 4000 in
theorem isRupert_ePair61 {x : Fin 7 → ℝ³} (T : Type16 x) (K : ℕ → Fin 7 → ℝ³)
    (hK : ∀ m, Tendsto (fun n => K n m) atTop (𝓝 (x m))) (s : Bool)
    (hfreq : ∃ᶠ n in atTop,
      EPairData (univ.image (K n)) (sgnB s) (K n 6) (K n 1) (K n 3) (K n 4) (K n 0))
    (hg : Gen16 T) : IsRupert (univ.image x) := by
  cases s
  · rw [sgnB_false] at hfreq
    refine isRupert_ePair_limit x T.inj T.noSeg (v := 6) (w := 1) (a := 4) (b := 3) (c := 0)
      (by decide) (T.t146.hf (i₀ := 6) (by decide)) (T.q1356.hf (i₀ := 6) (by decide))
      (by decide) (by decide) K hK (hfreq.mono fun n hn => hn.flip) hg.1.swapF ⟨?_, ?_⟩
    · rw [det3_lemmaE_ab, neg_ne_zero]; exact hg.2.1
    · rw [det3_lemmaE_ab, neg_ne_zero]; exact hg.2.2
  · rw [sgnB_true] at hfreq
    exact isRupert_ePair_limit x T.inj T.noSeg (v := 6) (w := 1) (a := 3) (b := 4) (c := 0)
      (by decide) (T.q1356.hf (i₀ := 6) (by decide)) (T.t146.hf (i₀ := 6) (by decide))
      (by decide) (by decide) K hK hfreq hg.1 hg.2

set_option maxRecDepth 4000 in
theorem isRupert_eTri20 {x : Fin 7 → ℝ³} (T : Type16 x) (K : ℕ → Fin 7 → ℝ³)
    (hK : ∀ m, Tendsto (fun n => K n m) atTop (𝓝 (x m))) (s : Bool)
    (hfreq : ∃ᶠ n in atTop,
      ETriData (univ.image (K n)) (sgnB s) (K n 2) (K n 0) (K n 5) (K n 4))
    (hg : Gen02 T) : IsRupert (univ.image x) := by
  have G := hg.1.rev
  rw [neg_sub] at G
  have adj := T.t245.adj (p := 2) (q := 5) (r := 0) (s := 3) (by decide) (by decide) (by decide)
    (by decide)
  have adj' := T.t245.adj (p := 5) (q := 2) (r := 0) (s := 3) (by decide) (by decide) (by decide)
    (by decide)
  cases s
  · rw [sgnB_false] at hfreq
    refine isRupert_eTri_limit x T.inj (v := 2) (w := 0) (a := 4) (b := 5) (by decide)
      (T.t024.hf (i₀ := 0) (by decide)) (T.q0235.hf (i₀ := 0) (by decide)) (by decide)
      (by decide) ?_ ?_ K hK (hfreq.mono fun n hn => hn.flip) G.par G.g1.swapF G.dist
    · intro i hi h1 h2 h3; exfalso; revert hi h1 h2 h3; revert i; decide
    · intro i hi h1 h2 h3
      obtain rfl : i = 3 := by revert hi h1 h2 h3; revert i; decide
      exact ⟨T.t245.N, adj'.1, adj'.2.1, adj'.2.2⟩
  · rw [sgnB_true] at hfreq
    refine isRupert_eTri_limit x T.inj (v := 2) (w := 0) (a := 5) (b := 4) (by decide)
      (T.q0235.hf (i₀ := 0) (by decide)) (T.t024.hf (i₀ := 0) (by decide)) (by decide)
      (by decide) ?_ ?_ K hK hfreq G.par G.g1 G.dist
    · intro i hi h1 h2 h3
      obtain rfl : i = 3 := by revert hi h1 h2 h3; revert i; decide
      exact ⟨T.t245.N, adj.1, adj.2.1, adj.2.2⟩
    · intro i hi h1 h2 h3; exfalso; revert hi h1 h2 h3; revert i; decide

set_option maxRecDepth 4000 in
theorem isRupert_eTri16 {x : Fin 7 → ℝ³} (T : Type16 x) (K : ℕ → Fin 7 → ℝ³)
    (hK : ∀ m, Tendsto (fun n => K n m) atTop (𝓝 (x m))) (s : Bool)
    (hfreq : ∃ᶠ n in atTop,
      ETriData (univ.image (K n)) (sgnB s) (K n 1) (K n 6) (K n 5) (K n 4))
    (hg : Gen16 T) : IsRupert (univ.image x) := by
  have G := hg.1.rev
  rw [neg_sub] at G
  have adj := T.t145.adj (p := 1) (q := 5) (r := 6) (s := 3) (by decide) (by decide) (by decide)
    (by decide)
  have adj' := T.t145.adj (p := 5) (q := 1) (r := 6) (s := 3) (by decide) (by decide) (by decide)
    (by decide)
  cases s
  · rw [sgnB_false] at hfreq
    refine isRupert_eTri_limit x T.inj (v := 1) (w := 6) (a := 4) (b := 5) (by decide)
      (T.t146.hf (i₀ := 6) (by decide)) (T.q1356.hf (i₀ := 6) (by decide)) (by decide)
      (by decide) ?_ ?_ K hK (hfreq.mono fun n hn => hn.flip) G.par G.g1.swapF G.dist
    · intro i hi h1 h2 h3; exfalso; revert hi h1 h2 h3; revert i; decide
    · intro i hi h1 h2 h3
      obtain rfl : i = 3 := by revert hi h1 h2 h3; revert i; decide
      exact ⟨T.t145.N, adj'.1, adj'.2.1, adj'.2.2⟩
  · rw [sgnB_true] at hfreq
    refine isRupert_eTri_limit x T.inj (v := 1) (w := 6) (a := 5) (b := 4) (by decide)
      (T.q1356.hf (i₀ := 6) (by decide)) (T.t146.hf (i₀ := 6) (by decide)) (by decide)
      (by decide) ?_ ?_ K hK hfreq G.par G.g1 G.dist
    · intro i hi h1 h2 h3
      obtain rfl : i = 3 := by revert hi h1 h2 h3; revert i; decide
      exact ⟨T.t145.N, adj.1, adj.2.1, adj.2.2⟩
    · intro i hi h1 h2 h3; exfalso; revert hi h1 h2 h3; revert i; decide

end Minimality

end
