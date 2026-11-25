module

public import Minimality.Type24MerC1

@[expose] public section

set_option autoImplicit false

open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21 Minimality.FaceChord Minimality.T24.SAT Minimality.T24.Sym
open Minimality.RimFromSigns Minimality.T24.Q45

namespace Minimality.T24.Mer

/-! ### Small facts about `mer` -/

theorem mer_inner_facet {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (S T : Fin 9) :
    ⟪F.N T, mer F S T⟫ = 0 := by
  simp only [mer, PiLp.inner_apply, Fin.sum_univ_three]
  simp
  ring

private theorem mer_eq_cross_cross' {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (S T : Fin 9) :
    mer F S T = cross (cross (F.N T) (F.N S)) (F.N T) := by
  ext j
  fin_cases j <;> (simp only [mer, cross, PiLp.inner_apply, Fin.sum_univ_three]; simp; ring)

/-- Cauchy-Schwarz sign of the source facet at the meridian view. -/
theorem mer_source_pos {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (S T : Fin 9) (h : mer F S T ≠ 0) :
    0 < ⟪F.N S, mer F S T⟫ := by
  have hlag : ⟪F.N S, mer F S T⟫ = ⟪cross (F.N T) (F.N S), cross (F.N T) (F.N S)⟫ := by
    simp only [mer, cross, PiLp.inner_apply, Fin.sum_univ_three]
    simp
    ring
  rw [hlag, real_inner_self_eq_norm_sq]
  refine sq_pos_of_pos (norm_pos_iff.mpr fun hcr => h ?_)
  rw [mer_eq_cross_cross', hcr]
  ext j; fin_cases j <;> simp [cross]

/-! ### Generic rim engine -/

/-- Decidable combinatorial certificate of a rim `r` on the face circle of facet `T` with chord
`r a → r (a + 1)` (an edge of `T` and of facet `tn a`): every other edge `i` is the ridge of facets
`tn i` (negative at the view) and `tp i` (positive); `sp i` contains `r i` but not `r (i + 1)`
(for `cross u (x (r (i + 1)) - x (r i)) ≠ 0`); every vertex other than the edge's endpoints that is
off `T` or on the rim is off edge `i` (off one of its two facets; off `T` for the chord). -/
abbrev RimCert {k : ℕ} [NeZero k] (T : Fin 9) (r : ZMod k → Fin 7) (a : ZMod k)
    (tn tp sp : ZMod k → Fin 9) : Prop :=
  Function.Injective r ∧
  (∀ i, i ≠ a → r i ∈ s0x_S24 (tn i) ∧ r (i + 1) ∈ s0x_S24 (tn i) ∧
      r i ∈ s0x_S24 (tp i) ∧ r (i + 1) ∈ s0x_S24 (tp i)) ∧
  (r a ∈ s0x_S24 T ∧ r (a + 1) ∈ s0x_S24 T ∧ r a ∈ s0x_S24 (tn a) ∧ r (a + 1) ∈ s0x_S24 (tn a)) ∧
  (∀ i, r i ∈ s0x_S24 (sp i) ∧ r (i + 1) ∉ s0x_S24 (sp i)) ∧
  (∀ i (y : Fin 7), y ≠ r i → y ≠ r (i + 1) → (y ∉ s0x_S24 T ∨ ∃ j, y = r j) →
    if i = a then y ∉ s0x_S24 T else (y ∉ s0x_S24 (tn i) ∨ y ∉ s0x_S24 (tp i)))

set_option synthInstance.maxSize 1024 in
instance {k : ℕ} [NeZero k] (T : Fin 9) (r : ZMod k → Fin 7) (a : ZMod k) (tn tp sp : ZMod k → Fin 9) :
    Decidable (RimCert T r a tn tp sp) := by
  unfold RimCert; infer_instance

/-- **Rim engine.**  At any view `u` on the face circle of `T`, the rim-edge facet signs, the chord
partner sign, `hmid`, the depth conditions and a Lemma-H far vertex give `FaceChordView F T`. -/
theorem faceChordView_of_rimCert {k : ℕ} [NeZero k] (hk : 3 ≤ k) {x : Fin 7 → ℝ³}
    (F : S0xFac 9 s0x_S24 x) (T : Fin 9) (u : ℝ³) (r : ZMod k → Fin 7) (a : ZMod k)
    (tn tp sp : ZMod k → Fin 9) (hcert : RimCert T r a tn tp sp)
    (hnu : ⟪F.N T, u⟫ = 0)
    (hsg : ∀ i, i ≠ a → ⟪F.N (tn i), u⟫ < 0 ∧ 0 < ⟪F.N (tp i), u⟫)
    (hca : ⟪F.N (tn a), u⟫ ≠ 0)
    (hmid : ∀ q ∈ s0x_S24 T, (∀ j, q ≠ r j) → ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
      x q = x (r a) + s • (x (r (a + 1)) - x (r a)) + δ • u)
    (hinj : Function.Injective fun i => ⟪x (r i), u⟫)
    (hz : UniOrSep (fun i => x (r i)) u)
    (hfar : ∃ w, r w ∉ s0x_S24 T ∧
      (∀ m, m ≠ w → r m ∉ s0x_S24 T → F.f T (x (r w)) < F.f T (x (r m))) ∧
      (⟪F.N T, cross (x (r (a + 1)) - x (r a)) (x (r w) - x (r a))⟫ ≠ 0 ∨
        ⟪x (r w) - x (r a), x (r (a + 1)) - x (r a)⟫ < 0 ∨
        ⟪x (r w) - x (r (a + 1)), x (r a) - x (r (a + 1))⟫ < 0)) :
    FaceChordView F T := by
  rcases hcert with ⟨hr_inj, h_ridge, h_chord, h_sp, h_off⟩
  have h_edge : ∀ i : ZMod k, ∃ σ : ℝ, σ ≠ 0 ∧
      ∀ y : Fin 7, y ≠ r i → y ≠ r (i + 1) → (y ∉ s0x_S24 T ∨ ∃ j, y = r j) →
        0 < σ * det3 (x (r (i + 1)) - x (r i)) (x y - x (r i)) u := by
    intro i
    by_cases hia : i = a
    · subst hia
      have hcr : cross u (x (r (i + 1)) - x (r i)) ≠ 0 :=
        cross_ne_zero_of_facet_sign F (tn i) (r i) (r (i + 1))
          h_chord.2.2.1 h_chord.2.2.2 hca (sp i) (h_sp i).1 (h_sp i).2
      obtain ⟨σ, hσ_ne, hσ⟩ :=
        det3_sign_edgeOn F T (r i) (r (i + 1)) h_chord.1 h_chord.2.1 u hnu hcr
      refine ⟨σ, hσ_ne, fun y hy1 hy2 hyT => hσ y ?_⟩
      have := h_off i y hy1 hy2 hyT
      simpa using this
    · have hri := h_ridge i hia
      have hcr : cross u (x (r (i + 1)) - x (r i)) ≠ 0 :=
        cross_ne_zero_of_facet_sign F (tn i) (r i) (r (i + 1))
          hri.1 hri.2.1 (hsg i hia).1.ne (sp i) (h_sp i).1 (h_sp i).2
      obtain ⟨σ, hσ_ne, hσ⟩ :=
        det3_sign_ridge F (tn i) (tp i) (r i) (r (i + 1))
          ⟨hri.1, hri.2.2.1⟩ ⟨hri.2.1, hri.2.2.2⟩ u (hsg i hia) hcr
      refine ⟨σ, hσ_ne, fun y hy1 hy2 hyT => hσ y ?_⟩
      have := h_off i y hy1 hy2 hyT
      simpa [hia] using this
  choose σ hσ_ne hσ using h_edge
  have : Fact (1 < k) := ⟨by omega⟩
  have h1_ne : (1 : ZMod k) ≠ 0 := by
    intro h0
    have : (1 : ZMod k).val = (0 : ZMod k).val := congrArg ZMod.val h0
    rw [ZMod.val_one, ZMod.val_zero] at this
    exact one_ne_zero this
  have h2_ne : (2 : ZMod k) ≠ 0 := by
    intro h0
    have hval : ((2 : ℕ) : ZMod k).val = 0 := by simpa using congrArg ZMod.val h0
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)] at hval
    omega
  have hlink : ∀ i : ZMod k, 0 < σ i * σ (i + 1) := by
    intro i
    have hne20 : r (i + 2) ≠ r i := fun heq => h2_ne (by
      have := hr_inj heq
      linear_combination this)
    have hne21 : r (i + 2) ≠ r (i + 1) := fun heq => h1_ne (by
      have := hr_inj heq
      linear_combination this)
    have hne01 : r i ≠ r (i + 1) := fun heq => h1_ne (by
      have := hr_inj heq
      linear_combination -this)
    have hne02 : r i ≠ r (i + 2) := hne20.symm
    have h1 := hσ i (r (i + 2)) hne20 hne21 (Or.inr ⟨i + 2, rfl⟩)
    have h2 := hσ (i + 1) (r i) hne01 (by rw [add_assoc, show (1 : ZMod k) + 1 = 2 by ring]; exact hne02) (Or.inr ⟨i, rfl⟩)
    have hcyc_tri : det3 (x (r (i + 1)) - x (r i)) (x (r (i + 2)) - x (r i)) u =
        det3 (x (r (i + 2)) - x (r (i + 1))) (x (r i) - x (r (i + 1))) u := by
      simpa [add_assoc] using det3_cycle_triangle (x (r i)) (x (r (i + 1))) (x (r (i + 2))) u
    rw [hcyc_tri] at h1
    rw [show i + 1 + 1 = i + 2 by ring] at h2
    exact sign_prod h1 h2
  have hchain : ∀ n : ℕ, 0 < σ 0 * σ (n : ZMod k) := by
    intro n
    induction n with
    | zero => simpa using mul_self_pos.mpr (hσ_ne 0)
    | succ n ih =>
      rw [Nat.cast_succ]
      exact sign_transfer ih (hlink (n : ZMod k))
  have h0_all : ∀ i : ZMod k, 0 < σ 0 * σ i := fun i => by
    have := hchain i.val
    simpa [ZMod.natCast_zmod_val] using this
  obtain ⟨w, hwS, hwfar, hwoff⟩ := hfar
  refine ⟨u, k, inferInstance, r, a, w, σ 0, hnu, hk, h_chord.1, h_chord.2.1, hσ_ne 0,
    ?_, ?_, hmid, hinj, hz, hwS, hwfar, hwoff⟩
  · intro i j hji hji1
    have hne1 : r j ≠ r i := fun heq => hji (hr_inj heq)
    have hne2 : r j ≠ r (i + 1) := fun heq => hji1 (hr_inj heq)
    exact sign_transfer (h0_all i) (hσ i (r j) hne1 hne2 (Or.inr ⟨j, rfl⟩))
  · intro q hqS hqr i
    exact sign_transfer (h0_all i) (hσ i q (hqr i) (hqr (i + 1)) (Or.inl hqS))

/-! ### Chord middles -/

/-- **Chord-Middle-Adjacent-Facets (Carbon A55).**  If `x P` lies strictly over the chord `Q R`
along `u` and facet `T'` contains `Q, R` but not `P`, every facet `A ∋ P` missing `Q` or `R` has the
opposite sign of `T'` at `u`. -/
theorem chord_middle_facet_sign {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) {u : ℝ³}
    {Q R P : Fin 7} {s δ : ℝ} (A T' : Fin 9) (hQ : Q ∈ s0x_S24 T') (hR : R ∈ s0x_S24 T')
    (hP : P ∉ s0x_S24 T') (hPA : P ∈ s0x_S24 A) (hoff : Q ∉ s0x_S24 A ∨ R ∉ s0x_S24 A)
    (hs : 0 < s) (hs1 : s < 1) (hx : x P = x Q + s • (x R - x Q) + δ • u) :
    ⟪F.N A, u⟫ * ⟪F.N T', u⟫ < 0 := by
  have hT'_u : δ * ⟪F.N T', u⟫ < 0 := by
    have h1 := (F.hN T' (x P) (x Q)).symm
    rw [F.zero T' Q hQ, sub_zero] at h1
    have h2 := (F.hN T' (x R) (x Q)).symm
    rw [F.zero T' R hR, F.zero T' Q hQ, sub_self] at h2
    have hPQ : x P - x Q = s • (x R - x Q) + δ • u := by rw [hx]; abel
    rw [hPQ, inner_add_right, real_inner_smul_right, real_inner_smul_right, h2, mul_zero,
      zero_add] at h1
    rw [h1]
    exact F.neg T' P hP
  have hA_u : 0 < δ * ⟪F.N A, u⟫ := by
    have hPQ : x P - x Q = s • (x R - x Q) + δ • u := by rw [hx]; abel
    have hδu : δ • u = (1 - s) • (x P - x Q) + s • (x P - x R) := by
      rw [show x P - x R = (x P - x Q) - (x R - x Q) by abel, hPQ]
      module
    have hAQ : ⟪F.N A, x P - x Q⟫ = - F.f A (x Q) := by
      have := (F.hN A (x P) (x Q)).symm
      rw [F.zero A P hPA, zero_sub] at this
      exact this
    have hAR : ⟪F.N A, x P - x R⟫ = - F.f A (x R) := by
      have := (F.hN A (x P) (x R)).symm
      rw [F.zero A P hPA, zero_sub] at this
      exact this
    have hmul : δ * ⟪F.N A, u⟫ = (1 - s) * (- F.f A (x Q)) + s * (- F.f A (x R)) := by
      rw [← real_inner_smul_right, hδu, inner_add_right, real_inner_smul_right,
        real_inner_smul_right, hAQ, hAR]
    rw [hmul]
    have h1s : 0 < 1 - s := by linarith
    have hAQ_nonneg : 0 ≤ - F.f A (x Q) := by
      by_cases hQA : Q ∈ s0x_S24 A
      · rw [F.zero A Q hQA, neg_zero]
      · exact (neg_pos.mpr (F.neg A Q hQA)).le
    have hAR_nonneg : 0 ≤ - F.f A (x R) := by
      by_cases hRA : R ∈ s0x_S24 A
      · rw [F.zero A R hRA, neg_zero]
      · exact (neg_pos.mpr (F.neg A R hRA)).le
    rcases hoff with hQA | hRA
    · have hpos1 : 0 < (1 - s) * (- F.f A (x Q)) := mul_pos h1s (neg_pos.mpr (F.neg A Q hQA))
      have hnn2 : 0 ≤ s * (- F.f A (x R)) := mul_nonneg hs.le hAR_nonneg
      linarith
    · have hnn1 : 0 ≤ (1 - s) * (- F.f A (x Q)) := mul_nonneg h1s.le hAQ_nonneg
      have hpos2 : 0 < s * (- F.f A (x R)) := mul_pos hs (neg_pos.mpr (F.neg A R hRA))
      linarith
  have hprod : (δ * δ) * (⟪F.N A, u⟫ * ⟪F.N T', u⟫) < 0 := by
    have : (δ * δ) * (⟪F.N A, u⟫ * ⟪F.N T', u⟫) = (δ * ⟪F.N A, u⟫) * (δ * ⟪F.N T', u⟫) := by ring
    rw [this]
    exact mul_neg_of_pos_of_neg hA_u hT'_u
  exact neg_of_mul_neg_right hprod (mul_self_nonneg δ)

/-- **Level chord middle.**  If the chord `Q R` is the ridge of facets `S` and `T` (so `mer F S T`
is orthogonal to it), a vertex `P` of `T` off `S` with acute base angles at `Q` and `R` lies strictly
over the chord along `mer F S T`. -/
theorem level_chord_middle {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (S T : Fin 9) (Q R P : Fin 7)
    (hQS : Q ∈ s0x_S24 S) (hRS : R ∈ s0x_S24 S) (hQT : Q ∈ s0x_S24 T) (hRT : R ∈ s0x_S24 T)
    (hPT : P ∈ s0x_S24 T) (hPS : P ∉ s0x_S24 S)
    (h1 : 0 < ⟪x P - x Q, x R - x Q⟫) (h2 : 0 < ⟪x P - x R, x Q - x R⟫) :
    ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧ x P = x Q + s • (x R - x Q) + δ • mer F S T := by
  set u := mer F S T
  set e := x R - x Q
  set d := x P - x Q
  have he_pos : 0 < ⟪e, e⟫ := by
    have hsplit : ⟪e, e⟫ = ⟪x P - x Q, x R - x Q⟫ + ⟪x P - x R, x Q - x R⟫ := by
      simp only [e, PiLp.inner_apply, Fin.sum_univ_three]
      simp
      ring
    linarith
  have he_ne : e ≠ 0 := by
    intro h0
    simp [h0] at he_pos
  have hNT_ne : F.N T ≠ 0 := by
    have hne_univ : ∃ y : Fin 7, y ∉ s0x_S24 T := by
      fin_cases T <;> first | exact ⟨0, by decide⟩ | exact ⟨3, by decide⟩ | exact ⟨1, by decide⟩
    obtain ⟨y, hy⟩ := hne_univ
    intro h0
    have := (F.hN T (x y) (x Q)).symm
    rw [h0, inner_zero_left, F.zero T Q hQT, sub_zero] at this
    have hy_neg := F.neg T y hy
    linarith
  have hNT_pos : 0 < ⟪F.N T, F.N T⟫ := by
    rw [real_inner_self_eq_norm_sq]
    exact sq_pos_of_pos (norm_pos_iff.mpr hNT_ne)
  have hNS_e : ⟪F.N S, e⟫ = 0 := by
    have := (F.hN S (x R) (x Q)).symm
    rw [F.zero S R hRS, F.zero S Q hQS, sub_self] at this
    exact this
  have hNT_e : ⟪F.N T, e⟫ = 0 := by
    have := (F.hN T (x R) (x Q)).symm
    rw [F.zero T R hRT, F.zero T Q hQT, sub_self] at this
    exact this
  have hNT_d : ⟪F.N T, d⟫ = 0 := by
    have := (F.hN T (x P) (x Q)).symm
    rw [F.zero T P hPT, F.zero T Q hQT, sub_self] at this
    exact this
  have hNS_d : ⟪F.N S, d⟫ < 0 := by
    have := (F.hN S (x P) (x Q)).symm
    rw [F.zero S Q hQS, sub_zero] at this
    dsimp [d]
    rw [this]
    exact F.neg S P hPS
  have hu_ne : u ≠ 0 := by
    intro h0
    have h0' : ⟪F.N T, F.N T⟫ • F.N S = ⟪F.N T, F.N S⟫ • F.N T := sub_eq_zero.mp h0
    have h_inner := congrArg (fun v => ⟪v, d⟫) h0'
    rw [real_inner_smul_left, real_inner_smul_left, hNT_d, mul_zero] at h_inner
    have : ⟪F.N T, F.N T⟫ * ⟪F.N S, d⟫ < 0 := mul_neg_of_pos_of_neg hNT_pos hNS_d
    linarith
  set s := ⟪d, e⟫ / ⟪e, e⟫
  have hs_pos : 0 < s := div_pos h1 he_pos
  have hs_lt : s < 1 := by
    rw [div_lt_one he_pos]
    have h_sub : ⟪e, e⟫ - ⟪d, e⟫ = ⟪x P - x R, x Q - x R⟫ := by
      simp only [e, d, PiLp.inner_apply, Fin.sum_univ_three]
      simp
      ring
    linarith
  set D := d - s • e
  have hD_e : ⟪D, e⟫ = 0 := by
    dsimp [D, s]
    rw [inner_sub_left, real_inner_smul_left]
    field_simp
    ring
  have hD_NT : ⟪D, F.N T⟫ = 0 := by
    dsimp [D]
    rw [inner_sub_left, real_inner_smul_left]
    rw [real_inner_comm] at hNT_d hNT_e
    rw [hNT_d, hNT_e, mul_zero, sub_zero]
  have hu_e : ⟪u, e⟫ = 0 := by
    dsimp [u, mer]
    rw [inner_sub_left, real_inner_smul_left, real_inner_smul_left, hNS_e, hNT_e, mul_zero,
      mul_zero, sub_zero]
  have hu_NT : ⟪u, F.N T⟫ = 0 := by
    rw [real_inner_comm]
    exact mer_inner_facet F S T
  have he_NT_cross : cross e (F.N T) ≠ 0 := by
    intro h0
    have hlag : ⟪cross e (F.N T), cross e (F.N T)⟫ =
        ⟪e, e⟫ * ⟪F.N T, F.N T⟫ - ⟪e, F.N T⟫ ^ 2 := by
      simp only [cross, PiLp.inner_apply, Fin.sum_univ_three]
      simp
      ring
    rw [h0, inner_zero_left] at hlag
    rw [show ⟪e, F.N T⟫ = ⟪F.N T, e⟫ from real_inner_comm _ _, hNT_e, sq, mul_zero, sub_zero] at hlag
    have : 0 < ⟪e, e⟫ * ⟪F.N T, F.N T⟫ := mul_pos he_pos hNT_pos
    linarith
  have huD_cross : cross u D = 0 :=
    cross_eq_zero_of_perp2 hu_e hu_NT hD_e hD_NT he_NT_cross
  set δ := ⟪D, u⟫ / ⟪u, u⟫
  have hδ : D = δ • u := eq_smul_of_cross_eq_zero hu_ne huD_cross
  have hδ_ne : δ ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hδ
    have hds : d = s • e := sub_eq_zero.mp hδ
    have : ⟪F.N S, d⟫ = 0 := by rw [hds, real_inner_smul_right, hNS_e, mul_zero]
    linarith
  refine ⟨s, δ, hs_pos, hs_lt, hδ_ne, ?_⟩
  have : x P = x Q + d := by dsimp [d]; abel
  rw [this, show d = s • e + D by dsimp [D]; abel, hδ]
  dsimp [e, u]
  abel

/-! ### 4-rim level-chord engine -/

private theorem strictUnimodal_of_zmod4 {z : ZMod 4 → ℝ} (hinj : Function.Injective z)
    (hp : ∃ p : ZMod 4, z (p - 1) < z p ∧ z (p + 1) < z p ∧
      (z (p + 2) < z (p + 1) ∨ z (p + 2) < z (p + 3))) :
    StrictUnimodal z := by
  refine ⟨fun i => fun heq => ?_, ?_⟩
  · have := hinj heq
    have h1 : (1 : ZMod 4) ≠ 0 := by decide
    exact h1 (by linear_combination -this)
  · obtain ⟨p, hp1, hp2, hp3⟩ := hp
    have hfilt : (univ.filter fun i : ZMod 4 => z (i - 1) < z i ∧ z (i + 1) < z i) = {p} := by
      ext i
      simp only [mem_filter, mem_univ, true_and, mem_singleton]
      constructor
      · rintro ⟨hi1, hi2⟩
        have hdiff : i - p = 0 ∨ i - p = 1 ∨ i - p = 2 ∨ i - p = 3 := by
          generalize i - p = d
          fin_cases d
          · exact Or.inl rfl
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr (Or.inl rfl))
          · exact Or.inr (Or.inr (Or.inr rfl))
        rcases hdiff with hd | hd | hd | hd
        · exact sub_eq_zero.mp hd
        · exfalso
          have hip : i = p + 1 := eq_add_of_sub_eq' hd
          rw [hip, add_sub_cancel_right] at hi1
          linarith
        · exfalso
          have hip : i = p + 2 := eq_add_of_sub_eq' hd
          rw [hip] at hi1 hi2
          rw [add_sub_assoc, show (2 - 1 : ZMod 4) = 1 by decide] at hi1
          rw [add_assoc, show (2 + 1 : ZMod 4) = 3 by decide] at hi2
          rcases hp3 with hlt | hlt <;> linarith
        · exfalso
          have hip : i = p + 3 := eq_add_of_sub_eq' hd
          rw [hip, add_assoc, show (3 + 1 : ZMod 4) = 0 by decide, add_zero] at hi2
          rw [sub_eq_add_neg, show (-1 : ZMod 4) = 3 by decide] at hp1
          linarith
      · rintro rfl
        exact ⟨hp1, hp2⟩
    rw [hfilt, card_singleton]

/-- **Level-chord 4-rim engine (Carbon A53 Adjacent-Tie-4Rim-Unimodality, A54 C2-C4).** -/
theorem faceChordView_mer4 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (S T : Fin 9)
    (r : ZMod 4 → Fin 7) (a : ZMod 4) (tn tp sp : ZMod 4 → Fin 9)
    (hcert : RimCert T r a tn tp sp) (hS : tn a = S)
    (hmS : ∀ q ∈ s0x_S24 T, (∀ j, q ≠ r j) → q ∉ s0x_S24 S)
    (hsg : ∀ i, i ≠ a → ⟪F.N (tn i), mer F S T⟫ < 0 ∧ 0 < ⟪F.N (tp i), mer F S T⟫)
    (hmid : ∀ q ∈ s0x_S24 T, (∀ j, q ≠ r j) →
      0 < ⟪x q - x (r a), x (r (a + 1)) - x (r a)⟫ ∧
        0 < ⟪x q - x (r (a + 1)), x (r a) - x (r (a + 1))⟫)
    (hguard : ⟪x (r (a + 3)) - x (r (a + 2)), mer F S T⟫ ≠ 0 ∨
      ⟪x (r (a + 3)) - x (r (a + 2)), x (r (a + 1)) - x (r a)⟫ ≠ 0)
    (hlev : (⟪x (r (a + 3)) - x (r a), mer F S T⟫ ≠ 0 ∨ ⟪x (r (a + 2)) - x (r a), mer F S T⟫ ≠ 0) ∧
      (⟪x (r (a + 3)) - x (r a), mer F S T⟫ ≠ 0 ∨
        ⟪x (r (a + 3)) - x (r a), x (r (a + 1)) - x (r a)⟫ ≠ 0 ∧
          ⟪x (r (a + 3)) - x (r (a + 1)), x (r (a + 1)) - x (r a)⟫ ≠ 0) ∧
      (⟪x (r (a + 2)) - x (r a), mer F S T⟫ ≠ 0 ∨
        ⟪x (r (a + 2)) - x (r a), x (r (a + 1)) - x (r a)⟫ ≠ 0 ∧
          ⟪x (r (a + 2)) - x (r (a + 1)), x (r (a + 1)) - x (r a)⟫ ≠ 0))
    (hfar : ∃ w, r w ∉ s0x_S24 T ∧
      (∀ m, m ≠ w → r m ∉ s0x_S24 T → F.f T (x (r w)) < F.f T (x (r m))) ∧
      (⟪F.N T, cross (x (r (a + 1)) - x (r a)) (x (r w) - x (r a))⟫ ≠ 0 ∨
        ⟪x (r w) - x (r a), x (r (a + 1)) - x (r a)⟫ < 0 ∨
        ⟪x (r w) - x (r (a + 1)), x (r a) - x (r (a + 1))⟫ < 0)) :
    FaceChordView F T := by
  set u0 := mer F S T
  set e := x (r (a + 1)) - x (r a)
  have hu0_ne : u0 ≠ 0 := by
    have hne : a + 1 ≠ a := by
      intro h0
      have : (1 : ZMod 4) = 0 := by linear_combination h0
      exact absurd this (by decide)
    have h := (hsg (a + 1) hne).1
    intro h0
    rw [h0, inner_zero_right] at h
    exact lt_irrefl 0 h
  have hS_pos : 0 < ⟪F.N S, u0⟫ := mer_source_pos F S T hu0_ne
  have hNT_u0 : ⟪F.N T, u0⟫ = 0 := mer_inner_facet F S T
  have he_ne : e ≠ 0 := by
    intro h0
    have hsp := hcert.2.2.2.1 a
    have h1 := F.zero (sp a) (r a) hsp.1
    have h2 := F.neg (sp a) (r (a + 1)) hsp.2
    have heq : x (r (a + 1)) = x (r a) := sub_eq_zero.mp h0
    rw [heq, h1] at h2
    exact lt_irrefl 0 h2
  have hee_pos : 0 < ⟪e, e⟫ := by
    rw [real_inner_self_eq_norm_sq]
    exact sq_pos_of_pos (norm_pos_iff.mpr he_ne)
  have hNT_e : ⟪F.N T, e⟫ = 0 := by
    have hc := hcert.2.2.1
    have := (F.hN T (x (r (a + 1))) (x (r a))).symm
    rw [F.zero T (r (a + 1)) hc.2.1, F.zero T (r a) hc.1, sub_self] at this
    exact this
  have hNS_e : ⟪F.N S, e⟫ = 0 := by
    have hc := hcert.2.2.1
    rw [← hS]
    have := (F.hN (tn a) (x (r (a + 1))) (x (r a))).symm
    rw [F.zero (tn a) (r (a + 1)) hc.2.2.2, F.zero (tn a) (r a) hc.2.2.1, sub_self] at this
    exact this
  have hu0_e : ⟪e, u0⟫ = 0 := by
    dsimp [u0, mer]
    rw [inner_sub_right, real_inner_smul_right, real_inner_smul_right]
    rw [show ⟪e, F.N S⟫ = ⟪F.N S, e⟫ from real_inner_comm _ _, hNS_e,
      show ⟪e, F.N T⟫ = ⟪F.N T, e⟫ from real_inner_comm _ _, hNT_e, mul_zero, mul_zero, sub_zero]
  -- Choose direction sign σ ∈ {1, -1}
  set αA := ⟪x (r (a + 3)) - x (r a), u0⟫
  set αB := ⟪x (r (a + 2)) - x (r a), u0⟫
  set σ : ℝ := if αA < 0 then 1 else if 0 < αA then -1 else if 0 < αB then 1 else -1
  have hσ_ne : σ ≠ 0 := by
    dsimp [σ]
    split_ifs <;> norm_num
  -- Collect smallness bounds for `t > 0`
  have h_fac_bound : ∃ t1 : ℝ, 0 < t1 ∧ ∀ t : ℝ, 0 < t → t < t1 →
      ∀ i : ZMod 4, i ≠ a →
        ⟪F.N (tn i), u0 + t • (σ • e)⟫ < 0 ∧ 0 < ⟪F.N (tp i), u0 + t • (σ • e)⟫ := by
    have h_each : ∀ i : ZMod 4, ∃ ti : ℝ, 0 < ti ∧ ∀ t : ℝ, 0 < t → t < ti →
        i ≠ a → ⟪F.N (tn i), u0 + t • (σ • e)⟫ < 0 ∧ 0 < ⟪F.N (tp i), u0 + t • (σ • e)⟫ := by
      intro i
      by_cases hia : i = a
      · exact ⟨1, one_pos, fun _ _ _ hi => absurd hia hi⟩
      · obtain ⟨hn, hp⟩ := hsg i hia
        set c1 := |σ * ⟪F.N (tn i), e⟫| + 1
        set c2 := |σ * ⟪F.N (tp i), e⟫| + 1
        refine ⟨min (-⟪F.N (tn i), u0⟫ / c1) (⟪F.N (tp i), u0⟫ / c2),
          lt_min (div_pos (neg_pos.mpr hn) (by positivity)) (div_pos hp (by positivity)),
          fun t ht ht_lt _ => ?_⟩
        have ht1 : t < -⟪F.N (tn i), u0⟫ / c1 := lt_of_lt_of_le ht_lt (min_le_left _ _)
        have ht2 : t < ⟪F.N (tp i), u0⟫ / c2 := lt_of_lt_of_le ht_lt (min_le_right _ _)
        constructor
        · rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
          have hbound : t * (σ * ⟪F.N (tn i), e⟫) ≤ t * c1 := by
            apply mul_le_mul_of_nonneg_left _ ht.le
            exact le_trans (le_abs_self _) (by linarith)
          have : t * c1 < -⟪F.N (tn i), u0⟫ := (lt_div_iff₀ (by positivity)).mp ht1
          linarith
        · rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
          have hbound : -(t * c2) ≤ t * (σ * ⟪F.N (tp i), e⟫) := by
            have : -(σ * ⟪F.N (tp i), e⟫) ≤ c2 := by
              exact le_trans (neg_le_abs _) (by linarith)
            nlinarith
          have : t * c2 < ⟪F.N (tp i), u0⟫ := (lt_div_iff₀ (by positivity)).mp ht2
          linarith
    choose ti hti_pos hti using h_each
    refine ⟨min (min (ti 0) (ti 1)) (min (ti 2) (ti 3)),
      lt_min (lt_min (hti_pos 0) (hti_pos 1)) (lt_min (hti_pos 2) (hti_pos 3)),
      fun t ht ht_lt i hi => ?_⟩
    fin_cases i
    · exact hti 0 t ht (lt_of_lt_of_le ht_lt (le_trans (min_le_left _ _) (min_le_left _ _))) hi
    · exact hti 1 t ht (lt_of_lt_of_le ht_lt (le_trans (min_le_left _ _) (min_le_right _ _))) hi
    · exact hti 2 t ht (lt_of_lt_of_le ht_lt (le_trans (min_le_right _ _) (min_le_left _ _))) hi
    · exact hti 3 t ht (lt_of_lt_of_le ht_lt (le_trans (min_le_right _ _) (min_le_right _ _))) hi
  have h_mid_bound : ∃ t2 : ℝ, 0 < t2 ∧ ∀ t : ℝ, 0 < t → t < t2 →
      ∀ q ∈ s0x_S24 T, (∀ j, q ≠ r j) → ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
        x q = x (r a) + s • e + δ • (u0 + t • (σ • e)) := by
    have h_each : ∀ q : Fin 7, ∃ tq : ℝ, 0 < tq ∧ ∀ t : ℝ, 0 < t → t < tq →
        q ∈ s0x_S24 T → (∀ j, q ≠ r j) → ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
          x q = x (r a) + s • e + δ • (u0 + t • (σ • e)) := by
      intro q
      by_cases hqT : q ∈ s0x_S24 T
      · by_cases hqr : ∀ j, q ≠ r j
        · have hc := hcert.2.2.1
          obtain ⟨s, δ, hs, hs1, hδ, hx⟩ := level_chord_middle F S T (r a) (r (a + 1)) q
            (by rw [← hS]; exact hc.2.2.1) (by rw [← hS]; exact hc.2.2.2)
            hc.1 hc.2.1 hqT (hmS q hqT hqr) (hmid q hqT hqr).1 (hmid q hqT hqr).2
          set c := |δ * σ| + 1
          refine ⟨min s (1 - s) / c, div_pos (lt_min hs (by linarith)) (by positivity),
            fun t ht ht_lt _ _ => ?_⟩
          have htc : t * c < min s (1 - s) := (lt_div_iff₀ (by positivity)).mp ht_lt
          have h_abs : |t * δ * σ| ≤ t * c := by
            rw [mul_assoc, abs_mul, abs_of_pos ht]
            apply mul_le_mul_of_nonneg_left _ ht.le
            dsimp [c]; linarith
          have h_abs' : |t * δ * σ| < min s (1 - s) := lt_of_le_of_lt h_abs htc
          have h_lo : -(1 - s) < t * δ * σ := by
            have := neg_lt_of_abs_lt (lt_of_lt_of_le h_abs' (min_le_right _ _))
            linarith
          have h_hi : t * δ * σ < s := lt_of_le_of_lt (le_abs_self _) (lt_of_lt_of_le h_abs' (min_le_left _ _))
          refine ⟨s - t * δ * σ, δ, by linarith, by linarith, hδ, ?_⟩
          rw [hx]
          ext j; simp [e, u0]; ring
        · exact ⟨1, one_pos, fun _ _ _ _ h => absurd h hqr⟩
      · exact ⟨1, one_pos, fun _ _ _ h _ => absurd h hqT⟩
    choose tq htq_pos htq using h_each
    set t2 := min (min (min (tq 0) (tq 1)) (min (tq 2) (tq 3)))
      (min (min (tq 4) (tq 5)) (tq 6))
    have ht2_pos : 0 < t2 :=
      lt_min (lt_min (lt_min (htq_pos 0) (htq_pos 1)) (lt_min (htq_pos 2) (htq_pos 3)))
        (lt_min (lt_min (htq_pos 4) (htq_pos 5)) (htq_pos 6))
    refine ⟨t2, ht2_pos, fun t ht ht_lt q hqT hqr => ?_⟩
    fin_cases q
    · exact htq 0 t ht (lt_of_lt_of_le ht_lt (le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_left _ _)))) hqT hqr
    · exact htq 1 t ht (lt_of_lt_of_le ht_lt (le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_right _ _)))) hqT hqr
    · exact htq 2 t ht (lt_of_lt_of_le ht_lt (le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))) hqT hqr
    · exact htq 3 t ht (lt_of_lt_of_le ht_lt (le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))) hqT hqr
    · exact htq 4 t ht (lt_of_lt_of_le ht_lt (le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_left _ _)))) hqT hqr
    · exact htq 5 t ht (lt_of_lt_of_le ht_lt (le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_right _ _)))) hqT hqr
    · exact htq 6 t ht (lt_of_lt_of_le ht_lt (le_trans (min_le_right _ _) (min_le_right _ _))) hqT hqr
  -- Bound `t` so all `O(1)` non-zero gaps beat `O(t)` terms for `z_i(t) = ⟪x (r i), u0 + t(σ e)⟫`
  have h_gap_bound : ∃ t3 : ℝ, 0 < t3 ∧ ∀ t : ℝ, 0 < t → t < t3 →
      ∀ (v : ℝ³), (v = x (r (a + 3)) - x (r a) ∨ v = x (r (a + 2)) - x (r a) ∨
        v = x (r (a + 3)) - x (r (a + 2))) →
      ⟪v, u0⟫ ≠ 0 → (0 < ⟪v, u0⟫ → 0 < ⟪v, u0 + t • (σ • e)⟫) ∧
        (⟪v, u0⟫ < 0 → ⟪v, u0 + t • (σ • e)⟫ < 0) := by
    have h_one : ∀ v : ℝ³, ∃ tv : ℝ, 0 < tv ∧ ∀ t : ℝ, 0 < t → t < tv →
        ⟪v, u0⟫ ≠ 0 → (0 < ⟪v, u0⟫ → 0 < ⟪v, u0 + t • (σ • e)⟫) ∧
          (⟪v, u0⟫ < 0 → ⟪v, u0 + t • (σ • e)⟫ < 0) := by
      intro v
      by_cases hv : ⟪v, u0⟫ = 0
      · exact ⟨1, one_pos, fun _ _ _ h => absurd hv h⟩
      · set c := |σ * ⟪v, e⟫| + 1
        refine ⟨|⟪v, u0⟫| / c, div_pos (abs_pos.mpr hv) (by positivity), fun t ht ht_lt _ => ?_⟩
        have htc : t * c < |⟪v, u0⟫| := (lt_div_iff₀ (by positivity)).mp ht_lt
        have h_abs : |t * (σ * ⟪v, e⟫)| < |⟪v, u0⟫| := by
          rw [abs_mul, abs_of_pos ht]
          exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left (by dsimp [c]; linarith) ht.le) htc
        rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
        constructor
        · intro hpos
          rw [abs_of_pos hpos] at h_abs
          linarith [neg_lt_of_abs_lt h_abs]
        · intro hneg
          rw [abs_of_neg hneg] at h_abs
          linarith [lt_of_abs_lt h_abs]
    obtain ⟨tv1, htv1_pos, htv1⟩ := h_one (x (r (a + 3)) - x (r a))
    obtain ⟨tv2, htv2_pos, htv2⟩ := h_one (x (r (a + 2)) - x (r a))
    obtain ⟨tv3, htv3_pos, htv3⟩ := h_one (x (r (a + 3)) - x (r (a + 2)))
    refine ⟨min (min tv1 tv2) tv3, lt_min (lt_min htv1_pos htv2_pos) htv3_pos,
      fun t ht ht_lt v hv hne => ?_⟩
    rcases hv with rfl | rfl | rfl
    · exact htv1 t ht (lt_of_lt_of_le ht_lt (le_trans (min_le_left _ _) (min_le_left _ _))) hne
    · exact htv2 t ht (lt_of_lt_of_le ht_lt (le_trans (min_le_left _ _) (min_le_right _ _))) hne
    · exact htv3 t ht (lt_of_lt_of_le ht_lt (min_le_right _ _)) hne
  -- Bound `t` so `O(1)` term `(r(a+3) or r(a+2))` beats `O(t)` term `(e)` when the other is 0
  have h_dom_bound : ∃ t4 : ℝ, 0 < t4 ∧ ∀ t : ℝ, 0 < t → t < t4 →
      ∀ (v w : ℝ³), (v = x (r (a + 3)) - x (r a) ∨ v = x (r (a + 2)) - x (r a)) →
      (w = x (r (a + 3)) - x (r a) ∨ w = x (r (a + 2)) - x (r a) ∨ w = e) →
      ⟪v, u0⟫ ≠ 0 → ⟪w, u0⟫ = 0 →
      (0 < ⟪v, u0⟫ → ⟪w, u0 + t • (σ • e)⟫ < ⟪v, u0 + t • (σ • e)⟫) ∧
      (⟪v, u0⟫ < 0 → ⟪v, u0 + t • (σ • e)⟫ < ⟪w, u0 + t • (σ • e)⟫) := by
    have h_pair : ∀ v w : ℝ³, ∃ tvw : ℝ, 0 < tvw ∧ ∀ t : ℝ, 0 < t → t < tvw →
        ⟪v, u0⟫ ≠ 0 → ⟪w, u0⟫ = 0 →
        (0 < ⟪v, u0⟫ → ⟪w, u0 + t • (σ • e)⟫ < ⟪v, u0 + t • (σ • e)⟫) ∧
        (⟪v, u0⟫ < 0 → ⟪v, u0 + t • (σ • e)⟫ < ⟪w, u0 + t • (σ • e)⟫) := by
      intro v w
      by_cases hv : ⟪v, u0⟫ = 0
      · exact ⟨1, one_pos, fun _ _ _ h _ => absurd hv h⟩
      · set c := |σ * ⟪v - w, e⟫| + 1
        refine ⟨|⟪v, u0⟫| / c, div_pos (abs_pos.mpr hv) (by positivity), fun t ht ht_lt _ hw0 => ?_⟩
        have htc : t * c < |⟪v, u0⟫| := (lt_div_iff₀ (by positivity)).mp ht_lt
        have h_abs : |t * (σ * ⟪v - w, e⟫)| < |⟪v, u0⟫| := by
          rw [abs_mul, abs_of_pos ht]
          exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left (by dsimp [c]; linarith) ht.le) htc
        have hdiff : ⟪v, u0 + t • (σ • e)⟫ - ⟪w, u0 + t • (σ • e)⟫ =
            ⟪v, u0⟫ + t * (σ * ⟪v - w, e⟫) := by
          rw [inner_add_right, inner_add_right, real_inner_smul_right, real_inner_smul_right,
            real_inner_smul_right, real_inner_smul_right, hw0, inner_sub_left]
          ring
        constructor
        · intro hpos
          rw [abs_of_pos hpos] at h_abs
          have := neg_lt_of_abs_lt h_abs
          linarith
        · intro hneg
          rw [abs_of_neg hneg] at h_abs
          have := lt_of_abs_lt h_abs
          linarith
    set vA := x (r (a + 3)) - x (r a)
    set vB := x (r (a + 2)) - x (r a)
    obtain ⟨tA1, htA1_pos, htA1⟩ := h_pair vA vA
    obtain ⟨tA2, htA2_pos, htA2⟩ := h_pair vA vB
    obtain ⟨tA3, htA3_pos, htA3⟩ := h_pair vA e
    obtain ⟨tB1, htB1_pos, htB1⟩ := h_pair vB vA
    obtain ⟨tB2, htB2_pos, htB2⟩ := h_pair vB vB
    obtain ⟨tB3, htB3_pos, htB3⟩ := h_pair vB e
    set t4 := min (min tA1 (min tA2 tA3)) (min tB1 (min tB2 tB3))
    refine ⟨t4, lt_min (lt_min htA1_pos (lt_min htA2_pos htA3_pos))
        (lt_min htB1_pos (lt_min htB2_pos htB3_pos)), fun t ht ht_lt v w hv hw hvn hw0 => ?_⟩
    rcases hv with rfl | rfl <;> rcases hw with rfl | rfl | rfl
    · exact htA1 t ht (lt_of_lt_of_le ht_lt (le_trans (min_le_left _ _) (min_le_left _ _))) hvn hw0
    · exact htA2 t ht (lt_of_lt_of_le ht_lt (le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))) hvn hw0
    · exact htA3 t ht (lt_of_lt_of_le ht_lt (le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))) hvn hw0
    · exact htB1 t ht (lt_of_lt_of_le ht_lt (le_trans (min_le_right _ _) (min_le_left _ _))) hvn hw0
    · exact htB2 t ht (lt_of_lt_of_le ht_lt (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))) hvn hw0
    · exact htB3 t ht (lt_of_lt_of_le ht_lt (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))) hvn hw0
  obtain ⟨t1, ht1_pos, ht1⟩ := h_fac_bound
  obtain ⟨t2, ht2_pos, ht2⟩ := h_mid_bound
  obtain ⟨t3, ht3_pos, ht3⟩ := h_gap_bound
  obtain ⟨t4, ht4_pos, ht4⟩ := h_dom_bound
  set t := min (min t1 t2) (min t3 t4) / 2
  have ht_pos : 0 < t := by positivity
  have ht_min : t < min (min t1 t2) (min t3 t4) := by
    have hpos : 0 < min (min t1 t2) (min t3 t4) :=
      lt_min (lt_min ht1_pos ht2_pos) (lt_min ht3_pos ht4_pos)
    dsimp [t]; linarith
  have ht_t1 : t < t1 := lt_of_lt_of_le ht_min (le_trans (min_le_left _ _) (min_le_left _ _))
  have ht_t2 : t < t2 := lt_of_lt_of_le ht_min (le_trans (min_le_left _ _) (min_le_right _ _))
  have ht_t3 : t < t3 := lt_of_lt_of_le ht_min (le_trans (min_le_right _ _) (min_le_left _ _))
  have ht_t4 : t < t4 := lt_of_lt_of_le ht_min (le_trans (min_le_right _ _) (min_le_right _ _))
  set u := u0 + t • (σ • e)
  have hnu : ⟪F.N T, u⟫ = 0 := by
    dsimp [u]
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right, hNT_u0, hNT_e, mul_zero,
      mul_zero, add_zero]
  have hca : ⟪F.N (tn a), u⟫ ≠ 0 := by
    dsimp [u]
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right, hS, hNS_e, mul_zero,
      mul_zero, add_zero]
    exact hS_pos.ne'
  -- Depth function z on ZMod 4
  set z : ZMod 4 → ℝ := fun i => ⟪x (r i), u⟫
  have hz_diff : ∀ i j : ZMod 4, z i - z j = ⟪x (r i) - x (r j), u⟫ := fun i j => by
    dsimp [z]; rw [inner_sub_left]
  have hz_QR : z (a + 1) - z a = t * σ * ⟪e, e⟫ := by
    rw [hz_diff]
    dsimp [u, e]
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right, hu0_e]
    ring
  have hz_AB_ne : z (a + 3) ≠ z (a + 2) := by
    intro heq
    have hsub : ⟪x (r (a + 3)) - x (r (a + 2)), u⟫ = 0 := by
      rw [← hz_diff, heq, sub_self]
    by_cases h0 : ⟪x (r (a + 3)) - x (r (a + 2)), u0⟫ = 0
    · rcases hguard with hgu | hge
      · exact hgu h0
      · rw [show u = u0 + t • (σ • e) from rfl, inner_add_right, real_inner_smul_right,
          real_inner_smul_right, h0, zero_add] at hsub
        exact mul_ne_zero ht_pos.ne' (mul_ne_zero hσ_ne hge) hsub
    · have hgap := ht3 t ht_pos ht_t3 (x (r (a + 3)) - x (r (a + 2))) (Or.inr (Or.inr rfl)) h0
      rcases lt_or_gt_of_ne h0 with hneg | hpos
      · exact (hgap.2 hneg).ne hsub
      · exact (hgap.1 hpos).ne' hsub
  -- Helper for injectivity on ZMod 4 from pairwise distinctness of {a, a+1, a+2, a+3}
  have z21 : a + 2 - 1 = a + 1 := by rw [add_sub_assoc]; norm_num
  have z22 : a + 2 + 2 = a := by rw [add_assoc, show (2 + 2 : ZMod 4) = 0 by decide, add_zero]
  have z23 : a + 2 + 3 = a + 1 := by rw [add_assoc, show (2 + 3 : ZMod 4) = 1 by decide]
  have z23' : a + 2 + 1 = a + 3 := by rw [add_assoc]; norm_num
  have z31 : a + 3 - 1 = a + 2 := by rw [add_sub_assoc]; norm_num
  have z30 : a + 3 + 1 = a := by rw [add_assoc, show (3 + 1 : ZMod 4) = 0 by decide, add_zero]
  have z32 : a + 3 + 2 = a + 1 := by rw [add_assoc, show (3 + 2 : ZMod 4) = 1 by decide]
  have z03 : a - 1 = a + 3 := by rw [sub_eq_add_neg, show (-1 : ZMod 4) = 3 by decide]
  have z12 : a + 1 + 1 = a + 2 := by rw [add_assoc]; norm_num
  have z13 : a + 1 + 2 = a + 3 := by rw [add_assoc]; norm_num
  have z10 : a + 1 + 3 = a := by rw [add_assoc, show (1 + 3 : ZMod 4) = 0 by decide, add_zero]
  have decomp4 : ∀ i : ZMod 4, i = a ∨ i = a + 1 ∨ i = a + 2 ∨ i = a + 3 := fun i => by
    have hd : i - a = 0 ∨ i - a = 1 ∨ i - a = 2 ∨ i - a = 3 := by
      generalize i - a = d; fin_cases d
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr rfl))
    rcases hd with h | h | h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (Or.inl (eq_add_of_sub_eq' h))
    · exact Or.inr (Or.inr (Or.inl (eq_add_of_sub_eq' h)))
    · exact Or.inr (Or.inr (Or.inr (eq_add_of_sub_eq' h)))
  have inj_of_pairs : (z a ≠ z (a + 1) ∧ z a ≠ z (a + 2) ∧ z a ≠ z (a + 3) ∧
      z (a + 1) ≠ z (a + 2) ∧ z (a + 1) ≠ z (a + 3) ∧ z (a + 2) ≠ z (a + 3)) →
      Function.Injective z := by
    rintro ⟨h01, h02, h03, h12, h13, h23⟩ i j hij
    rcases decomp4 i with rfl | rfl | rfl | rfl <;> rcases decomp4 j with rfl | rfl | rfl | rfl <;>
      first | rfl | exact absurd hij h01 | exact absurd hij h02 | exact absurd hij h03 |
        exact absurd hij h12 | exact absurd hij h13 | exact absurd hij h23 |
        exact absurd hij.symm h01 | exact absurd hij.symm h02 | exact absurd hij.symm h03 |
        exact absurd hij.symm h12 | exact absurd hij.symm h13 | exact absurd hij.symm h23
  have hz_edge_ne : ∀ b : ZMod 4, (b = a + 3 ∨ b = a + 2) → ⟪x (r b) - x (r a), u0⟫ = 0 →
      (⟪x (r b) - x (r a), e⟫ ≠ 0 ∧ ⟪x (r b) - x (r (a + 1)), e⟫ ≠ 0) →
      z b ≠ z a ∧ z b ≠ z (a + 1) := by
    intro b _ hb0 ⟨hbe1, hbe2⟩
    have hb1 : ⟪x (r b) - x (r (a + 1)), u0⟫ = 0 := by
      rw [show x (r b) - x (r (a + 1)) = (x (r b) - x (r a)) - e by dsimp [e]; abel,
        inner_sub_left, hb0, hu0_e, sub_zero]
    constructor
    · intro heq
      have : ⟪x (r b) - x (r a), u⟫ = 0 := by rw [← hz_diff, heq, sub_self]
      rw [show u = u0 + t • (σ • e) from rfl, inner_add_right, real_inner_smul_right,
        real_inner_smul_right, hb0, zero_add] at this
      exact mul_ne_zero ht_pos.ne' (mul_ne_zero hσ_ne hbe1) this
    · intro heq
      have : ⟪x (r b) - x (r (a + 1)), u⟫ = 0 := by rw [← hz_diff, heq, sub_self]
      rw [show u = u0 + t • (σ • e) from rfl, inner_add_right, real_inner_smul_right,
        real_inner_smul_right, hb1, zero_add] at this
      exact mul_ne_zero ht_pos.ne' (mul_ne_zero hσ_ne hbe2) this
  have hz_both : Function.Injective z ∧ StrictUnimodal z := by
    by_cases hA_neg : αA < 0
    · have hσ1 : σ = 1 := by simp [σ, hA_neg]
      have hz01 : z a < z (a + 1) := by
        have : 0 < z (a + 1) - z a := by rw [hz_QR, hσ1, mul_one]; exact mul_pos ht_pos hee_pos
        linarith
      have hz30 : z (a + 3) < z a := by
        have := (ht3 t ht_pos ht_t3 (x (r (a + 3)) - x (r a)) (Or.inl rfl) hA_neg.ne).2 hA_neg
        rw [← hz_diff] at this; linarith
      rcases lt_trichotomy αB 0 with hB_neg | hB_zero | hB_pos
      · have hz20 : z (a + 2) < z a := by
          have := (ht3 t ht_pos ht_t3 (x (r (a + 2)) - x (r a)) (Or.inr (Or.inl rfl)) hB_neg.ne).2 hB_neg
          rw [← hz_diff] at this; linarith
        have hinj : Function.Injective z := inj_of_pairs
          ⟨hz01.ne, hz20.ne', hz30.ne', (lt_trans hz20 hz01).ne', (lt_trans hz30 hz01).ne', hz_AB_ne.symm⟩
        refine ⟨hinj, strictUnimodal_of_zmod4 hinj ⟨a + 1, ?_, ?_, Or.inr ?_⟩⟩
        · simpa using hz01
        · rw [z12]; exact lt_trans hz20 hz01
        · rw [z13, z10]; exact hz30
      · have h2_ne : z (a + 2) ≠ z a ∧ z (a + 2) ≠ z (a + 1) := by
          apply hz_edge_ne (a + 2) (Or.inr rfl) hB_zero
          rcases hlev.2.2 with h | h
          · exact absurd hB_zero h
          · exact h
        have hz32 : z (a + 3) < z (a + 2) := by
          have := (ht4 t ht_pos ht_t4 (x (r (a + 3)) - x (r a)) (x (r (a + 2)) - x (r a))
            (Or.inl rfl) (Or.inr (Or.inl rfl)) hA_neg.ne hB_zero).2 hA_neg
          rw [← hz_diff, ← hz_diff] at this; linarith
        have hinj : Function.Injective z := inj_of_pairs
          ⟨hz01.ne, h2_ne.1.symm, hz30.ne', h2_ne.2.symm, (lt_trans hz30 hz01).ne', hz32.ne'⟩
        refine ⟨hinj, ?_⟩
        rcases lt_or_gt_of_ne h2_ne.2 with hz21 | hz12
        · refine strictUnimodal_of_zmod4 hinj ⟨a + 1, by simpa using hz01, ?_, Or.inr ?_⟩
          · rw [z12]; exact hz21
          · rw [z13, z10]; exact hz30
        · refine strictUnimodal_of_zmod4 hinj ⟨a + 2, ?_, ?_, Or.inr ?_⟩
          · rw [z21]; exact hz12
          · rw [z23']; exact hz32
          · rw [z22, z23]; exact hz01
      · have hz12 : z (a + 1) < z (a + 2) := by
          have := (ht4 t ht_pos ht_t4 (x (r (a + 2)) - x (r a)) e
            (Or.inr rfl) (Or.inr (Or.inr rfl)) hB_pos.ne' hu0_e).1 hB_pos
          have heu : ⟪e, u⟫ = z (a + 1) - z a := by dsimp [e]; rw [hz_diff]
          rw [heu, ← hz_diff] at this; linarith
        have hinj : Function.Injective z := inj_of_pairs
          ⟨hz01.ne, (lt_trans hz01 hz12).ne, hz30.ne', hz12.ne, (lt_trans hz30 hz01).ne',
            (lt_trans hz30 (lt_trans hz01 hz12)).ne'⟩
        refine ⟨hinj, strictUnimodal_of_zmod4 hinj ⟨a + 2, ?_, ?_, Or.inr ?_⟩⟩
        · rw [z21]; exact hz12
        · rw [z23']; exact lt_trans hz30 (lt_trans hz01 hz12)
        · rw [z22, z23]; exact hz01
    · by_cases hA_pos : 0 < αA
      · have hσ1 : σ = -1 := by simp [σ, hA_neg, hA_pos]
        have hz10 : z (a + 1) < z a := by
          have : z (a + 1) - z a < 0 := by
            rw [hz_QR, hσ1]; nlinarith
          linarith
        have hz03 : z a < z (a + 3) := by
          have := (ht3 t ht_pos ht_t3 (x (r (a + 3)) - x (r a)) (Or.inl rfl) hA_pos.ne').1 hA_pos
          rw [← hz_diff] at this; linarith
        rcases lt_trichotomy αB 0 with hB_neg | hB_zero | hB_pos
        · have hz21 : z (a + 2) < z (a + 1) := by
            have := (ht4 t ht_pos ht_t4 (x (r (a + 2)) - x (r a)) e
              (Or.inr rfl) (Or.inr (Or.inr rfl)) hB_neg.ne hu0_e).2 hB_neg
            have heu : ⟪e, u⟫ = z (a + 1) - z a := by dsimp [e]; rw [hz_diff]
            rw [heu, ← hz_diff] at this; linarith
          have hinj : Function.Injective z := inj_of_pairs
            ⟨hz10.ne', (lt_trans hz21 hz10).ne', hz03.ne, hz21.ne', (lt_trans hz10 hz03).ne,
              (lt_trans (lt_trans hz21 hz10) hz03).ne⟩
          refine ⟨hinj, strictUnimodal_of_zmod4 hinj ⟨a + 3, ?_, ?_, Or.inl ?_⟩⟩
          · rw [z31]; exact lt_trans (lt_trans hz21 hz10) hz03
          · rw [z30]; exact hz03
          · rw [z32, z30]; exact hz10
        · have h2_ne : z (a + 2) ≠ z a ∧ z (a + 2) ≠ z (a + 1) := by
            apply hz_edge_ne (a + 2) (Or.inr rfl) hB_zero
            rcases hlev.2.2 with h | h
            · exact absurd hB_zero h
            · exact h
          have hz23 : z (a + 2) < z (a + 3) := by
            have := (ht4 t ht_pos ht_t4 (x (r (a + 3)) - x (r a)) (x (r (a + 2)) - x (r a))
              (Or.inl rfl) (Or.inr (Or.inl rfl)) hA_pos.ne' hB_zero).1 hA_pos
            rw [← hz_diff, ← hz_diff] at this; linarith
          have hinj : Function.Injective z := inj_of_pairs
            ⟨hz10.ne', h2_ne.1.symm, hz03.ne, h2_ne.2.symm, (lt_trans hz10 hz03).ne, hz23.ne⟩
          refine ⟨hinj, strictUnimodal_of_zmod4 hinj ⟨a + 3, ?_, ?_, Or.inl ?_⟩⟩
          · rw [z31]; exact hz23
          · rw [z30]; exact hz03
          · rw [z32, z30]; exact hz10
        · have hz02 : z a < z (a + 2) := by
            have := (ht3 t ht_pos ht_t3 (x (r (a + 2)) - x (r a)) (Or.inr (Or.inl rfl)) hB_pos.ne').1 hB_pos
            rw [← hz_diff] at this; linarith
          have hinj : Function.Injective z := inj_of_pairs
            ⟨hz10.ne', hz02.ne, hz03.ne, (lt_trans hz10 hz02).ne, (lt_trans hz10 hz03).ne, hz_AB_ne.symm⟩
          refine ⟨hinj, ?_⟩
          rcases lt_or_gt_of_ne hz_AB_ne with hz32 | hz23
          · refine strictUnimodal_of_zmod4 hinj ⟨a + 2, ?_, ?_, Or.inl ?_⟩
            · rw [z21]; exact lt_trans hz10 hz02
            · rw [z23']; exact hz32
            · rw [z22, z23']; exact hz03
          · refine strictUnimodal_of_zmod4 hinj ⟨a + 3, ?_, ?_, Or.inl ?_⟩
            · rw [z31]; exact hz23
            · rw [z30]; exact hz03
            · rw [z32, z30]; exact hz10
      · have hA_zero : αA = 0 := le_antisymm (not_lt.mp hA_pos) (not_lt.mp hA_neg)
        have h3_ne : z (a + 3) ≠ z a ∧ z (a + 3) ≠ z (a + 1) := by
          apply hz_edge_ne (a + 3) (Or.inl rfl) hA_zero
          rcases hlev.2.1 with h | h
          · exact absurd hA_zero h
          · exact h
        have hB_ne : αB ≠ 0 := by
          rcases hlev.1 with h | h
          · exact absurd hA_zero h
          · exact h
        rcases lt_or_gt_of_ne hB_ne with hB_neg | hB_pos
        · have hσ1 : σ = -1 := by
            simp [σ, hA_neg, hA_pos, not_lt.mpr hB_neg.le]
          have hz10 : z (a + 1) < z a := by
            have : z (a + 1) - z a < 0 := by rw [hz_QR, hσ1]; nlinarith
            linarith
          have hz21 : z (a + 2) < z (a + 1) := by
            have := (ht4 t ht_pos ht_t4 (x (r (a + 2)) - x (r a)) e
              (Or.inr rfl) (Or.inr (Or.inr rfl)) hB_neg.ne hu0_e).2 hB_neg
            have heu : ⟪e, u⟫ = z (a + 1) - z a := by dsimp [e]; rw [hz_diff]
            rw [heu, ← hz_diff] at this; linarith
          have hz23 : z (a + 2) < z (a + 3) := by
            have := (ht4 t ht_pos ht_t4 (x (r (a + 2)) - x (r a)) (x (r (a + 3)) - x (r a))
              (Or.inr rfl) (Or.inl rfl) hB_neg.ne hA_zero).2 hB_neg
            rw [← hz_diff, ← hz_diff] at this; linarith
          have hinj : Function.Injective z := inj_of_pairs
            ⟨hz10.ne', (lt_trans hz21 hz10).ne', h3_ne.1.symm, hz21.ne', h3_ne.2.symm, hz23.ne⟩
          refine ⟨hinj, ?_⟩
          rcases lt_or_gt_of_ne h3_ne.1 with hz30 | hz03
          · refine strictUnimodal_of_zmod4 hinj ⟨a, ?_, hz10, Or.inl hz21⟩
            rw [z03]; exact hz30
          · refine strictUnimodal_of_zmod4 hinj ⟨a + 3, ?_, ?_, Or.inl ?_⟩
            · rw [z31]; exact hz23
            · rw [z30]; exact hz03
            · rw [z32, z30]; exact hz10
        · have hσ1 : σ = 1 := by
            simp [σ, hA_neg, hA_pos, hB_pos]
          have hz01 : z a < z (a + 1) := by
            have : 0 < z (a + 1) - z a := by rw [hz_QR, hσ1, mul_one]; exact mul_pos ht_pos hee_pos
            linarith
          have hz12 : z (a + 1) < z (a + 2) := by
            have := (ht4 t ht_pos ht_t4 (x (r (a + 2)) - x (r a)) e
              (Or.inr rfl) (Or.inr (Or.inr rfl)) hB_pos.ne' hu0_e).1 hB_pos
            have heu : ⟪e, u⟫ = z (a + 1) - z a := by dsimp [e]; rw [hz_diff]
            rw [heu, ← hz_diff] at this; linarith
          have hz32 : z (a + 3) < z (a + 2) := by
            have := (ht4 t ht_pos ht_t4 (x (r (a + 2)) - x (r a)) (x (r (a + 3)) - x (r a))
              (Or.inr rfl) (Or.inl rfl) hB_pos.ne' hA_zero).1 hB_pos
            rw [← hz_diff, ← hz_diff] at this; linarith
          have hinj : Function.Injective z := inj_of_pairs
            ⟨hz01.ne, (lt_trans hz01 hz12).ne, h3_ne.1.symm, hz12.ne, h3_ne.2.symm, hz32.ne'⟩
          refine ⟨hinj, strictUnimodal_of_zmod4 hinj ⟨a + 2, ?_, ?_, Or.inr ?_⟩⟩
          · rw [z21]; exact hz12
          · rw [z23']; exact hz32
          · rw [z22, z23]; exact hz01
  exact faceChordView_of_rimCert (k := 4) (by norm_num) F T u r a tn tp sp hcert
    hnu (ht1 t ht_pos ht_t1) hca (ht2 t ht_pos ht_t2) hz_both.1 (Or.inl hz_both.2) hfar

/-! ### Rim and edge tables for C1-C5 -/

def rimC2 : ZMod 4 → Fin 7 := ![0, 1, 2, 5]
def rimC3 : ZMod 4 → Fin 7 := ![0, 5, 3, 6]
def rimC4 : ZMod 4 → Fin 7 := ![0, 2, 6, 4]

/-- Rim-edge facet data (negative facet, positive facet, separating facet) per case. -/
def tnC1 : ZMod 5 → Fin 9 := ![0, 0, 6, 3, 3]
def tpC1 : ZMod 5 → Fin 9 := ![1, 5, 6, 8, 4]
def spC1 : ZMod 5 → Fin 9 := ![2, 1, 0, 6, 8]
def tnC2 : ZMod 4 → Fin 9 := ![1, 5, 6, 2]
def tpC2 : ZMod 4 → Fin 9 := ![0, 0, 2, 2]
def spC2 : ZMod 4 → Fin 9 := ![2, 1, 0, 6]
def tnC3 : ZMod 4 → Fin 9 := ![2, 6, 7, 4]
def tpC3 : ZMod 4 → Fin 9 := ![3, 3, 8, 4]
def spC3 : ZMod 4 → Fin 9 := ![0, 2, 3, 5]
def tnC4 : ZMod 4 → Fin 9 := ![0, 7, 8, 3]
def tpC4 : ZMod 4 → Fin 9 := ![0, 5, 4, 4]
def spC4 : ZMod 4 → Fin 9 := ![1, 0, 1, 8]
def tnC5 : ZMod 5 → Fin 9 := ![5, 6, 6, 7, 5]
def tpC5 : ZMod 5 → Fin 9 := ![0, 6, 3, 8, 1]
def spC5 : ZMod 5 → Fin 9 := ![1, 0, 2, 3, 4]

def rimC5 : ZMod 5 → Fin 7 := ![1, 2, 5, 3, 6]
def rimC5' : ZMod 5 → Fin 7 := ![1, 6, 4, 3, 2]

/-! ### Meridian cases C2-C5 and mirrors -/

theorem faceChordView_C2 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hM1 : 0 < ⟪F.N 0, mer F 2 3⟫ ∧ ⟪F.N 1, mer F 2 3⟫ < 0 ∧ ⟪F.N 5, mer F 2 3⟫ < 0)
    (hM2 : 0 < ⟪x 3 - x 5, x 0 - x 5⟫ ∧ 0 < ⟪x 3 - x 0, x 5 - x 0⟫ ∧
      0 < ⟪x 4 - x 5, x 0 - x 5⟫ ∧ 0 < ⟪x 4 - x 0, x 5 - x 0⟫)
    (hguard : ⟪x 2 - x 1, mer F 2 3⟫ ≠ 0 ∨ ⟪x 2 - x 1, x 0 - x 5⟫ ≠ 0)
    (hlev : (⟪x 2 - x 5, mer F 2 3⟫ ≠ 0 ∨ ⟪x 1 - x 5, mer F 2 3⟫ ≠ 0) ∧
      (⟪x 2 - x 5, mer F 2 3⟫ ≠ 0 ∨
        ⟪x 2 - x 5, x 0 - x 5⟫ ≠ 0 ∧ ⟪x 2 - x 0, x 0 - x 5⟫ ≠ 0) ∧
      (⟪x 1 - x 5, mer F 2 3⟫ ≠ 0 ∨
        ⟪x 1 - x 5, x 0 - x 5⟫ ≠ 0 ∧ ⟪x 1 - x 0, x 0 - x 5⟫ ≠ 0))
    (hM4 :
      (F.f 3 (x 1) < F.f 3 (x 2) ∧
        (⟪F.N 3, cross (x 0 - x 5) (x 1 - x 5)⟫ ≠ 0 ∨ ⟪x 1 - x 5, x 0 - x 5⟫ < 0 ∨
          ⟪x 1 - x 0, x 5 - x 0⟫ < 0)) ∨
      (F.f 3 (x 2) < F.f 3 (x 1) ∧
        (⟪F.N 3, cross (x 0 - x 5) (x 2 - x 5)⟫ ≠ 0 ∨ ⟪x 2 - x 5, x 0 - x 5⟫ < 0 ∨
          ⟪x 2 - x 0, x 5 - x 0⟫ < 0))) :
    FaceChordView F 3 := by
  rcases hM1 with ⟨h0, h1, h5⟩
  obtain ⟨h3a, h3b, h4a, h4b⟩ := hM2
  have hm : mer F 2 3 ≠ 0 := fun h => by rw [h, inner_zero_right] at h0; exact lt_irrefl 0 h0
  have h2 : 0 < ⟪F.N 2, mer F 2 3⟫ := mer_source_pos F 2 3 hm
  obtain ⟨s, δ, hs, hs1, -, hx⟩ := level_chord_middle F 2 3 5 0 3 (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) h3a h3b
  have h6 : ⟪F.N 6, mer F 2 3⟫ < 0 := by
    have := chord_middle_facet_sign F 6 2 (by decide) (by decide) (by decide) (by decide)
      (Or.inr (by decide)) hs hs1 hx
    nlinarith
  refine faceChordView_mer4 F 2 3 rimC2 3 tnC2 tpC2 spC2 (by decide) rfl
    (by decide) ?_ ?_ hguard hlev ?_
  · intro i hi
    fin_cases i
    · exact ⟨h1, h0⟩
    · exact ⟨h5, h0⟩
    · exact ⟨h6, h2⟩
    · exact absurd rfl hi
  · intro q hq hqr
    fin_cases q <;> first | exact absurd hq (by decide) | exact absurd rfl (hqr 0) |
      exact absurd rfl (hqr 3) | exact ⟨h3a, h3b⟩ | exact ⟨h4a, h4b⟩
  · rcases hM4 with ⟨h12, hoff⟩ | ⟨h21, hoff⟩
    · refine ⟨1, by decide, fun m hm hmr => ?_, hoff⟩
      fin_cases m <;> first | exact absurd rfl hm | exact absurd hmr (by decide) | exact h12
    · refine ⟨2, by decide, fun m hm hmr => ?_, hoff⟩
      fin_cases m <;> first | exact absurd rfl hm | exact absurd hmr (by decide) | exact h21

theorem faceChordView_C2' {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hM1 : 0 < ⟪F.N 1, mer F 4 3⟫ ∧ ⟪F.N 0, mer F 4 3⟫ < 0 ∧ ⟪F.N 5, mer F 4 3⟫ < 0)
    (hM2 : 0 < ⟪x 3 - x 4, x 0 - x 4⟫ ∧ 0 < ⟪x 3 - x 0, x 4 - x 0⟫ ∧
      0 < ⟪x 5 - x 4, x 0 - x 4⟫ ∧ 0 < ⟪x 5 - x 0, x 4 - x 0⟫)
    (hguard : ⟪x 6 - x 1, mer F 4 3⟫ ≠ 0 ∨ ⟪x 6 - x 1, x 0 - x 4⟫ ≠ 0)
    (hlev : (⟪x 6 - x 4, mer F 4 3⟫ ≠ 0 ∨ ⟪x 1 - x 4, mer F 4 3⟫ ≠ 0) ∧
      (⟪x 6 - x 4, mer F 4 3⟫ ≠ 0 ∨
        ⟪x 6 - x 4, x 0 - x 4⟫ ≠ 0 ∧ ⟪x 6 - x 0, x 0 - x 4⟫ ≠ 0) ∧
      (⟪x 1 - x 4, mer F 4 3⟫ ≠ 0 ∨
        ⟪x 1 - x 4, x 0 - x 4⟫ ≠ 0 ∧ ⟪x 1 - x 0, x 0 - x 4⟫ ≠ 0))
    (hM4 :
      (F.f 3 (x 1) < F.f 3 (x 6) ∧
        (⟪F.N 3, cross (x 0 - x 4) (x 1 - x 4)⟫ ≠ 0 ∨ ⟪x 1 - x 4, x 0 - x 4⟫ < 0 ∨
          ⟪x 1 - x 0, x 4 - x 0⟫ < 0)) ∨
      (F.f 3 (x 6) < F.f 3 (x 1) ∧
        (⟪F.N 3, cross (x 0 - x 4) (x 6 - x 4)⟫ ≠ 0 ∨ ⟪x 6 - x 4, x 0 - x 4⟫ < 0 ∨
          ⟪x 6 - x 0, x 4 - x 0⟫ < 0))) :
    FaceChordView F 3 := by
  exact faceChordView_sym F (faceChordView_C2 (sym24 F) (x := x ∘ pi24) hM1 hM2 hguard hlev hM4)

theorem faceChordView_C3 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hM1 : 0 < ⟪F.N 3, mer F 4 1⟫ ∧ 0 < ⟪F.N 8, mer F 4 1⟫ ∧
      ⟪F.N 2, mer F 4 1⟫ < 0 ∧ ⟪F.N 6, mer F 4 1⟫ < 0 ∧ ⟪F.N 7, mer F 4 1⟫ < 0)
    (hM2 : 0 < ⟪x 1 - x 6, x 0 - x 6⟫ ∧ 0 < ⟪x 1 - x 0, x 6 - x 0⟫)
    (hguard : ⟪x 3 - x 5, mer F 4 1⟫ ≠ 0 ∨ ⟪x 3 - x 5, x 0 - x 6⟫ ≠ 0)
    (hlev : (⟪x 3 - x 6, mer F 4 1⟫ ≠ 0 ∨ ⟪x 5 - x 6, mer F 4 1⟫ ≠ 0) ∧
      (⟪x 3 - x 6, mer F 4 1⟫ ≠ 0 ∨
        ⟪x 3 - x 6, x 0 - x 6⟫ ≠ 0 ∧ ⟪x 3 - x 0, x 0 - x 6⟫ ≠ 0) ∧
      (⟪x 5 - x 6, mer F 4 1⟫ ≠ 0 ∨
        ⟪x 5 - x 6, x 0 - x 6⟫ ≠ 0 ∧ ⟪x 5 - x 0, x 0 - x 6⟫ ≠ 0))
    (hM4 :
      (F.f 1 (x 3) < F.f 1 (x 5) ∧
        (⟪F.N 1, cross (x 0 - x 6) (x 3 - x 6)⟫ ≠ 0 ∨ ⟪x 3 - x 6, x 0 - x 6⟫ < 0 ∨
          ⟪x 3 - x 0, x 6 - x 0⟫ < 0)) ∨
      (F.f 1 (x 5) < F.f 1 (x 3) ∧
        (⟪F.N 1, cross (x 0 - x 6) (x 5 - x 6)⟫ ≠ 0 ∨ ⟪x 5 - x 6, x 0 - x 6⟫ < 0 ∨
          ⟪x 5 - x 0, x 6 - x 0⟫ < 0))) :
    FaceChordView F 1 := by
  rcases hM1 with ⟨h3, h8, h2, h6, h7⟩
  refine faceChordView_mer4 F 4 1 rimC3 3 tnC3 tpC3 spC3 (by decide) rfl
    (by decide) ?_ ?_ hguard hlev ?_
  · intro i hi
    fin_cases i
    · exact ⟨h2, h3⟩
    · exact ⟨h6, h3⟩
    · exact ⟨h7, h8⟩
    · exact absurd rfl hi
  · intro q hq hqr
    fin_cases q <;> first | exact absurd hq (by decide) | exact absurd rfl (hqr 0) |
      exact absurd rfl (hqr 3) | exact hM2
  · rcases hM4 with ⟨h35, hoff⟩ | ⟨h53, hoff⟩
    · refine ⟨2, by decide, fun m hm hmr => ?_, hoff⟩
      fin_cases m <;> first | exact absurd rfl hm | exact absurd hmr (by decide) | exact h35
    · refine ⟨1, by decide, fun m hm hmr => ?_, hoff⟩
      fin_cases m <;> first | exact absurd rfl hm | exact absurd hmr (by decide) | exact h53

theorem faceChordView_C3' {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hM1 : 0 < ⟪F.N 3, mer F 2 0⟫ ∧ 0 < ⟪F.N 6, mer F 2 0⟫ ∧
      ⟪F.N 4, mer F 2 0⟫ < 0 ∧ ⟪F.N 8, mer F 2 0⟫ < 0 ∧ ⟪F.N 7, mer F 2 0⟫ < 0)
    (hM2 : 0 < ⟪x 1 - x 2, x 0 - x 2⟫ ∧ 0 < ⟪x 1 - x 0, x 2 - x 0⟫)
    (hguard : ⟪x 3 - x 4, mer F 2 0⟫ ≠ 0 ∨ ⟪x 3 - x 4, x 0 - x 2⟫ ≠ 0)
    (hlev : (⟪x 3 - x 2, mer F 2 0⟫ ≠ 0 ∨ ⟪x 4 - x 2, mer F 2 0⟫ ≠ 0) ∧
      (⟪x 3 - x 2, mer F 2 0⟫ ≠ 0 ∨
        ⟪x 3 - x 2, x 0 - x 2⟫ ≠ 0 ∧ ⟪x 3 - x 0, x 0 - x 2⟫ ≠ 0) ∧
      (⟪x 4 - x 2, mer F 2 0⟫ ≠ 0 ∨
        ⟪x 4 - x 2, x 0 - x 2⟫ ≠ 0 ∧ ⟪x 4 - x 0, x 0 - x 2⟫ ≠ 0))
    (hM4 :
      (F.f 0 (x 3) < F.f 0 (x 4) ∧
        (⟪F.N 0, cross (x 0 - x 2) (x 3 - x 2)⟫ ≠ 0 ∨ ⟪x 3 - x 2, x 0 - x 2⟫ < 0 ∨
          ⟪x 3 - x 0, x 2 - x 0⟫ < 0)) ∨
      (F.f 0 (x 4) < F.f 0 (x 3) ∧
        (⟪F.N 0, cross (x 0 - x 2) (x 4 - x 2)⟫ ≠ 0 ∨ ⟪x 4 - x 2, x 0 - x 2⟫ < 0 ∨
          ⟪x 4 - x 0, x 2 - x 0⟫ < 0))) :
    FaceChordView F 0 := by
  exact faceChordView_sym F (faceChordView_C3 (sym24 F) (x := x ∘ pi24) hM1 hM2 hguard hlev hM4)

theorem faceChordView_C4 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hM1 : ⟪F.N 7, mer F 0 2⟫ < 0 ∧ ⟪F.N 8, mer F 0 2⟫ < 0 ∧
      0 < ⟪F.N 5, mer F 0 2⟫ ∧ 0 < ⟪F.N 4, mer F 0 2⟫)
    (hM2 : 0 < ⟪x 5 - x 0, x 2 - x 0⟫ ∧ 0 < ⟪x 5 - x 2, x 0 - x 2⟫)
    (hguard : ⟪x 4 - x 6, mer F 0 2⟫ ≠ 0 ∨ ⟪x 4 - x 6, x 2 - x 0⟫ ≠ 0)
    (hlev : (⟪x 4 - x 0, mer F 0 2⟫ ≠ 0 ∨ ⟪x 6 - x 0, mer F 0 2⟫ ≠ 0) ∧
      (⟪x 4 - x 0, mer F 0 2⟫ ≠ 0 ∨
        ⟪x 4 - x 0, x 2 - x 0⟫ ≠ 0 ∧ ⟪x 4 - x 2, x 2 - x 0⟫ ≠ 0) ∧
      (⟪x 6 - x 0, mer F 0 2⟫ ≠ 0 ∨
        ⟪x 6 - x 0, x 2 - x 0⟫ ≠ 0 ∧ ⟪x 6 - x 2, x 2 - x 0⟫ ≠ 0))
    (hM4 :
      (F.f 2 (x 6) < F.f 2 (x 4) ∧
        (⟪F.N 2, cross (x 2 - x 0) (x 6 - x 0)⟫ ≠ 0 ∨ ⟪x 6 - x 0, x 2 - x 0⟫ < 0 ∨
          ⟪x 6 - x 2, x 0 - x 2⟫ < 0)) ∨
      (F.f 2 (x 4) < F.f 2 (x 6) ∧
        (⟪F.N 2, cross (x 2 - x 0) (x 4 - x 0)⟫ ≠ 0 ∨ ⟪x 4 - x 0, x 2 - x 0⟫ < 0 ∨
          ⟪x 4 - x 2, x 0 - x 2⟫ < 0))) :
    FaceChordView F 2 := by
  rcases hM1 with ⟨h7, h8, h5, h4⟩
  have hm : mer F 0 2 ≠ 0 := fun h => by rw [h, inner_zero_right] at h5; exact lt_irrefl 0 h5
  have h0 : 0 < ⟪F.N 0, mer F 0 2⟫ := mer_source_pos F 0 2 hm
  obtain ⟨s, δ, hs, hs1, -, hx⟩ := level_chord_middle F 0 2 0 2 5 (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) hM2.1 hM2.2
  have h3 : ⟪F.N 3, mer F 0 2⟫ < 0 := by
    have := chord_middle_facet_sign F 3 0 (by decide) (by decide) (by decide) (by decide)
      (Or.inr (by decide)) hs hs1 hx
    nlinarith
  refine faceChordView_mer4 F 0 2 rimC4 0 tnC4 tpC4 spC4 (by decide) rfl
    (by decide) ?_ ?_ hguard hlev ?_
  · intro i hi
    fin_cases i
    · exact absurd rfl hi
    · exact ⟨h7, h5⟩
    · exact ⟨h8, h4⟩
    · exact ⟨h3, h4⟩
  · intro q hq hqr
    fin_cases q <;> first | exact absurd hq (by decide) | exact absurd rfl (hqr 0) |
      exact absurd rfl (hqr 1) | exact hM2
  · rcases hM4 with ⟨h64, hoff⟩ | ⟨h46, hoff⟩
    · refine ⟨2, by decide, fun m hm hmr => ?_, hoff⟩
      fin_cases m <;> first | exact absurd rfl hm | exact absurd hmr (by decide) | exact h64
    · refine ⟨3, by decide, fun m hm hmr => ?_, hoff⟩
      fin_cases m <;> first | exact absurd rfl hm | exact absurd hmr (by decide) | exact h46

theorem faceChordView_C4' {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hM1 : ⟪F.N 7, mer F 1 4⟫ < 0 ∧ ⟪F.N 6, mer F 1 4⟫ < 0 ∧
      0 < ⟪F.N 5, mer F 1 4⟫ ∧ 0 < ⟪F.N 2, mer F 1 4⟫)
    (hM2 : 0 < ⟪x 4 - x 0, x 6 - x 0⟫ ∧ 0 < ⟪x 4 - x 6, x 0 - x 6⟫)
    (hguard : ⟪x 5 - x 2, mer F 1 4⟫ ≠ 0 ∨ ⟪x 5 - x 2, x 6 - x 0⟫ ≠ 0)
    (hlev : (⟪x 5 - x 0, mer F 1 4⟫ ≠ 0 ∨ ⟪x 2 - x 0, mer F 1 4⟫ ≠ 0) ∧
      (⟪x 5 - x 0, mer F 1 4⟫ ≠ 0 ∨
        ⟪x 5 - x 0, x 6 - x 0⟫ ≠ 0 ∧ ⟪x 5 - x 6, x 6 - x 0⟫ ≠ 0) ∧
      (⟪x 2 - x 0, mer F 1 4⟫ ≠ 0 ∨
        ⟪x 2 - x 0, x 6 - x 0⟫ ≠ 0 ∧ ⟪x 2 - x 6, x 6 - x 0⟫ ≠ 0))
    (hM4 :
      (F.f 4 (x 2) < F.f 4 (x 5) ∧
        (⟪F.N 4, cross (x 6 - x 0) (x 2 - x 0)⟫ ≠ 0 ∨ ⟪x 2 - x 0, x 6 - x 0⟫ < 0 ∨
          ⟪x 2 - x 6, x 0 - x 6⟫ < 0)) ∨
      (F.f 4 (x 5) < F.f 4 (x 2) ∧
        (⟪F.N 4, cross (x 6 - x 0) (x 5 - x 0)⟫ ≠ 0 ∨ ⟪x 5 - x 0, x 6 - x 0⟫ < 0 ∨
          ⟪x 5 - x 6, x 0 - x 6⟫ < 0))) :
    FaceChordView F 4 := by
  exact faceChordView_sym F (faceChordView_C4 (sym24 F) (x := x ∘ pi24) hM1 hM2 hguard hlev hM4)

theorem faceChordView_C5 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hM1 : ⟪F.N 5, mer F 4 2⟫ < 0 ∧ ⟪F.N 6, mer F 4 2⟫ < 0 ∧
      ⟪F.N 7, mer F 4 2⟫ < 0 ∧ 0 < ⟪F.N 1, mer F 4 2⟫ ∧ 0 < ⟪F.N 8, mer F 4 2⟫)
    (hM2 : 0 < ⟪x 0 - x 2, cross (F.N 2) (F.N 4)⟫ * ⟪x 5 - x 0, cross (F.N 2) (F.N 4)⟫)
    (hinj : Function.Injective fun i : ZMod 5 => ⟪x (rimC5 i), mer F 4 2⟫)
    (hz : UniOrSep (fun i : ZMod 5 => x (rimC5 i)) (mer F 4 2))
    (hM4 :
      (F.f 2 (x 6) < F.f 2 (x 1) ∧ F.f 2 (x 6) < F.f 2 (x 3) ∧
        (⟪F.N 2, cross (x 5 - x 2) (x 6 - x 2)⟫ ≠ 0 ∨ ⟪x 6 - x 2, x 5 - x 2⟫ < 0 ∨
          ⟪x 6 - x 5, x 2 - x 5⟫ < 0)) ∨
      (F.f 2 (x 3) < F.f 2 (x 1) ∧ F.f 2 (x 3) < F.f 2 (x 6) ∧
        (⟪F.N 2, cross (x 5 - x 2) (x 3 - x 2)⟫ ≠ 0 ∨ ⟪x 3 - x 2, x 5 - x 2⟫ < 0 ∨
          ⟪x 3 - x 5, x 2 - x 5⟫ < 0)) ∨
      (F.f 2 (x 1) < F.f 2 (x 3) ∧ F.f 2 (x 1) < F.f 2 (x 6) ∧
        (⟪F.N 2, cross (x 5 - x 2) (x 1 - x 2)⟫ ≠ 0 ∨ ⟪x 1 - x 2, x 5 - x 2⟫ < 0 ∨
          ⟪x 1 - x 5, x 2 - x 5⟫ < 0))) :
    FaceChordView F 2 := by
  rcases hM1 with ⟨h5, h6, h7, h1, h8⟩
  obtain ⟨s, δ, hs, hs1, hδ, hx⟩ := chord_middle_of_mer F 4 2 6 2 5 0 (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) hM2
  have h0 : 0 < ⟪F.N 0, mer F 4 2⟫ := by
    have := chord_middle_facet_sign F 0 6 (by decide) (by decide) (by decide) (by decide)
      (Or.inr (by decide)) hs hs1 hx
    nlinarith
  have h3 : 0 < ⟪F.N 3, mer F 4 2⟫ := by
    have := chord_middle_facet_sign F 3 6 (by decide) (by decide) (by decide) (by decide)
      (Or.inl (by decide)) hs hs1 hx
    nlinarith
  refine faceChordView_of_rimCert (k := 5) (by norm_num) F 2 (mer F 4 2) rimC5 1
    tnC5 tpC5 spC5 (by decide) (mer_inner_facet F 4 2) ?_
    h6.ne ?_ hinj hz ?_
  · intro i hi
    fin_cases i
    · exact ⟨h5, h0⟩
    · exact absurd rfl hi
    · exact ⟨h6, h3⟩
    · exact ⟨h7, h8⟩
    · exact ⟨h5, h1⟩
  · intro q hq hqr
    have hq0 : q = 0 := by
      fin_cases q <;> first | exact absurd hq (by decide) | exact absurd rfl (hqr 1) |
        exact absurd rfl (hqr 2) | rfl
    subst hq0
    exact ⟨s, δ, hs, hs1, hδ, hx⟩
  · rcases hM4 with ⟨h61, h63, hoff⟩ | ⟨h31, h36, hoff⟩ | ⟨h13, h16, hoff⟩
    · refine ⟨4, by decide, fun m hm hmr => ?_, hoff⟩
      fin_cases m <;> first | exact absurd rfl hm | exact absurd hmr (by decide) | exact h61 |
        exact h63
    · refine ⟨3, by decide, fun m hm hmr => ?_, hoff⟩
      fin_cases m <;> first | exact absurd rfl hm | exact absurd hmr (by decide) | exact h31 |
        exact h36
    · refine ⟨0, by decide, fun m hm hmr => ?_, hoff⟩
      fin_cases m <;> first | exact absurd rfl hm | exact absurd hmr (by decide) | exact h13 |
        exact h16

end Minimality.T24.Mer
