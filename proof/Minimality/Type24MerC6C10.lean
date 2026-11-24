module

public import Minimality.Type24MerC2C5

@[expose] public section

set_option autoImplicit false

open scoped RealInnerProductSpace
open Finset Filter Topology
open Minimality Minimality.H21 Minimality.FaceChord Minimality.T24.SAT Minimality.T24.Sym
open Minimality.RimFromSigns Minimality.T24.Q45

namespace Minimality.T24.Mer

/-! ### (A) Two engine variants -/

/-- **Rim engine, explicit chord transversality.**  As `faceChordView_of_rimCert`, with `hca` replaced by
`hcr` (for a chord that is a diagonal of `T`, where no second facet contains it; then take `tn a = T`
in the certificate). -/
theorem faceChordView_of_rimCert_cr {k : ℕ} [NeZero k] (hk : 3 ≤ k) {x : Fin 7 → ℝ³}
    (F : S0xFac 9 s0x_S24 x) (T : Fin 9) (u : ℝ³) (r : ZMod k → Fin 7) (a : ZMod k)
    (tn tp sp : ZMod k → Fin 9) (hcert : RimCert T r a tn tp sp)
    (hnu : ⟪F.N T, u⟫ = 0)
    (hsg : ∀ i, i ≠ a → ⟪F.N (tn i), u⟫ < 0 ∧ 0 < ⟪F.N (tp i), u⟫)
    (hcr : cross u (x (r (a + 1)) - x (r a)) ≠ 0)
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
      obtain ⟨σ, hσ_ne, hσ⟩ :=
        det3_sign_edgeOn F T (r i) (r (i + 1)) h_chord.1 h_chord.2.1 u hnu hcr
      refine ⟨σ, hσ_ne, fun y hy1 hy2 hyT => hσ y ?_⟩
      have := h_off i y hy1 hy2 hyT
      simpa using this
    · have hri := h_ridge i hia
      have hcri : cross u (x (r (i + 1)) - x (r i)) ≠ 0 :=
        cross_ne_zero_of_facet_sign F (tn i) (r i) (r (i + 1))
          hri.1 hri.2.1 (hsg i hia).1.ne (sp i) (h_sp i).1 (h_sp i).2
      obtain ⟨σ, hσ_ne, hσ⟩ :=
        det3_sign_ridge F (tn i) (tp i) (r i) (r (i + 1))
          ⟨hri.1, hri.2.2.1⟩ ⟨hri.2.1, hri.2.2.2⟩ u (hsg i hia) hcri
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
    have h2 := hσ (i + 1) (r i) hne01
      (by rw [add_assoc, show (1 : ZMod k) + 1 = 2 by ring]; exact hne02) (Or.inr ⟨i, rfl⟩)
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

/-- **Chord-slide rim engine (any k).**  All strict tests at `u0` on the circle of `T`; the depths may tie
on the chord pair at `u0` (a level chord); `hz` holds along the slide `u0 + t σ (x R - x Q)`, `t → 0+`.
Witness: `faceChordView_of_rimCert` at `u0 + t σ (x R - x Q)` for one small `t > 0`. -/
theorem faceChordView_of_rimCert_slide {k : ℕ} [NeZero k] (hk : 3 ≤ k) {x : Fin 7 → ℝ³}
    (F : S0xFac 9 s0x_S24 x) (T : Fin 9) (u0 : ℝ³) (σ : ℝ) (r : ZMod k → Fin 7) (a : ZMod k)
    (tn tp sp : ZMod k → Fin 9) (hcert : RimCert T r a tn tp sp)
    (hnu : ⟪F.N T, u0⟫ = 0)
    (hsg : ∀ i, i ≠ a → ⟪F.N (tn i), u0⟫ < 0 ∧ 0 < ⟪F.N (tp i), u0⟫)
    (hca : ⟪F.N (tn a), u0⟫ ≠ 0)
    (hmid : ∀ q ∈ s0x_S24 T, (∀ j, q ≠ r j) → ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
      x q = x (r a) + s • (x (r (a + 1)) - x (r a)) + δ • u0)
    (hinj : ∀ i j : ZMod k, i ≠ j → ({i, j} : Finset (ZMod k)) ≠ {a, a + 1} →
      ⟪x (r i), u0⟫ ≠ ⟪x (r j), u0⟫)
    (hσ : σ ≠ 0)
    (hz : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      UniOrSep (fun i => x (r i)) (u0 + t • (σ • (x (r (a + 1)) - x (r a)))))
    (hfar : ∃ w, r w ∉ s0x_S24 T ∧
      (∀ m, m ≠ w → r m ∉ s0x_S24 T → F.f T (x (r w)) < F.f T (x (r m))) ∧
      (⟪F.N T, cross (x (r (a + 1)) - x (r a)) (x (r w) - x (r a))⟫ ≠ 0 ∨
        ⟪x (r w) - x (r a), x (r (a + 1)) - x (r a)⟫ < 0 ∨
        ⟪x (r w) - x (r (a + 1)), x (r a) - x (r (a + 1))⟫ < 0)) :
    FaceChordView F T := by
  set e := x (r (a + 1)) - x (r a)
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
  have h_open_lt : ∀ (v : ℝ³) (c : ℝ), ⟪v, u0⟫ < c →
      ∀ᶠ t in 𝓝[>] (0 : ℝ), ⟪v, u0 + t • (σ • e)⟫ < c := by
    intro v c hvc
    have hcont : ContinuousAt (fun t : ℝ => ⟪v, u0 + t • (σ • e)⟫) 0 := by
      have : (fun t : ℝ => ⟪v, u0 + t • (σ • e)⟫) = fun t : ℝ => ⟪v, u0⟫ + t * (σ * ⟪v, e⟫) := by
        ext t; rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
      rw [this]
      exact continuous_const.add (continuous_id.mul continuous_const) |>.continuousAt
    exact (hcont.tendsto.mono_left nhdsWithin_le_nhds).eventually (gt_mem_nhds (by simpa using hvc))
  have h_open_gt : ∀ (v : ℝ³) (c : ℝ), c < ⟪v, u0⟫ →
      ∀ᶠ t in 𝓝[>] (0 : ℝ), c < ⟪v, u0 + t • (σ • e)⟫ := by
    intro v c hvc
    have hcont : ContinuousAt (fun t : ℝ => ⟪v, u0 + t • (σ • e)⟫) 0 := by
      have : (fun t : ℝ => ⟪v, u0 + t • (σ • e)⟫) = fun t : ℝ => ⟪v, u0⟫ + t * (σ * ⟪v, e⟫) := by
        ext t; rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
      rw [this]
      exact continuous_const.add (continuous_id.mul continuous_const) |>.continuousAt
    exact (hcont.tendsto.mono_left nhdsWithin_le_nhds).eventually (lt_mem_nhds (by simpa using hvc))
  have h_open_ne : ∀ (v : ℝ³), ⟪v, u0⟫ ≠ 0 →
      ∀ᶠ t in 𝓝[>] (0 : ℝ), ⟪v, u0 + t • (σ • e)⟫ ≠ 0 := by
    intro v hv
    rcases lt_or_gt_of_ne hv with hlt | hgt
    · exact (h_open_lt v 0 hlt).mono fun _ h => h.ne
    · exact (h_open_gt v 0 hgt).mono fun _ h => h.ne'
  have h_sg : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ i : ZMod k, i ≠ a →
      ⟪F.N (tn i), u0 + t • (σ • e)⟫ < 0 ∧ 0 < ⟪F.N (tp i), u0 + t • (σ • e)⟫ := by
    rw [eventually_all]
    intro i
    by_cases hia : i = a
    · exact Eventually.of_forall fun _ hi => absurd hia hi
    · have h1 := h_open_lt (F.N (tn i)) 0 (hsg i hia).1
      have h2 := h_open_gt (F.N (tp i)) 0 (hsg i hia).2
      exact (h1.and h2).mono fun _ ⟨ha, hb⟩ _ => ⟨ha, hb⟩
  have h_ca : ∀ᶠ t in 𝓝[>] (0 : ℝ), ⟪F.N (tn a), u0 + t • (σ • e)⟫ ≠ 0 :=
    h_open_ne (F.N (tn a)) hca
  have h_mid : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ q ∈ s0x_S24 T, (∀ j, q ≠ r j) →
      ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
        x q = x (r a) + s • e + δ • (u0 + t • (σ • e)) := by
    rw [eventually_all]
    intro q
    by_cases hqT : q ∈ s0x_S24 T
    · by_cases hqr : ∀ j, q ≠ r j
      · obtain ⟨s, δ, hs, hs1, hδ, hx⟩ := hmid q hqT hqr
        set c := |δ * σ| + 1
        have hpos_eps : 0 < min s (1 - s) / c := div_pos (lt_min hs (by linarith)) (by positivity)
        have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ Set.Ioo 0 (min s (1 - s) / c) :=
          Ioo_mem_nhdsGT hpos_eps
        refine hev.mono fun t ⟨ht, ht_lt⟩ _ _ => ?_
        have htc : t * c < min s (1 - s) := (lt_div_iff₀ (by positivity)).mp ht_lt
        have h_abs : |t * δ * σ| ≤ t * c := by
          rw [mul_assoc, abs_mul, abs_of_pos ht]
          exact mul_le_mul_of_nonneg_left (by dsimp [c]; linarith) ht.le
        have h_abs' : |t * δ * σ| < min s (1 - s) := lt_of_le_of_lt h_abs htc
        have h_lo : -(1 - s) < t * δ * σ := by
          have := neg_lt_of_abs_lt (lt_of_lt_of_le h_abs' (min_le_right _ _))
          linarith
        have h_hi : t * δ * σ < s :=
          lt_of_le_of_lt (le_abs_self _) (lt_of_lt_of_le h_abs' (min_le_left _ _))
        refine ⟨s - t * δ * σ, δ, by linarith, by linarith, hδ, ?_⟩
        rw [hx]
        ext j; simp [e]; ring
      · exact Eventually.of_forall fun _ _ h => absurd h hqr
    · exact Eventually.of_forall fun _ h => absurd h hqT
  have h_chord_ne : ∀ᶠ t in 𝓝[>] (0 : ℝ), ⟪e, u0 + t • (σ • e)⟫ ≠ 0 := by
    have h_pos_set : ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, 0 < t → t < ε → ⟪e, u0 + t • (σ • e)⟫ ≠ 0 := by
      by_cases h0 : ⟪e, u0⟫ = 0
      · refine ⟨1, one_pos, fun t ht _ => ?_⟩
        rw [inner_add_right, real_inner_smul_right, real_inner_smul_right, h0, zero_add]
        exact mul_ne_zero ht.ne' (mul_ne_zero hσ hee_pos.ne')
      · refine ⟨|⟪e, u0⟫| / (|σ * ⟪e, e⟫| + 1), div_pos (abs_pos.mpr h0) (by positivity),
          fun t ht ht_lt => ?_⟩
        have htc : t * (|σ * ⟪e, e⟫| + 1) < |⟪e, u0⟫| := (lt_div_iff₀ (by positivity)).mp ht_lt
        have h_abs : |t * (σ * ⟪e, e⟫)| < |⟪e, u0⟫| := by
          rw [abs_mul, abs_of_pos ht]
          exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left (by linarith) ht.le) htc
        rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
        intro heq
        have : |t * (σ * ⟪e, e⟫)| = |⟪e, u0⟫| := by
          rw [show t * (σ * ⟪e, e⟫) = -⟪e, u0⟫ by linarith, abs_neg]
        linarith
    obtain ⟨ε, hε, hε_ne⟩ := h_pos_set
    exact Filter.Eventually.mono (Ioo_mem_nhdsGT hε) fun t ⟨ht, ht_lt⟩ => hε_ne t ht ht_lt
  have h_inj : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      Function.Injective fun i : ZMod k => ⟪x (r i), u0 + t • (σ • e)⟫ := by
    have h_pairs : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ i j : ZMod k, i ≠ j →
        ⟪x (r i) - x (r j), u0 + t • (σ • e)⟫ ≠ 0 := by
      rw [eventually_all]
      intro i
      rw [eventually_all]
      intro j
      by_cases hij : i = j
      · exact Eventually.of_forall fun _ h => absurd hij h
      · by_cases hpair : ({i, j} : Finset (ZMod k)) = {a, a + 1}
        · refine h_chord_ne.mono fun t ht _ => ?_
          have hmem : i ∈ ({a, a + 1} : Finset (ZMod k)) ∧ j ∈ ({a, a + 1} : Finset (ZMod k)) := by
            rw [← hpair]; exact ⟨mem_insert_self _ _, mem_insert_of_mem (mem_singleton_self _)⟩
          simp only [mem_insert, mem_singleton] at hmem
          rcases hmem with ⟨rfl | rfl, rfl | rfl⟩
          · exact absurd rfl hij
          · rw [show x (r i) - x (r (i + 1)) = -(x (r (i + 1)) - x (r i)) by abel, inner_neg_left]
            exact neg_ne_zero.mpr ht
          · exact ht
          · exact absurd rfl hij
        · have hne : ⟪x (r i) - x (r j), u0⟫ ≠ 0 := by
            rw [inner_sub_left, sub_ne_zero]
            exact hinj i j hij hpair
          exact (h_open_ne (x (r i) - x (r j)) hne).mono fun _ h _ => h
    refine h_pairs.mono fun t ht i j hij => ?_
    by_contra hne
    apply ht i j hne
    dsimp at hij
    rw [inner_sub_left, hij, sub_self]
  have h_all : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      (∀ i, i ≠ a → ⟪F.N (tn i), u0 + t • (σ • e)⟫ < 0 ∧ 0 < ⟪F.N (tp i), u0 + t • (σ • e)⟫) ∧
      ⟪F.N (tn a), u0 + t • (σ • e)⟫ ≠ 0 ∧
      (∀ q ∈ s0x_S24 T, (∀ j, q ≠ r j) → ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
        x q = x (r a) + s • e + δ • (u0 + t • (σ • e))) ∧
      Function.Injective (fun i => ⟪x (r i), u0 + t • (σ • e)⟫) ∧
      UniOrSep (fun i => x (r i)) (u0 + t • (σ • e)) :=
    h_sg.and (h_ca.and (h_mid.and (h_inj.and hz)))
  obtain ⟨t, hsg_t, hca_t, hmid_t, hinj_t, hz_t⟩ := h_all.exists
  have hnu_t : ⟪F.N T, u0 + t • (σ • e)⟫ = 0 := by
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right, hnu, hNT_e, mul_zero,
      mul_zero, add_zero]
  exact faceChordView_of_rimCert hk F T (u0 + t • (σ • e)) r a tn tp sp hcert
    hnu_t hsg_t hca_t hmid_t hinj_t hz_t hfar

/-! ### (B1) tie-ray identity (Carbon A56) -/

/-- An edge `p q` of facets `a, b` is parallel to `cross (F.N a) (F.N b)`, so by BAC-CAB the Type II
ray `cross (F.N T) (x p - x q)` is a multiple of `⟪N_T,N_b⟫ N_a - ⟪N_T,N_a⟫ N_b`; division-free form. -/
theorem cross_normal_edge_eq {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (T a b : Fin 9) (p q : Fin 7)
    (hpa : p ∈ s0x_S24 a) (hqa : q ∈ s0x_S24 a) (hpb : p ∈ s0x_S24 b) (hqb : q ∈ s0x_S24 b) :
    ⟪cross (F.N a) (F.N b), cross (F.N a) (F.N b)⟫ • cross (F.N T) (x p - x q) =
      ⟪x p - x q, cross (F.N a) (F.N b)⟫ • (⟪F.N T, F.N b⟫ • F.N a - ⟪F.N T, F.N a⟫ • F.N b) := by
  set L := cross (F.N a) (F.N b)
  set d := x p - x q
  by_cases hL : L = 0
  · simp [L, hL]
  · have hNa_d : ⟪F.N a, d⟫ = 0 := by
      have := (F.hN a (x p) (x q)).symm
      rw [F.zero a p hpa, F.zero a q hqa, sub_self] at this
      exact this
    have hNb_d : ⟪F.N b, d⟫ = 0 := by
      have := (F.hN b (x p) (x q)).symm
      rw [F.zero b p hpb, F.zero b q hqb, sub_self] at this
      exact this
    have hL_Na : ⟪L, F.N a⟫ = 0 := inner_cross_left _ _
    have hL_Nb : ⟪L, F.N b⟫ = 0 := inner_cross_right _ _
    have hNa_Nb_cr : cross (F.N a) (F.N b) ≠ 0 := hL
    have hLd_cr : cross L d = 0 := by
      refine cross_eq_zero_of_perp2 hL_Na hL_Nb ?_ ?_ hNa_Nb_cr
      · rwa [real_inner_comm]
      · rwa [real_inner_comm]
    have hd_eq : d = (⟪d, L⟫ / ⟪L, L⟫) • L := eq_smul_of_cross_eq_zero hL hLd_cr
    have hLL_ne : ⟪L, L⟫ ≠ 0 := by
      rw [real_inner_self_eq_norm_sq]
      exact (sq_pos_of_pos (norm_pos_iff.mpr hL)).ne'
    have hd_mul : ⟪L, L⟫ • d = ⟪d, L⟫ • L := by
      conv_lhs => rw [hd_eq, smul_smul]
      rw [mul_div_cancel₀ _ hLL_ne]
    have h_baccab : cross (F.N T) L = ⟪F.N T, F.N b⟫ • F.N a - ⟪F.N T, F.N a⟫ • F.N b := by
      ext j
      fin_cases j <;> (simp only [L, cross, PiLp.inner_apply, Fin.sum_univ_three]; simp; ring)
    have hcr_smul : ⟪L, L⟫ • cross (F.N T) d = cross (F.N T) (⟪L, L⟫ • d) := by
      ext j
      fin_cases j <;> (simp only [cross]; simp; ring)
    rw [hcr_smul, hd_mul]
    have hcr_smul2 : cross (F.N T) (⟪d, L⟫ • L) = ⟪d, L⟫ • cross (F.N T) L := by
      ext j
      fin_cases j <;> (simp only [cross]; simp; ring)
    rw [hcr_smul2, h_baccab]

/-- Depths along `⟪N_T,N_b⟫ N_a - ⟪N_T,N_a⟫ N_b` relative to a vertex `q` of `a` and `b`. -/
theorem inner_tieRay {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (T a b : Fin 9) (q v : Fin 7)
    (hqa : q ∈ s0x_S24 a) (hqb : q ∈ s0x_S24 b) :
    ⟪x v - x q, ⟪F.N T, F.N b⟫ • F.N a - ⟪F.N T, F.N a⟫ • F.N b⟫ =
      ⟪F.N T, F.N b⟫ * F.f a (x v) - ⟪F.N T, F.N a⟫ * F.f b (x v) := by
  have ha : ⟪x v - x q, F.N a⟫ = F.f a (x v) := by
    rw [real_inner_comm]
    have := (F.hN a (x v) (x q)).symm
    rwa [F.zero a q hqa, sub_zero] at this
  have hb : ⟪x v - x q, F.N b⟫ = F.f b (x v) := by
    rw [real_inner_comm]
    have := (F.hN b (x v) (x q)).symm
    rwa [F.zero b q hqb, sub_zero] at this
  rw [inner_sub_right, real_inner_smul_right, real_inner_smul_right, ha, hb]

/-- **A56 tie ray II[236, x0 - x4].**  `cross (F.N 7) (x 0 - x 4)` is a nonzero multiple of
`u* = ⟪N7,N4⟫ N3 - ⟪N7,N3⟫ N4`, positive iff the configuration is positively oriented
(`0 < det3 (x 4 - x 0) (x 5 - x 0) (x 6 - x 0)`; this determinant is never 0). -/
theorem tieRay_236_04 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    ∃ c : ℝ, (0 < c ∧ 0 < det3 (x 4 - x 0) (x 5 - x 0) (x 6 - x 0) ∨
        c < 0 ∧ det3 (x 4 - x 0) (x 5 - x 0) (x 6 - x 0) < 0) ∧
      cross (F.N 7) (x 0 - x 4) = c • (⟪F.N 7, F.N 4⟫ • F.N 3 - ⟪F.N 7, F.N 3⟫ • F.N 4) := by
  set L34 := cross (F.N 3) (F.N 4)
  set e4 := x 4 - x 0
  set e5 := x 5 - x 0
  set e6 := x 6 - x 0
  have he4_ne : e4 ≠ 0 := by
    intro h0
    have h1 := F.zero 1 0 (by decide)
    have h2 := F.neg 1 4 (by decide)
    have heq : x 4 = x 0 := sub_eq_zero.mp h0
    rw [heq, h1] at h2
    exact lt_irrefl 0 h2
  have he4_pos : 0 < ⟪e4, e4⟫ := by
    rw [real_inner_self_eq_norm_sq]
    exact sq_pos_of_pos (norm_pos_iff.mpr he4_ne)
  have hN3_e4 : ⟪F.N 3, e4⟫ = 0 := by
    have := (F.hN 3 (x 4) (x 0)).symm
    rwa [F.zero 3 4 (by decide), F.zero 3 0 (by decide), sub_self] at this
  have hN4_e4 : ⟪F.N 4, e4⟫ = 0 := by
    have := (F.hN 4 (x 4) (x 0)).symm
    rwa [F.zero 4 4 (by decide), F.zero 4 0 (by decide), sub_self] at this
  have hN3_e5 : ⟪F.N 3, e5⟫ = 0 := by
    have := (F.hN 3 (x 5) (x 0)).symm
    rwa [F.zero 3 5 (by decide), F.zero 3 0 (by decide), sub_self] at this
  have hN4_e6 : ⟪F.N 4, e6⟫ = 0 := by
    have := (F.hN 4 (x 6) (x 0)).symm
    rwa [F.zero 4 6 (by decide), F.zero 4 0 (by decide), sub_self] at this
  have hN4_e5 : ⟪F.N 4, e5⟫ < 0 := by
    have := (F.hN 4 (x 5) (x 0)).symm
    rw [F.zero 4 0 (by decide), sub_zero] at this
    dsimp [e5]; rw [this]; exact F.neg 4 5 (by decide)
  have hN3_e6 : ⟪F.N 3, e6⟫ < 0 := by
    have := (F.hN 3 (x 6) (x 0)).symm
    rw [F.zero 3 0 (by decide), sub_zero] at this
    dsimp [e6]; rw [this]; exact F.neg 3 6 (by decide)
  have hdet_id : det3 e4 e5 e6 * ⟪e4, L34⟫ = - ⟪e4, e4⟫ * ⟪F.N 4, e5⟫ * ⟪F.N 3, e6⟫ := by
    have h_gen : ∀ v4 v5 v6 n3 n4 : ℝ³,
        det3 v4 v5 v6 * ⟪v4, cross n3 n4⟫ =
          ⟪v4, v4⟫ * (⟪n3, v5⟫ * ⟪n4, v6⟫ - ⟪n4, v5⟫ * ⟪n3, v6⟫) +
          ⟪v5, v4⟫ * (⟪n3, v6⟫ * ⟪n4, v4⟫ - ⟪n4, v6⟫ * ⟪n3, v4⟫) +
          ⟪v6, v4⟫ * (⟪n3, v4⟫ * ⟪n4, v5⟫ - ⟪n4, v4⟫ * ⟪n3, v5⟫) := by
      intro v4 v5 v6 n3 n4
      simp only [det3, cross, PiLp.inner_apply, Fin.sum_univ_three]
      simp
      ring
    rw [h_gen e4 e5 e6 (F.N 3) (F.N 4), hN3_e4, hN4_e4, hN3_e5, hN4_e6]
    ring
  have hdet_pos : 0 < det3 e4 e5 e6 * ⟪x 0 - x 4, L34⟫ := by
    have hneg : ⟪x 0 - x 4, L34⟫ = - ⟪e4, L34⟫ := by
      rw [show x 0 - x 4 = - e4 by dsimp [e4]; abel, inner_neg_left]
    rw [hneg, mul_neg, hdet_id]
    have : 0 < ⟪F.N 4, e5⟫ * ⟪F.N 3, e6⟫ := mul_pos_of_neg_of_neg hN4_e5 hN3_e6
    nlinarith
  have hL34_ne : L34 ≠ 0 := by
    intro h0
    rw [h0, inner_zero_right, mul_zero] at hdet_pos
    exact lt_irrefl 0 hdet_pos
  have hL34_pos : 0 < ⟪L34, L34⟫ := by
    rw [real_inner_self_eq_norm_sq]
    exact sq_pos_of_pos (norm_pos_iff.mpr hL34_ne)
  have hcr_eq := cross_normal_edge_eq F 7 3 4 0 4 (by decide) (by decide) (by decide) (by decide)
  set c := ⟪x 0 - x 4, L34⟫ / ⟪L34, L34⟫
  refine ⟨c, ?_, ?_⟩
  · have h_prod : 0 < det3 e4 e5 e6 * c := by
      dsimp [c]
      rw [← mul_div_assoc]
      exact div_pos hdet_pos hL34_pos
    rcases lt_trichotomy (det3 e4 e5 e6) 0 with hdn | hdz | hdp
    · refine Or.inr ⟨by nlinarith, hdn⟩
    · rw [hdz, zero_mul] at h_prod; exact absurd h_prod (lt_irrefl 0)
    · refine Or.inl ⟨by nlinarith, hdp⟩
  · have := congrArg (fun v : ℝ³ => (1 / ⟪L34, L34⟫) • v) hcr_eq
    rw [smul_smul, one_div_mul_cancel hL34_pos.ne', one_smul, smul_smul, one_div, mul_comm, ← div_eq_mul_inv] at this
    exact this

/-! ### (B2) chord middle by two facet signs (Carbon A56) -/

/-- **Chord middle by two facet signs.**  On the face circle of `T ∋ A, B, M`, with facets `FA ∋ A, M`,
`B ∉ FA` and `FB ∋ B, M`, `A ∉ FB`: `M` lies strictly over the chord `A B` iff `⟪N_FA,u⟫ ⟪N_FB,u⟫ > 0`. -/
theorem chord_middle_iff_facet_signs {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (u : ℝ³)
    (T FA FB : Fin 9) (A B M : Fin 7) (hAT : A ∈ s0x_S24 T) (hBT : B ∈ s0x_S24 T) (hMT : M ∈ s0x_S24 T)
    (hAA : A ∈ s0x_S24 FA) (hMA : M ∈ s0x_S24 FA) (hBA : B ∉ s0x_S24 FA)
    (hBB : B ∈ s0x_S24 FB) (hMB : M ∈ s0x_S24 FB) (hAB : A ∉ s0x_S24 FB)
    (hnu : ⟪F.N T, u⟫ = 0) :
    (∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧ x M = x A + s • (x B - x A) + δ • u) ↔
      0 < ⟪F.N FA, u⟫ * ⟪F.N FB, u⟫ := by
  constructor
  · rintro ⟨s, δ, hs, hs1, hδ, hx⟩
    have hMA_AB : x M - x A = s • (x B - x A) + δ • u := by rw [hx]; abel
    have hδu : δ • u = (1 - s) • (x M - x A) + s • (x M - x B) := by
      rw [show x M - x B = (x M - x A) - (x B - x A) by abel, hMA_AB]
      module
    have hFA_MA : ⟪F.N FA, x M - x A⟫ = 0 := by
      have := (F.hN FA (x M) (x A)).symm
      rwa [F.zero FA M hMA, F.zero FA A hAA, sub_self] at this
    have hFA_MB : ⟪F.N FA, x M - x B⟫ = - F.f FA (x B) := by
      have := (F.hN FA (x M) (x B)).symm
      rwa [F.zero FA M hMA, zero_sub] at this
    have hFB_MB : ⟪F.N FB, x M - x B⟫ = 0 := by
      have := (F.hN FB (x M) (x B)).symm
      rwa [F.zero FB M hMB, F.zero FB B hBB, sub_self] at this
    have hFB_MA : ⟪F.N FB, x M - x A⟫ = - F.f FB (x A) := by
      have := (F.hN FB (x M) (x A)).symm
      rwa [F.zero FB M hMB, zero_sub] at this
    have hFA_u : 0 < δ * ⟪F.N FA, u⟫ := by
      rw [← real_inner_smul_right, hδu, inner_add_right, real_inner_smul_right,
        real_inner_smul_right, hFA_MA, hFA_MB, mul_zero, zero_add]
      exact mul_pos hs (neg_pos.mpr (F.neg FA B hBA))
    have hFB_u : 0 < δ * ⟪F.N FB, u⟫ := by
      rw [← real_inner_smul_right, hδu, inner_add_right, real_inner_smul_right,
        real_inner_smul_right, hFB_MA, hFB_MB, mul_zero, add_zero]
      exact mul_pos (by linarith) (neg_pos.mpr (F.neg FB A hAB))
    have hmul : (δ * δ) * (⟪F.N FA, u⟫ * ⟪F.N FB, u⟫) = (δ * ⟪F.N FA, u⟫) * (δ * ⟪F.N FB, u⟫) := by ring
    have hpos : 0 < (δ * δ) * (⟪F.N FA, u⟫ * ⟪F.N FB, u⟫) := by
      rw [hmul]; exact mul_pos hFA_u hFB_u
    exact pos_of_mul_pos_right hpos (mul_self_nonneg δ)
  · intro h_signs
    have hFA_u_ne : ⟪F.N FA, u⟫ ≠ 0 := fun h0 => by rw [h0, zero_mul] at h_signs; exact lt_irrefl 0 h_signs
    have hFB_u_ne : ⟪F.N FB, u⟫ ≠ 0 := fun h0 => by rw [h0, mul_zero] at h_signs; exact lt_irrefl 0 h_signs
    have hu_ne : u ≠ 0 := fun h0 => by apply hFA_u_ne; rw [h0, inner_zero_right]
    have hu_pos : 0 < ⟪u, u⟫ := by
      rw [real_inner_self_eq_norm_sq]
      exact sq_pos_of_pos (norm_pos_iff.mpr hu_ne)
    have hNT_ne : F.N T ≠ 0 := by
      have hne_univ : ∃ y : Fin 7, y ∉ s0x_S24 T := by
        fin_cases T <;> first | exact ⟨0, by decide⟩ | exact ⟨3, by decide⟩ | exact ⟨1, by decide⟩
      obtain ⟨y, hy⟩ := hne_univ
      intro h0
      have := (F.hN T (x y) (x A)).symm
      rw [h0, inner_zero_left, F.zero T A hAT, sub_zero] at this
      have hy_neg := F.neg T y hy
      linarith
    have hNT_pos : 0 < ⟪F.N T, F.N T⟫ := by
      rw [real_inner_self_eq_norm_sq]
      exact sq_pos_of_pos (norm_pos_iff.mpr hNT_ne)
    set L := cross (F.N T) u
    have hLL_eq : ⟪L, L⟫ = ⟪F.N T, F.N T⟫ * ⟪u, u⟫ := by
      have hlag : ⟪L, L⟫ = ⟪F.N T, F.N T⟫ * ⟪u, u⟫ - ⟪F.N T, u⟫ ^ 2 := by
        simp only [L, cross, PiLp.inner_apply, Fin.sum_univ_three]
        simp
        ring
      rw [hlag, hnu, sq, mul_zero, sub_zero]
    have hLL_pos : 0 < ⟪L, L⟫ := by rw [hLL_eq]; exact mul_pos hNT_pos hu_pos
    have hL_ne : L ≠ 0 := fun h0 => by rw [h0, inner_zero_left] at hLL_pos; exact lt_irrefl 0 hLL_pos
    set e := x B - x A
    set d := x M - x A
    have hNT_e : ⟪F.N T, e⟫ = 0 := by
      have := (F.hN T (x B) (x A)).symm
      rwa [F.zero T B hBT, F.zero T A hAT, sub_self] at this
    have hNT_d : ⟪F.N T, d⟫ = 0 := by
      have := (F.hN T (x M) (x A)).symm
      rwa [F.zero T M hMT, F.zero T A hAT, sub_self] at this
    have h_basis : ∀ v : ℝ³, ⟪F.N T, v⟫ = 0 →
        v = (⟪v, u⟫ / ⟪u, u⟫) • u + (⟪v, L⟫ / ⟪L, L⟫) • L := by
      intro v hv
      set rem := v - ((⟪v, u⟫ / ⟪u, u⟫) • u + (⟪v, L⟫ / ⟪L, L⟫) • L)
      have hrem_NT : ⟪F.N T, rem⟫ = 0 := by
        dsimp [rem]
        rw [inner_sub_right, inner_add_right, real_inner_smul_right, real_inner_smul_right,
          hv, hnu, show ⟪F.N T, L⟫ = 0 from by rw [real_inner_comm]; exact inner_cross_left _ _,
          mul_zero, mul_zero, add_zero, sub_zero]
      have hrem_u : ⟪u, rem⟫ = 0 := by
        dsimp [rem]
        rw [inner_sub_right, inner_add_right, real_inner_smul_right, real_inner_smul_right,
          show ⟪u, L⟫ = ⟪L, u⟫ from real_inner_comm _ _, show ⟪L, u⟫ = 0 from inner_cross_right _ _,
          mul_zero, add_zero, real_inner_comm u v, div_mul_cancel₀ _ hu_pos.ne', sub_self]
      have hrem_L : ⟪L, rem⟫ = 0 := by
        dsimp [rem]
        rw [inner_sub_right, inner_add_right, real_inner_smul_right, real_inner_smul_right,
          show ⟪L, u⟫ = 0 from inner_cross_right _ _, mul_zero, zero_add,
          real_inner_comm L v, div_mul_cancel₀ _ hLL_pos.ne', sub_self]
      have hrem0 : rem = 0 := by
        by_contra hne
        have hNT_u_cr : cross (F.N T) u ≠ 0 := hL_ne
        have hcr : cross L rem = 0 := by
          refine cross_eq_zero_of_perp2 ?_ ?_ ?_ ?_ hNT_u_cr
          · exact inner_cross_left _ _
          · exact inner_cross_right _ _
          · rwa [real_inner_comm]
          · rwa [real_inner_comm]
        have hrem_smul : rem = (⟪rem, L⟫ / ⟪L, L⟫) • L := eq_smul_of_cross_eq_zero hL_ne hcr
        rw [real_inner_comm] at hrem_L
        rw [hrem_L, zero_div, zero_smul] at hrem_smul
        exact hne hrem_smul
      exact sub_eq_zero.mp hrem0
    have hd_decomp := h_basis d hNT_d
    have hed_NT : ⟪F.N T, e - d⟫ = 0 := by rw [inner_sub_right, hNT_e, hNT_d, sub_zero]
    have hed_decomp := h_basis (e - d) hed_NT
    set α1 := ⟪d, u⟫ / ⟪u, u⟫
    set β1 := ⟪d, L⟫ / ⟪L, L⟫
    set α2 := ⟪e - d, u⟫ / ⟪u, u⟫
    set β2 := ⟪e - d, L⟫ / ⟪L, L⟫
    have hFA_d : ⟪F.N FA, d⟫ = 0 := by
      have := (F.hN FA (x M) (x A)).symm
      rwa [F.zero FA M hMA, F.zero FA A hAA, sub_self] at this
    have hFB_ed : ⟪F.N FB, e - d⟫ = 0 := by
      have := (F.hN FB (x B) (x M)).symm
      rw [show x B - x M = e - d by dsimp [e, d]; abel, F.zero FB B hBB, F.zero FB M hMB, sub_self] at this
      exact this
    have hFA_e : ⟪F.N FA, e⟫ < 0 := by
      have := (F.hN FA (x B) (x A)).symm
      rw [F.zero FA A hAA, sub_zero] at this
      dsimp [e]; rw [this]; exact F.neg FA B hBA
    have hFB_e : 0 < ⟪F.N FB, e⟫ := by
      have := (F.hN FB (x B) (x A)).symm
      rw [F.zero FB B hBB, zero_sub] at this
      dsimp [e]; rw [this]; exact neg_pos.mpr (F.neg FB A hAB)
    have hFA_rel : α1 * ⟪F.N FA, u⟫ + β1 * ⟪F.N FA, L⟫ = 0 := by
      have := congrArg (fun v => ⟪F.N FA, v⟫) hd_decomp
      rw [inner_add_right, real_inner_smul_right, real_inner_smul_right] at this
      linarith
    have hFB_rel : α2 * ⟪F.N FB, u⟫ + β2 * ⟪F.N FB, L⟫ = 0 := by
      have := congrArg (fun v => ⟪F.N FB, v⟫) hed_decomp
      rw [inner_add_right, real_inner_smul_right, real_inner_smul_right] at this
      linarith
    have he_eq : e = (α1 + α2) • u + (β1 + β2) • L := by
      calc e = d + (e - d) := by abel
        _ = (α1 • u + β1 • L) + (α2 • u + β2 • L) := by rw [hed_decomp, hd_decomp]
        _ = (α1 + α2) • u + (β1 + β2) • L := by module
    have h_eq1 : β1 * ⟪F.N FA, e⟫ = -(α1 * β2 - β1 * α2) * ⟪F.N FA, u⟫ := by
      have h1 : ⟪F.N FA, e⟫ = (α1 + α2) * ⟪F.N FA, u⟫ + (β1 + β2) * ⟪F.N FA, L⟫ := by
        rw [he_eq, inner_add_right, real_inner_smul_right, real_inner_smul_right]
      rw [h1]
      linear_combination (β1 + β2) * hFA_rel
    have h_eq2 : β2 * ⟪F.N FB, e⟫ = (α1 * β2 - β1 * α2) * ⟪F.N FB, u⟫ := by
      have h2 : ⟪F.N FB, e⟫ = (α1 + α2) * ⟪F.N FB, u⟫ + (β1 + β2) * ⟪F.N FB, L⟫ := by
        rw [he_eq, inner_add_right, real_inner_smul_right, real_inner_smul_right]
      rw [h2]
      linear_combination (β1 + β2) * hFB_rel
    have hdet_ne : α1 * β2 - β1 * α2 ≠ 0 := by
      intro h0
      rw [h0, neg_zero, zero_mul] at h_eq1
      rcases mul_eq_zero.mp h_eq1 with hβ1 | hFA0
      · have hα1 : α1 = 0 := by
          rw [hβ1, zero_mul, add_zero] at hFA_rel
          exact (mul_eq_zero.mp hFA_rel).resolve_right hFA_u_ne
        have hd0 : d = 0 := by rw [hd_decomp, hα1, hβ1, zero_smul, zero_smul, add_zero]
        have hFB_d0 : ⟪F.N FB, d⟫ = 0 := by rw [hd0, inner_zero_right]
        have : ⟪F.N FB, e⟫ = 0 := by
          rw [show e = d + (e - d) by abel, inner_add_right, hFB_d0, hFB_ed, add_zero]
        linarith
      · exact hFA_e.ne hFA0
    have hβ12_pos : 0 < β1 * β2 := by
      have hmul_eq : (β1 * β2) * (⟪F.N FA, e⟫ * ⟪F.N FB, e⟫) =
          -(α1 * β2 - β1 * α2) ^ 2 * (⟪F.N FA, u⟫ * ⟪F.N FB, u⟫) := by
        linear_combination ⟪F.N FB, e⟫ * β2 * h_eq1 + (-(α1 * β2 - β1 * α2) * ⟪F.N FA, u⟫) * h_eq2
      have h_rhs_neg : -(α1 * β2 - β1 * α2) ^ 2 * (⟪F.N FA, u⟫ * ⟪F.N FB, u⟫) < 0 := by
        have hsq : 0 < (α1 * β2 - β1 * α2) ^ 2 := sq_pos_of_ne_zero hdet_ne
        nlinarith
      have h_fe_neg : ⟪F.N FA, e⟫ * ⟪F.N FB, e⟫ < 0 := mul_neg_of_neg_of_pos hFA_e hFB_e
      have h_lhs_neg : (β1 * β2) * (⟪F.N FA, e⟫ * ⟪F.N FB, e⟫) < 0 := by linarith
      exact pos_of_mul_neg_left h_lhs_neg h_fe_neg.le
    have hdL_edL_pos : 0 < ⟪d, L⟫ * ⟪e - d, L⟫ := by
      have h_mul : β1 * β2 = (⟪d, L⟫ * ⟪e - d, L⟫) / (⟪L, L⟫ * ⟪L, L⟫) := by
        dsimp [β1, β2]; ring
      rw [h_mul] at hβ12_pos
      have hL2 : 0 < ⟪L, L⟫ * ⟪L, L⟫ := mul_pos hLL_pos hLL_pos
      have hmul2 := mul_pos hβ12_pos hL2
      rwa [div_mul_cancel₀ _ hL2.ne'] at hmul2
    -- Solve `s = ⟪d, L⟫ / ⟪e, L⟫`
    have heL_split : ⟪e, L⟫ = ⟪d, L⟫ + ⟪e - d, L⟫ := by rw [← inner_add_left, add_sub_cancel]
    have hprod : 0 < ⟪d, L⟫ * (⟪e, L⟫ - ⟪d, L⟫) := by simpa [heL_split] using hdL_edL_pos
    have heL_ne : ⟪e, L⟫ ≠ 0 := by
      intro h0
      rw [h0, zero_sub, mul_neg] at hprod
      have : 0 ≤ ⟪d, L⟫ * ⟪d, L⟫ := mul_self_nonneg _
      linarith
    set s := ⟪d, L⟫ / ⟪e, L⟫
    have heL2_pos : 0 < ⟪e, L⟫ ^ 2 := sq_pos_of_ne_zero heL_ne
    have hs_prod : s * (1 - s) * ⟪e, L⟫ ^ 2 = ⟪d, L⟫ * (⟪e, L⟫ - ⟪d, L⟫) := by
      dsimp [s]; field_simp
    have hs01 : 0 < s * (1 - s) := pos_of_mul_pos_left (by linarith) heL2_pos.le
    have hs_pos : 0 < s := by
      by_contra hs_le
      push Not at hs_le
      by_cases h0 : s = 0
      · rw [h0, zero_mul] at hs01; exact lt_irrefl 0 hs01
      · have hs_neg : s < 0 := lt_of_le_of_ne hs_le h0
        have : s * (1 - s) < 0 := mul_neg_of_neg_of_pos hs_neg (by linarith)
        linarith
    have hs_lt : s < 1 := by
      by_contra h1_le
      push Not at h1_le
      have : s * (1 - s) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hs_pos.le (by linarith)
      linarith
    set D := d - s • e
    have hD_NT : ⟪F.N T, D⟫ = 0 := by
      dsimp [D]; rw [inner_sub_right, real_inner_smul_right, hNT_d, hNT_e, mul_zero, sub_zero]
    have hD_L : ⟪D, L⟫ = 0 := by
      dsimp [D, s]; rw [inner_sub_left, real_inner_smul_left]; field_simp; ring
    have hD_decomp := h_basis D hD_NT
    rw [hD_L, zero_div, zero_smul, add_zero] at hD_decomp
    set δ := ⟪D, u⟫ / ⟪u, u⟫
    have hδ_ne : δ ≠ 0 := by
      intro h0
      have hD0 : D = 0 := by rw [hD_decomp, h0, zero_smul]
      have hds : d = s • e := sub_eq_zero.mp hD0
      have : s * ⟪F.N FA, e⟫ = 0 := by
        rw [← real_inner_smul_right, ← hds, hFA_d]
      rcases mul_eq_zero.mp this with hs0 | hFA0
      · exact hs_pos.ne' hs0
      · exact hFA_e.ne hFA0
    refine ⟨s, δ, hs_pos, hs_lt, hδ_ne, ?_⟩
    have : x M = x A + d := by dsimp [d]; abel
    rw [this, show d = s • e + D by dsimp [D]; abel, hD_decomp]
    dsimp [e]; abel

/-- The chord is transversal to `u` when the two facet signs agree (used for the diagonal chord of C10). -/
theorem cross_ne_zero_of_facet_signs {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (u : ℝ³)
    (FA FB : Fin 9) (A B : Fin 7) (hAA : A ∈ s0x_S24 FA) (hBA : B ∉ s0x_S24 FA)
    (hBB : B ∈ s0x_S24 FB) (hAB : A ∉ s0x_S24 FB) (h : 0 < ⟪F.N FA, u⟫ * ⟪F.N FB, u⟫) :
    cross u (x B - x A) ≠ 0 := by
  intro hcr
  have he : x B - x A ≠ 0 := by
    intro h0
    have h1 := F.zero FA A hAA
    have h2 := F.neg FA B hBA
    have heq : x B = x A := sub_eq_zero.mp h0
    rw [heq, h1] at h2
    exact lt_irrefl 0 h2
  have hcr' : cross (x B - x A) u = 0 := by
    rw [show cross (x B - x A) u = - cross u (x B - x A) by
      ext j; fin_cases j <;> simp [cross] <;> ring, hcr, neg_zero]
  set k := ⟪u, x B - x A⟫ / ⟪x B - x A, x B - x A⟫
  have hk : u = k • (x B - x A) := eq_smul_of_cross_eq_zero he hcr'
  have hFA : ⟪F.N FA, u⟫ = k * F.f FA (x B) := by
    rw [hk, real_inner_smul_right]
    have := (F.hN FA (x B) (x A)).symm
    rw [F.zero FA A hAA, sub_zero] at this
    rw [this]
  have hFB : ⟪F.N FB, u⟫ = k * (- F.f FB (x A)) := by
    rw [hk, real_inner_smul_right]
    have := (F.hN FB (x B) (x A)).symm
    rw [F.zero FB B hBB, zero_sub] at this
    rw [this]
  rw [hFA, hFB] at h
  have hprod : ⟪F.N FA, u⟫ * ⟪F.N FB, u⟫ = (k * k) * (F.f FA (x B) * (- F.f FB (x A))) := by
    rw [hFA, hFB]; ring
  have hneg : F.f FA (x B) * (- F.f FB (x A)) < 0 :=
    mul_neg_of_neg_of_pos (F.neg FA B hBA) (neg_pos.mpr (F.neg FB A hAB))
  have hle : (k * k) * (F.f FA (x B) * (- F.f FB (x A))) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (mul_self_nonneg k) hneg.le
  linarith

/-! ### Type II views (C9, C10): the view is on the face circle -/

theorem inner_cross_typeII (n d : ℝ³) (ε : ℝ) : ⟪n, ε • cross n d⟫ = 0 := by
  rw [real_inner_smul_right, real_inner_comm, inner_cross_left, mul_zero]

/-! ### Per-case statements, base cases proved from the engines -/

def rimC6a : ZMod 4 → Fin 7 := ![0, 5, 2, 6]
def rimC6b : ZMod 4 → Fin 7 := ![0, 2, 6, 4]
def rimC7a : ZMod 4 → Fin 7 := ![0, 2, 3, 4]
def rimC7a' : ZMod 4 → Fin 7 := ![0, 6, 3, 5]
def rimC8 : ZMod 4 → Fin 7 := ![5, 2, 6, 3]
def rimC8' : ZMod 4 → Fin 7 := ![4, 6, 2, 3]
def rimC6c : ZMod 5 → Fin 7 := ![0, 4, 6, 2, 5]
def rimC6d : ZMod 5 → Fin 7 := ![0, 1, 2, 6, 4]
def rimC6d' : ZMod 5 → Fin 7 := ![0, 1, 6, 2, 5]
def rimC10 : ZMod 5 → Fin 7 := ![4, 6, 1, 2, 5]
def rimC10' : ZMod 5 → Fin 7 := ![5, 2, 1, 6, 4]
def tnC6a : ZMod 4 → Fin 9 := ![3, 6, 5, 4]
def tpC6a : ZMod 4 → Fin 9 := ![2, 2, 5, 1]
def spC6a : ZMod 4 → Fin 9 := ![0, 3, 0, 5]
def tnC6b : ZMod 4 → Fin 9 := ![2, 5, 8, 3]
def tpC6b : ZMod 4 → Fin 9 := ![0, 5, 4, 4]
def spC6b : ZMod 4 → Fin 9 := ![1, 0, 1, 8]
def tnC7a : ZMod 4 → Fin 9 := ![0, 6, 8, 4]
def tpC7a : ZMod 4 → Fin 9 := ![2, 6, 3, 3]
def spC7a : ZMod 4 → Fin 9 := ![1, 0, 6, 8]
def tnC7a' : ZMod 4 → Fin 9 := ![1, 8, 6, 2]
def tpC7a' : ZMod 4 → Fin 9 := ![4, 8, 3, 3]
def spC7a' : ZMod 4 → Fin 9 := ![0, 1, 7, 6]
def tnC8 : ZMod 4 → Fin 9 := ![2, 5, 8, 6]
def tpC8 : ZMod 4 → Fin 9 := ![6, 7, 7, 6]
def spC8 : ZMod 4 → Fin 9 := ![3, 0, 1, 7]
def tnC8' : ZMod 4 → Fin 9 := ![4, 5, 6, 8]
def tpC8' : ZMod 4 → Fin 9 := ![8, 7, 7, 8]
def spC8' : ZMod 4 → Fin 9 := ![3, 1, 0, 6]
def tnC6c : ZMod 5 → Fin 9 := ![3, 8, 5, 6, 3]
def tpC6c : ZMod 5 → Fin 9 := ![4, 4, 5, 2, 2]
def spC6c : ZMod 5 → Fin 9 := ![0, 3, 1, 0, 6]
def tnC6d : ZMod 5 → Fin 9 := ![0, 0, 5, 8, 3]
def tpC6d : ZMod 5 → Fin 9 := ![1, 5, 5, 4, 4]
def spC6d : ZMod 5 → Fin 9 := ![2, 1, 0, 1, 8]
def tnC6d' : ZMod 5 → Fin 9 := ![1, 1, 5, 6, 3]
def tpC6d' : ZMod 5 → Fin 9 := ![0, 5, 5, 2, 2]
def spC6d' : ZMod 5 → Fin 9 := ![2, 0, 1, 0, 6]
def tnC7b : ZMod 5 → Fin 9 := ![1, 5, 6, 8, 4]
def tpC7b : ZMod 5 → Fin 9 := ![0, 0, 6, 3, 3]
def spC7b : ZMod 5 → Fin 9 := ![2, 1, 0, 6, 8]
def tnC7b' : ZMod 5 → Fin 9 := ![0, 5, 8, 6, 2]
def tpC7b' : ZMod 5 → Fin 9 := ![1, 1, 8, 3, 3]
def spC7b' : ZMod 5 → Fin 9 := ![2, 0, 1, 7, 6]
def tnC9 : ZMod 5 → Fin 9 := ![0, 6, 3, 8, 1]
def tpC9 : ZMod 5 → Fin 9 := ![5, 6, 6, 7, 5]
def spC9 : ZMod 5 → Fin 9 := ![1, 0, 2, 3, 4]
def tnC9' : ZMod 5 → Fin 9 := ![1, 8, 3, 6, 0]
def tpC9' : ZMod 5 → Fin 9 := ![5, 8, 8, 7, 5]
def spC9' : ZMod 5 → Fin 9 := ![0, 1, 4, 3, 2]
def tnC10 : ZMod 5 → Fin 9 := ![4, 1, 0, 2, 3]
def tpC10 : ZMod 5 → Fin 9 := ![8, 5, 5, 6, 3]
def spC10 : ZMod 5 → Fin 9 := ![3, 4, 1, 0, 2]
def tnC10' : ZMod 5 → Fin 9 := ![2, 0, 1, 4, 3]
def tpC10' : ZMod 5 → Fin 9 := ![6, 5, 5, 8, 3]
def spC10' : ZMod 5 → Fin 9 := ![3, 2, 0, 1, 4]

theorem faceChordView_C6a {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hM1 : 0 < ⟪F.N 2, mer F 5 7⟫ ∧ ⟪F.N 4, mer F 5 7⟫ < 0 ∧ 0 < ⟪F.N 1, mer F 5 7⟫)
    (hM2 : 0 < ⟪x 3 - x 2, x 6 - x 2⟫ ∧ 0 < ⟪x 3 - x 6, x 2 - x 6⟫)
    (hguard : ⟪x 5 - x 0, mer F 5 7⟫ ≠ 0 ∨ ⟪x 5 - x 0, x 6 - x 2⟫ ≠ 0)
    (hlev : (⟪x 5 - x 2, mer F 5 7⟫ ≠ 0 ∨ ⟪x 0 - x 2, mer F 5 7⟫ ≠ 0) ∧
      (⟪x 5 - x 2, mer F 5 7⟫ ≠ 0 ∨
        ⟪x 5 - x 2, x 6 - x 2⟫ ≠ 0 ∧ ⟪x 5 - x 6, x 6 - x 2⟫ ≠ 0) ∧
      (⟪x 0 - x 2, mer F 5 7⟫ ≠ 0 ∨
        ⟪x 0 - x 2, x 6 - x 2⟫ ≠ 0 ∧ ⟪x 0 - x 6, x 6 - x 2⟫ ≠ 0))
    (hM4 :
      (F.f 7 (x 0) < F.f 7 (x 5) ∧
        (⟪F.N 7, cross (x 6 - x 2) (x 0 - x 2)⟫ ≠ 0 ∨ ⟪x 0 - x 2, x 6 - x 2⟫ < 0 ∨
          ⟪x 0 - x 6, x 2 - x 6⟫ < 0)) ∨
      (F.f 7 (x 5) < F.f 7 (x 0) ∧
        (⟪F.N 7, cross (x 6 - x 2) (x 5 - x 2)⟫ ≠ 0 ∨ ⟪x 5 - x 2, x 6 - x 2⟫ < 0 ∨
          ⟪x 5 - x 6, x 2 - x 6⟫ < 0))) :
    FaceChordView F 7 := by
  obtain ⟨hN2, hN4, hN1⟩ := hM1
  obtain ⟨m3a, m3b⟩ := hM2
  have hm : mer F 5 7 ≠ 0 := fun h => by rw [h, inner_zero_right] at hN2; exact lt_irrefl 0 hN2
  have hN5 : 0 < ⟪F.N 5, mer F 5 7⟫ := mer_source_pos F 5 7 hm
  obtain ⟨s3, d3, hs3, hs13, hd3, hx3⟩ := level_chord_middle F 5 7 2 6 3
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) m3a m3b
  have hN3 : ⟪F.N 3, mer F 5 7⟫ < 0 := by
    have := chord_middle_facet_sign F 3 5 (by decide) (by decide) (by decide) (by decide)
      (Or.inl (by decide)) hs3 hs13 hx3
    nlinarith
  have hN6 : ⟪F.N 6, mer F 5 7⟫ < 0 := by
    have := chord_middle_facet_sign F 6 5 (by decide) (by decide) (by decide) (by decide)
      (Or.inr (by decide)) hs3 hs13 hx3
    nlinarith
  refine faceChordView_mer4 F 5 7 rimC6a 2 tnC6a tpC6a spC6a (by decide) rfl
    (by decide) ?_ ?_ hguard hlev ?_
  · intro i hi
    fin_cases i
    · exact ⟨hN3, hN2⟩
    · exact ⟨hN6, hN2⟩
    · exact absurd rfl hi
    · exact ⟨hN4, hN1⟩
  · intro q hq hqr
    fin_cases q <;> first
      | exact absurd hq (by decide)
      | exact absurd rfl (hqr 2)
      | exact absurd rfl (hqr 3)
      | exact ⟨m3a, m3b⟩
  · rcases hM4 with ⟨hf0_0, hoff⟩ | ⟨hf1_0, hoff⟩
    · refine ⟨0, by decide, fun m hm hmr => ?_, hoff⟩
      fin_cases m <;> first | exact absurd rfl hm | exact absurd hmr (by decide) | exact hf0_0
    · refine ⟨1, by decide, fun m hm hmr => ?_, hoff⟩
      fin_cases m <;> first | exact absurd rfl hm | exact absurd hmr (by decide) | exact hf1_0

theorem faceChordView_C6b {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hM1 : ⟪F.N 2, mer F 5 7⟫ < 0 ∧ 0 < ⟪F.N 0, mer F 5 7⟫ ∧ 0 < ⟪F.N 4, mer F 5 7⟫)
    (hM2 : 0 < ⟪x 3 - x 2, x 6 - x 2⟫ ∧ 0 < ⟪x 3 - x 6, x 2 - x 6⟫)
    (hguard : ⟪x 0 - x 4, mer F 5 7⟫ ≠ 0 ∨ ⟪x 0 - x 4, x 6 - x 2⟫ ≠ 0)
    (hlev : (⟪x 0 - x 2, mer F 5 7⟫ ≠ 0 ∨ ⟪x 4 - x 2, mer F 5 7⟫ ≠ 0) ∧
      (⟪x 0 - x 2, mer F 5 7⟫ ≠ 0 ∨
        ⟪x 0 - x 2, x 6 - x 2⟫ ≠ 0 ∧ ⟪x 0 - x 6, x 6 - x 2⟫ ≠ 0) ∧
      (⟪x 4 - x 2, mer F 5 7⟫ ≠ 0 ∨
        ⟪x 4 - x 2, x 6 - x 2⟫ ≠ 0 ∧ ⟪x 4 - x 6, x 6 - x 2⟫ ≠ 0))
    (hM4 :
      (F.f 7 (x 0) < F.f 7 (x 4) ∧
        (⟪F.N 7, cross (x 6 - x 2) (x 0 - x 2)⟫ ≠ 0 ∨ ⟪x 0 - x 2, x 6 - x 2⟫ < 0 ∨
          ⟪x 0 - x 6, x 2 - x 6⟫ < 0)) ∨
      (F.f 7 (x 4) < F.f 7 (x 0) ∧
        (⟪F.N 7, cross (x 6 - x 2) (x 4 - x 2)⟫ ≠ 0 ∨ ⟪x 4 - x 2, x 6 - x 2⟫ < 0 ∨
          ⟪x 4 - x 6, x 2 - x 6⟫ < 0))) :
    FaceChordView F 7 := by
  obtain ⟨hN2, hN0, hN4⟩ := hM1
  obtain ⟨m3a, m3b⟩ := hM2
  have hm : mer F 5 7 ≠ 0 := fun h => by rw [h, inner_zero_right] at hN2; exact lt_irrefl 0 hN2
  have hN5 : 0 < ⟪F.N 5, mer F 5 7⟫ := mer_source_pos F 5 7 hm
  obtain ⟨s3, d3, hs3, hs13, hd3, hx3⟩ := level_chord_middle F 5 7 2 6 3
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) m3a m3b
  have hN8 : ⟪F.N 8, mer F 5 7⟫ < 0 := by
    have := chord_middle_facet_sign F 8 5 (by decide) (by decide) (by decide) (by decide)
      (Or.inl (by decide)) hs3 hs13 hx3
    nlinarith
  have hN3 : ⟪F.N 3, mer F 5 7⟫ < 0 := by
    have := chord_middle_facet_sign F 3 5 (by decide) (by decide) (by decide) (by decide)
      (Or.inl (by decide)) hs3 hs13 hx3
    nlinarith
  refine faceChordView_mer4 F 5 7 rimC6b 1 tnC6b tpC6b spC6b (by decide) rfl
    (by decide) ?_ ?_ hguard hlev ?_
  · intro i hi
    fin_cases i
    · exact ⟨hN2, hN0⟩
    · exact absurd rfl hi
    · exact ⟨hN8, hN4⟩
    · exact ⟨hN3, hN4⟩
  · intro q hq hqr
    fin_cases q <;> first
      | exact absurd hq (by decide)
      | exact absurd rfl (hqr 1)
      | exact absurd rfl (hqr 2)
      | exact ⟨m3a, m3b⟩
  · rcases hM4 with ⟨hf0_0, hoff⟩ | ⟨hf1_0, hoff⟩
    · refine ⟨0, by decide, fun m hm hmr => ?_, hoff⟩
      fin_cases m <;> first | exact absurd rfl hm | exact absurd hmr (by decide) | exact hf0_0
    · refine ⟨3, by decide, fun m hm hmr => ?_, hoff⟩
      fin_cases m <;> first | exact absurd rfl hm | exact absurd hmr (by decide) | exact hf1_0

theorem faceChordView_C7a {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hM1 : 0 < ⟪F.N 2, mer F 6 7⟫ ∧ 0 < ⟪F.N 3, mer F 6 7⟫ ∧
      ⟪F.N 0, mer F 6 7⟫ < 0 ∧ ⟪F.N 4, mer F 6 7⟫ < 0)
    (hM2 : 0 < ⟪x 6 - x 2, x 3 - x 2⟫ ∧ 0 < ⟪x 6 - x 3, x 2 - x 3⟫)
    (hguard : ⟪x 0 - x 4, mer F 6 7⟫ ≠ 0 ∨ ⟪x 0 - x 4, x 3 - x 2⟫ ≠ 0)
    (hlev : (⟪x 0 - x 2, mer F 6 7⟫ ≠ 0 ∨ ⟪x 4 - x 2, mer F 6 7⟫ ≠ 0) ∧
      (⟪x 0 - x 2, mer F 6 7⟫ ≠ 0 ∨
        ⟪x 0 - x 2, x 3 - x 2⟫ ≠ 0 ∧ ⟪x 0 - x 3, x 3 - x 2⟫ ≠ 0) ∧
      (⟪x 4 - x 2, mer F 6 7⟫ ≠ 0 ∨
        ⟪x 4 - x 2, x 3 - x 2⟫ ≠ 0 ∧ ⟪x 4 - x 3, x 3 - x 2⟫ ≠ 0))
    (hM4 :
      (F.f 7 (x 0) < F.f 7 (x 4) ∧
        (⟪F.N 7, cross (x 3 - x 2) (x 0 - x 2)⟫ ≠ 0 ∨ ⟪x 0 - x 2, x 3 - x 2⟫ < 0 ∨
          ⟪x 0 - x 3, x 2 - x 3⟫ < 0)) ∨
      (F.f 7 (x 4) < F.f 7 (x 0) ∧
        (⟪F.N 7, cross (x 3 - x 2) (x 4 - x 2)⟫ ≠ 0 ∨ ⟪x 4 - x 2, x 3 - x 2⟫ < 0 ∨
          ⟪x 4 - x 3, x 2 - x 3⟫ < 0))) :
    FaceChordView F 7 := by
  obtain ⟨hN2, hN3, hN0, hN4⟩ := hM1
  obtain ⟨m6a, m6b⟩ := hM2
  have hm : mer F 6 7 ≠ 0 := fun h => by rw [h, inner_zero_right] at hN2; exact lt_irrefl 0 hN2
  have hN6 : 0 < ⟪F.N 6, mer F 6 7⟫ := mer_source_pos F 6 7 hm
  obtain ⟨s6, d6, hs6, hs16, hd6, hx6⟩ := level_chord_middle F 6 7 2 3 6
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) m6a m6b
  have hN8 : ⟪F.N 8, mer F 6 7⟫ < 0 := by
    have := chord_middle_facet_sign F 8 6 (by decide) (by decide) (by decide) (by decide)
      (Or.inl (by decide)) hs6 hs16 hx6
    nlinarith
  refine faceChordView_mer4 F 6 7 rimC7a 1 tnC7a tpC7a spC7a (by decide) rfl
    (by decide) ?_ ?_ hguard hlev ?_
  · intro i hi
    fin_cases i
    · exact ⟨hN0, hN2⟩
    · exact absurd rfl hi
    · exact ⟨hN8, hN3⟩
    · exact ⟨hN4, hN3⟩
  · intro q hq hqr
    fin_cases q <;> first
      | exact absurd hq (by decide)
      | exact absurd rfl (hqr 1)
      | exact absurd rfl (hqr 2)
      | exact ⟨m6a, m6b⟩
  · rcases hM4 with ⟨hf0_0, hoff⟩ | ⟨hf1_0, hoff⟩
    · refine ⟨0, by decide, fun m hm hmr => ?_, hoff⟩
      fin_cases m <;> first | exact absurd rfl hm | exact absurd hmr (by decide) | exact hf0_0
    · refine ⟨3, by decide, fun m hm hmr => ?_, hoff⟩
      fin_cases m <;> first | exact absurd rfl hm | exact absurd hmr (by decide) | exact hf1_0

theorem faceChordView_C7a' {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hM1 : 0 < ⟪F.N 4, mer F 8 7⟫ ∧ 0 < ⟪F.N 3, mer F 8 7⟫ ∧
      ⟪F.N 1, mer F 8 7⟫ < 0 ∧ ⟪F.N 2, mer F 8 7⟫ < 0)
    (hM2 : 0 < ⟪x 2 - x 6, x 3 - x 6⟫ ∧ 0 < ⟪x 2 - x 3, x 6 - x 3⟫)
    (hguard : ⟪x 0 - x 5, mer F 8 7⟫ ≠ 0 ∨ ⟪x 0 - x 5, x 3 - x 6⟫ ≠ 0)
    (hlev : (⟪x 0 - x 6, mer F 8 7⟫ ≠ 0 ∨ ⟪x 5 - x 6, mer F 8 7⟫ ≠ 0) ∧
      (⟪x 0 - x 6, mer F 8 7⟫ ≠ 0 ∨
        ⟪x 0 - x 6, x 3 - x 6⟫ ≠ 0 ∧ ⟪x 0 - x 3, x 3 - x 6⟫ ≠ 0) ∧
      (⟪x 5 - x 6, mer F 8 7⟫ ≠ 0 ∨
        ⟪x 5 - x 6, x 3 - x 6⟫ ≠ 0 ∧ ⟪x 5 - x 3, x 3 - x 6⟫ ≠ 0))
    (hM4 :
      (F.f 7 (x 0) < F.f 7 (x 5) ∧
        (⟪F.N 7, cross (x 3 - x 6) (x 0 - x 6)⟫ ≠ 0 ∨ ⟪x 0 - x 6, x 3 - x 6⟫ < 0 ∨
          ⟪x 0 - x 3, x 6 - x 3⟫ < 0)) ∨
      (F.f 7 (x 5) < F.f 7 (x 0) ∧
        (⟪F.N 7, cross (x 3 - x 6) (x 5 - x 6)⟫ ≠ 0 ∨ ⟪x 5 - x 6, x 3 - x 6⟫ < 0 ∨
          ⟪x 5 - x 3, x 6 - x 3⟫ < 0))) :
    FaceChordView F 7 := by
  exact faceChordView_sym F (faceChordView_C7a (sym24 F) (x := x ∘ pi24) hM1 hM2 hguard hlev hM4)

theorem faceChordView_C8 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hM1 : 0 < ⟪F.N 7, mer F 6 3⟫ ∧ ⟪F.N 5, mer F 6 3⟫ < 0)
    (hM2 : 0 < ⟪x 0 - x 3, x 5 - x 3⟫ ∧ 0 < ⟪x 0 - x 5, x 3 - x 5⟫ ∧
      0 < ⟪x 4 - x 3, x 5 - x 3⟫ ∧ 0 < ⟪x 4 - x 5, x 3 - x 5⟫)
    (hguard : ⟪x 6 - x 2, mer F 6 3⟫ ≠ 0 ∨ ⟪x 6 - x 2, x 5 - x 3⟫ ≠ 0)
    (hlev : (⟪x 6 - x 3, mer F 6 3⟫ ≠ 0 ∨ ⟪x 2 - x 3, mer F 6 3⟫ ≠ 0) ∧
      (⟪x 6 - x 3, mer F 6 3⟫ ≠ 0 ∨
        ⟪x 6 - x 3, x 5 - x 3⟫ ≠ 0 ∧ ⟪x 6 - x 5, x 5 - x 3⟫ ≠ 0) ∧
      (⟪x 2 - x 3, mer F 6 3⟫ ≠ 0 ∨
        ⟪x 2 - x 3, x 5 - x 3⟫ ≠ 0 ∧ ⟪x 2 - x 5, x 5 - x 3⟫ ≠ 0))
    (hM4 :
      (F.f 3 (x 2) < F.f 3 (x 6) ∧
        (⟪F.N 3, cross (x 5 - x 3) (x 2 - x 3)⟫ ≠ 0 ∨ ⟪x 2 - x 3, x 5 - x 3⟫ < 0 ∨
          ⟪x 2 - x 5, x 3 - x 5⟫ < 0)) ∨
      (F.f 3 (x 6) < F.f 3 (x 2) ∧
        (⟪F.N 3, cross (x 5 - x 3) (x 6 - x 3)⟫ ≠ 0 ∨ ⟪x 6 - x 3, x 5 - x 3⟫ < 0 ∨
          ⟪x 6 - x 5, x 3 - x 5⟫ < 0))) :
    FaceChordView F 3 := by
  obtain ⟨hN7, hN5⟩ := hM1
  obtain ⟨m0a, m0b, m4a, m4b⟩ := hM2
  have hm : mer F 6 3 ≠ 0 := fun h => by rw [h, inner_zero_right] at hN7; exact lt_irrefl 0 hN7
  have hN6 : 0 < ⟪F.N 6, mer F 6 3⟫ := mer_source_pos F 6 3 hm
  obtain ⟨s0, d0, hs0, hs10, hd0, hx0⟩ := level_chord_middle F 6 3 3 5 0
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) m0a m0b
  obtain ⟨s4, d4, hs4, hs14, hd4, hx4⟩ := level_chord_middle F 6 3 3 5 4
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) m4a m4b
  have hN2 : ⟪F.N 2, mer F 6 3⟫ < 0 := by
    have := chord_middle_facet_sign F 2 6 (by decide) (by decide) (by decide) (by decide)
      (Or.inl (by decide)) hs0 hs10 hx0
    nlinarith
  have hN8 : ⟪F.N 8, mer F 6 3⟫ < 0 := by
    have := chord_middle_facet_sign F 8 6 (by decide) (by decide) (by decide) (by decide)
      (Or.inr (by decide)) hs4 hs14 hx4
    nlinarith
  refine faceChordView_mer4 F 6 3 rimC8 3 tnC8 tpC8 spC8 (by decide) rfl
    (by decide) ?_ ?_ hguard hlev ?_
  · intro i hi
    fin_cases i
    · exact ⟨hN2, hN6⟩
    · exact ⟨hN5, hN7⟩
    · exact ⟨hN8, hN7⟩
    · exact absurd rfl hi
  · intro q hq hqr
    fin_cases q <;> first
      | exact absurd hq (by decide)
      | exact absurd rfl (hqr 0)
      | exact absurd rfl (hqr 3)
      | exact ⟨m0a, m0b⟩
      | exact ⟨m4a, m4b⟩
  · rcases hM4 with ⟨hf0_0, hoff⟩ | ⟨hf1_0, hoff⟩
    · refine ⟨1, by decide, fun m hm hmr => ?_, hoff⟩
      fin_cases m <;> first | exact absurd rfl hm | exact absurd hmr (by decide) | exact hf0_0
    · refine ⟨2, by decide, fun m hm hmr => ?_, hoff⟩
      fin_cases m <;> first | exact absurd rfl hm | exact absurd hmr (by decide) | exact hf1_0

theorem faceChordView_C8' {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hM1 : 0 < ⟪F.N 7, mer F 8 3⟫ ∧ ⟪F.N 5, mer F 8 3⟫ < 0)
    (hM2 : 0 < ⟪x 0 - x 3, x 4 - x 3⟫ ∧ 0 < ⟪x 0 - x 4, x 3 - x 4⟫ ∧
      0 < ⟪x 5 - x 3, x 4 - x 3⟫ ∧ 0 < ⟪x 5 - x 4, x 3 - x 4⟫)
    (hguard : ⟪x 2 - x 6, mer F 8 3⟫ ≠ 0 ∨ ⟪x 2 - x 6, x 4 - x 3⟫ ≠ 0)
    (hlev : (⟪x 2 - x 3, mer F 8 3⟫ ≠ 0 ∨ ⟪x 6 - x 3, mer F 8 3⟫ ≠ 0) ∧
      (⟪x 2 - x 3, mer F 8 3⟫ ≠ 0 ∨
        ⟪x 2 - x 3, x 4 - x 3⟫ ≠ 0 ∧ ⟪x 2 - x 4, x 4 - x 3⟫ ≠ 0) ∧
      (⟪x 6 - x 3, mer F 8 3⟫ ≠ 0 ∨
        ⟪x 6 - x 3, x 4 - x 3⟫ ≠ 0 ∧ ⟪x 6 - x 4, x 4 - x 3⟫ ≠ 0))
    (hM4 :
      (F.f 3 (x 6) < F.f 3 (x 2) ∧
        (⟪F.N 3, cross (x 4 - x 3) (x 6 - x 3)⟫ ≠ 0 ∨ ⟪x 6 - x 3, x 4 - x 3⟫ < 0 ∨
          ⟪x 6 - x 4, x 3 - x 4⟫ < 0)) ∨
      (F.f 3 (x 2) < F.f 3 (x 6) ∧
        (⟪F.N 3, cross (x 4 - x 3) (x 2 - x 3)⟫ ≠ 0 ∨ ⟪x 2 - x 3, x 4 - x 3⟫ < 0 ∨
          ⟪x 2 - x 4, x 3 - x 4⟫ < 0))) :
    FaceChordView F 3 := by
  exact faceChordView_sym F (faceChordView_C8 (sym24 F) (x := x ∘ pi24) hM1 hM2 hguard hlev hM4)

theorem faceChordView_C6c {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hM1 : 0 < ⟪F.N 4, mer F 5 7⟫ ∧ 0 < ⟪F.N 2, mer F 5 7⟫)
    (hM2 : 0 < ⟪x 3 - x 6, x 2 - x 6⟫ ∧ 0 < ⟪x 3 - x 2, x 6 - x 2⟫)
    (hinj : ∀ i j : ZMod 5, i ≠ j → ({i, j} : Finset (ZMod 5)) ≠ {2, 3} →
      ⟪x (rimC6c i), mer F 5 7⟫ ≠ ⟪x (rimC6c j), mer F 5 7⟫)
    (hz : ∃ σ : ℝ, σ ≠ 0 ∧ ∀ᶠ t in 𝓝[>] (0 : ℝ),
      UniOrSep (fun i : ZMod 5 => x (rimC6c i)) (mer F 5 7 + t • (σ • (x 2 - x 6))))
    (hM4 :
      (F.f 7 (x 0) < F.f 7 (x 4) ∧ F.f 7 (x 0) < F.f 7 (x 5) ∧
        (⟪F.N 7, cross (x 2 - x 6) (x 0 - x 6)⟫ ≠ 0 ∨ ⟪x 0 - x 6, x 2 - x 6⟫ < 0 ∨
          ⟪x 0 - x 2, x 6 - x 2⟫ < 0)) ∨
      (F.f 7 (x 4) < F.f 7 (x 0) ∧ F.f 7 (x 4) < F.f 7 (x 5) ∧
        (⟪F.N 7, cross (x 2 - x 6) (x 4 - x 6)⟫ ≠ 0 ∨ ⟪x 4 - x 6, x 2 - x 6⟫ < 0 ∨
          ⟪x 4 - x 2, x 6 - x 2⟫ < 0)) ∨
      (F.f 7 (x 5) < F.f 7 (x 0) ∧ F.f 7 (x 5) < F.f 7 (x 4) ∧
        (⟪F.N 7, cross (x 2 - x 6) (x 5 - x 6)⟫ ≠ 0 ∨ ⟪x 5 - x 6, x 2 - x 6⟫ < 0 ∨
          ⟪x 5 - x 2, x 6 - x 2⟫ < 0))) :
    FaceChordView F 7 := by
  obtain ⟨hN4, hN2⟩ := hM1
  obtain ⟨m3a, m3b⟩ := hM2
  have hm : mer F 5 7 ≠ 0 := fun h => by rw [h, inner_zero_right] at hN4; exact lt_irrefl 0 hN4
  have hN5 : 0 < ⟪F.N 5, mer F 5 7⟫ := mer_source_pos F 5 7 hm
  obtain ⟨s3, d3, hs3, hs13, hd3, hx3⟩ := level_chord_middle F 5 7 6 2 3
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) m3a m3b
  have hN3 : ⟪F.N 3, mer F 5 7⟫ < 0 := by
    have := chord_middle_facet_sign F 3 5 (by decide) (by decide) (by decide) (by decide)
      (Or.inl (by decide)) hs3 hs13 hx3
    nlinarith
  have hN8 : ⟪F.N 8, mer F 5 7⟫ < 0 := by
    have := chord_middle_facet_sign F 8 5 (by decide) (by decide) (by decide) (by decide)
      (Or.inr (by decide)) hs3 hs13 hx3
    nlinarith
  have hN6 : ⟪F.N 6, mer F 5 7⟫ < 0 := by
    have := chord_middle_facet_sign F 6 5 (by decide) (by decide) (by decide) (by decide)
      (Or.inl (by decide)) hs3 hs13 hx3
    nlinarith
  obtain ⟨σ, hσ, hzσ⟩ := hz
  refine faceChordView_of_rimCert_slide (k := 5) (by norm_num) F 7 (mer F 5 7) σ rimC6c 2 tnC6c tpC6c spC6c
    (by decide) (mer_inner_facet F 5 7) ?_ hN5.ne' ?_ hinj hσ hzσ ?_
  · intro i hi
    fin_cases i
    · exact ⟨hN3, hN4⟩
    · exact ⟨hN8, hN4⟩
    · exact absurd rfl hi
    · exact ⟨hN6, hN2⟩
    · exact ⟨hN3, hN2⟩
  · intro q hq hqr
    fin_cases q <;> first
      | exact absurd hq (by decide)
      | exact absurd rfl (hqr 2)
      | exact absurd rfl (hqr 3)
      | exact ⟨s3, d3, hs3, hs13, hd3, hx3⟩
  · rcases hM4 with ⟨hf0_0, hf0_1, hoff⟩ | ⟨hf1_0, hf1_1, hoff⟩ | ⟨hf2_0, hf2_1, hoff⟩
    · refine ⟨0, by decide, fun m hm hmr => ?_, hoff⟩
      fin_cases m <;> first | exact absurd rfl hm | exact absurd hmr (by decide) | exact hf0_0 | exact hf0_1
    · refine ⟨1, by decide, fun m hm hmr => ?_, hoff⟩
      fin_cases m <;> first | exact absurd rfl hm | exact absurd hmr (by decide) | exact hf1_0 | exact hf1_1
    · refine ⟨4, by decide, fun m hm hmr => ?_, hoff⟩
      fin_cases m <;> first | exact absurd rfl hm | exact absurd hmr (by decide) | exact hf2_0 | exact hf2_1

theorem faceChordView_C6d {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hM1 : ⟪F.N 0, mer F 5 7⟫ < 0 ∧ 0 < ⟪F.N 1, mer F 5 7⟫ ∧ 0 < ⟪F.N 4, mer F 5 7⟫)
    (hM2 : 0 < ⟪x 3 - x 2, x 6 - x 2⟫ ∧ 0 < ⟪x 3 - x 6, x 2 - x 6⟫)
    (hinj : ∀ i j : ZMod 5, i ≠ j → ({i, j} : Finset (ZMod 5)) ≠ {2, 3} →
      ⟪x (rimC6d i), mer F 5 7⟫ ≠ ⟪x (rimC6d j), mer F 5 7⟫)
    (hz : ∃ σ : ℝ, σ ≠ 0 ∧ ∀ᶠ t in 𝓝[>] (0 : ℝ),
      UniOrSep (fun i : ZMod 5 => x (rimC6d i)) (mer F 5 7 + t • (σ • (x 6 - x 2))))
    (hM4 :
      (F.f 7 (x 0) < F.f 7 (x 1) ∧ F.f 7 (x 0) < F.f 7 (x 4) ∧
        (⟪F.N 7, cross (x 6 - x 2) (x 0 - x 2)⟫ ≠ 0 ∨ ⟪x 0 - x 2, x 6 - x 2⟫ < 0 ∨
          ⟪x 0 - x 6, x 2 - x 6⟫ < 0)) ∨
      (F.f 7 (x 1) < F.f 7 (x 0) ∧ F.f 7 (x 1) < F.f 7 (x 4) ∧
        (⟪F.N 7, cross (x 6 - x 2) (x 1 - x 2)⟫ ≠ 0 ∨ ⟪x 1 - x 2, x 6 - x 2⟫ < 0 ∨
          ⟪x 1 - x 6, x 2 - x 6⟫ < 0)) ∨
      (F.f 7 (x 4) < F.f 7 (x 0) ∧ F.f 7 (x 4) < F.f 7 (x 1) ∧
        (⟪F.N 7, cross (x 6 - x 2) (x 4 - x 2)⟫ ≠ 0 ∨ ⟪x 4 - x 2, x 6 - x 2⟫ < 0 ∨
          ⟪x 4 - x 6, x 2 - x 6⟫ < 0))) :
    FaceChordView F 7 := by
  obtain ⟨hN0, hN1, hN4⟩ := hM1
  obtain ⟨m3a, m3b⟩ := hM2
  have hm : mer F 5 7 ≠ 0 := fun h => by rw [h, inner_zero_right] at hN0; exact lt_irrefl 0 hN0
  have hN5 : 0 < ⟪F.N 5, mer F 5 7⟫ := mer_source_pos F 5 7 hm
  obtain ⟨s3, d3, hs3, hs13, hd3, hx3⟩ := level_chord_middle F 5 7 2 6 3
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) m3a m3b
  have hN8 : ⟪F.N 8, mer F 5 7⟫ < 0 := by
    have := chord_middle_facet_sign F 8 5 (by decide) (by decide) (by decide) (by decide)
      (Or.inl (by decide)) hs3 hs13 hx3
    nlinarith
  have hN3 : ⟪F.N 3, mer F 5 7⟫ < 0 := by
    have := chord_middle_facet_sign F 3 5 (by decide) (by decide) (by decide) (by decide)
      (Or.inl (by decide)) hs3 hs13 hx3
    nlinarith
  obtain ⟨σ, hσ, hzσ⟩ := hz
  refine faceChordView_of_rimCert_slide (k := 5) (by norm_num) F 7 (mer F 5 7) σ rimC6d 2 tnC6d tpC6d spC6d
    (by decide) (mer_inner_facet F 5 7) ?_ hN5.ne' ?_ hinj hσ hzσ ?_
  · intro i hi
    fin_cases i
    · exact ⟨hN0, hN1⟩
    · exact ⟨hN0, hN5⟩
    · exact absurd rfl hi
    · exact ⟨hN8, hN4⟩
    · exact ⟨hN3, hN4⟩
  · intro q hq hqr
    fin_cases q <;> first
      | exact absurd hq (by decide)
      | exact absurd rfl (hqr 2)
      | exact absurd rfl (hqr 3)
      | exact ⟨s3, d3, hs3, hs13, hd3, hx3⟩
  · rcases hM4 with ⟨hf0_0, hf0_1, hoff⟩ | ⟨hf1_0, hf1_1, hoff⟩ | ⟨hf2_0, hf2_1, hoff⟩
    · refine ⟨0, by decide, fun m hm hmr => ?_, hoff⟩
      fin_cases m <;> first | exact absurd rfl hm | exact absurd hmr (by decide) | exact hf0_0 | exact hf0_1
    · refine ⟨1, by decide, fun m hm hmr => ?_, hoff⟩
      fin_cases m <;> first | exact absurd rfl hm | exact absurd hmr (by decide) | exact hf1_0 | exact hf1_1
    · refine ⟨4, by decide, fun m hm hmr => ?_, hoff⟩
      fin_cases m <;> first | exact absurd rfl hm | exact absurd hmr (by decide) | exact hf2_0 | exact hf2_1

theorem faceChordView_C6d' {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hM1 : ⟪F.N 1, mer F 5 7⟫ < 0 ∧ 0 < ⟪F.N 0, mer F 5 7⟫ ∧ 0 < ⟪F.N 2, mer F 5 7⟫)
    (hM2 : 0 < ⟪x 3 - x 6, x 2 - x 6⟫ ∧ 0 < ⟪x 3 - x 2, x 6 - x 2⟫)
    (hinj : ∀ i j : ZMod 5, i ≠ j → ({i, j} : Finset (ZMod 5)) ≠ {2, 3} →
      ⟪x (rimC6d' i), mer F 5 7⟫ ≠ ⟪x (rimC6d' j), mer F 5 7⟫)
    (hz : ∃ σ : ℝ, σ ≠ 0 ∧ ∀ᶠ t in 𝓝[>] (0 : ℝ),
      UniOrSep (fun i : ZMod 5 => x (rimC6d' i)) (mer F 5 7 + t • (σ • (x 2 - x 6))))
    (hM4 :
      (F.f 7 (x 0) < F.f 7 (x 1) ∧ F.f 7 (x 0) < F.f 7 (x 5) ∧
        (⟪F.N 7, cross (x 2 - x 6) (x 0 - x 6)⟫ ≠ 0 ∨ ⟪x 0 - x 6, x 2 - x 6⟫ < 0 ∨
          ⟪x 0 - x 2, x 6 - x 2⟫ < 0)) ∨
      (F.f 7 (x 1) < F.f 7 (x 0) ∧ F.f 7 (x 1) < F.f 7 (x 5) ∧
        (⟪F.N 7, cross (x 2 - x 6) (x 1 - x 6)⟫ ≠ 0 ∨ ⟪x 1 - x 6, x 2 - x 6⟫ < 0 ∨
          ⟪x 1 - x 2, x 6 - x 2⟫ < 0)) ∨
      (F.f 7 (x 5) < F.f 7 (x 0) ∧ F.f 7 (x 5) < F.f 7 (x 1) ∧
        (⟪F.N 7, cross (x 2 - x 6) (x 5 - x 6)⟫ ≠ 0 ∨ ⟪x 5 - x 6, x 2 - x 6⟫ < 0 ∨
          ⟪x 5 - x 2, x 6 - x 2⟫ < 0))) :
    FaceChordView F 7 := by
  have hr : ∀ i : ZMod 5, (x ∘ pi24) (rimC6d i) = x (rimC6d' i) := by
    intro i; fin_cases i <;> rfl
  have hm : mer (sym24 F) 5 7 = mer F 5 7 := rfl
  have h := faceChordView_C6d (sym24 F) (x := x ∘ pi24) hM1 hM2
    (by simp only [hr, hm]; exact hinj) (by simp only [hr, hm]; exact hz) hM4
  exact faceChordView_sym F h

theorem faceChordView_C7b {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hM1 : 0 < ⟪F.N 0, mer F 6 7⟫ ∧ 0 < ⟪F.N 3, mer F 6 7⟫)
    (hM2 : 0 < ⟪x 6 - x 2, x 3 - x 2⟫ ∧ 0 < ⟪x 6 - x 3, x 2 - x 3⟫)
    (hinj : ∀ i j : ZMod 5, i ≠ j → ({i, j} : Finset (ZMod 5)) ≠ {2, 3} →
      ⟪x (rimC1 i), mer F 6 7⟫ ≠ ⟪x (rimC1 j), mer F 6 7⟫)
    (hz : ∃ σ : ℝ, σ ≠ 0 ∧ ∀ᶠ t in 𝓝[>] (0 : ℝ),
      UniOrSep (fun i : ZMod 5 => x (rimC1 i)) (mer F 6 7 + t • (σ • (x 3 - x 2))))
    (hM4 :
      (F.f 7 (x 0) < F.f 7 (x 1) ∧ F.f 7 (x 0) < F.f 7 (x 4) ∧
        (⟪F.N 7, cross (x 3 - x 2) (x 0 - x 2)⟫ ≠ 0 ∨ ⟪x 0 - x 2, x 3 - x 2⟫ < 0 ∨
          ⟪x 0 - x 3, x 2 - x 3⟫ < 0)) ∨
      (F.f 7 (x 1) < F.f 7 (x 0) ∧ F.f 7 (x 1) < F.f 7 (x 4) ∧
        (⟪F.N 7, cross (x 3 - x 2) (x 1 - x 2)⟫ ≠ 0 ∨ ⟪x 1 - x 2, x 3 - x 2⟫ < 0 ∨
          ⟪x 1 - x 3, x 2 - x 3⟫ < 0)) ∨
      (F.f 7 (x 4) < F.f 7 (x 0) ∧ F.f 7 (x 4) < F.f 7 (x 1) ∧
        (⟪F.N 7, cross (x 3 - x 2) (x 4 - x 2)⟫ ≠ 0 ∨ ⟪x 4 - x 2, x 3 - x 2⟫ < 0 ∨
          ⟪x 4 - x 3, x 2 - x 3⟫ < 0))) :
    FaceChordView F 7 := by
  obtain ⟨hN0, hN3⟩ := hM1
  obtain ⟨m6a, m6b⟩ := hM2
  have hm : mer F 6 7 ≠ 0 := fun h => by rw [h, inner_zero_right] at hN0; exact lt_irrefl 0 hN0
  have hN6 : 0 < ⟪F.N 6, mer F 6 7⟫ := mer_source_pos F 6 7 hm
  obtain ⟨s6, d6, hs6, hs16, hd6, hx6⟩ := level_chord_middle F 6 7 2 3 6
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) m6a m6b
  have hN1 : ⟪F.N 1, mer F 6 7⟫ < 0 := by
    have := chord_middle_facet_sign F 1 6 (by decide) (by decide) (by decide) (by decide)
      (Or.inl (by decide)) hs6 hs16 hx6
    nlinarith
  have hN5 : ⟪F.N 5, mer F 6 7⟫ < 0 := by
    have := chord_middle_facet_sign F 5 6 (by decide) (by decide) (by decide) (by decide)
      (Or.inr (by decide)) hs6 hs16 hx6
    nlinarith
  have hN8 : ⟪F.N 8, mer F 6 7⟫ < 0 := by
    have := chord_middle_facet_sign F 8 6 (by decide) (by decide) (by decide) (by decide)
      (Or.inl (by decide)) hs6 hs16 hx6
    nlinarith
  have hN4 : ⟪F.N 4, mer F 6 7⟫ < 0 := by
    have := chord_middle_facet_sign F 4 6 (by decide) (by decide) (by decide) (by decide)
      (Or.inl (by decide)) hs6 hs16 hx6
    nlinarith
  obtain ⟨σ, hσ, hzσ⟩ := hz
  refine faceChordView_of_rimCert_slide (k := 5) (by norm_num) F 7 (mer F 6 7) σ rimC1 2 tnC7b tpC7b spC7b
    (by decide) (mer_inner_facet F 6 7) ?_ hN6.ne' ?_ hinj hσ hzσ ?_
  · intro i hi
    fin_cases i
    · exact ⟨hN1, hN0⟩
    · exact ⟨hN5, hN0⟩
    · exact absurd rfl hi
    · exact ⟨hN8, hN3⟩
    · exact ⟨hN4, hN3⟩
  · intro q hq hqr
    fin_cases q <;> first
      | exact absurd hq (by decide)
      | exact absurd rfl (hqr 2)
      | exact absurd rfl (hqr 3)
      | exact ⟨s6, d6, hs6, hs16, hd6, hx6⟩
  · rcases hM4 with ⟨hf0_0, hf0_1, hoff⟩ | ⟨hf1_0, hf1_1, hoff⟩ | ⟨hf2_0, hf2_1, hoff⟩
    · refine ⟨0, by decide, fun m hm hmr => ?_, hoff⟩
      fin_cases m <;> first | exact absurd rfl hm | exact absurd hmr (by decide) | exact hf0_0 | exact hf0_1
    · refine ⟨1, by decide, fun m hm hmr => ?_, hoff⟩
      fin_cases m <;> first | exact absurd rfl hm | exact absurd hmr (by decide) | exact hf1_0 | exact hf1_1
    · refine ⟨4, by decide, fun m hm hmr => ?_, hoff⟩
      fin_cases m <;> first | exact absurd rfl hm | exact absurd hmr (by decide) | exact hf2_0 | exact hf2_1

theorem faceChordView_C7b' {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hM1 : 0 < ⟪F.N 1, mer F 8 7⟫ ∧ 0 < ⟪F.N 3, mer F 8 7⟫)
    (hM2 : 0 < ⟪x 2 - x 6, x 3 - x 6⟫ ∧ 0 < ⟪x 2 - x 3, x 6 - x 3⟫)
    (hinj : ∀ i j : ZMod 5, i ≠ j → ({i, j} : Finset (ZMod 5)) ≠ {2, 3} →
      ⟪x (rimC1' i), mer F 8 7⟫ ≠ ⟪x (rimC1' j), mer F 8 7⟫)
    (hz : ∃ σ : ℝ, σ ≠ 0 ∧ ∀ᶠ t in 𝓝[>] (0 : ℝ),
      UniOrSep (fun i : ZMod 5 => x (rimC1' i)) (mer F 8 7 + t • (σ • (x 3 - x 6))))
    (hM4 :
      (F.f 7 (x 0) < F.f 7 (x 1) ∧ F.f 7 (x 0) < F.f 7 (x 5) ∧
        (⟪F.N 7, cross (x 3 - x 6) (x 0 - x 6)⟫ ≠ 0 ∨ ⟪x 0 - x 6, x 3 - x 6⟫ < 0 ∨
          ⟪x 0 - x 3, x 6 - x 3⟫ < 0)) ∨
      (F.f 7 (x 1) < F.f 7 (x 0) ∧ F.f 7 (x 1) < F.f 7 (x 5) ∧
        (⟪F.N 7, cross (x 3 - x 6) (x 1 - x 6)⟫ ≠ 0 ∨ ⟪x 1 - x 6, x 3 - x 6⟫ < 0 ∨
          ⟪x 1 - x 3, x 6 - x 3⟫ < 0)) ∨
      (F.f 7 (x 5) < F.f 7 (x 0) ∧ F.f 7 (x 5) < F.f 7 (x 1) ∧
        (⟪F.N 7, cross (x 3 - x 6) (x 5 - x 6)⟫ ≠ 0 ∨ ⟪x 5 - x 6, x 3 - x 6⟫ < 0 ∨
          ⟪x 5 - x 3, x 6 - x 3⟫ < 0))) :
    FaceChordView F 7 := by
  have hr : ∀ i : ZMod 5, (x ∘ pi24) (rimC1 i) = x (rimC1' i) := by
    intro i; fin_cases i <;> rfl
  have hm : mer (sym24 F) 6 7 = mer F 8 7 := rfl
  have h := faceChordView_C7b (sym24 F) (x := x ∘ pi24) hM1 hM2
    (by simp only [hr, hm]; exact hinj) (by simp only [hr, hm]; exact hz) hM4
  exact faceChordView_sym F h

theorem faceChordView_C9 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (u : ℝ³) (hnu : ⟪F.N 2, u⟫ = 0)
    (hM1 : 0 < ⟪F.N 5, u⟫ ∧ 0 < ⟪F.N 6, u⟫ ∧ 0 < ⟪F.N 7, u⟫ ∧
      ⟪F.N 0, u⟫ < 0 ∧ ⟪F.N 1, u⟫ < 0 ∧ ⟪F.N 3, u⟫ < 0 ∧ ⟪F.N 8, u⟫ < 0)
    (hinj : Function.Injective fun i : ZMod 5 => ⟪x (rimC5 i), u⟫)
    (hz : UniOrSep (fun i : ZMod 5 => x (rimC5 i)) u)
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
  obtain ⟨hN5, hN6, hN7, hN0, hN1, hN3, hN8⟩ := hM1
  refine faceChordView_of_rimCert (k := 5) (by norm_num) F 2 u rimC5 1 tnC9 tpC9 spC9
    (by decide) hnu ?_ hN6.ne' ?_ hinj hz ?_
  · intro i hi
    fin_cases i
    · exact ⟨hN0, hN5⟩
    · exact absurd rfl hi
    · exact ⟨hN3, hN6⟩
    · exact ⟨hN8, hN7⟩
    · exact ⟨hN1, hN5⟩
  · intro q hq hqr
    fin_cases q <;> first
      | exact absurd hq (by decide)
      | exact absurd rfl (hqr 1)
      | exact absurd rfl (hqr 2)
      | exact (chord_middle_iff_facet_signs F u 2 0 3 2 5 0
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) hnu).2 (mul_pos_of_neg_of_neg hN0 hN3)
  · rcases hM4 with ⟨hf0_0, hf0_1, hoff⟩ | ⟨hf1_0, hf1_1, hoff⟩ | ⟨hf2_0, hf2_1, hoff⟩
    · refine ⟨4, by decide, fun m hm hmr => ?_, hoff⟩
      fin_cases m <;> first | exact absurd rfl hm | exact absurd hmr (by decide) | exact hf0_0 | exact hf0_1
    · refine ⟨3, by decide, fun m hm hmr => ?_, hoff⟩
      fin_cases m <;> first | exact absurd rfl hm | exact absurd hmr (by decide) | exact hf1_0 | exact hf1_1
    · refine ⟨0, by decide, fun m hm hmr => ?_, hoff⟩
      fin_cases m <;> first | exact absurd rfl hm | exact absurd hmr (by decide) | exact hf2_0 | exact hf2_1

theorem faceChordView_C9' {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (u : ℝ³) (hnu : ⟪F.N 4, u⟫ = 0)
    (hM1 : 0 < ⟪F.N 5, u⟫ ∧ 0 < ⟪F.N 8, u⟫ ∧ 0 < ⟪F.N 7, u⟫ ∧
      ⟪F.N 1, u⟫ < 0 ∧ ⟪F.N 0, u⟫ < 0 ∧ ⟪F.N 3, u⟫ < 0 ∧ ⟪F.N 6, u⟫ < 0)
    (hinj : Function.Injective fun i : ZMod 5 => ⟪x (rimC5' i), u⟫)
    (hz : UniOrSep (fun i : ZMod 5 => x (rimC5' i)) u)
    (hM4 :
      (F.f 4 (x 2) < F.f 4 (x 1) ∧ F.f 4 (x 2) < F.f 4 (x 3) ∧
        (⟪F.N 4, cross (x 4 - x 6) (x 2 - x 6)⟫ ≠ 0 ∨ ⟪x 2 - x 6, x 4 - x 6⟫ < 0 ∨
          ⟪x 2 - x 4, x 6 - x 4⟫ < 0)) ∨
      (F.f 4 (x 3) < F.f 4 (x 1) ∧ F.f 4 (x 3) < F.f 4 (x 2) ∧
        (⟪F.N 4, cross (x 4 - x 6) (x 3 - x 6)⟫ ≠ 0 ∨ ⟪x 3 - x 6, x 4 - x 6⟫ < 0 ∨
          ⟪x 3 - x 4, x 6 - x 4⟫ < 0)) ∨
      (F.f 4 (x 1) < F.f 4 (x 3) ∧ F.f 4 (x 1) < F.f 4 (x 2) ∧
        (⟪F.N 4, cross (x 4 - x 6) (x 1 - x 6)⟫ ≠ 0 ∨ ⟪x 1 - x 6, x 4 - x 6⟫ < 0 ∨
          ⟪x 1 - x 4, x 6 - x 4⟫ < 0))) :
    FaceChordView F 4 := by
  have hr : ∀ i : ZMod 5, (x ∘ pi24) (rimC5 i) = x (rimC5' i) := by
    intro i; fin_cases i <;> rfl
  have h := faceChordView_C9 (sym24 F) (x := x ∘ pi24) u hnu hM1
    (by simp only [hr]; exact hinj) (by simp only [hr]; exact hz) hM4
  exact faceChordView_sym F h

theorem faceChordView_C10 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (u : ℝ³) (hnu : ⟪F.N 3, u⟫ = 0)
    (hM1 : 0 < ⟪F.N 5, u⟫ ∧ 0 < ⟪F.N 6, u⟫ ∧ 0 < ⟪F.N 8, u⟫ ∧
      ⟪F.N 0, u⟫ < 0 ∧ ⟪F.N 1, u⟫ < 0 ∧ ⟪F.N 2, u⟫ < 0 ∧ ⟪F.N 4, u⟫ < 0)
    (hinj : Function.Injective fun i : ZMod 5 => ⟪x (rimC10 i), u⟫)
    (hz : UniOrSep (fun i : ZMod 5 => x (rimC10 i)) u)
    (hM4 :
      (F.f 3 (x 6) < F.f 3 (x 1) ∧ F.f 3 (x 6) < F.f 3 (x 2) ∧
        (⟪F.N 3, cross (x 4 - x 5) (x 6 - x 5)⟫ ≠ 0 ∨ ⟪x 6 - x 5, x 4 - x 5⟫ < 0 ∨
          ⟪x 6 - x 4, x 5 - x 4⟫ < 0)) ∨
      (F.f 3 (x 1) < F.f 3 (x 6) ∧ F.f 3 (x 1) < F.f 3 (x 2) ∧
        (⟪F.N 3, cross (x 4 - x 5) (x 1 - x 5)⟫ ≠ 0 ∨ ⟪x 1 - x 5, x 4 - x 5⟫ < 0 ∨
          ⟪x 1 - x 4, x 5 - x 4⟫ < 0)) ∨
      (F.f 3 (x 2) < F.f 3 (x 6) ∧ F.f 3 (x 2) < F.f 3 (x 1) ∧
        (⟪F.N 3, cross (x 4 - x 5) (x 2 - x 5)⟫ ≠ 0 ∨ ⟪x 2 - x 5, x 4 - x 5⟫ < 0 ∨
          ⟪x 2 - x 4, x 5 - x 4⟫ < 0))) :
    FaceChordView F 3 := by
  obtain ⟨hN5, hN6, hN8, hN0, hN1, hN2, hN4⟩ := hM1
  have hcr : cross u (x 4 - x 5) ≠ 0 :=
    cross_ne_zero_of_facet_signs F u 2 4 5 4 (by decide) (by decide) (by decide) (by decide)
      (mul_pos_of_neg_of_neg hN2 hN4)
  refine faceChordView_of_rimCert_cr (k := 5) (by norm_num) F 3 u rimC10 4 tnC10 tpC10 spC10
    (by decide) hnu ?_ hcr ?_ hinj hz ?_
  · intro i hi
    fin_cases i
    · exact ⟨hN4, hN8⟩
    · exact ⟨hN1, hN5⟩
    · exact ⟨hN0, hN5⟩
    · exact ⟨hN2, hN6⟩
    · exact absurd rfl hi
  · intro q hq hqr
    fin_cases q <;> first
      | exact absurd hq (by decide)
      | exact absurd rfl (hqr 0)
      | exact absurd rfl (hqr 4)
      | exact (chord_middle_iff_facet_signs F u 3 2 4 5 4 0
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) hnu).2 (mul_pos_of_neg_of_neg hN2 hN4)
      | exact (chord_middle_iff_facet_signs F u 3 6 8 5 4 3
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) hnu).2 (mul_pos hN6 hN8)
  · rcases hM4 with ⟨hf0_0, hf0_1, hoff⟩ | ⟨hf1_0, hf1_1, hoff⟩ | ⟨hf2_0, hf2_1, hoff⟩
    · refine ⟨1, by decide, fun m hm hmr => ?_, hoff⟩
      fin_cases m <;> first | exact absurd rfl hm | exact absurd hmr (by decide) | exact hf0_0 | exact hf0_1
    · refine ⟨2, by decide, fun m hm hmr => ?_, hoff⟩
      fin_cases m <;> first | exact absurd rfl hm | exact absurd hmr (by decide) | exact hf1_0 | exact hf1_1
    · refine ⟨3, by decide, fun m hm hmr => ?_, hoff⟩
      fin_cases m <;> first | exact absurd rfl hm | exact absurd hmr (by decide) | exact hf2_0 | exact hf2_1

theorem faceChordView_C10' {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (u : ℝ³) (hnu : ⟪F.N 3, u⟫ = 0)
    (hM1 : 0 < ⟪F.N 5, u⟫ ∧ 0 < ⟪F.N 8, u⟫ ∧ 0 < ⟪F.N 6, u⟫ ∧
      ⟪F.N 1, u⟫ < 0 ∧ ⟪F.N 0, u⟫ < 0 ∧ ⟪F.N 4, u⟫ < 0 ∧ ⟪F.N 2, u⟫ < 0)
    (hinj : Function.Injective fun i : ZMod 5 => ⟪x (rimC10' i), u⟫)
    (hz : UniOrSep (fun i : ZMod 5 => x (rimC10' i)) u)
    (hM4 :
      (F.f 3 (x 2) < F.f 3 (x 1) ∧ F.f 3 (x 2) < F.f 3 (x 6) ∧
        (⟪F.N 3, cross (x 5 - x 4) (x 2 - x 4)⟫ ≠ 0 ∨ ⟪x 2 - x 4, x 5 - x 4⟫ < 0 ∨
          ⟪x 2 - x 5, x 4 - x 5⟫ < 0)) ∨
      (F.f 3 (x 1) < F.f 3 (x 2) ∧ F.f 3 (x 1) < F.f 3 (x 6) ∧
        (⟪F.N 3, cross (x 5 - x 4) (x 1 - x 4)⟫ ≠ 0 ∨ ⟪x 1 - x 4, x 5 - x 4⟫ < 0 ∨
          ⟪x 1 - x 5, x 4 - x 5⟫ < 0)) ∨
      (F.f 3 (x 6) < F.f 3 (x 2) ∧ F.f 3 (x 6) < F.f 3 (x 1) ∧
        (⟪F.N 3, cross (x 5 - x 4) (x 6 - x 4)⟫ ≠ 0 ∨ ⟪x 6 - x 4, x 5 - x 4⟫ < 0 ∨
          ⟪x 6 - x 5, x 4 - x 5⟫ < 0))) :
    FaceChordView F 3 := by
  have hr : ∀ i : ZMod 5, (x ∘ pi24) (rimC10 i) = x (rimC10' i) := by
    intro i; fin_cases i <;> rfl
  have h := faceChordView_C10 (sym24 F) (x := x ∘ pi24) u hnu hM1
    (by simp only [hr]; exact hinj) (by simp only [hr]; exact hz) hM4
  exact faceChordView_sym F h

end Minimality.T24.Mer
