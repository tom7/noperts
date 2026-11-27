module

public import Minimality.Type24HoleCore3
public import Minimality.UnimodalSplit
public import Minimality.Type24NoCoplanar
public import Minimality.LexTiltSplit

/-!
# Task FH1: `LexAny → EdgePlaneAny` for type 24 under `NoParRim`

Assembly of `OpenCellRob` (`openCellRob_of_lexAny`), open-cell `StrictRimN` (`strictRimN_of_openCell`),
generic tilt avoiding depth ties and parallel rim edges (`NoParallelRimEdges` via `not_parallel4`
and `NoParRim`), `RobUni` + distinct depths `⇒ StrictlyUnimodal`, and `UnimodalSplit` + `split_core_ep`.
-/

@[expose] public section

open scoped RealInnerProductSpace Topology
open Finset Filter
open Minimality Minimality.H21 Minimality.T24.SAT Minimality.T24.Z0 Minimality.T24.NC

namespace Minimality.T24.LexEP

private theorem s24_sep :
    ∀ i j : Fin 7, j ≠ i → ∃ t : Fin 9, i ∈ s0x_S24 t ∧ j ∉ s0x_S24 t := by decide

/-- No two disjoint edges among any `badRims` 4-set are parallel in `ℝ³`. -/
def NoParRim (x : Fin 7 → ℝ³) : Prop :=
  ∀ a b c d : Fin 7, [a, b, c, d].Nodup → ({a, b, c, d} : Finset (Fin 7)) ∈ badRims →
    cross (x a - x b) (x c - x d) ≠ 0

/-- Step 2: an open cell view `CellAt F U Dn u` on `S0xCycUD` gives `StrictRimN` (up to reversal). -/
theorem strictRimN_of_openCell {k : ℕ} [NeZero k] (hk : 3 ≤ k) {x : Fin 7 → ℝ³}
    (F : S0xFac 9 s0x_S24 x) {c : ZMod k → Fin 7} (hc : Function.Injective c)
    {U Dn : Finset (Fin 9)} (hcyc : S0xCycUD s0x_S24 c U Dn) {u : ℝ³} (hu : CellAt F U Dn u) :
    Split.StrictRimN x u c ∨ Split.StrictRimN x u (fun i => c (-i)) := by
  have hx := EdgeViewLink.inj_of_fac24 F
  obtain ⟨D⟩ := silL_of_cell F hcyc hu.cellLe hu
  choose μ hμ0 hμ using fun i => h21b_exists_mu hk hx hc D i
  have hsign := h21b_sign_agree hk hx hc D μ hμ0 hμ
  have Q : ∀ i m, m ≠ c i → m ≠ c (i + 1) →
      0 < D.fA i (x m) * ⟪D.B i, u⟫ - D.fB i (x m) * ⟪D.A i, u⟫ := by
    intro i m h0 h1
    rcases h21b_Q_pos D i m h0 h1 with h | ⟨h0', h⟩
    · exact h
    · rw [h0'] at h; exact absurd h (lt_irrefl _)
  have key : ∀ (i : ZMod k) (m : Fin 7),
      Split.det3 (x (c (i + 1)) - x (c i)) (x m - x (c i)) u =
        μ i * (D.fA i (x m) * ⟪D.B i, u⟫ - D.fB i (x m) * ⟪D.A i, u⟫) := by
    intro i m
    rw [Split.det3_eq_minimality]
    exact h21b_det_eq D i (μ i) (hμ i) m u
  rcases hsign with hp | hn
  · left
    intro m i h0 h1
    rw [key i m]
    exact mul_pos (hp i) (Q i m h0 h1)
  · right
    intro m i h0 h1
    obtain ⟨j, rfl⟩ : ∃ j, i = -j - 1 := ⟨-i - 1, by ring⟩
    simp only [show -(-j - 1 + 1) = j by ring, show -(-j - 1) = j + 1 by ring] at h0 h1 ⊢
    have e : Split.det3 (x (c j) - x (c (j + 1))) (x m - x (c (j + 1))) u =
        -Split.det3 (x (c (j + 1)) - x (c j)) (x m - x (c j)) u := by
      simp only [Split.det3, PiLp.sub_apply]; ring
    rw [e, key j m]
    have := mul_neg_of_neg_of_pos (hn j) (Q j m h1 h0)
    linarith

/-- `RobUni` is preserved under cycle reversal `i ↦ -i`. -/
theorem robUni_rev {k : ℕ} [NeZero k] {z : ZMod k → ℝ} (hz : RobUni z) :
    RobUni (fun i => z (-i)) := by
  intro B b c d hb hc hd hk ⟨e1, e2, e3, e4⟩
  have h0 : 0 < k - d := by omega
  have h1 : k - d < k - c := by omega
  have h2 : k - c < k - b := by omega
  have h3 : k - b < k := by omega
  refine hz (-B) (k - d) (k - c) (k - b) h0 h1 h2 h3 ⟨?_, ?_, ?_, ?_⟩
  · have : (-B + ((k - d : ℕ) : ZMod k)) = -(B + (d : ZMod k)) := by
      rw [Nat.cast_sub (le_of_lt hk), ZMod.natCast_self]; ring
    rw [this]; exact e3
  · have hA : (-B + ((k - d : ℕ) : ZMod k)) = -(B + (d : ZMod k)) := by
      rw [Nat.cast_sub (le_of_lt hk), ZMod.natCast_self]; ring
    have hB : (-B + ((k - c : ℕ) : ZMod k)) = -(B + (c : ZMod k)) := by
      rw [Nat.cast_sub (by omega), ZMod.natCast_self]; ring
    rw [hA, hB]; exact e4
  · have : (-B + ((k - b : ℕ) : ZMod k)) = -(B + (b : ZMod k)) := by
      rw [Nat.cast_sub (by omega), ZMod.natCast_self]; ring
    rw [this]; exact e1
  · have hA : (-B + ((k - b : ℕ) : ZMod k)) = -(B + (b : ZMod k)) := by
      rw [Nat.cast_sub (by omega), ZMod.natCast_self]; ring
    have hB : (-B + ((k - c : ℕ) : ZMod k)) = -(B + (c : ZMod k)) := by
      rw [Nat.cast_sub (by omega), ZMod.natCast_self]; ring
    rw [hA, hB]; exact e2

/-- `RobUni` is an open condition under affine perturbations `u + t • v`. -/
theorem robUni_ev_tilt {k : ℕ} [NeZero k] {X : ZMod k → ℝ³} {u : ℝ³}
    (hrob : RobUni (fun i => ⟪X i, u⟫)) (v : ℝ³) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), RobUni (fun i => ⟪X i, u + t • v⟫) := by
  have key : ∀ (B : ZMod k) (b c d : Fin k), ∀ᶠ t in 𝓝[>] (0 : ℝ),
      0 < (b : ℕ) → (b : ℕ) < c → (c : ℕ) < d →
      ¬ (⟪X (B + (b : ℕ)), u + t • v⟫ ≤ ⟪X B, u + t • v⟫ ∧
         ⟪X (B + (b : ℕ)), u + t • v⟫ ≤ ⟪X (B + (c : ℕ)), u + t • v⟫ ∧
         ⟪X (B + (d : ℕ)), u + t • v⟫ ≤ ⟪X B, u + t • v⟫ ∧
         ⟪X (B + (d : ℕ)), u + t • v⟫ ≤ ⟪X (B + (c : ℕ)), u + t • v⟫) := by
    intro B b c d
    by_cases hh : 0 < (b : ℕ) ∧ (b : ℕ) < c ∧ (c : ℕ) < d
    · have hnot := hrob B b c d hh.1 hh.2.1 hh.2.2 d.isLt
      have hdisj : ⟪X B, u⟫ < ⟪X (B + (b : ℕ)), u⟫ ∨ ⟪X (B + (c : ℕ)), u⟫ < ⟪X (B + (b : ℕ)), u⟫ ∨
          ⟪X B, u⟫ < ⟪X (B + (d : ℕ)), u⟫ ∨ ⟪X (B + (c : ℕ)), u⟫ < ⟪X (B + (d : ℕ)), u⟫ := by
        by_contra h
        push Not at h
        exact hnot h
      have ev_lt : ∀ p q : ZMod k, ⟪X p, u⟫ < ⟪X q, u⟫ →
          ∀ᶠ t in 𝓝[>] (0 : ℝ), ⟪X p, u + t • v⟫ < ⟪X q, u + t • v⟫ := fun p q hpq =>
        (Minimality.eventually_pos_affine (B := ⟪X q, v⟫ - ⟪X p, v⟫) (Or.inl (sub_pos.2 hpq))).mono
          fun t ht => by
            simp only [inner_add_right, real_inner_smul_right] at ht ⊢; linarith
      rcases hdisj with h1 | h1 | h1 | h1
      · filter_upwards [ev_lt _ _ h1] with t ht _ _ _ ⟨e1, _, _, _⟩; exact absurd e1 (not_le.2 ht)
      · filter_upwards [ev_lt _ _ h1] with t ht _ _ _ ⟨_, e2, _, _⟩; exact absurd e2 (not_le.2 ht)
      · filter_upwards [ev_lt _ _ h1] with t ht _ _ _ ⟨_, _, e3, _⟩; exact absurd e3 (not_le.2 ht)
      · filter_upwards [ev_lt _ _ h1] with t ht _ _ _ ⟨_, _, _, e4⟩; exact absurd e4 (not_le.2 ht)
    · exact Filter.Eventually.of_forall fun _ h0 h1 h2 => absurd ⟨h0, h1, h2⟩ hh
  have hall := Filter.eventually_all.2 fun B => Filter.eventually_all.2 fun b =>
    Filter.eventually_all.2 fun c => Filter.eventually_all.2 fun d => key B b c d
  filter_upwards [hall] with t ht B b c d h0 h1 h2 h3
  exact ht B ⟨b, by omega⟩ ⟨c, by omega⟩ ⟨d, h3⟩ h0 h1 h2

/-- `RobUni` + pairwise distinct values implies `StrictlyUnimodal`. -/
theorem strictlyUnimodal_of_robUni {k : ℕ} [NeZero k] (hk : 3 ≤ k)
    (X : ZMod k → ℝ³) (w : ℝ³)
    (hdist : ∀ i j : ZMod k, i ≠ j → ⟪X i, w⟫ ≠ ⟪X j, w⟫)
    (hrob : RobUni (fun i => ⟪X i, w⟫)) :
    ∃ m M : ZMod k, Split.UnimodalSplit.StrictlyUnimodal X w m M := by
  have : Nonempty (ZMod k) := ⟨0⟩
  obtain ⟨m, hm_univ, hm_min⟩ := Finset.exists_min_image Finset.univ (fun i : ZMod k => ⟪X i, w⟫) Finset.univ_nonempty
  obtain ⟨M, hM_univ, hM_max⟩ := Finset.exists_max_image Finset.univ (fun i : ZMod k => ⟪X i, w⟫) Finset.univ_nonempty
  have hm_lt : ∀ i : ZMod k, i ≠ m → ⟪X m, w⟫ < ⟪X i, w⟫ := fun i hi =>
    lt_of_le_of_ne (hm_min i (Finset.mem_univ i)) (hdist m i hi.symm)
  have hM_gt : ∀ i : ZMod k, i ≠ M → ⟪X i, w⟫ < ⟪X M, w⟫ := fun i hi =>
    lt_of_le_of_ne (hM_max i (Finset.mem_univ i)) (hdist i M hi)
  have hmM : m ≠ M := by
    intro h; subst h
    have h1 : (m + 1 : ZMod k) ≠ m := (Minimality.zmod_ne_add_one (by omega) m).symm
    linarith [hm_lt (m + 1) h1, hM_gt (m + 1) h1]
  refine ⟨m, M, hmM, fun s hs => ?_, fun s hs1 hs2 => ?_⟩
  · by_contra hle
    push Not at hle
    have hne : m + ((s + 1 : ℕ) : ZMod k) ≠ m + (s : ZMod k) := by
      intro h
      have h' : (((s + 1 : ℕ) : ZMod k)) = (s : ZMod k) := add_left_cancel h
      push_cast at h'
      have h1 : (1 : ZMod k) = 0 := by linear_combination h'
      have : Fact (1 < k) := ⟨by omega⟩
      exact one_ne_zero h1
    have hlt := lt_of_le_of_ne hle (hdist _ _ hne)
    have h0 : 0 < s := by
      rcases Nat.eq_zero_or_pos s with rfl | hpos
      · simp only [Nat.cast_zero, add_zero] at hlt
        have h1 : m + ((1 : ℕ) : ZMod k) ≠ m := by
          simpa using (Minimality.zmod_ne_add_one (by omega) m).symm
        linarith [hm_lt (m + ((1 : ℕ) : ZMod k)) h1]
      · exact hpos
    by_cases hsM : s + 1 = (M - m).val
    · have hM_eq : m + ((s + 1 : ℕ) : ZMod k) = M := by
        rw [hsM]; simp [ZMod.natCast_zmod_val]
      rw [hM_eq] at hlt
      linarith [hM_max (m + (s : ZMod k)) (Finset.mem_univ _)]
    · have hMval : (M - m).val < k := ZMod.val_lt (M - m)
      have hb : 0 < 1 := by omega
      have hc : 1 < (M - m).val - s := by omega
      have hd : (M - m).val - s < k - s := by omega
      have hdk : k - s < k := by omega
      have hnot := hrob (m + (s : ZMod k)) 1 ((M - m).val - s) (k - s) hb hc hd hdk
      apply hnot
      have e1 : (m + (s : ZMod k)) + ((1 : ℕ) : ZMod k) = m + ((s + 1 : ℕ) : ZMod k) := by
        push_cast; ring
      have e2 : (m + (s : ZMod k)) + (((M - m).val - s : ℕ) : ZMod k) = M := by
        rw [Nat.cast_sub (by omega), ZMod.natCast_zmod_val]; ring
      have e3 : (m + (s : ZMod k)) + ((k - s : ℕ) : ZMod k) = m := by
        rw [Nat.cast_sub (by omega), ZMod.natCast_self]; ring
      rw [e1, e2, e3]
      exact ⟨hlt.le, hM_max _ (Finset.mem_univ _), hm_min _ (Finset.mem_univ _), hm_min _ (Finset.mem_univ _)⟩
  · by_contra hle
    push Not at hle
    have hne : m + (s : ZMod k) ≠ m + ((s + 1 : ℕ) : ZMod k) := by
      intro h
      have h' : (s : ZMod k) = ((s + 1 : ℕ) : ZMod k) := add_left_cancel h
      push_cast at h'
      have h1 : (1 : ZMod k) = 0 := by linear_combination -h'
      have : Fact (1 < k) := ⟨by omega⟩
      exact one_ne_zero h1
    have hlt := lt_of_le_of_ne hle (hdist _ _ hne)
    by_cases hsM : s = (M - m).val
    · subst hsM
      have hM_eq : m + ((M - m).val : ZMod k) = M := by simp [ZMod.natCast_zmod_val]
      rw [hM_eq] at hlt
      linarith [hM_max (m + (((M - m).val + 1 : ℕ) : ZMod k)) (Finset.mem_univ _)]
    · by_cases hsk : s + 1 = k
      · have hm_eq : m + ((s + 1 : ℕ) : ZMod k) = m := by
          rw [hsk, ZMod.natCast_self, add_zero]
        rw [hm_eq] at hlt
        linarith [hm_min (m + (s : ZMod k)) (Finset.mem_univ _)]
      · have hltM : (M - m).val < s := by omega
        have hb : 0 < s - (M - m).val := by omega
        have hc : s - (M - m).val < s + 1 - (M - m).val := by omega
        have hd : s + 1 - (M - m).val < k - (M - m).val := by omega
        have hdk : k - (M - m).val < k := by
          have hMpos : 0 < (M - m).val := by rw [ZMod.val_pos]; exact sub_ne_zero.2 hmM.symm
          omega
        have hnot := hrob M (s - (M - m).val) (s + 1 - (M - m).val) (k - (M - m).val) hb hc hd hdk
        apply hnot
        have e1 : M + ((s - (M - m).val : ℕ) : ZMod k) = m + (s : ZMod k) := by
          rw [Nat.cast_sub (le_of_lt hltM), ZMod.natCast_zmod_val]; ring
        have e2 : M + ((s + 1 - (M - m).val : ℕ) : ZMod k) = m + ((s + 1 : ℕ) : ZMod k) := by
          rw [Nat.cast_sub (by omega), ZMod.natCast_zmod_val]; push_cast; ring
        have e3 : M + ((k - (M - m).val : ℕ) : ZMod k) = m := by
          rw [Nat.cast_sub (ZMod.val_lt _).le, ZMod.natCast_self, ZMod.natCast_zmod_val]; ring
        rw [e1, e2, e3]
        exact ⟨hM_max _ (Finset.mem_univ _), hlt.le, hm_min _ (Finset.mem_univ _), hm_min _ (Finset.mem_univ _)⟩

/-- **Task FH1:** Under `NoParRim x`, any `Gen.LexAny F` on type 24 yields `Gen.EdgePlaneAny x`. -/
theorem lexAny_edgePlaneAny_of_noPar {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hp : NoParRim x) (h : Gen.LexAny F) : Gen.EdgePlaneAny x := by
  have hx := EdgeViewLink.inj_of_fac24 F
  have hseg := Split.noBetween_of_fac F s24_sep
  obtain ⟨k, hne, c, U, Dn, u, hk, hc, hcyc, hu, hrob⟩ := T24.Stmt.openCellRob_of_lexAny h
  have hc' : ∃ (c' : ZMod k → Fin 7), Function.Injective c' ∧ Split.StrictRimN x u c' ∧
      RobUni (fun i => ⟪x (c' i), u⟫) := by
    rcases strictRimN_of_openCell (by omega) F hc hcyc hu with hr | hr
    · exact ⟨c, hc, hr, hrob⟩
    · exact ⟨fun i => c (-i), fun i j e => neg_injective (hc e), hr, robUni_rev hrob⟩
  obtain ⟨c', hc', hrim, hrob'⟩ := hc'
  let X : ZMod k → ℝ³ := fun i => x (c' i)
  have h20 : (2 : ZMod k) ≠ 0 := by
    intro h2
    have h2' : ((2 : ℕ) : ZMod k) = 0 := by exact_mod_cast h2
    rw [ZMod.natCast_eq_zero_iff] at h2'
    have := Nat.le_of_dvd (by norm_num) h2'
    omega
  have hpar : ∀ i j : ZMod k, i ≠ j → cross (X (i + 1) - X i) (X (j + 1) - X j) ≠ 0 := by
    intro i j hij hcr
    by_cases hij1 : j = i + 1
    · subst hij1
      have h1 := hrim (c' (i + 2)) i (fun e => by
        have := hc' e; exact h20 (by linear_combination this)) (fun e => by
        have := hc' e; have h1 : (1 : ZMod k) = 0 := by linear_combination this
        have hf : Fact (1 < k) := ⟨by omega⟩
        exact one_ne_zero h1)
      have hzero : Split.det3 (X (i + 1) - X i) (X (i + 2) - X i) u = 0 := by
        rw [show (i + 2 : ZMod k) = i + 1 + 1 by ring]
        have hadd : X (i + 1 + 1) - X i = (X (i + 1) - X i) + (X (i + 1 + 1) - X (i + 1)) := by abel
        rw [hadd, Split.det3_eq_inner_cross]
        have hcr' : cross (X (i + 1) - X i) ((X (i + 1) - X i) + (X (i + 1 + 1) - X (i + 1))) = 0 := by
          have : cross (X (i + 1) - X i) (X (i + 1) - X i) = 0 := by
            ext m; fin_cases m <;> simp [cross] <;> ring
          have hlin : cross (X (i + 1) - X i) ((X (i + 1) - X i) + (X (i + 1 + 1) - X (i + 1))) =
              cross (X (i + 1) - X i) (X (i + 1) - X i) +
              cross (X (i + 1) - X i) (X (i + 1 + 1) - X (i + 1)) := by
            ext m; fin_cases m <;> simp [cross] <;> ring
          rw [hlin, this, hcr, add_zero]
        rw [hcr', inner_zero_left]
      exact h1.ne' hzero
    · by_cases hji1 : i = j + 1
      · subst hji1
        have h1 := hrim (c' (j + 2)) j (fun e => by
          have := hc' e; exact h20 (by linear_combination this)) (fun e => by
          have := hc' e; have h1 : (1 : ZMod k) = 0 := by linear_combination this
          have hf : Fact (1 < k) := ⟨by omega⟩
          exact one_ne_zero h1)
        have hzero : Split.det3 (X (j + 1) - X j) (X (j + 2) - X j) u = 0 := by
          rw [show (j + 2 : ZMod k) = j + 1 + 1 by ring]
          have hadd : X (j + 1 + 1) - X j = (X (j + 1) - X j) + (X (j + 1 + 1) - X (j + 1)) := by abel
          rw [hadd, Split.det3_eq_inner_cross]
          have hcr_sym : cross (X (j + 1) - X j) (X (j + 1 + 1) - X (j + 1)) = 0 := by
            have : cross (X (j + 1) - X j) (X (j + 1 + 1) - X (j + 1)) =
                -cross (X (j + 1 + 1) - X (j + 1)) (X (j + 1) - X j) := by
              ext m; fin_cases m <;> simp [cross] <;> ring
            rw [this, hcr, neg_zero]
          have : cross (X (j + 1) - X j) (X (j + 1) - X j) = 0 := by
            ext m; fin_cases m <;> simp [cross] <;> ring
          have hlin : cross (X (j + 1) - X j) ((X (j + 1) - X j) + (X (j + 1 + 1) - X (j + 1))) =
              cross (X (j + 1) - X j) (X (j + 1) - X j) +
              cross (X (j + 1) - X j) (X (j + 1 + 1) - X (j + 1)) := by
            ext m; fin_cases m <;> simp [cross] <;> ring
          rw [hlin, this, hcr_sym, add_zero, inner_zero_left]
        exact h1.ne' hzero
      · have hnd : [c' (i + 1), c' i, c' (j + 1), c' j].Nodup := by
          have h10 : (1 : ZMod k) ≠ 0 := by
            intro h; have : Fact (1 < k) := ⟨by omega⟩; exact one_ne_zero h
          simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
            List.nodup_nil, not_false_eq_true, and_true]
          refine ⟨⟨fun e => h10 (by linear_combination hc' e),
            fun e => hij (by linear_combination hc' e),
            fun e => hij1 (hc' e).symm⟩,
            ⟨fun e => hji1 (hc' e), fun e => hij (hc' e)⟩,
            fun e => h10 (by linear_combination hc' e)⟩
        by_cases hbad : ({c' (i + 1), c' i, c' (j + 1), c' j} : Finset (Fin 7)) ∈ badRims
        · exact hp _ _ _ _ hnd hbad hcr
        · exact not_parallel4 F hnd hbad hcr
  let pairs := (Finset.univ : Finset (ZMod k × ZMod k)).filter (fun p => p.1 ≠ p.2)
  let Fset : Finset ℝ³ :=
    (pairs.image fun p => X p.1 - X p.2) ∪
    (pairs.image fun p => cross (X (p.1 + 1) - X p.1) (X (p.2 + 1) - X p.2))
  have hFset : ∀ y ∈ Fset, y ≠ 0 := by
    intro y hy
    simp only [Fset, pairs, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
      Finset.mem_univ, true_and] at hy
    rcases hy with ⟨p, hpne, rfl⟩ | ⟨p, hpne, rfl⟩
    · rw [sub_ne_zero]; intro he; exact hpne (hc' (hx he))
    · exact hpar p.1 p.2 hpne
  obtain ⟨v, -, hv⟩ := Minimality.exists_avoid_kernels (ι := {y : ℝ³ // y ∈ Fset})
    (fun y => innerₗ ℝ³ y.1)
    (fun y hy => by
      have h1 := LinearMap.congr_fun hy y.1
      simp only [innerₗ_apply_apply, LinearMap.zero_apply, inner_self_eq_zero] at h1
      exact hFset y.1 y.2 h1) isOpen_univ Set.univ_nonempty
  have hK : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ y ∈ Fset, ⟪y, u⟫ + t * ⟪y, v⟫ ≠ 0 := by
    have h_all : ∀ y : {y : ℝ³ // y ∈ Fset}, ∀ᶠ t in 𝓝[>] (0 : ℝ), ⟪y.1, u⟫ + t * ⟪y.1, v⟫ ≠ 0 :=
      fun y => Minimality.eventually_affine_ne fun _ => by simpa using hv y
    rw [← eventually_all] at h_all
    filter_upwards [h_all] with t ht y hy
    exact ht ⟨y, hy⟩
  obtain ⟨t, ht_rim, ht_rob, ht_K⟩ := ((Split.strictRim_ev hrim v).and
    ((robUni_ev_tilt hrob' v).and hK)).exists
  set u' := u + t • v with hu'
  have hu'_ne : ∀ y ∈ Fset, ⟪y, u'⟫ ≠ 0 := fun y hy => by
    have hne' := ht_K y hy
    rw [hu', inner_add_right, real_inner_smul_right]
    exact hne'
  have hdist : ∀ i j : ZMod k, i ≠ j → ⟪X i, u'⟫ ≠ ⟪X j, u'⟫ := by
    intro i j hij heq
    have hmem : X i - X j ∈ Fset := Finset.mem_union_left _ (Finset.mem_image.mpr
      ⟨(i, j), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩, rfl⟩)
    apply hu'_ne _ hmem
    rw [inner_sub_left, heq, sub_self]
  have hgen : Split.UnimodalSplit.NoParallelRimEdges X u' := by
    intro i j hij hdet
    have hmem : cross (X (i + 1) - X i) (X (j + 1) - X j) ∈ Fset :=
      Finset.mem_union_right _ (Finset.mem_image.mpr
        ⟨(i, j), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩, rfl⟩)
    apply hu'_ne _ hmem
    rw [← Split.det3_eq_inner_cross]
    exact hdet
  obtain ⟨m, M, huni⟩ := strictlyUnimodal_of_robUni (by omega) X u' hdist ht_rob
  have hccw := Split.UnimodalSplit.strictRimCcw_of_strictRimN x u' c' hc' ht_rim
  obtain ⟨a, cc, hsep⟩ := Split.UnimodalSplit.isDepthSeparatedAt_of_unimodal hk X u' m M hccw hdist huni hgen
  have hca : cc ≠ a := by
    intro he; subst he
    exact (hsep.1 (cc + 1) (Minimality.zmod_ne_add_one (by omega) cc).symm).ne (by
      simp only [X, Split.det3, PiLp.sub_apply]; ring)
  have hca1 : cc ≠ a + 1 := by
    intro he; subst he
    exact (hsep.1 a (Minimality.zmod_ne_add_one (by omega) a)).ne (by
      simp only [X, Split.det3, PiLp.sub_apply]; ring)
  obtain ⟨⟨σ, hrows⟩, _⟩ := Split.splitRows_of_isDepthSeparatedAt (by omega) x u' c' hc' ht_rim a cc hsep
  exact Split.EV.split_core_ep (by omega) x hx hseg c' hc' u' ht_rim a cc σ hca hca1 hrows

/-- Conditional core form of `HoleLeaf` under `NoParRim x` (drops `¬ Gen.LexAny F`). -/
theorem holeLeaf_core_noPar {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hp : NoParRim x) :
    HoleLeaf x F ↔ CbarIn x ∧ ¬ BoxApplies (Finset.univ.image x) ∧
      ¬ Gen.EdgePlaneAny x ∧ ¬ FaceChord.FaceChordView F 3 := by
  rw [Atlas.holeLeaf_iff_core3]
  exact ⟨fun ⟨h1, h2, _, h4, h5⟩ => ⟨h1, h2, h4, h5⟩,
    fun ⟨h1, h2, h4, h5⟩ => ⟨h1, h2, fun hl => h4 (lexAny_edgePlaneAny_of_noPar F hp hl), h4, h5⟩⟩

end Minimality.T24.LexEP
