module

public import Minimality.Type24HoleCore3
public import Minimality.UnimodalSplit
public import Minimality.Type24NoCoplanar
public import Minimality.LexTiltSplit

/-!
# Task FG / FH2: `LexAny → EdgePlaneAny` for type 24 (unconditional)

Proves `lexAny_edgePlaneAny : Gen.LexAny F → Gen.EdgePlaneAny x` for any `F : S0xFac 9 s0x_S24 x`,
and removes `¬ Gen.LexAny F` from the core form of `HoleLeaf` (`holeLeaf_iff_core2`, `hole24_core2`).

Route:
1. `T24.Stmt.openCellRob_of_lexAny` gives an open-cell view `u` on a `k ≥ 4` cycle `c` with `RobUni`.
2. `strictRimN_of_openCell` gives `StrictRimN x u c'` (up to cycle reversal, preserving `RobUni`).
3. Tilt `u' = u + t • v` in the open `StrictRimN` cell to achieve: pairwise distinct depths,
   `HiddenInTriangles`, `⟪E_a, u'⟫ ≠ 0` for all `a`, spin non-degeneracy `⟪n_{a,j}, u'⟫ ≠ 0`,
   `RobUni` (open), and `det3 E_i E_j u' = 0 → E_j = (-lam) • E_i` (`lam > 0`) for `i ≠ j`.
4. Perturb `X` in `(u')^⊥` along a parabola `(2^i, 4^i)` to `X_ε`, apply
   `UnimodalSplit.isDepthSeparatedAt_of_unimodal` at `ε_n → 0`, take a pigeonhole `(a, c)` limit:
   - if `a` has no parallel rim edge, `IsDepthSeparatedAt X u' a c` holds directly (`split_core_ep`);
   - if `a` has an opposite parallel edge `j` (`E_j = -lam • E_a`), then `c ∈ {j, j + 1}`,
     giving strict depth separation between `(a, j]` and `(j, a]`, so `epRows_of_spinCancel_gen`
     certifies `EPRows X u' a s α μ` and hence `Gen.EdgePlaneAny x`.
-/

@[expose] public section

open scoped RealInnerProductSpace Topology
open Finset Filter
open Minimality Minimality.H21 Minimality.T24.SAT Minimality.T24.Z0 Minimality.T24.NC

namespace Minimality.T24.LexEP

private theorem s24_sep :
    ∀ i j : Fin 7, j ≠ i → ∃ t : Fin 9, i ∈ s0x_S24 t ∧ j ∉ s0x_S24 t := by decide

private lemma cross_eq_zero_iff_collinear {a b : ℝ³} (ha : a ≠ 0) :
    cross a b = 0 → ∃ c : ℝ, b = c • a := by
  intro hcr
  have hcr0 : a 1 * b 2 - a 2 * b 1 = 0 := by simpa [cross] using congrArg (fun v => v 0) hcr
  have hcr1 : a 2 * b 0 - a 0 * b 2 = 0 := by simpa [cross] using congrArg (fun v => v 1) hcr
  have hcr2 : a 0 * b 1 - a 1 * b 0 = 0 := by simpa [cross] using congrArg (fun v => v 2) hcr
  have ha012 : a 0 ≠ 0 ∨ a 1 ≠ 0 ∨ a 2 ≠ 0 := by
    by_contra h
    push Not at h
    apply ha
    ext i; fin_cases i <;> simp [h.1, h.2.1, h.2.2]
  rcases ha012 with h0 | h1 | h2
  · refine ⟨b 0 / a 0, ?_⟩
    ext i; fin_cases i <;> simp only [PiLp.smul_apply, smul_eq_mul, Fin.isValue, Fin.reduceFinMk]
    · exact (div_mul_cancel₀ _ h0).symm
    · field_simp [h0]; linarith [hcr2]
    · field_simp [h0]; linarith [hcr1]
  · refine ⟨b 1 / a 1, ?_⟩
    ext i; fin_cases i <;> simp only [PiLp.smul_apply, smul_eq_mul, Fin.isValue, Fin.reduceFinMk]
    · field_simp [h1]; linarith [hcr2]
    · exact (div_mul_cancel₀ _ h1).symm
    · field_simp [h1]; linarith [hcr0]
  · refine ⟨b 2 / a 2, ?_⟩
    ext i; fin_cases i <;> simp only [PiLp.smul_apply, smul_eq_mul, Fin.isValue, Fin.reduceFinMk]
    · field_simp [h2]; linarith [hcr1]
    · field_simp [h2]; linarith [hcr0]
    · exact (div_mul_cancel₀ _ h2).symm

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
  obtain ⟨m, _, hm_min⟩ := Finset.exists_min_image Finset.univ (fun i : ZMod k => ⟪X i, w⟫) Finset.univ_nonempty
  obtain ⟨M, _, hM_max⟩ := Finset.exists_max_image Finset.univ (fun i : ZMod k => ⟪X i, w⟫) Finset.univ_nonempty
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
        rw [hsM]; simp
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
      have hM_eq : m + ((M - m).val : ZMod k) = M := by simp
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

/-- **Task FH2 (spin cancellation for general `k ≥ 4`):** when edge `j ≠ a` satisfies
`E_j = (-lam) • E_a` (`lam > 0`), `edgePlaneSpin X w a j j = edgePlaneSpin X w a j (j + 1) ≠ 0`,
and if a line `α₀ + μ₀ * ⟪X r - X a, w⟫` strictly separates the `det3 > 0` rows from the `det3 < 0`
rows, then `(s, M * α₀, M * μ₀)` satisfies `Split.EV.EPRows X w a`. -/
theorem epRows_of_spinCancel_gen {k : ℕ} [NeZero k] (hk : 4 ≤ k)
    (X : ZMod k → ℝ³) (w : ℝ³) (a j0 : ZMod k) (lam : ℝ) (hlam : 0 < lam)
    (hw0 : w ≠ 0) (hj0a : j0 ≠ a)
    (hE : X (j0 + 1) - X j0 = (-lam) • (X (a + 1) - X a))
    (hD : ⟪X (a + 1) - X a, w⟫ ≠ 0)
    (hspin_ne : ⟪⟪X (a + 1) - X a, X (a + 1) - X a⟫ • (X j0 - X a) -
        ⟪X (a + 1) - X a, X j0 - X a⟫ • (X (a + 1) - X a), w⟫ ≠ 0)
    (α₀ μ₀ : ℝ)
    (hsep : ∀ i j : ZMod k, i ≠ a → i ≠ j0 → (j = i ∨ j = i + 1) →
      0 < (α₀ + μ₀ * ⟪X j - X a, w⟫) * Split.det3 (X (i + 1) - X i) (X (a + 1) - X a) w) :
    ∃ s α μ : ℝ, Split.EV.EPRows X w a s α μ := by
  have : Fact (1 < k) := ⟨by omega⟩
  set Ea := X (a + 1) - X a
  set Ej := X (j0 + 1) - X j0
  set V := X j0 - X a
  set D := ⟪Ea, w⟫
  have hww : 0 < ⟪w, w⟫ := real_inner_self_pos.2 hw0
  have hSjj : Split.edgePlaneSpin X w a j0 j0 =
      lam * ⟪w, w⟫ * ⟪⟪Ea, Ea⟫ • V - ⟪Ea, V⟫ • Ea, w⟫ / D := by
    simp only [Split.edgePlaneSpin]
    change Split.det3 Ej (cross w V) w + (⟪V, w⟫ / D) * Split.det3 Ej (cross Ea w) w = _
    rw [hE]
    have e1 : Split.det3 ((-lam) • Ea) (cross w V) w =
        -lam * (⟪w, w⟫ * ⟪Ea, V⟫ - ⟪V, w⟫ * D) := by
      simp only [D, Split.det3, Split.inner3, Split.cross_0, Split.cross_1, Split.cross_2,
        PiLp.smul_apply, smul_eq_mul]
      ring
    have e2 : Split.det3 ((-lam) • Ea) (cross Ea w) w =
        -lam * (D * D - ⟪w, w⟫ * ⟪Ea, Ea⟫) := by
      simp only [D, Split.det3, Split.inner3, Split.cross_0, Split.cross_1, Split.cross_2,
        PiLp.smul_apply, smul_eq_mul]
      ring
    have hlin : ⟪⟪Ea, Ea⟫ • V - ⟪Ea, V⟫ • Ea, w⟫ = ⟪Ea, Ea⟫ * ⟪V, w⟫ - ⟪Ea, V⟫ * D := by
      simp only [D, inner_sub_left, real_inner_smul_left]
    rw [e1, e2, hlin]
    field_simp [hD]
    ring
  have hSjj1 : Split.edgePlaneSpin X w a j0 (j0 + 1) = Split.edgePlaneSpin X w a j0 j0 := by
    simp only [Split.edgePlaneSpin]
    have hVj : X (j0 + 1) - X a = V + (-lam) • Ea := by
      calc X (j0 + 1) - X a = (X j0 - X a) + (X (j0 + 1) - X j0) := by abel
        _ = V + (-lam) • Ea := by rw [show X (j0 + 1) - X j0 = (-lam) • Ea from hE]
    change Split.det3 Ej (cross w (X (j0 + 1) - X a)) w +
      (⟪X (j0 + 1) - X a, w⟫ / D) * Split.det3 Ej (cross Ea w) w =
      Split.det3 Ej (cross w V) w + (⟪V, w⟫ / D) * Split.det3 Ej (cross Ea w) w
    rw [hVj, hE]
    have e1 : Split.det3 ((-lam) • Ea) (cross w (V + (-lam) • Ea)) w =
        Split.det3 ((-lam) • Ea) (cross w V) w +
        (-lam) * (⟪w, w⟫ * ((-lam) * ⟪Ea, Ea⟫) - ((-lam) * D) * D) := by
      simp only [D, Split.det3, Split.inner3, Split.cross_0, Split.cross_1, Split.cross_2,
        PiLp.smul_apply, PiLp.add_apply, smul_eq_mul]
      ring
    have e2 : Split.det3 ((-lam) • Ea) (cross Ea w) w =
        -lam * (D * D - ⟪w, w⟫ * ⟪Ea, Ea⟫) := by
      simp only [D, Split.det3, Split.inner3, Split.cross_0, Split.cross_1, Split.cross_2,
        PiLp.smul_apply, smul_eq_mul]
      ring
    have ew : ⟪V + (-lam) • Ea, w⟫ = ⟪V, w⟫ + (-lam) * D := by
      simp only [D, inner_add_left, real_inner_smul_left]
    rw [e1, ew, e2]
    field_simp [hD]
    ring
  have hSjj_ne : Split.edgePlaneSpin X w a j0 j0 ≠ 0 := by
    rw [hSjj]
    exact div_ne_zero (mul_ne_zero (mul_ne_zero hlam.ne' hww.ne') hspin_ne) hD
  let s : ℝ := if 0 < Split.edgePlaneSpin X w a j0 j0 then 1 else -1
  have hs_pos : 0 < s * Split.edgePlaneSpin X w a j0 j0 := by
    dsimp only [s]
    split_ifs with h
    · simpa using h
    · have hlt : Split.edgePlaneSpin X w a j0 j0 < 0 := lt_of_le_of_ne (not_lt.mp h) hSjj_ne
      nlinarith
  have hd_zero : Split.det3 Ej Ea w = 0 := by
    rw [hE]
    simp only [Split.det3, PiLp.smul_apply, smul_eq_mul]; ring
  let rowFin : Finset (ZMod k × ZMod k) :=
    (Finset.univ.filter fun p : ZMod k × ZMod k => p.1 ≠ a ∧ p.1 ≠ j0 ∧ (p.2 = p.1 ∨ p.2 = p.1 + 1))
  let ratio : ZMod k × ZMod k → ℝ := fun p =>
    |s * Split.edgePlaneSpin X w a p.1 p.2| /
      ((α₀ + μ₀ * ⟪X p.2 - X a, w⟫) * Split.det3 (X (p.1 + 1) - X p.1) Ea w)
  let fB : ZMod k × ZMod k → ℝ := fun p => if p.1 = a then 0 else ratio p
  let B : ℝ := (insert (a, a) rowFin).sup' (Finset.insert_nonempty _ _) fB
  have hB_nonneg : 0 ≤ B := by
    have h0 := Finset.le_sup' fB (Finset.mem_insert_self (a, a) rowFin)
    simpa [fB] using h0
  let M : ℝ := 1 + B
  have hM_pos : 0 < M := by linarith
  refine ⟨s, M * α₀, M * μ₀, fun i j hi hj => ?_⟩
  have hscale : (M * α₀ + (M * μ₀) * ⟪X j - X a, w⟫) * Split.det3 (X (i + 1) - X i) Ea w =
      M * ((α₀ + μ₀ * ⟪X j - X a, w⟫) * Split.det3 (X (i + 1) - X i) Ea w) := by ring
  by_cases hij0 : i = j0
  · subst hij0
    change 0 < (M * α₀ + (M * μ₀) * ⟪X j - X a, w⟫) * Split.det3 Ej Ea w + s * Split.edgePlaneSpin X w a i j
    rw [hd_zero, mul_zero, zero_add]
    rcases hj with rfl | rfl
    · exact hs_pos
    · rw [hSjj1]; exact hs_pos
  · have hp_mem : (i, j) ∈ rowFin := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi, hij0, hj⟩
    have hr_pos : 0 < (α₀ + μ₀ * ⟪X j - X a, w⟫) * Split.det3 (X (i + 1) - X i) Ea w :=
      hsep i j hi hij0 hj
    have hle_sup : ratio (i, j) ≤ B := by
      have h1 := Finset.le_sup' (s := insert (a, a) rowFin) fB (Finset.mem_insert_of_mem hp_mem)
      simpa [fB, hi] using h1
    have hlt_M : ratio (i, j) < M := by dsimp only [M]; linarith
    have hMr : |s * Split.edgePlaneSpin X w a i j| <
        M * ((α₀ + μ₀ * ⟪X j - X a, w⟫) * Split.det3 (X (i + 1) - X i) Ea w) := by
      have := (div_lt_iff₀ hr_pos).mp hlt_M
      linarith
    change 0 < (M * α₀ + (M * μ₀) * ⟪X j - X a, w⟫) * Split.det3 (X (i + 1) - X i) Ea w +
      s * Split.edgePlaneSpin X w a i j
    rw [hscale]
    linarith [neg_le_abs (s * Split.edgePlaneSpin X w a i j)]

private lemma hsr_of_sep {k : ℕ} [NeZero k] (hk : 4 ≤ k) (Y : ZMod k → ℝ³) (w : ℝ³)
    (hccw : Split.UnimodalSplit.StrictRimCcw Y w) (a c : ZMod k) (hsep : Split.IsDepthSeparatedAt Y w a c) :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
      ∀ i j : ZMod k, i ≠ a → j ≠ c → (j = i ∨ j = i + 1) →
        0 < σ * (⟪Y j, w⟫ - ⟪Y c, w⟫) * Split.det3 (Y (i + 1) - Y i) (Y (a + 1) - Y a) w := by
  have : Fact (1 < k) := ⟨by omega⟩
  have hca1 : a + 1 ≠ c := by
    intro h; subst h
    have h0 : Split.det3 (Y (a + 1) - Y a) w (Y a) = Split.det3 (Y (a + 1) - Y a) w (Y (a + 1)) := by
      simp only [Split.det3, PiLp.sub_apply]; ring
    linarith [hsep.1 a (Minimality.zmod_ne_add_one (by omega) a)]
  let labK : ZMod k → Fin k := fun i => ⟨i.val, ZMod.val_lt i⟩
  have hlabK : Function.Injective labK := fun i j h => ZMod.val_injective k (congrArg Fin.val h)
  let YK : Fin k → ℝ³ := fun i => Y (i.val : ZMod k)
  have hYK : ∀ i : ZMod k, YK (labK i) = Y i := fun i => by simp [YK, labK]
  have hrim : Split.StrictRimN YK w labK := fun m i h1 h2 => by
    let m' : ZMod k := (m.val : ZMod k)
    have hm' : labK m' = m := Fin.ext (by simp [labK, m', ZMod.val_natCast, Nat.mod_eq_of_lt m.isLt])
    rw [show YK m = Y m' from rfl, hYK, hYK]
    exact hccw i m' (fun e => h1 (by rw [← hm', e])) (fun e => h2 (by rw [← hm', e]))
  have hsepK : Split.IsDepthSeparatedAt (fun i => YK (labK i)) w a c := by
    simpa only [hYK] using hsep
  obtain ⟨⟨σ, hrows⟩, _⟩ := Split.splitRows_of_isDepthSeparatedAt (by omega) YK w labK
    hlabK hrim a c hsepK
  have hσ0 : σ ≠ 0 := by
    intro h0
    have := hrows (a + 1) (a + 1) (Minimality.zmod_ne_add_one (by omega) a).symm (Or.inl rfl) hca1
    rw [h0, zero_mul] at this
    exact lt_irrefl 0 this
  rcases lt_or_gt_of_ne hσ0 with hσ | hσ
  · refine ⟨-1, Or.inr rfl, fun i j hi hjc hj => ?_⟩
    have hr := hrows i j hi hj hjc
    simp only [hYK] at hr
    rw [inner_sub_left] at hr
    have : -1 * (⟪Y j, w⟫ - ⟪Y c, w⟫) * Split.det3 (Y (i + 1) - Y i) (Y (a + 1) - Y a) w =
        ((-1) / σ) * (σ * ((⟪Y j, w⟫ - ⟪Y c, w⟫) * Split.det3 (Y (i + 1) - Y i) (Y (a + 1) - Y a) w)) := by
      field_simp [hσ0]
    rw [this]
    exact mul_pos (div_pos_of_neg_of_neg (by norm_num) hσ) hr
  · refine ⟨1, Or.inl rfl, fun i j hi hjc hj => ?_⟩
    have hr := hrows i j hi hj hjc
    simp only [hYK] at hr
    rw [inner_sub_left] at hr
    have : 1 * (⟪Y j, w⟫ - ⟪Y c, w⟫) * Split.det3 (Y (i + 1) - Y i) (Y (a + 1) - Y a) w =
        (1 / σ) * (σ * ((⟪Y j, w⟫ - ⟪Y c, w⟫) * Split.det3 (Y (i + 1) - Y i) (Y (a + 1) - Y a) w)) := by
      field_simp [hσ0]
    rw [this]
    exact mul_pos (div_pos (by norm_num) hσ) hr

private lemma subcaseB_spin {k : ℕ} [NeZero k] (hk : 4 ≤ k)
    (X : ZMod k → ℝ³) (w : ℝ³) (hw0 : w ≠ 0) (a c j0 : ZMod k)
    (hca : c ≠ a) (hca1 : c ≠ a + 1) (hj0a : j0 ≠ a) (hcj0 : c = j0 ∨ c = j0 + 1)
    (lam : ℝ) (hlam : 0 < lam)
    (hE : X (j0 + 1) - X j0 = (-lam) • (X (a + 1) - X a))
    (hD : ⟪X (a + 1) - X a, w⟫ ≠ 0)
    (hspin : ⟪⟪X (a + 1) - X a, X (a + 1) - X a⟫ • (X j0 - X a) -
        ⟪X (a + 1) - X a, X j0 - X a⟫ • (X (a + 1) - X a), w⟫ ≠ 0)
    (hdist : ∀ i j : ZMod k, i ≠ j → ⟪X i, w⟫ ≠ ⟪X j, w⟫)
    (hdet_ne : ∀ i : ZMod k, i ≠ a → i ≠ j0 → Split.det3 (X (i + 1) - X i) (X (a + 1) - X a) w ≠ 0)
    (σ₀ : ℝ) (hσ₀ : σ₀ = 1 ∨ σ₀ = -1)
    (hlim_rows : ∀ i j : ZMod k, i ≠ a → j ≠ c → (j = i ∨ j = i + 1) →
      0 ≤ σ₀ * (⟪X j, w⟫ - ⟪X c, w⟫) * Split.det3 (X (i + 1) - X i) (X (a + 1) - X a) w) :
    ∃ s α μ : ℝ, Split.EV.EPRows X w a s α μ := by
  have : Fact (1 < k) := ⟨by omega⟩
  let d := X (a + 1) - X a
  let S_ne : Finset (ZMod k) := Finset.univ.filter (· ≠ c)
  have hS_ne : S_ne.Nonempty := ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hca.symm⟩⟩
  let gap : ℝ := S_ne.inf' hS_ne (fun r => |⟪X r, w⟫ - ⟪X c, w⟫|)
  have hgap : 0 < gap := by
    rw [Finset.lt_inf'_iff]
    intro r hr
    exact abs_pos.mpr (sub_ne_zero.mpr (hdist r c (Finset.mem_filter.mp hr).2))
  have hi₀_ex : ∃ i₀ : ZMod k, i₀ ≠ a ∧ i₀ ≠ j0 ∧ (c = i₀ ∨ c = i₀ + 1) := by
    rcases hcj0 with rfl | rfl
    · refine ⟨c - 1, ?_, ?_, Or.inr (by ring)⟩
      · intro h; apply hca1; linear_combination h
      · intro h
        have : (1 : ZMod k) = 0 := by linear_combination -h
        exact one_ne_zero this
    · refine ⟨j0 + 1, ?_, ?_, Or.inl rfl⟩
      · exact hca
      · exact (Minimality.zmod_ne_add_one (by omega) j0).symm
  obtain ⟨i₀, hi₀a, hi₀j0, hi₀c⟩ := hi₀_ex
  have hdi₀ : Split.det3 (X (i₀ + 1) - X i₀) d w ≠ 0 := hdet_ne i₀ hi₀a hi₀j0
  let sgni : ℝ := if 0 < Split.det3 (X (i₀ + 1) - X i₀) d w then 1 else -1
  let τ : ℝ := -σ₀ * sgni * (gap / 2)
  have hσ₀_sq : σ₀ * σ₀ = 1 := by rcases hσ₀ with rfl | rfl <;> norm_num
  have hsg_pos : 0 < sgni * Split.det3 (X (i₀ + 1) - X i₀) d w := by
    dsimp only [sgni]
    split_ifs with h
    · simpa using h
    · have hlt : Split.det3 (X (i₀ + 1) - X i₀) d w < 0 := lt_of_le_of_ne (not_lt.mp h) hdi₀
      nlinarith
  have hτ_abs : |τ| < gap := by
    have hsg_abs : |sgni| = 1 := by dsimp only [sgni]; split_ifs <;> norm_num
    have hσ_abs : |σ₀| = 1 := by rcases hσ₀ with rfl | rfl <;> norm_num
    dsimp only [τ]
    rw [abs_mul, abs_mul, abs_neg, hσ_abs, hsg_abs, one_mul, one_mul, abs_of_pos (by linarith)]
    linarith
  let μ₀ : ℝ := σ₀
  let α₀ : ℝ := σ₀ * (⟪X a, w⟫ - (⟪X c, w⟫ + τ))
  have hsep_spin : ∀ i j : ZMod k, i ≠ a → i ≠ j0 → (j = i ∨ j = i + 1) →
      0 < (α₀ + μ₀ * ⟪X j - X a, w⟫) * Split.det3 (X (i + 1) - X i) d w := by
    intro i j hi hij0 hj
    have hlin : α₀ + μ₀ * ⟪X j - X a, w⟫ = σ₀ * (⟪X j, w⟫ - ⟪X c, w⟫ - τ) := by
      dsimp only [α₀, μ₀]; rw [inner_sub_left]; ring
    rw [hlin]
    by_cases hjc : j = c
    · subst hjc
      have hi_eq : i = i₀ := by
        rcases hcj0 with hcj | hcj
        · rcases hj with rfl | h1
          · exact absurd hcj hij0
          · rcases hi₀c with h0 | h0
            · rw [hcj] at h0; exact absurd h0.symm hi₀j0
            · rw [h1] at h0; exact add_right_cancel h0
        · rcases hj with rfl | h1
          · rcases hi₀c with h0 | h0
            · exact h0
            · rw [hcj] at h0; exact absurd (add_right_cancel h0).symm hi₀j0
          · rw [hcj] at h1; exact absurd (add_right_cancel h1.symm) hij0
      subst hi_eq
      have hmul : σ₀ * (⟪X j, w⟫ - ⟪X j, w⟫ - τ) * Split.det3 (X (i + 1) - X i) d w =
          (σ₀ * σ₀) * (gap / 2) * (sgni * Split.det3 (X (i + 1) - X i) d w) := by
        dsimp only [τ]; ring
      rw [hmul, hσ₀_sq, one_mul]
      exact mul_pos (by linarith) hsg_pos
    · have hle := hlim_rows i j hi hjc hj
      have hdi : Split.det3 (X (i + 1) - X i) d w ≠ 0 := hdet_ne i hi hij0
      have hzc : ⟪X j, w⟫ - ⟪X c, w⟫ ≠ 0 := sub_ne_zero.mpr (hdist j c hjc)
      have hσ_ne : σ₀ ≠ 0 := by rcases hσ₀ with rfl | rfl <;> norm_num
      have hprod_ne : σ₀ * (⟪X j, w⟫ - ⟪X c, w⟫) * Split.det3 (X (i + 1) - X i) d w ≠ 0 :=
        mul_ne_zero (mul_ne_zero hσ_ne hzc) hdi
      have hpos : 0 < σ₀ * (⟪X j, w⟫ - ⟪X c, w⟫) * Split.det3 (X (i + 1) - X i) d w :=
        lt_of_le_of_ne hle hprod_ne.symm
      have hgap_j : gap ≤ |⟪X j, w⟫ - ⟪X c, w⟫| :=
        Finset.inf'_le (fun r => |⟪X r, w⟫ - ⟪X c, w⟫|) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjc⟩)
      set zj := ⟪X j, w⟫ - ⟪X c, w⟫
      set dj := Split.det3 (X (i + 1) - X i) d w
      have hsame_sign : 0 < zj * (zj - τ) := by
        rcases abs_cases zj with ⟨ha1, ha2⟩ | ⟨ha1, ha2⟩
        · have h1 : τ < zj := lt_of_lt_of_le (lt_of_le_of_lt (le_abs_self τ) hτ_abs) (by linarith)
          exact mul_pos (by linarith) (by linarith)
        · have h1 : zj < τ := lt_of_le_of_lt (by linarith)
            (lt_of_lt_of_le (neg_lt.mp (lt_of_le_of_lt (neg_le_abs τ) hτ_abs)) (by linarith))
          exact mul_pos_of_neg_of_neg (by linarith) (by linarith)
      have hmul : (σ₀ * (zj - τ) * dj) * (zj ^ 2) = (σ₀ * zj * dj) * (zj * (zj - τ)) := by ring
      have hsq_pos : 0 < zj ^ 2 := sq_pos_of_ne_zero hzc
      have hRHS_pos := mul_pos hpos hsame_sign
      rw [← hmul] at hRHS_pos
      exact pos_of_mul_pos_left hRHS_pos hsq_pos.le
  exact epRows_of_spinCancel_gen hk X w a j0 lam hlam hw0 hj0a hE hD hspin α₀ μ₀ hsep_spin

/-- **Perturbation + limit lemma (FH2):** Any strictly unimodal `k`-rim (`k ≥ 4`) with `StrictRimN`,
`HiddenInTriangles`, `hD ≠ 0`, `hspin_ne`, and where every `det3 E_i E_j w = 0` (`i ≠ j`) is an
antiparallel 3D pair `E_j = (-lam) • E_i` (`lam > 0`), yields `Gen.EdgePlaneAny x`. -/
theorem edgePlaneAny_of_unimodal_par {n k : ℕ} [NeZero k] (hk : 4 ≤ k) (x : Fin n → ℝ³)
    (hx : Function.Injective x) (hseg : Split.NoBetween x)
    (lab : ZMod k → Fin n) (hinj : Function.Injective lab) (w : ℝ³)
    (hrim : Split.StrictRimN x w lab) (hhid : Split.HiddenInTriangles x w lab)
    (m M : ZMod k)
    (hdist : ∀ i j : ZMod k, i ≠ j → ⟪x (lab i), w⟫ ≠ ⟪x (lab j), w⟫)
    (huni : Split.UnimodalSplit.StrictlyUnimodal (fun i => x (lab i)) w m M)
    (hD_all : ∀ a : ZMod k, ⟪x (lab (a + 1)) - x (lab a), w⟫ ≠ 0)
    (hpar_only : ∀ i j : ZMod k, i ≠ j →
      Split.det3 (x (lab (i + 1)) - x (lab i)) (x (lab (j + 1)) - x (lab j)) w = 0 →
      ∃ lam : ℝ, 0 < lam ∧ x (lab (j + 1)) - x (lab j) = (-lam) • (x (lab (i + 1)) - x (lab i)))
    (hspin_all : ∀ a j : ZMod k, j ≠ a →
      (∃ lam : ℝ, 0 < lam ∧ x (lab (j + 1)) - x (lab j) = (-lam) • (x (lab (a + 1)) - x (lab a))) →
      ⟪⟪x (lab (a + 1)) - x (lab a), x (lab (a + 1)) - x (lab a)⟫ • (x (lab j) - x (lab a)) -
        ⟪x (lab (a + 1)) - x (lab a), x (lab j) - x (lab a)⟫ • (x (lab (a + 1)) - x (lab a)), w⟫ ≠ 0) :
    Gen.EdgePlaneAny x := by
  classical
  have : Fact (1 < k) := ⟨by omega⟩
  let X : ZMod k → ℝ³ := fun i => x (lab i)
  have hw0 : w ≠ 0 := by
    intro h0
    have h1 := hD_all 0
    rw [h0, inner_zero_right] at h1
    exact h1 rfl
  -- Construct an orthogonal pair `e1, e2 ∈ w^⊥` with `det3 e1 e2 w ≠ 0`
  have hw012 : w 0 ≠ 0 ∨ w 1 ≠ 0 ∨ w 2 ≠ 0 := by
    by_contra h; push Not at h; apply hw0; ext i; fin_cases i <;> simp [h.1, h.2.1, h.2.2]
  let u₀ : ℝ³ := if w 0 ≠ 0 then !₂[0, 1, 0] else !₂[1, 0, 0]
  let e1 : ℝ³ := cross w u₀
  let e2 : ℝ³ := cross w e1
  have he1_ne : e1 ≠ 0 := by
    intro he
    have h0' : e1 0 = 0 := by rw [he]; simp
    have h1' : e1 1 = 0 := by rw [he]; simp
    have h2' : e1 2 = 0 := by rw [he]; simp
    dsimp only [e1] at h0' h1' h2'
    rw [Split.cross_0] at h0'
    rw [Split.cross_1] at h1'
    rw [Split.cross_2] at h2'
    dsimp only [u₀] at h0' h1' h2'
    split_ifs at h0' h1' h2' with h0
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
        mul_one, mul_zero, sub_zero] at h2'
      exact h0 h2'
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        mul_one, mul_zero, zero_sub, neg_eq_zero] at h1' h2'
      rcases hw012 with h | h | h
      · exact h0 h
      · exact h h2'
      · exact h (by simpa using h1')
  have he1_orth : ⟪e1, w⟫ = 0 := by
    dsimp only [e1]; simp only [Split.inner3, Split.cross_0, Split.cross_1, Split.cross_2]; ring
  have he2_orth : ⟪e2, w⟫ = 0 := by
    dsimp only [e2]; simp only [Split.inner3, Split.cross_0, Split.cross_1, Split.cross_2]; ring
  have hdet_e12 : Split.det3 e1 e2 w ≠ 0 := by
    have : Split.det3 e1 e2 w = ⟪e1, e1⟫ * ⟪w, w⟫ - ⟪e1, w⟫ ^ 2 := by
      dsimp only [e2]
      simp only [Split.det3, Split.inner3, Split.cross_0, Split.cross_1, Split.cross_2]; ring
    rw [this, he1_orth, sq, mul_zero, sub_zero]
    have hww : 0 < ⟪w, w⟫ := real_inner_self_pos.2 hw0
    have hee : 0 < ⟪e1, e1⟫ := real_inner_self_pos.2 he1_ne
    nlinarith
  -- Parabola perturbation `δ i = (2^i.val) • e1 + (4^i.val) • e2` in `w^⊥`
  let δ : ZMod k → ℝ³ := fun i => ((2 : ℝ) ^ i.val) • e1 + ((4 : ℝ) ^ i.val) • e2
  have hδ_orth : ∀ i : ZMod k, ⟪δ i, w⟫ = 0 := fun i => by
    dsimp only [δ]
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left, he1_orth, he2_orth,
      mul_zero, mul_zero, add_zero]
  have hδ_slope : ∀ i j : ZMod k, i ≠ j →
      Split.det3 (δ (i + 1) - δ i) (δ (j + 1) - δ j) w ≠ 0 := by
    have hslope_ne : ∀ i j : ZMod k, i ≠ j →
        ((2 : ℝ) ^ (i + 1).val - (2 : ℝ) ^ i.val) * ((4 : ℝ) ^ (j + 1).val - (4 : ℝ) ^ j.val) -
        ((4 : ℝ) ^ (i + 1).val - (4 : ℝ) ^ i.val) * ((2 : ℝ) ^ (j + 1).val - (2 : ℝ) ^ j.val) ≠ 0 := by
      intro i j hij h0
      have hsucc : ∀ r : ZMod k, ((2 : ℝ) ^ (r + 1).val - (2 : ℝ) ^ r.val) ≠ 0 := fun r => by
        have hne : (r + 1).val ≠ r.val := fun h => by
          have := ZMod.val_injective k h
          exact (Minimality.zmod_ne_add_one (by omega) r).symm this
        intro e
        have heq : (2 : ℝ) ^ (r + 1).val = (2 : ℝ) ^ r.val := sub_eq_zero.1 e
        have := StrictMono.injective (fun a b (hab : a < b) =>
          pow_lt_pow_right₀ (by norm_num : (1 : ℝ) < 2) hab) heq
        exact hne this
      have hslope_eq : ∀ r : ZMod k,
          ((4 : ℝ) ^ (r + 1).val - (4 : ℝ) ^ r.val) / ((2 : ℝ) ^ (r + 1).val - (2 : ℝ) ^ r.val) =
            (2 : ℝ) ^ (r + 1).val + (2 : ℝ) ^ r.val := fun r => by
        have h1 : (4 : ℝ) ^ (r + 1).val - (4 : ℝ) ^ r.val =
            ((2 : ℝ) ^ (r + 1).val - (2 : ℝ) ^ r.val) * ((2 : ℝ) ^ (r + 1).val + (2 : ℝ) ^ r.val) := by
          have ha : (4 : ℝ) ^ (r + 1).val = ((2 : ℝ) ^ (r + 1).val) ^ 2 := by
            rw [← pow_mul, mul_comm, pow_mul]; norm_num
          have hb : (4 : ℝ) ^ r.val = ((2 : ℝ) ^ r.val) ^ 2 := by
            rw [← pow_mul, mul_comm, pow_mul]; norm_num
          rw [ha, hb]; ring
        rw [h1, mul_div_cancel_left₀ _ (hsucc r)]
      have hsum_eq : (2 : ℝ) ^ (i + 1).val + (2 : ℝ) ^ i.val =
          (2 : ℝ) ^ (j + 1).val + (2 : ℝ) ^ j.val := by
        have hi := hsucc i
        have hj := hsucc j
        rw [← hslope_eq i, ← hslope_eq j]
        field_simp [hi, hj]
        linarith
      -- Two sums of powers of 2 `(2^a + 2^b = 2^c + 2^d)` with `a ≠ b, c ≠ d` in `ℕ`:
      have hnat_eq : (2 : ℕ) ^ (i + 1).val + 2 ^ i.val = 2 ^ (j + 1).val + 2 ^ j.val := by
        exact_mod_cast hsum_eq
      have hval_i : (i + 1).val = i.val + 1 ∨ (i.val = k - 1 ∧ (i + 1).val = 0) := by
        rcases eq_or_ne (i.val + 1) k with h | h
        · right; refine ⟨by omega, ?_⟩
          have : i + 1 = ((i.val + 1 : ℕ) : ZMod k) := by push_cast; simp
          rw [this, h, ZMod.natCast_self, ZMod.val_zero]
        · left
          have hlt : i.val + 1 < k := by have := ZMod.val_lt i; omega
          have : i + 1 = ((i.val + 1 : ℕ) : ZMod k) := by push_cast; simp
          rw [this, ZMod.val_natCast, Nat.mod_eq_of_lt hlt]
      have hval_j : (j + 1).val = j.val + 1 ∨ (j.val = k - 1 ∧ (j + 1).val = 0) := by
        rcases eq_or_ne (j.val + 1) k with h | h
        · right; refine ⟨by omega, ?_⟩
          have : j + 1 = ((j.val + 1 : ℕ) : ZMod k) := by push_cast; simp
          rw [this, h, ZMod.natCast_self, ZMod.val_zero]
        · left
          have hlt : j.val + 1 < k := by have := ZMod.val_lt j; omega
          have : j + 1 = ((j.val + 1 : ℕ) : ZMod k) := by push_cast; simp
          rw [this, ZMod.val_natCast, Nat.mod_eq_of_lt hlt]
      rcases hval_i with hi1 | ⟨hi1, hi2⟩ <;> rcases hval_j with hj1 | ⟨hj1, hj2⟩
      · rw [hi1, hj1] at hnat_eq
        have : 3 * 2 ^ i.val = 3 * 2 ^ j.val := by
          have h1 : 2 ^ (i.val + 1) + 2 ^ i.val = 3 * 2 ^ i.val := by ring
          have h2 : 2 ^ (j.val + 1) + 2 ^ j.val = 3 * 2 ^ j.val := by ring
          omega
        have hpow : 2 ^ i.val = 2 ^ j.val := by omega
        have hijv : i.val = j.val := Nat.pow_right_injective (by norm_num) hpow
        exact hij (ZMod.val_injective k hijv)
      · rw [hi1, hj1, hj2, pow_zero] at hnat_eq
        have heven : 2 ^ (k - 1) ≥ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
        have h3 : 3 * 2 ^ i.val = 2 ^ (k - 1) + 1 := by
          have h1 : 2 ^ (i.val + 1) + 2 ^ i.val = 3 * 2 ^ i.val := by ring
          omega
        rcases eq_or_ne i.val 0 with hi0 | hi0
        · rw [hi0, pow_zero] at h3; omega
        · have hdvd : 2 ∣ 3 * 2 ^ i.val := dvd_mul_of_dvd_right (dvd_pow_self 2 hi0) 3
          have hdvd2 : 2 ∣ 2 ^ (k - 1) + 1 := h3 ▸ hdvd
          have hdvd1 : 2 ∣ 2 ^ (k - 1) := dvd_pow_self 2 (by omega)
          have : 2 ∣ 1 := (Nat.dvd_add_right hdvd1).1 hdvd2
          omega
      · rw [hi1, hi2, hj1, pow_zero] at hnat_eq
        have heven : 2 ^ (k - 1) ≥ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
        have h3 : 3 * 2 ^ j.val = 2 ^ (k - 1) + 1 := by
          have h1 : 2 ^ (j.val + 1) + 2 ^ j.val = 3 * 2 ^ j.val := by ring
          omega
        rcases eq_or_ne j.val 0 with hj0 | hj0
        · rw [hj0, pow_zero] at h3; omega
        · have hdvd : 2 ∣ 3 * 2 ^ j.val := dvd_mul_of_dvd_right (dvd_pow_self 2 hj0) 3
          have hdvd2 : 2 ∣ 2 ^ (k - 1) + 1 := h3 ▸ hdvd
          have hdvd1 : 2 ∣ 2 ^ (k - 1) := dvd_pow_self 2 (by omega)
          have : 2 ∣ 1 := (Nat.dvd_add_right hdvd1).1 hdvd2
          omega
      · exact hij (ZMod.val_injective k (by omega))
    intro i j hij hdet
    have hlin : Split.det3 (δ (i + 1) - δ i) (δ (j + 1) - δ j) w =
        (((2 : ℝ) ^ (i + 1).val - (2 : ℝ) ^ i.val) * ((4 : ℝ) ^ (j + 1).val - (4 : ℝ) ^ j.val) -
        ((4 : ℝ) ^ (i + 1).val - (4 : ℝ) ^ i.val) * ((2 : ℝ) ^ (j + 1).val - (2 : ℝ) ^ j.val)) *
          Split.det3 e1 e2 w := by
      dsimp only [δ]
      simp only [Split.det3, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      ring
    rw [hlin] at hdet
    rcases mul_eq_zero.mp hdet with h | h
    · exact hslope_ne i j hij h
    · exact hdet_e12 h
  -- For small `ε > 0`, `X_ε = fun i => X i + ε • δ i` satisfies `StrictRimCcw` and `NoParallelRimEdges`
  let Xε : ℝ → ZMod k → ℝ³ := fun ε i => X i + ε • δ i
  have hccw0 : Split.UnimodalSplit.StrictRimCcw X w :=
    Split.UnimodalSplit.strictRimCcw_of_strictRimN x w lab hinj hrim
  have hev_ccw : ∀ᶠ ε in 𝓝[>] (0 : ℝ), Split.UnimodalSplit.StrictRimCcw (Xε ε) w := by
    have key : ∀ i j : ZMod k, j ≠ i → j ≠ i + 1 →
        ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < Split.det3 (Xε ε (i + 1) - Xε ε i) (Xε ε j - Xε ε i) w := by
      intro i j hij1 hij2
      have hc0 : 0 < Split.det3 (X (i + 1) - X i) (X j - X i) w := hccw0 i j hij1 hij2
      have hcont : Continuous (fun ε : ℝ => Split.det3 (Xε ε (i + 1) - Xε ε i) (Xε ε j - Xε ε i) w) := by
        dsimp only [Xε, Split.det3]; fun_prop
      exact (hcont.continuousWithinAt.eventually (lt_mem_nhds (by simpa [Xε] using hc0)))
    have hall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ i j : ZMod k,
        j ≠ i → j ≠ i + 1 → 0 < Split.det3 (Xε ε (i + 1) - Xε ε i) (Xε ε j - Xε ε i) w := by
      have h1 := Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j =>
        if h : j ≠ i ∧ j ≠ i + 1 then (key i j h.1 h.2).mono fun _ hε _ _ => hε
        else Filter.Eventually.of_forall fun _ h1 h2 => absurd ⟨h1, h2⟩ h
      exact h1
    exact hall
  have hev_npar : ∀ᶠ ε in 𝓝[>] (0 : ℝ), Split.UnimodalSplit.NoParallelRimEdges (Xε ε) w := by
    have key : ∀ i j : ZMod k, i ≠ j →
        ∀ᶠ ε in 𝓝[>] (0 : ℝ), Split.det3 (Xε ε (i + 1) - Xε ε i) (Xε ε (j + 1) - Xε ε j) w ≠ 0 := by
      intro i j hij
      let A := Split.det3 (X (i + 1) - X i) (X (j + 1) - X j) w
      let B := Split.det3 (X (i + 1) - X i) (δ (j + 1) - δ j) w +
        Split.det3 (δ (i + 1) - δ i) (X (j + 1) - X j) w
      let C := Split.det3 (δ (i + 1) - δ i) (δ (j + 1) - δ j) w
      have hC : C ≠ 0 := hδ_slope i j hij
      have heq : ∀ ε : ℝ, Split.det3 (Xε ε (i + 1) - Xε ε i) (Xε ε (j + 1) - Xε ε j) w =
          A + ε * B + ε ^ 2 * C := fun ε => by
        dsimp only [Xε, A, B, C]
        simp only [Split.det3, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
      -- A quadratic `A + ε B + ε^2 C` with `C ≠ 0` is nonzero for `ε ∈ (0, ε₀)`
      by_cases hA : A ≠ 0
      · have hcont : Continuous (fun ε : ℝ => A + ε * B + ε ^ 2 * C) := by fun_prop
        exact (hcont.continuousWithinAt.eventually_ne (by simpa using hA)).mono fun ε hε => by
          rw [heq]; exact hε
      · push Not at hA
        by_cases hB : B ≠ 0
        · have hcont : ContinuousAt (fun ε : ℝ => B + ε * C) 0 := (continuous_const.add (continuous_id.mul continuous_const)).continuousAt
          have hev_nz : ∀ᶠ ε in 𝓝[>] (0 : ℝ), B + ε * C ≠ 0 :=
            (hcont.eventually_ne (by simpa using hB)).filter_mono nhdsWithin_le_nhds
          filter_upwards [hev_nz, self_mem_nhdsWithin] with ε hε1 (hε0 : 0 < ε)
          rw [heq, hA, zero_add]
          have : ε * B + ε ^ 2 * C = ε * (B + ε * C) := by ring
          rw [this]
          exact mul_ne_zero hε0.ne' hε1
        · push Not at hB
          filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
          rw [heq, hA, hB, mul_zero, add_zero, zero_add]
          exact mul_ne_zero (pow_ne_zero 2 hε.ne') hC
    exact Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j =>
      if h : i ≠ j then (key i j h).mono fun _ hε _ => hε
      else Filter.Eventually.of_forall fun _ hij => absurd hij h
  obtain ⟨δ₀, hδ₀, hδ_ball⟩ := Metric.mem_nhdsWithin_iff.mp (hev_ccw.and hev_npar)
  have hδ_both : ∀ {ε : ℝ}, ε ∈ Set.Ioo 0 δ₀ →
      Split.UnimodalSplit.StrictRimCcw (Xε ε) w ∧ Split.UnimodalSplit.NoParallelRimEdges (Xε ε) w :=
    fun {ε} hε => hδ_ball ⟨mem_ball_zero_iff.mpr (by rw [Real.norm_eq_abs, abs_of_pos hε.1]; exact hε.2), hε.1⟩
  -- Sample `ε_n = δ₀ / (n + 2) ∈ (0, δ₀)` and apply `isDepthSeparatedAt_of_unimodal`
  have hXε_z : ∀ ε : ℝ, ∀ i : ZMod k, ⟪Xε ε i, w⟫ = ⟪X i, w⟫ := fun ε i => by
    dsimp only [Xε]
    rw [inner_add_left, real_inner_smul_left, hδ_orth, mul_zero, add_zero]
  have hdist_ε : ∀ ε : ℝ, ∀ i j : ZMod k, i ≠ j → ⟪Xε ε i, w⟫ ≠ ⟪Xε ε j, w⟫ := fun ε i j hij => by
    rw [hXε_z, hXε_z]; exact hdist i j hij
  have huni_ε : ∀ ε : ℝ, Split.UnimodalSplit.StrictlyUnimodal (Xε ε) w m M := fun _ =>
    ⟨huni.1, fun s hs => by simpa only [hXε_z] using huni.2.1 s hs,
      fun s hs1 hs2 => by simpa only [hXε_z] using huni.2.2 s hs1 hs2⟩
  let eps : ℕ → ℝ := fun n => δ₀ / ((n : ℝ) + 2)
  have heps_mem : ∀ n : ℕ, eps n ∈ Set.Ioo 0 δ₀ := fun n => by
    have hn : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    refine ⟨div_pos hδ₀ hn, ?_⟩
    rw [div_lt_iff₀ hn]
    nlinarith
  have hsep_n : ∀ n : ℕ, ∃ p : ZMod k × ZMod k, Split.IsDepthSeparatedAt (Xε (eps n)) w p.1 p.2 := by
    intro n
    have ⟨hccw_n, hnpar_n⟩ := hδ_both (heps_mem n)
    obtain ⟨a, c, hs⟩ := Split.UnimodalSplit.isDepthSeparatedAt_of_unimodal hk (Xε (eps n)) w m M
      hccw_n (hdist_ε (eps n)) (huni_ε (eps n)) hnpar_n
    exact ⟨(a, c), hs⟩
  choose pair hpair using hsep_n
  obtain ⟨⟨a, c⟩, hinf⟩ := Finite.exists_infinite_fiber pair
  let S_inf : Set ℕ := pair ⁻¹' {(a, c)}
  have hS_inf : Set.Infinite S_inf := Set.infinite_coe_iff.mp hinf
  obtain ⟨n₀, hn₀⟩ := hS_inf.nonempty
  have hsep₀ : Split.IsDepthSeparatedAt (Xε (eps n₀)) w a c := by
    have h := hpair n₀
    have hn₀' : pair n₀ = (a, c) := hn₀
    rw [hn₀'] at h
    exact h
  have hdepth_arcs :
      (((∀ s : ℕ, 0 < s → s ≤ (a - c).val → ⟪X c, w⟫ < ⟪X (c + s), w⟫) ∧
          ∀ s : ℕ, (a - c).val < s → s < k → ⟪X (c + s), w⟫ < ⟪X c, w⟫) ∨
        ((∀ s : ℕ, 0 < s → s ≤ (a - c).val → ⟪X (c + s), w⟫ < ⟪X c, w⟫) ∧
          ∀ s : ℕ, (a - c).val < s → s < k → ⟪X c, w⟫ < ⟪X (c + s), w⟫)) := by
    simpa only [hXε_z] using hsep₀.2
  -- Limit `ε_n → 0` along `S_inf` gives `det3 (X (a+1) - X a) w (X c) ≤ det3 (X (a+1) - X a) w (X i)`
  have hlim_min : ∀ i : ZMod k,
      Split.det3 (X (a + 1) - X a) w (X c) ≤ Split.det3 (X (a + 1) - X a) w (X i) := by
    intro i
    by_cases hic : i = c
    · subst hic; exact le_rfl
    · let F_lim : Filter ℕ := Filter.atTop ⊓ Filter.principal S_inf
      have : F_lim.NeBot := Filter.inf_principal_neBot_iff.mpr fun s hs => by
        obtain ⟨N, hN⟩ := Filter.mem_atTop_sets.mp hs
        obtain ⟨n, hnS, hnN⟩ := hS_inf.exists_gt N
        exact ⟨n, hN n hnN.le, hnS⟩
      have heps_tend : Filter.Tendsto eps F_lim (𝓝 0) :=
        (tendsto_const_nhds.div_atTop
          (Filter.tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)).mono_left inf_le_left
      have hLHS : Filter.Tendsto (fun n => Split.det3 (Xε (eps n) (a + 1) - Xε (eps n) a) w (Xε (eps n) c))
          F_lim (𝓝 (Split.det3 (X (a + 1) - X a) w (X c))) := by
        have hcont : Continuous (fun ε : ℝ => Split.det3 (Xε ε (a + 1) - Xε ε a) w (Xε ε c)) := by
          dsimp only [Xε, Split.det3]; fun_prop
        have h0 : Split.det3 (Xε 0 (a + 1) - Xε 0 a) w (Xε 0 c) =
            Split.det3 (X (a + 1) - X a) w (X c) := by simp [Xε]
        rw [← h0]
        exact (hcont.continuousAt (x := (0 : ℝ))).tendsto.comp heps_tend
      have hRHS : Filter.Tendsto (fun n => Split.det3 (Xε (eps n) (a + 1) - Xε (eps n) a) w (Xε (eps n) i))
          F_lim (𝓝 (Split.det3 (X (a + 1) - X a) w (X i))) := by
        have hcont : Continuous (fun ε : ℝ => Split.det3 (Xε ε (a + 1) - Xε ε a) w (Xε ε i)) := by
          dsimp only [Xε, Split.det3]; fun_prop
        have h0 : Split.det3 (Xε 0 (a + 1) - Xε 0 a) w (Xε 0 i) =
            Split.det3 (X (a + 1) - X a) w (X i) := by simp [Xε]
        rw [← h0]
        exact (hcont.continuousAt (x := (0 : ℝ))).tendsto.comp heps_tend
      have hle_ev : ∀ᶠ n in F_lim,
          Split.det3 (Xε (eps n) (a + 1) - Xε (eps n) a) w (Xε (eps n) c) ≤
          Split.det3 (Xε (eps n) (a + 1) - Xε (eps n) a) w (Xε (eps n) i) := by
        filter_upwards [Filter.mem_inf_of_right (Filter.mem_principal_self S_inf)] with n hn
        have h := hpair n
        rw [show pair n = (a, c) from hn] at h
        exact (h.1 i hic).le
      exact le_of_tendsto_of_tendsto hLHS hRHS hle_ev
  -- 2D convex polygon projection perpendicular to `w` along edge `a`
  let d := X (a + 1) - X a
  let N := cross d w
  let p : ZMod k → ℝ² := fun i => Split.projP N w (X i)
  have hp_ccw : 0 < ⟪N, N⟫ ∧ Minimality.IsCcwPolygon p := by
    have hj : ∃ j : ZMod k, j ≠ a ∧ j ≠ a + 1 := by
      refine ⟨a + 2, ?_, ?_⟩
      · have := Minimality.zmod_add_ne (k := k) (a := 0) (b := 2) (by omega) (by omega) (by decide) a
        simpa using this.symm
      · have := Minimality.zmod_add_ne (k := k) (a := 1) (b := 2) (by omega) (by omega) (by decide) a
        simpa using this.symm
    obtain ⟨j, hj1, hj2⟩ := hj
    have hrj := hccw0 a j hj1 hj2
    have hN0 : N ≠ 0 := by
      intro hN
      have h0 : Split.det3 d (X j - X a) w = -⟪N, X j - X a⟫ := by
        have h1 : Split.det3 d (X j - X a) w = -Split.det3 d w (X j - X a) := by
          simp only [Split.det3]; ring
        rw [h1, Split.det3_eq_inner]
      rw [hN, inner_zero_left, neg_zero] at h0
      linarith
    have hnn0 : 0 < ⟪N, N⟫ := (real_inner_self_nonneg (x := N)).lt_of_ne' (fun h => hN0 (inner_self_eq_zero.mp h))
    refine ⟨hnn0, (by omega : 3 ≤ k), fun i l hli hl1 => ?_⟩
    change 0 < Minimality.cross2 (Split.projP N w (X (i + 1)) - Split.projP N w (X i))
      (Split.projP N w (X l) - Split.projP N w (X i))
    rw [Split.projP_sub, Split.projP_sub, Split.cross2_projP]
    exact mul_pos hnn0 (hccw0 i l hli hl1)
  obtain ⟨_, hp⟩ := hp_ccw
  let ν : ℝ² := !₂[-1, 0]
  have hν : ν ≠ 0 := by
    intro h; have := congrArg (fun v => v 0) h; simp [ν] at this
  have hinner : ∀ i : ZMod k, ⟪ν, p i⟫ = -Split.det3 d w (X i) := fun i => by
    have h1 : ⟪ν, p i⟫ = -(p i 0) := by simp [ν, PiLp.inner_apply, Fin.sum_univ_two]
    have h2 : p i 0 = ⟪X i, N⟫ := by simp [p, Split.projP]
    have h3 : ⟪X i, N⟫ = Split.det3 d w (X i) := by
      rw [real_inner_comm]; exact (Split.det3_eq_inner d w (X i)).symm
    linarith
  have hcmax' : ∀ i : ZMod k, ⟪ν, p i⟫ ≤ ⟪ν, p c⟫ := fun i => by
    linarith [hinner i, hinner c, hlim_min i]
  have hj2 : a + 2 ≠ a ∧ a + 2 ≠ a + 1 := by
    refine ⟨?_, ?_⟩
    · have := Minimality.zmod_add_ne (k := k) (a := 0) (b := 2) (by omega) (by omega) (by decide) a
      simpa using this.symm
    · have := Minimality.zmod_add_ne (k := k) (a := 1) (b := 2) (by omega) (by omega) (by decide) a
      simpa using this.symm
  have ha_lt_j : ⟪ν, p a⟫ < ⟪ν, p (a + 2)⟫ := by
    have hpos := hccw0 a (a + 2) hj2.1 hj2.2
    have h1 : Split.det3 d (X (a + 2) - X a) w = -(Split.det3 d w (X (a + 2)) - Split.det3 d w (X a)) := by
      simp only [Split.det3, PiLp.sub_apply]; ring
    rw [h1] at hpos
    linarith [hinner a, hinner (a + 2)]
  have ha_eq_a1 : ⟪ν, p (a + 1)⟫ = ⟪ν, p a⟫ := by
    have h0 : Split.det3 d w (X (a + 1)) - Split.det3 d w (X a) = 0 := by
      dsimp only [d]; simp only [Split.det3, PiLp.sub_apply]; ring
    linarith [hinner a, hinner (a + 1)]
  have hca : c ≠ a := by intro h; rw [h] at hcmax'; linarith [hcmax' (a + 2)]
  have hca1 : c ≠ a + 1 := by intro h; rw [h] at hcmax'; linarith [hcmax' (a + 2)]
  by_cases hpar_a : ∃ j0 : ZMod k, j0 ≠ a ∧ Split.det3 (X (j0 + 1) - X j0) d w = 0
  · -- Subcase B: `a` has an opposite parallel edge `j0` (`E_{j0} = -lam • E_a`), spin cancellation!
    obtain ⟨j0, hj0a, hj0_det⟩ := hpar_a
    have hj0_det' : Split.det3 d (X (j0 + 1) - X j0) w = 0 := by
      have : Split.det3 d (X (j0 + 1) - X j0) w = -Split.det3 (X (j0 + 1) - X j0) d w := by
        simp only [Split.det3]; ring
      rw [this, hj0_det, neg_zero]
    obtain ⟨lam, hlam, hE⟩ := hpar_only a j0 hj0a.symm hj0_det'
    have hcj0 : c = j0 ∨ c = j0 + 1 := by
      have h0_le : 0 ≤ Split.det3 (X (j0 + 1) - X j0) (X c - X j0) w := by
        by_cases hc1 : c = j0
        · subst hc1; simp [Split.det3]
        · by_cases hc2 : c = j0 + 1
          · subst hc2; simp only [Split.det3, PiLp.sub_apply]; ring_nf; exact le_rfl
          · exact (hccw0 j0 c hc1 hc2).le
      rw [hE] at h0_le
      have hmul : 0 ≤ (-lam) * Split.det3 d (X c - X j0) w := by
        have h1 : Split.det3 ((-lam) • d) (X c - X j0) w = (-lam) * Split.det3 d (X c - X j0) w := by
          simp only [Split.det3, PiLp.smul_apply, smul_eq_mul]; ring
        linarith
      have hjc_le : Split.det3 d w (X j0) ≤ Split.det3 d w (X c) := by
        have h1 : Split.det3 d (X c - X j0) w = -(Split.det3 d w (X c) - Split.det3 d w (X j0)) := by
          simp only [Split.det3, PiLp.sub_apply]; ring
        rw [h1] at hmul
        nlinarith
      have heq_j : ⟪ν, p j0⟫ = ⟪ν, p c⟫ := by
        linarith [hinner j0, hinner c, hlim_min j0, hjc_le]
      rcases hp.max_adjacent hν hcmax' heq_j with h | h | h
      · exact Or.inr (by linear_combination -h)
      · exact Or.inl h.symm
      · exfalso
        have hne1 : j0 + 1 ≠ j0 - 1 := (Minimality.zmod_sub_one_ne_add_one (by omega) j0).symm
        have hne2 : j0 + 1 ≠ j0 - 1 + 1 := by
          have : j0 - 1 + 1 = j0 := by ring
          rw [this]; exact (Minimality.zmod_ne_add_one (by omega) j0).symm
        have hpos := hccw0 (j0 - 1) (j0 + 1) hne1 hne2
        have e1 : j0 - 1 + 1 = j0 := by ring
        rw [e1] at hpos
        have e2 : X (j0 + 1) - X (j0 - 1) = (X j0 - X (j0 - 1)) + (X (j0 + 1) - X j0) := by abel
        rw [e2, hE] at hpos
        have e3 : Split.det3 (X j0 - X (j0 - 1)) ((X j0 - X (j0 - 1)) + (-lam) • d) w =
            (-lam) * Split.det3 (X j0 - X (j0 - 1)) d w := by
          simp only [Split.det3, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
        rw [e3] at hpos
        have e4 : Split.det3 (X j0 - X (j0 - 1)) d w = Split.det3 d w (X j0) - Split.det3 d w (X (j0 - 1)) := by
          simp only [Split.det3, PiLp.sub_apply]; ring
        rw [e4] at hpos
        have hlt : Split.det3 d w (X j0) < Split.det3 d w (X (j0 - 1)) := by nlinarith
        have hcj : c = j0 - 1 := by linear_combination -h
        rw [hcj] at hlim_min
        linarith [hlim_min j0]
    -- Get `SplitRows (Xε (eps n)) w a c σ_n` for all `n ∈ S_inf`, pick a constant sign `σ₀ ∈ {1, -1}`
    have hsr_n : ∀ n ∈ S_inf, ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
        ∀ i j : ZMod k, i ≠ a → j ≠ c → (j = i ∨ j = i + 1) →
          0 < σ * (⟪X j, w⟫ - ⟪X c, w⟫) *
            Split.det3 (Xε (eps n) (i + 1) - Xε (eps n) i) (Xε (eps n) (a + 1) - Xε (eps n) a) w := by
      intro n hn
      have ⟨hccw_n, _⟩ := hδ_both (heps_mem n)
      have hsep_n' := hpair n
      rw [show pair n = (a, c) from hn] at hsep_n'
      obtain ⟨σ, hσ, hrows⟩ := hsr_of_sep hk (Xε (eps n)) w hccw_n a c hsep_n'
      refine ⟨σ, hσ, fun i j hi hjc hj => ?_⟩
      simpa only [hXε_z] using hrows i j hi hjc hj
    -- Either `σ = 1` or `σ = -1` holds for infinitely many `n ∈ S_inf`
    let S_pos : Set ℕ := {n ∈ S_inf | ∀ i j : ZMod k, i ≠ a → j ≠ c → (j = i ∨ j = i + 1) →
      0 < 1 * (⟪X j, w⟫ - ⟪X c, w⟫) *
        Split.det3 (Xε (eps n) (i + 1) - Xε (eps n) i) (Xε (eps n) (a + 1) - Xε (eps n) a) w}
    let S_neg : Set ℕ := {n ∈ S_inf | ∀ i j : ZMod k, i ≠ a → j ≠ c → (j = i ∨ j = i + 1) →
      0 < (-1) * (⟪X j, w⟫ - ⟪X c, w⟫) *
        Split.det3 (Xε (eps n) (i + 1) - Xε (eps n) i) (Xε (eps n) (a + 1) - Xε (eps n) a) w}
    have hS_union : S_inf ⊆ S_pos ∪ S_neg := by
      intro n hn
      obtain ⟨σ, hσ, hrows⟩ := hsr_n n hn
      rcases hσ with rfl | rfl
      · exact Or.inl ⟨hn, hrows⟩
      · exact Or.inr ⟨hn, hrows⟩
    have hS_choice : (∃ σ₀ : ℝ, (σ₀ = 1 ∨ σ₀ = -1) ∧ ∃ S' : Set ℕ, Set.Infinite S' ∧ ∀ n ∈ S',
        ∀ i j : ZMod k, i ≠ a → j ≠ c → (j = i ∨ j = i + 1) →
          0 < σ₀ * (⟪X j, w⟫ - ⟪X c, w⟫) *
            Split.det3 (Xε (eps n) (i + 1) - Xε (eps n) i) (Xε (eps n) (a + 1) - Xε (eps n) a) w) := by
      by_cases hpi : Set.Infinite S_pos
      · exact ⟨1, Or.inl rfl, S_pos, hpi, fun n hn => hn.2⟩
      · have hni : Set.Infinite S_neg := by
          intro hnf
          exact hS_inf (((Set.not_infinite.mp hpi).union hnf).subset hS_union)
        exact ⟨-1, Or.inr rfl, S_neg, hni, fun n hn => hn.2⟩
    obtain ⟨σ₀, hσ₀, S', hS', hS'_rows⟩ := hS_choice
    -- Take limit along `S'` as `n → ∞`
    have hlim_rows : ∀ i j : ZMod k, i ≠ a → j ≠ c → (j = i ∨ j = i + 1) →
        0 ≤ σ₀ * (⟪X j, w⟫ - ⟪X c, w⟫) * Split.det3 (X (i + 1) - X i) d w := by
      intro i j hi hjc hj
      let F_lim : Filter ℕ := Filter.atTop ⊓ Filter.principal S'
      have : F_lim.NeBot := Filter.inf_principal_neBot_iff.mpr fun s hs => by
        obtain ⟨N, hN⟩ := Filter.mem_atTop_sets.mp hs
        obtain ⟨n, hnS, hnN⟩ := hS'.exists_gt N
        exact ⟨n, hN n hnN.le, hnS⟩
      have heps_tend : Filter.Tendsto eps F_lim (𝓝 0) :=
        (tendsto_const_nhds.div_atTop
          (Filter.tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)).mono_left inf_le_left
      have hRHS : Filter.Tendsto (fun n => σ₀ * (⟪X j, w⟫ - ⟪X c, w⟫) *
            Split.det3 (Xε (eps n) (i + 1) - Xε (eps n) i) (Xε (eps n) (a + 1) - Xε (eps n) a) w)
          F_lim (𝓝 (σ₀ * (⟪X j, w⟫ - ⟪X c, w⟫) * Split.det3 (X (i + 1) - X i) d w)) := by
        have hcont : Continuous (fun ε : ℝ => σ₀ * (⟪X j, w⟫ - ⟪X c, w⟫) *
            Split.det3 (Xε ε (i + 1) - Xε ε i) (Xε ε (a + 1) - Xε ε a) w) := by
          dsimp only [Xε, Split.det3]; fun_prop
        have h0 : σ₀ * (⟪X j, w⟫ - ⟪X c, w⟫) *
            Split.det3 (Xε 0 (i + 1) - Xε 0 i) (Xε 0 (a + 1) - Xε 0 a) w =
            σ₀ * (⟪X j, w⟫ - ⟪X c, w⟫) * Split.det3 (X (i + 1) - X i) d w := by
          dsimp only [d]; simp [Xε]
        rw [← h0]
        exact (hcont.continuousAt (x := (0 : ℝ))).tendsto.comp heps_tend
      have hle_ev : ∀ᶠ n in F_lim, (0 : ℝ) ≤ σ₀ * (⟪X j, w⟫ - ⟪X c, w⟫) *
            Split.det3 (Xε (eps n) (i + 1) - Xε (eps n) i) (Xε (eps n) (a + 1) - Xε (eps n) a) w := by
        filter_upwards [Filter.mem_inf_of_right (Filter.mem_principal_self S')] with n hn
        exact (hS'_rows n hn i j hi hjc hj).le
      exact le_of_tendsto_of_tendsto tendsto_const_nhds hRHS hle_ev
    -- For `i ∉ {a, j0}`, `det3 (X (i+1) - X i) d w ≠ 0`
    have hdet_ne : ∀ i : ZMod k, i ≠ a → i ≠ j0 → Split.det3 (X (i + 1) - X i) d w ≠ 0 := by
      intro i hi hij0 hdet
      have hdet' : Split.det3 d (X (i + 1) - X i) w = 0 := by
        have : Split.det3 d (X (i + 1) - X i) w = -Split.det3 (X (i + 1) - X i) d w := by
          simp only [Split.det3]; ring
        rw [this, hdet, neg_zero]
      obtain ⟨lami, hlami, hEi⟩ := hpar_only a i hi.symm hdet'
      -- `X (i+1) - X i` and `X (j0+1) - X j0` are both negative multiples of `d`, so positive multiples of each other:
      have hpos_ij : X (i + 1) - X i = (lami / lam) • (X (j0 + 1) - X j0) := by
        rw [hE, hEi, smul_smul]; congr 1; field_simp [hlam.ne']
      -- Impossible in `StrictRimCcw` for `i ≠ j0`:
      by_cases hij1 : j0 = i + 1
      · subst hij1
        have hne1 : i + 2 ≠ i := by
          have := Minimality.zmod_add_ne (k := k) (a := 0) (b := 2) (by omega) (by omega) (by decide) i
          simpa using this.symm
        have hne2 : i + 2 ≠ i + 1 := by
          have := Minimality.zmod_add_ne (k := k) (a := 1) (b := 2) (by omega) (by omega) (by decide) i
          simpa using this.symm
        have h1 := hccw0 i (i + 2) hne1 hne2
        have e2 : X (i + 2) - X i = (X (i + 1) - X i) + (X (i + 1 + 1) - X (i + 1)) := by
          rw [show (i + 2 : ZMod k) = i + 1 + 1 by ring]; abel
        rw [e2, hpos_ij] at h1
        have : Split.det3 ((lami / lam) • (X (i + 1 + 1) - X (i + 1)))
            ((lami / lam) • (X (i + 1 + 1) - X (i + 1)) + (X (i + 1 + 1) - X (i + 1))) w = 0 := by
          simp only [Split.det3, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
        linarith
      · by_cases hji1 : i = j0 + 1
        · subst hji1
          have hne1 : j0 + 2 ≠ j0 := by
            have := Minimality.zmod_add_ne (k := k) (a := 0) (b := 2) (by omega) (by omega) (by decide) j0
            simpa using this.symm
          have hne2 : j0 + 2 ≠ j0 + 1 := by
            have := Minimality.zmod_add_ne (k := k) (a := 1) (b := 2) (by omega) (by omega) (by decide) j0
            simpa using this.symm
          have h1 := hccw0 j0 (j0 + 2) hne1 hne2
          have e2 : X (j0 + 2) - X j0 = (X (j0 + 1) - X j0) + (X (j0 + 1 + 1) - X (j0 + 1)) := by
            rw [show (j0 + 2 : ZMod k) = j0 + 1 + 1 by ring]; abel
          rw [e2, hpos_ij] at h1
          have : Split.det3 (X (j0 + 1) - X j0)
              ((X (j0 + 1) - X j0) + (lami / lam) • (X (j0 + 1) - X j0)) w = 0 := by
            simp only [Split.det3, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
          linarith
        · have h1 := hccw0 i j0 hij0.symm hij1
          have h2 := hccw0 j0 i hij0 hji1
          rw [hpos_ij] at h1
          have h3 : Split.det3 ((lami / lam) • (X (j0 + 1) - X j0)) (X j0 - X i) w =
              -(lami / lam) * Split.det3 (X (j0 + 1) - X j0) (X i - X j0) w := by
            simp only [Split.det3, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; ring
          rw [h3] at h1
          have hpos_div : 0 < lami / lam := div_pos hlami hlam
          nlinarith
    obtain ⟨s, α, μ, hrow⟩ := subcaseB_spin hk X w hw0 a c j0 hca hca1 hj0a hcj0 lam hlam hE
      (hD_all a) (hspin_all a j0 hj0a ⟨lam, hlam, hE⟩) hdist hdet_ne σ₀ hσ₀ hlim_rows
    exact ⟨k, inferInstance, lab, w, a, s, α, μ, by omega, hinj, hrim, hhid, hD_all a, hrow⟩
  · -- Subcase A: no parallel edge to `a`, so `IsDepthSeparatedAt X w a c` holds directly!
    have hstrict : ∀ i : ZMod k, i ≠ c → Split.det3 d w (X c) < Split.det3 d w (X i) := by
      intro i hic
      have hle := hcmax' i
      rcases lt_or_eq_of_le hle with hlt | heq
      · linarith [hinner i, hinner c]
      · exfalso
        have hadj := hp.max_adjacent hν hcmax' heq
        rcases hadj with rfl | rfl | rfl
        · have hia : c - 1 ≠ a := fun h => hca1 (by linear_combination h)
          have h0 : Split.det3 (X (c - 1 + 1) - X (c - 1)) d w = 0 := by
            have hc1 : c - 1 + 1 = c := by ring
            have hswap : Split.det3 (X c - X (c - 1)) d w = Split.det3 d w (X c) - Split.det3 d w (X (c - 1)) := by
              simp only [Split.det3, PiLp.sub_apply]; ring
            rw [hc1, hswap]
            linarith [hinner c, hinner (c - 1)]
          exact hpar_a ⟨c - 1, hia, h0⟩
        · exact absurd rfl hic
        · have h0 : Split.det3 (X (c + 1) - X c) d w = 0 := by
            have hswap : Split.det3 (X (c + 1) - X c) d w = Split.det3 d w (X (c + 1)) - Split.det3 d w (X c) := by
              simp only [Split.det3, PiLp.sub_apply]; ring
            rw [hswap]
            linarith [hinner c, hinner (c + 1)]
          exact hpar_a ⟨c, hca, h0⟩
    have hsep_X : Split.IsDepthSeparatedAt X w a c := ⟨hstrict, hdepth_arcs⟩
    obtain ⟨⟨σ, hrows⟩, _⟩ := Split.splitRows_of_isDepthSeparatedAt (by omega) x w lab
      hinj hrim a c hsep_X
    exact Split.EV.split_core_ep (by omega) x hx hseg lab hinj w hrim a c σ hca hca1 hrows

/-- **Unconditional Type 24 `LexAny → EdgePlaneAny` (Task FG / FH2).** -/
theorem lexAny_edgePlaneAny {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (h : Gen.LexAny F) :
    Gen.EdgePlaneAny x := by
  have hx := EdgeViewLink.inj_of_fac24 F
  obtain ⟨k, hne, c, U, Dn, u, hk, hc, hcyc, hu, hrob⟩ := T24.Stmt.openCellRob_of_lexAny h
  have hc' : ∃ (c' : ZMod k → Fin 7), Function.Injective c' ∧ Split.StrictRimN x u c' ∧
      RobUni (fun i => ⟪x (c' i), u⟫) := by
    rcases strictRimN_of_openCell (by omega) F hc hcyc hu with hr | hr
    · exact ⟨c, hc, hr, hrob⟩
    · exact ⟨fun i => c (-i), fun i j e => neg_injective (hc e), hr, robUni_rev hrob⟩
  obtain ⟨c', hc', hrim, hrob'⟩ := hc'
  let X : ZMod k → ℝ³ := fun i => x (c' i)
  have hseg := Split.noBetween_of_fac F s24_sep
  have hd1 : ∀ i : ZMod k, X (i + 1) - X i ≠ 0 := fun i h0 => by
    have h2 : i + 2 ≠ i := by
      have := Minimality.zmod_add_ne (k := k) (a := 0) (b := 2) (by omega) (by omega) (by decide) i
      simpa using this.symm
    have h21 : i + 2 ≠ i + 1 := by
      have := Minimality.zmod_add_ne (k := k) (a := 1) (b := 2) (by omega) (by omega) (by decide) i
      simpa using this.symm
    have hpos := hrim (c' (i + 2)) i (fun e => h2 (hc' e)) (fun e => h21 (hc' e))
    rw [show x (c' (i + 1)) - x (c' i) = X (i + 1) - X i from rfl, h0] at hpos
    simp [Split.det3] at hpos
  let mOff := (Finset.univ : Finset (Fin 7)).filter (fun m => ∀ j : ZMod k, m ≠ c' j)
  let triVec : {m : Fin 7 // m ∈ mOff} × ZMod k → ℝ³ := fun ⟨m, j⟩ =>
    cross (x (c' j) - x (c' 0)) (x m.1 - x (c' 0))
  let spinVec : ZMod k × ZMod k → ℝ³ := fun ⟨a, j⟩ =>
    ⟪X (a + 1) - X a, X (a + 1) - X a⟫ • (X j - X a) -
      ⟪X (a + 1) - X a, X j - X a⟫ • (X (a + 1) - X a)
  let pairs := (Finset.univ : Finset (ZMod k × ZMod k)).filter (fun p => p.1 ≠ p.2)
  let spinPairs := (Finset.univ : Finset (ZMod k × ZMod k)).filter (fun p => p.2 ≠ p.1 ∧ p.2 ≠ p.1 + 1)
  let Fset : Finset ℝ³ :=
    (pairs.image fun p => X p.1 - X p.2) ∪
    ((Finset.univ : Finset (ZMod k)).image fun a => X (a + 1) - X a) ∪
    ((pairs.image fun p => cross (X (p.1 + 1) - X p.1) (X (p.2 + 1) - X p.2)).filter (· ≠ 0)) ∪
    (spinPairs.image spinVec) ∪
    (((Finset.univ : Finset ({m : Fin 7 // m ∈ mOff} × ZMod k)).image triVec).filter (· ≠ 0))
  have hFset : ∀ y ∈ Fset, y ≠ 0 := by
    intro y hy
    simp only [Fset, pairs, spinPairs, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
      Finset.mem_univ, true_and] at hy
    rcases hy with ((((⟨p, hpne, rfl⟩ | ⟨a, rfl⟩) | ⟨⟨p, _, rfl⟩, hcr⟩) | ⟨p, hp, rfl⟩) | ⟨⟨p, _⟩, hy0⟩)
    · rw [sub_ne_zero]; intro he; exact hpne (hc' (hx he))
    · exact hd1 a
    · exact hcr
    · intro hs0
      have hpos := hrim (c' p.2) p.1 (fun e => hp.1 (hc' e)) (fun e => hp.2 (hc' e))
      have h00 : Split.det3 (X (p.1 + 1) - X p.1) (spinVec p) u =
          ⟪X (p.1 + 1) - X p.1, X (p.1 + 1) - X p.1⟫ *
            Split.det3 (X (p.1 + 1) - X p.1) (X p.2 - X p.1) u := by
        dsimp only [spinVec]
        simp only [Split.det3, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; ring
      rw [hs0] at h00
      have hz : Split.det3 (X (p.1 + 1) - X p.1) 0 u = 0 := by simp [Split.det3]
      rw [hz] at h00
      have hE_sq : 0 < ⟪X (p.1 + 1) - X p.1, X (p.1 + 1) - X p.1⟫ := real_inner_self_pos.2 (hd1 p.1)
      nlinarith
    · exact hy0
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
  have hhid : Split.HiddenInTriangles x u' c' := by
    refine Split.hidden_of_rim (by omega) x hx hseg u' c' hc' ht_rim fun m hm j _ hcr => ?_
    rw [Split.det3_eq_inner_cross]
    have hm_mem : m ∈ mOff := Finset.mem_filter.mpr ⟨Finset.mem_univ m, hm⟩
    have hmem : triVec ⟨⟨m, hm_mem⟩, j⟩ ∈ Fset :=
      Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), hcr⟩)
    exact hu'_ne _ hmem
  have hdist : ∀ i j : ZMod k, i ≠ j → ⟪X i, u'⟫ ≠ ⟪X j, u'⟫ := by
    intro i j hij heq
    have hmem : X i - X j ∈ Fset :=
      Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_union_left _ (Finset.mem_image.mpr
          ⟨(i, j), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩, rfl⟩))))
    apply hu'_ne _ hmem
    rw [inner_sub_left, heq, sub_self]
  have hD_all : ∀ a : ZMod k, ⟪X (a + 1) - X a, u'⟫ ≠ 0 := fun a =>
    hu'_ne _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ a))))))
  have hpar_only : ∀ i j : ZMod k, i ≠ j →
      Split.det3 (X (i + 1) - X i) (X (j + 1) - X j) u' = 0 →
      ∃ lam : ℝ, 0 < lam ∧ X (j + 1) - X j = (-lam) • (X (i + 1) - X i) := by
    intro i j hij hdet
    have hcr : cross (X (i + 1) - X i) (X (j + 1) - X j) = 0 := by
      by_contra hcr_ne
      have hmem : cross (X (i + 1) - X i) (X (j + 1) - X j) ∈ Fset :=
        Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨Finset.mem_image.mpr
            ⟨(i, j), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩, rfl⟩, hcr_ne⟩)))
      apply hu'_ne _ hmem
      rw [← Split.det3_eq_inner_cross]
      exact hdet
    obtain ⟨κ, hκ⟩ := cross_eq_zero_iff_collinear (hd1 i) hcr
    have hκ_ne : κ ≠ 0 := by
      intro h0; rw [h0, zero_smul] at hκ; exact hd1 j hκ
    have hκ_neg : κ < 0 := by
      by_contra hge
      have hκ_pos : 0 < κ := lt_of_le_of_ne (not_lt.mp hge) hκ_ne.symm
      by_cases hij1 : j = i + 1
      · subst hij1
        have hne1 : i + 2 ≠ i := by
          have := Minimality.zmod_add_ne (k := k) (a := 0) (b := 2) (by omega) (by omega) (by decide) i
          simpa using this.symm
        have hne2 : i + 2 ≠ i + 1 := by
          have := Minimality.zmod_add_ne (k := k) (a := 1) (b := 2) (by omega) (by omega) (by decide) i
          simpa using this.symm
        have hpos := ht_rim (c' (i + 2)) i (fun e => hne1 (hc' e)) (fun e => hne2 (hc' e))
        have e2 : x (c' (i + 2)) - x (c' i) = (X (i + 1) - X i) + (X (i + 1 + 1) - X (i + 1)) := by
          rw [show (i + 2 : ZMod k) = i + 1 + 1 by ring]; dsimp only [X]; abel
        change 0 < Split.det3 (X (i + 1) - X i) (x (c' (i + 2)) - x (c' i)) u' at hpos
        rw [e2, hκ] at hpos
        have : Split.det3 (X (i + 1) - X i) ((X (i + 1) - X i) + κ • (X (i + 1) - X i)) u' = 0 := by
          simp only [Split.det3, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
        linarith
      · by_cases hji1 : i = j + 1
        · subst hji1
          have hne1 : j + 2 ≠ j := by
            have := Minimality.zmod_add_ne (k := k) (a := 0) (b := 2) (by omega) (by omega) (by decide) j
            simpa using this.symm
          have hne2 : j + 2 ≠ j + 1 := by
            have := Minimality.zmod_add_ne (k := k) (a := 1) (b := 2) (by omega) (by omega) (by decide) j
            simpa using this.symm
          have hpos := ht_rim (c' (j + 2)) j (fun e => hne1 (hc' e)) (fun e => hne2 (hc' e))
          have e2 : x (c' (j + 2)) - x (c' j) = (X (j + 1) - X j) + (X (j + 1 + 1) - X (j + 1)) := by
            rw [show (j + 2 : ZMod k) = j + 1 + 1 by ring]; dsimp only [X]; abel
          change 0 < Split.det3 (X (j + 1) - X j) (x (c' (j + 2)) - x (c' j)) u' at hpos
          rw [e2, hκ] at hpos
          have : Split.det3 (κ • (X (j + 1 + 1) - X (j + 1)))
              (κ • (X (j + 1 + 1) - X (j + 1)) + (X (j + 1 + 1) - X (j + 1))) u' = 0 := by
            simp only [Split.det3, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
          linarith
        · have h1 := ht_rim (c' j) i (fun e => hij.symm (hc' e)) (fun e => hij1 (hc' e))
          have h2 := ht_rim (c' i) j (fun e => hij (hc' e)) (fun e => hji1 (hc' e))
          change 0 < Split.det3 (X (i + 1) - X i) (X j - X i) u' at h1
          change 0 < Split.det3 (X (j + 1) - X j) (X i - X j) u' at h2
          rw [hκ] at h2
          have h3 : Split.det3 (κ • (X (i + 1) - X i)) (X i - X j) u' =
              -κ * Split.det3 (X (i + 1) - X i) (X j - X i) u' := by
            simp only [Split.det3, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; ring
          rw [h3] at h2
          nlinarith
    exact ⟨-κ, neg_pos.2 hκ_neg, by simpa using hκ⟩
  have hspin_all : ∀ a j : ZMod k, j ≠ a →
      (∃ lam : ℝ, 0 < lam ∧ X (j + 1) - X j = (-lam) • (X (a + 1) - X a)) →
      ⟪spinVec (a, j), u'⟫ ≠ 0 := by
    intro a j hja ⟨lam, _, hE⟩
    have hja1 : j ≠ a + 1 := by
      intro he; subst he
      have hne1 : a + 2 ≠ a := by
        have := Minimality.zmod_add_ne (k := k) (a := 0) (b := 2) (by omega) (by omega) (by decide) a
        simpa using this.symm
      have hne2 : a + 2 ≠ a + 1 := by
        have := Minimality.zmod_add_ne (k := k) (a := 1) (b := 2) (by omega) (by omega) (by decide) a
        simpa using this.symm
      have hpos := ht_rim (c' (a + 2)) a (fun e => hne1 (hc' e)) (fun e => hne2 (hc' e))
      have e2 : x (c' (a + 2)) - x (c' a) = (X (a + 1) - X a) + (X (a + 1 + 1) - X (a + 1)) := by
        rw [show (a + 2 : ZMod k) = a + 1 + 1 by ring]; dsimp only [X]; abel
      change 0 < Split.det3 (X (a + 1) - X a) (x (c' (a + 2)) - x (c' a)) u' at hpos
      rw [e2, hE] at hpos
      have : Split.det3 (X (a + 1) - X a) ((X (a + 1) - X a) + (-lam) • (X (a + 1) - X a)) u' = 0 := by
        simp only [Split.det3, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
      linarith
    exact hu'_ne _ (Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨(a, j), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hja, hja1⟩, rfl⟩)))
  obtain ⟨m, M, huni⟩ := strictlyUnimodal_of_robUni (by omega) X u' hdist ht_rob
  exact edgePlaneAny_of_unimodal_par hk x hx hseg c' hc' u' ht_rim hhid m M hdist huni
    hD_all hpar_only hspin_all

/-- **Core form of `HoleLeaf` without `¬ Gen.LexAny F`:** Box, Edge-Plane, and the quad-circle face chord. -/
theorem holeLeaf_iff_core2 {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x} :
    HoleLeaf x F ↔ CbarIn x ∧ ¬ BoxApplies (Finset.univ.image x) ∧
      ¬ Gen.EdgePlaneAny x ∧ ¬ FaceChord.FaceChordView F 3 := by
  rw [Atlas.holeLeaf_iff_core3]
  exact ⟨fun ⟨h1, h2, _, h4, h5⟩ => ⟨h1, h2, h4, h5⟩,
    fun ⟨h1, h2, h4, h5⟩ => ⟨h1, h2, fun hl => h4 (lexAny_edgePlaneAny F hl), h4, h5⟩⟩

/-- `Hole24` implies the 2-conjunct-free core form. -/
theorem hole24_core2 {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x} (h : Hole24 x F) :
    CbarIn x ∧ ¬ BoxApplies (Finset.univ.image x) ∧
      ¬ Gen.EdgePlaneAny x ∧ ¬ FaceChord.FaceChordView F 3 :=
  holeLeaf_iff_core2.1 h.1

end Minimality.T24.LexEP
