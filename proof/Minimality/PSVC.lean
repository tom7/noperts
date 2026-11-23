module

public import Minimality.SVC

@[expose] public section

/-!
# Pair closure (PAIRLEAN): two views coupled by the Gram symmetry

Generalises `SVC.single_view_closure` to two views `w1`, `w2`. A *decomposition* of a view `w`
is a list `d` of index pairs `(i, j)` with `w = ∑ c_ij (x i - x j)`, all `c_ij > 0`
(`DecOK`). Then `⟪w, u⟫ = ∑ c_ij (z_i(u) - z_j(u))` for the depths at any view `u`, so the
depth order at `u` can give `⟪w, u⟫` a sign (evidence). Two couplings follow from the metric:
* SELF: a decomposition of `w` with every term negative at `w`'s own order contradicts
  `0 ≤ ⟪w, w⟫`;
* GRAM: positive evidence for `⟪w1, w2⟫` and negative evidence (from a decomposition of
  `w1` read at the order of `w2`, or of `w2` read at the order of `w1`) contradict.
Decompositions come from vertices with three facets (`corner_coords`, sign of each coefficient
= minus the facing of the opposite facet) and from triangle facets edge-on at the view
(`tri_coords`).

The finite check is split in two Bool functions (`check2`: every order at `w2` is excluded,
passes a rim, or is in the list `B2`; `check1`: every order at `w1` is excluded, passes a rim,
or is killed by GRAM against every order of `B2`), both closed by `decide +kernel`.
-/

set_option autoImplicit false

open scoped RealInnerProductSpace
open Minimality Minimality.H21

namespace Minimality.PSVC

open Minimality.SVC

/-! ### Decompositions -/

/-- `w = ∑ c_k (x (P i_k) - x (P j_k))` over the list `d`, all `c_k > 0`. -/
def DecOK {n p : ℕ} (x : Fin n → ℝ³) (P : Fin p → Fin n) (w : ℝ³)
    (d : List (Fin p × Fin p)) : Prop :=
  ∃ cs : List ℝ, cs.length = d.length ∧ (∀ c ∈ cs, 0 < c) ∧
    w = (List.zipWith (fun c ij => c • (x (P ij.1) - x (P ij.2))) cs d).sum

/-- The term of `σ • (x a - x c)` (`σ` the sign of the coefficient). -/
def termOf {p : ℕ} (σ : SignType) (a c : Fin p) : List (Fin p × Fin p) :=
  if σ = 1 then [(a, c)] else if σ = -1 then [(c, a)] else []

/-- Decomposition at a vertex `c` with neighbours `a k` and opposite facets `T k`. -/
def cornerDec {m p : ℕ} (sw : Fin m → SignType) (c : Fin p) (a : Fin 3 → Fin p)
    (T : Fin 3 → Fin m) : List (Fin p × Fin p) :=
  termOf (-sw (T 0)) (a 0) c ++ termOf (-sw (T 1)) (a 1) c ++ termOf (-sw (T 2)) (a 2) c

/-- Decomposition of a view in the plane of a triangle `p q r`, base `r`, opposite facets
`op` (of `p`) and `oq` (of `q`). -/
def triDec {m p : ℕ} (sw : Fin m → SignType) (r a b : Fin p) (oa ob : Fin m) :
    List (Fin p × Fin p) :=
  termOf (-sw oa) a r ++ termOf (-sw ob) b r

theorem decOK_nil {n p : ℕ} (x : Fin n → ℝ³) (P : Fin p → Fin n) : DecOK x P 0 [] :=
  ⟨[], rfl, by simp, by simp⟩

theorem decOK_append {n p : ℕ} {x : Fin n → ℝ³} {P : Fin p → Fin n} {w1 w2 : ℝ³}
    {d1 d2 : List (Fin p × Fin p)} (h1 : DecOK x P w1 d1) (h2 : DecOK x P w2 d2) :
    DecOK x P (w1 + w2) (d1 ++ d2) := by
  obtain ⟨c1, l1, p1, e1⟩ := h1
  obtain ⟨c2, l2, p2, e2⟩ := h2
  refine ⟨c1 ++ c2, by simp [l1, l2], fun c hc => ?_, ?_⟩
  · rcases List.mem_append.mp hc with h | h
    · exact p1 c h
    · exact p2 c h
  · rw [List.zipWith_append l1, List.sum_append, ← e1, ← e2]

theorem decOK_term {n p : ℕ} (x : Fin n → ℝ³) (P : Fin p → Fin n) (lam : ℝ) (a c : Fin p) :
    DecOK x P (lam • (x (P a) - x (P c))) (termOf (SignType.sign lam) a c) := by
  rcases lt_trichotomy lam 0 with h | h | h
  · have hs : SignType.sign lam = -1 := sign_neg h
    rw [hs]
    refine ⟨[-lam], rfl, by simpa using h, ?_⟩
    simp only [termOf, show ((-1 : SignType) = 1) = False by decide, ite_false, ite_true,
      List.zipWith_cons_cons, List.zipWith_nil_right, List.sum_cons, List.sum_nil, add_zero]
    rw [neg_smul, ← smul_neg, neg_sub]
  · subst h
    rw [sign_zero, zero_smul]
    exact decOK_nil x P
  · have hs : SignType.sign lam = 1 := sign_pos h
    rw [hs]
    refine ⟨[lam], rfl, by simpa using h, ?_⟩
    simp [termOf]

/-- Inner product of a list sum. -/
theorem inner_list_sum (l : List ℝ³) (u : ℝ³) :
    ⟪l.sum, u⟫ = (l.map fun v => ⟪v, u⟫).sum := by
  induction l with
  | nil => simp
  | cons v l ih => simp [inner_add_left, ih]

/-- Evaluation of a decomposed view against `u`. -/
theorem decOK_inner {n p : ℕ} {x : Fin n → ℝ³} {P : Fin p → Fin n} {w : ℝ³}
    {d : List (Fin p × Fin p)} (cs : List ℝ) (hl : cs.length = d.length)
    (he : w = (List.zipWith (fun c ij => c • (x (P ij.1) - x (P ij.2))) cs d).sum) (u : ℝ³) :
    ⟪w, u⟫ = (List.zipWith (fun c ij => c * (⟪x (P ij.1), u⟫ - ⟪x (P ij.2), u⟫)) cs d).sum := by
  subst he
  rw [inner_list_sum]
  induction cs generalizing d with
  | nil => simp
  | cons c cs ih =>
    cases d with
    | nil => simp at hl
    | cons ij d =>
      simp only [List.zipWith_cons_cons, List.map_cons, List.sum_cons]
      rw [ih (by simpa using hl), real_inner_smul_left, inner_sub_left]

/-- A list of positive coefficients times positive (negative) differences. -/
theorem zipWith_pos {p : ℕ} (cs : List ℝ) (d : List (Fin p × Fin p)) (g : Fin p × Fin p → ℝ)
    (hl : cs.length = d.length) (hc : ∀ c ∈ cs, 0 < c) (hg : ∀ ij ∈ d, 0 < g ij)
    (hne : d ≠ []) : 0 < (List.zipWith (fun c ij => c * g ij) cs d).sum := by
  induction cs generalizing d with
  | nil => cases d with
    | nil => exact absurd rfl hne
    | cons _ _ => simp at hl
  | cons c cs ih =>
    cases d with
    | nil => simp at hl
    | cons ij d =>
      simp only [List.zipWith_cons_cons, List.sum_cons]
      have h1 : 0 < c * g ij := mul_pos (hc c (by simp)) (hg ij (by simp))
      by_cases hd : d = []
      · subst hd; simp [h1]
      · have := ih d (by simpa using hl) (fun c' h => hc c' (by simp [h]))
          (fun ij' h => hg ij' (by simp [h])) hd
        linarith

/-- A list of positive coefficients times negative values has negative sum. -/
theorem zipWith_neg {p : ℕ} (cs : List ℝ) (d : List (Fin p × Fin p)) (g : Fin p × Fin p → ℝ)
    (hl : cs.length = d.length) (hc : ∀ c ∈ cs, 0 < c) (hg : ∀ ij ∈ d, g ij < 0)
    (hne : d ≠ []) : (List.zipWith (fun c ij => c * g ij) cs d).sum < 0 := by
  induction cs generalizing d with
  | nil => cases d with
    | nil => exact absurd rfl hne
    | cons _ _ => simp at hl
  | cons c cs ih =>
    cases d with
    | nil => simp at hl
    | cons ij d =>
      simp only [List.zipWith_cons_cons, List.sum_cons]
      have h1 : c * g ij < 0 := mul_neg_of_pos_of_neg (hc c (by simp)) (hg ij (by simp))
      by_cases hd : d = []
      · subst hd; simp [h1]
      · have := ih d (by simpa using hl) (fun c' h => hc c' (by simp [h]))
          (fun ij' h => hg ij' (by simp [h])) hd
        linarith

/-! ### Evidence -/

/-- All terms of `d` positive at the order `L` (and `d ≠ []`). -/
def evPos {p : ℕ} (L : List (Fin p)) (d : List (Fin p × Fin p)) : Bool :=
  !d.isEmpty && d.all fun ij => Nat.blt (rk L ij.2) (rk L ij.1)

/-- All terms of `d` negative at the order `L` (and `d ≠ []`). -/
def evNeg {p : ℕ} (L : List (Fin p)) (d : List (Fin p × Fin p)) : Bool :=
  !d.isEmpty && d.all fun ij => Nat.blt (rk L ij.1) (rk L ij.2)

theorem evPos_sound {n p : ℕ} {x : Fin n → ℝ³} {P : Fin p → Fin n} {w u : ℝ³}
    {d : List (Fin p × Fin p)} (hd : DecOK x P w d) {L : List (Fin p)}
    (hrk : ∀ i j, rk L i < rk L j → ⟪x (P i), u⟫ < ⟪x (P j), u⟫) (h : evPos L d = true) :
    0 < ⟪w, u⟫ := by
  obtain ⟨cs, hl, hc, he⟩ := hd
  simp only [evPos, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff,
    List.all_eq_true, Nat.blt_eq] at h
  rw [decOK_inner cs hl he u]
  exact zipWith_pos cs d (fun ij => ⟪x (P ij.1), u⟫ - ⟪x (P ij.2), u⟫) hl hc
    (fun ij hij => sub_pos.mpr (hrk _ _ (h.2 ij hij))) h.1

theorem evNeg_sound {n p : ℕ} {x : Fin n → ℝ³} {P : Fin p → Fin n} {w u : ℝ³}
    {d : List (Fin p × Fin p)} (hd : DecOK x P w d) {L : List (Fin p)}
    (hrk : ∀ i j, rk L i < rk L j → ⟪x (P i), u⟫ < ⟪x (P j), u⟫) (h : evNeg L d = true) :
    ⟪w, u⟫ < 0 := by
  obtain ⟨cs, hl, hc, he⟩ := hd
  simp only [evNeg, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff,
    List.all_eq_true, Nat.blt_eq] at h
  rw [decOK_inner cs hl he u]
  exact zipWith_neg cs d (fun ij => ⟪x (P ij.1), u⟫ - ⟪x (P ij.2), u⟫) hl hc
    (fun ij hij => sub_neg.mpr (hrk _ _ (h.2 ij hij))) h.1

/-- GRAM contradiction for the order pair `(L1, L2)`. -/
def gramBad {p : ℕ} (E1 E2 : List (List (Fin p × Fin p))) (L1 L2 : List (Fin p)) : Bool :=
  (E1.any (evPos L2) || E2.any (evPos L1)) && (E1.any (evNeg L2) || E2.any (evNeg L1))

/-- An order is excluded at its own view: forced pair, separated circuit, or SELF. -/
def exclOK {p : ℕ} (forced : List (Fin p × Fin p)) (deps : List (Fin p → SignType))
    (E : List (List (Fin p × Fin p))) (L : List (Fin p)) : Bool :=
  forced.any (fun ij => Nat.blt (rk L ij.1) (rk L ij.2)) ||
    deps.any (fun s => sepR s L || sepR (fun i => -s i) L) || E.any (evNeg L)

/-- Check at the second view: every order is excluded, passes a rim, or is listed in `B2`. -/
def check2 {m n p : ℕ} (S : Fin m → Finset (Fin n)) (P : Fin p → Fin n) (sw : Fin m → SignType)
    (forced : List (Fin p × Fin p)) (deps : List (Fin p → SignType))
    (E : List (List (Fin p × Fin p))) (R : List (Rim m p)) (B2 : List (List (Fin p))) : Bool :=
  R.all (rimValid S P sw) &&
    (List.finRange p).permutations'.all fun L =>
      exclOK forced deps E L || R.any (fun ρ => rimOK ρ L) || B2.contains L

/-- Check at the first view: every order is excluded, passes a rim, or is killed by GRAM
against every listed order `B2` of the second view. -/
def check1 {m n p : ℕ} (S : Fin m → Finset (Fin n)) (P : Fin p → Fin n) (sw : Fin m → SignType)
    (forced : List (Fin p × Fin p)) (deps : List (Fin p → SignType))
    (E1 E2 : List (List (Fin p × Fin p))) (R : List (Rim m p)) (B2 : List (List (Fin p))) :
    Bool :=
  R.all (rimValid S P sw) &&
    (List.finRange p).permutations'.all fun L =>
      exclOK forced deps E1 L || R.any (fun ρ => rimOK ρ L) || B2.all (gramBad E1 E2 L)

/-! ### Soundness -/

theorem exclOK_false {n p : ℕ} {x : Fin n → ℝ³} {P : Fin p → Fin n} {w : ℝ³}
    {forced : List (Fin p × Fin p)} (hforced : ∀ ij ∈ forced, ⟪x (P ij.2), w⟫ < ⟪x (P ij.1), w⟫)
    {deps : List (Fin p → SignType)}
    (hdeps : ∀ s ∈ deps, ∃ mu : Fin p → ℝ, ∑ i, mu i = 0 ∧ ∑ i, mu i • x (P i) = 0 ∧
      ∀ i, SignType.sign (mu i) = s i)
    {E : List (List (Fin p × Fin p))} (hE : ∀ d ∈ E, DecOK x P w d) {L : List (Fin p)}
    (hrk : ∀ i j, rk L i < rk L j → ⟪x (P i), w⟫ < ⟪x (P j), w⟫)
    (h : exclOK forced deps E L = true) : False := by
  simp only [exclOK, Bool.or_eq_true, List.any_eq_true] at h
  rcases h with (⟨ij, hij, hlt⟩ | ⟨s, hs, hsep⟩) | ⟨d, hd, hneg⟩
  · rw [Nat.blt_eq] at hlt
    exact absurd (hforced ij hij) (not_lt.mpr (hrk _ _ hlt).le)
  · obtain ⟨mu, hsum, hdep, hsg⟩ := hdeps s hs
    have hz : ∑ i, mu i * ⟪x (P i), w⟫ = 0 := dep_depth mu (fun i => x (P i)) hdep w
    rcases hsep with h | h
    · exact sepR_sound hrk hsg hsum hz h
    · refine sepR_sound (mu := fun i => -mu i) hrk (fun i => ?_) ?_ ?_ h
      · rw [Left.sign_neg, hsg]
      · rw [Finset.sum_neg_distrib, hsum, neg_zero]
      · simp only [neg_mul, Finset.sum_neg_distrib, hz, neg_zero]
  · have := evNeg_sound (hE d hd) hrk hneg
    linarith [real_inner_self_nonneg (x := w)]

theorem gramBad_false {n p : ℕ} {x : Fin n → ℝ³} {P : Fin p → Fin n} {w1 w2 : ℝ³}
    {E1 E2 : List (List (Fin p × Fin p))} (hE1 : ∀ d ∈ E1, DecOK x P w1 d)
    (hE2 : ∀ d ∈ E2, DecOK x P w2 d) {L1 L2 : List (Fin p)}
    (hrk1 : ∀ i j, rk L1 i < rk L1 j → ⟪x (P i), w1⟫ < ⟪x (P j), w1⟫)
    (hrk2 : ∀ i j, rk L2 i < rk L2 j → ⟪x (P i), w2⟫ < ⟪x (P j), w2⟫)
    (h : gramBad E1 E2 L1 L2 = true) : False := by
  have hc : ⟪w2, w1⟫ = ⟪w1, w2⟫ := real_inner_comm _ _
  simp only [gramBad, Bool.and_eq_true, Bool.or_eq_true, List.any_eq_true] at h
  obtain ⟨hp, hn⟩ := h
  have hpos : 0 < ⟪w1, w2⟫ := by
    rcases hp with ⟨d, hd, he⟩ | ⟨d, hd, he⟩
    · exact evPos_sound (hE1 d hd) hrk2 he
    · rw [← hc]; exact evPos_sound (hE2 d hd) hrk1 he
  have hneg : ⟪w1, w2⟫ < 0 := by
    rcases hn with ⟨d, hd, he⟩ | ⟨d, hd, he⟩
    · exact evNeg_sound (hE1 d hd) hrk2 he
    · rw [← hc]; exact evNeg_sound (hE2 d hd) hrk1 he
  linarith

/-- A valid rim passing at the order gives `LexAny` (the last branch of `svc_local`). -/
theorem lexAny_of_rimOK {m n p : ℕ} {S : Fin m → Finset (Fin n)} {x : Fin n → ℝ³}
    (F : S0xFac m S x) (P : Fin p → Fin n) (w : ℝ³) (sw : Fin m → SignType) (ρ : Rim m p)
    (hsw : ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn → SignType.sign ⟪F.N t, w⟫ = sw t)
    (hR : ∃ d1 : ℝ³, ∀ t, sw t = 0 → SignType.sign ⟪F.N t, d1⟫ = ρ.sd t)
    (hv : rimValid S P sw ρ = true) {L : List (Fin p)}
    (hrk : ∀ i j, rk L i < rk L j → ⟪x (P i), w⟫ < ⟪x (P j), w⟫) (hok : rimOK ρ L = true) :
    Minimality.Gen.LexAny F := by
  simp only [rimValid, Bool.and_eq_true, decide_eq_true_eq] at hv
  obtain ⟨⟨⟨⟨hk, hinj⟩, hcyc⟩, hU⟩, hD⟩ := hv
  obtain ⟨d1, hd1⟩ := hR
  refine Minimality.GenQuad.lexAny_of_clauses F hk hinj hcyc w d1 0 ?_ ?_ ?_
  · intro t ht
    have hs := hsw t (Or.inl ht)
    rw [inner_zero_right]
    rcases hU t ht with h | ⟨h0, h1⟩
    · exact Or.inl (sign_eq_one_iff.mp (hs.trans h))
    · refine Or.inr ⟨sign_eq_zero_iff.mp (hs.trans h0), Or.inl ?_⟩
      exact sign_eq_one_iff.mp ((hd1 t h0).trans h1)
  · intro t ht
    have hs := hsw t (Or.inr ht)
    rw [inner_zero_right, neg_zero]
    rcases hD t ht with h | ⟨h0, h1⟩
    · exact Or.inl (neg_pos.mpr (sign_eq_neg_one_iff.mp (hs.trans h)))
    · refine Or.inr ⟨neg_eq_zero.mpr (sign_eq_zero_iff.mp (hs.trans h0)), Or.inl ?_⟩
      exact neg_pos.mpr (sign_eq_neg_one_iff.mp ((hd1 t h0).trans h1))
  · exact rimOK_sound hrk (y := fun i => x (P i)) (fun i => rfl) ρ hok

/-- **Pair closure.** Two views `w1`, `w2` with facings (on the rim facets), tilts, forced
pairs, signed dependencies, decompositions and distinct depths; if `check1` and `check2` pass,
then `Gen.LexAny F`. -/
theorem pair_closure {m n p : ℕ} {S : Fin m → Finset (Fin n)} {x : Fin n → ℝ³}
    (F : S0xFac m S x) (P : Fin p → Fin n) (w1 w2 : ℝ³) (sw1 sw2 : Fin m → SignType)
    (R1 R2 : List (Rim m p))
    (hsw1 : ∀ ρ ∈ R1, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn → SignType.sign ⟪F.N t, w1⟫ = sw1 t)
    (hsw2 : ∀ ρ ∈ R2, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn → SignType.sign ⟪F.N t, w2⟫ = sw2 t)
    (hR1 : ∀ ρ ∈ R1, ∃ d1 : ℝ³, ∀ t, sw1 t = 0 → SignType.sign ⟪F.N t, d1⟫ = ρ.sd t)
    (hR2 : ∀ ρ ∈ R2, ∃ d1 : ℝ³, ∀ t, sw2 t = 0 → SignType.sign ⟪F.N t, d1⟫ = ρ.sd t)
    (forced1 forced2 : List (Fin p × Fin p))
    (hforced1 : ∀ ij ∈ forced1, ⟪x (P ij.2), w1⟫ < ⟪x (P ij.1), w1⟫)
    (hforced2 : ∀ ij ∈ forced2, ⟪x (P ij.2), w2⟫ < ⟪x (P ij.1), w2⟫)
    (deps : List (Fin p → SignType))
    (hdeps : ∀ s ∈ deps, ∃ mu : Fin p → ℝ, ∑ i, mu i = 0 ∧ ∑ i, mu i • x (P i) = 0 ∧
      ∀ i, SignType.sign (mu i) = s i)
    (E1 E2 : List (List (Fin p × Fin p)))
    (hE1 : ∀ d ∈ E1, DecOK x P w1 d) (hE2 : ∀ d ∈ E2, DecOK x P w2 d)
    (hgen1 : ∀ i j, i ≠ j → ⟪x (P i), w1⟫ ≠ ⟪x (P j), w1⟫)
    (hgen2 : ∀ i j, i ≠ j → ⟪x (P i), w2⟫ ≠ ⟪x (P j), w2⟫)
    (B2 : List (List (Fin p)))
    (hc1 : check1 S P sw1 forced1 deps E1 E2 R1 B2 = true)
    (hc2 : check2 S P sw2 forced2 deps E2 R2 B2 = true) : Minimality.Gen.LexAny F := by
  classical
  obtain ⟨L1, hL1, hrk1⟩ := exists_order (fun i => ⟪x (P i), w1⟫)
    (fun i j h => by by_contra hne; exact hgen1 i j hne h)
  obtain ⟨L2, hL2, hrk2⟩ := exists_order (fun i => ⟪x (P i), w2⟫)
    (fun i j h => by by_contra hne; exact hgen2 i j hne h)
  simp only [check1, check2, Bool.and_eq_true, List.all_eq_true] at hc1 hc2
  obtain ⟨hv1, hp1⟩ := hc1
  obtain ⟨hv2, hp2⟩ := hc2
  have h2 := hp2 L2 hL2
  simp only [Bool.or_eq_true, List.any_eq_true] at h2
  rcases h2 with (hx | ⟨ρ, hρ, hok⟩) | hmem
  · exact (exclOK_false hforced2 hdeps hE2 hrk2 hx).elim
  · exact lexAny_of_rimOK F P w2 sw2 ρ (hsw2 ρ hρ) (hR2 ρ hρ) (hv2 ρ hρ) hrk2 hok
  · have h1 := hp1 L1 hL1
    simp only [Bool.or_eq_true, List.any_eq_true, List.all_eq_true] at h1
    rcases h1 with (hx | ⟨ρ, hρ, hok⟩) | hall
    · exact (exclOK_false hforced1 hdeps hE1 hrk1 hx).elim
    · exact lexAny_of_rimOK F P w1 sw1 ρ (hsw1 ρ hρ) (hR1 ρ hρ) (hv1 ρ hρ) hrk1 hok
    · have hm : L2 ∈ B2 := by simpa using hmem
      exact (gramBad_false hE1 hE2 hrk1 hrk2 (hall L2 hm)).elim

/-! ### Decompositions from facets -/

/-- Coordinates in three linearly independent vectors of `ℝ³`. -/
theorem exists_coords (e : Fin 3 → ℝ³) (hli : LinearIndependent ℝ e) (w : ℝ³) :
    ∃ lam : Fin 3 → ℝ, w = ∑ k, lam k • e k := by
  have hcard : Fintype.card (Fin 3) = Module.finrank ℝ ℝ³ := by simp
  let b := basisOfLinearIndependentOfCardEqFinrank hli hcard
  refine ⟨b.repr w, ?_⟩
  have := b.sum_repr w
  rw [coe_basisOfLinearIndependentOfCardEqFinrank] at this
  exact this.symm

/-- **Corner coordinates.** At a vertex `c` with neighbours `a k` and facets `T k` (`T k`
contains `c` and the other two neighbours, not `a k`), every view is
`w = ∑ λ_k (x (a k) - x c)` with `sign λ_k = - sign ⟪N (T k), w⟫`. -/
theorem corner_coords {m n : ℕ} {S : Fin m → Finset (Fin n)} {x : Fin n → ℝ³}
    (F : S0xFac m S x) (c : Fin n) (a : Fin 3 → Fin n) (T : Fin 3 → Fin m)
    (hc : ∀ k, c ∈ S (T k)) (hon : ∀ k j, j ≠ k → a j ∈ S (T k)) (hoff : ∀ k, a k ∉ S (T k))
    (w : ℝ³) :
    ∃ lam : Fin 3 → ℝ, w = ∑ k, lam k • (x (a k) - x c) ∧
      ∀ k, SignType.sign (lam k) = -SignType.sign ⟪F.N (T k), w⟫ := by
  have hNe : ∀ k j, ⟪F.N (T k), x (a j) - x c⟫ = if j = k then F.f (T k) (x (a k)) else 0 := by
    intro k j
    rw [← F.hN, F.zero _ c (hc k), sub_zero]
    split_ifs with h
    · subst h; rfl
    · exact F.zero _ _ (hon k j h)
  have hli : LinearIndependent ℝ (fun k => x (a k) - x c) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg k
    have h := congrArg (fun v => ⟪F.N (T k), v⟫) hg
    simp only [inner_sum, real_inner_smul_right, hNe, mul_ite, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true, inner_zero_right] at h
    exact (mul_eq_zero.mp h).resolve_right (F.neg _ _ (hoff k)).ne
  obtain ⟨lam, hw⟩ := exists_coords _ hli w
  refine ⟨lam, hw, fun k => ?_⟩
  have h : ⟪F.N (T k), w⟫ = lam k * F.f (T k) (x (a k)) := by
    rw [hw]
    simp only [inner_sum, real_inner_smul_right, hNe, mul_ite, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [h, sign_mul, sign_neg (F.neg _ _ (hoff k))]
  rcases SignType.sign (lam k) with _ | _ | _ <;> rfl

/-- **Triangle coordinates.** A view `w` in the plane of facet `t ⊇ {a, b, r}` (a vertex `y`
off `t`; `oa` contains `b, r` not `a`; `ob` contains `a, r` not `b`) is
`w = λ_a (x a - x r) + λ_b (x b - x r)` with `sign λ_a = - sign ⟪N oa, w⟫`, same for `b`. -/
theorem tri_coords {m n : ℕ} {S : Fin m → Finset (Fin n)} {x : Fin n → ℝ³}
    (F : S0xFac m S x) (t oa ob : Fin m) (a b r y : Fin n) (ha : a ∈ S t) (hb : b ∈ S t)
    (hr : r ∈ S t) (hy : y ∉ S t) (hoab : b ∈ S oa) (hoar : r ∈ S oa) (hoaa : a ∉ S oa)
    (hoba : a ∈ S ob) (hobr : r ∈ S ob) (hobb : b ∉ S ob) (w : ℝ³)
    (hw : ⟪F.N t, w⟫ = 0) :
    ∃ la lb : ℝ, w = la • (x a - x r) + lb • (x b - x r) ∧
      SignType.sign la = -SignType.sign ⟪F.N oa, w⟫ ∧
      SignType.sign lb = -SignType.sign ⟪F.N ob, w⟫ := by
  have ev : ∀ s v, ⟪F.N s, x v - x r⟫ = F.f s (x v) - F.f s (x r) := fun s v => (F.hN s _ _).symm
  set e : Fin 3 → ℝ³ := ![x a - x r, x b - x r, x y - x r] with he
  have t0 : ⟪F.N t, x a - x r⟫ = 0 := by rw [ev, F.zero _ _ ha, F.zero _ _ hr, sub_self]
  have t1 : ⟪F.N t, x b - x r⟫ = 0 := by rw [ev, F.zero _ _ hb, F.zero _ _ hr, sub_self]
  have t2 : ⟪F.N t, x y - x r⟫ = F.f t (x y) := by rw [ev, F.zero _ _ hr, sub_zero]
  have a0 : ⟪F.N oa, x a - x r⟫ = F.f oa (x a) := by rw [ev, F.zero _ _ hoar, sub_zero]
  have a1 : ⟪F.N oa, x b - x r⟫ = 0 := by rw [ev, F.zero _ _ hoab, F.zero _ _ hoar, sub_self]
  have b0 : ⟪F.N ob, x a - x r⟫ = 0 := by rw [ev, F.zero _ _ hoba, F.zero _ _ hobr, sub_self]
  have b1 : ⟪F.N ob, x b - x r⟫ = F.f ob (x b) := by rw [ev, F.zero _ _ hobr, sub_zero]
  have fy := F.neg _ _ hy
  have fa := F.neg _ _ hoaa
  have fb := F.neg _ _ hobb
  have hli : LinearIndependent ℝ e := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fin.sum_univ_three] at hg
    simp only [he, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons] at hg
    have h1 := congrArg (fun v => ⟪F.N t, v⟫) hg
    simp only [inner_add_right, real_inner_smul_right, t0, t1, t2, inner_zero_right] at h1
    have g2 : g 2 = 0 := by
      have : g 2 * F.f t (x y) = 0 := by linarith
      exact (mul_eq_zero.mp this).resolve_right fy.ne
    have h2 := congrArg (fun v => ⟪F.N oa, v⟫) hg
    simp only [inner_add_right, real_inner_smul_right, a0, a1, g2, inner_zero_right] at h2
    have g0 : g 0 = 0 := by
      have : g 0 * F.f oa (x a) = 0 := by linarith
      exact (mul_eq_zero.mp this).resolve_right fa.ne
    have h3 := congrArg (fun v => ⟪F.N ob, v⟫) hg
    simp only [inner_add_right, real_inner_smul_right, b0, b1, g2, inner_zero_right] at h3
    have g1 : g 1 = 0 := by
      have : g 1 * F.f ob (x b) = 0 := by linarith
      exact (mul_eq_zero.mp this).resolve_right fb.ne
    intro k; fin_cases k <;> assumption
  obtain ⟨lam, hw'⟩ := exists_coords e hli w
  rw [Fin.sum_univ_three] at hw'
  simp only [he, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at hw'
  have l2 : lam 2 = 0 := by
    have h := congrArg (fun v => ⟪F.N t, v⟫) hw'
    simp only [inner_add_right, real_inner_smul_right, t0, t1, t2, hw] at h
    have : lam 2 * F.f t (x y) = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_right fy.ne
  rw [l2, zero_smul, add_zero] at hw'
  refine ⟨lam 0, lam 1, hw', ?_, ?_⟩
  · have h : ⟪F.N oa, w⟫ = lam 0 * F.f oa (x a) := by
      rw [hw']; simp only [inner_add_right, real_inner_smul_right, a0, a1]; ring
    rw [h, sign_mul, sign_neg fa]
    rcases SignType.sign (lam 0) with _ | _ | _ <;> rfl
  · have h : ⟪F.N ob, w⟫ = lam 1 * F.f ob (x b) := by
      rw [hw']; simp only [inner_add_right, real_inner_smul_right, b0, b1]; ring
    rw [h, sign_mul, sign_neg fb]
    rcases SignType.sign (lam 1) with _ | _ | _ <;> rfl

/-- `cornerDec` is a decomposition (indices through `P`). -/
theorem decOK_corner {m n p : ℕ} {S : Fin m → Finset (Fin n)} {x : Fin n → ℝ³}
    (F : S0xFac m S x) (P : Fin p → Fin n) (sw : Fin m → SignType) (c : Fin p)
    (a : Fin 3 → Fin p) (T : Fin 3 → Fin m)
    (hc : ∀ k, P c ∈ S (T k)) (hon : ∀ k j, j ≠ k → P (a j) ∈ S (T k))
    (hoff : ∀ k, P (a k) ∉ S (T k)) (w : ℝ³)
    (hsw : ∀ k, SignType.sign ⟪F.N (T k), w⟫ = sw (T k)) :
    DecOK x P w (cornerDec sw c a T) := by
  obtain ⟨lam, hw, hs⟩ := corner_coords F (P c) (fun k => P (a k)) T hc hon hoff w
  have hs' : ∀ k, -sw (T k) = SignType.sign (lam k) := fun k => by rw [hs k, hsw k]
  rw [Fin.sum_univ_three] at hw
  rw [hw, cornerDec, hs' 0, hs' 1, hs' 2]
  exact decOK_append (decOK_append (decOK_term x P _ _ _) (decOK_term x P _ _ _))
    (decOK_term x P _ _ _)

/-- `triDec` is a decomposition (indices through `P`). -/
theorem decOK_tri {m n p : ℕ} {S : Fin m → Finset (Fin n)} {x : Fin n → ℝ³}
    (F : S0xFac m S x) (P : Fin p → Fin n) (sw : Fin m → SignType) (t oa ob : Fin m)
    (a b r : Fin p) (y : Fin n) (ha : P a ∈ S t) (hb : P b ∈ S t)
    (hr : P r ∈ S t) (hy : y ∉ S t) (hoab : P b ∈ S oa) (hoar : P r ∈ S oa)
    (hoaa : P a ∉ S oa) (hoba : P a ∈ S ob) (hobr : P r ∈ S ob) (hobb : P b ∉ S ob) (w : ℝ³)
    (hw : ⟪F.N t, w⟫ = 0) (hsa : SignType.sign ⟪F.N oa, w⟫ = sw oa)
    (hsb : SignType.sign ⟪F.N ob, w⟫ = sw ob) :
    DecOK x P w (triDec sw r a b oa ob) := by
  obtain ⟨la, lb, hw', h1, h2⟩ :=
    tri_coords F t oa ob (P a) (P b) (P r) y ha hb hr hy hoab hoar hoaa hoba hobr hobb w hw
  rw [hw', triDec, ← hsa, ← hsb, ← h1, ← h2]
  exact decOK_append (decOK_term x P _ _ _) (decOK_term x P _ _ _)

end Minimality.PSVC
