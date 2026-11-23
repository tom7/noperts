module

public import Minimality.SVCLex

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


/-!
# Triple closure (PAIRLEAN2): three views coupled pairwise by the Gram symmetry

Extends `PSVC.pair_closure` to three views `u`, `v`, `w`. At each view an order of the points
is excluded (forced pair, separated signed circuit, SELF), passes a valid rim (then `LexAny`),
or is *bad*. The bad orders at `v` and `w` are listed (`Bv`, `Bw`, certified by `check2`). At
the outer view `u` every bad order `L` must be killed together with every pair `(b, c)` of
`Bv × Bw`: GRAM (`gramBad`) on `(L, b)`, on `(L, c)` or on `(b, c)`. The Bool function
`triOK` tries the two cheap cases first (`L` GRAM-kills all of `Bv`, or all of `Bw`).

Also `decOK_edge` / `edge_forced`: an edge view `x i - x j` decomposes as itself, and puts
`i` strictly above `j`.
-/

set_option autoImplicit false

open scoped RealInnerProductSpace
open Minimality Minimality.H21

namespace Minimality.PSVC

open Minimality.SVC

/-- Every pair `(b, c)` of listed bad orders at `v`, `w` is GRAM-killed with `L` (the order at
the outer view `u`) or with each other. -/
def triOK {p : ℕ} (Eu Ev Ew : List (List (Fin p × Fin p))) (Bv Bw : List (List (Fin p)))
    (L : List (Fin p)) : Bool :=
  Bv.all (gramBad Eu Ev L) || Bw.all (gramBad Eu Ew L) ||
    Bv.all fun b => gramBad Eu Ev L b || Bw.all fun c => gramBad Eu Ew L c || gramBad Ev Ew b c

/-- Check at the outer view `u`: every order is excluded, passes a rim, or satisfies `triOK`. -/
def checkT {m n p : ℕ} (S : Fin m → Finset (Fin n)) (P : Fin p → Fin n) (sw : Fin m → SignType)
    (forced : List (Fin p × Fin p)) (deps : List (Fin p → SignType))
    (Eu Ev Ew : List (List (Fin p × Fin p))) (R : List (Rim m p)) (Bv Bw : List (List (Fin p))) :
    Bool :=
  R.all (rimValid S P sw) &&
    (List.finRange p).permutations'.all fun L =>
      exclOK forced deps Eu L || R.any (fun ρ => rimOK ρ L) || triOK Eu Ev Ew Bv Bw L

theorem triOK_false {n p : ℕ} {x : Fin n → ℝ³} {P : Fin p → Fin n} {u v w : ℝ³}
    {Eu Ev Ew : List (List (Fin p × Fin p))} (hEu : ∀ d ∈ Eu, DecOK x P u d)
    (hEv : ∀ d ∈ Ev, DecOK x P v d) (hEw : ∀ d ∈ Ew, DecOK x P w d)
    {Bv Bw : List (List (Fin p))} {Lu Lv Lw : List (Fin p)} (hv : Lv ∈ Bv) (hw : Lw ∈ Bw)
    (hrku : ∀ i j, rk Lu i < rk Lu j → ⟪x (P i), u⟫ < ⟪x (P j), u⟫)
    (hrkv : ∀ i j, rk Lv i < rk Lv j → ⟪x (P i), v⟫ < ⟪x (P j), v⟫)
    (hrkw : ∀ i j, rk Lw i < rk Lw j → ⟪x (P i), w⟫ < ⟪x (P j), w⟫)
    (h : triOK Eu Ev Ew Bv Bw Lu = true) : False := by
  simp only [triOK, Bool.or_eq_true, List.all_eq_true] at h
  rcases h with (h | h) | h
  · exact gramBad_false hEu hEv hrku hrkv (h Lv hv)
  · exact gramBad_false hEu hEw hrku hrkw (h Lw hw)
  · rcases h Lv hv with h1 | h1
    · exact gramBad_false hEu hEv hrku hrkv h1
    · rcases h1 Lw hw with h2 | h2
      · exact gramBad_false hEu hEw hrku hrkw h2
      · exact gramBad_false hEv hEw hrkv hrkw h2

/-- One view's input to `triple_closure`: facings on the rim facets, tilts, forced pairs,
decompositions, distinct depths. -/
structure ViewData {m n p : ℕ} {S : Fin m → Finset (Fin n)} {x : Fin n → ℝ³}
    (F : S0xFac m S x) (P : Fin p → Fin n) (w : ℝ³) (sw : Fin m → SignType)
    (R : List (Rim m p)) (forced : List (Fin p × Fin p)) (E : List (List (Fin p × Fin p))) :
    Prop where
  hsw : ∀ ρ ∈ R, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn → SignType.sign ⟪F.N t, w⟫ = sw t
  hR : ∀ ρ ∈ R, ∃ d1 : ℝ³, ∀ t, sw t = 0 → SignType.sign ⟪F.N t, d1⟫ = ρ.sd t
  hforced : ∀ ij ∈ forced, ⟪x (P ij.2), w⟫ < ⟪x (P ij.1), w⟫
  hE : ∀ d ∈ E, DecOK x P w d
  hgen : ∀ i j, i ≠ j → ⟪x (P i), w⟫ ≠ ⟪x (P j), w⟫

/-- The sorted order at a view of a `ViewData`: excluded orders are impossible, a passing rim
gives `LexAny`, and otherwise the order is bad. -/
theorem ViewData.order {m n p : ℕ} {S : Fin m → Finset (Fin n)} {x : Fin n → ℝ³}
    {F : S0xFac m S x} {P : Fin p → Fin n} {w : ℝ³} {sw : Fin m → SignType}
    {R : List (Rim m p)} {forced : List (Fin p × Fin p)} {E : List (List (Fin p × Fin p))}
    (V : ViewData F P w sw R forced E) :
    ∃ L ∈ (List.finRange p).permutations', ∀ i j, rk L i < rk L j → ⟪x (P i), w⟫ < ⟪x (P j), w⟫ :=
  exists_order (fun i => ⟪x (P i), w⟫) (fun i j h => by by_contra hne; exact V.hgen i j hne h)

/-- **Triple closure.** Three views with `ViewData` and shared signed dependencies; if `check2`
holds at `v` (list `Bv`) and at `w` (list `Bw`) and `checkT` at `u`, then `Gen.LexAny F`. -/
theorem triple_closure {m n p : ℕ} {S : Fin m → Finset (Fin n)} {x : Fin n → ℝ³}
    (F : S0xFac m S x) (P : Fin p → Fin n) (u v w : ℝ³) (su sv sw : Fin m → SignType)
    (Ru Rv Rw : List (Rim m p)) (fu fv fw : List (Fin p × Fin p))
    (Eu Ev Ew : List (List (Fin p × Fin p)))
    (Vu : ViewData F P u su Ru fu Eu) (Vv : ViewData F P v sv Rv fv Ev)
    (Vw : ViewData F P w sw Rw fw Ew)
    (deps : List (Fin p → SignType))
    (hdeps : ∀ s ∈ deps, ∃ mu : Fin p → ℝ, ∑ i, mu i = 0 ∧ ∑ i, mu i • x (P i) = 0 ∧
      ∀ i, SignType.sign (mu i) = s i)
    (Bv Bw : List (List (Fin p)))
    (hcu : checkT S P su fu deps Eu Ev Ew Ru Bv Bw = true)
    (hcv : check2 S P sv fv deps Ev Rv Bv = true)
    (hcw : check2 S P sw fw deps Ew Rw Bw = true) : Minimality.Gen.LexAny F := by
  classical
  obtain ⟨Lu, hLu, hrku⟩ := Vu.order
  obtain ⟨Lv, hLv, hrkv⟩ := Vv.order
  obtain ⟨Lw, hLw, hrkw⟩ := Vw.order
  simp only [checkT, check2, Bool.and_eq_true, List.all_eq_true] at hcu hcv hcw
  obtain ⟨hvu, hpu⟩ := hcu
  obtain ⟨hvv, hpv⟩ := hcv
  obtain ⟨hvw, hpw⟩ := hcw
  have h2 := hpv Lv hLv
  simp only [Bool.or_eq_true, List.any_eq_true] at h2
  rcases h2 with (hx | ⟨ρ, hρ, hok⟩) | hmv
  · exact (exclOK_false Vv.hforced hdeps Vv.hE hrkv hx).elim
  · exact lexAny_of_rimOK F P v sv ρ (Vv.hsw ρ hρ) (Vv.hR ρ hρ) (hvv ρ hρ) hrkv hok
  have h3 := hpw Lw hLw
  simp only [Bool.or_eq_true, List.any_eq_true] at h3
  rcases h3 with (hx | ⟨ρ, hρ, hok⟩) | hmw
  · exact (exclOK_false Vw.hforced hdeps Vw.hE hrkw hx).elim
  · exact lexAny_of_rimOK F P w sw ρ (Vw.hsw ρ hρ) (Vw.hR ρ hρ) (hvw ρ hρ) hrkw hok
  have h1 := hpu Lu hLu
  simp only [Bool.or_eq_true, List.any_eq_true] at h1
  rcases h1 with (hx | ⟨ρ, hρ, hok⟩) | ht
  · exact (exclOK_false Vu.hforced hdeps Vu.hE hrku hx).elim
  · exact lexAny_of_rimOK F P u su ρ (Vu.hsw ρ hρ) (Vu.hR ρ hρ) (hvu ρ hρ) hrku hok
  · exact (triOK_false Vu.hE Vv.hE Vw.hE (by simpa using hmv) (by simpa using hmw)
      hrku hrkv hrkw ht).elim

/-! ### Edge views -/

/-- An edge view `x (P i) - x (P j)` is its own decomposition. -/
theorem decOK_edge {n p : ℕ} (x : Fin n → ℝ³) (P : Fin p → Fin n) (i j : Fin p) :
    DecOK x P (x (P i) - x (P j)) [(i, j)] :=
  ⟨[1], rfl, by simp, by simp⟩

/-- At the edge view `x a - x b` (`x a ≠ x b`) the point `a` is strictly deeper than `b`. -/
theorem edge_forced {n : ℕ} (x : Fin n → ℝ³) (a b : Fin n) (h : x a ≠ x b) :
    ⟪x b, x a - x b⟫ < ⟪x a, x a - x b⟫ := by
  have hpos : 0 < ⟪x a - x b, x a - x b⟫ :=
    real_inner_self_pos.mpr (sub_ne_zero.mpr h)
  rw [inner_sub_left] at hpos
  linarith

/-! ### Gram determinant for disjoint edge-on facets (input of `hR_gram`) -/

/-- Two vectors with a common orthogonal-to-one test vector `a` (`⟪N1, a⟫ ≠ 0 = ⟪N2, a⟫`,
`N2 ≠ 0`) are independent: their Gram determinant is nonzero. -/
theorem gram_ne_of {N1 N2 a : ℝ³} (h1 : ⟪N1, a⟫ ≠ 0) (h2 : ⟪N2, a⟫ = 0) (hN2 : N2 ≠ 0) :
    ⟪N1, N1⟫ * ⟪N2, N2⟫ - ⟪N1, N2⟫ ^ 2 ≠ 0 := by
  intro hG
  set g11 := ⟪N1, N1⟫
  set g12 := ⟪N1, N2⟫
  set g22 := ⟪N2, N2⟫
  have hN1 : N1 ≠ 0 := by rintro rfl; exact h1 (inner_zero_left a)
  have h11 : 0 < g11 := real_inner_self_pos.mpr hN1
  set v := g12 • N1 - g11 • N2 with hv
  have hvv : ⟪v, v⟫ = g11 * (g11 * g22 - g12 ^ 2) := by
    simp only [hv, inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
      real_inner_comm N1 N2]
    ring
  have hv0 : v = 0 := by
    rw [hG, mul_zero] at hvv
    exact inner_self_eq_zero.mp hvv
  have ha : ⟪v, a⟫ = g12 * ⟪N1, a⟫ := by
    simp only [hv, inner_sub_left, real_inner_smul_left, h2, mul_zero, sub_zero]
  rw [hv0, inner_zero_left] at ha
  have g12z : g12 = 0 := (mul_eq_zero.mp ha.symm).resolve_right h1
  have hv1 : g12 • N1 - g11 • N2 = 0 := hv0
  rw [g12z, zero_smul, zero_sub, neg_eq_zero] at hv1
  exact hN2 ((smul_eq_zero.mp hv1).resolve_left h11.ne')

/-- `gram_ne_of` with the test vector orthogonal to the first vector. -/
theorem gram_ne_of' {N1 N2 a : ℝ³} (h1 : ⟪N1, a⟫ = 0) (h2 : ⟪N2, a⟫ ≠ 0) (hN1 : N1 ≠ 0) :
    ⟪N1, N1⟫ * ⟪N2, N2⟫ - ⟪N1, N2⟫ ^ 2 ≠ 0 := by
  have := gram_ne_of h2 h1 hN1
  rw [real_inner_comm N1 N2, mul_comm] at this
  exact this

/-- A facet normal is nonzero (a point on the facet and one off it). -/
theorem facet_N_ne {m n : ℕ} {S : Fin m → Finset (Fin n)} {x : Fin n → ℝ³}
    (F : S0xFac m S x) (t : Fin m) (i j : Fin n) (hi : i ∈ S t) (hj : j ∉ S t) : F.N t ≠ 0 := by
  intro h
  have := F.hN t (x j) (x i)
  rw [h, inner_zero_left, F.zero t i hi, sub_zero] at this
  exact (F.neg t j hj).ne this

end Minimality.PSVC


/-!
# Pencil rule PENC (PAIRLEAN3)

If two views `v1`, `v2` and an edge vector `e = x i - x j` are all orthogonal to one nonzero
vector `N` (the normal of a facet that is edge-on at both views and contains `i`, `j`), the three
vectors are linearly dependent: `c1 v1 + c2 v2 + c3 e = 0`, `c ≠ 0`. Pairing with test vectors
`t` (facet normals) whose signs at `v1`, `v2`, `e` are known constrains the sign pattern of `c`
(`zeroSumOK`). When every consistent pattern has `c3 ≠ 0` and the same signs of
`α = -c1/c3`, `β = -c2/c3` (`pencCheck`), we get `e = α v1 + β v2` with those signs
(`pencil_of_check`). Then `0 ≤ ⟪e, e⟫ = α (z_i - z_j)(v1) + β (z_i - z_j)(v2)`, so the depth
orders at `v1`, `v2` cannot make both terms `≤ 0` with one `< 0` (`pencKill_false`).

`triple_closure_p` is `triple_closure` with the pair kills `gramBad || PENC` (`pairBad`).
-/

set_option autoImplicit false

open scoped RealInnerProductSpace
open Minimality Minimality.H21

namespace Minimality.PSVC

open Minimality.SVC

/-! ### Linear algebra -/

/-- Three vectors of `ℝ³` orthogonal to a nonzero vector are linearly dependent. -/
theorem dep_of_perp {N v1 v2 e : ℝ³} (hN : N ≠ 0) (h1 : ⟪N, v1⟫ = 0) (h2 : ⟪N, v2⟫ = 0)
    (h3 : ⟪N, e⟫ = 0) :
    ∃ c1 c2 c3 : ℝ, (c1 ≠ 0 ∨ c2 ≠ 0 ∨ c3 ≠ 0) ∧ c1 • v1 + c2 • v2 + c3 • e = 0 := by
  have hnli : ¬ LinearIndependent ℝ ![v1, v2, e, N] := by
    intro hli
    have := hli.fintype_card_le_finrank
    simp at this
  rw [Fintype.not_linearIndependent_iff] at hnli
  obtain ⟨g, hg, i, hi⟩ := hnli
  rw [Fin.sum_univ_four] at hg
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] at hg
  have hNN : 0 < ⟪N, N⟫ := real_inner_self_pos.mpr hN
  have g3 : g 3 = 0 := by
    have h := congrArg (fun v => ⟪N, v⟫) hg
    simp only [inner_add_right, real_inner_smul_right, h1, h2, h3, inner_zero_right,
      mul_zero, zero_add] at h
    exact (mul_eq_zero.mp h).resolve_right hNN.ne'
  rw [g3, zero_smul, add_zero] at hg
  refine ⟨g 0, g 1, g 2, ?_, hg⟩
  fin_cases i
  · exact Or.inl hi
  · exact Or.inr (Or.inl hi)
  · exact Or.inr (Or.inr hi)
  · exact absurd g3 hi

/-! ### Sign patterns -/

/-- The signs of three reals with zero sum: all zero, or both strict signs occur. -/
def zeroSumOK (a b c : SignType) : Bool :=
  (a == 0 && b == 0 && c == 0) ||
    ((a == 1 || b == 1 || c == 1) && (a == -1 || b == -1 || c == -1))

theorem sign_cases (r : ℝ) :
    (r < 0 ∧ SignType.sign r = -1) ∨ (r = 0 ∧ SignType.sign r = 0) ∨
      (0 < r ∧ SignType.sign r = 1) := by
  rcases lt_trichotomy r 0 with h | h | h
  · exact Or.inl ⟨h, sign_neg h⟩
  · exact Or.inr (Or.inl ⟨h, by rw [h, sign_zero]⟩)
  · exact Or.inr (Or.inr ⟨h, sign_pos h⟩)

theorem zeroSumOK_of {a b c : ℝ} (h : a + b + c = 0) :
    zeroSumOK (SignType.sign a) (SignType.sign b) (SignType.sign c) = true := by
  rcases sign_cases a with ⟨ha, sa⟩ | ⟨ha, sa⟩ | ⟨ha, sa⟩ <;>
  rcases sign_cases b with ⟨hb, sb⟩ | ⟨hb, sb⟩ | ⟨hb, sb⟩ <;>
  rcases sign_cases c with ⟨hc, sc⟩ | ⟨hc, sc⟩ | ⟨hc, sc⟩ <;>
  rw [sa, sb, sc] <;> first | decide | (exfalso; linarith)

/-- All 27 sign triples. -/
def sgnL : List SignType := [-1, 0, 1]

def pats3 : List (SignType × SignType × SignType) :=
  sgnL.flatMap fun a => sgnL.flatMap fun b => sgnL.map fun c => (a, b, c)

theorem mem_pats3 (k : SignType × SignType × SignType) : k ∈ pats3 := by
  obtain ⟨a, b, c⟩ := k
  cases a <;> cases b <;> cases c <;> decide

/-- Test rows `(s1, s2, s3)` (signs of one test vector at `v1`, `v2`, `e`). Every nonzero sign
pattern `(k1, k2, k3)` of a dependency `c1 v1 + c2 v2 + c3 e = 0` that is consistent with all
rows has `k3 ≠ 0`, `sign (-c1/c3) = σ1` and `sign (-c2/c3) = σ2`. -/
def pencCheck (T : List (SignType × SignType × SignType)) (σ1 σ2 : SignType) : Bool :=
  pats3.all fun k =>
    (k.1 == 0 && k.2.1 == 0 && k.2.2 == 0) ||
      !(T.all fun r => zeroSumOK (k.1 * r.1) (k.2.1 * r.2.1) (k.2.2 * r.2.2)) ||
      (k.2.2 != 0 && -(k.1 * k.2.2) == σ1 && -(k.2.1 * k.2.2) == σ2)

theorem sign_inv' (c : ℝ) : SignType.sign c⁻¹ = SignType.sign c := by
  rcases lt_trichotomy c 0 with h | h | h
  · rw [sign_neg h, sign_neg (inv_lt_zero.mpr h)]
  · rw [h, inv_zero]
  · rw [sign_pos h, sign_pos (inv_pos.mpr h)]

/-- **Pencil lemma.** `v1`, `v2`, `e` orthogonal to `N ≠ 0`, test vectors with known signs,
`pencCheck` passes: `e = α v1 + β v2` with `sign α = σ1`, `sign β = σ2`. -/
theorem pencil_of_check {N v1 v2 e : ℝ³} (hN : N ≠ 0) (h1 : ⟪N, v1⟫ = 0) (h2 : ⟪N, v2⟫ = 0)
    (h3 : ⟪N, e⟫ = 0) (T : List (SignType × SignType × SignType))
    (hT : ∀ r ∈ T, ∃ t : ℝ³, SignType.sign ⟪t, v1⟫ = r.1 ∧ SignType.sign ⟪t, v2⟫ = r.2.1 ∧
      SignType.sign ⟪t, e⟫ = r.2.2)
    {σ1 σ2 : SignType} (hc : pencCheck T σ1 σ2 = true) :
    ∃ α β : ℝ, e = α • v1 + β • v2 ∧ SignType.sign α = σ1 ∧ SignType.sign β = σ2 := by
  obtain ⟨c1, c2, c3, hne, hdep⟩ := dep_of_perp hN h1 h2 h3
  have hrows : (T.all fun r => zeroSumOK (SignType.sign c1 * r.1) (SignType.sign c2 * r.2.1)
      (SignType.sign c3 * r.2.2)) = true := by
    rw [List.all_eq_true]
    intro r hr
    obtain ⟨t, s1, s2, s3⟩ := hT r hr
    have hz : c1 * ⟪t, v1⟫ + c2 * ⟪t, v2⟫ + c3 * ⟪t, e⟫ = 0 := by
      have h := congrArg (fun v => ⟪t, v⟫) hdep
      simpa only [inner_add_right, real_inner_smul_right, inner_zero_right] using h
    have := zeroSumOK_of hz
    rwa [sign_mul, sign_mul, sign_mul, s1, s2, s3] at this
  simp only [pencCheck, List.all_eq_true] at hc
  have hk := hc _ (mem_pats3 (SignType.sign c1, SignType.sign c2, SignType.sign c3))
  simp only [hrows, Bool.not_true, Bool.or_false, Bool.or_eq_true, Bool.and_eq_true,
    beq_iff_eq, bne_iff_ne, ne_eq] at hk
  rcases hk with ⟨⟨z1, z2⟩, z3⟩ | ⟨⟨k3, hα⟩, hβ⟩
  · exfalso
    rw [sign_eq_zero_iff] at z1 z2 z3
    rcases hne with h | h | h <;> contradiction
  · have c3ne : c3 ≠ 0 := fun h => k3 (by rw [h, sign_zero])
    refine ⟨-c1 / c3, -c2 / c3, ?_, ?_, ?_⟩
    · have he : e = c3⁻¹ • (c3 • e) := by rw [smul_smul, inv_mul_cancel₀ c3ne, one_smul]
      have h' : c3 • e = -(c1 • v1 + c2 • v2) := by
        rw [eq_neg_iff_add_eq_zero, add_comm]; exact hdep
      rw [he, h']
      module
    · rw [div_eq_mul_inv, sign_mul, sign_inv', Left.sign_neg, ← hα, neg_mul]
    · rw [div_eq_mul_inv, sign_mul, sign_inv', Left.sign_neg, ← hβ, neg_mul]

/-! ### The rule on depth orders -/

/-- A pencil rule: `x (P i) - x (P j) = α v1 + β v2`, `sign α = s1`, `sign β = s2`. -/
structure Penc (p : ℕ) where
  i : Fin p
  j : Fin p
  s1 : SignType
  s2 : SignType
deriving DecidableEq

def PencOK {n p : ℕ} (x : Fin n → ℝ³) (P : Fin p → Fin n) (v1 v2 : ℝ³) (r : Penc p) : Prop :=
  ∃ α β : ℝ, x (P r.i) - x (P r.j) = α • v1 + β • v2 ∧ SignType.sign α = r.s1 ∧
    SignType.sign β = r.s2

/-- The term `α (z_i - z_j)` is strictly negative at the order `L` (`sign α = s`). -/
def negT {p : ℕ} (s : SignType) (L : List (Fin p)) (i j : Fin p) : Bool :=
  (s == 1 && Nat.blt (rk L i) (rk L j)) || (s == -1 && Nat.blt (rk L j) (rk L i))

/-- PENC kill: both terms `≤ 0`, one `< 0`. -/
def pencKill {p : ℕ} (r : Penc p) (L1 L2 : List (Fin p)) : Bool :=
  (negT r.s1 L1 r.i r.j || r.s1 == 0) && (negT r.s2 L2 r.i r.j || r.s2 == 0) &&
    (negT r.s1 L1 r.i r.j || negT r.s2 L2 r.i r.j)

theorem negT_sound {n p : ℕ} {x : Fin n → ℝ³} {P : Fin p → Fin n} {v : ℝ³} {L : List (Fin p)}
    (hrk : ∀ i j, rk L i < rk L j → ⟪x (P i), v⟫ < ⟪x (P j), v⟫) {i j : Fin p} {α : ℝ}
    (h : negT (SignType.sign α) L i j = true) : α * (⟪x (P i), v⟫ - ⟪x (P j), v⟫) < 0 := by
  simp only [negT, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, Nat.blt_eq] at h
  rcases h with ⟨hs, hl⟩ | ⟨hs, hl⟩
  · exact mul_neg_of_pos_of_neg (sign_eq_one_iff.mp hs) (sub_neg.mpr (hrk _ _ hl))
  · exact mul_neg_of_neg_of_pos (sign_eq_neg_one_iff.mp hs) (sub_pos.mpr (hrk _ _ hl))

theorem term_le {n p : ℕ} {x : Fin n → ℝ³} {P : Fin p → Fin n} {v : ℝ³} {L : List (Fin p)}
    (hrk : ∀ i j, rk L i < rk L j → ⟪x (P i), v⟫ < ⟪x (P j), v⟫) {i j : Fin p} {α : ℝ}
    (h : (negT (SignType.sign α) L i j || SignType.sign α == 0) = true) :
    α * (⟪x (P i), v⟫ - ⟪x (P j), v⟫) ≤ 0 := by
  rcases Bool.or_eq_true _ _ ▸ h with h | h
  · exact (negT_sound hrk h).le
  · rw [beq_iff_eq, sign_eq_zero_iff] at h
    rw [h, zero_mul]

theorem pencKill_false {n p : ℕ} {x : Fin n → ℝ³} {P : Fin p → Fin n} {v1 v2 : ℝ³}
    {r : Penc p} (hr : PencOK x P v1 v2 r) {L1 L2 : List (Fin p)}
    (hrk1 : ∀ i j, rk L1 i < rk L1 j → ⟪x (P i), v1⟫ < ⟪x (P j), v1⟫)
    (hrk2 : ∀ i j, rk L2 i < rk L2 j → ⟪x (P i), v2⟫ < ⟪x (P j), v2⟫)
    (h : pencKill r L1 L2 = true) : False := by
  obtain ⟨α, β, he, sα, sβ⟩ := hr
  have hee : ⟪x (P r.i) - x (P r.j), x (P r.i) - x (P r.j)⟫ =
      α * (⟪x (P r.i), v1⟫ - ⟪x (P r.j), v1⟫) + β * (⟪x (P r.i), v2⟫ - ⟪x (P r.j), v2⟫) := by
    calc _ = ⟪x (P r.i) - x (P r.j), α • v1 + β • v2⟫ := by rw [← he]
      _ = _ := by
        rw [inner_add_right, real_inner_smul_right, real_inner_smul_right, inner_sub_left,
          inner_sub_left]
  have h0 := real_inner_self_nonneg (x := x (P r.i) - x (P r.j))
  simp only [pencKill, Bool.and_eq_true] at h
  obtain ⟨⟨ha, hb⟩, hab⟩ := h
  rw [← sα] at ha hab
  rw [← sβ] at hb hab
  have t1 := term_le hrk1 ha
  have t2 := term_le hrk2 hb
  rcases Bool.or_eq_true _ _ ▸ hab with h | h
  · have := negT_sound hrk1 h; linarith
  · have := negT_sound hrk2 h; linarith

/-! ### Facet form of the pencil check -/

/-- Sign of `⟪N t, x a - x b⟫` read from incidence (meaningful when `a ∈ S t ∨ b ∈ S t`). -/
def esgn {m n : ℕ} (S : Fin m → Finset (Fin n)) (a b : Fin n) (t : Fin m) : SignType :=
  if a ∈ S t then (if b ∈ S t then 0 else 1) else (if b ∈ S t then -1 else 0)

theorem esgn_sound {m n : ℕ} {S : Fin m → Finset (Fin n)} {x : Fin n → ℝ³}
    (F : S0xFac m S x) (a b : Fin n) (t : Fin m) (h : a ∈ S t ∨ b ∈ S t) :
    SignType.sign ⟪F.N t, x a - x b⟫ = esgn S a b t := by
  rw [F.inner_sub]
  unfold esgn
  by_cases ha : a ∈ S t <;> by_cases hb : b ∈ S t <;> simp only [ha, hb, ite_true, ite_false]
  · rw [F.zero t a ha, F.zero t b hb, sub_self, sign_zero]
  · rw [F.zero t a ha, zero_sub]; exact sign_pos (neg_pos.mpr (F.neg t b hb))
  · rw [F.zero t b hb, sub_zero]; exact sign_neg (F.neg t a ha)
  · exact absurd h (by tauto)

/-- The pencil check for the edge `P r.i, P r.j` of facet `a` (edge-on at both views, facings
`s1`, `s2`), test facets `T` (each containing `P r.i` or `P r.j`). -/
def pencCheckF {m n p : ℕ} (S : Fin m → Finset (Fin n)) (P : Fin p → Fin n)
    (s1 s2 : Fin m → SignType) (a : Fin m) (T : List (Fin m)) (r : Penc p) : Bool :=
  decide (P r.i ∈ S a) && decide (P r.j ∈ S a) && s1 a == 0 && s2 a == 0 &&
    T.all (fun t => decide (P r.i ∈ S t) || decide (P r.j ∈ S t)) &&
    pencCheck (T.map fun t => (s1 t, s2 t, esgn S (P r.i) (P r.j) t)) r.s1 r.s2

theorem pencOK_of_checkF {m n p : ℕ} {S : Fin m → Finset (Fin n)} {x : Fin n → ℝ³}
    (F : S0xFac m S x) (P : Fin p → Fin n) (v1 v2 : ℝ³) (s1 s2 : Fin m → SignType)
    (a : Fin m) (T : List (Fin m)) (r : Penc p) (y : Fin n) (hy : y ∉ S a)
    (hs1 : ∀ t ∈ a :: T, SignType.sign ⟪F.N t, v1⟫ = s1 t)
    (hs2 : ∀ t ∈ a :: T, SignType.sign ⟪F.N t, v2⟫ = s2 t)
    (hc : pencCheckF S P s1 s2 a T r = true) : PencOK x P v1 v2 r := by
  simp only [pencCheckF, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
    List.all_eq_true, Bool.or_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨hi, hj⟩, z1⟩, z2⟩, hT⟩, hc⟩ := hc
  have hN : F.N a ≠ 0 := facet_N_ne F a (P r.i) y hi hy
  have e1 : ⟪F.N a, v1⟫ = 0 := sign_eq_zero_iff.mp ((hs1 a (by simp)).trans z1)
  have e2 : ⟪F.N a, v2⟫ = 0 := sign_eq_zero_iff.mp ((hs2 a (by simp)).trans z2)
  have e3 : ⟪F.N a, x (P r.i) - x (P r.j)⟫ = 0 := by
    rw [F.inner_sub, F.zero a _ hi, F.zero a _ hj, sub_self]
  refine pencil_of_check hN e1 e2 e3 _ ?_ hc
  intro q hq
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hq
  have htT : t ∈ a :: T := List.mem_cons_of_mem a ht
  refine ⟨F.N t, hs1 t htT, hs2 t htT, ?_⟩
  rcases hT t ht with h | h
  · exact esgn_sound F _ _ t (Or.inl h)
  · exact esgn_sound F _ _ t (Or.inr h)

/-! ### Triple closure with PENC -/

/-- Pair kill: GRAM or a pencil rule. -/
def pairBad {p : ℕ} (E1 E2 : List (List (Fin p × Fin p))) (R : List (Penc p))
    (L1 L2 : List (Fin p)) : Bool :=
  gramBad E1 E2 L1 L2 || R.any fun r => pencKill r L1 L2

theorem pairBad_false {n p : ℕ} {x : Fin n → ℝ³} {P : Fin p → Fin n} {w1 w2 : ℝ³}
    {E1 E2 : List (List (Fin p × Fin p))} (hE1 : ∀ d ∈ E1, DecOK x P w1 d)
    (hE2 : ∀ d ∈ E2, DecOK x P w2 d) {R : List (Penc p)} (hR : ∀ r ∈ R, PencOK x P w1 w2 r)
    {L1 L2 : List (Fin p)}
    (hrk1 : ∀ i j, rk L1 i < rk L1 j → ⟪x (P i), w1⟫ < ⟪x (P j), w1⟫)
    (hrk2 : ∀ i j, rk L2 i < rk L2 j → ⟪x (P i), w2⟫ < ⟪x (P j), w2⟫)
    (h : pairBad E1 E2 R L1 L2 = true) : False := by
  simp only [pairBad, Bool.or_eq_true, List.any_eq_true] at h
  rcases h with h | ⟨r, hr, hk⟩
  · exact gramBad_false hE1 hE2 hrk1 hrk2 h
  · exact pencKill_false (hR r hr) hrk1 hrk2 hk

/-- `triOK` with `pairBad` (GRAM or PENC) for the three pairs. -/
def triOKp {p : ℕ} (Eu Ev Ew : List (List (Fin p × Fin p))) (Ruv Ruw Rvw : List (Penc p))
    (Bv Bw : List (List (Fin p))) (L : List (Fin p)) : Bool :=
  Bv.all (pairBad Eu Ev Ruv L) || Bw.all (pairBad Eu Ew Ruw L) ||
    Bv.all fun b => pairBad Eu Ev Ruv L b || Bw.all fun c =>
      pairBad Eu Ew Ruw L c || pairBad Ev Ew Rvw b c

/-- `checkT` with `triOKp`. -/
def checkTp {m n p : ℕ} (S : Fin m → Finset (Fin n)) (P : Fin p → Fin n) (sw : Fin m → SignType)
    (forced : List (Fin p × Fin p)) (deps : List (Fin p → SignType))
    (Eu Ev Ew : List (List (Fin p × Fin p))) (Ruv Ruw Rvw : List (Penc p)) (R : List (Rim m p))
    (Bv Bw : List (List (Fin p))) : Bool :=
  R.all (rimValid S P sw) &&
    (List.finRange p).permutations'.all fun L =>
      exclOK forced deps Eu L || R.any (fun ρ => rimOK ρ L) || triOKp Eu Ev Ew Ruv Ruw Rvw Bv Bw L

theorem triOKp_false {n p : ℕ} {x : Fin n → ℝ³} {P : Fin p → Fin n} {u v w : ℝ³}
    {Eu Ev Ew : List (List (Fin p × Fin p))} (hEu : ∀ d ∈ Eu, DecOK x P u d)
    (hEv : ∀ d ∈ Ev, DecOK x P v d) (hEw : ∀ d ∈ Ew, DecOK x P w d)
    {Ruv Ruw Rvw : List (Penc p)} (hRuv : ∀ r ∈ Ruv, PencOK x P u v r)
    (hRuw : ∀ r ∈ Ruw, PencOK x P u w r) (hRvw : ∀ r ∈ Rvw, PencOK x P v w r)
    {Bv Bw : List (List (Fin p))} {Lu Lv Lw : List (Fin p)} (hv : Lv ∈ Bv) (hw : Lw ∈ Bw)
    (hrku : ∀ i j, rk Lu i < rk Lu j → ⟪x (P i), u⟫ < ⟪x (P j), u⟫)
    (hrkv : ∀ i j, rk Lv i < rk Lv j → ⟪x (P i), v⟫ < ⟪x (P j), v⟫)
    (hrkw : ∀ i j, rk Lw i < rk Lw j → ⟪x (P i), w⟫ < ⟪x (P j), w⟫)
    (h : triOKp Eu Ev Ew Ruv Ruw Rvw Bv Bw Lu = true) : False := by
  simp only [triOKp, Bool.or_eq_true, List.all_eq_true] at h
  rcases h with (h | h) | h
  · exact pairBad_false hEu hEv hRuv hrku hrkv (h Lv hv)
  · exact pairBad_false hEu hEw hRuw hrku hrkw (h Lw hw)
  · rcases h Lv hv with h1 | h1
    · exact pairBad_false hEu hEv hRuv hrku hrkv h1
    · rcases h1 Lw hw with h2 | h2
      · exact pairBad_false hEu hEw hRuw hrku hrkw h2
      · exact pairBad_false hEv hEw hRvw hrkv hrkw h2

/-- **Triple closure with PENC.** As `triple_closure`, with pencil rules `Ruv`, `Ruw`, `Rvw`
(each `PencOK` for its pair of views) added to the GRAM pair kills of `checkTp`. -/
theorem triple_closure_p {m n p : ℕ} {S : Fin m → Finset (Fin n)} {x : Fin n → ℝ³}
    (F : S0xFac m S x) (P : Fin p → Fin n) (u v w : ℝ³) (su sv sw : Fin m → SignType)
    (Ru Rv Rw : List (Rim m p)) (fu fv fw : List (Fin p × Fin p))
    (Eu Ev Ew : List (List (Fin p × Fin p)))
    (Vu : ViewData F P u su Ru fu Eu) (Vv : ViewData F P v sv Rv fv Ev)
    (Vw : ViewData F P w sw Rw fw Ew)
    (deps : List (Fin p → SignType))
    (hdeps : ∀ s ∈ deps, ∃ mu : Fin p → ℝ, ∑ i, mu i = 0 ∧ ∑ i, mu i • x (P i) = 0 ∧
      ∀ i, SignType.sign (mu i) = s i)
    (Ruv Ruw Rvw : List (Penc p)) (hRuv : ∀ r ∈ Ruv, PencOK x P u v r)
    (hRuw : ∀ r ∈ Ruw, PencOK x P u w r) (hRvw : ∀ r ∈ Rvw, PencOK x P v w r)
    (Bv Bw : List (List (Fin p)))
    (hcu : checkTp S P su fu deps Eu Ev Ew Ruv Ruw Rvw Ru Bv Bw = true)
    (hcv : check2 S P sv fv deps Ev Rv Bv = true)
    (hcw : check2 S P sw fw deps Ew Rw Bw = true) : Minimality.Gen.LexAny F := by
  classical
  obtain ⟨Lu, hLu, hrku⟩ := Vu.order
  obtain ⟨Lv, hLv, hrkv⟩ := Vv.order
  obtain ⟨Lw, hLw, hrkw⟩ := Vw.order
  simp only [checkTp, check2, Bool.and_eq_true, List.all_eq_true] at hcu hcv hcw
  obtain ⟨hvu, hpu⟩ := hcu
  obtain ⟨hvv, hpv⟩ := hcv
  obtain ⟨hvw, hpw⟩ := hcw
  have h2 := hpv Lv hLv
  simp only [Bool.or_eq_true, List.any_eq_true] at h2
  rcases h2 with (hx | ⟨ρ, hρ, hok⟩) | hmv
  · exact (exclOK_false Vv.hforced hdeps Vv.hE hrkv hx).elim
  · exact lexAny_of_rimOK F P v sv ρ (Vv.hsw ρ hρ) (Vv.hR ρ hρ) (hvv ρ hρ) hrkv hok
  have h3 := hpw Lw hLw
  simp only [Bool.or_eq_true, List.any_eq_true] at h3
  rcases h3 with (hx | ⟨ρ, hρ, hok⟩) | hmw
  · exact (exclOK_false Vw.hforced hdeps Vw.hE hrkw hx).elim
  · exact lexAny_of_rimOK F P w sw ρ (Vw.hsw ρ hρ) (Vw.hR ρ hρ) (hvw ρ hρ) hrkw hok
  have h1 := hpu Lu hLu
  simp only [Bool.or_eq_true, List.any_eq_true] at h1
  rcases h1 with (hx | ⟨ρ, hρ, hok⟩) | ht
  · exact (exclOK_false Vu.hforced hdeps Vu.hE hrku hx).elim
  · exact lexAny_of_rimOK F P u su ρ (Vu.hsw ρ hρ) (Vu.hR ρ hρ) (hvu ρ hρ) hrku hok
  · exact (triOKp_false Vu.hE Vv.hE Vw.hE hRuv hRuw hRvw (by simpa using hmv)
      (by simpa using hmw) hrku hrkv hrkw ht).elim

/-! ### Tie-tolerant pair and triple closure (`lexKey` + weak orders) -/

theorem lexKey_fst_le {y z w d1 d2 : ℝ³} (h : lexKey y w d1 d2 < lexKey z w d1 d2) :
    ⟪y, w⟫ ≤ ⟪z, w⟫ := by
  unfold lexKey at h
  rw [Prod.Lex.toLex_lt_toLex] at h
  rcases h with h | ⟨h, _⟩
  · exact h.le
  · exact h.le

theorem zipWith_nonneg {p : ℕ} (cs : List ℝ) (d : List (Fin p × Fin p)) (g : Fin p × Fin p → ℝ)
    (hl : cs.length = d.length) (hc : ∀ c ∈ cs, 0 < c) (hg : ∀ ij ∈ d, 0 ≤ g ij) :
    0 ≤ (List.zipWith (fun c ij => c * g ij) cs d).sum := by
  induction cs generalizing d with
  | nil => simp
  | cons c cs ih =>
    cases d with
    | nil => simp at hl
    | cons ij d =>
      simp only [List.zipWith_cons_cons, List.sum_cons]
      have h1 : 0 ≤ c * g ij := mul_nonneg (hc c (by simp)).le (hg ij (by simp))
      have h2 := ih d (by simpa using hl) (fun c' h => hc c' (by simp [h]))
        (fun ij' h => hg ij' (by simp [h]))
      linarith

theorem zipWith_nonpos {p : ℕ} (cs : List ℝ) (d : List (Fin p × Fin p)) (g : Fin p × Fin p → ℝ)
    (hl : cs.length = d.length) (hc : ∀ c ∈ cs, 0 < c) (hg : ∀ ij ∈ d, g ij ≤ 0) :
    (List.zipWith (fun c ij => c * g ij) cs d).sum ≤ 0 := by
  induction cs generalizing d with
  | nil => simp
  | cons c cs ih =>
    cases d with
    | nil => simp at hl
    | cons ij d =>
      simp only [List.zipWith_cons_cons, List.sum_cons]
      have h1 : c * g ij ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (hc c (by simp)).le (hg ij (by simp))
      have h2 := ih d (by simpa using hl) (fun c' h => hc c' (by simp [h]))
        (fun ij' h => hg ij' (by simp [h]))
      linarith

theorem evPos_lex_sound {n p : ℕ} {x : Fin n → ℝ³} {P : Fin p → Fin n} {w u d1 d2 : ℝ³}
    {d : List (Fin p × Fin p)} (hd : DecOK x P w d) {L : List (Fin p)}
    (hrk : ∀ i j, rk L i < rk L j → lexKey (x (P i)) u d1 d2 < lexKey (x (P j)) u d1 d2)
    (h : evPos L d = true) : 0 ≤ ⟪w, u⟫ := by
  obtain ⟨cs, hl, hc, he⟩ := hd
  simp only [evPos, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff,
    List.all_eq_true, Nat.blt_eq] at h
  rw [decOK_inner cs hl he u]
  exact zipWith_nonneg cs d (fun ij => ⟪x (P ij.1), u⟫ - ⟪x (P ij.2), u⟫) hl hc
    (fun ij hij => sub_nonneg.mpr (lexKey_fst_le (hrk _ _ (h.2 ij hij))))

theorem evNeg_lex_sound {n p : ℕ} {x : Fin n → ℝ³} {P : Fin p → Fin n} {w u d1 d2 : ℝ³}
    {d : List (Fin p × Fin p)} (hd : DecOK x P w d) {L : List (Fin p)}
    (hrk : ∀ i j, rk L i < rk L j → lexKey (x (P i)) u d1 d2 < lexKey (x (P j)) u d1 d2)
    (h : evNeg L d = true) : ⟪w, u⟫ ≤ 0 := by
  obtain ⟨cs, hl, hc, he⟩ := hd
  simp only [evNeg, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff,
    List.all_eq_true, Nat.blt_eq] at h
  rw [decOK_inner cs hl he u]
  exact zipWith_nonpos cs d (fun ij => ⟪x (P ij.1), u⟫ - ⟪x (P ij.2), u⟫) hl hc
    (fun ij hij => sub_nonpos.mpr (lexKey_fst_le (hrk _ _ (h.2 ij hij))))

theorem exclOK_lex_false {n p : ℕ} {x : Fin n → ℝ³} {P : Fin p → Fin n} {w d1 d2 : ℝ³}
    (hw : w ≠ 0)
    {forced : List (Fin p × Fin p)} (hforced : ∀ ij ∈ forced, ⟪x (P ij.2), w⟫ < ⟪x (P ij.1), w⟫)
    {deps : List (Fin p → SignType)}
    (hdeps : ∀ s ∈ deps, ∃ mu : Fin p → ℝ, ∑ i, mu i = 0 ∧ ∑ i, mu i • x (P i) = 0 ∧
      ∀ i, SignType.sign (mu i) = s i)
    {E : List (List (Fin p × Fin p))} (hE : ∀ d ∈ E, DecOK x P w d) {L : List (Fin p)}
    (hrk : ∀ i j, rk L i < rk L j → lexKey (x (P i)) w d1 d2 < lexKey (x (P j)) w d1 d2)
    (h : exclOK forced deps E L = true) : False := by
  simp only [exclOK, Bool.or_eq_true, List.any_eq_true] at h
  rcases h with (⟨ij, hij, hlt⟩ | ⟨s, hs, hsep⟩) | ⟨d, hd, hneg⟩
  · rw [Nat.blt_eq] at hlt
    exact absurd (hrk _ _ hlt) (lt_asymm (lexKey_lt_of_lt (hforced ij hij)))
  · obtain ⟨mu, hsum, hdep, hsg⟩ := hdeps s hs
    rcases hsep with h | h
    · exact sepR_lex_sound hrk hsg hsum hdep h
    · refine sepR_lex_sound hrk (mu := fun i => -mu i) (fun i => ?_) ?_ ?_ h
      · rw [Left.sign_neg, hsg]
      · rw [Finset.sum_neg_distrib, hsum, neg_zero]
      · simp only [neg_smul, Finset.sum_neg_distrib, hdep, neg_zero]
  · have hle := evNeg_lex_sound (hE d hd) hrk hneg
    have hpos : 0 < ⟪w, w⟫ :=
      lt_of_le_of_ne real_inner_self_nonneg (fun e => hw (inner_self_eq_zero.mp e.symm))
    linarith

theorem gramBad_lex_false {n p : ℕ} {x : Fin n → ℝ³} {P : Fin p → Fin n}
    {w1 w2 d11 d12 d21 d22 : ℝ³} (hw : ⟪w1, w2⟫ ≠ 0)
    {E1 E2 : List (List (Fin p × Fin p))} (hE1 : ∀ d ∈ E1, DecOK x P w1 d)
    (hE2 : ∀ d ∈ E2, DecOK x P w2 d) {L1 L2 : List (Fin p)}
    (hrk1 : ∀ i j, rk L1 i < rk L1 j → lexKey (x (P i)) w1 d11 d12 < lexKey (x (P j)) w1 d11 d12)
    (hrk2 : ∀ i j, rk L2 i < rk L2 j → lexKey (x (P i)) w2 d21 d22 < lexKey (x (P j)) w2 d21 d22)
    (h : gramBad E1 E2 L1 L2 = true) : False := by
  have hc : ⟪w2, w1⟫ = ⟪w1, w2⟫ := real_inner_comm _ _
  simp only [gramBad, Bool.and_eq_true, Bool.or_eq_true, List.any_eq_true] at h
  obtain ⟨hp, hn⟩ := h
  have hnonneg : 0 ≤ ⟪w1, w2⟫ := by
    rcases hp with ⟨d, hd, he⟩ | ⟨d, hd, he⟩
    · exact evPos_lex_sound (hE1 d hd) hrk2 he
    · rw [← hc]; exact evPos_lex_sound (hE2 d hd) hrk1 he
  have hnonpos : ⟪w1, w2⟫ ≤ 0 := by
    rcases hn with ⟨d, hd, he⟩ | ⟨d, hd, he⟩
    · exact evNeg_lex_sound (hE1 d hd) hrk2 he
    · rw [← hc]; exact evNeg_lex_sound (hE2 d hd) hrk1 he
  exact hw (le_antisymm hnonpos hnonneg)

def pencKillW {p : ℕ} (r : Penc p) (L1 L2 : List (Fin p)) : Bool :=
  (r.i != r.j) && pencKill r L1 L2

theorem term_lex_le {n p : ℕ} {x : Fin n → ℝ³} {P : Fin p → Fin n} {v d1 d2 : ℝ³}
    {L : List (Fin p)}
    (hrk : ∀ i j, rk L i < rk L j → lexKey (x (P i)) v d1 d2 < lexKey (x (P j)) v d1 d2)
    {i j : Fin p} {α : ℝ}
    (h : (negT (SignType.sign α) L i j || SignType.sign α == 0) = true) :
    α * (⟪x (P i), v⟫ - ⟪x (P j), v⟫) ≤ 0 := by
  rcases Bool.or_eq_true _ _ |>.mp h with h | h
  · simp only [negT, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, Nat.blt_eq] at h
    rcases h with ⟨hs, hl⟩ | ⟨hs, hl⟩
    · exact mul_nonpos_of_nonneg_of_nonpos (sign_eq_one_iff.mp hs).le
        (sub_nonpos.mpr (lexKey_fst_le (hrk _ _ hl)))
    · exact mul_nonpos_of_nonpos_of_nonneg (sign_eq_neg_one_iff.mp hs).le
        (sub_nonneg.mpr (lexKey_fst_le (hrk _ _ hl)))
  · rw [beq_iff_eq, sign_eq_zero_iff] at h
    rw [h, zero_mul]

theorem pencKillW_lex_false {n p : ℕ} {x : Fin n → ℝ³} {P : Fin p → Fin n}
    (hP : Function.Injective (fun i => x (P i))) {v1 v2 d11 d12 d21 d22 : ℝ³}
    {r : Penc p} (hr : PencOK x P v1 v2 r) {L1 L2 : List (Fin p)}
    (hrk1 : ∀ i j, rk L1 i < rk L1 j → lexKey (x (P i)) v1 d11 d12 < lexKey (x (P j)) v1 d11 d12)
    (hrk2 : ∀ i j, rk L2 i < rk L2 j → lexKey (x (P i)) v2 d21 d22 < lexKey (x (P j)) v2 d21 d22)
    (h : pencKillW r L1 L2 = true) : False := by
  simp only [pencKillW, Bool.and_eq_true, bne_iff_ne] at h
  obtain ⟨hne, hk⟩ := h
  obtain ⟨α, β, he, sα, sβ⟩ := hr
  have hee : ⟪x (P r.i) - x (P r.j), x (P r.i) - x (P r.j)⟫ =
      α * (⟪x (P r.i), v1⟫ - ⟪x (P r.j), v1⟫) + β * (⟪x (P r.i), v2⟫ - ⟪x (P r.j), v2⟫) := by
    calc _ = ⟪x (P r.i) - x (P r.j), α • v1 + β • v2⟫ := by rw [← he]
      _ = _ := by
        rw [inner_add_right, real_inner_smul_right, real_inner_smul_right, inner_sub_left,
          inner_sub_left]
  have hpos : 0 < ⟪x (P r.i) - x (P r.j), x (P r.i) - x (P r.j)⟫ :=
    lt_of_le_of_ne real_inner_self_nonneg
      (fun e => sub_ne_zero.mpr (fun h => hne (hP h)) (inner_self_eq_zero.mp e.symm))
  simp only [pencKill, Bool.and_eq_true] at hk
  obtain ⟨⟨ha, hb⟩, _⟩ := hk
  rw [← sα] at ha
  rw [← sβ] at hb
  have t1 := term_lex_le hrk1 ha
  have t2 := term_lex_le hrk2 hb
  linarith

def pairBadW {p : ℕ} (E1 E2 : List (List (Fin p × Fin p))) (R : List (Penc p))
    (L1 L2 : List (Fin p)) : Bool :=
  gramBad E1 E2 L1 L2 || R.any fun r => pencKillW r L1 L2

theorem pairBadW_lex_false {n p : ℕ} {x : Fin n → ℝ³} {P : Fin p → Fin n}
    (hP : Function.Injective (fun i => x (P i))) {w1 w2 d11 d12 d21 d22 : ℝ³} (hw : ⟪w1, w2⟫ ≠ 0)
    {E1 E2 : List (List (Fin p × Fin p))} (hE1 : ∀ d ∈ E1, DecOK x P w1 d)
    (hE2 : ∀ d ∈ E2, DecOK x P w2 d) {R : List (Penc p)} (hR : ∀ r ∈ R, PencOK x P w1 w2 r)
    {L1 L2 : List (Fin p)}
    (hrk1 : ∀ i j, rk L1 i < rk L1 j → lexKey (x (P i)) w1 d11 d12 < lexKey (x (P j)) w1 d11 d12)
    (hrk2 : ∀ i j, rk L2 i < rk L2 j → lexKey (x (P i)) w2 d21 d22 < lexKey (x (P j)) w2 d21 d22)
    (h : pairBadW E1 E2 R L1 L2 = true) : False := by
  simp only [pairBadW, Bool.or_eq_true, List.any_eq_true] at h
  rcases h with h | ⟨r, hr, hk⟩
  · exact gramBad_lex_false hw hE1 hE2 hrk1 hrk2 h
  · exact pencKillW_lex_false hP (hR r hr) hrk1 hrk2 hk

def triOKpW {p : ℕ} (Eu Ev Ew : List (List (Fin p × Fin p))) (Ruv Ruw Rvw : List (Penc p))
    (Bv Bw : List (List (Fin p))) (L : List (Fin p)) : Bool :=
  Bv.all (pairBadW Eu Ev Ruv L) || Bw.all (pairBadW Eu Ew Ruw L) ||
    Bv.all fun b => pairBadW Eu Ev Ruv L b || Bw.all fun c =>
      pairBadW Eu Ew Ruw L c || pairBadW Ev Ew Rvw b c

def check2W {m n p : ℕ} (S : Fin m → Finset (Fin n)) (P : Fin p → Fin n) (sw : Fin m → SignType)
    (forced : List (Fin p × Fin p)) (deps : List (Fin p → SignType))
    (E : List (List (Fin p × Fin p))) (R : List (Rim m p)) (T : List (Fin p × Fin p))
    (B2 : List (List (Fin p))) : Bool :=
  R.all (rimValid S P sw) &&
    (weakOrders p T).all fun W =>
      rimClosedW R (exclOK forced deps E) (linExts W) ||
        (linExts W).all fun L => exclOK forced deps E L || B2.contains L

def check1W {m n p : ℕ} (S : Fin m → Finset (Fin n)) (P : Fin p → Fin n) (sw : Fin m → SignType)
    (forced : List (Fin p × Fin p)) (deps : List (Fin p → SignType))
    (E1 E2 : List (List (Fin p × Fin p))) (R : List (Rim m p)) (T : List (Fin p × Fin p))
    (B2 : List (List (Fin p))) : Bool :=
  R.all (rimValid S P sw) &&
    (weakOrders p T).all fun W =>
      rimClosedW R (exclOK forced deps E1) (linExts W) ||
        (linExts W).all fun L => exclOK forced deps E1 L || B2.all (gramBad E1 E2 L)

def checkTW {m n p : ℕ} (S : Fin m → Finset (Fin n)) (P : Fin p → Fin n) (sw : Fin m → SignType)
    (forced : List (Fin p × Fin p)) (deps : List (Fin p → SignType))
    (Eu Ev Ew : List (List (Fin p × Fin p))) (R : List (Rim m p)) (T : List (Fin p × Fin p))
    (Bv Bw : List (List (Fin p))) : Bool :=
  R.all (rimValid S P sw) &&
    (weakOrders p T).all fun W =>
      rimClosedW R (exclOK forced deps Eu) (linExts W) ||
        (linExts W).all fun L => exclOK forced deps Eu L || triOK Eu Ev Ew Bv Bw L

def checkTpW {m n p : ℕ} (S : Fin m → Finset (Fin n)) (P : Fin p → Fin n) (sw : Fin m → SignType)
    (forced : List (Fin p × Fin p)) (deps : List (Fin p → SignType))
    (Eu Ev Ew : List (List (Fin p × Fin p))) (Ruv Ruw Rvw : List (Penc p))
    (R : List (Rim m p)) (T : List (Fin p × Fin p)) (Bv Bw : List (List (Fin p))) : Bool :=
  R.all (rimValid S P sw) &&
    (weakOrders p T).all fun W =>
      rimClosedW R (exclOK forced deps Eu) (linExts W) ||
        (linExts W).all fun L => exclOK forced deps Eu L || triOKpW Eu Ev Ew Ruv Ruw Rvw Bv Bw L

/-- Tie-tolerant `ViewData`: replaces `hgen` with per-rim `(d1, d2)` (`Split.det3 w d1 d2 ≠ 0`),
injectivity of `x ∘ P`, and allowed tie pairs `T`. -/
structure ViewDataLex {m n p : ℕ} {S : Fin m → Finset (Fin n)} {x : Fin n → ℝ³}
    (F : S0xFac m S x) (P : Fin p → Fin n) (w : ℝ³) (sw : Fin m → SignType)
    (R : List (Rim m p)) (forced : List (Fin p × Fin p)) (E : List (List (Fin p × Fin p)))
    (T : List (Fin p × Fin p)) : Prop where
  hne : R ≠ []
  hsw : ∀ ρ ∈ R, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn → SignType.sign ⟪F.N t, w⟫ = sw t
  hR : ∀ ρ ∈ R, ∃ d1 d2 : ℝ³,
    (∀ t, sw t = 0 → SignType.sign ⟪F.N t, d1⟫ = ρ.sd t) ∧ Split.det3 w d1 d2 ≠ 0
  hforced : ∀ ij ∈ forced, ⟪x (P ij.2), w⟫ < ⟪x (P ij.1), w⟫
  hE : ∀ d ∈ E, DecOK x P w d
  hP : Function.Injective (fun i => x (P i))
  hT : ∀ i j, i ≠ j → ⟪x (P i), w⟫ = ⟪x (P j), w⟫ → (i, j) ∈ T ∨ (j, i) ∈ T

private theorem check2W_extract {m n p : ℕ} {S : Fin m → Finset (Fin n)} {x : Fin n → ℝ³}
    {F : S0xFac m S x} {P : Fin p → Fin n} {w : ℝ³} {sw : Fin m → SignType}
    {R : List (Rim m p)} {forced : List (Fin p × Fin p)} {E : List (List (Fin p × Fin p))}
    {T : List (Fin p × Fin p)} (V : ViewDataLex F P w sw R forced E T)
    {deps : List (Fin p → SignType)}
    (hdeps : ∀ s ∈ deps, ∃ mu : Fin p → ℝ, ∑ i, mu i = 0 ∧ ∑ i, mu i • x (P i) = 0 ∧
      ∀ i, SignType.sign (mu i) = s i)
    {B2 : List (List (Fin p))} (hc : check2W S P sw forced deps E R T B2 = true) :
    Minimality.Gen.LexAny F ∨
      ∃ d1 d2 : ℝ³, ∃ L ∈ B2,
        ∀ i j, rk L i < rk L j → lexKey (x (P i)) w d1 d2 < lexKey (x (P j)) w d1 d2 := by
  classical
  obtain ⟨W, hW, hW_ext⟩ := weakOrders_sound (fun i => ⟪x (P i), w⟫) T V.hT
  simp only [check2W, Bool.and_eq_true, List.all_eq_true] at hc
  obtain ⟨hval, hcW⟩ := hc
  rcases Bool.or_eq_true _ _ |>.mp (hcW W hW) with hrim | hall
  · simp only [rimClosedW, Bool.or_eq_true, List.all_eq_true, List.any_eq_true] at hrim
    rcases hrim with hexcl | ⟨ρ, hρ, hrim⟩
    · obtain ⟨ρ0, hρ0⟩ := List.exists_mem_of_ne_nil R V.hne
      obtain ⟨d1, d2, _, hdet⟩ := V.hR ρ0 hρ0
      obtain ⟨L, hL, _, hrk⟩ := hW_ext (fun i => lexKey (x (P i)) w d1 d2)
        (fun _ _ h => lexKey_lt_of_lt h)
        (fun i j h => by by_contra hne'; exact lexKey_ne hdet (fun e => hne' (V.hP e)) h)
      exact absurd (exclOK_lex_false (w_ne_zero_of_det3 hdet) V.hforced hdeps V.hE hrk (hexcl L hL)) False.elim
    · obtain ⟨d1, d2, hd1, hdet⟩ := V.hR ρ hρ
      obtain ⟨L, hL, _, hrk⟩ := hW_ext (fun i => lexKey (x (P i)) w d1 d2)
        (fun _ _ h => lexKey_lt_of_lt h)
        (fun i j h => by by_contra hne'; exact lexKey_ne hdet (fun e => hne' (V.hP e)) h)
      rcases hrim L hL with hexcl | hok
      · exact absurd (exclOK_lex_false (w_ne_zero_of_det3 hdet) V.hforced hdeps V.hE hrk hexcl) False.elim
      · exact Or.inl (lexAny_of_rimOK_lex F P w d1 d2 sw ρ (V.hsw ρ hρ) hd1 (hval ρ hρ) hrk hok)
  · obtain ⟨ρ0, hρ0⟩ := List.exists_mem_of_ne_nil R V.hne
    obtain ⟨d1, d2, _, hdet⟩ := V.hR ρ0 hρ0
    obtain ⟨L, hL, _, hrk⟩ := hW_ext (fun i => lexKey (x (P i)) w d1 d2)
      (fun _ _ h => lexKey_lt_of_lt h)
      (fun i j h => by by_contra hne'; exact lexKey_ne hdet (fun e => hne' (V.hP e)) h)
    rcases Bool.or_eq_true _ _ |>.mp (List.all_eq_true.mp hall L hL) with hexcl | hmem
    · exact absurd (exclOK_lex_false (w_ne_zero_of_det3 hdet) V.hforced hdeps V.hE hrk hexcl) False.elim
    · exact Or.inr ⟨d1, d2, L, by simpa using hmem, hrk⟩

/-- **Pair closure, tie-tolerant.** -/
theorem pair_closure_lex {m n p : ℕ} {S : Fin m → Finset (Fin n)} {x : Fin n → ℝ³}
    (F : S0xFac m S x) (P : Fin p → Fin n) (w1 w2 : ℝ³) (sw1 sw2 : Fin m → SignType)
    (R1 R2 : List (Rim m p)) (f1 f2 : List (Fin p × Fin p))
    (E1 E2 : List (List (Fin p × Fin p))) (T1 T2 : List (Fin p × Fin p))
    (V1 : ViewDataLex F P w1 sw1 R1 f1 E1 T1) (V2 : ViewDataLex F P w2 sw2 R2 f2 E2 T2)
    (hw : ⟪w1, w2⟫ ≠ 0)
    (deps : List (Fin p → SignType))
    (hdeps : ∀ s ∈ deps, ∃ mu : Fin p → ℝ, ∑ i, mu i = 0 ∧ ∑ i, mu i • x (P i) = 0 ∧
      ∀ i, SignType.sign (mu i) = s i)
    (B2 : List (List (Fin p)))
    (hc1 : check1W S P sw1 f1 deps E1 E2 R1 T1 B2 = true)
    (hc2 : check2W S P sw2 f2 deps E2 R2 T2 B2 = true) : Minimality.Gen.LexAny F := by
  classical
  rcases check2W_extract V2 hdeps hc2 with hlex | ⟨d21, d22, L2, hL2, hrk2⟩
  · exact hlex
  · obtain ⟨W1, hW1, hW1_ext⟩ := weakOrders_sound (fun i => ⟪x (P i), w1⟫) T1 V1.hT
    simp only [check1W, Bool.and_eq_true, List.all_eq_true] at hc1
    obtain ⟨hval1, hcW1⟩ := hc1
    rcases Bool.or_eq_true _ _ |>.mp (hcW1 W1 hW1) with hrim | hall
    · simp only [rimClosedW, Bool.or_eq_true, List.all_eq_true, List.any_eq_true] at hrim
      rcases hrim with hexcl | ⟨ρ, hρ, hrim⟩
      · obtain ⟨ρ0, hρ0⟩ := List.exists_mem_of_ne_nil R1 V1.hne
        obtain ⟨d11, d12, _, hdet1⟩ := V1.hR ρ0 hρ0
        obtain ⟨L1, hL1, _, hrk1⟩ := hW1_ext (fun i => lexKey (x (P i)) w1 d11 d12)
          (fun _ _ h => lexKey_lt_of_lt h)
          (fun i j h => by by_contra hne'; exact lexKey_ne hdet1 (fun e => hne' (V1.hP e)) h)
        exact (exclOK_lex_false (w_ne_zero_of_det3 hdet1) V1.hforced hdeps V1.hE hrk1 (hexcl L1 hL1)).elim
      · obtain ⟨d11, d12, hd1, hdet1⟩ := V1.hR ρ hρ
        obtain ⟨L1, hL1, _, hrk1⟩ := hW1_ext (fun i => lexKey (x (P i)) w1 d11 d12)
          (fun _ _ h => lexKey_lt_of_lt h)
          (fun i j h => by by_contra hne'; exact lexKey_ne hdet1 (fun e => hne' (V1.hP e)) h)
        rcases hrim L1 hL1 with hexcl | hok
        · exact (exclOK_lex_false (w_ne_zero_of_det3 hdet1) V1.hforced hdeps V1.hE hrk1 hexcl).elim
        · exact lexAny_of_rimOK_lex F P w1 d11 d12 sw1 ρ (V1.hsw ρ hρ) hd1 (hval1 ρ hρ) hrk1 hok
    · obtain ⟨ρ0, hρ0⟩ := List.exists_mem_of_ne_nil R1 V1.hne
      obtain ⟨d11, d12, _, hdet1⟩ := V1.hR ρ0 hρ0
      obtain ⟨L1, hL1, _, hrk1⟩ := hW1_ext (fun i => lexKey (x (P i)) w1 d11 d12)
        (fun _ _ h => lexKey_lt_of_lt h)
        (fun i j h => by by_contra hne'; exact lexKey_ne hdet1 (fun e => hne' (V1.hP e)) h)
      rcases Bool.or_eq_true _ _ |>.mp (List.all_eq_true.mp hall L1 hL1) with hexcl | hgram
      · exact (exclOK_lex_false (w_ne_zero_of_det3 hdet1) V1.hforced hdeps V1.hE hrk1 hexcl).elim
      · exact (gramBad_lex_false hw V1.hE V2.hE hrk1 hrk2 (List.all_eq_true.mp hgram L2 hL2)).elim

theorem triOK_lex_false {n p : ℕ} {x : Fin n → ℝ³} {P : Fin p → Fin n}
    {u v w du1 du2 dv1 dv2 dw1 dw2 : ℝ³}
    (huv : ⟪u, v⟫ ≠ 0) (huw : ⟪u, w⟫ ≠ 0) (hvw : ⟪v, w⟫ ≠ 0)
    {Eu Ev Ew : List (List (Fin p × Fin p))} (hEu : ∀ d ∈ Eu, DecOK x P u d)
    (hEv : ∀ d ∈ Ev, DecOK x P v d) (hEw : ∀ d ∈ Ew, DecOK x P w d)
    {Bv Bw : List (List (Fin p))} {Lu Lv Lw : List (Fin p)} (hv : Lv ∈ Bv) (hw : Lw ∈ Bw)
    (hrku : ∀ i j, rk Lu i < rk Lu j → lexKey (x (P i)) u du1 du2 < lexKey (x (P j)) u du1 du2)
    (hrkv : ∀ i j, rk Lv i < rk Lv j → lexKey (x (P i)) v dv1 dv2 < lexKey (x (P j)) v dv1 dv2)
    (hrkw : ∀ i j, rk Lw i < rk Lw j → lexKey (x (P i)) w dw1 dw2 < lexKey (x (P j)) w dw1 dw2)
    (h : triOK Eu Ev Ew Bv Bw Lu = true) : False := by
  simp only [triOK, Bool.or_eq_true, List.all_eq_true] at h
  rcases h with (h | h) | h
  · exact gramBad_lex_false huv hEu hEv hrku hrkv (h Lv hv)
  · exact gramBad_lex_false huw hEu hEw hrku hrkw (h Lw hw)
  · rcases h Lv hv with h1 | h1
    · exact gramBad_lex_false huv hEu hEv hrku hrkv h1
    · rcases h1 Lw hw with h2 | h2
      · exact gramBad_lex_false huw hEu hEw hrku hrkw h2
      · exact gramBad_lex_false hvw hEv hEw hrkv hrkw h2

theorem triOKpW_lex_false {n p : ℕ} {x : Fin n → ℝ³} {P : Fin p → Fin n}
    (hP : Function.Injective (fun i => x (P i)))
    {u v w du1 du2 dv1 dv2 dw1 dw2 : ℝ³}
    (huv : ⟪u, v⟫ ≠ 0) (huw : ⟪u, w⟫ ≠ 0) (hvw : ⟪v, w⟫ ≠ 0)
    {Eu Ev Ew : List (List (Fin p × Fin p))} (hEu : ∀ d ∈ Eu, DecOK x P u d)
    (hEv : ∀ d ∈ Ev, DecOK x P v d) (hEw : ∀ d ∈ Ew, DecOK x P w d)
    {Ruv Ruw Rvw : List (Penc p)} (hRuv : ∀ r ∈ Ruv, PencOK x P u v r)
    (hRuw : ∀ r ∈ Ruw, PencOK x P u w r) (hRvw : ∀ r ∈ Rvw, PencOK x P v w r)
    {Bv Bw : List (List (Fin p))} {Lu Lv Lw : List (Fin p)} (hv : Lv ∈ Bv) (hw : Lw ∈ Bw)
    (hrku : ∀ i j, rk Lu i < rk Lu j → lexKey (x (P i)) u du1 du2 < lexKey (x (P j)) u du1 du2)
    (hrkv : ∀ i j, rk Lv i < rk Lv j → lexKey (x (P i)) v dv1 dv2 < lexKey (x (P j)) v dv1 dv2)
    (hrkw : ∀ i j, rk Lw i < rk Lw j → lexKey (x (P i)) w dw1 dw2 < lexKey (x (P j)) w dw1 dw2)
    (h : triOKpW Eu Ev Ew Ruv Ruw Rvw Bv Bw Lu = true) : False := by
  simp only [triOKpW, Bool.or_eq_true, List.all_eq_true] at h
  rcases h with (h | h) | h
  · exact pairBadW_lex_false hP huv hEu hEv hRuv hrku hrkv (h Lv hv)
  · exact pairBadW_lex_false hP huw hEu hEw hRuw hrku hrkw (h Lw hw)
  · rcases h Lv hv with h1 | h1
    · exact pairBadW_lex_false hP huv hEu hEv hRuv hrku hrkv h1
    · rcases h1 Lw hw with h2 | h2
      · exact pairBadW_lex_false hP huw hEu hEw hRuw hrku hrkw h2
      · exact pairBadW_lex_false hP hvw hEv hEw hRvw hrkv hrkw h2

/-- **Triple closure, tie-tolerant.** -/
theorem triple_closure_lex {m n p : ℕ} {S : Fin m → Finset (Fin n)} {x : Fin n → ℝ³}
    (F : S0xFac m S x) (P : Fin p → Fin n) (u v w : ℝ³) (su sv sw : Fin m → SignType)
    (Ru Rv Rw : List (Rim m p)) (fu fv fw : List (Fin p × Fin p))
    (Eu Ev Ew : List (List (Fin p × Fin p))) (Tu Tv Tw : List (Fin p × Fin p))
    (Vu : ViewDataLex F P u su Ru fu Eu Tu) (Vv : ViewDataLex F P v sv Rv fv Ev Tv)
    (Vw : ViewDataLex F P w sw Rw fw Ew Tw)
    (huv : ⟪u, v⟫ ≠ 0) (huw : ⟪u, w⟫ ≠ 0) (hvw : ⟪v, w⟫ ≠ 0)
    (deps : List (Fin p → SignType))
    (hdeps : ∀ s ∈ deps, ∃ mu : Fin p → ℝ, ∑ i, mu i = 0 ∧ ∑ i, mu i • x (P i) = 0 ∧
      ∀ i, SignType.sign (mu i) = s i)
    (Bv Bw : List (List (Fin p)))
    (hcu : checkTW S P su fu deps Eu Ev Ew Ru Tu Bv Bw = true)
    (hcv : check2W S P sv fv deps Ev Rv Tv Bv = true)
    (hcw : check2W S P sw fw deps Ew Rw Tw Bw = true) : Minimality.Gen.LexAny F := by
  classical
  rcases check2W_extract Vv hdeps hcv with hlex | ⟨dv1, dv2, Lv, hLv, hrkv⟩
  · exact hlex
  rcases check2W_extract Vw hdeps hcw with hlex | ⟨dw1, dw2, Lw, hLw, hrkw⟩
  · exact hlex
  obtain ⟨Wu, hWu, hWu_ext⟩ := weakOrders_sound (fun i => ⟪x (P i), u⟫) Tu Vu.hT
  simp only [checkTW, Bool.and_eq_true, List.all_eq_true] at hcu
  obtain ⟨hvu, hcuW⟩ := hcu
  rcases Bool.or_eq_true _ _ |>.mp (hcuW Wu hWu) with hrim | hall
  · simp only [rimClosedW, Bool.or_eq_true, List.all_eq_true, List.any_eq_true] at hrim
    rcases hrim with hexcl | ⟨ρ, hρ, hrim⟩
    · obtain ⟨ρ0, hρ0⟩ := List.exists_mem_of_ne_nil Ru Vu.hne
      obtain ⟨du1, du2, _, hdetu⟩ := Vu.hR ρ0 hρ0
      obtain ⟨Lu, hLu, _, hrku⟩ := hWu_ext (fun i => lexKey (x (P i)) u du1 du2)
        (fun _ _ h => lexKey_lt_of_lt h)
        (fun i j h => by by_contra hne'; exact lexKey_ne hdetu (fun e => hne' (Vu.hP e)) h)
      exact (exclOK_lex_false (w_ne_zero_of_det3 hdetu) Vu.hforced hdeps Vu.hE hrku (hexcl Lu hLu)).elim
    · obtain ⟨du1, du2, hd1, hdetu⟩ := Vu.hR ρ hρ
      obtain ⟨Lu, hLu, _, hrku⟩ := hWu_ext (fun i => lexKey (x (P i)) u du1 du2)
        (fun _ _ h => lexKey_lt_of_lt h)
        (fun i j h => by by_contra hne'; exact lexKey_ne hdetu (fun e => hne' (Vu.hP e)) h)
      rcases hrim Lu hLu with hexcl | hok
      · exact (exclOK_lex_false (w_ne_zero_of_det3 hdetu) Vu.hforced hdeps Vu.hE hrku hexcl).elim
      · exact lexAny_of_rimOK_lex F P u du1 du2 su ρ (Vu.hsw ρ hρ) hd1 (hvu ρ hρ) hrku hok
  · obtain ⟨ρ0, hρ0⟩ := List.exists_mem_of_ne_nil Ru Vu.hne
    obtain ⟨du1, du2, _, hdetu⟩ := Vu.hR ρ0 hρ0
    obtain ⟨Lu, hLu, _, hrku⟩ := hWu_ext (fun i => lexKey (x (P i)) u du1 du2)
      (fun _ _ h => lexKey_lt_of_lt h)
      (fun i j h => by by_contra hne'; exact lexKey_ne hdetu (fun e => hne' (Vu.hP e)) h)
    rcases Bool.or_eq_true _ _ |>.mp (List.all_eq_true.mp hall Lu hLu) with hexcl | ht
    · exact (exclOK_lex_false (w_ne_zero_of_det3 hdetu) Vu.hforced hdeps Vu.hE hrku hexcl).elim
    · exact (triOK_lex_false huv huw hvw Vu.hE Vv.hE Vw.hE hLv hLw hrku hrkv hrkw ht).elim

/-- **Triple closure with PENC, tie-tolerant.** -/
theorem triple_closure_p_lex {m n p : ℕ} {S : Fin m → Finset (Fin n)} {x : Fin n → ℝ³}
    (F : S0xFac m S x) (P : Fin p → Fin n) (u v w : ℝ³) (su sv sw : Fin m → SignType)
    (Ru Rv Rw : List (Rim m p)) (fu fv fw : List (Fin p × Fin p))
    (Eu Ev Ew : List (List (Fin p × Fin p))) (Tu Tv Tw : List (Fin p × Fin p))
    (Vu : ViewDataLex F P u su Ru fu Eu Tu) (Vv : ViewDataLex F P v sv Rv fv Ev Tv)
    (Vw : ViewDataLex F P w sw Rw fw Ew Tw)
    (huv : ⟪u, v⟫ ≠ 0) (huw : ⟪u, w⟫ ≠ 0) (hvw : ⟪v, w⟫ ≠ 0)
    (deps : List (Fin p → SignType))
    (hdeps : ∀ s ∈ deps, ∃ mu : Fin p → ℝ, ∑ i, mu i = 0 ∧ ∑ i, mu i • x (P i) = 0 ∧
      ∀ i, SignType.sign (mu i) = s i)
    (Ruv Ruw Rvw : List (Penc p)) (hRuv : ∀ r ∈ Ruv, PencOK x P u v r)
    (hRuw : ∀ r ∈ Ruw, PencOK x P u w r) (hRvw : ∀ r ∈ Rvw, PencOK x P v w r)
    (Bv Bw : List (List (Fin p)))
    (hcu : checkTpW S P su fu deps Eu Ev Ew Ruv Ruw Rvw Ru Tu Bv Bw = true)
    (hcv : check2W S P sv fv deps Ev Rv Tv Bv = true)
    (hcw : check2W S P sw fw deps Ew Rw Tw Bw = true) : Minimality.Gen.LexAny F := by
  classical
  rcases check2W_extract Vv hdeps hcv with hlex | ⟨dv1, dv2, Lv, hLv, hrkv⟩
  · exact hlex
  rcases check2W_extract Vw hdeps hcw with hlex | ⟨dw1, dw2, Lw, hLw, hrkw⟩
  · exact hlex
  obtain ⟨Wu, hWu, hWu_ext⟩ := weakOrders_sound (fun i => ⟪x (P i), u⟫) Tu Vu.hT
  simp only [checkTpW, Bool.and_eq_true, List.all_eq_true] at hcu
  obtain ⟨hvu, hcuW⟩ := hcu
  rcases Bool.or_eq_true _ _ |>.mp (hcuW Wu hWu) with hrim | hall
  · simp only [rimClosedW, Bool.or_eq_true, List.all_eq_true, List.any_eq_true] at hrim
    rcases hrim with hexcl | ⟨ρ, hρ, hrim⟩
    · obtain ⟨ρ0, hρ0⟩ := List.exists_mem_of_ne_nil Ru Vu.hne
      obtain ⟨du1, du2, _, hdetu⟩ := Vu.hR ρ0 hρ0
      obtain ⟨Lu, hLu, _, hrku⟩ := hWu_ext (fun i => lexKey (x (P i)) u du1 du2)
        (fun _ _ h => lexKey_lt_of_lt h)
        (fun i j h => by by_contra hne'; exact lexKey_ne hdetu (fun e => hne' (Vu.hP e)) h)
      exact (exclOK_lex_false (w_ne_zero_of_det3 hdetu) Vu.hforced hdeps Vu.hE hrku (hexcl Lu hLu)).elim
    · obtain ⟨du1, du2, hd1, hdetu⟩ := Vu.hR ρ hρ
      obtain ⟨Lu, hLu, _, hrku⟩ := hWu_ext (fun i => lexKey (x (P i)) u du1 du2)
        (fun _ _ h => lexKey_lt_of_lt h)
        (fun i j h => by by_contra hne'; exact lexKey_ne hdetu (fun e => hne' (Vu.hP e)) h)
      rcases hrim Lu hLu with hexcl | hok
      · exact (exclOK_lex_false (w_ne_zero_of_det3 hdetu) Vu.hforced hdeps Vu.hE hrku hexcl).elim
      · exact lexAny_of_rimOK_lex F P u du1 du2 su ρ (Vu.hsw ρ hρ) hd1 (hvu ρ hρ) hrku hok
  · obtain ⟨ρ0, hρ0⟩ := List.exists_mem_of_ne_nil Ru Vu.hne
    obtain ⟨du1, du2, _, hdetu⟩ := Vu.hR ρ0 hρ0
    obtain ⟨Lu, hLu, _, hrku⟩ := hWu_ext (fun i => lexKey (x (P i)) u du1 du2)
      (fun _ _ h => lexKey_lt_of_lt h)
      (fun i j h => by by_contra hne'; exact lexKey_ne hdetu (fun e => hne' (Vu.hP e)) h)
    rcases Bool.or_eq_true _ _ |>.mp (List.all_eq_true.mp hall Lu hLu) with hexcl | ht
    · exact (exclOK_lex_false (w_ne_zero_of_det3 hdetu) Vu.hforced hdeps Vu.hE hrku hexcl).elim
    · exact (triOKpW_lex_false Vu.hP huv huw hvw Vu.hE Vv.hE Vw.hE hRuv hRuw hRvw hLv hLw
        hrku hrkv hrkw ht).elim

end Minimality.PSVC
