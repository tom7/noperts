module

public import Minimality.GenQuad

@[expose] public section

/-!
# Single-view closure (SVC), type-free

Spec: nopert229 notes/GENERALIZE-1122B.md section 1. Fix a view `w`, a point list `P`
(indices of the rim vertices) and a list of rims around `w` (cycles with up/down facets and a
tilt signature for the facets edge-on at `w`). A strict depth order of `P` at `w` is excluded if
it violates a forced pair, or separates the positive from the negative support of a signed
affine dependency (`radon_no_sep`). If every order of `P` is excluded or passes every alternating
quadruple of some rim (a finite Bool check `check`, closed by `decide`), then `Gen.LexAny F`.

Geometry enters only through: the facing signature `sw` at `w` (`hsw`), one tilt `d1` per rim
realizing the rim's tilt signature on the edge-on facets (`hR`), the signed dependencies
(`hdeps`; signs e.g. from `dep_sign_of_facet`), and distinct depths (`hgen`).
-/

set_option autoImplicit false

open scoped RealInnerProductSpace
open Minimality Minimality.LexCell Minimality.H21

namespace Minimality.SVC

/-- A rim around the view: a cycle of indices into the point list, the up and down facets, and
the tilt signature `sd` (read only on the facets edge-on at the view). -/
structure Rim (m p : ℕ) where
  k : ℕ
  [nz : NeZero k]
  c : ZMod k → Fin p
  U : Finset (Fin m)
  Dn : Finset (Fin m)
  sd : Fin m → SignType

attribute [instance] Rim.nz

/-- Rank of `i` in the list `L` (lowest depth first). -/
def rk {p : ℕ} (L : List (Fin p)) (i : Fin p) : ℕ := L.idxOf i

/-- The clause of an alternating quadruple (valleys `v1 v2`, peaks `q1 q2`) holds at the order. -/
def clauseOK {p : ℕ} (L : List (Fin p)) (v1 v2 q1 q2 : Fin p) : Bool :=
  Nat.blt (rk L q1) (rk L v1) || Nat.blt (rk L q2) (rk L v1) ||
    Nat.blt (rk L q1) (rk L v2) || Nat.blt (rk L q2) (rk L v2)

/-- Every alternating quadruple of the rim passes at the order `L`. -/
def rimOK {m p : ℕ} (ρ : Rim m p) (L : List (Fin p)) : Bool :=
  (List.range ρ.k).all fun a => (List.range' (a + 1) (ρ.k - (a + 1))).all fun b =>
    (List.range' (b + 1) (ρ.k - (b + 1))).all fun c =>
      (List.range' (c + 1) (ρ.k - (c + 1))).all fun d =>
        clauseOK L (ρ.c b) (ρ.c d) (ρ.c a) (ρ.c c) && clauseOK L (ρ.c a) (ρ.c c) (ρ.c b) (ρ.c d)

/-- The order puts all positive points of `s` strictly above all negative ones (and `s` has a
positive entry). -/
def sepR {p : ℕ} (s : Fin p → SignType) (L : List (Fin p)) : Bool :=
  (List.finRange p).any (fun i => decide (s i = 1)) &&
    (List.finRange p).all fun i => (List.finRange p).all fun j =>
      !(decide (s i = 1) && decide (s j = -1)) || Nat.blt (rk L j) (rk L i)

/-- Static validity of a rim: length, injectivity, silhouette, facings at the view and tilt. -/
def rimValid {m n p : ℕ} (S : Fin m → Finset (Fin n)) (P : Fin p → Fin n)
    (sw : Fin m → SignType) (ρ : Rim m p) : Bool :=
  decide (4 ≤ ρ.k) && decide (Function.Injective (P ∘ ρ.c)) &&
    decide (S0xCycUD S (P ∘ ρ.c) ρ.U ρ.Dn) &&
    decide (∀ t ∈ ρ.U, sw t = 1 ∨ (sw t = 0 ∧ ρ.sd t = 1)) &&
    decide (∀ t ∈ ρ.Dn, sw t = -1 ∨ (sw t = 0 ∧ ρ.sd t = -1))

/-- The finite check: rims valid, and every order of `P` (a permutation list, lowest first) is
excluded by a forced pair `(i, j)` (meaning `z j < z i`) or a dependency, or passes some rim. -/
def check {m n p : ℕ} (S : Fin m → Finset (Fin n)) (P : Fin p → Fin n) (sw : Fin m → SignType)
    (forced : List (Fin p × Fin p)) (deps : List (Fin p → SignType)) (R : List (Rim m p)) : Bool :=
  R.all (rimValid S P sw) &&
    (List.finRange p).permutations'.all fun L =>
      forced.any (fun ij => Nat.blt (rk L ij.1) (rk L ij.2)) ||
        deps.any (fun s => sepR s L || sepR (fun i => -s i) L) ||
        R.any (fun ρ => rimOK ρ L)

/-! ### Support lemmas -/

/-- **Radon, no separation**: an affine dependency (`∑ mu = 0`, `∑ mu z = 0` for the depths `z`)
with a positive weight never has all positive points strictly above all negative ones. -/
theorem radon_no_sep {p : ℕ} (mu z : Fin p → ℝ) (hsum : ∑ i, mu i = 0)
    (hz : ∑ i, mu i * z i = 0) (hpos : ∃ i, 0 < mu i)
    (hsep : ∀ i j, 0 < mu i → mu j < 0 → z j < z i) : False := by
  classical
  obtain ⟨i0, hi0⟩ := hpos
  obtain ⟨a, ha, hmin⟩ := Finset.exists_min_image (Finset.univ.filter fun i => 0 < mu i) z
    ⟨i0, by simp [hi0]⟩
  have ha' : 0 < mu a := (Finset.mem_filter.mp ha).2
  have hterm : ∀ i, 0 ≤ mu i * (z i - z a) := by
    intro i
    rcases lt_trichotomy (mu i) 0 with h | h | h
    · have := hsep a i ha' h; nlinarith
    · simp [h]
    · have := hmin i (by simp [h]); nlinarith
  have hsum0 : ∑ i, mu i * (z i - z a) = 0 := by
    have : ∑ i, mu i * (z i - z a) = ∑ i, mu i * z i - (∑ i, mu i) * z a := by
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib]; simp [mul_sub]
    rw [this, hz, hsum]; ring
  have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hterm i)).mp hsum0
  have hnn : ∀ i, 0 ≤ mu i := by
    intro i; by_contra h; push Not at h
    have h1 := hall i (Finset.mem_univ _)
    have := hsep a i ha' h
    have : 0 < mu i * (z i - z a) := mul_pos_of_neg_of_neg h (by linarith)
    linarith
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hnn i)).mp hsum i0 (Finset.mem_univ _)
  linarith

/-- Depth form of a dependency. -/
theorem dep_depth {p : ℕ} (mu : Fin p → ℝ) (y : Fin p → ℝ³) (hdep : ∑ i, mu i • y i = 0)
    (w : ℝ³) : ∑ i, mu i * ⟪y i, w⟫ = 0 := by
  have h := congrArg (fun v => ⟪v, w⟫) hdep
  simp only [sum_inner, real_inner_smul_left, inner_zero_left] at h
  exact h

/-- **Facet pairing**: if exactly two support points `i ≠ j` of an affine dependency lie off
facet `t`, their weights have opposite signs. -/
theorem dep_sign_of_facet {m n p : ℕ} {S : Fin m → Finset (Fin n)} {x : Fin n → ℝ³}
    (F : S0xFac m S x) (P : Fin p → Fin n) (mu : Fin p → ℝ) (hsum : ∑ i, mu i = 0)
    (hdep : ∑ i, mu i • x (P i) = 0) (t : Fin m) {i j : Fin p} (hij : i ≠ j)
    (hi : P i ∉ S t) (hj : P j ∉ S t) (hon : ∀ l, l ≠ i → l ≠ j → P l ∈ S t) :
    SignType.sign (mu i) = -SignType.sign (mu j) := by
  have hf : ∀ y, F.f t y = F.f t 0 + ⟪F.N t, y⟫ := by
    intro y; have := F.hN t y 0; rw [sub_zero] at this; linarith
  have hs : ∑ l, mu l * F.f t (x (P l)) = 0 := by
    have hf' : ∀ l, mu l * F.f t (x (P l)) = mu l * F.f t 0 + mu l * ⟪F.N t, x (P l)⟫ := by
      intro l; rw [hf (x (P l)), mul_add]
    simp only [hf']
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, hsum, zero_mul, zero_add]
    have := dep_depth mu (fun l => x (P l)) hdep (F.N t)
    simpa [real_inner_comm] using this
  rw [Fintype.sum_eq_add i j hij (fun l hl => by rw [F.zero t _ (hon l hl.1 hl.2), mul_zero])]
    at hs
  have fi := F.neg t _ hi
  have fj := F.neg t _ hj
  rcases lt_trichotomy (mu j) 0 with h | h | h
  · have : 0 < mu i := by
      by_contra hc; push Not at hc; nlinarith [mul_nonneg_of_nonpos_of_nonpos hc fi.le]
    rw [sign_pos this, sign_neg h]; try rfl
  · have : mu i = 0 := by
      rw [h, zero_mul, add_zero] at hs
      exact (mul_eq_zero.mp hs).resolve_right fi.ne
    rw [this, h, sign_zero]; rfl
  · have : mu i < 0 := by
      by_contra hc; push Not at hc; nlinarith [mul_nonpos_of_nonneg_of_nonpos hc fi.le]
    rw [sign_neg this, sign_pos h]

/-! ### Soundness of the pieces -/

theorem clauseOK_sound {p : ℕ} {L : List (Fin p)} {z : Fin p → ℝ}
    (hrk : ∀ i j, rk L i < rk L j → z i < z j) {y : Fin p → ℝ³} {w d1 d2 : ℝ³}
    (hz : ∀ i, ⟪y i, w⟫ = z i) {v1 v2 q1 q2 : Fin p} (h : clauseOK L v1 v2 q1 q2 = true) :
    Minimality.GenQuad.LexClause (y v1) (y v2) (y q1) (y q2) w d1 d2 := by
  apply Minimality.GenQuad.lexClause_of_notM
  rintro ⟨h1, h2, h3, h4⟩
  simp only [clauseOK, Bool.or_eq_true, Nat.blt_eq] at h
  rw [hz, hz] at h1 h2 h3 h4
  rcases h with ((h | h) | h) | h
  · linarith [hrk _ _ h]
  · linarith [hrk _ _ h]
  · linarith [hrk _ _ h]
  · linarith [hrk _ _ h]

theorem sepR_sound {p : ℕ} {L : List (Fin p)} {z mu : Fin p → ℝ} {s : Fin p → SignType}
    (hrk : ∀ i j, rk L i < rk L j → z i < z j) (hsg : ∀ i, SignType.sign (mu i) = s i)
    (hsum : ∑ i, mu i = 0) (hz : ∑ i, mu i * z i = 0) (h : sepR s L = true) : False := by
  simp only [sepR, Bool.and_eq_true, List.any_eq_true, List.all_eq_true, List.mem_finRange,
    true_and, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff,
    decide_eq_false_iff_not, Nat.blt_eq, forall_const] at h
  obtain ⟨⟨i0, hi0⟩, hall⟩ := h
  refine radon_no_sep mu z hsum hz ⟨i0, ?_⟩ ?_
  · rw [← sign_eq_one_iff, hsg, hi0]
  · intro i j hi hj
    rcases hall i j with (h | h) | h
    · exact absurd (by rw [← hsg]; exact sign_pos hi) h
    · exact absurd (by rw [← hsg]; exact sign_neg hj) h
    · exact hrk _ _ h

/-- `rimOK` gives the clause hypothesis of `GenQuad.lexAny_of_clauses`. -/
theorem rimOK_sound {m p : ℕ} {L : List (Fin p)} {z : Fin p → ℝ}
    (hrk : ∀ i j, rk L i < rk L j → z i < z j) {y : Fin p → ℝ³} {w d1 d2 : ℝ³}
    (hz : ∀ i, ⟪y i, w⟫ = z i) (ρ : Rim m p) (h : rimOK ρ L = true) :
    ∀ (B : ZMod ρ.k) (b' c' d' : ℕ), 0 < b' → b' < c' → c' < d' → d' < ρ.k →
      Minimality.GenQuad.LexClause (y (ρ.c (B + b'))) (y (ρ.c (B + d'))) (y (ρ.c B))
        (y (ρ.c (B + c'))) w d1 d2 := by
  simp only [rimOK, List.all_eq_true, List.mem_range, List.mem_range', Bool.and_eq_true] at h
  have key : ∀ a b c d : ℕ, a < b → b < c → c < d → d < ρ.k →
      clauseOK L (ρ.c b) (ρ.c d) (ρ.c a) (ρ.c c) = true ∧
        clauseOK L (ρ.c a) (ρ.c c) (ρ.c b) (ρ.c d) = true := by
    intro a b c d hab hbc hcd hd
    exact h a (by omega) b ⟨b - (a + 1), by omega, by omega⟩ c ⟨c - (b + 1), by omega, by omega⟩
      d ⟨d - (c + 1), by omega, by omega⟩
  apply Minimality.GenQuad.clauses_of_sorted (p := fun i => y (ρ.c i))
  · refine Minimality.GenQuad.sorted_cases _ ?_
    intro a b c d hab hbc hcd hd
    exact clauseOK_sound hrk hz (key a b c d hab hbc hcd hd).1
  · refine Minimality.GenQuad.sorted_cases _ ?_
    intro a b c d hab hbc hcd hd
    exact clauseOK_sound hrk hz (key a b c d hab hbc hcd hd).2

/-- The sorted order: a permutation list of `Fin p` whose ranks are strictly monotone in `z`
(for injective `z`). -/
theorem exists_order {p : ℕ} (z : Fin p → ℝ) (hz : Function.Injective z) :
    ∃ L ∈ (List.finRange p).permutations', ∀ i j, rk L i < rk L j → z i < z j := by
  let σ := Tuple.sort z
  have hmono := Tuple.monotone_sort z
  refine ⟨List.ofFn σ, ?_, ?_⟩
  · rw [List.mem_permutations']
    have := Equiv.Perm.ofFn_comp_perm σ id
    simpa [List.ofFn_id] using this
  · have hnd : (List.ofFn σ).Nodup := List.nodup_ofFn.mpr σ.injective
    have hrkσ : ∀ a, rk (List.ofFn σ) (σ a) = a := by
      intro a
      have := hnd.idxOf_getElem a (by simp)
      simpa [rk, List.getElem_ofFn] using this
    intro i j h
    obtain ⟨a, rfl⟩ := σ.surjective i
    obtain ⟨b, rfl⟩ := σ.surjective j
    rw [hrkσ, hrkσ] at h
    have hle : z (σ a) ≤ z (σ b) := hmono (Fin.le_of_lt (Fin.lt_def.mpr h))
    refine lt_of_le_of_ne hle (fun e => ?_)
    have := σ.injective (hz e)
    subst this
    exact lt_irrefl _ h

/-! ### Main theorem -/

/-- **Single-view closure.** -/
theorem single_view_closure {m n p : ℕ} {S : Fin m → Finset (Fin n)} {x : Fin n → ℝ³}
    (F : S0xFac m S x) (P : Fin p → Fin n) (w : ℝ³) (sw : Fin m → SignType)
    (hsw : ∀ t, SignType.sign ⟪F.N t, w⟫ = sw t)
    (R : List (Rim m p))
    (hR : ∀ ρ ∈ R, ∃ d1 : ℝ³, ∀ t, sw t = 0 → SignType.sign ⟪F.N t, d1⟫ = ρ.sd t)
    (forced : List (Fin p × Fin p))
    (hforced : ∀ ij ∈ forced, ⟪x (P ij.2), w⟫ < ⟪x (P ij.1), w⟫)
    (deps : List (Fin p → SignType))
    (hdeps : ∀ s ∈ deps, ∃ mu : Fin p → ℝ, ∑ i, mu i = 0 ∧ ∑ i, mu i • x (P i) = 0 ∧
      ∀ i, SignType.sign (mu i) = s i)
    (hgen : ∀ i j, i ≠ j → ⟪x (P i), w⟫ ≠ ⟪x (P j), w⟫)
    (hcheck : check S P sw forced deps R = true) : Minimality.Gen.LexAny F := by
  classical
  set z : Fin p → ℝ := fun i => ⟪x (P i), w⟫ with hzdef
  have hzinj : Function.Injective z := fun i j h => by
    by_contra hne; exact hgen i j hne h
  obtain ⟨L, hL, hrk⟩ := exists_order z hzinj
  simp only [check, Bool.and_eq_true, List.all_eq_true] at hcheck
  obtain ⟨hval, hperm⟩ := hcheck
  have hL' := hperm L hL
  simp only [Bool.or_eq_true, List.any_eq_true] at hL'
  rcases hL' with (⟨ij, hij, hlt⟩ | ⟨s, hs, hsep⟩) | ⟨ρ, hρ, hok⟩
  · rw [Nat.blt_eq] at hlt
    exact absurd (hforced ij hij) (not_lt.mpr (hrk _ _ hlt).le)
  · exfalso
    obtain ⟨mu, hsum, hdep, hsg⟩ := hdeps s hs
    have hz : ∑ i, mu i * z i = 0 := dep_depth mu (fun i => x (P i)) hdep w
    rcases hsep with h | h
    · exact sepR_sound hrk hsg hsum hz h
    · refine sepR_sound (mu := fun i => -mu i) hrk (fun i => ?_) ?_ ?_ h
      · rw [Left.sign_neg, hsg]
      · rw [Finset.sum_neg_distrib, hsum, neg_zero]
      · simp only [neg_mul, Finset.sum_neg_distrib, hz, neg_zero]
  · have hv := hval ρ hρ
    simp only [rimValid, Bool.and_eq_true, decide_eq_true_eq] at hv
    obtain ⟨⟨⟨⟨hk, hinj⟩, hcyc⟩, hU⟩, hD⟩ := hv
    obtain ⟨d1, hd1⟩ := hR ρ hρ
    refine Minimality.GenQuad.lexAny_of_clauses F hk hinj hcyc w d1 0 ?_ ?_ ?_
    · intro t ht
      rw [inner_zero_right]
      rcases hU t ht with h | ⟨h0, h1⟩
      · exact Or.inl (sign_eq_one_iff.mp ((hsw t).trans h))
      · refine Or.inr ⟨sign_eq_zero_iff.mp ((hsw t).trans h0), Or.inl ?_⟩
        exact sign_eq_one_iff.mp ((hd1 t h0).trans h1)
    · intro t ht
      rw [inner_zero_right, neg_zero]
      rcases hD t ht with h | ⟨h0, h1⟩
      · exact Or.inl (neg_pos.mpr (sign_eq_neg_one_iff.mp ((hsw t).trans h)))
      · refine Or.inr ⟨neg_eq_zero.mpr (sign_eq_zero_iff.mp ((hsw t).trans h0)), Or.inl ?_⟩
        exact neg_pos.mpr (sign_eq_neg_one_iff.mp ((hd1 t h0).trans h1))
    · exact rimOK_sound hrk (y := fun i => x (P i)) (fun i => rfl) ρ hok

end Minimality.SVC
