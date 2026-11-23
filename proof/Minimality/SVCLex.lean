module

public import Minimality.SVC
public import Minimality.GenQuadCross

@[expose] public section

/-!
# Single-view closure with lexicographic depths (SVCLex), type-free

The finite `SVC.check` of `SVC.single_view_closure` (one rim, no dependencies), but the rim points
are ordered by the lexicographic order of their depth triples `(⟪y, w⟫, ⟪y, d1⟫, ⟪y, d2⟫)`, where
`d1` is the rim tilt. So depth ties at the view `w` need no hypothesis: when `w, d1, d2` is a basis
(`Split.det3 w d1 d2 ≠ 0`), distinct points have distinct triples (`GenQuad.depth_injective`), and
`d2` is otherwise free (the facings are decided by `w` and `d1`). Forced pairs are strict at `w`.
Use it in place of `single_view_closure` whenever the `hgen` (distinct depths) input is open.
-/

set_option autoImplicit false

open scoped RealInnerProductSpace
open Minimality Minimality.LexCell Minimality.H21

namespace Minimality.SVC

/-- The lexicographic depth key of `y` at `(w, d1, d2)`. -/
noncomputable def lexKey (y w d1 d2 : ℝ³) : Lex (ℝ × Lex (ℝ × ℝ)) :=
  toLex (⟪y, w⟫, toLex (⟪y, d1⟫, ⟪y, d2⟫))

theorem lexLt3_of_lexKey_lt {y z w d1 d2 : ℝ³} (h : lexKey y w d1 d2 < lexKey z w d1 d2) :
    LexLt3 (⟪y, w⟫, ⟪y, d1⟫, ⟪y, d2⟫) (⟪z, w⟫, ⟪z, d1⟫, ⟪z, d2⟫) := by
  unfold lexKey at h
  rw [Prod.Lex.toLex_lt_toLex] at h
  unfold LexLt3 LexPos3
  rcases h with h | ⟨h1, h2⟩
  · exact Or.inl (sub_pos.mpr h)
  · refine Or.inr ⟨sub_eq_zero.mpr h1.symm, ?_⟩
    rw [Prod.Lex.toLex_lt_toLex] at h2
    rcases h2 with h | ⟨h1', h2'⟩
    · exact Or.inl (sub_pos.mpr h)
    · exact Or.inr ⟨sub_eq_zero.mpr h1'.symm, sub_pos.mpr h2'⟩

theorem lexKey_lt_of_lt {y z w d1 d2 : ℝ³} (h : ⟪y, w⟫ < ⟪z, w⟫) :
    lexKey y w d1 d2 < lexKey z w d1 d2 := by
  unfold lexKey
  exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl h)

theorem lexKey_ne {y z w d1 d2 : ℝ³} (hdet : Split.det3 w d1 d2 ≠ 0) (hyz : y ≠ z) :
    lexKey y w d1 d2 ≠ lexKey z w d1 d2 := by
  intro h
  unfold lexKey at h
  have h' := toLex.injective h
  simp only [Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq] at h'
  obtain ⟨h0, h1, h2⟩ := h'
  refine hyz (sub_eq_zero.mp (GenQuad.depth_injective hdet ?_ ?_ ?_)) <;>
    rw [inner_sub_left] <;> linarith

/-- `exists_order` for any linearly ordered key. -/
theorem exists_order_lin {p : ℕ} {α : Type*} [LinearOrder α] (z : Fin p → α)
    (hz : Function.Injective z) :
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

theorem clauseOK_lex_sound {p : ℕ} {L : List (Fin p)} {y : Fin p → ℝ³} {w d1 d2 : ℝ³}
    (hrk : ∀ i j, rk L i < rk L j → lexKey (y i) w d1 d2 < lexKey (y j) w d1 d2)
    {v1 v2 q1 q2 : Fin p} (h : clauseOK L v1 v2 q1 q2 = true) :
    Minimality.GenQuad.LexClause (y v1) (y v2) (y q1) (y q2) w d1 d2 := by
  simp only [clauseOK, Bool.or_eq_true, Nat.blt_eq] at h
  unfold Minimality.GenQuad.LexClause
  rcases h with ((h | h) | h) | h
  · exact Or.inl (lexLt3_of_lexKey_lt (hrk _ _ h))
  · exact Or.inr (Or.inl (lexLt3_of_lexKey_lt (hrk _ _ h)))
  · exact Or.inr (Or.inr (Or.inl (lexLt3_of_lexKey_lt (hrk _ _ h))))
  · exact Or.inr (Or.inr (Or.inr (lexLt3_of_lexKey_lt (hrk _ _ h))))

theorem rimOK_lex_sound {m p : ℕ} {L : List (Fin p)} {y : Fin p → ℝ³} {w d1 d2 : ℝ³}
    (hrk : ∀ i j, rk L i < rk L j → lexKey (y i) w d1 d2 < lexKey (y j) w d1 d2)
    (ρ : Rim m p) (h : rimOK ρ L = true) :
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
    exact clauseOK_lex_sound hrk (key a b c d hab hbc hcd hd).1
  · refine Minimality.GenQuad.sorted_cases _ ?_
    intro a b c d hab hbc hcd hd
    exact clauseOK_lex_sound hrk (key a b c d hab hbc hcd hd).2

/-- **Single-view closure, lexicographic depths.** As `single_view_closure` with one rim `ρ` and
no dependencies, but without `hgen`: the points are ordered by their depth triples at
`(w, d1, d2)`, `d1` the rim tilt, `w, d1, d2` a basis, and the points of `P` distinct. -/
theorem single_view_closure_lex {m n p : ℕ} {S : Fin m → Finset (Fin n)} {x : Fin n → ℝ³}
    (F : S0xFac m S x) (P : Fin p → Fin n) (w d1 d2 : ℝ³) (sw : Fin m → SignType)
    (hsw : ∀ t, SignType.sign ⟪F.N t, w⟫ = sw t) (ρ : Rim m p)
    (hd1 : ∀ t, sw t = 0 → SignType.sign ⟪F.N t, d1⟫ = ρ.sd t)
    (forced : List (Fin p × Fin p))
    (hforced : ∀ ij ∈ forced, ⟪x (P ij.2), w⟫ < ⟪x (P ij.1), w⟫)
    (hP : Function.Injective (fun i => x (P i))) (hdet : Split.det3 w d1 d2 ≠ 0)
    (hcheck : check S P sw forced [] [ρ] = true) : Minimality.Gen.LexAny F := by
  classical
  set z : Fin p → Lex (ℝ × Lex (ℝ × ℝ)) := fun i => lexKey (x (P i)) w d1 d2 with hzdef
  have hzinj : Function.Injective z := fun i j h => by
    by_contra hne; exact lexKey_ne hdet (fun e => hne (hP e)) h
  obtain ⟨L, hL, hrk⟩ := exists_order_lin z hzinj
  simp only [check, Bool.and_eq_true, List.all_eq_true] at hcheck
  obtain ⟨hval, hperm⟩ := hcheck
  have hL' := hperm L hL
  simp only [Bool.or_eq_true, List.any_eq_true] at hL'
  rcases hL' with (⟨ij, hij, hlt⟩ | ⟨s, hs, -⟩) | ⟨ρ', hρ', hok⟩
  · rw [Nat.blt_eq] at hlt
    exact absurd (hrk _ _ hlt) (lt_asymm (lexKey_lt_of_lt (hforced ij hij)))
  · simp at hs
  · simp only [List.mem_singleton] at hρ'
    subst hρ'
    have hv := hval ρ' (List.mem_singleton_self _)
    simp only [rimValid, Bool.and_eq_true, decide_eq_true_eq] at hv
    obtain ⟨⟨⟨⟨hk, hinj⟩, hcyc⟩, hU⟩, hD⟩ := hv
    refine Minimality.GenQuad.lexAny_of_clauses F hk hinj hcyc w d1 d2 ?_ ?_ ?_
    · intro t ht
      rcases hU t ht with h | ⟨h0, h1⟩
      · exact Or.inl (sign_eq_one_iff.mp ((hsw t).trans h))
      · refine Or.inr ⟨sign_eq_zero_iff.mp ((hsw t).trans h0), Or.inl ?_⟩
        exact sign_eq_one_iff.mp ((hd1 t h0).trans h1)
    · intro t ht
      rcases hD t ht with h | ⟨h0, h1⟩
      · exact Or.inl (neg_pos.mpr (sign_eq_neg_one_iff.mp ((hsw t).trans h)))
      · refine Or.inr ⟨neg_eq_zero.mpr (sign_eq_zero_iff.mp ((hsw t).trans h0)), Or.inl ?_⟩
        exact neg_pos.mpr (sign_eq_neg_one_iff.mp ((hd1 t h0).trans h1))
    · exact rimOK_lex_sound hrk (y := fun i => x (P i)) ρ' hok

theorem w_ne_zero_of_det3 {w d1 d2 : ℝ³} (h : Split.det3 w d1 d2 ≠ 0) : w ≠ 0 := by
  intro hw
  subst hw
  apply h
  unfold Split.det3
  simp

/-- If `w ≠ 0` and `d1` is not a scalar multiple of `w` (witnessed by a vector `N` orthogonal
to `w` but not to `d1`), then there exists `d2` with `Split.det3 w d1 d2 ≠ 0`. -/
theorem exists_det3_ne_zero {w d1 N1 N2 : ℝ³} (hw : ⟪N1, w⟫ ≠ 0)
    (hNw : ⟪N2, w⟫ = 0) (hNd : ⟪N2, d1⟫ ≠ 0) :
    ∃ d2 : ℝ³, Split.det3 w d1 d2 ≠ 0 := by
  let d2 : ℝ³ := !₂[w 1 * d1 2 - w 2 * d1 1, w 2 * d1 0 - w 0 * d1 2, w 0 * d1 1 - w 1 * d1 0]
  refine ⟨d2, fun h0 => ?_⟩
  have hsq : (w 1 * d1 2 - w 2 * d1 1) ^ 2 + (w 2 * d1 0 - w 0 * d1 2) ^ 2 +
      (w 0 * d1 1 - w 1 * d1 0) ^ 2 = 0 := by
    simpa [Split.det3, d2, sq] using h0
  have hc0 : w 1 * d1 2 - w 2 * d1 1 = 0 := by nlinarith
  have hc1 : w 2 * d1 0 - w 0 * d1 2 = 0 := by nlinarith
  have hc2 : w 0 * d1 1 - w 1 * d1 0 = 0 := by nlinarith
  have hw0 : w ≠ 0 := fun h => hw (by simp [h])
  have hcoord : w 0 ≠ 0 ∨ w 1 ≠ 0 ∨ w 2 ≠ 0 := by
    by_contra h
    push_neg at h
    exact hw0 (by ext i; fin_cases i <;> simp [h])
  have hcol : ∃ c : ℝ, d1 = c • w := by
    rcases hcoord with h | h | h
    · refine ⟨d1 0 / w 0, ?_⟩
      ext i; fin_cases i
      · simp [PiLp.smul_apply, smul_eq_mul, div_mul_cancel₀ _ h]
      · simp only [PiLp.smul_apply, smul_eq_mul, div_mul_eq_mul_div]
        exact (eq_div_iff h).mpr (by change d1 1 * w 0 = d1 0 * w 1; linarith)
      · simp only [PiLp.smul_apply, smul_eq_mul, div_mul_eq_mul_div]
        exact (eq_div_iff h).mpr (by change d1 2 * w 0 = d1 0 * w 2; linarith)
    · refine ⟨d1 1 / w 1, ?_⟩
      ext i; fin_cases i
      · simp only [PiLp.smul_apply, smul_eq_mul, div_mul_eq_mul_div]
        exact (eq_div_iff h).mpr (by change d1 0 * w 1 = d1 1 * w 0; linarith)
      · simp [PiLp.smul_apply, smul_eq_mul, div_mul_cancel₀ _ h]
      · simp only [PiLp.smul_apply, smul_eq_mul, div_mul_eq_mul_div]
        exact (eq_div_iff h).mpr (by change d1 2 * w 1 = d1 1 * w 2; linarith)
    · refine ⟨d1 2 / w 2, ?_⟩
      ext i; fin_cases i
      · simp only [PiLp.smul_apply, smul_eq_mul, div_mul_eq_mul_div]
        exact (eq_div_iff h).mpr (by change d1 0 * w 2 = d1 2 * w 0; linarith)
      · simp only [PiLp.smul_apply, smul_eq_mul, div_mul_eq_mul_div]
        exact (eq_div_iff h).mpr (by change d1 1 * w 2 = d1 2 * w 1; linarith)
      · simp [PiLp.smul_apply, smul_eq_mul, div_mul_cancel₀ _ h]
  obtain ⟨c, rfl⟩ := hcol
  rw [real_inner_smul_right, hNw, mul_zero] at hNd
  exact hNd rfl

/-- **Radon, no separation (lexicographic)**: an affine dependency `∑ mu = 0`, `∑ mu • y = 0`
cannot separate positive and negative weights in `lexKey y w d1 d2`. -/
theorem radon_no_sep_lex {p : ℕ} (mu : Fin p → ℝ) (y : Fin p → ℝ³) (w d1 d2 : ℝ³)
    (hsum : ∑ i, mu i = 0) (hy : ∑ i, mu i • y i = 0) (hpos : ∃ i, 0 < mu i)
    (hsep : ∀ i j, 0 < mu i → mu j < 0 → lexKey (y j) w d1 d2 < lexKey (y i) w d1 d2) :
    False := by
  classical
  have hz_eq : ∀ u : ℝ³, ∑ i, mu i * ⟪y i, u⟫ = 0 := fun u => dep_depth mu y hy u
  -- Helper: if `∀ i j, 0 < mu i → mu j < 0 → z j ≤ z i` and `∑ mu_i z_i = 0`, then `z` is
  -- constant on `{i | mu i ≠ 0}`.
  have const_of_le : ∀ z : Fin p → ℝ, ∑ i, mu i * z i = 0 →
      (∀ i j, 0 < mu i → mu j < 0 → z j ≤ z i) →
      ∃ c : ℝ, ∀ i, mu i ≠ 0 → z i = c := by
    intro z hz hle
    obtain ⟨i0, hi0⟩ := hpos
    obtain ⟨a, ha, hmin⟩ := Finset.exists_min_image (Finset.univ.filter fun i => 0 < mu i) z
      ⟨i0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi0⟩⟩
    have ha_pos : 0 < mu a := (Finset.mem_filter.mp ha).2
    have hnonneg : ∀ i, 0 ≤ mu i * (z i - z a) := by
      intro i
      rcases lt_trichotomy (mu i) 0 with hi | hi | hi
      · have hja : z i ≤ z a := hle a i ha_pos hi
        exact mul_nonneg_of_nonpos_of_nonpos hi.le (sub_nonpos.mpr hja)
      · simp [hi]
      · have hai : z a ≤ z i := hmin i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)
        exact mul_nonneg hi.le (sub_nonneg.mpr hai)
    have hsum0 : ∑ i, mu i * (z i - z a) = 0 := by
      simp_rw [mul_sub, Finset.sum_sub_distrib, hz, ← Finset.sum_mul, hsum, zero_mul, sub_zero]
    have hzero : ∀ i ∈ Finset.univ, mu i * (z i - z a) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hnonneg i)).mp hsum0
    refine ⟨z a, fun i hmi => ?_⟩
    have := mul_eq_zero.mp (hzero i (Finset.mem_univ i))
    exact sub_eq_zero.mp (this.resolve_left hmi)
  have hle0 : ∀ i j, 0 < mu i → mu j < 0 → ⟪y j, w⟫ ≤ ⟪y i, w⟫ := by
    intro i j hi hj
    have h := hsep i j hi hj
    unfold lexKey at h
    rw [Prod.Lex.toLex_lt_toLex] at h
    rcases h with h | ⟨h, _⟩
    · exact h.le
    · exact h.le
  obtain ⟨c0, hc0⟩ := const_of_le (fun i => ⟪y i, w⟫) (hz_eq w) hle0
  have hle1 : ∀ i j, 0 < mu i → mu j < 0 → ⟪y j, d1⟫ ≤ ⟪y i, d1⟫ := by
    intro i j hi hj
    have h := hsep i j hi hj
    unfold lexKey at h
    rw [Prod.Lex.toLex_lt_toLex, Prod.Lex.toLex_lt_toLex] at h
    have ej : ⟪y j, w⟫ = c0 := hc0 j hj.ne
    have ei : ⟪y i, w⟫ = c0 := hc0 i hi.ne'
    rcases h with h | ⟨_, h | ⟨h, _⟩⟩
    · linarith
    · exact h.le
    · exact h.le
  obtain ⟨c1, hc1⟩ := const_of_le (fun i => ⟪y i, d1⟫) (hz_eq d1) hle1
  refine radon_no_sep mu (fun i => ⟪y i, d2⟫) hsum (hz_eq d2) hpos ?_
  intro i j hi hj
  have h := hsep i j hi hj
  unfold lexKey at h
  rw [Prod.Lex.toLex_lt_toLex, Prod.Lex.toLex_lt_toLex] at h
  have ej0 : ⟪y j, w⟫ = c0 := hc0 j hj.ne
  have ei0 : ⟪y i, w⟫ = c0 := hc0 i hi.ne'
  have ej1 : ⟪y j, d1⟫ = c1 := hc1 j hj.ne
  have ei1 : ⟪y i, d1⟫ = c1 := hc1 i hi.ne'
  rcases h with h | ⟨_, h | ⟨_, h⟩⟩
  · linarith
  · linarith
  · exact h

theorem sepR_lex_sound {n p : ℕ} {L : List (Fin p)} {x : Fin n → ℝ³} {P : Fin p → Fin n}
    {w d1 d2 : ℝ³} {mu : Fin p → ℝ} {s : Fin p → SignType}
    (hrk : ∀ i j, rk L i < rk L j → lexKey (x (P i)) w d1 d2 < lexKey (x (P j)) w d1 d2)
    (hsg : ∀ i, SignType.sign (mu i) = s i) (hsum : ∑ i, mu i = 0)
    (hy : ∑ i, mu i • x (P i) = 0) (h : sepR s L = true) : False := by
  simp only [sepR, Bool.and_eq_true, List.any_eq_true, List.all_eq_true, List.mem_finRange,
    true_and, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff,
    decide_eq_false_iff_not, Nat.blt_eq, forall_const] at h
  obtain ⟨⟨i0, hi0⟩, hall⟩ := h
  refine radon_no_sep_lex mu (fun i => x (P i)) w d1 d2 hsum hy ⟨i0, ?_⟩ ?_
  · rw [← sign_eq_one_iff, hsg, hi0]
  · intro i j hi hj
    rcases hall i j with (h | h) | h
    · exact absurd (by rw [← hsg]; exact sign_pos hi) h
    · exact absurd (by rw [← hsg]; exact sign_neg hj) h
    · exact hrk _ _ h

/-! ### Weak-order enumeration with allowed tie pairs `T` -/

/-- Whether two indices are allowed to tie according to `T`. -/
def allowPair {p : ℕ} (T : List (Fin p × Fin p)) (a b : Fin p) : Bool :=
  T.contains (a, b) || T.contains (b, a)

/-- All non-empty cliques in `rem` (with respect to `allowPair T`) extending `cur`. -/
def addCliques {p : ℕ} (T : List (Fin p × Fin p)) (cur : List (Fin p)) :
    List (Fin p) → List (List (Fin p))
  | [] => if cur.isEmpty then [] else [cur.reverse]
  | y :: ys =>
    let without := addCliques T cur ys
    if cur.all (fun x => allowPair T x y) then
      addCliques T (y :: cur) ys ++ without
    else without

/-- Ordered partitions of `rem` into `T`-cliques (bounded by `fuel`). -/
def weakOrdersAux {p : ℕ} (T : List (Fin p × Fin p)) :
    ℕ → List (Fin p) → List (List (List (Fin p)))
  | 0, _ => [[]]
  | fuel + 1, rem =>
    if rem.isEmpty then [[]]
    else (addCliques T [] rem).flatMap fun B =>
      (weakOrdersAux T fuel (rem.filter fun x => !B.contains x)).map (B :: ·)

/-- All weak orders on `Fin p` whose tie blocks only contain pairs in `T`. -/
def weakOrders (p : ℕ) (T : List (Fin p × Fin p)) : List (List (List (Fin p))) :=
  weakOrdersAux T p (List.finRange p)

/-- All linear extensions of an ordered partition `W`. -/
def linExts {p : ℕ} : List (List (Fin p)) → List (List (Fin p))
  | [] => [[]]
  | B :: W => B.permutations'.flatMap fun perm => (linExts W).map (perm ++ ·)

private theorem addCliques_ne_nil {p : ℕ} {T : List (Fin p × Fin p)}
    {cur rem B : List (Fin p)} (hB : B ∈ addCliques T cur rem) : B ≠ [] := by
  induction rem generalizing cur with
  | nil =>
    simp only [addCliques] at hB
    split_ifs at hB with h
    · simp at hB
    · simp only [List.mem_singleton] at hB
      subst hB
      intro hrev
      have : cur = [] := by simpa using congrArg List.reverse hrev
      simp [this] at h
  | cons y ys ih =>
    simp only [addCliques] at hB
    split_ifs at hB
    · rcases List.mem_append.mp hB with h1 | h2
      · exact ih h1
      · exact ih h2
    · exact ih hB

/-- Split a Boolean check over `weakOrders p T` by the minimum element `a : Fin p` of the first block. -/
theorem weakOrders_split {p : ℕ} (hp : 0 < p) (T : List (Fin p × Fin p))
    (f : List (List (Fin p)) → Bool)
    (h : ∀ a : Fin p,
      ((addCliques T [] (List.finRange p)).filter (fun B => B.head? == some a)).all (fun B =>
        (weakOrdersAux T (p - 1) ((List.finRange p).filter fun x => !B.contains x)).all fun W =>
          f (B :: W)) = true) :
    (weakOrders p T).all f = true := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne'
  have hne : (List.finRange (q + 1)).isEmpty = false := by
    rw [List.isEmpty_eq_false_iff, ← List.length_pos_iff_ne_nil]
    simp
  rw [weakOrders, weakOrdersAux, hne]
  simp only [Bool.false_eq_true, ite_false, List.all_eq_true, List.mem_flatMap, List.mem_map]
  rintro W ⟨B, hB, W', hW', rfl⟩
  have hBne : B ≠ [] := addCliques_ne_nil hB
  cases hBeq : B with
  | nil => exact absurd hBeq hBne
  | cons a bs =>
    have ha := h a
    simp only [List.all_eq_true, List.mem_filter, beq_iff_eq] at ha
    simpa [hBeq] using ha B ⟨hB, by simp [hBeq]⟩ W' hW'

/-- Fused `addCliques` + `List.all` (avoids materializing clique lists in kernel `whnf`). -/
def allCliquesF {p : ℕ} (T : List (Fin p × Fin p)) (cur : List (Fin p)) :
    List (Fin p) → (List (Fin p) → Bool) → Bool
  | [], f => if cur.isEmpty then true else f cur.reverse
  | y :: ys, f =>
    allCliquesF T cur ys f &&
      if cur.all (fun x => allowPair T x y) then allCliquesF T (y :: cur) ys f else true

theorem allCliquesF_eq {p : ℕ} (T : List (Fin p × Fin p)) (cur rem : List (Fin p))
    (f : List (Fin p) → Bool) :
    (addCliques T cur rem).all f = allCliquesF T cur rem f := by
  induction rem generalizing cur with
  | nil =>
    simp only [addCliques, allCliquesF]
    cases cur.isEmpty <;> simp
  | cons y ys ih =>
    simp only [addCliques, allCliquesF]
    split_ifs with h
    · rw [List.all_append, ih, ih, Bool.and_comm]
    · simp [ih cur]

/-- Fused `weakOrdersAux` + `List.all` (avoids materializing weak-order lists in kernel `whnf`). -/
def allWeakOrdersF {p : ℕ} (T : List (Fin p × Fin p)) :
    ℕ → List (Fin p) → (List (List (Fin p)) → Bool) → Bool
  | 0, _, f => f []
  | fuel + 1, rem, f =>
    if rem.isEmpty then f []
    else allCliquesF T [] rem fun B =>
      allWeakOrdersF T fuel (rem.filter fun x => !B.contains x) (fun W => f (B :: W))

theorem allWeakOrdersF_eq {p : ℕ} (T : List (Fin p × Fin p)) (fuel : ℕ)
    (rem : List (Fin p)) (f : List (List (Fin p)) → Bool) :
    (weakOrdersAux T fuel rem).all f = allWeakOrdersF T fuel rem f := by
  induction fuel generalizing rem f with
  | zero => simp [weakOrdersAux, allWeakOrdersF]
  | succ fuel ih =>
    simp only [weakOrdersAux, allWeakOrdersF]
    split_ifs with h
    · simp
    · rw [List.all_flatMap, allCliquesF_eq]
      congr 1; funext B
      rw [List.all_map]
      exact ih _ _

/-- Split `(weakOrders p T).all f = true` by `a : Fin p` (first block's head) and
`k : Fin 3` (`k = 0`: `B.length ≥ 2`; `k = 1`: `B = [a]` and second block's head `< p / 2` or empty;
`k = 2`: `B = [a]` and second block's head `≥ p / 2`). -/
theorem weakOrders_split3 {p : ℕ} (hp : 0 < p) (T : List (Fin p × Fin p))
    (f : List (List (Fin p)) → Bool)
    (h0 : ∀ a : Fin p,
      allCliquesF T [] (List.finRange p) (fun B =>
        if B.head? == some a && decide (2 ≤ B.length) then
          allWeakOrdersF T (p - 1) ((List.finRange p).filter fun x => !B.contains x) (fun W => f (B :: W))
        else true) = true)
    (h1 : ∀ a : Fin p,
      allWeakOrdersF T (p - 1) ((List.finRange p).filter fun x => x != a) (fun W =>
        if W.head?.bind List.head? |>.all (fun b => decide (b.val < p / 2)) then f ([a] :: W)
        else true) = true)
    (h2 : ∀ a : Fin p,
      allWeakOrdersF T (p - 1) ((List.finRange p).filter fun x => x != a) (fun W =>
        if W.head?.bind List.head? |>.any (fun b => decide (p / 2 ≤ b.val)) then f ([a] :: W)
        else true) = true) :
    (weakOrders p T).all f = true := by
  refine weakOrders_split hp T f (fun a => ?_)
  have ha0 := h0 a
  have ha1 := h1 a
  have ha2 := h2 a
  rw [← allCliquesF_eq] at ha0
  rw [← allWeakOrdersF_eq] at ha1 ha2
  simp only [List.all_eq_true, List.mem_filter, beq_iff_eq] at ha0 ha1 ha2 ⊢
  intro B ⟨hB, hhead⟩ W hW
  by_cases hlen : 2 ≤ B.length
  · have := ha0 B hB
    simp only [hhead, beq_self_eq_true, decide_true, Bool.and_self, ↓reduceIte,
      ← allWeakOrdersF_eq, List.all_eq_true, hlen] at this
    exact this W hW
  · have hBne : B ≠ [] := addCliques_ne_nil hB
    cases hBeq : B with
    | nil => exact absurd hBeq hBne
    | cons a' bs =>
      have hbs : bs = [] := by
        cases bs with
        | nil => rfl
        | cons _ _ => simp [hBeq] at hlen
      subst hbs
      have ha_eq : a' = a := by simpa [hBeq] using hhead
      subst ha_eq
      have hfilt : (List.finRange p).filter (fun x => !([a'].contains x)) =
          (List.finRange p).filter (fun x => x != a') := by
        congr 1; funext x; by_cases hx : x = a' <;> simp [hx]
      rw [hBeq] at hW
      rw [hfilt] at hW
      cases hWhead : W.head?.bind List.head? with
      | none =>
        have := ha1 W hW
        simpa [hWhead] using this
      | some b =>
        by_cases hb : b.val < p / 2
        · have := ha1 W hW
          simpa [hWhead, hb] using this
        · have := ha2 W hW
          have hb' : p / 2 ≤ b.val := Nat.le_of_not_lt hb
          simpa [hWhead, hb'] using this

private theorem addCliques_sub_nodup {p : ℕ} {T : List (Fin p × Fin p)} {cur rem B : List (Fin p)}
    (hB : B ∈ addCliques T cur rem) (hc : cur.Nodup) (hr : rem.Nodup)
    (hdisj : ∀ x ∈ cur, x ∉ rem) :
    (∀ x ∈ B, x ∈ cur ∨ x ∈ rem) ∧ B.Nodup := by
  induction rem generalizing cur with
  | nil =>
    simp only [addCliques] at hB
    split_ifs at hB
    · simp at hB
    · simp only [List.mem_singleton] at hB
      subst hB
      exact ⟨fun x hx => Or.inl (List.mem_reverse.mp hx), List.nodup_reverse.mpr hc⟩
  | cons y ys ih =>
    simp only [addCliques] at hB
    have hry : y ∉ ys := (List.nodup_cons.mp hr).1
    have hrys : ys.Nodup := (List.nodup_cons.mp hr).2
    have hdisj' : ∀ x ∈ cur, x ∉ ys := fun x hx hxy => hdisj x hx (List.mem_cons_of_mem y hxy)
    split_ifs at hB
    · rcases List.mem_append.mp hB with h1 | h1
      · have hyc : y ∉ cur := fun hy => hdisj y hy List.mem_cons_self
        have hc' : (y :: cur).Nodup := List.nodup_cons.mpr ⟨hyc, hc⟩
        have hdisj'' : ∀ x ∈ y :: cur, x ∉ ys := by
          intro x hx hxy
          rcases List.mem_cons.mp hx with rfl | hx
          · exact hry hxy
          · exact hdisj' x hx hxy
        obtain ⟨hsub, hnd⟩ := ih h1 hc' hrys hdisj''
        refine ⟨fun x hx => ?_, hnd⟩
        rcases hsub x hx with hx | hx
        · rcases List.mem_cons.mp hx with rfl | hx
          · exact Or.inr List.mem_cons_self
          · exact Or.inl hx
        · exact Or.inr (List.mem_cons_of_mem y hx)
      · obtain ⟨hsub, hnd⟩ := ih h1 hc hrys hdisj'
        exact ⟨fun x hx => (hsub x hx).imp_right (List.mem_cons_of_mem y), hnd⟩
    · obtain ⟨hsub, hnd⟩ := ih hB hc hrys hdisj'
      exact ⟨fun x hx => (hsub x hx).imp_right (List.mem_cons_of_mem y), hnd⟩

private theorem weakOrdersAux_perm {p : ℕ} {T : List (Fin p × Fin p)} :
    ∀ {fuel : ℕ} {rem : List (Fin p)} {W : List (List (Fin p))} {L : List (Fin p)},
      W ∈ weakOrdersAux T fuel rem → rem.length ≤ fuel → rem.Nodup → L ∈ linExts W → L.Perm rem
  | 0, rem, W, L, hW, hlen, _, hL => by
    have hrem : rem = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hlen)
    subst hrem
    simp only [weakOrdersAux, List.mem_singleton] at hW
    subst hW
    simp only [linExts, List.mem_singleton] at hL
    subst hL
    exact List.Perm.refl []
  | fuel + 1, rem, W, L, hW, hlen, hnd, hL => by
    simp only [weakOrdersAux] at hW
    split_ifs at hW with hemp
    · have hrem : rem = [] := List.isEmpty_iff.mp hemp
      subst hrem
      simp only [List.mem_singleton] at hW
      subst hW
      simp only [linExts, List.mem_singleton] at hL
      subst hL
      exact List.Perm.refl []
    · simp only [List.mem_flatMap, List.mem_map] at hW
      obtain ⟨B, hB, W', hW', rfl⟩ := hW
      simp only [linExts, List.mem_flatMap, List.mem_map] at hL
      obtain ⟨perm, hperm, L', hL', rfl⟩ := hL
      obtain ⟨hBsub, hBnd⟩ := addCliques_sub_nodup hB List.nodup_nil hnd (fun _ h => by simp at h)
      have hBsub' : ∀ x ∈ B, x ∈ rem := fun x hx => (hBsub x hx).resolve_left (by simp)
      have hBne : B ≠ [] := addCliques_ne_nil hB
      have hlt : (rem.filter fun x => !B.contains x).length < rem.length := by
        obtain ⟨b, hb⟩ := List.exists_mem_of_ne_nil B hBne
        apply List.length_filter_lt_length_iff_exists.mpr
        exact ⟨b, hBsub' b hb, by simp [hb]⟩
      have hL'perm : L'.Perm (rem.filter fun x => !B.contains x) :=
        weakOrdersAux_perm hW' (Nat.le_of_lt_succ (lt_of_lt_of_le hlt hlen)) (hnd.filter _) hL'
      have hperm' : perm.Perm B := List.mem_permutations'.mp hperm
      refine (hperm'.append hL'perm).trans ?_
      refine (List.perm_ext_iff_of_nodup ?_ hnd).mpr ?_
      · refine List.nodup_append.mpr ⟨hBnd, hnd.filter _, fun x hx y hy hxy => ?_⟩
        subst hxy
        simp only [List.mem_filter, Bool.not_eq_true'] at hy
        exact absurd hx (by simpa using hy.2)
      · intro x
        simp only [List.mem_append, List.mem_filter, Bool.not_eq_true']
        constructor
        · rintro (hx | ⟨hx, _⟩)
          · exact hBsub' x hx
          · exact hx
        · intro hx
          by_cases hxB : x ∈ B
          · exact Or.inl hxB
          · exact Or.inr ⟨hx, Bool.eq_false_iff.mpr fun h => hxB (List.contains_iff_mem.mp h)⟩

theorem mem_linExts_of_weakOrders {p : ℕ} {T : List (Fin p × Fin p)}
    {W : List (List (Fin p))} {L : List (Fin p)}
    (hW : W ∈ weakOrders p T) (hL : L ∈ linExts W) :
    L ∈ (List.finRange p).permutations' :=
  List.mem_permutations'.mpr (weakOrdersAux_perm hW (by simp) (List.nodup_finRange p) hL)

private theorem mem_addCliques_nil {p : ℕ} (T : List (Fin p × Fin p))
    (cur : List (Fin p)) (hne : cur ≠ []) (rem : List (Fin p)) :
    cur.reverse ∈ addCliques T cur rem := by
  induction rem generalizing cur with
  | nil => simp [addCliques, List.isEmpty_iff.not.mpr hne]
  | cons r rs ih =>
    simp only [addCliques]
    split_ifs
    · exact List.mem_append.mpr (Or.inr (ih cur hne))
    · exact ih cur hne

private theorem mem_addCliques {p : ℕ} {T : List (Fin p × Fin p)}
    {cur rem B : List (Fin p)} (hsub : B.Sublist rem) (hnd : rem.Nodup) (hne : B ≠ [])
    (hT : ∀ x ∈ B, ∀ y ∈ B, x ≠ y → allowPair T x y = true)
    (hcurT : ∀ x ∈ cur, ∀ y ∈ B, allowPair T x y = true) :
    cur.reverse ++ B ∈ addCliques T cur rem := by
  induction rem generalizing cur B with
  | nil =>
    rw [List.sublist_nil] at hsub
    exact absurd hsub hne
  | cons r rs ih =>
    have hr_not : r ∉ rs := (List.nodup_cons.mp hnd).1
    have hrs_nd : rs.Nodup := (List.nodup_cons.mp hnd).2
    simp only [addCliques]
    cases hsub with
    | cons _ hsub' =>
      have hr_not_B : r ∉ B := fun hm => hr_not (hsub'.subset hm)
      split_ifs
      · exact List.mem_append.mpr (Or.inr (ih hsub' hrs_nd hne hT hcurT))
      · exact ih hsub' hrs_nd hne hT hcurT
    | cons_cons _ hsub' =>
      rename_i bs
      have hc : cur.all (fun x => allowPair T x r) = true :=
        List.all_eq_true.mpr (fun x hx => hcurT x hx r List.mem_cons_self)
      simp only [hc, ↓reduceIte]
      refine List.mem_append.mpr (Or.inl ?_)
      by_cases hbs : bs = []
      · subst hbs
        simpa using mem_addCliques_nil T (r :: cur) (List.cons_ne_nil _ _) rs
      · have hT' : ∀ x ∈ bs, ∀ y ∈ bs, x ≠ y → allowPair T x y = true :=
          fun x hx y hy hxy => hT x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy) hxy
        have hcurT' : ∀ x ∈ r :: cur, ∀ y ∈ bs, allowPair T x y = true := by
          intro x hx y hy
          rcases List.mem_cons.mp hx with rfl | hx'
          · exact hT x List.mem_cons_self y (List.mem_cons_of_mem _ hy)
              (fun e => hr_not (hsub'.subset (e ▸ hy)))
          · exact hcurT x hx' y (List.mem_cons_of_mem _ hy)
        simpa [List.reverse_cons, List.append_assoc] using ih hsub' hrs_nd hbs hT' hcurT'

private theorem mem_weakOrdersAux {p : ℕ} {T : List (Fin p × Fin p)}
    {fuel : ℕ} {rem : List (Fin p)} (hfuel : rem.length ≤ fuel) (hnd : rem.Nodup)
    {W : List (List (Fin p))}
    (hW_ne : ∀ B ∈ W, B ≠ [])
    (hW_T : ∀ B ∈ W, ∀ x ∈ B, ∀ y ∈ B, x ≠ y → allowPair T x y = true)
    (hW_sub : ∀ B ∈ W, B.Sublist (rem.filter (fun x => x ∈ B)))
    (hW_part : ∀ x, x ∈ rem ↔ ∃ B ∈ W, x ∈ B)
    (hW_disj : W.Pairwise (fun B₁ B₂ => ∀ x ∈ B₁, x ∉ B₂)) :
    W ∈ weakOrdersAux T fuel rem := by
  induction fuel generalizing rem W with
  | zero =>
    have hrem : rem = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hfuel)
    subst hrem
    have hWe : W = [] := by
      cases W with
      | nil => rfl
      | cons B Bs =>
        obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil B (hW_ne B (by simp))
        have := (hW_part x).mpr ⟨B, by simp, hx⟩
        simp at this
    subst hWe
    simp [weakOrdersAux]
  | succ fuel ih =>
    simp only [weakOrdersAux]
    by_cases hrem : rem.isEmpty
    · simp only [hrem, ↓reduceIte]
      have hrem0 : rem = [] := List.isEmpty_iff.mp hrem
      subst hrem0
      have hWe : W = [] := by
        cases W with
        | nil => rfl
        | cons B Bs =>
          obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil B (hW_ne B (by simp))
          have := (hW_part x).mpr ⟨B, by simp, hx⟩
          simp at this
      subst hWe
      simp
    · simp only [hrem, ↓reduceIte, Bool.false_eq_true]
      have hrem_ne : rem ≠ [] := List.isEmpty_iff.not.mp hrem
      cases W with
      | nil =>
        obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil rem hrem_ne
        obtain ⟨B, hB, _⟩ := (hW_part x).mp hx
        simp at hB
      | cons B Bs =>
        refine List.mem_flatMap.mpr ⟨B, ?_, ?_⟩
        · have hB_sub : B.Sublist rem := (hW_sub B (by simp)).trans (List.filter_sublist)
          exact mem_addCliques hB_sub hnd (hW_ne B (by simp))
            (hW_T B (by simp)) (fun x hx => by simp at hx)
        · refine List.mem_map.mpr ⟨Bs, ih ?_ (hnd.filter _) ?_ ?_ ?_ ?_ ?_, rfl⟩
          · obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil B (hW_ne B (by simp))
            have hxr : x ∈ rem := ((hW_part x).mpr ⟨B, by simp, hx⟩)
            have hlen : (rem.filter fun y => !B.contains y).length < rem.length := by
              refine List.length_filter_lt_length_iff_exists.mpr ⟨x, hxr, ?_⟩
              simp [hx]
            omega
          · exact fun B' hB' => hW_ne B' (by simp [hB'])
          · exact fun B' hB' => hW_T B' (by simp [hB'])
          · intro B' hB'
            have hdisj := (List.pairwise_cons.mp hW_disj).1 B' hB'
            have hsub' := hW_sub B' (by simp [hB'])
            have heq : rem.filter (fun x => x ∈ B') =
                (rem.filter (fun x => !B.contains x)).filter (fun x => x ∈ B') := by
              rw [List.filter_filter]
              refine List.filter_congr fun x _ => ?_
              by_cases hxB' : x ∈ B'
              · have hxB : x ∉ B := fun h => hdisj x h hxB'
                simp [hxB', hxB]
              · simp [hxB']
            rw [← heq]
            exact hsub'
          · intro x
            simp only [List.mem_filter, Bool.not_eq_true', List.contains_eq_mem,
              decide_eq_false_iff_not]
            constructor
            · rintro ⟨hxr, hxB⟩
              obtain ⟨B', hB', hxB'⟩ := (hW_part x).mp hxr
              rcases List.mem_cons.mp hB' with rfl | hBs
              · exact absurd hxB' hxB
              · exact ⟨B', hBs, hxB'⟩
            · rintro ⟨B', hB', hxB'⟩
              have hdisj := (List.pairwise_cons.mp hW_disj).1 B' hB'
              refine ⟨(hW_part x).mpr ⟨B', by simp [hB'], hxB'⟩, fun hxB => hdisj x hxB hxB'⟩
          · exact (List.pairwise_cons.mp hW_disj).2

private theorem mem_linExts {p : ℕ} {W : List (List (Fin p))} {L : List (Fin p)}
    (hL : ∃ f : (B : List (Fin p)) → B ∈ W → List (Fin p),
      (∀ B hB, f B hB ∈ B.permutations') ∧
      L = (W.attach.map (fun ⟨B, hB⟩ => f B hB)).flatten) :
    L ∈ linExts W := by
  induction W generalizing L with
  | nil =>
    obtain ⟨f, _, rfl⟩ := hL
    simp [linExts]
  | cons B Bs ih =>
    obtain ⟨f, hf, rfl⟩ := hL
    simp only [linExts, List.mem_flatMap, List.mem_map]
    refine ⟨f B (by simp), hf B (by simp), _, ih ⟨fun B' hB' => f B' (by simp [hB']),
      fun B' hB' => hf B' (by simp [hB']), rfl⟩, ?_⟩
    simp [List.attach_cons, Function.comp_def]

/-- **Weak-order soundness**: for any depth function `z : Fin p → ℝ` whose ties are all
contained in `T`, there exists `W ∈ weakOrders p T` such that every injective key `key`
refining `z` has its sorted order `L` in `linExts W`. -/
theorem weakOrders_sound {p : ℕ} (z : Fin p → ℝ) (T : List (Fin p × Fin p))
    (hT : ∀ i j, i ≠ j → z i = z j → (i, j) ∈ T ∨ (j, i) ∈ T) :
    ∃ W ∈ weakOrders p T, ∀ {α : Type*} [LinearOrder α] (key : Fin p → α),
      (∀ i j, z i < z j → key i < key j) → Function.Injective key →
      ∃ L ∈ linExts W, L ∈ (List.finRange p).permutations' ∧
        ∀ i j, rk L i < rk L j → key i < key j := by
  classical
  let vals : List ℝ := ((List.finRange p).map z).dedup.mergeSort (· ≤ ·)
  let mkBlk : ℝ → List (Fin p) := fun v => (List.finRange p).filter (fun i => decide (z i = v))
  let W : List (List (Fin p)) := vals.map mkBlk
  have hvals_nd : vals.Nodup := by
    refine (List.Perm.nodup_iff (List.mergeSort_perm _ _)).mpr ?_
    exact List.nodup_dedup _
  have hvals_sort : vals.Pairwise (· < ·) := by
    have hs := List.pairwise_mergeSort (le := fun a b : ℝ => decide (a ≤ b))
      (fun a b c hab hbc => decide_eq_true (le_trans (of_decide_eq_true hab) (of_decide_eq_true hbc)))
      (fun a b => by simp [le_total]) ((List.finRange p).map z).dedup
    exact List.pairwise_iff_forall_sublist.mpr fun {a b} hab => by
      have hle : a ≤ b := of_decide_eq_true (List.pairwise_iff_forall_sublist.mp hs hab)
      have hne := List.pairwise_iff_forall_sublist.mp hvals_nd hab
      exact lt_of_le_of_ne hle hne
  have hvals_mem : ∀ i : Fin p, z i ∈ vals := fun i => by
    rw [(List.mergeSort_perm _ _).mem_iff, List.mem_dedup]
    exact List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩
  have hW_mem : W ∈ weakOrders p T := by
    refine mem_weakOrdersAux (by simp) (List.nodup_finRange p) ?_ ?_ ?_ ?_ ?_
    · intro B hB
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hB
      have hv' : v ∈ ((List.finRange p).map z).dedup :=
        (List.mergeSort_perm _ _).mem_iff.mp hv
      obtain ⟨i, _, hi⟩ := List.mem_map.mp (List.mem_dedup.mp hv')
      exact List.ne_nil_of_mem (List.mem_filter.mpr ⟨List.mem_finRange i, by simp [hi]⟩)
    · intro B hB x hx y hy hxy
      obtain ⟨v, _, rfl⟩ := List.mem_map.mp hB
      have hzx : z x = v := by simpa [mkBlk] using (List.mem_filter.mp hx).2
      have hzy : z y = v := by simpa [mkBlk] using (List.mem_filter.mp hy).2
      rcases hT x y hxy (hzx.trans hzy.symm) with h | h
      · simp [allowPair, h]
      · simp [allowPair, h]
    · intro B hB
      obtain ⟨v, _, rfl⟩ := List.mem_map.mp hB
      have : (List.finRange p).filter (fun x => x ∈ mkBlk v) = mkBlk v := by
        refine List.filter_congr fun x _ => ?_
        simp [mkBlk]
      rw [this]
    · intro x
      simp only [List.mem_finRange, true_iff]
      exact ⟨mkBlk (z x), List.mem_map.mpr ⟨z x, hvals_mem x, rfl⟩,
        List.mem_filter.mpr ⟨List.mem_finRange x, by simp⟩⟩
    · refine List.pairwise_map.mpr (hvals_sort.imp fun {v₁ v₂} hlt x hx₁ hx₂ => ?_)
      have h1 : z x = v₁ := by simpa [mkBlk] using (List.mem_filter.mp hx₁).2
      have h2 : z x = v₂ := by simpa [mkBlk] using (List.mem_filter.mp hx₂).2
      linarith
  refine ⟨W, hW_mem, fun {α} _ key hmono hinj => ?_⟩
  -- For each block `mkBlk v`, sort it by `key`
  let sortBlk : List (Fin p) → List (Fin p) := fun B =>
    B.mergeSort (fun i j => decide (key i ≤ key j))
  let L : List (Fin p) := (W.map sortBlk).flatten
  have hperm_blk : ∀ B ∈ W, sortBlk B ∈ B.permutations' := fun B _ => by
    rw [List.mem_permutations']
    exact List.mergeSort_perm _ _
  have hL_ext : L ∈ linExts W := by
    refine mem_linExts ⟨fun B _ => sortBlk B, hperm_blk, ?_⟩
    simp [L]
  have hL_perm : L ∈ (List.finRange p).permutations' := by
    rw [List.mem_permutations']
    have h1 : List.Perm L W.flatten := by
      refine List.Perm.flatten_congr ?_
      simp only [List.forall₂_map_left_iff, List.forall₂_same]
      intro B _
      exact List.mergeSort_perm _ _
    have hW_nd : W.flatten.Nodup := by
      refine List.nodup_flatten.mpr ⟨?_, ?_⟩
      · intro B hB
        obtain ⟨v, _, rfl⟩ := List.mem_map.mp hB
        exact (List.nodup_finRange p).filter _
      · refine List.pairwise_map.mpr (hvals_sort.imp fun {v₁ v₂} hlt x hx₁ hx₂ => ?_)
        have h1 : z x = v₁ := by simpa [mkBlk] using (List.mem_filter.mp hx₁).2
        have h2 : z x = v₂ := by simpa [mkBlk] using (List.mem_filter.mp hx₂).2
        linarith
    have hW_perm : List.Perm W.flatten (List.finRange p) := by
      refine (List.perm_ext_iff_of_nodup hW_nd (List.nodup_finRange p)).mpr fun x => ?_
      simp only [List.mem_flatten, List.mem_finRange, iff_true]
      exact ⟨mkBlk (z x), List.mem_map.mpr ⟨z x, hvals_mem x, rfl⟩,
        List.mem_filter.mpr ⟨List.mem_finRange x, by simp⟩⟩
    exact h1.trans hW_perm
  have hL_nd : L.Nodup :=
    ((List.mem_permutations'.mp hL_perm).nodup_iff).mpr (List.nodup_finRange p)
  have hL_sorted : L.Pairwise (fun i j => key i < key j) := by
    have hsort_pw : ∀ B ∈ W, (sortBlk B).Pairwise (fun i j => key i < key j) := by
      intro B hB
      have hB_nd : B.Nodup := by
        obtain ⟨v, _, rfl⟩ := List.mem_map.mp hB
        exact (List.nodup_finRange p).filter _
      have hs_nd : (sortBlk B).Nodup :=
        ((List.mergeSort_perm _ _).nodup_iff).mpr hB_nd
      have hs := List.pairwise_mergeSort (le := fun i j => decide (key i ≤ key j))
        (fun a b c hab hbc => decide_eq_true (le_trans (of_decide_eq_true hab) (of_decide_eq_true hbc)))
        (fun a b => by simp [le_total]) B
      exact List.pairwise_iff_forall_sublist.mpr fun {a b} hab => by
        have hle : key a ≤ key b := of_decide_eq_true (List.pairwise_iff_forall_sublist.mp hs hab)
        have hne : a ≠ b := List.pairwise_iff_forall_sublist.mp hs_nd hab
        exact lt_of_le_of_ne hle (fun e => hne (hinj e))
    rw [List.pairwise_flatten]
    refine ⟨fun B' hB' => ?_, ?_⟩
    · obtain ⟨B, hB, rfl⟩ := List.mem_map.mp hB'
      exact hsort_pw B hB
    · have hpw : W.Pairwise (fun B₁ B₂ => ∀ i ∈ B₁, ∀ j ∈ B₂, key i < key j) := by
        refine List.pairwise_map.mpr (hvals_sort.imp fun {v₁ v₂} hlt i hi₁ j hj₂ => ?_)
        have h1 : z i = v₁ := by simpa [mkBlk] using (List.mem_filter.mp hi₁).2
        have h2 : z j = v₂ := by simpa [mkBlk] using (List.mem_filter.mp hj₂).2
        exact hmono i j (h1 ▸ h2 ▸ hlt)
      refine List.pairwise_map.mpr (hpw.imp fun {B₁ B₂} h i hi j hj => ?_)
      exact h i ((List.mergeSort_perm _ _).mem_iff.mp hi) j
        ((List.mergeSort_perm _ _).mem_iff.mp hj)
  refine ⟨L, hL_ext, hL_perm, fun i j hrk => ?_⟩
  have hi : i ∈ L := (List.mem_permutations'.mp hL_perm).mem_iff.mpr (List.mem_finRange i)
  have hj : j ∈ L := (List.mem_permutations'.mp hL_perm).mem_iff.mpr (List.mem_finRange j)
  have hlt := (List.pairwise_iff_getElem.mp hL_sorted) (L.idxOf i) (L.idxOf j)
    (List.idxOf_lt_length_of_mem hi) (List.idxOf_lt_length_of_mem hj) hrk
  simpa [List.getElem_idxOf] using hlt

/-! ### Multi-rim tie-tolerant SVC check and theorem -/

/-- Order exclusion for `SVC` (forced pairs and signed dependencies). -/
def exclOK_svc {p : ℕ} (forced : List (Fin p × Fin p)) (deps : List (Fin p → SignType))
    (L : List (Fin p)) : Bool :=
  forced.any (fun ij => Nat.blt (rk L ij.1) (rk L ij.2)) ||
    deps.any (fun s => sepR s L || sepR (fun i => -s i) L)

/-- Whether a weak order `W` is closed by exclusions or a single rim across all its linear extensions. -/
def rimClosedW {m p : ℕ} (R : List (Rim m p)) (excl : List (Fin p) → Bool)
    (exts : List (List (Fin p))) : Bool :=
  exts.all excl || R.any fun ρ => exts.all fun L => excl L || rimOK ρ L

def fact : ℕ → ℕ
  | 0 => 1
  | n + 1 => (n + 1) * fact n

def lehmerAux {p : ℕ} : List (Fin p) → ℕ
  | [] => 0
  | x :: xs =>
    let cnt := xs.foldl (fun acc y => if y < x then acc + 1 else acc) 0
    cnt * fact xs.length + lehmerAux xs

def buildMasks {m p : ℕ} (forced : List (Fin p × Fin p)) (deps : List (Fin p → SignType))
    (R : List (Rim m p)) : ℕ × List ℕ :=
  (List.finRange p).permutations'.foldl (fun (exM, rMs) L =>
    let idx := lehmerAux L
    let bit := 1 <<< idx
    if exclOK_svc forced deps L then (exM ||| bit, rMs)
    else
      let rMs' := List.zipWith (fun ρ msk => if rimOK ρ L then msk ||| bit else msk) R rMs
      (exM, rMs')) (0, R.map fun _ => 0)

def allWeakOrdersAux {p : ℕ} (T : List (Fin p × Fin p)) (f : List (List (Fin p)) → Bool) :
    ℕ → List (Fin p) → List (List (Fin p)) → Bool
  | 0, _, acc => f acc.reverse
  | fuel + 1, rem, acc =>
    if rem.isEmpty then f acc.reverse
    else (addCliques T [] rem).all fun B =>
      allWeakOrdersAux T f fuel (rem.filter fun x => !B.contains x) (B :: acc)

def checkW_aux {p : ℕ} (T : List (Fin p × Fin p)) (exM : ℕ) (rMs : List ℕ) : Bool :=
  allWeakOrdersAux T (fun W =>
    let wMask := (linExts W).foldl (fun acc L => acc ||| (1 <<< lehmerAux L)) 0
    (wMask &&& exM) == wMask || rMs.any fun rM => (wMask &&& (exM ||| rM)) == wMask)
    p (List.finRange p) []

def checkBijection (p : ℕ) : Bool :=
  let idxs := (List.finRange p).permutations'.map lehmerAux
  let m := idxs.foldl (fun acc k => acc ||| (1 <<< k)) 0
  m == (1 <<< fact p) - 1 && idxs.length == fact p

/-- Tie-tolerant `SVC.check` over weak orders whose tie pairs are in `T` (bitmask-accelerated). -/
def checkW {m n p : ℕ} (S : Fin m → Finset (Fin n)) (P : Fin p → Fin n) (sw : Fin m → SignType)
    (forced : List (Fin p × Fin p)) (deps : List (Fin p → SignType)) (R : List (Rim m p))
    (T : List (Fin p × Fin p)) : Bool :=
  R.all (rimValid S P sw) && checkBijection p &&
    let pM := buildMasks forced deps R
    checkW_aux T pM.1 pM.2

private theorem testBit_foldl_or {α : Type*} (f : α → ℕ) (init : ℕ) (l : List α)
    {x : α} (hx : x ∈ l) :
    Nat.testBit (l.foldl (fun acc a => acc ||| (1 <<< f a)) init) (f x) = true := by
  have hmono : ∀ (l' : List α) (i : ℕ) (k : ℕ), Nat.testBit i k = true →
      Nat.testBit (l'.foldl (fun acc a => acc ||| (1 <<< f a)) i) k = true := by
    intro l'
    induction l' with
    | nil => intro i k hk; exact hk
    | cons y ys ih =>
      intro i k hk
      apply ih
      simp [Nat.testBit_or, hk]
  induction l generalizing init with
  | nil => simp at hx
  | cons y ys ih =>
    rcases List.mem_cons.mp hx with rfl | hx'
    · rw [List.foldl_cons]
      apply hmono
      simp [Nat.testBit_or, Nat.testBit_shiftLeft]
    · exact ih _ hx'

private theorem testBit_and_eq {a b k : ℕ} (ha : Nat.testBit a k = true)
    (heq : (a &&& b) == a) : Nat.testBit b k = true := by
  have h := congrArg (fun n => Nat.testBit n k) (beq_iff_eq.mp heq)
  simp only [Nat.testBit_and, ha, Bool.true_and] at h
  exact h

private theorem allWeakOrdersAux_sound {p : ℕ} {T : List (Fin p × Fin p)}
    {f : List (List (Fin p)) → Bool} {fuel : ℕ} {rem : List (Fin p)} {acc : List (List (Fin p))}
    (h : allWeakOrdersAux T f fuel rem acc = true) :
    ∀ W ∈ weakOrdersAux T fuel rem, f (acc.reverse ++ W) = true := by
  induction fuel generalizing rem acc with
  | zero =>
    intro W hW
    simp only [weakOrdersAux, List.mem_singleton] at hW
    subst hW
    simpa [allWeakOrdersAux] using h
  | succ fuel ih =>
    intro W hW
    simp only [allWeakOrdersAux] at h
    simp only [weakOrdersAux] at hW
    by_cases hrem : rem.isEmpty
    · simp only [hrem, ↓reduceIte, List.mem_singleton] at h hW
      subst hW
      simpa using h
    · simp only [hrem, ↓reduceIte, Bool.false_eq_true, List.all_eq_true,
        List.mem_flatMap, List.mem_map] at h hW
      obtain ⟨B, hB, W', hW', rfl⟩ := hW
      have := ih (h B hB) W' hW'
      simpa [List.reverse_cons, List.append_assoc] using this

private theorem buildMasks_fold_inv {m p : ℕ} (forced : List (Fin p × Fin p))
    (deps : List (Fin p → SignType)) (R : List (Rim m p))
    (hinj : ∀ L₁ ∈ (List.finRange p).permutations', ∀ L₂ ∈ (List.finRange p).permutations',
      lehmerAux L₁ = lehmerAux L₂ → L₁ = L₂)
    (L : List (Fin p)) (hL : L ∈ (List.finRange p).permutations')
    (l : List (List (Fin p))) (hl : ∀ L' ∈ l, L' ∈ (List.finRange p).permutations')
    (ex₀ : ℕ) (r₀ : List ℕ) (hr₀ : r₀.length = R.length)
    (hex₀ : Nat.testBit ex₀ (lehmerAux L) = true → exclOK_svc forced deps L = true)
    (hr₀_ok : ∀ (ri : ℕ) (hri : ri < R.length), Nat.testBit (r₀.getD ri 0) (lehmerAux L) = true →
      rimOK (R[ri]) L = true) :
    let res := l.foldl (fun (exM, rMs) L' =>
      let idx := lehmerAux L'
      let bit := 1 <<< idx
      if exclOK_svc forced deps L' then (exM ||| bit, rMs)
      else
        let rMs' := List.zipWith (fun ρ msk => if rimOK ρ L' then msk ||| bit else msk) R rMs
        (exM, rMs')) (ex₀, r₀)
    res.2.length = R.length ∧
      (Nat.testBit res.1 (lehmerAux L) = true → exclOK_svc forced deps L = true) ∧
      (∀ ri (hri : ri < R.length), Nat.testBit (res.2.getD ri 0) (lehmerAux L) = true →
        rimOK (R[ri]) L = true) := by
  induction l generalizing ex₀ r₀ with
  | nil => exact ⟨hr₀, hex₀, hr₀_ok⟩
  | cons L' ls ih =>
    have hL' : L' ∈ (List.finRange p).permutations' := hl L' List.mem_cons_self
    have hls : ∀ x ∈ ls, x ∈ (List.finRange p).permutations' :=
      fun x hx => hl x (List.mem_cons_of_mem _ hx)
    simp only [List.foldl_cons]
    by_cases he : exclOK_svc forced deps L' = true
    · simp only [he, ↓reduceIte]
      refine ih hls (ex₀ ||| (1 <<< lehmerAux L')) r₀ hr₀ (fun h => ?_) hr₀_ok
      simp only [Nat.testBit_or, Bool.or_eq_true] at h
      rcases h with h | h
      · exact hex₀ h
      · have heq : lehmerAux L' = lehmerAux L := by
          by_contra hne
          simp only [Nat.testBit_shiftLeft, Nat.testBit_one_eq_true_iff_self_eq_zero,
            Bool.and_eq_true, decide_eq_true_eq] at h
          exact hne (by omega)
        rw [← hinj L' hL' L hL heq]
        exact he
    · simp only [he, Bool.false_eq_true, ↓reduceIte]
      have hlen' : (List.zipWith (fun ρ msk => if rimOK ρ L' then msk ||| (1 <<< lehmerAux L') else msk) R r₀).length = R.length := by
        simp [hr₀]
      refine ih hls ex₀ _ hlen' hex₀ (fun ri hri h => ?_)
      have hri0 : ri < r₀.length := hr₀ ▸ hri
      have hget : (List.zipWith (fun ρ msk => if rimOK ρ L' then msk ||| (1 <<< lehmerAux L') else msk) R r₀).getD ri 0 =
          if rimOK (R[ri]) L' then r₀.getD ri 0 ||| (1 <<< lehmerAux L') else r₀.getD ri 0 := by
        simp only [List.getD_eq_getElem?_getD, List.getElem?_zipWith,
          List.getElem?_eq_getElem hri, List.getElem?_eq_getElem hri0]
        rfl
      rw [hget] at h
      split_ifs at h with hr_ok
      · simp only [Nat.testBit_or, Bool.or_eq_true] at h
        rcases h with h | h
        · exact hr₀_ok ri hri h
        · have heq : lehmerAux L' = lehmerAux L := by
            by_contra hne
            simp only [Nat.testBit_shiftLeft, Nat.testBit_one_eq_true_iff_self_eq_zero,
              Bool.and_eq_true, decide_eq_true_eq] at h
            exact hne (by omega)
          rw [← hinj L' hL' L hL heq]
          exact hr_ok
      · exact hr₀_ok ri hri h

private theorem buildMasks_sound {m p : ℕ} {forced : List (Fin p × Fin p)}
    {deps : List (Fin p → SignType)} {R : List (Rim m p)}
    (hinj : ∀ L₁ ∈ (List.finRange p).permutations', ∀ L₂ ∈ (List.finRange p).permutations',
      lehmerAux L₁ = lehmerAux L₂ → L₁ = L₂)
    {L : List (Fin p)} (hL : L ∈ (List.finRange p).permutations') :
    (buildMasks forced deps R).2.length = R.length ∧
      (Nat.testBit (buildMasks forced deps R).1 (lehmerAux L) = true →
        exclOK_svc forced deps L = true) ∧
      (∀ ri (hri : ri < R.length),
        Nat.testBit ((buildMasks forced deps R).2.getD ri 0) (lehmerAux L) = true →
          rimOK (R[ri]) L = true) :=
  buildMasks_fold_inv forced deps R hinj L hL (List.finRange p).permutations'
    (fun _ h => h) 0 (R.map fun _ => 0) (by simp)
    (fun h => by simp at h) (fun ri hri h => by
      have : (R.map (fun _ => (0 : ℕ))).getD ri 0 = 0 := by
        simp [List.getD_eq_getElem?_getD, hri]
      rw [this] at h
      simp at h)

theorem exclOK_svc_lex_false {n p : ℕ} {x : Fin n → ℝ³} {P : Fin p → Fin n} {w d1 d2 : ℝ³}
    {forced : List (Fin p × Fin p)} (hforced : ∀ ij ∈ forced, ⟪x (P ij.2), w⟫ < ⟪x (P ij.1), w⟫)
    {deps : List (Fin p → SignType)}
    (hdeps : ∀ s ∈ deps, ∃ mu : Fin p → ℝ, ∑ i, mu i = 0 ∧ ∑ i, mu i • x (P i) = 0 ∧
      ∀ i, SignType.sign (mu i) = s i)
    {L : List (Fin p)}
    (hrk : ∀ i j, rk L i < rk L j → lexKey (x (P i)) w d1 d2 < lexKey (x (P j)) w d1 d2)
    (h : exclOK_svc forced deps L = true) : False := by
  simp only [exclOK_svc, Bool.or_eq_true, List.any_eq_true] at h
  rcases h with ⟨ij, hij, hlt⟩ | ⟨s, hs, hsep⟩
  · rw [Nat.blt_eq] at hlt
    exact absurd (hrk _ _ hlt) (lt_asymm (lexKey_lt_of_lt (hforced ij hij)))
  · obtain ⟨mu, hsum, hdep, hsg⟩ := hdeps s hs
    rcases hsep with h | h
    · exact sepR_lex_sound hrk hsg hsum hdep h
    · refine sepR_lex_sound hrk (mu := fun i => -mu i) (fun i => ?_) ?_ ?_ h
      · rw [Left.sign_neg, hsg]
      · rw [Finset.sum_neg_distrib, hsum, neg_zero]
      · simp only [neg_smul, Finset.sum_neg_distrib, hdep, neg_zero]

theorem lexAny_of_rimOK_lex {m n p : ℕ} {S : Fin m → Finset (Fin n)} {x : Fin n → ℝ³}
    (F : S0xFac m S x) (P : Fin p → Fin n) (w d1 d2 : ℝ³) (sw : Fin m → SignType) (ρ : Rim m p)
    (hsw : ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn → SignType.sign ⟪F.N t, w⟫ = sw t)
    (hd1 : ∀ t, sw t = 0 → SignType.sign ⟪F.N t, d1⟫ = ρ.sd t)
    (hv : rimValid S P sw ρ = true) {L : List (Fin p)}
    (hrk : ∀ i j, rk L i < rk L j → lexKey (x (P i)) w d1 d2 < lexKey (x (P j)) w d1 d2)
    (hok : rimOK ρ L = true) : Minimality.Gen.LexAny F := by
  simp only [rimValid, Bool.and_eq_true, decide_eq_true_eq] at hv
  obtain ⟨⟨⟨⟨hk, hinj⟩, hcyc⟩, hU⟩, hD⟩ := hv
  refine Minimality.GenQuad.lexAny_of_clauses F hk hinj hcyc w d1 d2 ?_ ?_ ?_
  · intro t ht
    have hs := hsw t (Or.inl ht)
    rcases hU t ht with h | ⟨h0, h1⟩
    · exact Or.inl (sign_eq_one_iff.mp (hs.trans h))
    · refine Or.inr ⟨sign_eq_zero_iff.mp (hs.trans h0), Or.inl ?_⟩
      exact sign_eq_one_iff.mp ((hd1 t h0).trans h1)
  · intro t ht
    have hs := hsw t (Or.inr ht)
    rcases hD t ht with h | ⟨h0, h1⟩
    · exact Or.inl (neg_pos.mpr (sign_eq_neg_one_iff.mp (hs.trans h)))
    · refine Or.inr ⟨neg_eq_zero.mpr (sign_eq_zero_iff.mp (hs.trans h0)), Or.inl ?_⟩
      exact neg_pos.mpr (sign_eq_neg_one_iff.mp ((hd1 t h0).trans h1))
  · exact rimOK_lex_sound hrk (y := fun i => x (P i)) ρ hok

/-- **Multi-rim single-view closure, tie-tolerant.** Replaces `hgen` of `svc_local` with
per-rim `(d1, d2)` (`Split.det3 w d1 d2 ≠ 0`), injectivity of `x ∘ P`, and allowed tie pairs `T`. -/
private theorem testBit_foldl_or_mem {l : List ℕ} {init k : ℕ}
    (hinit : Nat.testBit init k = false) (hk : k ∉ l) :
    Nat.testBit (l.foldl (fun acc a => acc ||| (1 <<< a)) init) k = false := by
  induction l generalizing init with
  | nil => exact hinit
  | cons a as ih =>
    simp only [List.foldl_cons]
    apply ih
    · have hne : a ≠ k := fun h => hk (h ▸ List.mem_cons_self)
      simp only [Nat.testBit_or, hinit, Nat.testBit_shiftLeft, Bool.false_or,
        Bool.and_eq_false_iff, decide_eq_false_iff_not]
      by_cases hle : a ≤ k
      · right
        have hpos : 1 ≤ k - a := by omega
        exact Nat.testBit_eq_false_of_lt
          (lt_of_lt_of_le (by decide : 1 < 2 ^ 1) (Nat.pow_le_pow_right (by decide) hpos))
      · exact Or.inl hle
    · exact fun h => hk (List.mem_cons_of_mem _ h)

private theorem nodup_of_checkBijection {p : ℕ} (h : checkBijection p = true) :
    ((List.finRange p).permutations'.map lehmerAux).Nodup := by
  classical
  simp only [checkBijection, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨hm, hlen⟩ := h
  set idxs := (List.finRange p).permutations'.map lehmerAux
  have hmem : ∀ k ∈ List.range (fact p), k ∈ idxs := by
    intro k hk
    rw [List.mem_range] at hk
    by_contra hnot
    have hf := testBit_foldl_or_mem (init := 0) (k := k) (by simp) hnot
    rw [hm] at hf
    have ht : Nat.testBit ((1 <<< fact p) - 1) k = true := by
      rw [Nat.shiftLeft_eq, one_mul, Nat.testBit_two_pow_sub_one]
      exact decide_eq_true hk
    rw [ht] at hf
    cases hf
  have hsub : (List.range (fact p)).toFinset ⊆ idxs.toFinset :=
    fun k hk => List.mem_toFinset.mpr (hmem k (List.mem_toFinset.mp hk))
  have hcard : fact p ≤ idxs.toFinset.card := by
    have hr : (List.range (fact p)).toFinset.card = fact p := by
      rw [List.toFinset_card_of_nodup List.nodup_range, List.length_range]
    rw [← hr]
    exact Finset.card_le_card hsub
  have hle := List.toFinset_card_le idxs
  have heq : idxs.dedup.length = idxs.length := by
    rw [← List.card_toFinset]
    omega
  rw [← (List.dedup_sublist idxs).eq_of_length heq]
  exact List.nodup_dedup idxs

theorem svc_local_lex {m n p : ℕ} {S : Fin m → Finset (Fin n)} {x : Fin n → ℝ³}
    (F : S0xFac m S x) (P : Fin p → Fin n) (w : ℝ³) (sw : Fin m → SignType)
    (R : List (Rim m p)) (hne : R ≠ [])
    (hsw : ∀ ρ ∈ R, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn → SignType.sign ⟪F.N t, w⟫ = sw t)
    (hR : ∀ ρ ∈ R, ∃ d1 d2 : ℝ³,
      (∀ t, sw t = 0 → SignType.sign ⟪F.N t, d1⟫ = ρ.sd t) ∧ Split.det3 w d1 d2 ≠ 0)
    (forced : List (Fin p × Fin p))
    (hforced : ∀ ij ∈ forced, ⟪x (P ij.2), w⟫ < ⟪x (P ij.1), w⟫)
    (deps : List (Fin p → SignType))
    (hdeps : ∀ s ∈ deps, ∃ mu : Fin p → ℝ, ∑ i, mu i = 0 ∧ ∑ i, mu i • x (P i) = 0 ∧
      ∀ i, SignType.sign (mu i) = s i)
    (hP : Function.Injective (fun i => x (P i)))
    (T : List (Fin p × Fin p))
    (hT : ∀ i j, i ≠ j → ⟪x (P i), w⟫ = ⟪x (P j), w⟫ → (i, j) ∈ T ∨ (j, i) ∈ T)
    (hcheck : checkW S P sw forced deps R T = true) : Minimality.Gen.LexAny F := by
  classical
  obtain ⟨W, hW, hW_ext⟩ := weakOrders_sound (fun i => ⟪x (P i), w⟫) T hT
  simp only [checkW, Bool.and_eq_true, List.all_eq_true] at hcheck
  obtain ⟨⟨hval, hbij⟩, hclosed⟩ := hcheck
  have hnd : ((List.finRange p).permutations'.map lehmerAux).Nodup :=
    nodup_of_checkBijection hbij
  have hinj : ∀ L₁ ∈ (List.finRange p).permutations', ∀ L₂ ∈ (List.finRange p).permutations',
      lehmerAux L₁ = lehmerAux L₂ → L₁ = L₂ := by
    intro L₁ h1 L₂ h2 heq
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp h1
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp h2
    have hij : i = j := by
      have hfin : (⟨i, by simpa using hi⟩ : Fin ((List.finRange p).permutations'.map lehmerAux).length) =
          ⟨j, by simpa using hj⟩ :=
        List.nodup_iff_injective_getElem.mp hnd (by simpa using heq)
      exact congrArg Fin.val hfin
    subst hij
    rfl
  have hWc := allWeakOrdersAux_sound hclosed W hW
  simp only [List.reverse_nil, List.nil_append, Bool.or_eq_true, List.any_eq_true] at hWc
  rcases hWc with hexcl | ⟨rM, hrM, hrim⟩
  · obtain ⟨ρ0, hρ0⟩ := List.exists_mem_of_ne_nil R hne
    obtain ⟨d1, d2, _, hdet⟩ := hR ρ0 hρ0
    obtain ⟨L, hL, hLp, hrk⟩ := hW_ext (fun i => lexKey (x (P i)) w d1 d2)
      (fun _ _ h => lexKey_lt_of_lt h)
      (fun i j h => by by_contra hne'; exact lexKey_ne hdet (fun e => hne' (hP e)) h)
    have hbit := testBit_and_eq (testBit_foldl_or lehmerAux 0 (linExts W) hL) hexcl
    have hex := (buildMasks_sound hinj hLp).2.1 hbit
    exact (exclOK_svc_lex_false hforced hdeps hrk hex).elim
  · have hL0 : List.finRange p ∈ (List.finRange p).permutations' :=
      List.mem_permutations'.mpr (List.Perm.refl _)
    have hlen := (buildMasks_sound (forced := forced) (deps := deps) (R := R) hinj hL0).1
    have ⟨ri, hri_len, hri_eq⟩ : ∃ ri, ∃ hri : ri < (buildMasks forced deps R).2.length,
        (buildMasks forced deps R).2[ri] = rM := List.mem_iff_getElem.mp hrM
    have hri : ri < R.length := hlen ▸ hri_len
    let ρ := R[ri]
    have hρ : ρ ∈ R := List.getElem_mem hri
    obtain ⟨d1, d2, hd1, hdet⟩ := hR ρ hρ
    obtain ⟨L, hL, hLp, hrk⟩ := hW_ext (fun i => lexKey (x (P i)) w d1 d2)
      (fun _ _ h => lexKey_lt_of_lt h)
      (fun i j h => by by_contra hne'; exact lexKey_ne hdet (fun e => hne' (hP e)) h)
    have hbit := testBit_and_eq (testBit_foldl_or lehmerAux 0 (linExts W) hL) hrim
    rw [Nat.testBit_or, Bool.or_eq_true] at hbit
    rcases hbit with hex_bit | hrim_bit
    · exact (exclOK_svc_lex_false hforced hdeps hrk
        ((buildMasks_sound hinj hLp).2.1 hex_bit)).elim
    · have hrM_get : (buildMasks forced deps R).2.getD ri 0 = rM := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hri_len, hri_eq]
      rw [← hrM_get] at hrim_bit
      have hok := (buildMasks_sound hinj hLp).2.2 ri hri hrim_bit
      exact lexAny_of_rimOK_lex F P w d1 d2 sw ρ (hsw ρ hρ) hd1 (hval ρ hρ) hrk hok

/-- If `w ≠ 0` and `n` is orthogonal to `w` but not to `d`, then `w` and `d` are linearly
independent, so there exists `d2` with `Split.det3 w d d2 ≠ 0`. -/
theorem exists_det3_ne_zero_of_orth {w d n : ℝ³} (hw : w ≠ 0) (hnw : ⟪n, w⟫ = 0)
    (hnd : ⟪n, d⟫ ≠ 0) : ∃ d2 : ℝ³, Split.det3 w d d2 ≠ 0 := by
  let d2 : ℝ³ := EuclideanSpace.single 0 (w 1 * d 2 - w 2 * d 1) +
    EuclideanSpace.single 1 (w 2 * d 0 - w 0 * d 2) +
    EuclideanSpace.single 2 (w 0 * d 1 - w 1 * d 0)
  refine ⟨d2, fun hdet => ?_⟩
  have heq : Split.det3 w d d2 =
      (w 1 * d 2 - w 2 * d 1) ^ 2 + (w 2 * d 0 - w 0 * d 2) ^ 2 +
      (w 0 * d 1 - w 1 * d 0) ^ 2 := by
    dsimp only [Split.det3, d2]
    simp only [PiLp.add_apply, PiLp.single_apply]
    norm_num; ring
  have hsq : (w 1 * d 2 - w 2 * d 1) ^ 2 + (w 2 * d 0 - w 0 * d 2) ^ 2 +
      (w 0 * d 1 - w 1 * d 0) ^ 2 = 0 := by linarith
  have hc0 : w 1 * d 2 = w 2 * d 1 := by
    have : (w 1 * d 2 - w 2 * d 1) ^ 2 = 0 := by nlinarith
    linarith [sq_eq_zero_iff.mp this]
  have hc1 : w 2 * d 0 = w 0 * d 2 := by
    have : (w 2 * d 0 - w 0 * d 2) ^ 2 = 0 := by nlinarith
    linarith [sq_eq_zero_iff.mp this]
  have hc2 : w 0 * d 1 = w 1 * d 0 := by
    have : (w 0 * d 1 - w 1 * d 0) ^ 2 = 0 := by nlinarith
    linarith [sq_eq_zero_iff.mp this]
  have hcomp : w 0 ≠ 0 ∨ w 1 ≠ 0 ∨ w 2 ≠ 0 := by
    by_contra h; push Not at h; apply hw; ext i; fin_cases i <;> simp [h]
  rcases hcomp with h0 | h1 | h2
  · have hlin : w 0 • d = d 0 • w := by
      ext i; fin_cases i <;> simp [PiLp.smul_apply] <;> linarith
    have := congrArg (fun v => ⟪n, v⟫) hlin
    simp only [real_inner_smul_right, hnw, mul_zero] at this
    exact hnd ((mul_eq_zero.mp this).resolve_left h0)
  · have hlin : w 1 • d = d 1 • w := by
      ext i; fin_cases i <;> simp [PiLp.smul_apply] <;> linarith
    have := congrArg (fun v => ⟪n, v⟫) hlin
    simp only [real_inner_smul_right, hnw, mul_zero] at this
    exact hnd ((mul_eq_zero.mp this).resolve_left h1)
  · have hlin : w 2 • d = d 2 • w := by
      ext i; fin_cases i <;> simp [PiLp.smul_apply] <;> linarith
    have := congrArg (fun v => ⟪n, v⟫) hlin
    simp only [real_inner_smul_right, hnw, mul_zero] at this
    exact hnd ((mul_eq_zero.mp this).resolve_left h2)

end Minimality.SVC
