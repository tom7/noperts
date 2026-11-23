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

end Minimality.SVC
