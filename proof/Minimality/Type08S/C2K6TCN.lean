module

public import Minimality.Type08S.C2K6TCL

@[expose] public section

set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
open scoped RealInnerProductSpace Topology
open Finset Filter
namespace Minimality
namespace Type08Sp
namespace C2

set_option maxHeartbeats 3200000 in
/-- `k5d_cell` with an additional lex-tie premise for `hreal`. -/
theorem k6t3_cell (V : Finset ℝ³) (p q r d : ℝ³) (hΔ : det3 p q r ≠ 0) {k : ℕ} [NeZero k] (hk : 3 ≤ k)
    (X : ZMod k → ℝ × ℝ × ℝ) (hX : ∀ i j, X i = X j → i = j) (hmem : ∀ i, fpoint p q r d (X i) ∈ V)
    (O : List (ℝ × ℝ × ℝ))
    (hVall : ∀ y ∈ V, (∃ i, y = fpoint p q r d (X i)) ∨ ∃ t ∈ O, y = fpoint p q r d t)
    {u1 u2 t1 t2 lo hi : ℝ} (hut : u1 * t2 - u2 * t1 ≠ 0) (hlh : lo < hi)
    (C : ℝ → ℝ → Prop) (hC : ∀ lam, lo < lam → lam < hi → C (u1 + lam * t1) (u2 + lam * t2))
    (hT : ∀ v1 v2, C v1 v2 →
      (∀ i j, j ≠ i → j ≠ i + 1 → TSc 1 (X (i + 1) - X i) (X j - X i) (v1, v2, 0)) ∧
      (∀ t ∈ O, ∀ i, TSc 1 (X (i + 1) - X i) (t - X i) (v1, v2, 0)))
    (L : List (ℝ × ℝ × ℝ)) (hXL : ∀ i, X i ∈ L)
    (hreal : ∀ v1 v2, C v1 v2 → ∀ k0 U T B : ℝ,
      (∀ s ∈ L, ∀ t ∈ L, s.1 * ⟪p, r⟫ + s.2.1 * ⟪q, r⟫ + s.2.2 * ⟪r, r⟫ < t.1 * ⟪p, r⟫ + t.2.1 * ⟪q, r⟫ + t.2.2 * ⟪r, r⟫ →
        k0 + s.1 * U + s.2.1 * T + s.2.2 * B < k0 + t.1 * U + t.2.1 * T + t.2.2 * B) →
      (∀ s ∈ L, ∀ t ∈ L, s.1 * ⟪p, r⟫ + s.2.1 * ⟪q, r⟫ + s.2.2 * ⟪r, r⟫ = t.1 * ⟪p, r⟫ + t.2.1 * ⟪q, r⟫ + t.2.2 * ⟪r, r⟫ →
        (s.1 * ⟪p, fcomb p q r v1 v2 0⟫ + s.2.1 * ⟪q, fcomb p q r v1 v2 0⟫ + s.2.2 * ⟪r, fcomb p q r v1 v2 0⟫ <
         t.1 * ⟪p, fcomb p q r v1 v2 0⟫ + t.2.1 * ⟪q, fcomb p q r v1 v2 0⟫ + t.2.2 * ⟪r, fcomb p q r v1 v2 0⟫) →
        k0 + s.1 * U + s.2.1 * T + s.2.2 * B < k0 + t.1 * U + t.2.1 * T + t.2.2 * B) →
      (∀ i j, k0 + (X i).1 * U + (X i).2.1 * T + (X i).2.2 * B = k0 + (X j).1 * U + (X j).2.1 * T + (X j).2.2 * B → i = j) →
      LexUni (fun _ => (0 : ℝ)) (fun i => k0 + (X i).1 * U + (X i).2.1 * T + (X i).2.2 * B)) :
    HasLexCellAt V r := by
  obtain ⟨lam, hl0, hl1, hL⟩ := exists_sep_tilt p q r d hΔ X hX hut hlh
  set v1 := u1 + lam * t1
  set v2 := u2 + lam * t2
  have hCv := hC lam hl0 hl1
  obtain ⟨hcy, hre⟩ := hT v1 v2 hCv
  have hlex' : LexUni (fun i => ⟪fpoint p q r d (X i), r⟫)
      (fun i => ⟪fpoint p q r d (X i), fcomb p q r v1 v2 0⟫) := by
    set v := fcomb p q r v1 v2 0 with hv
    obtain ⟨M, hM⟩ := k5d_exists_key (fun s => (⟪fpoint p q r d s, r⟫, ⟪fpoint p q r d s, v⟫)) L
    set K := M • r + v with hK
    have hkey : ∀ s : ℝ × ℝ × ℝ, M * ⟪fpoint p q r d s, r⟫ + ⟪fpoint p q r d s, v⟫ =
        ⟪d, K⟫ + s.1 * ⟪p, K⟫ + s.2.1 * ⟪q, K⟫ + s.2.2 * ⟪r, K⟫ := by
      intro s
      rw [← inner_fpoint p q r d K s, hK, inner_add_right, real_inner_smul_right]
    have hz : ∀ s : ℝ × ℝ × ℝ, ⟪fpoint p q r d s, r⟫ = ⟪d, r⟫ + s.1 * ⟪p, r⟫ + s.2.1 * ⟪q, r⟫ + s.2.2 * ⟪r, r⟫ :=
      fun s => inner_fpoint p q r d r s
    have hMi : ∀ i j, LexLt (⟪fpoint p q r d (X i), r⟫, ⟪fpoint p q r d (X i), v⟫)
        (⟪fpoint p q r d (X j), r⟫, ⟪fpoint p q r d (X j), v⟫) →
        M * ⟪fpoint p q r d (X i), r⟫ + ⟪fpoint p q r d (X i), v⟫ <
          M * ⟪fpoint p q r d (X j), r⟫ + ⟪fpoint p q r d (X j), v⟫ :=
      fun i j h => hM (X i) (hXL i) (X j) (hXL j) h
    refine k5d_lex_of_real _ _ hL M hMi ?_
    have hfun : (fun i => M * ⟪fpoint p q r d (X i), r⟫ + ⟪fpoint p q r d (X i), v⟫) =
        (fun i => ⟪d, K⟫ + (X i).1 * ⟪p, K⟫ + (X i).2.1 * ⟪q, K⟫ + (X i).2.2 * ⟪r, K⟫) := funext (fun i => hkey _)
    rw [hfun]
    refine hreal v1 v2 hCv ⟪d, K⟫ ⟪p, K⟫ ⟪q, K⟫ ⟪r, K⟫ ?_ ?_ ?_
    · intro s hs t ht hlt
      have h1 : LexLt (⟪fpoint p q r d s, r⟫, ⟪fpoint p q r d s, v⟫)
          (⟪fpoint p q r d t, r⟫, ⟪fpoint p q r d t, v⟫) := by
        left; simp only; rw [hz s, hz t]; linarith
      have := hM s hs t ht h1
      rw [hkey, hkey] at this
      exact this
    · intro s hs t ht heq hw
      have h1 : LexLt (⟪fpoint p q r d s, r⟫, ⟪fpoint p q r d s, v⟫)
          (⟪fpoint p q r d t, r⟫, ⟪fpoint p q r d t, v⟫) := by
        right
        refine ⟨?_, ?_⟩
        · simp only; rw [hz s, hz t]; linarith
        · have e1 := inner_fpoint p q r d v s
          have e2 := inner_fpoint p q r d v t
          simp only; rw [e1, e2]
          have hv : v = fcomb p q r v1 v2 0 := hv
          rw [hv] at *
          linarith
      have := hM s hs t ht h1
      rw [hkey, hkey] at this
      exact this
    · intro i j hij
      by_contra hne
      have hne' : (⟪fpoint p q r d (X i), r⟫, ⟪fpoint p q r d (X i), v⟫) ≠
          (⟪fpoint p q r d (X j), r⟫, ⟪fpoint p q r d (X j), v⟫) := fun h =>
        hne (hL i j (congrArg Prod.fst h) (congrArg Prod.snd h))
      rw [← hkey, ← hkey] at hij
      rcases lexLt_total hne' with h | h
      · exact absurd hij (ne_of_lt (hMi i j h))
      · exact absurd hij.symm (ne_of_lt (hMi j i h))
  rcases hΔ.lt_or_gt with hneg | hpos
  · have hD : 0 < -det3 p q r := by linarith
    refine ⟨k, inferInstance, fun i => fpoint p q r d (X (-i)), fcomb p q r v1 v2 0, ?_⟩
    have := lexCell_coord V p q r d (k := k) hk (fun i => X (-i)) (v1, v2, 0)
      (fun i => hmem (-i))
      (hcyc_rev (fun i j h1 h2 => tsc_scale hD (hcy i j h1 h2))) ?_ (lexUni_neg hlex')
    · simpa using this
    · intro y hy hyx
      rcases hVall y hy with ⟨i, rfl⟩ | ⟨t, ht, rfl⟩
      · exact (hyx (-i) (by simp)).elim
      · exact ⟨t, rfl, hrest_rev (fun i => tsc_scale hD (hre t ht i))⟩
  · refine ⟨k, inferInstance, fun i => fpoint p q r d (X i), fcomb p q r v1 v2 0, ?_⟩
    have := lexCell_coord V p q r d (k := k) hk X (v1, v2, 0) hmem
      (fun i j h1 h2 => tsc_scale hpos (hcy i j h1 h2)) ?_ hlex'
    · simpa using this
    · intro y hy hyx
      rcases hVall y hy with ⟨i, rfl⟩ | ⟨t, ht, rfl⟩
      · exact (hyx i rfl).elim
      · exact ⟨t, rfl, fun i => tsc_scale hpos (hre t ht i)⟩

end C2
end Type08Sp
end Minimality
