module

public import Minimality.Type08S.LexK
public import Minimality.Type08S.C2K19C
public import Minimality.Type08S.C2K3D

@[expose] public section

/-!
# lexgen support: k-level lex cells with neighbour-step (peak) depth conditions

`lexk_cell_frame` (LexK.lean) needs the full lex-sorted depth list.  When some depth pairs have no fixed order on
the cell's domain (a free top pair, unrelated far points), use `lexg_cell_frame_nb` (one peak) or
`lexg_cell_frame_nb2` (free top pair `i0, i0 + 1`): only the neighbour steps toward the peak are needed.
The tilt list is internally extended by `(1,0,0), (0,1,0)`, which separates every pair of distinct frame points,
so injectivity of the lex depths comes from injectivity of `X`.  Prefix `lexg_`.
-/
set_option autoImplicit true
set_option relaxedAutoImplicit true
open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

theorem lexg_pos_append : ∀ (l m : List ℝ), lexkPos l → lexkPos (l ++ m)
  | [], _, h => h.elim
  | b :: l, m, h => by
    rcases h with h | ⟨h0, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨h0, lexg_pos_append l m h⟩

theorem lexg_trich_fun {α : Type*} (g : α → ℝ) : ∀ l : List α,
    lexkPos (l.map g) ∨ lexkPos (l.map (fun a => -g a)) ∨ ∀ a ∈ l, g a = 0
  | [] => Or.inr (Or.inr (by simp))
  | a :: l => by
    simp only [List.map_cons, lexkPos_cons, List.mem_cons, forall_eq_or_imp]
    rcases lt_trichotomy (g a) 0 with h | h | h
    · exact Or.inr (Or.inl (Or.inl (by linarith)))
    · rcases lexg_trich_fun g l with h' | h' | h'
      · exact Or.inl (Or.inr ⟨h, h'⟩)
      · exact Or.inr (Or.inl (Or.inr ⟨by rw [h]; ring, h'⟩))
      · exact Or.inr (Or.inr ⟨h, h'⟩)
    · exact Or.inl (Or.inl h)

/-- Core (ℝ³ form, ccw): TS rows lex-positive, every pair lex-separated, and a lex unimodality proof from the
lex-ordered pairs. -/
theorem lexg_core (V : Finset ℝ³) (u₀ : ℝ³) (vs : List ℝ³) {k : ℕ} [NeZero k] (hk : 3 ≤ k)
    (x : ZMod k → ℝ³) (hmem : ∀ i, x i ∈ V)
    (hcyc : ∀ i j, j ≠ i → j ≠ i + 1 → lexkPos ((u₀ :: vs).map (det3 (x (i + 1) - x i) (x j - x i))))
    (hrest : ∀ y ∈ V, (∀ j, y ≠ x j) → ∀ i, lexkPos ((u₀ :: vs).map (det3 (x (i + 1) - x i) (y - x i))))
    (hsep : ∀ i j, i ≠ j → LexkDep u₀ vs (x i) (x j) ∨ LexkDep u₀ vs (x j) (x i))
    (hU : ∀ z w : ZMod k → ℝ, (∀ i j, z i = z j → w i = w j → i = j) →
      (∀ i j, LexkDep u₀ vs (x i) (x j) → LexLt (z i, w i) (z j, w j)) → LexUni z w) :
    HasLexCellAt V u₀ := by
  have E1 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ p : ZMod k × ZMod k, p.2 ≠ p.1 → p.2 ≠ p.1 + 1 →
      TiltSign (x (p.1 + 1) - x p.1) (x p.2 - x p.1) u₀ (lexkVec vs δ) := by
    refine Filter.eventually_all.2 fun p => ?_
    by_cases h : p.2 ≠ p.1 ∧ p.2 ≠ p.1 + 1
    · exact (lexk_ts_ev (hcyc p.1 p.2 h.1 h.2)).mono fun δ hδ _ _ => hδ
    · exact Eventually.of_forall fun δ h1 h2 => absurd ⟨h1, h2⟩ h
  have E2 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ y ∈ V, (∀ j, y ≠ x j) → ∀ i,
      TiltSign (x (i + 1) - x i) (y - x i) u₀ (lexkVec vs δ) := by
    refine (Filter.eventually_all_finset V).2 fun y hy => ?_
    by_cases h : ∀ j, y ≠ x j
    · exact (Filter.eventually_all.2 fun i => lexk_ts_ev (hrest y hy h i)).mono fun δ hδ _ => hδ
    · exact Eventually.of_forall fun δ h' => absurd h' h
  have E3 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ p : ZMod k × ZMod k, LexkDep u₀ vs (x p.1) (x p.2) →
      LexLt (⟪x p.1, u₀⟫, ⟪x p.1, lexkVec vs δ⟫) (⟪x p.2, u₀⟫, ⟪x p.2, lexkVec vs δ⟫) := by
    refine Filter.eventually_all.2 fun p => ?_
    by_cases h : LexkDep u₀ vs (x p.1) (x p.2)
    · exact (lexk_dep_ev h).mono fun δ hδ _ => hδ
    · exact Eventually.of_forall fun δ h' => absurd h' h
  obtain ⟨δ, ⟨h1, h2⟩, h3⟩ := ((E1.and E2).and E3).exists
  have hinj : ∀ i j, ⟪x i, u₀⟫ = ⟪x j, u₀⟫ → ⟪x i, lexkVec vs δ⟫ = ⟪x j, lexkVec vs δ⟫ → i = j := by
    intro i j hz hw
    by_contra hne
    rcases hsep i j hne with h | h
    · have := h3 (i, j) h; simp only at this; rw [hz, hw] at this; exact lexk_lt_irrefl _ this
    · have := h3 (j, i) h; simp only at this; rw [hz, hw] at this; exact lexk_lt_irrefl _ this
  exact ⟨k, inferInstance, x, lexkVec vs δ, hk, hmem, fun i j a b => h1 (i, j) a b, h2,
    hU _ _ hinj fun i j h => h3 (i, j) h⟩

/-- Core, reversed orientation (rows lex-negative); the cell uses the reversed cycle. -/
theorem lexg_core_rev (V : Finset ℝ³) (u₀ : ℝ³) (vs : List ℝ³) {k : ℕ} [NeZero k] (hk : 3 ≤ k)
    (x : ZMod k → ℝ³) (hmem : ∀ i, x i ∈ V)
    (hcyc : ∀ i j, j ≠ i → j ≠ i + 1 →
      lexkPos ((u₀ :: vs).map (fun u => -det3 (x (i + 1) - x i) (x j - x i) u)))
    (hrest : ∀ y ∈ V, (∀ j, y ≠ x j) → ∀ i,
      lexkPos ((u₀ :: vs).map (fun u => -det3 (x (i + 1) - x i) (y - x i) u)))
    (hsep : ∀ i j, i ≠ j → LexkDep u₀ vs (x i) (x j) ∨ LexkDep u₀ vs (x j) (x i))
    (hU : ∀ z w : ZMod k → ℝ, (∀ i j, z i = z j → w i = w j → i = j) →
      (∀ i j, LexkDep u₀ vs (x i) (x j) → LexLt (z i, w i) (z j, w j)) → LexUni z w) :
    HasLexCellAt V u₀ := by
  refine lexg_core V u₀ vs hk (fun i => x (-i)) (fun i => hmem _) ?_ ?_ ?_ ?_
  · intro i j h1 h2
    have := hcyc (-i - 1) (-j) (fun e => h2 (by linear_combination -e)) (fun e => h1 (by linear_combination -e))
    have e1 : -i - 1 + 1 = -i := by ring
    have e2 : -(i + 1) = -i - 1 := by ring
    rw [e1] at this
    refine lexkPos_map_of _ _ 1 one_pos (fun u => ?_) _ this
    rw [one_mul, e2, lexk_det3_rev]
  · intro y hy hyx i
    have := hrest y hy (fun j => by simpa using hyx (-j)) (-i - 1)
    have e1 : -i - 1 + 1 = -i := by ring
    have e2 : -(i + 1) = -i - 1 := by ring
    rw [e1] at this
    refine lexkPos_map_of _ _ 1 one_pos (fun u => ?_) _ this
    rw [one_mul, e2, lexk_det3_rev]
  · intro i j hij
    exact hsep (-i) (-j) (fun e => hij (neg_injective e))
  · intro z w hinj H
    have h := hU (fun i => z (-i)) (fun i => w (-i)) (fun i j h1 h2 => neg_injective (hinj _ _ h1 h2))
      (fun i j h => H (-i) (-j) (by simpa only [neg_neg] using h))
    apply lexUni_rev_shift 0
    simpa only [zero_sub] using h

/-- Depth step `s <lex t` in frame coordinates: `(⟪t - s, r⟫, ⟪t - s, T₁⟫, …)` lex-positive. -/
def lexgRow (p q r d : ℝ³) (T : List (ℝ × ℝ × ℝ)) (s t : ℝ × ℝ × ℝ) : Prop :=
  lexkPos (((0, 0, 1) :: T).map (fun v => ⟪fpoint p q r d t - fpoint p q r d s, lexkF p q r v⟫))

theorem lexg_det3_lin (p q r : ℝ³) (a b c : ℝ) :
    det3 (fcomb p q r a b c) q r = a * det3 p q r ∧ det3 p (fcomb p q r a b c) r = b * det3 p q r ∧
      det3 p q (fcomb p q r a b c) = c * det3 p q r := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [fcomb, det3_expand, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] <;> ring

/-- **k-level lex cell, frame form, with a caller-supplied lex unimodality proof** (from the depth steps
`lexgRow`).  Either sign of `det3 p q r`. -/
theorem lexg_cell_frame (V : Finset ℝ³) (p q r d : ℝ³) (hΔ : det3 p q r ≠ 0) {k : ℕ} [NeZero k] (hk : 3 ≤ k)
    (X : ZMod k → ℝ × ℝ × ℝ) (hXinj : ∀ i j, X i = X j → i = j) (T : List (ℝ × ℝ × ℝ))
    (hmem : ∀ i, fpoint p q r d (X i) ∈ V)
    (hcyc : ∀ i j, j ≠ i → j ≠ i + 1 → lexkPos (((0, 0, 1) :: T).map (lexkD3 (X (i + 1) - X i) (X j - X i))))
    (hrest : ∀ y ∈ V, (∀ j, y ≠ fpoint p q r d (X j)) → ∃ t, y = fpoint p q r d t ∧
      ∀ i, lexkPos (((0, 0, 1) :: T).map (lexkD3 (X (i + 1) - X i) (t - X i))))
    (hU : ∀ z w : ZMod k → ℝ, (∀ i j, z i = z j → w i = w j → i = j) →
      (∀ i j, lexgRow p q r d T (X i) (X j) → LexLt (z i, w i) (z j, w j)) → LexUni z w) :
    HasLexCellAt V r := by
  have hr : lexkF p q r (0, 0, 1) = r := by simp [lexkF, fcomb]
  set T' := T ++ [(1, 0, 0), (0, 1, 0)] with hT'
  set vs := T'.map (lexkF p q r) with hvs
  have hL : ∀ (g : ℝ³ → ℝ), (r :: vs).map g = ((0, 0, 1) :: T').map (fun v => g (lexkF p q r v)) := by
    intro g; simp only [hvs, List.map_cons, List.map_map, hr]; rfl
  have hA : ∀ (g : ℝ × ℝ × ℝ → ℝ), lexkPos (((0, 0, 1) :: T).map g) →
      lexkPos (((0, 0, 1) :: T').map g) := by
    intro g h
    have e : ((0, 0, 1) :: T').map g = ((0, 0, 1) :: T).map g ++ [(1, 0, 0), (0, 1, 0)].map g := by
      simp [hT']
    rw [e]; exact lexg_pos_append _ _ h
  have hsep : ∀ i j, i ≠ j → LexkDep r vs (fpoint p q r d (X i)) (fpoint p q r d (X j)) ∨
      LexkDep r vs (fpoint p q r d (X j)) (fpoint p q r d (X i)) := by
    intro i j hij
    unfold LexkDep; rw [hL, hL]
    rcases lexg_trich_fun (fun v => ⟪fpoint p q r d (X j) - fpoint p q r d (X i), lexkF p q r v⟫)
      ((0, 0, 1) :: T') with h | h | h
    · exact Or.inl h
    · right
      refine lexkPos_map_of _ _ 1 one_pos (fun v => ?_) _ h
      simp only [one_mul]
      rw [← inner_neg_left, neg_sub]
    · exfalso
      have h1 := h (1, 0, 0) (by simp [hT'])
      have h2 := h (0, 1, 0) (by simp [hT'])
      have h3 := h (0, 0, 1) (by simp)
      simp only [lexk_inner_F, one_mul, zero_mul, add_zero, zero_add] at h1 h2 h3
      have hw := fpoint_sub p q r d (X j) (X i)
      have hww : ⟪fpoint p q r d (X j) - fpoint p q r d (X i),
          fcomb p q r (X j - X i).1 (X j - X i).2.1 (X j - X i).2.2⟫ = 0 := by
        simp only [fcomb, inner_add_right, real_inner_smul_right, h1, h2, h3, mul_zero, add_zero]
      rw [← hw] at hww
      have w0 := inner_self_eq_zero.1 hww
      rw [w0] at hw
      obtain ⟨d1, d2, d3'⟩ := lexg_det3_lin p q r (X j - X i).1 (X j - X i).2.1 (X j - X i).2.2
      rw [← hw] at d1 d2 d3'
      have z1 : det3 (0 : ℝ³) q r = 0 := by simp [det3_expand]
      have z2 : det3 p (0 : ℝ³) r = 0 := by simp [det3_expand]
      have z3 : det3 p q (0 : ℝ³) = 0 := by simp [det3_expand]
      rw [z1] at d1; rw [z2] at d2; rw [z3] at d3'
      have E1 := (mul_eq_zero.1 d1.symm).resolve_right hΔ
      have E2 := (mul_eq_zero.1 d2.symm).resolve_right hΔ
      have E3 := (mul_eq_zero.1 d3'.symm).resolve_right hΔ
      have e0 : X j - X i = 0 := Prod.ext E1 (Prod.ext E2 E3)
      exact hij (hXinj _ _ (sub_eq_zero.1 e0)).symm
  have hdx : ∀ i j, lexgRow p q r d T (X i) (X j) →
      LexkDep r vs (fpoint p q r d (X i)) (fpoint p q r d (X j)) := by
    intro i j h; unfold LexkDep; rw [hL]; exact hA _ h
  rcases lt_or_gt_of_ne hΔ with hneg | hpos
  · refine lexg_core_rev V r vs hk _ hmem (fun i j h1 h2 => ?_) (fun y hy hyx i => ?_) hsep
      (fun z w hinj H => hU z w hinj fun i j h => H i j (hdx i j h))
    · rw [hL]
      exact lexkPos_map_of _ _ (-det3 p q r) (by linarith) (fun v => by rw [lexk_det3_frame]; ring) _
        (hA _ (hcyc i j h1 h2))
    · obtain ⟨t, rfl, ht⟩ := hrest y hy hyx
      rw [hL]
      exact lexkPos_map_of _ _ (-det3 p q r) (by linarith) (fun v => by rw [lexk_det3_frame]; ring) _
        (hA _ (ht i))
  · refine lexg_core V r vs hk _ hmem (fun i j h1 h2 => ?_) (fun y hy hyx i => ?_) hsep
      (fun z w hinj H => hU z w hinj fun i j h => H i j (hdx i j h))
    · rw [hL]
      exact lexkPos_map_of _ _ (det3 p q r) hpos (fun v => by rw [lexk_det3_frame]) _ (hA _ (hcyc i j h1 h2))
    · obtain ⟨t, rfl, ht⟩ := hrest y hy hyx
      rw [hL]
      exact lexkPos_map_of _ _ (det3 p q r) hpos (fun v => by rw [lexk_det3_frame]) _ (hA _ (ht i))

/-- One peak `i0`: every other index has a lex-higher neighbour. -/
theorem lexg_cell_frame_nb (V : Finset ℝ³) (p q r d : ℝ³) (hΔ : det3 p q r ≠ 0) {k : ℕ} [NeZero k]
    (hk : 3 ≤ k) (X : ZMod k → ℝ × ℝ × ℝ) (hXinj : ∀ i j, X i = X j → i = j) (T : List (ℝ × ℝ × ℝ))
    (hmem : ∀ i, fpoint p q r d (X i) ∈ V)
    (hcyc : ∀ i j, j ≠ i → j ≠ i + 1 → lexkPos (((0, 0, 1) :: T).map (lexkD3 (X (i + 1) - X i) (X j - X i))))
    (hrest : ∀ y ∈ V, (∀ j, y ≠ fpoint p q r d (X j)) → ∃ t, y = fpoint p q r d t ∧
      ∀ i, lexkPos (((0, 0, 1) :: T).map (lexkD3 (X (i + 1) - X i) (t - X i))))
    (i0 : ZMod k) (hP1 : lexgRow p q r d T (X (i0 - 1)) (X i0)) (hP2 : lexgRow p q r d T (X (i0 + 1)) (X i0))
    (hnb : ∀ i, i ≠ i0 →
      lexgRow p q r d T (X i) (X (i - 1)) ∨ lexgRow p q r d T (X i) (X (i + 1))) :
    HasLexCellAt V r :=
  lexg_cell_frame V p q r d hΔ hk X hXinj T hmem hcyc hrest fun z w hinj H =>
    k19_lexUni_nb z w hinj i0 (H _ _ hP1) (H _ _ hP2) fun i hi => (hnb i hi).imp (H _ _) (H _ _)

/-- Free top pair `(i0, i0 + 1)` (their order is not needed). -/
theorem lexg_cell_frame_nb2 (V : Finset ℝ³) (p q r d : ℝ³) (hΔ : det3 p q r ≠ 0) {k : ℕ} [NeZero k]
    (hk : 3 ≤ k) (X : ZMod k → ℝ × ℝ × ℝ) (hXinj : ∀ i j, X i = X j → i = j) (T : List (ℝ × ℝ × ℝ))
    (hmem : ∀ i, fpoint p q r d (X i) ∈ V)
    (hcyc : ∀ i j, j ≠ i → j ≠ i + 1 → lexkPos (((0, 0, 1) :: T).map (lexkD3 (X (i + 1) - X i) (X j - X i))))
    (hrest : ∀ y ∈ V, (∀ j, y ≠ fpoint p q r d (X j)) → ∃ t, y = fpoint p q r d t ∧
      ∀ i, lexkPos (((0, 0, 1) :: T).map (lexkD3 (X (i + 1) - X i) (t - X i))))
    (i0 : ZMod k) (hne : i0 + 1 ≠ i0) (hP1 : lexgRow p q r d T (X (i0 - 1)) (X i0))
    (hP2 : lexgRow p q r d T (X (i0 + 1 + 1)) (X (i0 + 1)))
    (hnb : ∀ i, i ≠ i0 → i ≠ i0 + 1 →
      lexgRow p q r d T (X i) (X (i - 1)) ∨ lexgRow p q r d T (X i) (X (i + 1))) :
    HasLexCellAt V r :=
  lexg_cell_frame V p q r d hΔ hk X hXinj T hmem hcyc hrest fun z w hinj H =>
    k19_lexUni_nb2 z w hinj i0 hne (H _ _ hP1) (H _ _ hP2) fun i hi hi' => (hnb i hi hi').imp (H _ _) (H _ _)

end C2
end Type08Sp
end Minimality
