module

public import Minimality.Type08S.P2Defs
public import Minimality.Type08S.P2P4
public import Minimality.Type08S.P2E1
public import Minimality.Type08S.P2E2

@[expose] public section

set_option relaxedAutoImplicit true

/-!
# E3 (type 08): package P2, route B of `tt3/handoff.md` — the refined limit theorem with no tie hypothesis
and no touching hypothesis

`isRupert_type08_limit_hdnR'`: a `Norm08` shape off `T`, `T'` and outside the Q region is Rupert, or the
single-circle closing of its region has a robust limit corner rim with its own HDN (`RobHDN`).

Proof (no tie restoration, no `TieOKG`, no `¬ Touch`):
1. the region (N2: `γ6 > 1`, T4: `γ6 < 1 < α1`) and its group `i`;
2. MF holds at the limit `K` itself at every unimodular metric (`N2_core`, `T4_core` need no genericity);
3. Lemma R2T* (`E1.r2t_star`) at `K`: a closing of group `i` is robustly unimodal at `K`, or the weak far
   triple `z_w ≤ c ≤ z_v`;
4. the weak far triple: `c = z_w` puts four vertices in a plane ⟂ the view, impossible (a facet
   determinant); `c > z_w` is `TieN2 ∧ N2Closable` (with P4) resp. `TieT4 ∧ T4Closable`, Rupert by GT
   (`gt_far_N2''`, `gt_far_T4'`);
5. the robust closing: generic approximants `θ_n → θ` in the same region give the polygon part for both
   closings at one sign `s` (`poly08`); `E2.isRupert_or_rimHDN_of_tendsto_geom` with robustness at `K`
   gives Rupert or a robust corner rim with its own HDN; N2's `K_{a'}` (not in `SC08`) is Rupert by
   `rupert_of_free_limit_rim`.
-/

set_option autoImplicit true
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

/-! ### Small facts -/

theorem pts08_inj {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) :
    Function.Injective (pts08 a a' b b' c c' d) := by
  have hnd := N.F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨haa', hab, hab', hac, hac'⟩, ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩,
    ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd
  obtain ⟨hda, hda', hdb, hdb', hdc, hdc'⟩ := N.hd.ne
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [pts08]

/-- Copy of C2c's `case_of_reg`. -/
theorem case_of_regE {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) {o E₁ E₂ E₃ : ℝ³}
    {θ : Fin 6 → ℝ} (hE : det3 E₁ E₂ E₃ ≠ 0) (hθ : ∀ k, 0 < ineq08 θ k)
    (hpts : pts08 a a' b b' c c' d = nfShape08 o E₁ E₂ E₃ θ) (i : Fin 3)
    (h : (i = 0 ∧ RegN2 N.F) ∨ (i = 1 ∧ RegT4 N.F)) :
    (i = 0 ∧ 1 < θ 5) ∨ (i = 1 ∧ θ 5 < 1 ∧ 1 < θ 0) := by
  have hnd := N.F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨haa', hab, hab', hac, hac'⟩, ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩,
    ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd
  have hg := region_gamma6 N hE hθ hpts
  have ha := region_alpha1 N hE hθ hpts
  have hfc : N.F.abc'.f c < 0 := N.F.abc'.neg c (by simp) (Ne.symm hac) (Ne.symm hbc) hcc'
  rcases h with ⟨rfl, h⟩ | ⟨rfl, h1, h2⟩
  · left
    refine ⟨rfl, ?_⟩
    have h' : N.F.abc'.f a' < N.F.abc'.f c := h
    rw [hg] at h'; nlinarith
  · right
    have hfa : N.F.a'bc.f a < 0 :=
      N.F.a'bc.neg a (by simp) (by ne_tac) (by ne_tac) (by ne_tac)
    refine ⟨rfl, ?_, ?_⟩
    · have h' : N.F.abc'.f c < N.F.abc'.f a' := h1
      rw [hg] at h'; nlinarith
    · have h' : N.F.a'bc.f c' < N.F.a'bc.f a := h2
      rw [ha] at h'; nlinarith

/-- Off `T`, `T'` and the Q region, the shape is in the N2 or the T4 region. -/
theorem region08 {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d)
    (hT : ¬ IsT a' b c d) (hT' : ¬ IsT' a b c' d) (hQ : ¬ RegQ N.F) : RegN2 N.F ∨ RegT4 N.F := by
  by_cases htie₁ : N.F.abc'.f a' = N.F.abc'.f c
  · exact absurd (N.hd.tieT_geom htie₁) hT
  rcases lt_or_gt_of_ne htie₁ with h | h
  · exact Or.inl h
  · by_cases htie₂ : N.F.a'bc.f c' = N.F.a'bc.f a
    · exact absurd (N.hd.tieT'_geom htie₂) hT'
    rcases lt_or_gt_of_ne htie₂ with h' | h'
    · exact Or.inr ⟨h, h'⟩
    · exact absurd ⟨h, h'⟩ hQ

/-- The weak far triple of an edge group (`z_w ≤ c ≤ z_v`; R2T*'s exception). -/
def WStraddle {n : ℕ} (y : Fin n → ℝ³) : ViewGroup n → Prop
  | .single _ => False
  | .edge u v w f1 r f2 =>
      ⟪y f1, u y⟫ = ⟪y r, u y⟫ ∧ ⟪y r, u y⟫ = ⟪y f2, u y⟫ ∧
        ⟪y w, u y⟫ ≤ ⟪y r, u y⟫ ∧ ⟪y r, u y⟫ ≤ ⟪y v, u y⟫

/-! ### R2T* at the limit (MF at every metric, no genericity) -/

set_option maxHeartbeats 1000000 in
theorem r2t08 {o E₁ E₂ E₃ : ℝ³} (hE : det3 E₁ E₂ E₃ ≠ 0) {θ : Fin 6 → ℝ} (hθ : ∀ k, 0 < ineq08 θ k)
    (hy : Function.Injective (nfShape08 o E₁ E₂ E₃ θ))
    (hseg : ∀ i j m : Fin 7, nfShape08 o E₁ E₂ E₃ θ m ≠ nfShape08 o E₁ E₂ E₃ θ i →
      nfShape08 o E₁ E₂ E₃ θ m ≠ nfShape08 o E₁ E₂ E₃ θ j → ∀ s : ℝ, 0 < s → s < 1 →
      nfShape08 o E₁ E₂ E₃ θ m ≠ nfShape08 o E₁ E₂ E₃ θ i +
        s • (nfShape08 o E₁ E₂ E₃ θ j - nfShape08 o E₁ E₂ E₃ θ i))
    (i : Fin 3) (hcase : (i = 0 ∧ 1 < θ 5) ∨ (i = 1 ∧ θ 5 < 1 ∧ 1 < θ 0)) :
    (∃ j, IsRobustUnimodal ((test08 i true j).depth (nfShape08 o E₁ E₂ E₃ θ))) ∨
      WStraddle (nfShape08 o E₁ E₂ E₃ θ) (grp08 i) := by
  set y := nfShape08 o E₁ E₂ E₃ θ with hydef
  have hord := ord08 (o := o) hE hθ i
  rcases hcase with ⟨rfl, h6⟩ | ⟨rfl, h6, h0⟩
  · have e1 : test08 0 true true = LabTest.quad (fun y => y 4 - y 1) 4 2 5 3 := rfl
    have e2 : test08 0 true false = LabTest.quad (fun y => y 4 - y 1) 1 2 5 3 := rfl
    have R := r2t_star y (fun y => y 4 - y 1) (covView_diff08 4 1) 4 1 2 5 3 hy (by decide) hseg
      hord (by
        intro L hL h1 h2
        have hinj : ∀ j, Function.Injective ((test08 0 true j).depth
            (nfShape08 (L o) (L E₁) (L E₂) (L E₃) θ)) := by
          intro j; cases j
          · rw [e2, ← mapShape_nfShape08]; exact h2
          · rw [e1, ← mapShape_nfShape08]; exact h1
        obtain ⟨j, hj⟩ := N2_core o E₁ E₂ E₃ hE θ hθ h6 L hL hinj
        rw [← mapShape_nfShape08] at hj
        cases j
        · right; rw [← e2]; exact hj
        · left; rw [← e1]; exact hj)
    rcases R with h | h | h
    · exact Or.inl ⟨true, by rw [e1]; exact h⟩
    · exact Or.inl ⟨false, by rw [e2]; exact h⟩
    · exact Or.inr h
  · have e1 : test08 1 true true = LabTest.quad (fun y => y 2 - y 6) 2 5 3 4 := rfl
    have e2 : test08 1 true false = LabTest.quad (fun y => y 2 - y 6) 6 5 3 4 := rfl
    have R := r2t_star y (fun y => y 2 - y 6) (covView_diff08 2 6) 2 6 5 3 4 hy (by decide) hseg
      hord (by
        intro L hL h1 h2
        have hinj : ∀ j, Function.Injective ((test08 1 true j).depth
            (nfShape08 (L o) (L E₁) (L E₂) (L E₃) θ)) := by
          intro j; cases j
          · rw [e2, ← mapShape_nfShape08]; exact h2
          · rw [e1, ← mapShape_nfShape08]; exact h1
        obtain ⟨j, hj⟩ := T4_core o E₁ E₂ E₃ hE θ hθ L hL hinj
        rw [← mapShape_nfShape08] at hj
        cases j
        · right; rw [← e2]; exact hj
        · left; rw [← e1]; exact hj)
    rcases R with h | h | h
    · exact Or.inl ⟨true, by rw [e1]; exact h⟩
    · exact Or.inl ⟨false, by rw [e2]; exact h⟩
    · exact Or.inr h

/-! ### The weak far triple: impossible at `c = z_w`, GT otherwise -/

theorem wstraddle_N2 {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) (hreg : RegN2 N.F)
    {o E₁ E₂ E₃ : ℝ³} {θ : Fin 6 → ℝ} (hE : det3 E₁ E₂ E₃ ≠ 0) (hθ : ∀ k, 0 < ineq08 θ k)
    (hpts : pts08 a a' b b' c c' d = nfShape08 o E₁ E₂ E₃ θ)
    (h : WStraddle (pts08 a a' b b' c c' d) (grp08 0)) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  simp only [grp08, WStraddle, pts08, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    Matrix.head_cons] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hu : c - a' ≠ 0 := by
    have := pts08_inj N
    intro e; exact absurd (this (sub_eq_zero.mp e : pts08 a a' b b' c c' d 4 = pts08 a a' b b' c c' d 1))
      (by decide)
  rcases h3.lt_or_eq with h3 | h3
  · have hq2 := hq2_of_regN2 N hreg
    exact gt_far_N2'' N hreg hq2 ⟨h1, h2.symm⟩ (by linarith) (by linarith)
  · exfalso
    -- `a', b, c', b'` in one plane ⟂ `c - a'`
    have hz : det3 (b - a') (c' - a') (b' - a') = 0 :=
      det3_eq_zero_of_perp hu (by rw [inner_sub_left]; linarith) (by rw [inner_sub_left]; linarith)
        (by rw [inner_sub_left]; linarith)
    have d1 : det3 (b - a') (c' - a') (b' - a') = det3 E₁ E₂ E₃ * fc08 θ 1 2 5 3 := by
      have := det3_nf08 o E₁ E₂ E₃ θ 1 2 5 3; rw [← hpts] at this; exact this
    have e : fc08 θ 1 2 5 3 = -fc08 θ 1 3 5 2 := by
      simp only [fc08, cdet, cp08, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]; ring
    have p22 := hθ 22
    simp only [ineq08, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons] at p22
    have hne : fc08 θ 1 3 5 2 ≠ 0 := by
      intro h0; rw [h0, zero_mul] at p22; exact lt_irrefl _ p22
    rw [d1, e] at hz
    exact (mul_ne_zero hE (neg_ne_zero.mpr hne)) hz

theorem wstraddle_T4 {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) (hreg : RegT4 N.F)
    {o E₁ E₂ E₃ : ℝ³} {θ : Fin 6 → ℝ} (hE : det3 E₁ E₂ E₃ ≠ 0) (hθ : ∀ k, 0 < ineq08 θ k)
    (hpts : pts08 a a' b b' c c' d = nfShape08 o E₁ E₂ E₃ θ)
    (h : WStraddle (pts08 a a' b b' c c' d) (grp08 1)) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  simp only [grp08, WStraddle, pts08, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    Matrix.head_cons] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hu : b - d ≠ 0 := by
    have := pts08_inj N
    intro e; exact absurd (this (sub_eq_zero.mp e : pts08 a a' b b' c c' d 2 = pts08 a a' b b' c c' d 6))
      (by decide)
  rcases h3.lt_or_eq with h3 | h3
  · exact gt_far_T4' N hreg.1 hreg.2 ⟨h2.symm, h1⟩ (by linarith) (by linarith)
  · exfalso
    -- `d, c', b', c` in one plane ⟂ `b - d`
    have hz : det3 (c' - d) (b' - d) (c - d) = 0 :=
      det3_eq_zero_of_perp hu (by rw [inner_sub_left]; linarith) (by rw [inner_sub_left]; linarith)
        (by rw [inner_sub_left]; linarith)
    have d1 : det3 (c' - d) (b' - d) (c - d) = det3 E₁ E₂ E₃ * fc08 θ 6 5 3 4 := by
      have := det3_nf08 o E₁ E₂ E₃ θ 6 5 3 4; rw [← hpts] at this; exact this
    have e : fc08 θ 6 5 3 4 = -(θ 1 * θ 2) := by
      simp only [fc08, cdet, cp08, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]; ring
    have p1 := hθ 1; have p2 := hθ 2
    simp only [ineq08, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons] at p1 p2
    rw [d1, e] at hz
    exact (mul_ne_zero hE (neg_ne_zero.mpr (mul_pos p1 p2).ne')) hz

/-! ### The refined limit theorem -/

set_option maxHeartbeats 4000000 in
/-- **P2, route B: the refined limit theorem with no tie and no touching hypothesis.** -/
theorem isRupert_type08_limit_hdnR' {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d)
    (hT : ¬ IsT a' b c d) (hT' : ¬ IsT' a b c' d) (hQ : ¬ RegQ N.F) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) ∨
      ∃ t ∈ SC08, ((t.1 = 0 ∧ RegN2 N.F) ∨ (t.1 = 1 ∧ RegT4 N.F)) ∧ RobHDN a a' b b' c c' d t := by
  classical
  obtain ⟨o, E₁, E₂, E₃, θ, hE, hθ, hpts⟩ := exists_nf08 N
  -- the region and its group
  obtain ⟨i, hreg⟩ : ∃ i : Fin 3, (i = 0 ∧ RegN2 N.F) ∨ (i = 1 ∧ RegT4 N.F) := by
    rcases region08 N hT hT' hQ with h | h
    · exact ⟨0, Or.inl ⟨rfl, h⟩⟩
    · exact ⟨1, Or.inr ⟨rfl, h⟩⟩
  have hcase := case_of_regE N hE hθ hpts i hreg
  obtain ⟨hseg, hsp⟩ := seg08 N
  simp only [hpts] at hseg hsp
  have hy : Function.Injective (nfShape08 o E₁ E₂ E₃ θ) := by rw [← hpts]; exact pts08_inj N
  -- R2T* at `(nfShape08 o E₁ E₂ E₃ θ)`
  rcases r2t08 hE hθ hy hseg i hcase with ⟨j, hrob⟩ | hws
  swap
  · -- the weak far triple
    left
    rw [← hpts] at hws
    rcases hreg with ⟨rfl, h⟩ | ⟨rfl, h⟩
    · exact wstraddle_N2 N h hE hθ hpts hws
    · exact wstraddle_T4 N h hE hθ hpts hws
  -- generic approximants in the same region: the polygon part at one sign `s`
  obtain ⟨θs, hθs, hgen⟩ := exists_seq_eval_ne_zero_fin genPoly08_ne_zero θ
  have hineq : ∀ᶠ n in atTop, ∀ k, 0 < ineq08 (θs n) k := by
    rw [Filter.eventually_all]
    intro k
    exact (((continuous_ineq08 k).tendsto θ).comp hθs).eventually (lt_mem_nhds (hθ k))
  have hcs : ∀ᶠ n in atTop, (i = 0 ∧ 1 < θs n 5) ∨ (i = 1 ∧ θs n 5 < 1 ∧ 1 < θs n 0) := by
    have c5 : Tendsto (fun n => θs n 5) atTop (𝓝 (θ 5)) := ((continuous_apply 5).tendsto θ).comp hθs
    have c0 : Tendsto (fun n => θs n 0) atTop (𝓝 (θ 0)) := ((continuous_apply 0).tendsto θ).comp hθs
    rcases hcase with ⟨hi, h5⟩ | ⟨hi, h5, h0⟩
    · filter_upwards [c5.eventually (lt_mem_nhds h5)] with n hn
      exact Or.inl ⟨hi, hn⟩
    · filter_upwards [c5.eventually (gt_mem_nhds h5), c0.eventually (lt_mem_nhds h0)] with n hn hn'
      exact Or.inr ⟨hi, hn, hn'⟩
  have hgeom : ∀ᶠ n in atTop, ∃ s : Bool, ∀ j', RimGeom (nfShape08 o E₁ E₂ E₃ (θs n))
      ((test08 i s j').view (nfShape08 o E₁ E₂ E₃ (θs n))) (test08 i s j').lab := by
    filter_upwards [hineq, hcs] with n hn hc
    obtain ⟨i', s, hc', hg⟩ := poly08 o E₁ E₂ E₃ hE (θs n) hn (hgen n)
    have hii : i' = i := by
      rcases hc' with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;>
      rcases hc with ⟨h4, h5⟩ | ⟨h4, h5, h6⟩
      · rw [h1, h4]
      · exfalso; linarith
      · exfalso; linarith
      · rw [h1, h4]
      · exfalso; linarith
      · exfalso; linarith
    subst hii
    exact ⟨s, hg⟩
  obtain ⟨s, hfreq⟩ := frequently_exists_of_finite hgeom.frequently
  -- robustness of the closing `(i, s, j)` at `(nfShape08 o E₁ E₂ E₃ θ)`
  have hrob' : IsRobustUnimodal ((test08 i s j).depth (nfShape08 o E₁ E₂ E₃ θ)) := by
    cases s
    · rw [depth_neg08]; exact hrob.neg
    · exact hrob
  -- the limit corner rim
  have hu : (test08 i s j).view (nfShape08 o E₁ E₂ E₃ θ) ≠ 0 := by
    have := view0_test08 N (i, s, j); rw [hpts] at this; exact this
  have hxs : ∀ m, Tendsto (fun n => nfShape08 o E₁ E₂ E₃ (θs n) m) atTop (𝓝 ((nfShape08 o E₁ E₂ E₃ θ) m)) := fun m =>
    (((continuous_apply m).comp (continuous_nf08 o E₁ E₂ E₃)).tendsto θ).comp hθs
  have hus : Tendsto (fun n => (test08 i s j).view (nfShape08 o E₁ E₂ E₃ (θs n))) atTop
      (𝓝 ((test08 i s j).view (nfShape08 o E₁ E₂ E₃ θ))) :=
    (((covView_test08 i s j).1.comp (continuous_nf08 o E₁ E₂ E₃)).tendsto θ).comp hθs
  rcases isRupert_or_rimHDN_of_tendsto_geom (nfShape08 o E₁ E₂ E₃ θ) hseg hsp (test08 i s j).lab hu
      (fun n => nfShape08 o E₁ E₂ E₃ (θs n)) (fun n => (test08 i s j).view (nfShape08 o E₁ E₂ E₃ (θs n)))
      hxs hus (hfreq.mono fun n h => h j) hrob' with h | ⟨k', hk, σ, hr, hz, hn⟩
  · left
    rw [← hpts, image_pts08] at h; exact h
  · by_cases ht : (i, s, j) ∈ SC08
    · right
      refine ⟨(i, s, j), ht, hreg, k', hk, σ, ?_, ?_, ?_⟩
      · rw [hpts]; exact hr
      · rw [hpts]; exact hz
      · rw [hpts]; exact hn
    · left
      rw [← hpts] at hr
      exact rupert_of_free_limit_rim N hT hT' (i, s, j) ht σ hr

/-- **The `P2Pkg` statement** (`isRupert_type08_limit_hdnR`), now proved; its hypotheses `hties`, `hN2`,
`hT4` are not used. -/
theorem isRupert_type08_limit_hdnR {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d)
    (hT : ¬ IsT a' b c d) (hT' : ¬ IsT' a b c' d) (hQ : ¬ RegQ N.F)
    (hties : (RegN2 N.F → TieOKG 0 a a' b b' c c' d) ∧ (RegT4 N.F → TieOKG 1 a a' b b' c c' d))
    (hN2 : ¬ (TieN2 a a' b b' c c' ∧ N2Closable N)) (hT4 : ¬ (TieT4 b b' c c' d ∧ T4Closable N)) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) ∨
      ∃ t ∈ SC08, ((t.1 = 0 ∧ RegN2 N.F) ∨ (t.1 = 1 ∧ RegT4 N.F)) ∧ RobHDN a a' b b' c c' d t :=
  isRupert_type08_limit_hdnR' N hT hT' hQ

end Type08Sp
end Minimality

#print axioms Minimality.Type08Sp.r2t08
#print axioms Minimality.Type08Sp.wstraddle_N2
#print axioms Minimality.Type08Sp.wstraddle_T4
#print axioms Minimality.Type08Sp.isRupert_type08_limit_hdnR'
#print axioms Minimality.Type08Sp.isRupert_type08_limit_hdnR
