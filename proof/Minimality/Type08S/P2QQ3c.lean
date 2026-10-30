module

public import Minimality.Type08S.P2QQ3b
public import Minimality.Type08S.P2QQ2b
public import Minimality.Type08S.GT_Wrap28
public import Minimality.Type08S.GT_Wrap16
public import Minimality.Type08S.P2E3

@[expose] public section

set_option relaxedAutoImplicit true
/-!
# pkQ / Q3c: W copies of P2E3 (`pts08_inj`, `case_of_regE`, `region08`, `wstraddle_*`, main) and the GT wrappers
`gt_far_N2''`, `gt_far_T4'` (signature only: the proofs use `N.F`, `N.hd`), ending in PQ0's
`isRupert_type08_limit_hdnR'_w`.
-/

set_option autoImplicit true
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace W

variable {a a' b b' c c' d : ℝ³}

/-- **The far triple tie, N2** (`Norm08w` copy of `GT_Wrap28.gt_far_N2''`; only `N.F`, `N.hd` are used). -/
theorem gt_far_N2'' (N : Norm08w a a' b b' c c' d)
    (hfar : N.F.abc'.f a' < N.F.abc'.f c) (hq₂ : N.F.ab'c'.f a' < N.F.ab'c'.f c)
    (htouch : ⟪b, c - a'⟫ = ⟪c', c - a'⟫ ∧ ⟪b', c - a'⟫ = ⟪c', c - a'⟫)
    (hzw0 : ⟪a', c - a'⟫ < ⟪b', c - a'⟫) (hzv0 : ⟪b', c - a'⟫ ≤ ⟪c, c - a'⟫) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  obtain ⟨E, U, zv, zw, A, b1, b2, r1, r2, s, m3, a1, a2, a3, FH, FQab, FQac, FT1, FT2, FT3, P, hE⟩ :=
    n2_pic N.F N.hd hfar hq₂ htouch hzw0 hzv0
  have Fr := n2_frame N.F
  by_cases hnb : NotBeyondW E ⟪N.F.a'b'c.N, N.F.a'b'c.N⟫ b1 b2 r1 r2 A 0
  · exact n2_sminus N.F N.hd P hE hnb
  · have hwb : WeakBeyond E ⟪N.F.a'b'c.N, N.F.a'b'c.N⟫ b1 b2 r1 r2 := by
      rw [P.hAE] at hnb
      have hE' : 0 < E := by rw [hE]; exact Fr.hee
      exact weak_of_not_nb hE' Fr.hNN hnb
    rcases P.cfg.hzv.lt_or_eq with hz | hz
    · rcases lt_trichotomy r2 b2 with hrb | hrb | hrb
      · exact n2_lt N.F N.hd P hE hz hwb hrb
      · exact n2_eq N.F N.hd P hE hz hwb hrb
      · exact n2_gt N.F N.hd P hE hz hwb hrb
    · rcases lt_trichotomy r2 b2 with hrb | hrb | hrb
      · exact n2_lt0 N.F N.hd P hE hz.symm hwb hrb
      · exact n2_eq0 N.F N.hd P hE hz.symm hwb hrb
      · exact n2_gt0 N.F N.hd P hE hz.symm hwb hrb


/-- **The far triple tie, T4** (`Norm08w` copy of `GT_Wrap16.gt_far_T4'`). -/
theorem gt_far_T4' (N : Norm08w a a' b b' c c' d)
    (hfc : N.F.abc'.f c < N.F.abc'.f a') (hfc' : N.F.a'bc.f c' < N.F.a'bc.f a)
    (htouch : ⟪c, b - d⟫ = ⟪b', b - d⟫ ∧ ⟪c', b - d⟫ = ⟪b', b - d⟫)
    (hzw0 : ⟪d, b - d⟫ < ⟪c, b - d⟫) (hzv0 : ⟪c, b - d⟫ ≤ ⟪b, b - d⟫) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  obtain ⟨E, U, zv, zw, A, b1, b2, r1, r2, xa, za, ua, a3, t, FH, FQac, FT1, FT2, FT3, FT4, P, hE⟩ :=
    t4_pic N.F N.hd hfc hfc' htouch hzw0 hzv0
  have Fr := t4_frame N.F N.hd
  by_cases hnb : NotBeyondW E ⟪N.F.a'bc.N, N.F.a'bc.N⟫ b1 b2 r1 r2 A 0
  · exact t4_sminus N.F N.hd P hE hnb
  · have hwb : WeakBeyond E ⟪N.F.a'bc.N, N.F.a'bc.N⟫ b1 b2 r1 r2 := by
      rw [P.hAE] at hnb
      have hE' : 0 < E := by rw [hE]; exact Fr.hee
      exact weak_of_not_nb hE' Fr.hNN hnb
    rcases lt_trichotomy r2 b2 with hrb | hrb | hrb
    · rcases lt_or_ge za zv with hzz | hzz
      · exact t4_c N.F N.hd P hE hwb hrb hzz
      · exact t4_b0 N.F N.hd P hE hwb hrb hzz
    · have hzz : zv < za := by
        rcases P.cfg.hzv.lt_or_eq with hz | hz
        · have cfg := P.cfg.toCfg hz
          exact cfg.T2_a_neg_iff.mp (cfg.T2_a_neg_of_le hrb.ge)
        · have := P.hmp
          rw [← hz] at this ⊢
          linarith
      exact t4_eq N.F N.hd P hE hwb hrb hzz
    · have hzz : zv < za := by
        rcases P.cfg.hzv.lt_or_eq with hz | hz
        · have cfg := P.cfg.toCfg hz
          exact cfg.T2_a_neg_iff.mp (cfg.T2_a_neg_of hrb)
        · have := P.hmp
          rw [← hz] at this ⊢
          linarith
      exact t4_a0 N.F N.hd P hE hwb hrb hzz

/-! ### Small facts -/

theorem pts08_inj {a a' b b' c c' d : ℝ³} (N : Norm08w a a' b b' c c' d) :
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
theorem case_of_regE {a a' b b' c c' d : ℝ³} (N : Norm08w a a' b b' c c' d) {o E₁ E₂ E₃ : ℝ³}
    {θ : Fin 6 → ℝ} (hE : det3 E₁ E₂ E₃ ≠ 0) (hθ : Ineq08w θ)
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
theorem region08 {a a' b b' c c' d : ℝ³} (N : Norm08w a a' b b' c c' d)
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

/-! ### The weak far triple: impossible at `c = z_w`, GT otherwise -/

theorem wstraddle_N2 {a a' b b' c c' d : ℝ³} (N : Norm08w a a' b b' c c' d) (hreg : RegN2 N.F)
    {o E₁ E₂ E₃ : ℝ³} {θ : Fin 6 → ℝ} (hE : det3 E₁ E₂ E₃ ≠ 0) (hθ : Ineq08w θ)
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
    have p22 := hθ.pos 22 (by decide) (by decide) (by decide)
    simp only [ineq08, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons] at p22
    have hne : fc08 θ 1 3 5 2 ≠ 0 := by
      intro h0; rw [h0, zero_mul] at p22; exact lt_irrefl _ p22
    rw [d1, e] at hz
    exact (mul_ne_zero hE (neg_ne_zero.mpr hne)) hz

theorem wstraddle_T4 {a a' b b' c c' d : ℝ³} (N : Norm08w a a' b b' c c' d) (hreg : RegT4 N.F)
    {o E₁ E₂ E₃ : ℝ³} {θ : Fin 6 → ℝ} (hE : det3 E₁ E₂ E₃ ≠ 0) (hθ : Ineq08w θ)
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
    have p1 := hθ.pos 1 (by decide) (by decide) (by decide); have p2 := hθ.pos 2 (by decide) (by decide) (by decide)
    simp only [ineq08, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons] at p1 p2
    rw [d1, e] at hz
    exact (mul_ne_zero hE (neg_ne_zero.mpr (mul_pos p1 p2).ne')) hz

/-! ### The refined limit theorem -/

set_option maxHeartbeats 4000000 in
/-- **P2, route B: the refined limit theorem with no tie and no touching hypothesis.** -/
theorem isRupert_type08_limit_hdnR' {a a' b b' c c' d : ℝ³} (N : Norm08w a a' b b' c c' d)
    (hT : ¬ IsT a' b c d) (hT' : ¬ IsT' a b c' d) (hQ : ¬ RegQ N.F) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) ∨
      ∃ t ∈ SC08, ((t.1 = 0 ∧ RegN2 N.F) ∨ (t.1 = 1 ∧ RegT4 N.F)) ∧ RobHDN a a' b b' c c' d t := by
  classical
  obtain ⟨o, E₁, E₂, E₃, θ, hE, hθ, hpts, -⟩ := exists_nf08w N
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
  rcases r2t08_w hE hθ hy hseg i hcase with ⟨j, hrob⟩ | hws
  swap
  · -- the weak far triple
    left
    rw [← hpts] at hws
    rcases hreg with ⟨rfl, h⟩ | ⟨rfl, h⟩
    · exact wstraddle_N2 N h hE hθ hpts hws
    · exact wstraddle_T4 N h hE hθ hpts hws
  -- generic approximants in the same region: the polygon part at one sign `s`
  obtain ⟨θs, hθs, hineq, hgen⟩ := exists_seq_strict θ hθ
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


end W

theorem isRupert_type08_limit_hdnR'_w {a a' b b' c c' d : ℝ³} (N : Norm08w a a' b b' c c' d)
    (hT : ¬ IsT a' b c d) (hT' : ¬ IsT' a b c' d) (hQ : ¬ RegQ N.F) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) ∨
      ∃ t ∈ SC08, ((t.1 = 0 ∧ RegN2 N.F) ∨ (t.1 = 1 ∧ RegT4 N.F)) ∧ RobHDN a a' b b' c c' d t :=
  W.isRupert_type08_limit_hdnR' N hT hT' hQ

end Type08Sp
end Minimality

