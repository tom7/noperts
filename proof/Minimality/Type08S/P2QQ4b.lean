module

public import Minimality.Type08S.P2QQ4a

@[expose] public section

set_option relaxedAutoImplicit true
/-!
# pkQ / Q4b: `isRupert_type08_limit_T4cl` (statement as in PQ0).  Copy of `P2TL2.isRupert_type08_limit_T`.
-/

set_option autoImplicit true
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

/-- The weak far triple of the T4 group at `T`: `z_c = z_d` is impossible (region-free; copy of the `exfalso`
branch of `wstraddle_T4`), so it is `TouchT`. -/
theorem touchT_of_wstraddle_w {a a' b b' c c' d : ℝ³} (N : Norm08w a a' b b' c c' d)
    {o E₁ E₂ E₃ : ℝ³} {θ : Fin 6 → ℝ} (hE : det3 E₁ E₂ E₃ ≠ 0) (hθ : Ineq08w θ)
    (hpts : pts08 a a' b b' c c' d = nfShape08 o E₁ E₂ E₃ θ)
    (h : ⟪pts08 a a' b b' c c' d 5, pts08 a a' b b' c c' d 2 - pts08 a a' b b' c c' d 6⟫ =
        ⟪pts08 a a' b b' c c' d 3, pts08 a a' b b' c c' d 2 - pts08 a a' b b' c c' d 6⟫ ∧
      ⟪pts08 a a' b b' c c' d 3, pts08 a a' b b' c c' d 2 - pts08 a a' b b' c c' d 6⟫ =
        ⟪pts08 a a' b b' c c' d 4, pts08 a a' b b' c c' d 2 - pts08 a a' b b' c c' d 6⟫ ∧
      ⟪pts08 a a' b b' c c' d 6, pts08 a a' b b' c c' d 2 - pts08 a a' b b' c c' d 6⟫ ≤
        ⟪pts08 a a' b b' c c' d 3, pts08 a a' b b' c c' d 2 - pts08 a a' b b' c c' d 6⟫ ∧
      ⟪pts08 a a' b b' c c' d 3, pts08 a a' b b' c c' d 2 - pts08 a a' b b' c c' d 6⟫ ≤
        ⟪pts08 a a' b b' c c' d 2, pts08 a a' b b' c c' d 2 - pts08 a a' b b' c c' d 6⟫) :
    TouchT b b' c c' d := by
  simp only [pts08, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    Matrix.head_cons] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hu : b - d ≠ 0 := by
    have := W4.pts08_inj N
    intro e; exact absurd (this (sub_eq_zero.mp e : pts08 a a' b b' c c' d 2 = pts08 a a' b b' c c' d 6))
      (by decide)
  refine ⟨⟨by linarith, by linarith⟩, ?_, by linarith⟩
  rcases h3.lt_or_eq with h3 | h3
  · linarith
  · exfalso
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

set_option maxHeartbeats 4000000 in
/-- **P1-L.  The refined limit theorem at `T`.** -/
theorem isRupert_type08_limit_T4cl {a a' b b' c c' d : ℝ³} (N : Norm08w a a' b b' c c' d) (hTT : IsT a' b c d ∨ IsT' a b c' d) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) ∨ TouchT b b' c c' d ∨
      (RobKb a a' b b' c c' d ∧ ∃ s, RobHDN a a' b b' c c' d (1, s, true)) ∨
      (¬ RobKb a a' b b' c c' d ∧ ∃ s, RobHDN a a' b b' c c' d (1, s, false)) := by
  classical
  obtain ⟨o, E₁, E₂, E₃, θ, hE, hθ, hpts, -⟩ := exists_nf08w N
  obtain ⟨hg1, hg2⟩ := T4cl_of_TTp N hTT
  have hnd := N.F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨haa', hab, hab', hac, hac'⟩, ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩,
    ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd
  have hfc : N.F.abc'.f c < 0 := N.F.abc'.neg c (by simp) (Ne.symm hac) (Ne.symm hbc) hcc'
  have hfa : N.F.a'bc.f a < 0 :=
    N.F.a'bc.neg a (by simp) (by ne_tac) (by ne_tac) (by ne_tac)
  have hg := W4.region_gamma6 N hE hθ hpts
  have ha := W4.region_alpha1 N hE hθ hpts
  have h5 : θ 5 ≤ 1 := by
    rw [hg] at hg1; nlinarith
  have h0 : 1 ≤ θ 0 := by
    rw [ha] at hg2; nlinarith
  obtain ⟨hseg, hsp⟩ := W4.seg08 N
  simp only [hpts] at hseg hsp
  have hy : Function.Injective (nfShape08 o E₁ E₂ E₃ θ) := by rw [← hpts]; exact W4.pts08_inj N
  have R := r2t08_T4_w hE hθ hy hseg
  have key : ∀ j, IsRobustUnimodal ((test08 1 true j).depth (nfShape08 o E₁ E₂ E₃ θ)) →
      IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) ∨ ∃ s, RobHDN a a' b b' c c' d (1, s, j) := by
    intro j hrob
    obtain ⟨θs, hθs, hineq, hgen, hlt⟩ := exists_seq_strict_T4cl θ hθ h0 h5
    have hcs : ∀ᶠ n in atTop, θs n 5 < 1 ∧ 1 < θs n 0 := Filter.Eventually.of_forall hlt
    have hgeom : ∀ᶠ n in atTop, ∃ s : Bool, ∀ j', RimGeom (nfShape08 o E₁ E₂ E₃ (θs n))
        ((test08 1 s j').view (nfShape08 o E₁ E₂ E₃ (θs n))) (test08 1 s j').lab := by
      filter_upwards [hineq, hcs] with n hn hc
      obtain ⟨i', s, hc', hg⟩ := poly08 o E₁ E₂ E₃ hE (θs n) hn (hgen n)
      have hii : i' = 1 := by
        rcases hc' with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
        · exfalso; linarith [hc.1]
        · exact h1
        · exfalso; linarith [hc.2]
      subst hii
      exact ⟨s, hg⟩
    obtain ⟨s, hfreq⟩ := frequently_exists_of_finite hgeom.frequently
    have hrob' : IsRobustUnimodal ((test08 1 s j).depth (nfShape08 o E₁ E₂ E₃ θ)) := by
      cases s
      · rw [depth_neg08]; exact hrob.neg
      · exact hrob
    have hu : (test08 1 s j).view (nfShape08 o E₁ E₂ E₃ θ) ≠ 0 := by
      have := W4.view0_test08 N (1, s, j); rw [hpts] at this; exact this
    have hxs : ∀ m, Tendsto (fun n => nfShape08 o E₁ E₂ E₃ (θs n) m) atTop
        (𝓝 ((nfShape08 o E₁ E₂ E₃ θ) m)) := fun m =>
      (((continuous_apply m).comp (continuous_nf08 o E₁ E₂ E₃)).tendsto θ).comp hθs
    have hus : Tendsto (fun n => (test08 1 s j).view (nfShape08 o E₁ E₂ E₃ (θs n))) atTop
        (𝓝 ((test08 1 s j).view (nfShape08 o E₁ E₂ E₃ θ))) :=
      (((covView_test08 1 s j).1.comp (continuous_nf08 o E₁ E₂ E₃)).tendsto θ).comp hθs
    rcases isRupert_or_rimHDN_of_tendsto_geom (nfShape08 o E₁ E₂ E₃ θ) hseg hsp (test08 1 s j).lab hu
        (fun n => nfShape08 o E₁ E₂ E₃ (θs n)) (fun n => (test08 1 s j).view (nfShape08 o E₁ E₂ E₃ (θs n)))
        hxs hus (hfreq.mono fun n h => h j) hrob' with h | ⟨k', hk, σ, hr, hz, hn⟩
    · left
      rw [← hpts, image_pts08] at h; exact h
    · right
      refine ⟨s, k', hk, σ, ?_, ?_, ?_⟩
      · rw [hpts]; exact hr
      · rw [hpts]; exact hz
      · rw [hpts]; exact hn
  by_cases hKb : RobKb a a' b b' c c' d
  · have hrob : IsRobustUnimodal ((test08 1 true true).depth (nfShape08 o E₁ E₂ E₃ θ)) := by
      have := hKb; unfold RobKb at this; rw [hpts] at this; exact this
    rcases key true hrob with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inl ⟨hKb, h⟩))
  · rcases R with h | h | h
    · exact absurd (by unfold RobKb; rw [hpts]; exact h) hKb
    · rcases key false h with h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inr (Or.inr ⟨hKb, h'⟩))
    · refine Or.inr (Or.inl (touchT_of_wstraddle_w N hE hθ hpts ?_))
      rw [hpts]; exact h

end Type08Sp
end Minimality
