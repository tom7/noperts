module

public import Minimality.Type08S.P2QQ0b

@[expose] public section

set_option relaxedAutoImplicit true
/-!
# pkQ / Q0c: `Norm08w.hU_lt`, `exists_nf08w`, `nf_inj6_w`, `ord08_w`.
-/

set_option autoImplicit true
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

/-- Common part of `exists_nf08w` and `Norm08w.hU_lt`: the frame, the strict entries, and `μ ≠ 0`. -/
theorem nf08w_core {a a' b b' c c' d : ℝ³} (N : Norm08w a a' b b' c c' d) :
    ∃ (o E₁ E₂ E₃ : ℝ³) (θ : Fin 6 → ℝ), det3 E₁ E₂ E₃ ≠ 0 ∧
      (∀ k : Fin 24, k ≠ 9 → k ≠ 10 → k ≠ 11 → 0 < ineq08 θ k) ∧
      pts08 a a' b b' c c' d = nfShape08 o E₁ E₂ E₃ θ ∧
      ∃ μ : ℝ, μ ≠ 0 ∧ galeD N.G.l N.G.m a a' = μ * gWa θ ∧ galeD N.G.l N.G.m b b' = μ * gWb θ ∧
        galeD N.G.l N.G.m c c' = μ * gWc θ ∧ galeD N.G.l N.G.m b c = μ * gWU θ := by
  have hd := N.hd
  have hdet : det3 (a - d) (b - d) (c - d) ≠ 0 := by
    have := hd.det_Qac_ne
    intro h; apply this
    simp only [det3_expand, PiLp.sub_apply] at h ⊢
    linarith
  obtain ⟨p, q, hp, hq, hpq, hc'⟩ := hd.Qab_coords
  obtain ⟨r, s, hr, hs, hrs, hb'⟩ := hd.Qac_coords
  obtain ⟨t, u, ht, hu, htu, ha'⟩ := hd.Qbc_coords
  have hpts : pts08 a a' b b' c c' d = nfShape08 d (a - d) (b - d) (c - d) ![p, q, r, s, t, u] := by
    funext i
    fin_cases i <;> simp [pts08, nfShape08]
    all_goals assumption
  refine ⟨d, a - d, b - d, c - d, ![p, q, r, s, t, u], hdet, ?_, hpts, ?_⟩
  swap
  · obtain ⟨μ, h0, h1, h2, h3, h4⟩ := gale_nf08w N.G hdet hc' hb' ha' (by linarith)
    exact ⟨μ, h0, h1, h2, h3, h4⟩
  have hF := N.F
  have hnd := N.F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨haa', hab, hab', hac, hac'⟩, ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩,
    ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd
  have hE := hdet
  obtain ⟨f1, f2, f3, f4⟩ := fc08_d ![p, q, r, s, t, u]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Matrix.head_cons] at f1 f2 f3 f4
  have n1 : fc08 ![p, q, r, s, t, u] 0 3 5 6 ≠ 0 := by rw [f1]; positivity
  have n2 : fc08 ![p, q, r, s, t, u] 1 2 5 6 ≠ 0 := by rw [f2]; positivity
  have n3 : fc08 ![p, q, r, s, t, u] 1 3 4 6 ≠ 0 := by rw [f3]; positivity
  have n4 : fc08 ![p, q, r, s, t, u] 1 3 5 6 ≠ 0 := by
    rw [f4]; have : 0 < t * s * p + u * r * q := by positivity
    linarith
  have g12 := fac08 hdet hpts N.F.ab'c' 0 3 5 1 rfl rfl rfl hd.ab'c' (N.F.ab'c'.neg a' (by simp) (by ne_tac) (by ne_tac) (by ne_tac)) n1
  have g13 := fac08 hdet hpts N.F.ab'c' 0 3 5 2 rfl rfl rfl hd.ab'c' (N.F.ab'c'.neg b (by simp) (by ne_tac) (by ne_tac) (by ne_tac)) n1
  have g14 := fac08 hdet hpts N.F.ab'c' 0 3 5 4 rfl rfl rfl hd.ab'c' (N.F.ab'c'.neg c (by simp) (by ne_tac) (by ne_tac) (by ne_tac)) n1
  have g15 := fac08 hdet hpts N.F.a'bc' 1 2 5 0 rfl rfl rfl hd.a'bc' (N.F.a'bc'.neg a (by simp) (by ne_tac) (by ne_tac) (by ne_tac)) n2
  have g16 := fac08 hdet hpts N.F.a'bc' 1 2 5 3 rfl rfl rfl hd.a'bc' (N.F.a'bc'.neg b' (by simp) (by ne_tac) (by ne_tac) (by ne_tac)) n2
  have g17 := fac08 hdet hpts N.F.a'bc' 1 2 5 4 rfl rfl rfl hd.a'bc' (N.F.a'bc'.neg c (by simp) (by ne_tac) (by ne_tac) (by ne_tac)) n2
  have g18 := fac08 hdet hpts N.F.a'b'c 1 3 4 0 rfl rfl rfl hd.a'b'c (N.F.a'b'c.neg a (by simp) (by ne_tac) (by ne_tac) (by ne_tac)) n3
  have g19 := fac08 hdet hpts N.F.a'b'c 1 3 4 2 rfl rfl rfl hd.a'b'c (N.F.a'b'c.neg b (by simp) (by ne_tac) (by ne_tac) (by ne_tac)) n3
  have g20 := fac08 hdet hpts N.F.a'b'c 1 3 4 5 rfl rfl rfl hd.a'b'c (N.F.a'b'c.neg c' (by simp) (by ne_tac) (by ne_tac) (by ne_tac)) n3
  have g21 := fac08 hdet hpts N.F.a'b'c' 1 3 5 0 rfl rfl rfl hd.a'b'c' (N.F.a'b'c'.neg a (by simp) (by ne_tac) (by ne_tac) (by ne_tac)) n4
  have g22 := fac08 hdet hpts N.F.a'b'c' 1 3 5 2 rfl rfl rfl hd.a'b'c' (N.F.a'b'c'.neg b (by simp) (by ne_tac) (by ne_tac) (by ne_tac)) n4
  have g23 := fac08 hdet hpts N.F.a'b'c' 1 3 5 4 rfl rfl rfl hd.a'b'c' (N.F.a'b'c'.neg c (by simp) (by ne_tac) (by ne_tac) (by ne_tac)) n4
  have h6 : 0 < p + q - 1 := by linarith
  have h7 : 0 < r + s - 1 := by linarith
  have h8 : 0 < t + u - 1 := by linarith
  intro k hk9 hk10 hk11
  fin_cases k
  exacts [hp, hq, hr, hs, ht, hu, h6, h7, h8, absurd rfl hk9, absurd rfl hk10, absurd rfl hk11,
    g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23]

/-- `[b c] < 0` on `Norm08w` (`[b c] = μ·gWU`, `gWU < 0`, `μ ≠ 0`). -/
theorem Norm08w.hU_lt {a a' b b' c c' d : ℝ³} (N : Norm08w a a' b b' c c' d) :
    galeD N.G.l N.G.m b c < 0 := by
  obtain ⟨o, E₁, E₂, E₃, θ, hE, hθ, hpts, μ, hμ, h1, h2, h3, h4⟩ := nf08w_core N
  have hU := N.hU
  have hg := gWU_neg_w0 θ hθ
  rw [h4] at hU ⊢
  have : 0 < μ := by
    rcases lt_or_gt_of_ne hμ with h | h
    · exfalso; nlinarith
    · exact h
  nlinarith

/-- **Normal form on the closure** (copy of `exists_nf08`; entries 9–11 replaced by `gWa, gWb ≥ 0`; `μ > 0`). -/
theorem exists_nf08w {a a' b b' c c' d : ℝ³} (N : Norm08w a a' b b' c c' d) :
    ∃ (o E₁ E₂ E₃ : ℝ³) (θ : Fin 6 → ℝ), det3 E₁ E₂ E₃ ≠ 0 ∧ Ineq08w θ ∧
      pts08 a a' b b' c c' d = nfShape08 o E₁ E₂ E₃ θ ∧
      ∃ μ : ℝ, 0 < μ ∧ galeD N.G.l N.G.m a a' = μ * gWa θ ∧ galeD N.G.l N.G.m b b' = μ * gWb θ ∧
        galeD N.G.l N.G.m c c' = μ * gWc θ := by
  obtain ⟨o, E₁, E₂, E₃, θ, hE, hθ, hpts, μ, hμ, h1, h2, h3, h4⟩ := nf08w_core N
  have hU := N.hU_lt
  have hg := gWU_neg_w0 θ hθ
  rw [h4] at hU
  have hμp : 0 < μ := by nlinarith
  have hκa := N.hκa; have hκb := N.hκb
  rw [h1] at hκa; rw [h2] at hκb
  refine ⟨o, E₁, E₂, E₃, θ, hE, ⟨hθ, ?_, ?_⟩, hpts, μ, hμp, h1, h2, h3⟩
  · exact nonneg_of_mul_nonneg_right hκa hμp
  · exact nonneg_of_mul_nonneg_right hκb hμp

theorem nf_inj6_w {o E₁ E₂ E₃ : ℝ³} (hE : det3 E₁ E₂ E₃ ≠ 0) {θ : Fin 6 → ℝ}
    (hθ : Ineq08w θ) :
    Function.Injective (fun i : Fin 6 => nfShape08 o E₁ E₂ E₃ θ i.castSucc) := by
  have p0 := hθ.pos 0 (by decide) (by decide) (by decide)
  have p1 := hθ.pos 1 (by decide) (by decide) (by decide)
  have p2 := hθ.pos 2 (by decide) (by decide) (by decide)
  have p3 := hθ.pos 3 (by decide) (by decide) (by decide)
  have p4 := hθ.pos 4 (by decide) (by decide) (by decide)
  have p5 := hθ.pos 5 (by decide) (by decide) (by decide)
  simp only [ineq08, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Matrix.head_cons] at p0 p1 p2 p3 p4 p5
  intro i j h
  by_contra hne
  have key := nfinj08 hE (θ := θ) i.castSucc j.castSucc h
  have h0 := key 0; have h1 := key 1; have h2 := key 2
  fin_cases i <;> fin_cases j <;> first | exact hne rfl | (revert h0 h1 h2; norm_num [cp08] <;> (intros; linarith))

theorem ord08_w {o E₁ E₂ E₃ : ℝ³} (hE : det3 E₁ E₂ E₃ ≠ 0) {θ : Fin 6 → ℝ}
    (hθ : Ineq08w θ) (i : Fin 3) :
    (grp08 i).Ordered (nfShape08 o E₁ E₂ E₃ θ) := by
  have hinj := nf_inj6_w (o := o) hE hθ
  have p1 := hθ.pos 1 (by decide) (by decide) (by decide)
  have p5 := hθ.pos 5 (by decide) (by decide) (by decide)
  simp only [ineq08, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Matrix.head_cons] at p1 p5
  fin_cases i
  · exact inner_lt08 (fun h => absurd (hinj (a₁ := 4) (a₂ := 1) h) (by decide))
  · refine inner_lt08 (fun h => ?_)
    have := nfinj08 hE (θ := θ) 2 6 h 1
    simp [cp08] at this
  · trivial

end Type08Sp
end Minimality
