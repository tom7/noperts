module

public import Minimality.Type08S.P2I6
public import Minimality.Type08S.P2I8

@[expose] public section

set_option relaxedAutoImplicit true

/-!
# I7: R4′ with `a` hidden (`α4 > 1`) at `T'` (29.13): `X_bc' = (b, c', b', c)` robustly unimodal at `ℓ` with no
double normal in space perpendicular to `Q_bc`'s circle  ⟹  Rupert.  (Theorem D slide of `K_b` along `Q_bc`'s circle.)
-/

set_option autoImplicit true
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

/-- **R4′ at `T'`, `a` hidden** (`b' = d + α4 (a - d) + γ4 (c - d)`, `α4 > 1`). -/
theorem close_Tp_R4h_hdn {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) (hT' : IsT' a b c' d)
    {α4 γ4 : ℝ} (hb'rep : b' = d + α4 • (a - d) + γ4 • (c - d)) (hα : 1 < α4)
    (hrob : IsRobustUnimodal (fun i : ZMod 4 => ⟪quad b c' b' c i, b - d⟫))
    (hnd : NoHDNAt ({b, c', b', c} : Finset ℝ³) (b - d)) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  obtain ⟨e1, e2, e3, κ, hF, hκ, hxe, hf2, hL, hr⟩ := frame_Kb N
  obtain ⟨α4', β1, γ4', β6, γ6, hdet, hc', hb', ha', hα4, hγ4, hαγ, hβ1, hβ6, hγ6, hγ61, hcv⟩ :=
    norm08_coordsTp' N hT'
  -- uniqueness of `α4`
  have hαeq : α4' = α4 := by
    have hv : (α4' - α4) • (a - d) + (γ4' - γ4) • (c - d) = 0 := by
      have h1 : d + α4' • (a - d) + γ4' • (c - d) = d + α4 • (a - d) + γ4 • (c - d) := by
        rw [← hb', ← hb'rep]
      have : (α4' - α4) • (a - d) + (γ4' - γ4) • (c - d) =
          (d + α4' • (a - d) + γ4' • (c - d)) - (d + α4 • (a - d) + γ4 • (c - d)) := by module
      rw [this, h1, sub_self]
    have h0 : det3 ((α4' - α4) • (a - d) + (γ4' - γ4) • (c - d)) (c - d) (b - d) =
        (α4' - α4) * det3 (a - d) (c - d) (b - d) := by
      simp only [det3_expand, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
    rw [hv] at h0
    have hz : det3 (0 : ℝ³) (c - d) (b - d) = 0 := by simp [det3_expand]
    rw [hz] at h0
    have hne : det3 (a - d) (c - d) (b - d) ≠ 0 := by
      intro h; apply hdet
      have e : det3 (a - d) (b - d) (c - d) = - det3 (a - d) (c - d) (b - d) := by
        simp only [det3_expand]; ring
      rw [e, h, neg_zero]
    rcases mul_eq_zero.mp h0.symm with h | h
    · linarith
    · exact absurd h hne
  subst hαeq
  obtain ⟨hd1, hd2, hd3⟩ : ⟪b - d, e1⟫ = 0 ∧ ⟪b - d, e2⟫ = 0 ∧ ⟪b - d, e3⟫ = κ := by
    rw [hxe]
    refine ⟨?_, ?_, ?_⟩
    · rw [real_inner_smul_left, real_inner_comm, hF.n13]; ring
    · rw [real_inner_smul_left, real_inner_comm, hF.n23]; ring
    · rw [real_inner_smul_left, hF.n33]; ring
  set L := ⟪c - d, e1⟫ with hLdef
  set zf := ⟪c - d, e3⟫ with hzf
  set Xr := ⟪b' - d, e1⟫ with hXr
  set Yr := ⟪b' - d, e2⟫ with hYr
  set zr := ⟪b' - d, e3⟫ with hzr
  set Xa := ⟪a - d, e1⟫ with hXa
  set Ya := ⟪a - d, e2⟫ with hYa
  set za := ⟪a - d, e3⟫ with hza
  have hB : b' - d = α4' • (a - d) + γ4' • (c - d) := by rw [hb']; module
  have ip : ∀ (v w : ℝ³) (r s : ℝ) (x : ℝ³), ⟪r • v + s • w, x⟫ = r * ⟪v, x⟫ + s * ⟪w, x⟫ := by
    intro v w r s x; rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
  have r1 : Xr = α4' * Xa + γ4' * L := by rw [hXr, hB, ip]
  have r2 : Yr = α4' * Ya := by rw [hYr, hB, ip, hf2]; ring
  have r3 : zr = α4' * za + γ4' * zf := by rw [hzr, hB, ip]
  have hYa : 0 < Ya := by
    have : 0 < α4' * Ya := by rw [← r2]; exact hr
    exact pos_of_mul_pos_right this hα4.le
  have hcA : c' - d = (a - d) + β1 • (b - d) := by
    have : c' = d + (1 : ℝ) • (a - d) + β1 • (b - d) := hc'
    rw [this]; module
  have g1 : ⟪c' - d, e1⟫ = Xa := by rw [hcA, inner_add_left, real_inner_smul_left, hd1]; ring
  have g2 : ⟪c' - d, e2⟫ = Ya := by rw [hcA, inner_add_left, real_inner_smul_left, hd2]; ring
  have g3 : ⟪c' - d, e3⟫ = za + β1 * κ := by rw [hcA, inner_add_left, real_inner_smul_left, hd3]
  have hpA : a' - d = β6 • (b - d) + γ6 • (c - d) := by rw [ha']; module
  have p1 : ⟪a' - d, e1⟫ = γ6 * L := by rw [hpA, ip, hd1]; ring
  have p2 : ⟪a' - d, e2⟫ = 0 := by rw [hpA, ip, hd2, hf2]; ring
  have p3 : ⟪a' - d, e3⟫ = β6 * κ + γ6 * zf := by rw [hpA, ip, hd3]
  -- points
  have pB : b = fpt e1 e2 e3 d 0 0 κ := by
    have := pc_coords hF d b; rw [hd1, hd2, hd3] at this; exact this
  have pC : c = fpt e1 e2 e3 d L 0 zf := by
    have := pc_coords hF d c; rw [hf2] at this; exact this
  have pB' : b' = fpt e1 e2 e3 d Xr Yr zr := pc_coords hF d b'
  have pC' : c' = fpt e1 e2 e3 d Xa Ya (za + β1 * κ) := by
    have := pc_coords hF d c'; rw [g1, g2, g3] at this; exact this
  have pA : a = fpt e1 e2 e3 d Xa Ya (za + β1 * κ + (-(β1 * κ))) := by
    have := pc_coords hF d a
    rw [show za + β1 * κ + (-(β1 * κ)) = za by ring]; exact this
  have pA' : a' = fpt e1 e2 e3 d (γ6 * L) 0 (β6 * κ + γ6 * zf) := by
    have := pc_coords hF d a'; rw [p1, p2, p3] at this; exact this
  have hP : ∀ j, quad b c' b' c j =
      Qg e1 e2 e3 d κ L zf Xr Yr zr Xa Ya (za + β1 * κ) (-j) := by
    intro j
    have n1 : -(1 : ZMod 4) = 3 := by decide
    have n2 : -(2 : ZMod 4) = 2 := by decide
    have n3 : -(3 : ZMod 4) = 1 := by decide
    rcases zmod4_cases j with rfl | rfl | rfl | rfl <;>
      simp only [Qg, n1, n2, n3, neg_zero, quad, Matrix.cons_val, ← pB, ← pC, ← pB', ← pC']
  -- numeric facts
  have hcg : 0 < Ya * Xr - Xa * Yr := by
    have : Ya * Xr - Xa * Yr = γ4' * L * Ya := by rw [r1, r2]; ring
    rw [this]; positivity
  have hcr : 0 < (Xa - Xr) * (-Yr) - (Ya - Yr) * (L - Xr) := by
    have : (Xa - Xr) * (-Yr) - (Ya - Yr) * (L - Xr) = Ya * L * (α4' + γ4' - 1) := by
      rw [r1, r2]; ring
    rw [this]; have : 0 < α4' + γ4' - 1 := by linarith
    positivity
  have hYgr : Ya < Yr := by rw [r2]; nlinarith
  have hXp0 : 0 < γ6 * L := by positivity
  have hXpL : γ6 * L < L := by nlinarith
  have hDp : L * ((β6 * κ + γ6 * zf) - κ) - γ6 * L * (zf - κ) ≠ 0 := by
    have : L * ((β6 * κ + γ6 * zf) - κ) - γ6 * L * (zf - κ) = L * κ * (β6 + γ6 - 1) := by ring
    rw [this]
    refine mul_ne_zero (mul_ne_zero hL.ne' hκ) (by linarith)
  have hδ : κ * (-(β1 * κ)) < 0 := by
    have : κ * (-(β1 * κ)) = -(β1 * κ ^ 2) := by ring
    rw [this]; have : 0 < κ ^ 2 := by positivity
    have : 0 < β1 * κ ^ 2 := by positivity
    linarith
  have key : ∀ κv : ℝ, 0 < κv → (κv • e3 = b - d ∨ κv • e3 = d - b) →
      IsRupert ({d, fpt e1 e2 e3 d 0 0 κ, fpt e1 e2 e3 d L 0 zf, fpt e1 e2 e3 d Xr Yr zr,
        fpt e1 e2 e3 d Xa Ya (za + β1 * κ), fpt e1 e2 e3 d (γ6 * L) 0 (β6 * κ + γ6 * zf),
        fpt e1 e2 e3 d Xa Ya (za + β1 * κ + (-(β1 * κ)))} : Finset ℝ³) := by
    intro κv hκv hv
    have hz : IsRobustUnimodal (fun i => ⟪Qg e1 e2 e3 d κ L zf Xr Yr zr Xa Ya (za + β1 * κ) i, κv • e3⟫) := by
      have h0 : IsRobustUnimodal (fun i : ZMod 4 => ⟪quad b c' b' c (-i), κv • e3⟫) := by
        rcases hv with hv | hv
        · rw [hv]; exact hrob.reflect
        · rw [hv]
          have := hrob.reflect.neg
          convert this using 2 with i
          rw [← inner_neg_right, neg_sub]
      convert h0 using 2 with i
      rw [hP (-i), neg_neg]
    obtain ⟨hc1, hc2⟩ := qg_rim_ccw hF d hκv hL hr hYa hcr hcg (κ := κ) (zf := zf) (zr := zr)
      (zg := za + β1 * κ)
    have hbad : NoPersistHDN (Qg e1 e2 e3 d κ L zf Xr Yr zr Xa Ya (za + β1 * κ)) (κv • e3)
        ((κ * κv) • e1) := by
      have hfun : Qg e1 e2 e3 d κ L zf Xr Yr zr Xa Ya (za + β1 * κ) = fun i => quad b c' b' c (-i) := by
        funext i; rw [hP (-i), neg_neg]
      have h0 : NoHDNRim (Qg e1 e2 e3 d κ L zf Xr Yr zr Xa Ya (za + β1 * κ)) (b - d) := by
        rw [hfun]
        exact hnd.rim _ (fun i => by
          rcases zmod4_cases (-i) with h | h | h | h <;> simp [quad, h])
      have h1 : NoHDNRim (Qg e1 e2 e3 d κ L zf Xr Yr zr Xa Ya (za + β1 * κ)) (κv • e3) := by
        rcases hv with hv | hv
        · rw [hv]; exact h0
        · rw [hv, ← neg_sub]; exact h0.neg
      have he3 : e3 ≠ 0 := by
        intro h; have := hF.n33; rw [h] at this; simp at this
      exact noPersist_of_noHDNRim (by norm_num : 3 ≤ 4) _ ((κ * κv) • e1) (smul_ne_zero hκv.ne' he3) hc1 h1
    exact close_hidden_frame hF d hκ hκv hL hr hYa hcr hcg hXp0 hXpL hDp hYgr hδ hz hbad
  have fin : IsRupert ({d, fpt e1 e2 e3 d 0 0 κ, fpt e1 e2 e3 d L 0 zf, fpt e1 e2 e3 d Xr Yr zr,
        fpt e1 e2 e3 d Xa Ya (za + β1 * κ), fpt e1 e2 e3 d (γ6 * L) 0 (β6 * κ + γ6 * zf),
        fpt e1 e2 e3 d Xa Ya (za + β1 * κ + (-(β1 * κ)))} : Finset ℝ³) := by
    rcases lt_or_gt_of_ne hκ with hn | hp
    · exact key (-κ) (by linarith) (Or.inr (by rw [neg_smul, ← hxe]; abel))
    · exact key κ hp (Or.inl hxe.symm)
  rw [← pB, ← pC, ← pB', ← pC', ← pA', ← pA] at fin
  convert fin using 1
  ext y
  simp only [mem_insert, mem_singleton]
  tauto

end Type08Sp
end Minimality

#print axioms Minimality.Type08Sp.close_Tp_R4h_hdn
