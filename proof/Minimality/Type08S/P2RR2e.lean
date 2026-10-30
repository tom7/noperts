module

public import Minimality.Type08S.P2RR2d

@[expose] public section

set_option relaxedAutoImplicit true
/-!
# pkR / R2e: `lexCell_N2WS`.
-/
set_option autoImplicit true
set_option linter.unusedVariables false
set_option maxHeartbeats 6400000

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

theorem lexCell_N2WS {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) (h : StN2WS a a' b b' c c' d)
    (hang : AngBig a b b' c d) : HasLexCellAt (V8 a a' b b' c c' d) (b - d) := by
  obtain ⟨hT, hB, hw⟩ := h
  obtain ⟨e1, e2, e3, o, ν, v1, C0, w1, ha, w3, α1, α4, β1, γ4, β6, hF, hν, hv1, hha, hα1, hα4, hγ4, hβ1,
    hβ6, hE, hu, hd, hb, hc, ha_, ha', hb', hc', hcd, hdot⟩ := h3_setup N hT
  have hγ1 : 1 < γ4 := R2.angBig_gamma hν hv1 hha hd hb hc ha_ hb' hang
  obtain ⟨hw1, hw2, hw3, hw4⟩ := hw
  -- depths
  have zc' : ⟪c', b - d⟫ = ν * (⟪o, e3⟫ + (α1 * w3 + β1 * ν)) := by
    rw [hdot, hc', inner_pt_3 hF]
  have zb : ⟪b, b - d⟫ = ν * (⟪o, e3⟫ + ν) := by rw [hdot, hb, inner_pt_3 hF]
  have zb' : ⟪b', b - d⟫ = ν * (⟪o, e3⟫ + (α4 * w3 + γ4 * C0)) := by
    rw [hdot, hb', inner_pt_3 hF]
  have zd : ⟪d, b - d⟫ = ν * (⟪o, e3⟫ + 0) := by rw [hdot, hd, inner_pt_3 hF]
  have za : ⟪a, b - d⟫ = ν * (⟪o, e3⟫ + w3) := by rw [hdot, ha_, inner_pt_3 hF]
  have zc : ⟪c, b - d⟫ = ν * (⟪o, e3⟫ + C0) := by rw [hdot, hc, inner_pt_3 hF]
  have hz1 : ν = α1 * w3 + β1 * ν := by
    have := hw1; rw [zb, zc'] at this
    have := mul_left_cancel₀ hν.ne' this; linarith
  have hz2 : ν = α4 * w3 + γ4 * C0 := by
    have := hw2; rw [zb', zc'] at this
    have := mul_left_cancel₀ hν.ne' this; linarith
  obtain ⟨hw3', hC', hpos⟩ := R2.arith_N2 hν hα1 hα4 hγ4 hβ1 hE hz1 hz2
  -- orientation
  obtain ⟨σ, hσ, hσv⟩ : ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ σ * v1 < 0 := by
    rcases lt_or_gt_of_ne hv1 with h | h
    · exact ⟨1, Or.inl rfl, by linarith⟩
    · exact ⟨-1, Or.inr rfl, by linarith⟩
  obtain ⟨t1, t2, hp1, hp3, hp4, n1, n2, n3, n4⟩ :=
    R2.tilt_choice (α1 := α1) (w1 := w1) hσ hσv hha hα4 hγ1
  have tt := K.K_ppp (t3 := 0) hF hσ hν hσv hha hα1 hα4 hγ4 hβ1 hβ6 hE hd hb hc ha_ ha' hb' hc' hu hp1 hp3 hp4
  -- lex part
  set v := pc e1 e2 e3 t1 t2 0 with hv
  have iv : ∀ X Y z : ℝ, ⟪pt e1 e2 e3 o X Y z, v⟫ = ⟪o, v⟫ + X * t1 + Y * t2 := by
    intro X Y z; rw [hv, R2.inner_pt_v hF]; ring
  have zlt : ∀ X Y : ℝ, X < Y → ν * (⟪o, e3⟫ + X) < ν * (⟪o, e3⟫ + Y) := fun X Y h =>
    mul_lt_mul_of_pos_left (by linarith) hν
  have zne : ∀ X Y : ℝ, X ≠ Y → ν * (⟪o, e3⟫ + X) ≠ ν * (⟪o, e3⟫ + Y) := fun X Y h h' =>
    h (by have := mul_left_cancel₀ hν.ne' h'; linarith)
  have lexU : LexUni (fun i => ⟪K.cyc5 d a c' b' c i, b - d⟫) (fun i => ⟪K.cyc5 d a c' b' c i, v⟫) := by
    have e1' : (fun i => ⟪K.cyc5 d a c' b' c i, b - d⟫) =
        K.cyc5 ⟪d, b - d⟫ ⟪a, b - d⟫ ⟪c', b - d⟫ ⟪b', b - d⟫ ⟪c, b - d⟫ := by
      funext i; rcases K.z5c i with rfl | rfl | rfl | rfl | rfl <;> rfl
    have e2' : (fun i => ⟪K.cyc5 d a c' b' c i, v⟫) =
        K.cyc5 ⟪d, v⟫ ⟪a, v⟫ ⟪c', v⟫ ⟪b', v⟫ ⟪c, v⟫ := by
      funext i; rcases K.z5c i with rfl | rfl | rfl | rfl | rfl <;> rfl
    rw [e1', e2']
    have hv_d : ⟪d, v⟫ = ⟪o, v⟫ + (-v1) * t1 + 0 * t2 := by rw [hd, iv]
    have hv_a : ⟪a, v⟫ = ⟪o, v⟫ + (-v1 + w1) * t1 + ha * t2 := by rw [ha_, iv]
    have hv_c' : ⟪c', v⟫ = ⟪o, v⟫ + (-v1 + α1 * w1) * t1 + (α1 * ha) * t2 := by rw [hc', iv]
    have hv_b' : ⟪b', v⟫ = ⟪o, v⟫ + (-v1 * (1 - γ4) + α4 * w1) * t1 + (α4 * ha) * t2 := by rw [hb', iv]
    have hv_c : ⟪c, v⟫ = ⟪o, v⟫ + 0 * t1 + 0 * t2 := by rw [hc, iv]
    have hzb' : ⟪b', b - d⟫ = ⟪c', b - d⟫ := hw2
    apply R2.lexUni_cyc5
    · left; show ⟪a, b - d⟫ < ⟪c', b - d⟫
      rw [za, zc', ← hz1]; exact zlt _ _ hw3'
    · left; show ⟪c, b - d⟫ < ⟪b', b - d⟫
      rw [zc, zb', ← hz2]; exact zlt _ _ hC'
    · rcases hpos with h | h
      · left; left; show ⟪d, b - d⟫ < ⟪a, b - d⟫
        rw [zd, za]; exact zlt _ _ h
      · right; left; show ⟪d, b - d⟫ < ⟪c, b - d⟫
        rw [zd, zc]; exact zlt _ _ h
    · refine R2.pair_ne fun hz => ?_
      rw [zd, zc'] at hz; exact absurd hz (zne _ _ (by linarith))
    · refine R2.pair_ne fun hz => ?_
      have : ⟪d, b - d⟫ ≠ ⟪b', b - d⟫ := by rw [zd, hzb', zc']; exact zne _ _ (by linarith)
      exact absurd hz this
    · refine R2.pair_ne fun _ => ?_
      rw [hv_d, hv_a]; intro h; apply n1; linarith
    · refine R2.pair_ne fun _ => ?_
      rw [hv_d, hv_c]; intro h; apply n2; linarith
    · refine R2.pair_ne fun hz => ?_
      have : ⟪a, b - d⟫ ≠ ⟪b', b - d⟫ := by rw [za, hzb', zc']; exact zne _ _ (by linarith)
      exact absurd hz this
    · refine R2.pair_ne fun _ => ?_
      rw [hv_a, hv_c]; intro h; apply n3; linarith
    · refine R2.pair_ne fun hz => ?_
      rw [zc, zc'] at hz; exact absurd hz (zne _ _ (by linarith))
    · refine R2.pair_ne fun _ => ?_
      rw [hv_c', hv_b']; intro h; apply n4; linarith
  have lexO := K.LexUni.orient hσ lexU
  have hmem : ∀ j, K.cyc5 d a c' b' c j ∈ V8 a a' b b' c c' d := by
    intro j
    rcases K.z5c j with rfl | rfl | rfl | rfl | rfl <;>
      simp [V8, K.cyc5]
  refine ⟨5, inferInstance, K.orient σ (K.cyc5 d a c' b' c), v, by norm_num, ?_, tt.1, tt.2, ?_⟩
  · intro i
    unfold K.orient; split_ifs
    · exact hmem i
    · exact hmem (-i)
  · have e1' : (fun i => ⟪K.orient σ (K.cyc5 d a c' b' c) i, b - d⟫) =
        K.orient σ (fun i => ⟪K.cyc5 d a c' b' c i, b - d⟫) := by
      funext i; unfold K.orient; split_ifs <;> rfl
    have e2' : (fun i => ⟪K.orient σ (K.cyc5 d a c' b' c) i, v⟫) =
        K.orient σ (fun i => ⟪K.cyc5 d a c' b' c i, v⟫) := by
      funext i; unfold K.orient; split_ifs <;> rfl
    rw [e1', e2']; exact lexO

end Type08Sp
end Minimality
