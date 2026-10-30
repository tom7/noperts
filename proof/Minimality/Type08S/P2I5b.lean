module

public import Minimality.Type08S.P2I4
public import Minimality.Type08S.P2I8
public import Minimality.Type08S.P2TpSetup

@[expose] public section

set_option relaxedAutoImplicit true

/-!
# I5: R3 at `T'` (29.13): `X_2c' = (d, c', b', c)` robustly unimodal at `ℓ = b - d` and without a double
normal in space perpendicular to `Q_ab`'s circle  ⟹  Rupert.  (Theorem D slide of `K_2` along `Q_ab`'s circle.)
-/

set_option autoImplicit true
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

theorem inner_dmb {e1 e2 e3 b d : ℝ³} (hF : Fr e1 e2 e3) {κ : ℝ} (hxe : d - b = κ • e3) :
    ⟪d - b, e1⟫ = 0 ∧ ⟪d - b, e2⟫ = 0 ∧ ⟪d - b, e3⟫ = κ := by
  rw [hxe]
  refine ⟨?_, ?_, ?_⟩
  · rw [real_inner_smul_left, real_inner_comm, hF.n13]; ring
  · rw [real_inner_smul_left, real_inner_comm, hF.n23]; ring
  · rw [real_inner_smul_left, hF.n33]; ring

/-- **R3 at `T'`** (29.13). -/
theorem close_Tp_R3_hdn {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) (hT' : IsT' a b c' d)
    (hrob : IsRobustUnimodal (fun i : ZMod 4 => ⟪quad d c' b' c i, b - d⟫))
    (hnd : NoHDNAt ({d, c', b', c} : Finset ℝ³) (b - d)) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  obtain ⟨e1, e2, e3, κ, hF, hκ, hxe, hf2, hL, hr⟩ := frame_K2 N
  obtain ⟨α4, β1, γ4, β6, γ6, hdet, hc', hb', ha', hα4, hγ4, hαγ, hβ1, hβ6, hγ6, hγ61, hcv⟩ :=
    norm08_coordsTp' N hT'
  obtain ⟨hd1, hd2, hd3⟩ := inner_dmb hF hxe
  -- affine relations relative to `b`
  have hA : a - b = (c' - b) + β1 • (d - b) := by
    have : c' = d + (1 : ℝ) • (a - d) + β1 • (b - d) := hc'
    rw [this]; module
  have hA' : a' - b = (1 - β6 - γ6) • (d - b) + γ6 • (c - b) := by
    rw [ha']; module
  have hB' : b' - b = α4 • (a - b) + γ4 • (c - b) + (1 - α4 - γ4) • (d - b) := by
    rw [hb']; module
  set L := ⟪c' - b, e1⟫ with hLdef
  set zf := ⟪c' - b, e3⟫ with hzf
  set Xg := ⟪c - b, e1⟫ with hXg
  set Yg := ⟪c - b, e2⟫ with hYg
  set zg := ⟪c - b, e3⟫ with hzg
  have ip : ∀ (v w : ℝ³) (r s : ℝ) (x : ℝ³), ⟪r • v + s • w, x⟫ = r * ⟪v, x⟫ + s * ⟪w, x⟫ := by
    intro v w r s x; rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
  -- the coordinates of `a`
  have a1 : ⟪a - b, e1⟫ = L := by rw [hA, inner_add_left, real_inner_smul_left, hd1]; ring
  have a2 : ⟪a - b, e2⟫ = 0 := by rw [hA, inner_add_left, real_inner_smul_left, hd2, hf2]; ring
  have a3 : ⟪a - b, e3⟫ = zf + β1 * κ := by rw [hA, inner_add_left, real_inner_smul_left, hd3]
  have q1 : ⟪a' - b, e1⟫ = γ6 * Xg := by rw [hA', ip, hd1]; ring
  have q2 : ⟪a' - b, e2⟫ = γ6 * Yg := by rw [hA', ip, hd2]; ring
  have q3 : ⟪a' - b, e3⟫ = (1 - β6 - γ6) * κ + γ6 * zg := by rw [hA', ip, hd3]
  have hip3 : ∀ (r s t : ℝ) (v w z : ℝ³) (x : ℝ³),
      ⟪r • v + s • w + t • z, x⟫ = r * ⟪v, x⟫ + s * ⟪w, x⟫ + t * ⟪z, x⟫ := by
    intro r s t v w z x
    rw [inner_add_left, inner_add_left, real_inner_smul_left, real_inner_smul_left, real_inner_smul_left]
  have r1 : ⟪b' - b, e1⟫ = α4 * L + γ4 * Xg := by rw [hB', hip3, a1, hd1]; ring
  have r2 : ⟪b' - b, e2⟫ = γ4 * Yg := by rw [hB', hip3, a2, hd2]; ring
  have r3 : ⟪b' - b, e3⟫ = α4 * (zf + β1 * κ) + γ4 * zg + (1 - α4 - γ4) * κ := by
    rw [hB', hip3, a3, hd3]
  have hYr : 0 < γ4 * Yg := by rw [← r2]; exact hr
  have hYg : 0 < Yg := pos_of_mul_pos_right hYr hγ4.le
  -- points in the frame
  have pB : b' = fpt e1 e2 e3 b (α4 * L + γ4 * Xg) (γ4 * Yg) (α4 * (zf + β1 * κ) + γ4 * zg + (1 - α4 - γ4) * κ) := by
    have := pc_coords hF b b'; rw [r1, r2, r3] at this; exact this
  have pD : d = fpt e1 e2 e3 b 0 0 κ := by
    have := pc_coords hF b d; rw [hd1, hd2, hd3] at this; exact this
  have pC' : c' = fpt e1 e2 e3 b L 0 zf := by
    have := pc_coords hF b c'; rw [hf2] at this; exact this
  have pC : c = fpt e1 e2 e3 b Xg Yg zg := pc_coords hF b c
  have pA : a = fpt e1 e2 e3 b L 0 (zf + β1 * κ) := by
    have := pc_coords hF b a; rw [a1, a2, a3] at this; exact this
  have pA' : a' = fpt e1 e2 e3 b (γ6 * Xg) (γ6 * Yg) ((1 - β6 - γ6) * κ + γ6 * zg) := by
    have := pc_coords hF b a'; rw [q1, q2, q3] at this; exact this
  -- the quadrilateral
  have hQ : ∀ j, Qg e1 e2 e3 b κ L zf (α4 * L + γ4 * Xg) (γ4 * Yg)
      (α4 * (zf + β1 * κ) + γ4 * zg + (1 - α4 - γ4) * κ) Xg Yg zg j = quad d c' b' c j := by
    intro j
    simp only [Qg]
    rw [← pD, ← pC', ← pB, ← pC]
  -- numeric facts
  have hcg : 0 < Yg * (α4 * L + γ4 * Xg) - Xg * (γ4 * Yg) := by
    have : Yg * (α4 * L + γ4 * Xg) - Xg * (γ4 * Yg) = α4 * L * Yg := by ring
    rw [this]; positivity
  have hcr : 0 < (Xg - (α4 * L + γ4 * Xg)) * (-(γ4 * Yg)) - (Yg - γ4 * Yg) * (L - (α4 * L + γ4 * Xg)) := by
    have : (Xg - (α4 * L + γ4 * Xg)) * (-(γ4 * Yg)) - (Yg - γ4 * Yg) * (L - (α4 * L + γ4 * Xg)) =
        Yg * L * (α4 + γ4 - 1) := by ring
    rw [this]; have : 0 < α4 + γ4 - 1 := by linarith
    positivity
  have hYq : 0 < γ6 * Yg := by positivity
  have hYlt : γ6 * Yg < Yg := by nlinarith
  have hcop : γ6 * Xg * Yg = γ6 * Yg * Xg := by ring
  have hchord : 0 < κ * ((0 - Yg) * (((1 - β6 - γ6) * κ + γ6 * zg) - zg) -
      (κ - zg) * (γ6 * Yg - Yg)) := by
    have : κ * ((0 - Yg) * (((1 - β6 - γ6) * κ + γ6 * zg) - zg) - (κ - zg) * (γ6 * Yg - Yg)) =
        β6 * κ ^ 2 * Yg := by ring
    rw [this]; have : 0 < κ ^ 2 := by positivity
    positivity
  have hpz : 0 < κ * ((zf + β1 * κ) - zf) := by
    have : κ * ((zf + β1 * κ) - zf) = β1 * κ ^ 2 := by ring
    rw [this]; have : 0 < κ ^ 2 := by positivity
    positivity
  -- the view `κv e3` with `κv = |κ|`
  have key : ∀ κv : ℝ, 0 < κv → (κv • e3 = b - d ∨ κv • e3 = d - b) →
      IsRupert ({b, fpt e1 e2 e3 b 0 0 κ, fpt e1 e2 e3 b L 0 zf,
        fpt e1 e2 e3 b (α4 * L + γ4 * Xg) (γ4 * Yg) (α4 * (zf + β1 * κ) + γ4 * zg + (1 - α4 - γ4) * κ),
        fpt e1 e2 e3 b Xg Yg zg, fpt e1 e2 e3 b L 0 (zf + β1 * κ),
        fpt e1 e2 e3 b (γ6 * Xg) (γ6 * Yg) ((1 - β6 - γ6) * κ + γ6 * zg)} : Finset ℝ³) := by
    intro κv hκv hv
    obtain ⟨hc1, hc2⟩ := qg_rim_ccw hF b hκv hL hYr hYg hcr hcg (κ := κ) (zf := zf)
      (zr := α4 * (zf + β1 * κ) + γ4 * zg + (1 - α4 - γ4) * κ) (zg := zg)
    have hz : IsRobustUnimodal (fun i => ⟪Qg e1 e2 e3 b κ L zf (α4 * L + γ4 * Xg) (γ4 * Yg)
        (α4 * (zf + β1 * κ) + γ4 * zg + (1 - α4 - γ4) * κ) Xg Yg zg i, κv • e3⟫) := by
      simp only [hQ]
      rcases hv with hv | hv
      · rw [hv]; exact hrob
      · rw [hv]
        have := hrob.neg
        convert this using 2 with i
        rw [← inner_neg_right, neg_sub]
    have hbad : NoPersistHDN (Qg e1 e2 e3 b κ L zf (α4 * L + γ4 * Xg) (γ4 * Yg)
        (α4 * (zf + β1 * κ) + γ4 * zg + (1 - α4 - γ4) * κ) Xg Yg zg) (κv • e3) (L • e1) := by
      have hfun : Qg e1 e2 e3 b κ L zf (α4 * L + γ4 * Xg) (γ4 * Yg)
          (α4 * (zf + β1 * κ) + γ4 * zg + (1 - α4 - γ4) * κ) Xg Yg zg = quad d c' b' c := funext hQ
      have h0 : NoHDNRim (quad d c' b' c) (b - d) := hnd.rim (quad d c' b' c) (fun i => by
        rcases zmod4_cases i with rfl | rfl | rfl | rfl <;> simp [quad])
      have h1 : NoHDNRim (quad d c' b' c) (κv • e3) := by
        rcases hv with hv | hv
        · rw [hv]; exact h0
        · rw [hv, ← neg_sub]; exact h0.neg
      rw [hfun]
      rw [← hfun]
      have he3 : e3 ≠ 0 := by
        intro h; have := hF.n33; rw [h] at this; simp at this
      refine noPersist_of_noHDNRim (by norm_num : 3 ≤ 4) _ (L • e1) (smul_ne_zero hκv.ne' he3) ?_
        (by rw [hfun]; exact h1)
      intro i j hi hj
      exact hc1 i j hi hj
    exact close_end_frame hF b hκ hκv hL hYr hYg hcr hcg hYq hYlt hcop hchord hpz hz hbad
  have fin : IsRupert ({b, fpt e1 e2 e3 b 0 0 κ, fpt e1 e2 e3 b L 0 zf,
        fpt e1 e2 e3 b (α4 * L + γ4 * Xg) (γ4 * Yg) (α4 * (zf + β1 * κ) + γ4 * zg + (1 - α4 - γ4) * κ),
        fpt e1 e2 e3 b Xg Yg zg, fpt e1 e2 e3 b L 0 (zf + β1 * κ),
        fpt e1 e2 e3 b (γ6 * Xg) (γ6 * Yg) ((1 - β6 - γ6) * κ + γ6 * zg)} : Finset ℝ³) := by
    rcases lt_or_gt_of_ne hκ with hn | hp
    · exact key (-κ) (by linarith) (Or.inl (by rw [neg_smul, ← hxe]; abel))
    · exact key κ hp (Or.inr hxe.symm)
  rw [← pD, ← pC', ← pB, ← pC, ← pA, ← pA'] at fin
  convert fin using 1
  ext y
  simp only [mem_insert, mem_singleton]
  tauto

end Type08Sp
end Minimality

#print axioms Minimality.Type08Sp.close_Tp_R3_hdn
