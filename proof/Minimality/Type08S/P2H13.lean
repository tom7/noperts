module

public import Minimality.Type08S.P2H10

@[expose] public section

set_option relaxedAutoImplicit true

/-!
# pkH H13: on `Norm08` the parallel set is empty (strict Lemma E), so the SC2 hypothesis is chord end at `f` only

* `lemE_strict`: the three Lemma-E products are strictly negative on every `Norm08` shape.
* `par_false`: in the frame, `Par5` (top side on the chord's line) forces `x ∈ Π'`, i.e. a zero product.
* `close_hdn_pers'`: `close_hdn_pers` with the SC2 hypotheses restricted to `CEf5` (chord end at `f`).
-/

set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

variable {e1 e2 e3 : ℝ³}

def LemE3s (xp x f r g : ℝ³) : Prop :=
  det3 (r - f) (g - f) (x - f) * det3 (r - f) (g - f) (xp - f) < 0

set_option maxHeartbeats 1000000 in
theorem lemE_strict {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) :
    LemE3s a' c b c' b' ∧ LemE3s d b c b' c' ∧ LemE3s b d c' b' c := by
  obtain ⟨o, E₁, E₂, E₃, θ, hE, hθ, hpts⟩ := exists_nf08 N
  have hS : ∀ i, pts08 a a' b b' c c' d i = nfShape08 o E₁ E₂ E₃ θ i := fun i => by rw [hpts]
  have ha' : a' = nfShape08 o E₁ E₂ E₃ θ 1 := by simpa [pts08] using hS 1
  have hb : b = nfShape08 o E₁ E₂ E₃ θ 2 := by simpa [pts08] using hS 2
  have hb' : b' = nfShape08 o E₁ E₂ E₃ θ 3 := by simpa [pts08] using hS 3
  have hc : c = nfShape08 o E₁ E₂ E₃ θ 4 := by simpa [pts08] using hS 4
  have hc' : c' = nfShape08 o E₁ E₂ E₃ θ 5 := by simpa [pts08] using hS 5
  have hd : d = nfShape08 o E₁ E₂ E₃ θ 6 := by simpa [pts08] using hS 6
  obtain ⟨p0, p1, p2, p3, p4, p5, e1', e2', e3', ga, gb, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12⟩ :=
    common08 θ hθ
  have hD2 : 0 < det3 E₁ E₂ E₃ * det3 E₁ E₂ E₃ := mul_self_pos.mpr hE
  unfold LemE3s
  rw [ha', hb, hb', hc, hc', hd]
  refine ⟨?_, ?_, ?_⟩
  · rw [det3_nfd, det3_nfd]
    simp only [ddet, cp08, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
      Matrix.head_cons]
    have k : 0 < (-(θ 0) + (θ 0) * (θ 3) - (θ 1) * (θ 2) + (θ 2)) *
        (-(θ 0) * (θ 3) + (θ 0) * (θ 3) * (θ 4) + (θ 0) * (θ 5) + (θ 1) * (θ 2) * (θ 5) - (θ 2) * (θ 5)) :=
      mul_pos ga (by linarith)
    nlinarith [mul_pos hD2 k]
  · rw [det3_nfd, det3_nfd]
    simp only [ddet, cp08, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
      Matrix.head_cons]
    have k : 0 < (-(θ 0) + (θ 0) * (θ 3) - (θ 1) * (θ 2) + (θ 2)) * (θ 1 * θ 2) :=
      mul_pos ga (mul_pos p1 p2)
    nlinarith [mul_pos hD2 k]
  · rw [det3_nfd, det3_nfd]
    simp only [ddet, cp08, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
      Matrix.head_cons]
    have k : 0 < (-(θ 0) + (θ 0) * (θ 3) - (θ 1) * (θ 2) + (θ 2)) * (θ 1 * θ 2) :=
      mul_pos ga (mul_pos p1 p2)
    nlinarith [mul_pos hD2 k]

/-- The parallel set contradicts strict Lemma E (`x` would lie on `Π'`). -/
theorem par_false (hF : Fr e1 e2 e3) (O : ℝ³) {κ L zf Xr Yr zr Xg Yg zg : ℝ}
    (h : LemE3s O (O + pc e1 e2 e3 0 0 κ) (O + pc e1 e2 e3 L 0 zf) (O + pc e1 e2 e3 Xr Yr zr)
      (O + pc e1 e2 e3 Xg Yg zg))
    (hp : Par5 L κ zf Xr Yr zr Xg Yg zg) : False := by
  obtain ⟨hY, ⟨h1, h2⟩, -⟩ := hp
  unfold LemE3s at h
  have hOd : O - (O + pc e1 e2 e3 L 0 zf) = pc e1 e2 e3 (0 - L) (0 - 0) (0 - zf) := by
    simp only [pc]; module
  rw [hOd] at h
  simp only [add_sub_add_left_eq_sub, pc_sub, det3_pc hF] at h
  subst hY
  have hDx : (Xr - Xg) * (κ - zf) + L * (zr - zg) = 0 := by linear_combination h1 - h2
  have key : Yr ^ 2 * (((Xr - Xg) * (κ - zf) + L * (zr - zg)) * ((Xr - Xg) * (0 - zf) + L * (zr - zg))) < 0 := by
    convert h using 1; ring
  rw [hDx] at key; simp at key

/-- SC2 of N2 `K_c` reduced to the chord end at `f`. -/
theorem SC2N2_of_CEf {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d)
    (h : ∀ (e1 e2 e3 : ℝ³) (κ : ℝ), Fr e1 e2 e3 → κ ≠ 0 → c - a' = κ • e3 → ⟪b - a', e2⟫ = 0 →
      0 < ⟪b - a', e1⟫ → 0 < ⟪c' - a', e2⟫ → Rob4 κ ⟪b - a', e3⟫ ⟪c' - a', e3⟫ ⟪b' - a', e3⟫ →
      CEf5 ⟪b - a', e1⟫ κ ⟪b - a', e3⟫ ⟪c' - a', e1⟫ ⟪c' - a', e2⟫ ⟪c' - a', e3⟫ ⟪b' - a', e1⟫ ⟪b' - a', e2⟫
        ⟪b' - a', e3⟫ → IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³))) :
    SC2N2 a a' b b' c c' d := by
  intro e1 e2 e3 κ hF hκ hce hb2 hL hr hrob hcase
  rcases hcase with hf | hpar
  · exact h e1 e2 e3 κ hF hκ hce hb2 hL hr hrob hf
  · exfalso
    have hxx : c = a' + pc e1 e2 e3 0 0 κ := by rw [← pc_smul_e3 hF, ← hce]; abel
    have hxf : b = a' + pc e1 e2 e3 ⟪b - a', e1⟫ 0 ⟪b - a', e3⟫ := by
      have := pc_coords hF a' b; rw [hb2] at this; exact this
    have hxr : c' = a' + pc e1 e2 e3 ⟪c' - a', e1⟫ ⟪c' - a', e2⟫ ⟪c' - a', e3⟫ := pc_coords hF a' c'
    have hxg : b' = a' + pc e1 e2 e3 ⟪b' - a', e1⟫ ⟪b' - a', e2⟫ ⟪b' - a', e3⟫ := pc_coords hF a' b'
    refine par_false hF a' ?_ hpar
    rw [← hxx, ← hxf, ← hxr, ← hxg]; exact (lemE_strict N).1

/-- SC2 of T4 `K_b` reduced to the chord end at `f`. -/
theorem SC2Kb_of_CEf {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d)
    (h : ∀ (e1 e2 e3 : ℝ³) (κ : ℝ), Fr e1 e2 e3 → κ ≠ 0 → b - d = κ • e3 → ⟪c - d, e2⟫ = 0 →
      0 < ⟪c - d, e1⟫ → 0 < ⟪b' - d, e2⟫ → Rob4 κ ⟪c - d, e3⟫ ⟪b' - d, e3⟫ ⟪c' - d, e3⟫ →
      CEf5 ⟪c - d, e1⟫ κ ⟪c - d, e3⟫ ⟪b' - d, e1⟫ ⟪b' - d, e2⟫ ⟪b' - d, e3⟫ ⟪c' - d, e1⟫ ⟪c' - d, e2⟫
        ⟪c' - d, e3⟫ → IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³))) :
    SC2Kb a a' b b' c c' d := by
  intro e1 e2 e3 κ hF hκ hce hb2 hL hr hrob hcase
  rcases hcase with hf | hpar
  · exact h e1 e2 e3 κ hF hκ hce hb2 hL hr hrob hf
  · exfalso
    have hxx : b = d + pc e1 e2 e3 0 0 κ := by rw [← pc_smul_e3 hF, ← hce]; abel
    have hxf : c = d + pc e1 e2 e3 ⟪c - d, e1⟫ 0 ⟪c - d, e3⟫ := by
      have := pc_coords hF d c; rw [hb2] at this; exact this
    have hxr : b' = d + pc e1 e2 e3 ⟪b' - d, e1⟫ ⟪b' - d, e2⟫ ⟪b' - d, e3⟫ := pc_coords hF d b'
    have hxg : c' = d + pc e1 e2 e3 ⟪c' - d, e1⟫ ⟪c' - d, e2⟫ ⟪c' - d, e3⟫ := pc_coords hF d c'
    refine par_false hF d ?_ hpar
    rw [← hxx, ← hxf, ← hxr, ← hxg]; exact (lemE_strict N).2.1

/-- SC2 of T4 `K_2` reduced to the chord end at `f`. -/
theorem SC2K2_of_CEf {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d)
    (h : ∀ (e1 e2 e3 : ℝ³) (κ : ℝ), Fr e1 e2 e3 → κ ≠ 0 → d - b = κ • e3 → ⟪c' - b, e2⟫ = 0 →
      0 < ⟪c' - b, e1⟫ → 0 < ⟪b' - b, e2⟫ → Rob4 κ ⟪c' - b, e3⟫ ⟪b' - b, e3⟫ ⟪c - b, e3⟫ →
      CEf5 ⟪c' - b, e1⟫ κ ⟪c' - b, e3⟫ ⟪b' - b, e1⟫ ⟪b' - b, e2⟫ ⟪b' - b, e3⟫ ⟪c - b, e1⟫ ⟪c - b, e2⟫
        ⟪c - b, e3⟫ → IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³))) :
    SC2K2 a a' b b' c c' d := by
  intro e1 e2 e3 κ hF hκ hce hb2 hL hr hrob hcase
  rcases hcase with hf | hpar
  · exact h e1 e2 e3 κ hF hκ hce hb2 hL hr hrob hf
  · exfalso
    have hxx : d = b + pc e1 e2 e3 0 0 κ := by rw [← pc_smul_e3 hF, ← hce]; abel
    have hxf : c' = b + pc e1 e2 e3 ⟪c' - b, e1⟫ 0 ⟪c' - b, e3⟫ := by
      have := pc_coords hF b c'; rw [hb2] at this; exact this
    have hxr : b' = b + pc e1 e2 e3 ⟪b' - b, e1⟫ ⟪b' - b, e2⟫ ⟪b' - b, e3⟫ := pc_coords hF b b'
    have hxg : c = b + pc e1 e2 e3 ⟪c - b, e1⟫ ⟪c - b, e2⟫ ⟪c - b, e3⟫ := pc_coords hF b c
    refine par_false hF b ?_ hpar
    rw [← hxx, ← hxf, ← hxr, ← hxg]; exact (lemE_strict N).2.2

end Type08Sp
end Minimality
