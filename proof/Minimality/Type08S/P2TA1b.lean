module

public import Minimality.Type08S.P2TA1a

@[expose] public section

set_option relaxedAutoImplicit true
/-!
# pkP / A1b: `np_KbT` and `close_hdn_np_KbT` (`K_b` at `T`, non-persistent HDN).
-/

set_option autoImplicit true
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

variable {e1 e2 e3 : ℝ³}

/-- `hpm` for `a'` at `T`: `a'` over the far end `f` of the segment `[x, f]`, with `κ (z_{a'} - z_f) > 0`; the
slide `u_t = κv e3 + t (κ κv) e1` brings `a'` into the open side from `f`. -/
theorem hpm_T (hF : Fr e1 e2 e3) (O : ℝ³) {κ κv L zf zp : ℝ} (hκ : κ ≠ 0) (hκv : κv ≠ 0)
    (hL : 0 < L) (hm : 0 < κ * (zp - zf)) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
      fpt e1 e2 e3 O L 0 zp = fpt e1 e2 e3 O 0 0 κ +
        s • (fpt e1 e2 e3 O L 0 zf - fpt e1 e2 e3 O 0 0 κ) + δ • (κv • e3 + t • ((κ * κv) • e1)) := by
  have h1 : ∀ᶠ t in 𝓝 (0 : ℝ), t * κ * (zp - κ) < L :=
    (show Continuous fun t : ℝ => t * κ * (zp - κ) by fun_prop).continuousAt.eventually_lt
      continuousAt_const (by simpa using hL)
  have h2 : ∀ᶠ t in 𝓝 (0 : ℝ), t * κ * (zf - κ) < L :=
    (show Continuous fun t : ℝ => t * κ * (zf - κ) by fun_prop).continuousAt.eventually_lt
      continuousAt_const (by simpa using hL)
  filter_upwards [nhdsWithin_le_nhds (h1.and h2), self_mem_nhdsWithin] with t ⟨ht1, ht2⟩ ht0
  have ht : 0 < t := ht0
  have hD : 0 < L - t * κ * (zf - κ) := by linarith
  have hr0 : 0 < t * κ * (zp - zf) / (L - t * κ * (zf - κ)) :=
    div_pos (by nlinarith [mul_pos ht hm]) hD
  have hr1 : t * κ * (zp - zf) / (L - t * κ * (zf - κ)) < 1 := by
    rw [div_lt_one hD]; nlinarith
  have hDne : L - t * κ * (zf - κ) ≠ 0 := hD.ne'
  refine ⟨1 - t * κ * (zp - zf) / (L - t * κ * (zf - κ)),
    L * (zp - zf) / ((L - t * κ * (zf - κ)) * κv), by linarith, by linarith, ?_, ?_⟩
  · have : zp - zf ≠ 0 := by rintro h; rw [h] at hm; simp at hm
    exact div_ne_zero (mul_ne_zero hL.ne' this) (mul_ne_zero hD.ne' hκv)
  · have E1 : L = (1 - t * κ * (zp - zf) / (L - t * κ * (zf - κ))) * L +
        L * (zp - zf) / ((L - t * κ * (zf - κ)) * κv) * (t * (κ * κv)) := by
      field_simp; ring
    have E3 : zp = κ + (1 - t * κ * (zp - zf) / (L - t * κ * (zf - κ))) * (zf - κ) +
        L * (zp - zf) / ((L - t * κ * (zf - κ)) * κv) * κv := by
      generalize hDg : L - t * κ * (zf - κ) = D at hDne ⊢
      field_simp
      rw [← hDg]; ring
    simp only [fpt, pc]
    linear_combination (norm := module) E1 • e1 + E3 • e3

set_option maxHeartbeats 4000000 in
theorem np_KbT {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) (hT : IsT a' b c d)
    (hF : Fr e1 e2 e3) {κ κv : ℝ} (hκ : κ ≠ 0) (hκv : κv = κ ∨ κv = -κ) (hxe : b - d = κ • e3)
    (hf2 : ⟪c - d, e2⟫ = 0) (hL : 0 < ⟪c - d, e1⟫) (hr : 0 < ⟪b' - d, e2⟫)
    {k' : ℕ} [NeZero k'] (hk3 : 3 ≤ k') (σ : ZMod k' → ZMod 4) (u e : ℝ³)
    (hu : u = κv • e3) (he : e = ⟪c - d, e1⟫ • e1)
    (hcyc : ∀ i j : ZMod k', j ≠ i → j ≠ i + 1 → 0 < det3 (quad b c' b' c (σ (i + 1)) - quad b c' b' c (σ i))
      (quad b c' b' c (σ j) - quad b c' b' c (σ i)) u)
    (hleft : ∀ (i : ZMod k') (a_ : ZMod 4), 0 ≤ det3 (quad b c' b' c (σ (i + 1)) - quad b c' b' c (σ i))
      (quad b c' b' c a_ - quad b c' b' c (σ i)) u)
    (hz : IsRobustUnimodal (fun i => ⟪quad b c' b' c (σ i), u⟫))
    (hbad : NoPersistHDN (fun i => quad b c' b' c (σ i)) u e) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  obtain ⟨hcr, hcg, hXp, hYp', hDp', hlam⟩ := pic_KbT N hT hF hκ hxe hf2 hL hr
  obtain ⟨hYg, hYp, -, hYq, hYlt, hcop, hchord⟩ := extra_KbT N hT hF hκ hxe hf2 hL hr hcg hlam
  have hκv0 : κv ≠ 0 := by rcases hκv with h | h <;> rw [h] <;> simp [hκ]
  have hxx : b = fpt e1 e2 e3 d 0 0 κ := by
    rw [fpt, ← pc_smul_e3 hF, ← hxe]; abel
  have hxf : c = fpt e1 e2 e3 d ⟪c - d, e1⟫ 0 ⟪c - d, e3⟫ := by
    have := pc_coords hF d c; rw [hf2] at this; exact this
  have hxr : b' = fpt e1 e2 e3 d ⟪b' - d, e1⟫ ⟪b' - d, e2⟫ ⟪b' - d, e3⟫ := pc_coords hF d b'
  have hxg : c' = fpt e1 e2 e3 d ⟪c' - d, e1⟫ ⟪c' - d, e2⟫ ⟪c' - d, e3⟫ := pc_coords hF d c'
  have hxp : a' = fpt e1 e2 e3 d ⟪a' - d, e1⟫ 0 ⟪a' - d, e3⟫ := by
    have := pc_coords hF d a'; rw [hYp] at this; exact this
  have hxw : a = fpt e1 e2 e3 d ⟪a - d, e1⟫ ⟪a - d, e2⟫ ⟪a - d, e3⟫ := pc_coords hF d a
  have n1 : -(1 : ZMod 4) = 3 := by decide
  have n2 : -(2 : ZMod 4) = 2 := by decide
  have n3 : -(3 : ZMod 4) = 1 := by decide
  have hP : ∀ j, quad b c' b' c j = Qg e1 e2 e3 d κ ⟪c - d, e1⟫ ⟪c - d, e3⟫ ⟪b' - d, e1⟫ ⟪b' - d, e2⟫
      ⟪b' - d, e3⟫ ⟪c' - d, e1⟫ ⟪c' - d, e2⟫ ⟪c' - d, e3⟫ (-j) := by
    intro j
    rcases zmod4_cases j with rfl | rfl | rfl | rfl <;>
      simp only [Qg, n1, n2, n3, neg_zero, quad, Matrix.cons_val, ← hxx, ← hxf, ← hxr, ← hxg]
  have hw := rows_T4 hF d (κ := κ) (κv := κv) (L := ⟪c - d, e1⟫) (zf := ⟪c - d, e3⟫)
    (Xr := ⟪b' - d, e1⟫) (Yr := ⟪b' - d, e2⟫) (zr := ⟪b' - d, e3⟫) (Xg := ⟪c' - d, e1⟫)
    (Yg := ⟪c' - d, e2⟫) (zg := ⟪c' - d, e3⟫) (Xq := ⟪a - d, e1⟫) (Yq := ⟪a - d, e2⟫)
    (zq := ⟪a - d, e3⟫) hκ hκv0 hL hr hYg hcr hcg hYq hYlt hcop hchord
  have hxp' : a' = fpt e1 e2 e3 d ⟪c - d, e1⟫ 0 ⟪a' - d, e3⟫ := by rw [← hXp]; exact hxp
  have hpx : fpt e1 e2 e3 d ⟪c - d, e1⟫ 0 ⟪a' - d, e3⟫ ≠ fpt e1 e2 e3 d 0 0 κ := by
    intro h
    have := congrArg (fun p => ⟪p - d, e1⟫) h
    simp only [fpt, add_sub_cancel_left, inner_pc_e1 hF] at this
    exact hL.ne this.symm
  have hpf : fpt e1 e2 e3 d ⟪c - d, e1⟫ 0 ⟪a' - d, e3⟫ ≠ fpt e1 e2 e3 d ⟪c - d, e1⟫ 0 ⟪c - d, e3⟫ := by
    intro h
    have := congrArg (fun p => ⟪p - d, e3⟫) h
    simp only [fpt, add_sub_cancel_left, inner_pc_e3 hF] at this
    rw [this, sub_self, mul_zero] at hDp'
    exact lt_irrefl _ hDp'
  have key := close_np_frame_g hF d (fpt e1 e2 e3 d ⟪a - d, e1⟫ ⟪a - d, e2⟫ ⟪a - d, e3⟫) hκ hκv0 hL hr
    hYg hcr hcg hpx hpf (hpm_T hF d hκ hκv0 hL hDp') hw (quad b c' b' c) (fun j => -j) (fun x => neg_neg x) hP hk3 σ u e hu
    (by rw [he]) hcyc hleft hz hbad
  rw [← hxp'] at key
  rw [← hxx, ← hxf, ← hxr, ← hxg, ← hxw] at key
  convert key using 1
  ext y
  simp only [mem_insert, mem_singleton]
  tauto


end Type08Sp
end Minimality
