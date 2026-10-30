module

public import Minimality.Type08S.P2TBt1

@[expose] public section

set_option relaxedAutoImplicit true
/-!
# pkP / B / Bt2: `noPersist_sigma_of_quad`.
-/

set_option autoImplicit true
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

variable {e1 e2 e3 : ℝ³}

/-- In the `K_2` frame at `T`: the rim `σ` of the quadrilateral `(d, c', b', c)` is a rotation or reflection of it,
so `NoPersistHDN` for the whole quadrilateral gives it for the rim. -/
theorem noPersist_core {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) (hT : IsT a' b c d)
    (hF : Fr e1 e2 e3) {κ κv : ℝ} (hκ : κ ≠ 0) (hκv : κv = κ ∨ κv = -κ) (hxe : d - b = κ • e3)
    (hf2 : ⟪c' - b, e2⟫ = 0) (hL : 0 < ⟪c' - b, e1⟫) (hr : 0 < ⟪b' - b, e2⟫)
    {k' : ℕ} [NeZero k'] (hk3 : 3 ≤ k') (σ : ZMod k' → ZMod 4) (u e : ℝ³)
    (hu : u = κv • e3) (he : e = ⟪c' - b, e1⟫ • e1)
    (hcyc : ∀ i j : ZMod k', j ≠ i → j ≠ i + 1 → 0 < det3 (quad d c' b' c (σ (i + 1)) - quad d c' b' c (σ i))
      (quad d c' b' c (σ j) - quad d c' b' c (σ i)) u)
    (hleft : ∀ (i : ZMod k') (a_ : ZMod 4), 0 ≤ det3 (quad d c' b' c (σ (i + 1)) - quad d c' b' c (σ i))
      (quad d c' b' c a_ - quad d c' b' c (σ i)) u)
    (hq : NoPersistHDN (quad d c' b' c) u e) :
    NoPersistHDN (fun i => quad d c' b' c (σ i)) u e := by
  obtain ⟨hcr, hcg, hXd0, hXdL, hlam⟩ := pic_K2T N hT hF hκ hxe hf2 hL hr
  obtain ⟨hYg, hYp, hDp, hYq, hcop, hchord⟩ := extra_K2T N hT hF hκ hxe hf2 hL hr hcg hlam
  have hκv0 : κv ≠ 0 := by rcases hκv with h | h <;> rw [h] <;> simp [hκ]
  have hxx : d = fpt e1 e2 e3 b 0 0 κ := by
    rw [fpt, ← pc_smul_e3 hF, ← hxe]; abel
  have hxf : c' = fpt e1 e2 e3 b ⟪c' - b, e1⟫ 0 ⟪c' - b, e3⟫ := by
    have := pc_coords hF b c'; rw [hf2] at this; exact this
  have hxr : b' = fpt e1 e2 e3 b ⟪b' - b, e1⟫ ⟪b' - b, e2⟫ ⟪b' - b, e3⟫ := pc_coords hF b b'
  have hxg : c = fpt e1 e2 e3 b ⟪c - b, e1⟫ ⟪c - b, e2⟫ ⟪c - b, e3⟫ := pc_coords hF b c
  have hP : ∀ j, quad d c' b' c j = Qg e1 e2 e3 b κ ⟪c' - b, e1⟫ ⟪c' - b, e3⟫ ⟪b' - b, e1⟫ ⟪b' - b, e2⟫
      ⟪b' - b, e3⟫ ⟪c - b, e1⟫ ⟪c - b, e2⟫ ⟪c - b, e3⟫ j := by
    intro j
    simp only [Qg]
    rw [← hxx, ← hxf, ← hxr, ← hxg]
  have hcyc' := hcyc
  have hleft' := hleft
  simp only [hP, hu] at hcyc' hleft'
  have hk4 := rim_k_eq_4 hF hκv0 hL hr hYg hcr hcg hk3 σ hcyc' hleft'
  subst hk4
  obtain ⟨hpos, hneg⟩ := rim_orient4 hF hκv0 hL hr hYg hcr hcg σ hcyc' hleft'
  rcases lt_or_gt_of_ne hκv0 with hn | hp
  · obtain ⟨c0, hc⟩ := hneg hn
    have := noPersist_to_reflect c0 hq
    convert this using 2 with i
    rw [hc i]
  · obtain ⟨c0, hc⟩ := hpos hp
    have := noPersist_to_shift c0 hq
    convert this using 2 with i
    rw [hc i]

end Type08Sp
end Minimality
