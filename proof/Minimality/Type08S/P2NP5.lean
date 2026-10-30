module

public import Minimality.Type08S.P2NP4

@[expose] public section

set_option relaxedAutoImplicit true

/-!
# P3a, N2 `K_c`: `np_N2` — the slide closes the robust rim `(c, b, c', b')` when its HDNs do not persist.
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

theorem np_N2 {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) (hreg : RegN2 N.F)
    (hF : Fr e1 e2 e3) {κ κv : ℝ} (hκ : κ ≠ 0) (hκv : κv = κ ∨ κv = -κ) (hce : c - a' = κ • e3)
    (hb2 : ⟪b - a', e2⟫ = 0) (hL : 0 < ⟪b - a', e1⟫) (hr : 0 < ⟪c' - a', e2⟫)
    {k' : ℕ} [NeZero k'] (hk3 : 3 ≤ k') (σ : ZMod k' → ZMod 4) (u e : ℝ³)
    (hu : u = κv • e3) (he : e = ⟪b - a', e1⟫ • e1)
    (hcyc : ∀ i j : ZMod k', j ≠ i → j ≠ i + 1 → 0 < det3 (quad c b c' b' (σ (i + 1)) - quad c b c' b' (σ i))
      (quad c b c' b' (σ j) - quad c b c' b' (σ i)) u)
    (hleft : ∀ (i : ZMod k') (a_ : ZMod 4), 0 ≤ det3 (quad c b c' b' (σ (i + 1)) - quad c b c' b' (σ i))
      (quad c b c' b' a_ - quad c b c' b' (σ i)) u)
    (hz : IsRobustUnimodal (fun i => ⟪quad c b c' b' (σ i), u⟫))
    (hbad : NoPersistHDN (fun i => quad c b c' b' (σ i)) u e) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  obtain ⟨hcr, hcg, hXd0, hXdL, hYa, hfr, hrg, hgx⟩ := pic_N2 N hreg hF hκ hce hb2 hL hr
  obtain ⟨hYg, hYd, hDp⟩ := extra_N2 N hreg hF hκ hce hb2 hL hr
  have hκv0 : κv ≠ 0 := by rcases hκv with h | h <;> rw [h] <;> simp [hκ]
  have hxx : c = fpt e1 e2 e3 a' 0 0 κ := by
    rw [fpt, ← pc_smul_e3 hF, ← hce]; abel
  have hxf : b = fpt e1 e2 e3 a' ⟪b - a', e1⟫ 0 ⟪b - a', e3⟫ := by
    have := pc_coords hF a' b; rw [hb2] at this; exact this
  have hxr : c' = fpt e1 e2 e3 a' ⟪c' - a', e1⟫ ⟪c' - a', e2⟫ ⟪c' - a', e3⟫ := pc_coords hF a' c'
  have hxg : b' = fpt e1 e2 e3 a' ⟪b' - a', e1⟫ ⟪b' - a', e2⟫ ⟪b' - a', e3⟫ := pc_coords hF a' b'
  have hxp : d = fpt e1 e2 e3 a' ⟪d - a', e1⟫ 0 ⟪d - a', e3⟫ := by
    have := pc_coords hF a' d; rw [hYd] at this; exact this
  have hxw : a = fpt e1 e2 e3 a' ⟪a - a', e1⟫ ⟪a - a', e2⟫ ⟪a - a', e3⟫ := pc_coords hF a' a
  have hP : ∀ j, quad c b c' b' j = Qg e1 e2 e3 a' κ ⟪b - a', e1⟫ ⟪b - a', e3⟫ ⟪c' - a', e1⟫ ⟪c' - a', e2⟫
      ⟪c' - a', e3⟫ ⟪b' - a', e1⟫ ⟪b' - a', e2⟫ ⟪b' - a', e3⟫ (id j) := by
    intro j
    simp only [Qg, id]
    rw [← hxx, ← hxf, ← hxr, ← hxg]
  have hw := rows_N2 hF a' (κ := κ) (κv := κv) (L := ⟪b - a', e1⟫) (zf := ⟪b - a', e3⟫)
    (Xr := ⟪c' - a', e1⟫) (Yr := ⟪c' - a', e2⟫) (zr := ⟪c' - a', e3⟫) (Xg := ⟪b' - a', e1⟫)
    (Yg := ⟪b' - a', e2⟫) (zg := ⟪b' - a', e3⟫) (Xa := ⟪a - a', e1⟫) (Ya := ⟪a - a', e2⟫)
    (za := ⟪a - a', e3⟫) hκv0 hL hYa hfr hrg hgx (κ * κv)
  have key := close_np_frame hF a' (fpt e1 e2 e3 a' ⟪a - a', e1⟫ ⟪a - a', e2⟫ ⟪a - a', e3⟫) hκ hκv0 hL hr
    hYg hcr hcg hXd0 hXdL hDp hw (quad c b c' b') id (fun _ => rfl) hP hk3 σ u e hu
    (by rw [he]) hcyc hleft hz hbad
  rw [← hxx, ← hxf, ← hxr, ← hxg, ← hxp, ← hxw] at key
  convert key using 1
  ext y
  simp only [mem_insert, mem_singleton]
  tauto

end Type08Sp
end Minimality

#print axioms Minimality.Type08Sp.np_N2
