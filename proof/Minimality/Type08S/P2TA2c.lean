module

public import Minimality.Type08S.P2TA2b

@[expose] public section

set_option relaxedAutoImplicit true
/-!
# pkP / A2c: `cef_KbT` (copy of `cef_Kb` at `T`).
-/

set_option autoImplicit true
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

variable {e1 e2 e3 : ℝ³}

set_option maxHeartbeats 4000000 in
theorem cef_KbT {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) (hT : IsT a' b c d) :
    CEfKb a a' b b' c c' d := by
  intro e1 e2 e3 κ hF hκ hxe hf2 hL hr hrob hce5
  have hnd := N.F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨haa', hab, hab', hac, hac'⟩, ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩,
    ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd
  obtain ⟨hcr, hcg, hXp, hYp', hDp', hlam⟩ := pic_KbT N hT hF hκ hxe hf2 hL hr
  obtain ⟨hYg, hYp, -, hYq, hYlt, hcop, hchord⟩ := extra_KbT N hT hF hκ hxe hf2 hL hr hcg hlam
  have hxx : b = d + pc e1 e2 e3 0 0 κ := by
    rw [← pc_smul_e3 hF, ← hxe]; abel
  have hxf : c = d + pc e1 e2 e3 ⟪c - d, e1⟫ 0 ⟪c - d, e3⟫ := by
    have := pc_coords hF d c; rw [hf2] at this; exact this
  have hxr : b' = d + pc e1 e2 e3 ⟪b' - d, e1⟫ ⟪b' - d, e2⟫ ⟪b' - d, e3⟫ := pc_coords hF d b'
  have hxg : c' = d + pc e1 e2 e3 ⟪c' - d, e1⟫ ⟪c' - d, e2⟫ ⟪c' - d, e3⟫ := pc_coords hF d c'
  have hxp : a' = d + pc e1 e2 e3 ⟪a' - d, e1⟫ 0 ⟪a' - d, e3⟫ := by
    have := pc_coords hF d a'; rw [hYp] at this; exact this
  have hxw : a = d + pc e1 e2 e3 ⟪a - d, e1⟫ ⟪a - d, e2⟫ ⟪a - d, e3⟫ := pc_coords hF d a
  set E : Finset ℝ³ := {d + pc e1 e2 e3 ⟪a' - d, e1⟫ 0 ⟪a' - d, e3⟫,
    d + pc e1 e2 e3 ⟪a - d, e1⟫ ⟪a - d, e2⟫ ⟪a - d, e3⟫} with hEdef
  set V5 := rim5 e1 e2 e3 d ⟪c - d, e1⟫ 0 κ ⟪c - d, e3⟫ ⟪b' - d, e1⟫ ⟪b' - d, e2⟫ ⟪b' - d, e3⟫
    ⟪c' - d, e1⟫ ⟪c' - d, e2⟫ ⟪c' - d, e3⟫ E with hV5
  have m1 : d + pc e1 e2 e3 0 0 0 ∈ V5 := by simp [hV5, rim5]
  have m0 : d + pc e1 e2 e3 0 0 κ ∈ V5 := by simp [hV5, rim5]
  have m2 : d + pc e1 e2 e3 ⟪c - d, e1⟫ 0 ⟪c - d, e3⟫ ∈ V5 := by simp [hV5, rim5]
  have m4 : d + pc e1 e2 e3 ⟪c' - d, e1⟫ ⟪c' - d, e2⟫ ⟪c' - d, e3⟫ ∈ V5 := by simp [hV5, rim5]
  have hE : ∀ᶠ s : ℝ in atTop, ∀ y ∈ E, TriCert V5 (pc e1 e2 e3 0 0 1) (pc e1 e2 e3 (κ * s) (-κ) 0) y := by
    filter_upwards [triCert_midG' hF d V5 hL hYg hYq hYlt hcop hchord m4 m0 m2,
      triCert_cornerF (σ := κ) hF d V5 hL hYg m1 m2 m4 (zd := ⟪a' - d, e3⟫) (by nlinarith [hDp'])] with s hs hs' y hy
    rw [hEdef, Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl
    · rw [hXp]; exact hs'
    · exact hs
  have hR := ce_frame hF d E hκ hL hr hYg hcr hcg hE hrob
    (fun hY => lemEs_frame hF d hr hY (by rw [← hxx, ← hxf, ← hxr, ← hxg]; exact (lemE_strict N).2.1)) hce5
  simp only [rim5, hEdef] at hR
  rw [show d + pc e1 e2 e3 0 0 0 = d by simp [pc], ← hxx, ← hxf, ← hxr, ← hxg, ← hxp, ← hxw] at hR
  have hset : insert d ({a, a', b, b', c, c'} : Finset ℝ³) = ({d, b, c, b', c'} : Finset ℝ³) ∪ {a', a} := by
    ext y; simp only [mem_insert, mem_singleton, mem_union]
    constructor
    · rintro (h | h | h | h | h | h | h) <;> subst h <;> simp only [true_or, or_true]
    · rintro ((h | h | h | h | h) | (h | h)) <;> subst h <;> simp only [true_or, or_true]
  rw [hset]; exact hR

end Type08Sp
end Minimality
