module

public import Minimality.Type08S.P2I5b
public import Minimality.Type08S.P2I7b
public import Minimality.Type08S.P2TpX

@[expose] public section

set_option relaxedAutoImplicit true

set_option autoImplicit true
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

theorem Tp_other_noHDN {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d)
    (hX : ¬ NoHDNAt ({d, a, b', c} : Finset ℝ³) (b - d)) (hS : ¬ TpHDN2 a b b' c c' d) :
    NoHDNAt ({d, c', b', c} : Finset ℝ³) (b - d) ∧ NoHDNAt ({b, c', b', c} : Finset ℝ³) (b - d) := by
  have hnd := N.F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨haa', hab, hab', hac, hac'⟩, ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩,
    ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd
  obtain ⟨hda, hda', hdb, hdb', hdc, hdc'⟩ := N.hd.ne
  constructor
  · by_contra h
    apply hS
    refine ⟨{d, a, b', c}, {d, c', b', c}, ?_, ?_, ?_, hX, h⟩
    · intro e
      have : c' ∈ ({d, a, b', c} : Finset ℝ³) := by rw [e]; simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with h | h | h | h
      · exact hdc' h.symm
      · exact hac' h.symm
      · exact hb'c' h.symm
      · exact hcc' h.symm
    · simp
    · simp
  · by_contra h
    apply hS
    refine ⟨{d, a, b', c}, {b, c', b', c}, ?_, ?_, ?_, hX, h⟩
    · intro e
      have : c' ∈ ({d, a, b', c} : Finset ℝ³) := by rw [e]; simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with h | h | h | h
      · exact hdc' h.symm
      · exact hac' h.symm
      · exact hb'c' h.symm
      · exact hcc' h.symm
    · simp
    · simp

end Type08Sp
end Minimality
#print axioms Minimality.Type08Sp.Tp_other_noHDN
