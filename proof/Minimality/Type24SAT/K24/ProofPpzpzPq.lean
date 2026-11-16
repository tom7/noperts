module

public import Minimality.Type24SAT.K24.LratPpzpzPq

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Minimality.SAT.Checker
namespace Minimality.H24.SAT.Lrat
def PpzpzPqC0 : List Step := PpzpzPqS0 ++ PpzpzPqS1 ++ PpzpzPqS2 ++ PpzpzPqS3
def PpzpzPqC1 : List Step := PpzpzPqS4
theorem PpzpzPqok0 : chkChunk 15 PpzpzPqCnf ([]) PpzpzPqC0 = true := by decide +kernel
theorem PpzpzPqok1 : chkChunk 15 PpzpzPqCnf (PpzpzPqC0) PpzpzPqC1 = true := by decide +kernel
theorem PpzpzPqfinal : OKs 15 PpzpzPqCnf [] [PpzpzPqC0,PpzpzPqC1] :=
  ⟨PpzpzPqok0, ⟨PpzpzPqok1, trivial⟩⟩
theorem PpzpzPqempty : [PpzpzPqC0,PpzpzPqC1].flatten.any (fun s => s.2.1.isEmpty) = true := by decide +kernel
theorem PpzpzPqunsat : ∀ ρ : Nat → Bool, ¬ ∀ c ∈ PpzpzPqCnf, SatCl ρ c := chunks_sound 15 PpzpzPqCnf _ PpzpzPqfinal PpzpzPqempty
end Minimality.H24.SAT.Lrat
