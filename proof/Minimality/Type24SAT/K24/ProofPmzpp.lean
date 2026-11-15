module

public import Minimality.Type24SAT.K24.LratPmzpp

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Minimality.SAT.Checker
namespace Minimality.H24.SAT.K24
def PmzppC0 : List Step := PmzppS0 ++ PmzppS1 ++ PmzppS2 ++ PmzppS3
def PmzppC1 : List Step := PmzppS4 ++ PmzppS5 ++ PmzppS6 ++ PmzppS7
def PmzppC2 : List Step := PmzppS8 ++ PmzppS9 ++ PmzppS10
theorem Pmzppok0 : chkChunk 15 PmzppCnf ([]) PmzppC0 = true := by decide +kernel
theorem Pmzppok1 : chkChunk 15 PmzppCnf (PmzppC0) PmzppC1 = true := by decide +kernel
theorem Pmzppok2 : chkChunk 15 PmzppCnf (PmzppC0 ++ PmzppC1) PmzppC2 = true := by decide +kernel
theorem Pmzppfinal : OKs 15 PmzppCnf [] [PmzppC0,PmzppC1,PmzppC2] :=
  ⟨Pmzppok0, ⟨Pmzppok1, ⟨Pmzppok2, trivial⟩⟩⟩
theorem Pmzppempty : [PmzppC0,PmzppC1,PmzppC2].flatten.any (fun s => s.2.1.isEmpty) = true := by decide +kernel
theorem Pmzppunsat : ∀ ρ : Nat → Bool, ¬ ∀ c ∈ PmzppCnf, SatCl ρ c := chunks_sound 15 PmzppCnf _ Pmzppfinal Pmzppempty
end Minimality.H24.SAT.K24
