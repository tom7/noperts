module

public import Minimality.Type24SAT.K24.LratPpzpp

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Minimality.SAT.Checker
namespace Minimality.H24.SAT.K24
def PpzppC0 : List Step := PpzppS0 ++ PpzppS1 ++ PpzppS2 ++ PpzppS3
def PpzppC1 : List Step := PpzppS4 ++ PpzppS5 ++ PpzppS6 ++ PpzppS7
def PpzppC2 : List Step := PpzppS8 ++ PpzppS9 ++ PpzppS10 ++ PpzppS11
def PpzppC3 : List Step := PpzppS12 ++ PpzppS13 ++ PpzppS14
theorem Ppzppok0 : chkChunk 15 PpzppCnf ([]) PpzppC0 = true := by decide +kernel
theorem Ppzppok1 : chkChunk 15 PpzppCnf (PpzppC0) PpzppC1 = true := by decide +kernel
theorem Ppzppok2 : chkChunk 15 PpzppCnf (PpzppC0 ++ PpzppC1) PpzppC2 = true := by decide +kernel
theorem Ppzppok3 : chkChunk 15 PpzppCnf (PpzppC0 ++ PpzppC1 ++ PpzppC2) PpzppC3 = true := by decide +kernel
theorem Ppzppfinal : OKs 15 PpzppCnf [] [PpzppC0,PpzppC1,PpzppC2,PpzppC3] :=
  ⟨Ppzppok0, ⟨Ppzppok1, ⟨Ppzppok2, ⟨Ppzppok3, trivial⟩⟩⟩⟩
theorem Ppzppempty : [PpzppC0,PpzppC1,PpzppC2,PpzppC3].flatten.any (fun s => s.2.1.isEmpty) = true := by decide +kernel
theorem Ppzppunsat : ∀ ρ : Nat → Bool, ¬ ∀ c ∈ PpzppCnf, SatCl ρ c := chunks_sound 15 PpzppCnf _ Ppzppfinal Ppzppempty
end Minimality.H24.SAT.K24
