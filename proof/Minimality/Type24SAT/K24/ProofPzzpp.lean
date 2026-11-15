module

public import Minimality.Type24SAT.K24.LratPzzpp

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Minimality.SAT.Checker
namespace Minimality.H24.SAT.K24
def PzzppC0 : List Step := PzzppS0 ++ PzzppS1 ++ PzzppS2 ++ PzzppS3
def PzzppC1 : List Step := PzzppS4 ++ PzzppS5 ++ PzzppS6 ++ PzzppS7
def PzzppC2 : List Step := PzzppS8 ++ PzzppS9 ++ PzzppS10 ++ PzzppS11
def PzzppC3 : List Step := PzzppS12
theorem Pzzppok0 : chkChunk 15 PzzppCnf ([]) PzzppC0 = true := by decide +kernel
theorem Pzzppok1 : chkChunk 15 PzzppCnf (PzzppC0) PzzppC1 = true := by decide +kernel
theorem Pzzppok2 : chkChunk 15 PzzppCnf (PzzppC0 ++ PzzppC1) PzzppC2 = true := by decide +kernel
theorem Pzzppok3 : chkChunk 15 PzzppCnf (PzzppC0 ++ PzzppC1 ++ PzzppC2) PzzppC3 = true := by decide +kernel
theorem Pzzppfinal : OKs 15 PzzppCnf [] [PzzppC0,PzzppC1,PzzppC2,PzzppC3] :=
  ⟨Pzzppok0, ⟨Pzzppok1, ⟨Pzzppok2, ⟨Pzzppok3, trivial⟩⟩⟩⟩
theorem Pzzppempty : [PzzppC0,PzzppC1,PzzppC2,PzzppC3].flatten.any (fun s => s.2.1.isEmpty) = true := by decide +kernel
theorem Pzzppunsat : ∀ ρ : Nat → Bool, ¬ ∀ c ∈ PzzppCnf, SatCl ρ c := chunks_sound 15 PzzppCnf _ Pzzppfinal Pzzppempty
end Minimality.H24.SAT.K24
