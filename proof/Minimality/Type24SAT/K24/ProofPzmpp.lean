module

public import Minimality.Type24SAT.K24.LratPzmpp

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Minimality.SAT.Checker
namespace Minimality.H24.SAT.Lrat
def PzmppC0 : List Step := PzmppS0 ++ PzmppS1 ++ PzmppS2 ++ PzmppS3
def PzmppC1 : List Step := PzmppS4 ++ PzmppS5 ++ PzmppS6 ++ PzmppS7
def PzmppC2 : List Step := PzmppS8 ++ PzmppS9 ++ PzmppS10
theorem Pzmppok0 : chkChunk 15 PzmppCnf ([]) PzmppC0 = true := by decide +kernel
theorem Pzmppok1 : chkChunk 15 PzmppCnf (PzmppC0) PzmppC1 = true := by decide +kernel
theorem Pzmppok2 : chkChunk 15 PzmppCnf (PzmppC0 ++ PzmppC1) PzmppC2 = true := by decide +kernel
theorem Pzmppfinal : OKs 15 PzmppCnf [] [PzmppC0,PzmppC1,PzmppC2] :=
  ⟨Pzmppok0, ⟨Pzmppok1, ⟨Pzmppok2, trivial⟩⟩⟩
theorem Pzmppempty : [PzmppC0,PzmppC1,PzmppC2].flatten.any (fun s => s.2.1.isEmpty) = true := by decide +kernel
theorem Pzmppunsat : ∀ ρ : Nat → Bool, ¬ ∀ c ∈ PzmppCnf, SatCl ρ c := chunks_sound 15 PzmppCnf _ Pzmppfinal Pzmppempty
end Minimality.H24.SAT.Lrat
