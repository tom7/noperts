module

public import Minimality.Type24SAT.K24.LratZpmmm

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Minimality.SAT.Checker
namespace Minimality.H24.SAT.K24
def ZpmmmC0 : List Step := ZpmmmS0 ++ ZpmmmS1 ++ ZpmmmS2 ++ ZpmmmS3
def ZpmmmC1 : List Step := ZpmmmS4 ++ ZpmmmS5 ++ ZpmmmS6 ++ ZpmmmS7
def ZpmmmC2 : List Step := ZpmmmS8 ++ ZpmmmS9 ++ ZpmmmS10 ++ ZpmmmS11
def ZpmmmC3 : List Step := ZpmmmS12 ++ ZpmmmS13 ++ ZpmmmS14 ++ ZpmmmS15
theorem Zpmmmok0 : chkChunk 15 ZpmmmCnf ([]) ZpmmmC0 = true := by decide +kernel
theorem Zpmmmok1 : chkChunk 15 ZpmmmCnf (ZpmmmC0) ZpmmmC1 = true := by decide +kernel
theorem Zpmmmok2 : chkChunk 15 ZpmmmCnf (ZpmmmC0 ++ ZpmmmC1) ZpmmmC2 = true := by decide +kernel
theorem Zpmmmok3 : chkChunk 15 ZpmmmCnf (ZpmmmC0 ++ ZpmmmC1 ++ ZpmmmC2) ZpmmmC3 = true := by decide +kernel
theorem Zpmmmfinal : OKs 15 ZpmmmCnf [] [ZpmmmC0,ZpmmmC1,ZpmmmC2,ZpmmmC3] :=
  ⟨Zpmmmok0, ⟨Zpmmmok1, ⟨Zpmmmok2, ⟨Zpmmmok3, trivial⟩⟩⟩⟩
theorem Zpmmmempty : [ZpmmmC0,ZpmmmC1,ZpmmmC2,ZpmmmC3].flatten.any (fun s => s.2.1.isEmpty) = true := by decide +kernel
theorem Zpmmmunsat : ∀ ρ : Nat → Bool, ¬ ∀ c ∈ ZpmmmCnf, SatCl ρ c := chunks_sound 15 ZpmmmCnf _ Zpmmmfinal Zpmmmempty
end Minimality.H24.SAT.K24
