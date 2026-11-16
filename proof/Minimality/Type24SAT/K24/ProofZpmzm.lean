module

public import Minimality.Type24SAT.K24.LratZpmzm

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Minimality.SAT.Checker
namespace Minimality.H24.SAT.Lrat
def ZpmzmC0 : List Step := ZpmzmS0 ++ ZpmzmS1 ++ ZpmzmS2 ++ ZpmzmS3
def ZpmzmC1 : List Step := ZpmzmS4 ++ ZpmzmS5 ++ ZpmzmS6 ++ ZpmzmS7
def ZpmzmC2 : List Step := ZpmzmS8 ++ ZpmzmS9 ++ ZpmzmS10 ++ ZpmzmS11
def ZpmzmC3 : List Step := ZpmzmS12 ++ ZpmzmS13 ++ ZpmzmS14 ++ ZpmzmS15
theorem Zpmzmok0 : chkChunk 15 ZpmzmCnf ([]) ZpmzmC0 = true := by decide +kernel
theorem Zpmzmok1 : chkChunk 15 ZpmzmCnf (ZpmzmC0) ZpmzmC1 = true := by decide +kernel
theorem Zpmzmok2 : chkChunk 15 ZpmzmCnf (ZpmzmC0 ++ ZpmzmC1) ZpmzmC2 = true := by decide +kernel
theorem Zpmzmok3 : chkChunk 15 ZpmzmCnf (ZpmzmC0 ++ ZpmzmC1 ++ ZpmzmC2) ZpmzmC3 = true := by decide +kernel
theorem Zpmzmfinal : OKs 15 ZpmzmCnf [] [ZpmzmC0,ZpmzmC1,ZpmzmC2,ZpmzmC3] :=
  ⟨Zpmzmok0, ⟨Zpmzmok1, ⟨Zpmzmok2, ⟨Zpmzmok3, trivial⟩⟩⟩⟩
theorem Zpmzmempty : [ZpmzmC0,ZpmzmC1,ZpmzmC2,ZpmzmC3].flatten.any (fun s => s.2.1.isEmpty) = true := by decide +kernel
theorem Zpmzmunsat : ∀ ρ : Nat → Bool, ¬ ∀ c ∈ ZpmzmCnf, SatCl ρ c := chunks_sound 15 ZpmzmCnf _ Zpmzmfinal Zpmzmempty
end Minimality.H24.SAT.Lrat
