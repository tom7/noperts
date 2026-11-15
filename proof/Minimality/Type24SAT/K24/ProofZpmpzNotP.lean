module

public import Minimality.Type24SAT.K24.LratZpmpzNotP

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Minimality.SAT.Checker
namespace Minimality.H24.SAT.K24
def ZpmpzNotPC0 : List Step := ZpmpzNotPS0 ++ ZpmpzNotPS1 ++ ZpmpzNotPS2 ++ ZpmpzNotPS3
def ZpmpzNotPC1 : List Step := ZpmpzNotPS4 ++ ZpmpzNotPS5 ++ ZpmpzNotPS6 ++ ZpmpzNotPS7
def ZpmpzNotPC2 : List Step := ZpmpzNotPS8 ++ ZpmpzNotPS9 ++ ZpmpzNotPS10 ++ ZpmpzNotPS11
theorem ZpmpzNotPok0 : chkChunk 15 ZpmpzNotPCnf ([]) ZpmpzNotPC0 = true := by decide +kernel
theorem ZpmpzNotPok1 : chkChunk 15 ZpmpzNotPCnf (ZpmpzNotPC0) ZpmpzNotPC1 = true := by decide +kernel
theorem ZpmpzNotPok2 : chkChunk 15 ZpmpzNotPCnf (ZpmpzNotPC0 ++ ZpmpzNotPC1) ZpmpzNotPC2 = true := by decide +kernel
theorem ZpmpzNotPfinal : OKs 15 ZpmpzNotPCnf [] [ZpmpzNotPC0,ZpmpzNotPC1,ZpmpzNotPC2] :=
  ⟨ZpmpzNotPok0, ⟨ZpmpzNotPok1, ⟨ZpmpzNotPok2, trivial⟩⟩⟩
theorem ZpmpzNotPempty : [ZpmpzNotPC0,ZpmpzNotPC1,ZpmpzNotPC2].flatten.any (fun s => s.2.1.isEmpty) = true := by decide +kernel
theorem ZpmpzNotPunsat : ∀ ρ : Nat → Bool, ¬ ∀ c ∈ ZpmpzNotPCnf, SatCl ρ c := chunks_sound 15 ZpmpzNotPCnf _ ZpmpzNotPfinal ZpmpzNotPempty
end Minimality.H24.SAT.K24
