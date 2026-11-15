module

public import Minimality.Type24SAT.K24.LratZpppzNotP

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Minimality.SAT.Checker
namespace Minimality.H24.SAT.K24
def ZpppzNotPC0 : List Step := ZpppzNotPS0 ++ ZpppzNotPS1 ++ ZpppzNotPS2 ++ ZpppzNotPS3
def ZpppzNotPC1 : List Step := ZpppzNotPS4 ++ ZpppzNotPS5 ++ ZpppzNotPS6 ++ ZpppzNotPS7
def ZpppzNotPC2 : List Step := ZpppzNotPS8 ++ ZpppzNotPS9 ++ ZpppzNotPS10
theorem ZpppzNotPok0 : chkChunk 15 ZpppzNotPCnf ([]) ZpppzNotPC0 = true := by decide +kernel
theorem ZpppzNotPok1 : chkChunk 15 ZpppzNotPCnf (ZpppzNotPC0) ZpppzNotPC1 = true := by decide +kernel
theorem ZpppzNotPok2 : chkChunk 15 ZpppzNotPCnf (ZpppzNotPC0 ++ ZpppzNotPC1) ZpppzNotPC2 = true := by decide +kernel
theorem ZpppzNotPfinal : OKs 15 ZpppzNotPCnf [] [ZpppzNotPC0,ZpppzNotPC1,ZpppzNotPC2] :=
  ⟨ZpppzNotPok0, ⟨ZpppzNotPok1, ⟨ZpppzNotPok2, trivial⟩⟩⟩
theorem ZpppzNotPempty : [ZpppzNotPC0,ZpppzNotPC1,ZpppzNotPC2].flatten.any (fun s => s.2.1.isEmpty) = true := by decide +kernel
theorem ZpppzNotPunsat : ∀ ρ : Nat → Bool, ¬ ∀ c ∈ ZpppzNotPCnf, SatCl ρ c := chunks_sound 15 ZpppzNotPCnf _ ZpppzNotPfinal ZpppzNotPempty
end Minimality.H24.SAT.K24
