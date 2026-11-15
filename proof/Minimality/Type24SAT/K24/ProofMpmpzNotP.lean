module

public import Minimality.Type24SAT.K24.LratMpmpzNotP

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Minimality.SAT.Checker
namespace Minimality.H24.SAT.K24
def MpmpzNotPC0 : List Step := MpmpzNotPS0 ++ MpmpzNotPS1 ++ MpmpzNotPS2 ++ MpmpzNotPS3
def MpmpzNotPC1 : List Step := MpmpzNotPS4 ++ MpmpzNotPS5 ++ MpmpzNotPS6 ++ MpmpzNotPS7
def MpmpzNotPC2 : List Step := MpmpzNotPS8 ++ MpmpzNotPS9 ++ MpmpzNotPS10 ++ MpmpzNotPS11
def MpmpzNotPC3 : List Step := MpmpzNotPS12
theorem MpmpzNotPok0 : chkChunk 15 MpmpzNotPCnf ([]) MpmpzNotPC0 = true := by decide +kernel
theorem MpmpzNotPok1 : chkChunk 15 MpmpzNotPCnf (MpmpzNotPC0) MpmpzNotPC1 = true := by decide +kernel
theorem MpmpzNotPok2 : chkChunk 15 MpmpzNotPCnf (MpmpzNotPC0 ++ MpmpzNotPC1) MpmpzNotPC2 = true := by decide +kernel
theorem MpmpzNotPok3 : chkChunk 15 MpmpzNotPCnf (MpmpzNotPC0 ++ MpmpzNotPC1 ++ MpmpzNotPC2) MpmpzNotPC3 = true := by decide +kernel
theorem MpmpzNotPfinal : OKs 15 MpmpzNotPCnf [] [MpmpzNotPC0,MpmpzNotPC1,MpmpzNotPC2,MpmpzNotPC3] :=
  ⟨MpmpzNotPok0, ⟨MpmpzNotPok1, ⟨MpmpzNotPok2, ⟨MpmpzNotPok3, trivial⟩⟩⟩⟩
theorem MpmpzNotPempty : [MpmpzNotPC0,MpmpzNotPC1,MpmpzNotPC2,MpmpzNotPC3].flatten.any (fun s => s.2.1.isEmpty) = true := by decide +kernel
theorem MpmpzNotPunsat : ∀ ρ : Nat → Bool, ¬ ∀ c ∈ MpmpzNotPCnf, SatCl ρ c := chunks_sound 15 MpmpzNotPCnf _ MpmpzNotPfinal MpmpzNotPempty
end Minimality.H24.SAT.K24
