module

public import Minimality.Type24SAT.K24.LratPpppzNotP

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Minimality.SAT.Checker
namespace Minimality.H24.SAT.Lrat
def PpppzNotPC0 : List Step := PpppzNotPS0 ++ PpppzNotPS1 ++ PpppzNotPS2 ++ PpppzNotPS3
def PpppzNotPC1 : List Step := PpppzNotPS4 ++ PpppzNotPS5 ++ PpppzNotPS6 ++ PpppzNotPS7
def PpppzNotPC2 : List Step := PpppzNotPS8 ++ PpppzNotPS9 ++ PpppzNotPS10 ++ PpppzNotPS11
def PpppzNotPC3 : List Step := PpppzNotPS12 ++ PpppzNotPS13 ++ PpppzNotPS14 ++ PpppzNotPS15
def PpppzNotPC4 : List Step := PpppzNotPS16
theorem PpppzNotPok0 : chkChunk 15 PpppzNotPCnf ([]) PpppzNotPC0 = true := by decide +kernel
theorem PpppzNotPok1 : chkChunk 15 PpppzNotPCnf (PpppzNotPC0) PpppzNotPC1 = true := by decide +kernel
theorem PpppzNotPok2 : chkChunk 15 PpppzNotPCnf (PpppzNotPC0 ++ PpppzNotPC1) PpppzNotPC2 = true := by decide +kernel
theorem PpppzNotPok3 : chkChunk 15 PpppzNotPCnf (PpppzNotPC0 ++ PpppzNotPC1 ++ PpppzNotPC2) PpppzNotPC3 = true := by decide +kernel
theorem PpppzNotPok4 : chkChunk 15 PpppzNotPCnf (PpppzNotPC0 ++ PpppzNotPC1 ++ PpppzNotPC2 ++ PpppzNotPC3) PpppzNotPC4 = true := by decide +kernel
theorem PpppzNotPfinal : OKs 15 PpppzNotPCnf [] [PpppzNotPC0,PpppzNotPC1,PpppzNotPC2,PpppzNotPC3,PpppzNotPC4] :=
  ⟨PpppzNotPok0, ⟨PpppzNotPok1, ⟨PpppzNotPok2, ⟨PpppzNotPok3, ⟨PpppzNotPok4, trivial⟩⟩⟩⟩⟩
theorem PpppzNotPempty : [PpppzNotPC0,PpppzNotPC1,PpppzNotPC2,PpppzNotPC3,PpppzNotPC4].flatten.any (fun s => s.2.1.isEmpty) = true := by decide +kernel
theorem PpppzNotPunsat : ∀ ρ : Nat → Bool, ¬ ∀ c ∈ PpppzNotPCnf, SatCl ρ c := chunks_sound 15 PpppzNotPCnf _ PpppzNotPfinal PpppzNotPempty
end Minimality.H24.SAT.Lrat
