module

public import Minimality.Type24SAT.K24.LratZpzpzNotP

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Minimality.SAT.Checker
namespace Minimality.H24.SAT.Lrat
def ZpzpzNotPC0 : List Step := ZpzpzNotPS0 ++ ZpzpzNotPS1 ++ ZpzpzNotPS2 ++ ZpzpzNotPS3
def ZpzpzNotPC1 : List Step := ZpzpzNotPS4 ++ ZpzpzNotPS5 ++ ZpzpzNotPS6
theorem ZpzpzNotPok0 : chkChunk 15 ZpzpzNotPCnf ([]) ZpzpzNotPC0 = true := by decide +kernel
theorem ZpzpzNotPok1 : chkChunk 15 ZpzpzNotPCnf (ZpzpzNotPC0) ZpzpzNotPC1 = true := by decide +kernel
theorem ZpzpzNotPfinal : OKs 15 ZpzpzNotPCnf [] [ZpzpzNotPC0,ZpzpzNotPC1] :=
  ⟨ZpzpzNotPok0, ⟨ZpzpzNotPok1, trivial⟩⟩
theorem ZpzpzNotPempty : [ZpzpzNotPC0,ZpzpzNotPC1].flatten.any (fun s => s.2.1.isEmpty) = true := by decide +kernel
theorem ZpzpzNotPunsat : ∀ ρ : Nat → Bool, ¬ ∀ c ∈ ZpzpzNotPCnf, SatCl ρ c := chunks_sound 15 ZpzpzNotPCnf _ ZpzpzNotPfinal ZpzpzNotPempty
end Minimality.H24.SAT.Lrat
