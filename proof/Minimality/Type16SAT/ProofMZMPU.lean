module

public import Minimality.Type16SAT.LratMZMPU

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Minimality.H29.SAT.K29
def MZMPUC0 : List Step := MZMPUS0 ++ MZMPUS1 ++ MZMPUS2 ++ MZMPUS3
def MZMPUC1 : List Step := MZMPUS4 ++ MZMPUS5 ++ MZMPUS6 ++ MZMPUS7
def MZMPUC2 : List Step := MZMPUS8 ++ MZMPUS9
theorem MZMPUok0 : chkChunk 15 MZMPUCnf ([]) MZMPUC0 = true := by decide +kernel
theorem MZMPUok1 : chkChunk 15 MZMPUCnf (MZMPUC0) MZMPUC1 = true := by decide +kernel
theorem MZMPUok2 : chkChunk 15 MZMPUCnf (MZMPUC0 ++ MZMPUC1) MZMPUC2 = true := by decide +kernel
theorem MZMPUfinal : OKs 15 MZMPUCnf [] [MZMPUC0,MZMPUC1,MZMPUC2] :=
  ⟨MZMPUok0, ⟨MZMPUok1, ⟨MZMPUok2, trivial⟩⟩⟩
theorem MZMPUempty : [MZMPUC0,MZMPUC1,MZMPUC2].flatten.any (fun s => s.2.1.isEmpty) = true := by decide +kernel
theorem MZMPUunsat : ∀ ρ : Nat → Bool, ¬ ∀ c ∈ MZMPUCnf, SatCl ρ c := chunks_sound 15 MZMPUCnf _ MZMPUfinal MZMPUempty
end Minimality.H29.SAT.K29
