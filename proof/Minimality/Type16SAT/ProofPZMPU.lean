module

public import Minimality.Type16SAT.LratPZMPU

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Minimality.H29.SAT.K29
def PZMPUC0 : List Step := PZMPUS0 ++ PZMPUS1 ++ PZMPUS2 ++ PZMPUS3
def PZMPUC1 : List Step := PZMPUS4 ++ PZMPUS5 ++ PZMPUS6 ++ PZMPUS7
def PZMPUC2 : List Step := PZMPUS8 ++ PZMPUS9 ++ PZMPUS10
theorem PZMPUok0 : chkChunk 15 PZMPUCnf ([]) PZMPUC0 = true := by decide +kernel
theorem PZMPUok1 : chkChunk 15 PZMPUCnf (PZMPUC0) PZMPUC1 = true := by decide +kernel
theorem PZMPUok2 : chkChunk 15 PZMPUCnf (PZMPUC0 ++ PZMPUC1) PZMPUC2 = true := by decide +kernel
theorem PZMPUfinal : OKs 15 PZMPUCnf [] [PZMPUC0,PZMPUC1,PZMPUC2] :=
  ⟨PZMPUok0, ⟨PZMPUok1, ⟨PZMPUok2, trivial⟩⟩⟩
theorem PZMPUempty : [PZMPUC0,PZMPUC1,PZMPUC2].flatten.any (fun s => s.2.1.isEmpty) = true := by decide +kernel
theorem PZMPUunsat : ∀ ρ : Nat → Bool, ¬ ∀ c ∈ PZMPUCnf, SatCl ρ c := chunks_sound 15 PZMPUCnf _ PZMPUfinal PZMPUempty
end Minimality.H29.SAT.K29
