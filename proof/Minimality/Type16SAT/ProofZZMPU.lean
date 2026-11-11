module

public import Minimality.Type16SAT.LratZZMPU

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Minimality.H29.SAT.K29
def ZZMPUC0 : List Step := ZZMPUS0 ++ ZZMPUS1 ++ ZZMPUS2 ++ ZZMPUS3
def ZZMPUC1 : List Step := ZZMPUS4 ++ ZZMPUS5 ++ ZZMPUS6 ++ ZZMPUS7
def ZZMPUC2 : List Step := ZZMPUS8 ++ ZZMPUS9
theorem ZZMPUok0 : chkChunk 15 ZZMPUCnf ([]) ZZMPUC0 = true := by decide +kernel
theorem ZZMPUok1 : chkChunk 15 ZZMPUCnf (ZZMPUC0) ZZMPUC1 = true := by decide +kernel
theorem ZZMPUok2 : chkChunk 15 ZZMPUCnf (ZZMPUC0 ++ ZZMPUC1) ZZMPUC2 = true := by decide +kernel
theorem ZZMPUfinal : OKs 15 ZZMPUCnf [] [ZZMPUC0,ZZMPUC1,ZZMPUC2] :=
  ⟨ZZMPUok0, ⟨ZZMPUok1, ⟨ZZMPUok2, trivial⟩⟩⟩
theorem ZZMPUempty : [ZZMPUC0,ZZMPUC1,ZZMPUC2].flatten.any (fun s => s.2.1.isEmpty) = true := by decide +kernel
theorem ZZMPUunsat : ∀ ρ : Nat → Bool, ¬ ∀ c ∈ ZZMPUCnf, SatCl ρ c := chunks_sound 15 ZZMPUCnf _ ZZMPUfinal ZZMPUempty
end Minimality.H29.SAT.K29
