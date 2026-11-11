module

public import Minimality.Type16SAT.LratZMPMU

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Minimality.H29.SAT.K29
def ZMPMUC0 : List Step := ZMPMUS0 ++ ZMPMUS1 ++ ZMPMUS2 ++ ZMPMUS3
def ZMPMUC1 : List Step := ZMPMUS4 ++ ZMPMUS5 ++ ZMPMUS6 ++ ZMPMUS7
def ZMPMUC2 : List Step := ZMPMUS8 ++ ZMPMUS9
theorem ZMPMUok0 : chkChunk 15 ZMPMUCnf ([]) ZMPMUC0 = true := by decide +kernel
theorem ZMPMUok1 : chkChunk 15 ZMPMUCnf (ZMPMUC0) ZMPMUC1 = true := by decide +kernel
theorem ZMPMUok2 : chkChunk 15 ZMPMUCnf (ZMPMUC0 ++ ZMPMUC1) ZMPMUC2 = true := by decide +kernel
theorem ZMPMUfinal : OKs 15 ZMPMUCnf [] [ZMPMUC0,ZMPMUC1,ZMPMUC2] :=
  ⟨ZMPMUok0, ⟨ZMPMUok1, ⟨ZMPMUok2, trivial⟩⟩⟩
theorem ZMPMUempty : [ZMPMUC0,ZMPMUC1,ZMPMUC2].flatten.any (fun s => s.2.1.isEmpty) = true := by decide +kernel
theorem ZMPMUunsat : ∀ ρ : Nat → Bool, ¬ ∀ c ∈ ZMPMUCnf, SatCl ρ c := chunks_sound 15 ZMPMUCnf _ ZMPMUfinal ZMPMUempty
end Minimality.H29.SAT.K29
