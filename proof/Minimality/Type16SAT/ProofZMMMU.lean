module

public import Minimality.Type16SAT.LratZMMMU

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Minimality.H29.SAT.K29
def ZMMMUC0 : List Step := ZMMMUS0 ++ ZMMMUS1 ++ ZMMMUS2 ++ ZMMMUS3
def ZMMMUC1 : List Step := ZMMMUS4 ++ ZMMMUS5 ++ ZMMMUS6 ++ ZMMMUS7
def ZMMMUC2 : List Step := ZMMMUS8 ++ ZMMMUS9 ++ ZMMMUS10 ++ ZMMMUS11
def ZMMMUC3 : List Step := ZMMMUS12
theorem ZMMMUok0 : chkChunk 15 ZMMMUCnf ([]) ZMMMUC0 = true := by decide +kernel
theorem ZMMMUok1 : chkChunk 15 ZMMMUCnf (ZMMMUC0) ZMMMUC1 = true := by decide +kernel
theorem ZMMMUok2 : chkChunk 15 ZMMMUCnf (ZMMMUC0 ++ ZMMMUC1) ZMMMUC2 = true := by decide +kernel
theorem ZMMMUok3 : chkChunk 15 ZMMMUCnf (ZMMMUC0 ++ ZMMMUC1 ++ ZMMMUC2) ZMMMUC3 = true := by decide +kernel
theorem ZMMMUfinal : OKs 15 ZMMMUCnf [] [ZMMMUC0,ZMMMUC1,ZMMMUC2,ZMMMUC3] :=
  ⟨ZMMMUok0, ⟨ZMMMUok1, ⟨ZMMMUok2, ⟨ZMMMUok3, trivial⟩⟩⟩⟩
theorem ZMMMUempty : [ZMMMUC0,ZMMMUC1,ZMMMUC2,ZMMMUC3].flatten.any (fun s => s.2.1.isEmpty) = true := by decide +kernel
theorem ZMMMUunsat : ∀ ρ : Nat → Bool, ¬ ∀ c ∈ ZMMMUCnf, SatCl ρ c := chunks_sound 15 ZMMMUCnf _ ZMMMUfinal ZMMMUempty
end Minimality.H29.SAT.K29
