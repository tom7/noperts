module

public import Minimality.Type16SAT.LratZMZMU

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Minimality.H29.SAT.K29
def ZMZMUC0 : List Step := ZMZMUS0 ++ ZMZMUS1 ++ ZMZMUS2 ++ ZMZMUS3
def ZMZMUC1 : List Step := ZMZMUS4 ++ ZMZMUS5 ++ ZMZMUS6 ++ ZMZMUS7
def ZMZMUC2 : List Step := ZMZMUS8 ++ ZMZMUS9 ++ ZMZMUS10
theorem ZMZMUok0 : chkChunk 15 ZMZMUCnf ([]) ZMZMUC0 = true := by decide +kernel
theorem ZMZMUok1 : chkChunk 15 ZMZMUCnf (ZMZMUC0) ZMZMUC1 = true := by decide +kernel
theorem ZMZMUok2 : chkChunk 15 ZMZMUCnf (ZMZMUC0 ++ ZMZMUC1) ZMZMUC2 = true := by decide +kernel
theorem ZMZMUfinal : OKs 15 ZMZMUCnf [] [ZMZMUC0,ZMZMUC1,ZMZMUC2] :=
  ⟨ZMZMUok0, ⟨ZMZMUok1, ⟨ZMZMUok2, trivial⟩⟩⟩
theorem ZMZMUempty : [ZMZMUC0,ZMZMUC1,ZMZMUC2].flatten.any (fun s => s.2.1.isEmpty) = true := by decide +kernel
theorem ZMZMUunsat : ∀ ρ : Nat → Bool, ¬ ∀ c ∈ ZMZMUCnf, SatCl ρ c := chunks_sound 15 ZMZMUCnf _ ZMZMUfinal ZMZMUempty
end Minimality.H29.SAT.K29
