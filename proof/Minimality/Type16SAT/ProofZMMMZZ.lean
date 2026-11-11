module

public import Minimality.Type16SAT.LratZMMMZZ

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Minimality.H29.SAT.K29
def ZMMMZZC0 : List Step := ZMMMZZS0 ++ ZMMMZZS1 ++ ZMMMZZS2 ++ ZMMMZZS3
def ZMMMZZC1 : List Step := ZMMMZZS4 ++ ZMMMZZS5 ++ ZMMMZZS6 ++ ZMMMZZS7
def ZMMMZZC2 : List Step := ZMMMZZS8 ++ ZMMMZZS9
theorem ZMMMZZok0 : chkChunk 15 ZMMMZZCnf ([]) ZMMMZZC0 = true := by decide +kernel
theorem ZMMMZZok1 : chkChunk 15 ZMMMZZCnf (ZMMMZZC0) ZMMMZZC1 = true := by decide +kernel
theorem ZMMMZZok2 : chkChunk 15 ZMMMZZCnf (ZMMMZZC0 ++ ZMMMZZC1) ZMMMZZC2 = true := by decide +kernel
theorem ZMMMZZfinal : OKs 15 ZMMMZZCnf [] [ZMMMZZC0,ZMMMZZC1,ZMMMZZC2] :=
  ⟨ZMMMZZok0, ⟨ZMMMZZok1, ⟨ZMMMZZok2, trivial⟩⟩⟩
theorem ZMMMZZempty : [ZMMMZZC0,ZMMMZZC1,ZMMMZZC2].flatten.any (fun s => s.2.1.isEmpty) = true := by decide +kernel
theorem ZMMMZZunsat : ∀ ρ : Nat → Bool, ¬ ∀ c ∈ ZMMMZZCnf, SatCl ρ c := chunks_sound 15 ZMMMZZCnf _ ZMMMZZfinal ZMMMZZempty
end Minimality.H29.SAT.K29
