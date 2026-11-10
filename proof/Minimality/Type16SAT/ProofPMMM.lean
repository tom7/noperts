module

public import Minimality.Type16SAT.LratPMMM

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Minimality.H29.SAT.K29
def PMMMC0 : List Step := PMMMS0 ++ PMMMS1 ++ PMMMS2 ++ PMMMS3
def PMMMC1 : List Step := PMMMS4 ++ PMMMS5 ++ PMMMS6 ++ PMMMS7
def PMMMC2 : List Step := PMMMS8 ++ PMMMS9 ++ PMMMS10
theorem PMMMok0 : chkChunk 15 PMMMCnf ([]) PMMMC0 = true := by decide +kernel
theorem PMMMok1 : chkChunk 15 PMMMCnf (PMMMC0) PMMMC1 = true := by decide +kernel
theorem PMMMok2 : chkChunk 15 PMMMCnf (PMMMC0 ++ PMMMC1) PMMMC2 = true := by decide +kernel
theorem PMMMfinal : OKs 15 PMMMCnf [] [PMMMC0,PMMMC1,PMMMC2] :=
  ⟨PMMMok0, ⟨PMMMok1, ⟨PMMMok2, trivial⟩⟩⟩
theorem PMMMempty : [PMMMC0,PMMMC1,PMMMC2].flatten.any (fun s => s.2.1.isEmpty) = true := by decide +kernel
theorem PMMMunsat : ∀ ρ : Nat → Bool, ¬ ∀ c ∈ PMMMCnf, SatCl ρ c := chunks_sound 15 PMMMCnf _ PMMMfinal PMMMempty
end Minimality.H29.SAT.K29
