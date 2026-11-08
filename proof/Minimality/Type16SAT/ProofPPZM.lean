module

public import Minimality.Type16SAT.LratPPZM

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Minimality.H29.SAT.K29
def PPZMC0 : List Step := PPZMS0 ++ PPZMS1 ++ PPZMS2 ++ PPZMS3
def PPZMC1 : List Step := PPZMS4 ++ PPZMS5 ++ PPZMS6
theorem PPZMok0 : chkChunk 15 PPZMCnf ([]) PPZMC0 = true := by decide +kernel
theorem PPZMok1 : chkChunk 15 PPZMCnf (PPZMC0) PPZMC1 = true := by decide +kernel
theorem PPZMfinal : OKs 15 PPZMCnf [] [PPZMC0,PPZMC1] :=
  ⟨PPZMok0, ⟨PPZMok1, trivial⟩⟩
theorem PPZMempty : [PPZMC0,PPZMC1].flatten.any (fun s => s.2.1.isEmpty) = true := by decide +kernel
theorem PPZMunsat : ∀ ρ : Nat → Bool, ¬ ∀ c ∈ PPZMCnf, SatCl ρ c := chunks_sound 15 PPZMCnf _ PPZMfinal PPZMempty
end Minimality.H29.SAT.K29
