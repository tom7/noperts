module

public import Minimality.Type16SAT.LratPPZP

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Minimality.H29.SAT.K29
def PPZPC0 : List Step := PPZPS0 ++ PPZPS1 ++ PPZPS2
theorem PPZPok0 : chkChunk 15 PPZPCnf ([]) PPZPC0 = true := by decide +kernel
theorem PPZPfinal : OKs 15 PPZPCnf [] [PPZPC0] :=
  ⟨PPZPok0, trivial⟩
theorem PPZPempty : [PPZPC0].flatten.any (fun s => s.2.1.isEmpty) = true := by decide +kernel
theorem PPZPunsat : ∀ ρ : Nat → Bool, ¬ ∀ c ∈ PPZPCnf, SatCl ρ c := chunks_sound 15 PPZPCnf _ PPZPfinal PPZPempty
end Minimality.H29.SAT.K29
