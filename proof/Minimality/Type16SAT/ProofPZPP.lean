module

public import Minimality.Type16SAT.LratPZPP

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Minimality.H29.SAT.K29
def PZPPC0 : List Step := PZPPS0 ++ PZPPS1
theorem PZPPok0 : chkChunk 15 PZPPCnf ([]) PZPPC0 = true := by decide +kernel
theorem PZPPfinal : OKs 15 PZPPCnf [] [PZPPC0] :=
  ⟨PZPPok0, trivial⟩
theorem PZPPempty : [PZPPC0].flatten.any (fun s => s.2.1.isEmpty) = true := by decide +kernel
theorem PZPPunsat : ∀ ρ : Nat → Bool, ¬ ∀ c ∈ PZPPCnf, SatCl ρ c := chunks_sound 15 PZPPCnf _ PZPPfinal PZPPempty
end Minimality.H29.SAT.K29
