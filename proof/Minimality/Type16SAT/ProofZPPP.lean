module

public import Minimality.Type16SAT.LratZPPP

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Minimality.H29.SAT.K29
def ZPPPC0 : List Step := ZPPPS0 ++ ZPPPS1 ++ ZPPPS2 ++ ZPPPS3
theorem ZPPPok0 : chkChunk 15 ZPPPCnf ([]) ZPPPC0 = true := by decide +kernel
theorem ZPPPfinal : OKs 15 ZPPPCnf [] [ZPPPC0] :=
  ⟨ZPPPok0, trivial⟩
theorem ZPPPempty : [ZPPPC0].flatten.any (fun s => s.2.1.isEmpty) = true := by decide +kernel
theorem ZPPPunsat : ∀ ρ : Nat → Bool, ¬ ∀ c ∈ ZPPPCnf, SatCl ρ c := chunks_sound 15 ZPPPCnf _ ZPPPfinal ZPPPempty
end Minimality.H29.SAT.K29
