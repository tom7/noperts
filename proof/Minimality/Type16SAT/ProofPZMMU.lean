module

public import Minimality.Type16SAT.LratPZMMU

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Minimality.H29.SAT.K29
def PZMMUC0 : List Step := PZMMUS0 ++ PZMMUS1 ++ PZMMUS2 ++ PZMMUS3
def PZMMUC1 : List Step := PZMMUS4 ++ PZMMUS5 ++ PZMMUS6 ++ PZMMUS7
def PZMMUC2 : List Step := PZMMUS8 ++ PZMMUS9 ++ PZMMUS10
theorem PZMMUok0 : chkChunk 15 PZMMUCnf ([]) PZMMUC0 = true := by decide +kernel
theorem PZMMUok1 : chkChunk 15 PZMMUCnf (PZMMUC0) PZMMUC1 = true := by decide +kernel
theorem PZMMUok2 : chkChunk 15 PZMMUCnf (PZMMUC0 ++ PZMMUC1) PZMMUC2 = true := by decide +kernel
theorem PZMMUfinal : OKs 15 PZMMUCnf [] [PZMMUC0,PZMMUC1,PZMMUC2] :=
  ⟨PZMMUok0, ⟨PZMMUok1, ⟨PZMMUok2, trivial⟩⟩⟩
theorem PZMMUempty : [PZMMUC0,PZMMUC1,PZMMUC2].flatten.any (fun s => s.2.1.isEmpty) = true := by decide +kernel
theorem PZMMUunsat : ∀ ρ : Nat → Bool, ¬ ∀ c ∈ PZMMUCnf, SatCl ρ c := chunks_sound 15 PZMMUCnf _ PZMMUfinal PZMMUempty
end Minimality.H29.SAT.K29
