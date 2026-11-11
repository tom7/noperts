module

public import Minimality.Type16SAT.LratZZMMU

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Minimality.H29.SAT.K29
def ZZMMUC0 : List Step := ZZMMUS0 ++ ZZMMUS1 ++ ZZMMUS2 ++ ZZMMUS3
def ZZMMUC1 : List Step := ZZMMUS4 ++ ZZMMUS5 ++ ZZMMUS6 ++ ZZMMUS7
def ZZMMUC2 : List Step := ZZMMUS8 ++ ZZMMUS9 ++ ZZMMUS10 ++ ZZMMUS11
def ZZMMUC3 : List Step := ZZMMUS12 ++ ZZMMUS13
theorem ZZMMUok0 : chkChunk 15 ZZMMUCnf ([]) ZZMMUC0 = true := by decide +kernel
theorem ZZMMUok1 : chkChunk 15 ZZMMUCnf (ZZMMUC0) ZZMMUC1 = true := by decide +kernel
theorem ZZMMUok2 : chkChunk 15 ZZMMUCnf (ZZMMUC0 ++ ZZMMUC1) ZZMMUC2 = true := by decide +kernel
theorem ZZMMUok3 : chkChunk 15 ZZMMUCnf (ZZMMUC0 ++ ZZMMUC1 ++ ZZMMUC2) ZZMMUC3 = true := by decide +kernel
theorem ZZMMUfinal : OKs 15 ZZMMUCnf [] [ZZMMUC0,ZZMMUC1,ZZMMUC2,ZZMMUC3] :=
  ⟨ZZMMUok0, ⟨ZZMMUok1, ⟨ZZMMUok2, ⟨ZZMMUok3, trivial⟩⟩⟩⟩
theorem ZZMMUempty : [ZZMMUC0,ZZMMUC1,ZZMMUC2,ZZMMUC3].flatten.any (fun s => s.2.1.isEmpty) = true := by decide +kernel
theorem ZZMMUunsat : ∀ ρ : Nat → Bool, ¬ ∀ c ∈ ZZMMUCnf, SatCl ρ c := chunks_sound 15 ZZMMUCnf _ ZZMMUfinal ZZMMUempty
end Minimality.H29.SAT.K29
