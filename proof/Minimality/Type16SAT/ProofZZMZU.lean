module

public import Minimality.Type16SAT.LratZZMZU

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Minimality.H29.SAT.K29
def ZZMZUC0 : List Step := ZZMZUS0 ++ ZZMZUS1 ++ ZZMZUS2 ++ ZZMZUS3
def ZZMZUC1 : List Step := ZZMZUS4 ++ ZZMZUS5 ++ ZZMZUS6 ++ ZZMZUS7
def ZZMZUC2 : List Step := ZZMZUS8 ++ ZZMZUS9 ++ ZZMZUS10
theorem ZZMZUok0 : chkChunk 15 ZZMZUCnf ([]) ZZMZUC0 = true := by decide +kernel
theorem ZZMZUok1 : chkChunk 15 ZZMZUCnf (ZZMZUC0) ZZMZUC1 = true := by decide +kernel
theorem ZZMZUok2 : chkChunk 15 ZZMZUCnf (ZZMZUC0 ++ ZZMZUC1) ZZMZUC2 = true := by decide +kernel
theorem ZZMZUfinal : OKs 15 ZZMZUCnf [] [ZZMZUC0,ZZMZUC1,ZZMZUC2] :=
  ⟨ZZMZUok0, ⟨ZZMZUok1, ⟨ZZMZUok2, trivial⟩⟩⟩
theorem ZZMZUempty : [ZZMZUC0,ZZMZUC1,ZZMZUC2].flatten.any (fun s => s.2.1.isEmpty) = true := by decide +kernel
theorem ZZMZUunsat : ∀ ρ : Nat → Bool, ¬ ∀ c ∈ ZZMZUCnf, SatCl ρ c := chunks_sound 15 ZZMZUCnf _ ZZMZUfinal ZZMZUempty
end Minimality.H29.SAT.K29
