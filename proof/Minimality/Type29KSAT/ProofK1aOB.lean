module

public import Minimality.Type29KSAT.LratK1aOB

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Minimality.H29.SAT.K29
def K1aOBC0 : List Step := K1aOBS0 ++ K1aOBS1 ++ K1aOBS2 ++ K1aOBS3
def K1aOBC1 : List Step := K1aOBS4 ++ K1aOBS5 ++ K1aOBS6 ++ K1aOBS7
def K1aOBC2 : List Step := K1aOBS8 ++ K1aOBS9 ++ K1aOBS10 ++ K1aOBS11
def K1aOBC3 : List Step := K1aOBS12 ++ K1aOBS13 ++ K1aOBS14 ++ K1aOBS15
def K1aOBC4 : List Step := K1aOBS16 ++ K1aOBS17 ++ K1aOBS18 ++ K1aOBS19
def K1aOBC5 : List Step := K1aOBS20 ++ K1aOBS21 ++ K1aOBS22 ++ K1aOBS23
def K1aOBC6 : List Step := K1aOBS24 ++ K1aOBS25 ++ K1aOBS26 ++ K1aOBS27
def K1aOBC7 : List Step := K1aOBS28 ++ K1aOBS29 ++ K1aOBS30 ++ K1aOBS31
def K1aOBC8 : List Step := K1aOBS32 ++ K1aOBS33 ++ K1aOBS34 ++ K1aOBS35
def K1aOBC9 : List Step := K1aOBS36 ++ K1aOBS37 ++ K1aOBS38 ++ K1aOBS39
theorem K1aOBok0 : chkChunk 15 K1aOBCnf ([]) K1aOBC0 = true := by decide +kernel
theorem K1aOBok1 : chkChunk 15 K1aOBCnf (K1aOBC0) K1aOBC1 = true := by decide +kernel
theorem K1aOBok2 : chkChunk 15 K1aOBCnf (K1aOBC0 ++ K1aOBC1) K1aOBC2 = true := by decide +kernel
theorem K1aOBok3 : chkChunk 15 K1aOBCnf (K1aOBC0 ++ K1aOBC1 ++ K1aOBC2) K1aOBC3 = true := by decide +kernel
theorem K1aOBok4 : chkChunk 15 K1aOBCnf (K1aOBC0 ++ K1aOBC1 ++ K1aOBC2 ++ K1aOBC3) K1aOBC4 = true := by decide +kernel
theorem K1aOBok5 : chkChunk 15 K1aOBCnf (K1aOBC0 ++ K1aOBC1 ++ K1aOBC2 ++ K1aOBC3 ++ K1aOBC4) K1aOBC5 = true := by decide +kernel
theorem K1aOBok6 : chkChunk 15 K1aOBCnf (K1aOBC0 ++ K1aOBC1 ++ K1aOBC2 ++ K1aOBC3 ++ K1aOBC4 ++ K1aOBC5) K1aOBC6 = true := by decide +kernel
theorem K1aOBok7 : chkChunk 15 K1aOBCnf (K1aOBC0 ++ K1aOBC1 ++ K1aOBC2 ++ K1aOBC3 ++ K1aOBC4 ++ K1aOBC5 ++ K1aOBC6) K1aOBC7 = true := by decide +kernel
theorem K1aOBok8 : chkChunk 15 K1aOBCnf (K1aOBC0 ++ K1aOBC1 ++ K1aOBC2 ++ K1aOBC3 ++ K1aOBC4 ++ K1aOBC5 ++ K1aOBC6 ++ K1aOBC7) K1aOBC8 = true := by decide +kernel
theorem K1aOBok9 : chkChunk 15 K1aOBCnf (K1aOBC0 ++ K1aOBC1 ++ K1aOBC2 ++ K1aOBC3 ++ K1aOBC4 ++ K1aOBC5 ++ K1aOBC6 ++ K1aOBC7 ++ K1aOBC8) K1aOBC9 = true := by decide +kernel
theorem K1aOBfinal : OKs 15 K1aOBCnf [] [K1aOBC0,K1aOBC1,K1aOBC2,K1aOBC3,K1aOBC4,K1aOBC5,K1aOBC6,K1aOBC7,K1aOBC8,K1aOBC9] :=
  ⟨K1aOBok0, ⟨K1aOBok1, ⟨K1aOBok2, ⟨K1aOBok3, ⟨K1aOBok4, ⟨K1aOBok5, ⟨K1aOBok6, ⟨K1aOBok7, ⟨K1aOBok8, ⟨K1aOBok9, trivial⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem K1aOBempty : [K1aOBC0,K1aOBC1,K1aOBC2,K1aOBC3,K1aOBC4,K1aOBC5,K1aOBC6,K1aOBC7,K1aOBC8,K1aOBC9].flatten.any (fun s => s.2.1.isEmpty) = true := by decide +kernel
theorem K1aOBunsat : ∀ ρ : Nat → Bool, ¬ ∀ c ∈ K1aOBCnf, SatCl ρ c := chunks_sound 15 K1aOBCnf _ K1aOBfinal K1aOBempty
end Minimality.H29.SAT.K29
