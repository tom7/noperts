module

public import Minimality.Type24HoleConfined
public import Minimality.Q4Lex

/-! Item 2 of GENREV24-HOLE: `Hole24` equals the core `Hole24Flags ∧ (Hole24Q45Special ∨ Hole24R1) ∧ ¬ BoxApplies`. -/


set_option autoImplicit false
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21 Minimality.T24.SAT Minimality.T24.NC Minimality.T24.Z0
  Minimality.T24.Adj

@[expose] public section

namespace Minimality.T24

/-- Item 2: every conjunct added to `Hole24R1` by the chain R2 .. R9 follows from `¬ LexAny`. -/
theorem hole24R9_of_R1 {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x} (h : Hole24R1 x F) :
    Hole24R9 x F := by
  have hL : ¬ RCell.LexAny F := (hole24R_of_hole24R1 h).2.2.2.2.1
  have h5 := hole24R4_reduce (hole24R3_reduce (hole24R2_reduce (hole24R1_reduce h)))
  exact ⟨⟨⟨⟨h5, fun hs => hL (svcCell_lexAny hs), fun hp => hL (pairL3u27_lexAny hp)⟩,
    fun ht => hL (triple_lexAny ht)⟩, fun ht => hL (triple2_lexAny ht)⟩,
    fun ht => hL (triple3_lexAny ht)⟩

theorem hole24R9_iff {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x} :
    Hole24R9 x F ↔ Hole24R1 x F :=
  ⟨fun h => h.1.1.1.1.1.1.1.1, hole24R9_of_R1⟩

theorem hole24Q45R9_iff {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x} :
    Hole24Q45R9 x F ↔ Hole24Q45Special x F := by
  refine ⟨fun h => h.1.1.1.1.1, fun hQ => ?_⟩
  have hL : ¬ RCell.LexAny F := hQ.2.2.2.2.2.1
  exact ⟨⟨⟨⟨hole24Q45_reduce hQ, fun hs => hL (svcCell_lexAny hs), fun hp => hL (pairL3u27_lexAny hp)⟩,
    fun ht => hL (triple_lexAny ht)⟩, fun ht => hL (triple2_lexAny ht)⟩,
    fun ht => hL (triple3_lexAny ht)⟩

/-- Item 2: the cleaned hole. Same set as `Hole24` (`hole24_iff_core`). -/
def Hole24Core (x : Fin 7 → ℝ³) (fs : Fin 9 → ℝ³ →ᵃ[ℝ] ℝ) (F : S0xFac 9 s0x_S24 x) : Prop :=
  Hole24Flags x fs ∧ (Hole24Q45Special x F ∨ Hole24R1 x F) ∧ ¬ BoxApplies (Finset.univ.image x)

theorem hole24_iff_core {x : Fin 7 → ℝ³} {fs : Fin 9 → ℝ³ →ᵃ[ℝ] ℝ}
    (hh : ∀ t i, (i ∈ s0x_S24 t → fs t (x i) = 0) ∧ (i ∉ s0x_S24 t → fs t (x i) < 0)) :
    Hole24 x fs (mkFac24 fs hh) ↔ Hole24Core x fs (mkFac24 fs hh) := by
  constructor
  · rintro ⟨hf, hQR, -, -, hbox, -, -⟩
    exact ⟨hf, hQR.imp hole24Q45R9_iff.1 hole24R9_iff.1, hbox⟩
  · rintro ⟨hf, hQR, hbox⟩
    have hL : ¬ RCell.LexAny (mkFac24 fs hh) := by
      rcases hQR with hQ | hR
      · exact hQ.2.2.2.2.2.1
      · exact (hole24R_of_hole24R1 hR).2.2.2.2.1
    have hx := EdgeViewLink.inj_of_fac24 (mkFac24 fs hh)
    refine ⟨hf, hQR.imp hole24Q45R9_iff.2 hole24R9_iff.2, ?_, ?_, hbox, ?_, ?_⟩
    · rintro ⟨hc3, hmu⟩
      rcases w63_closes_star_or_facetCell fs hh hc3 hmu with h | h
      · exact hL h
      · exact hf.1 h
    · rintro ⟨hb3, hmu⟩
      rcases e23_closes_star_or_facetCell fs hh hb3 hmu with h | h
      · exact hL h
      · exact hf.1 h
    · exact fun h => hL (Minimality.GenRev.lexAny_of_q4Any _ hx h)
    · exact fun h => hL (Minimality.GenRev.lexAny_of_edgeAny _ h)

end Minimality.T24
