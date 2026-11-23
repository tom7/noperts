module

public import Minimality.Type29Pair2Lex1Masks

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace Minimality.PL29

theorem pair2_w1_h0_5 :
    SVC.allCliquesF pair2_T1 [] (List.finRange 7) (fun B =>
      if B.head? == some 5 && decide (2 ≤ B.length) then
        SVC.allWeakOrdersF pair2_T1 6 ((List.finRange 7).filter fun x => !B.contains x) (fun W =>
          (let exts := SVC.linExts (B :: W);
          pair2_rMs1.any (fun rM => exts.all fun L => Nat.testBit rM (SVC.lehmerAux L)) ||
            exts.all fun L => Nat.testBit pair2_m21 (SVC.lehmerAux L)))
      else true) = true := by
  decide +kernel

end Minimality.PL29
