module

public import Minimality.Type29Pair2Lex1Masks

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace Minimality.PL29

theorem pair2_w1_h2_0 :
    SVC.allWeakOrdersF pair2_T1 6 ((List.finRange 7).filter fun x => x != 0) (fun W =>
      if (W.head?.bind List.head?).any (fun b => decide (7 / 2 ≤ b.val)) then
        (let exts := SVC.linExts ([0] :: W);
          pair2_rMs1.any (fun rM => exts.all fun L => Nat.testBit rM (SVC.lehmerAux L)) ||
            exts.all fun L => Nat.testBit pair2_m21 (SVC.lehmerAux L))
      else true) = true := by
  decide +kernel

end Minimality.PL29
