module

public import Minimality.Type29Pair2Lex2Masks

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace Minimality.PL29

theorem pair2_w2_h1_2 :
    SVC.allWeakOrdersF pair2_T2 6 ((List.finRange 7).filter fun x => x != 2) (fun W =>
      if (W.head?.bind List.head?).all (fun b => decide (b.val < 7 / 2)) then
        (let exts := SVC.linExts ([2] :: W);
          pair2_rMs2.any (fun rM => exts.all fun L => Nat.testBit rM (SVC.lehmerAux L)) ||
            exts.all fun L => Nat.testBit pair2_m22 (SVC.lehmerAux L))
      else true) = true := by
  decide +kernel

end Minimality.PL29
