module

public import Minimality.Type29Pair5Lex1Masks

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace Minimality.PL29

theorem pair5_w1_h1_3 :
    SVC.allWeakOrdersF pair5_T1 6 ((List.finRange 7).filter fun x => x != 3) (fun W =>
      if (W.head?.bind List.head?).all (fun b => decide (b.val < 7 / 2)) then
        (let exts := SVC.linExts ([3] :: W);
          pair5_rMs1.any (fun rM => exts.all fun L => Nat.testBit rM (SVC.lehmerAux L)) ||
            exts.all fun L => Nat.testBit pair5_m21 (SVC.lehmerAux L))
      else true) = true := by
  decide +kernel

end Minimality.PL29
