module

public import Minimality.Type29Pair5Lex2Masks

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace Minimality.PL29

theorem pair5_w2_h1_0 :
    SVC.allWeakOrdersF pair5_T2 6 ((List.finRange 7).filter fun x => x != 0) (fun W =>
      if (W.head?.bind List.head?).all (fun b => decide (b.val < 7 / 2)) then
        (let exts := SVC.linExts ([0] :: W);
          pair5_rMs2.any (fun rM => exts.all fun L => Nat.testBit rM (SVC.lehmerAux L)) ||
            exts.all fun L => Nat.testBit pair5_m22 (SVC.lehmerAux L))
      else true) = true := by
  decide +kernel

end Minimality.PL29
