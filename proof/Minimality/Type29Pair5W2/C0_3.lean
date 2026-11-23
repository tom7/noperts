module

public import Minimality.Type29Pair5Lex2Masks

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace Minimality.PL29

theorem pair5_w2_h0_3 :
    SVC.allCliquesF pair5_T2 [] (List.finRange 7) (fun B =>
      if B.head? == some 3 && decide (2 ≤ B.length) then
        SVC.allWeakOrdersF pair5_T2 6 ((List.finRange 7).filter fun x => !B.contains x) (fun W =>
          (let exts := SVC.linExts (B :: W);
          pair5_rMs2.any (fun rM => exts.all fun L => Nat.testBit rM (SVC.lehmerAux L)) ||
            exts.all fun L => Nat.testBit pair5_m22 (SVC.lehmerAux L)))
      else true) = true := by
  decide +kernel

end Minimality.PL29
