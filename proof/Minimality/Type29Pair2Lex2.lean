module

public import Minimality.Type29Pair2W2.C0_0
public import Minimality.Type29Pair2W2.C0_1
public import Minimality.Type29Pair2W2.C0_2
public import Minimality.Type29Pair2W2.C0_3
public import Minimality.Type29Pair2W2.C0_4
public import Minimality.Type29Pair2W2.C0_5
public import Minimality.Type29Pair2W2.C0_6
public import Minimality.Type29Pair2W2.C1_0
public import Minimality.Type29Pair2W2.C1_1
public import Minimality.Type29Pair2W2.C1_2
public import Minimality.Type29Pair2W2.C1_3
public import Minimality.Type29Pair2W2.C1_4
public import Minimality.Type29Pair2W2.C1_5
public import Minimality.Type29Pair2W2.C1_6
public import Minimality.Type29Pair2W2.C2_0
public import Minimality.Type29Pair2W2.C2_1
public import Minimality.Type29Pair2W2.C2_2
public import Minimality.Type29Pair2W2.C2_3
public import Minimality.Type29Pair2W2.C2_4
public import Minimality.Type29Pair2W2.C2_5
public import Minimality.Type29Pair2W2.C2_6

@[expose] public section

set_option autoImplicit false

open scoped RealInnerProductSpace
open Minimality Minimality.H21 Minimality.SVCC Minimality.PSVC

namespace Minimality.PL29

theorem pair2_check2W : check2W s0x_S29 pair2_P pair2_swB [] pair2_D pair2_EB pair2_RB pair2_T2 pair2_B2 = true := by
  refine check2W_of_masks _ _ _ _ _ _ _ _ _ pair2_rMs2 pair2_m22
    (by decide +kernel) rfl pair2_hr2 pair2_hm22 ?_
  refine SVC.weakOrders_split3 (by omega) pair2_T2 _ (fun a => ?_) (fun a => ?_) (fun a => ?_)
  · fin_cases a
    exacts [pair2_w2_h0_0, pair2_w2_h0_1, pair2_w2_h0_2, pair2_w2_h0_3, pair2_w2_h0_4, pair2_w2_h0_5, pair2_w2_h0_6]
  · fin_cases a
    exacts [pair2_w2_h1_0, pair2_w2_h1_1, pair2_w2_h1_2, pair2_w2_h1_3, pair2_w2_h1_4, pair2_w2_h1_5, pair2_w2_h1_6]
  · fin_cases a
    exacts [pair2_w2_h2_0, pair2_w2_h2_1, pair2_w2_h2_2, pair2_w2_h2_3, pair2_w2_h2_4, pair2_w2_h2_5, pair2_w2_h2_6]

end Minimality.PL29
