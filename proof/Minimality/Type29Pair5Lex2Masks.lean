module

public import Minimality.Type29Pair5

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000

open scoped RealInnerProductSpace
open Minimality Minimality.H21 Minimality.SVCC Minimality.PSVC

namespace Minimality.PL29

def pair5_T2 : List (Fin 7 × Fin 7) :=
  [(0,1), (0,2), (0,3), (0,4), (0,5), (0,6), (1,2), (1,3), (1,4), (1,5), (1,6), (2,5), (2,6), (3,4), (3,5), (4,5), (5,6)]

def pair5_rMs2 : List Nat := [0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000ffffff03f00cffffff03f33fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000ffffff03f00cffffff03f33fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff03f33fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff03f33fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff]

def pair5_m22 : Nat := 0xdfc7ffffffffffff007fff00000000000000003f000000ffffff00dfc7000000340fd3ffffff1c04ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff007fffffffff1c04ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000003f000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00003fffffff03f00c000000ffffff00000003f00cffffff00000000cfc0ffffffffffffffffffffffffffffff00dfc7000000340fd3ffffff1c04ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff340fd3ffffff03f00cffffff4ff33fffffffffffffffffffffffffffffff1c04ffffffffffffff4ff33fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00003fffffff03f00c000000ffffff340fd3ffffff03f00cffffff4ff33fffffffffffffffffffffffffffffffffffffffffffffffff4ff33fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff007fffffffff1c04ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff1c04ffffffffffffff4ff33fffffffffffffffffffffffff4ff33fffffffffffffffffffffffffffffffffffff

theorem pair5_hr2 : (List.finRange 7).permutations'.all (fun L =>
    (List.finRange pair5_RB.length).all (fun i =>
      !Nat.testBit (pair5_rMs2.getD i.val 0) (SVC.lehmerAux L) ||
        (exclOK [] pair5_D pair5_EB L || SVC.rimOK (pair5_RB[i]) L))) = true := by
  refine perms7_split _ (fun a => ?_)
  fin_cases a <;> decide +kernel

theorem pair5_hm22 : (List.finRange 7).permutations'.all (fun L =>
    !Nat.testBit pair5_m22 (SVC.lehmerAux L) || (exclOK [] pair5_D pair5_EB L || pair5_B2.contains L)) = true := by
  refine perms7_split _ (fun a => ?_)
  fin_cases a <;> decide +kernel

end Minimality.PL29
