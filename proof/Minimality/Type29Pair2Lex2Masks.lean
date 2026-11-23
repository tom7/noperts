module

public import Minimality.Type29Pair2

@[expose] public section

/-!
# Type 29: precomputed bitmasks for `pair2` (`check2W`)
-/

set_option autoImplicit false

open scoped RealInnerProductSpace
open Minimality Minimality.H21 Minimality.SVCC Minimality.PSVC

namespace Minimality.PL29

def pair2_T2 : List (Fin 7 × Fin 7) :=
  [(0,1), (0,2), (0,3), (0,4), (0,5), (0,6), (1,3), (1,4), (1,6), (2,4), (2,5), (2,6), (3,4), (3,6), (4,5), (4,6), (5,6)]

def pair2_rMs2 : List Nat := [0xfffffffffffffffffffffffffffffffffffffff03ffffffffc0ff3fffffffffffffff03ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff03ffffffffc0ff3fffffffffffffffffffffffffffffffffffffff03ffffffffffffffffffffffffffffffffffffffffffffffffffffffffc0ff3ffffffffffffffffffcffffffffffffffffffffffffffffffffffffffffffff03ffffffffffffffffffffffffffffffffffffffffffffffffffff03ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc0ff3ffffffffffffffffffcfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffcfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffcfffffffffffffffff]

def pair2_m22 : Nat := 0x3f00c00dfc7ffffffffffff307fff03f00c000ffffc003003f00cffffff00dfc7000fff340fd3fffffffffffffffffffc0030340fd3ffffffff04ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff03f00c000ffffc003003f00cffffffffffffffffffffffffffffffffffff000fffffffff03f34dfffffffffffffc0030ffffff03f34d03f34dc3f34d03f00cffffffffffff03f34d33ffcdffffffffffffffffffffffffffffff00dfc7000fff340fd3ffffffffffffffffffffffffffffffffffffffffff000fffffffff03f34dffffffffffff340fd3ffffff03f34dfff37d4ff37dffffffffffffffffffffffffffffffffffffffffffffffff4ff37dfffffffffffffc0030340fd3ffffffff04fffffffffffffffffffffffffffffffffc0030ffffff03f34d03f34dc3f34d340fd3ffffff03f34dfff37d4ff37dffffffffffff03f34dfff37dfff37dff04ffffffffc3f34d4ff37dfff37dffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff03f00cffffffffffff03f34d33ffcdffffffffffffffffffffffffffffffffffffffffff03f34dfff37dfff37dffffffffffff33ffcdfffffffff37dffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff4ff37dffffffff04ffffffffc3f34d4ff37dfff37dffffffffffff33ffcdfffffffff37d

theorem pair2_hr2 : (List.finRange 7).permutations'.all (fun L =>
    (List.finRange pair2_RB.length).all (fun i =>
      !Nat.testBit (pair2_rMs2.getD i.val 0) (SVC.lehmerAux L) ||
        (exclOK [] pair2_D pair2_EB L || SVC.rimOK (pair2_RB[i]) L))) = true := by
  refine perms7_split _ (fun a => ?_)
  fin_cases a <;> decide +kernel

theorem pair2_hm22 : (List.finRange 7).permutations'.all (fun L =>
    !Nat.testBit pair2_m22 (SVC.lehmerAux L) || (exclOK [] pair2_D pair2_EB L || pair2_B2.contains L)) = true := by
  refine perms7_split _ (fun a => ?_)
  fin_cases a <;> decide +kernel

end Minimality.PL29
