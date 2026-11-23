module

public import Minimality.Type29Pair2

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000

open scoped RealInnerProductSpace
open Minimality Minimality.H21 Minimality.SVCC Minimality.PSVC

namespace Minimality.PL29

def pair2_T1 : List (Fin 7 × Fin 7) :=
  [(0,1), (0,2), (0,3), (0,4), (0,5), (0,6), (1,2), (1,3), (1,5), (1,6), (2,3), (2,4), (2,5), (2,6), (3,4), (3,5), (3,6), (4,5)]

def pair2_rMs1 : List Nat := [0xffffffffffffffffffffffffffffffffffffffcfffffcff0ffffffffffffffffffffcfffffcc00ffffffffffffffffffffcff0ffcc00fc0c00ff0000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff37ffdf34cfd3fccff0ffffff7d3c3fffffff34cfd3fccff3fffffffd3cfffffffffccff0fccff3ffffffff0cffffffffffffffffffffffffffffffffffffff7d3c3ffd3cffff0cffffffffffffffffcfffffcff0ffffffffffff37ffdf34cfd3fccff0ffffff7d3c3fffcfff34cfd3f0cfc0ffffffffffffffcff0fccff0f0cfc0ffffffc30000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffcfffffcc00ffffffffffffffffff34cfd3fccff3fffffffd3cffffcfff34cfd3f0cfc0ffffffffffffffcc00fccff3f0cfc0c3ffcf03300ffffffffffffffffffffffffffffffffffffffd3cffffffff03300fffffffffffffffcff0ffcc00fc0c00ff0000fffffffccff0fccff3ffffffff0cffffcff0fccff0f0cfc0ffffffc30000ffcc00fccff3f0cfc0c3ffcf03300ffc0c00ffffffffffffc3ffcf03ffcfff0000ff0cffc3000003300f03ffcfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7d3c3ffd3cffff0cfffffffffffffffffffffffffffffffffffffffffffffd3cffffffff03300fffffffff0000ff0cffc3000003300f03ffcfffffffffffffffffffffffffffffff]

def pair2_m21 : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff37ffdf34cfd3ffffffffffff7d3fffffffffffffffffffffffffffffffff34cfd3ffffff33ffccffffff4ff33fffffffffffff33ffccfffffffff300ffffffffffffffffffffffffffffff7d3fffffffff4ff33ffff300ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff34cfd3ffffff33ffccffffff4ff33fffffffffffffffffffffffffffffffffffff33ffccffffffffffb2fccff2ffffffffffffffffffffffffffffffffffff4ff33ffffffffccff2ffffffffffffffffffffffffffffffffffffffffffffffff33ffccfffffffff300ffffffffffffffffffffffffffffffffffff33ffccffffffffffb2fccff2ffffffffffffffffb2ffffb2fc0cb2fffffffff300fffffffccff2fc0cb2ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7d3fffffffff4ff33ffff300ffffffffffffffffffffffffffffffffffffffffff4ff33ffffffffccff2fffffffffffffff300fffffffccff2fc0cb2ffffffffffffffffffffffffffffff

theorem pair2_hr1 : (List.finRange 7).permutations'.all (fun L =>
    (List.finRange pair2_RA.length).all (fun i =>
      !Nat.testBit (pair2_rMs1.getD i.val 0) (SVC.lehmerAux L) ||
        (exclOK [] pair2_D pair2_EA L || SVC.rimOK (pair2_RA[i]) L))) = true := by
  refine perms7_split _ (fun a => ?_)
  fin_cases a <;> decide +kernel

private theorem pair2_hm21_0 : (((List.finRange 7).erase 0).permutations'.all fun L =>
    !Nat.testBit pair2_m21 (SVC.lehmerAux (0 :: L)) || (exclOK [] pair2_D pair2_EA (0 :: L) || pair2_B2.all (gramBad pair2_EA pair2_EB (0 :: L)))) = true := by
  decide +kernel
private theorem pair2_hm21_1 : (((List.finRange 7).erase 1).permutations'.all fun L =>
    !Nat.testBit pair2_m21 (SVC.lehmerAux (1 :: L)) || (exclOK [] pair2_D pair2_EA (1 :: L) || pair2_B2.all (gramBad pair2_EA pair2_EB (1 :: L)))) = true := by
  decide +kernel
private theorem pair2_hm21_2 : (((List.finRange 7).erase 2).permutations'.all fun L =>
    !Nat.testBit pair2_m21 (SVC.lehmerAux (2 :: L)) || (exclOK [] pair2_D pair2_EA (2 :: L) || pair2_B2.all (gramBad pair2_EA pair2_EB (2 :: L)))) = true := by
  decide +kernel
private theorem pair2_hm21_3 : (((List.finRange 7).erase 3).permutations'.all fun L =>
    !Nat.testBit pair2_m21 (SVC.lehmerAux (3 :: L)) || (exclOK [] pair2_D pair2_EA (3 :: L) || pair2_B2.all (gramBad pair2_EA pair2_EB (3 :: L)))) = true := by
  decide +kernel
private theorem pair2_hm21_4 : (((List.finRange 7).erase 4).permutations'.all fun L =>
    !Nat.testBit pair2_m21 (SVC.lehmerAux (4 :: L)) || (exclOK [] pair2_D pair2_EA (4 :: L) || pair2_B2.all (gramBad pair2_EA pair2_EB (4 :: L)))) = true := by
  decide +kernel
private theorem pair2_hm21_5 : (((List.finRange 7).erase 5).permutations'.all fun L =>
    !Nat.testBit pair2_m21 (SVC.lehmerAux (5 :: L)) || (exclOK [] pair2_D pair2_EA (5 :: L) || pair2_B2.all (gramBad pair2_EA pair2_EB (5 :: L)))) = true := by
  decide +kernel
private theorem pair2_hm21_6 : (((List.finRange 7).erase 6).permutations'.all fun L =>
    !Nat.testBit pair2_m21 (SVC.lehmerAux (6 :: L)) || (exclOK [] pair2_D pair2_EA (6 :: L) || pair2_B2.all (gramBad pair2_EA pair2_EB (6 :: L)))) = true := by
  decide +kernel

theorem pair2_hm21 : (List.finRange 7).permutations'.all (fun L =>
    !Nat.testBit pair2_m21 (SVC.lehmerAux L) || (exclOK [] pair2_D pair2_EA L || pair2_B2.all (gramBad pair2_EA pair2_EB L))) = true := by
  refine perms7_split _ (fun a => ?_)
  fin_cases a
  exacts [pair2_hm21_0, pair2_hm21_1, pair2_hm21_2, pair2_hm21_3, pair2_hm21_4, pair2_hm21_5, pair2_hm21_6]

end Minimality.PL29
