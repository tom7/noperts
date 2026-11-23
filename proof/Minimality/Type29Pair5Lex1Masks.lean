module

public import Minimality.Type29Pair5

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000

open scoped RealInnerProductSpace
open Minimality Minimality.H21 Minimality.SVCC Minimality.PSVC

namespace Minimality.PL29

def pair5_T1 : List (Fin 7 × Fin 7) :=
  [(0,1), (0,2), (0,3), (0,4), (0,5), (0,6), (1,2), (1,3), (1,5), (1,6), (2,3), (2,4), (2,5), (2,6), (3,4), (3,5), (3,6), (4,5), (4,6)]

def pair5_rMs1 : List Nat := [0xffcfc0ffffffffffffffffff03ffffffcfc0fffffff3fffffffffffffffffffffffffffffffdfffc7dfffffffffffffffffffffffffffffffffffffffffffffffffffc7dfffffdffffffff03ffffffffffffffffffffffffffffffcfc0ffffffffffffffffff03ffffffcfc0fffffff3ffcdffffff03f34dfffffffffffffffffffffffffffffffffffff3ffcdfffffffffffffcdfffffffffffffffffffffffffffffffff03ffff03f34dfffffffcdfffffffffffcfc0fffffff3ffffffffffffffffffcfc0fffffff3ffcdffffff03f34dfffffffffffffffffffffffffffffff3fffff3ffcdfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdfffc7dfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdffffffffffffffdffffffffffffc7dffffffffffffffdffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff3ffcdfffffffffffffcdffff3fffff3ffcdfffffffffffffffffffffdffffffffffffffdffffffffffffffdffffffffffffffdffffffffffffffffffcdffffffffffffffffffffffffffffffffffc7dfffffdfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc7dffffffffffffffdffffffffffffffdffffffffffffffdfffffffffffffffffffffffffffffffffffffffff03ffffffffffffffffffffffffffff03ffff03f34dfffffffcdffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffcdfffffffffffffffffffffffffffffffffffffffffffffffffff]

def pair5_m21 : Nat := 0xffffffffeff8ffffff03f300ff8fc0ffffffffffffffffffffffffffffffffeff8fffffffbffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8fc0ffffffffffffffffffffffffffffffffeff8ffffff03f300ff8fc0ffffffffffffffffffffffffffffffffeff8fffffffbffedffffffe3fb4dfffffffffffffbffed30dfc5fffb4503f30003f34dffffff30dfc500d345ff8fc0ffffffe3fb4dfffb4500d345ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeff8fffffffbffffffffffffffffffeff8fffffffbffedffffffe3fb4dfffffffffffffffffffffffffffffffbfffffbffedfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbffed30dfc5fffb45fffffffffffffffffffffffffffffffbfffffbffedffffffffffffffffffffffff30dfc5fcdff7fffffffc5dfffffffffffb45fffffffffffffc5dffffffffffffffffffffffffffffffff03f30003f34dffffff30dfc500d345ffffff03f34dfffffffcdff7fcdff7ffffffffffffffffffffffffffffffffffff30dfc5fcdff7fffffffc5dffffffff00d345fcdff7fffffffc5dffff8fc0ffffffffffffffffffffffffff8fc0ffffffe3fb4dfffb4500d345fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffb45fffffffffffffc5dffffffff00d345fcdff7fffffffc5dff

theorem pair5_hr1 : (List.finRange 7).permutations'.all (fun L =>
    (List.finRange pair5_RA.length).all (fun i =>
      !Nat.testBit (pair5_rMs1.getD i.val 0) (SVC.lehmerAux L) ||
        (exclOK [] pair5_D pair5_EA L || SVC.rimOK (pair5_RA[i]) L))) = true := by
  refine perms7_split _ (fun a => ?_)
  fin_cases a <;> decide +kernel

private theorem pair5_hm21_0 : (((List.finRange 7).erase 0).permutations'.all fun L =>
    !Nat.testBit pair5_m21 (SVC.lehmerAux (0 :: L)) || (exclOK [] pair5_D pair5_EA (0 :: L) || pair5_B2.all (gramBad pair5_EA pair5_EB (0 :: L)))) = true := by
  decide +kernel
private theorem pair5_hm21_1 : (((List.finRange 7).erase 1).permutations'.all fun L =>
    !Nat.testBit pair5_m21 (SVC.lehmerAux (1 :: L)) || (exclOK [] pair5_D pair5_EA (1 :: L) || pair5_B2.all (gramBad pair5_EA pair5_EB (1 :: L)))) = true := by
  decide +kernel
private theorem pair5_hm21_2 : (((List.finRange 7).erase 2).permutations'.all fun L =>
    !Nat.testBit pair5_m21 (SVC.lehmerAux (2 :: L)) || (exclOK [] pair5_D pair5_EA (2 :: L) || pair5_B2.all (gramBad pair5_EA pair5_EB (2 :: L)))) = true := by
  decide +kernel
private theorem pair5_hm21_3 : (((List.finRange 7).erase 3).permutations'.all fun L =>
    !Nat.testBit pair5_m21 (SVC.lehmerAux (3 :: L)) || (exclOK [] pair5_D pair5_EA (3 :: L) || pair5_B2.all (gramBad pair5_EA pair5_EB (3 :: L)))) = true := by
  decide +kernel
private theorem pair5_hm21_4 : (((List.finRange 7).erase 4).permutations'.all fun L =>
    !Nat.testBit pair5_m21 (SVC.lehmerAux (4 :: L)) || (exclOK [] pair5_D pair5_EA (4 :: L) || pair5_B2.all (gramBad pair5_EA pair5_EB (4 :: L)))) = true := by
  decide +kernel
private theorem pair5_hm21_5 : (((List.finRange 7).erase 5).permutations'.all fun L =>
    !Nat.testBit pair5_m21 (SVC.lehmerAux (5 :: L)) || (exclOK [] pair5_D pair5_EA (5 :: L) || pair5_B2.all (gramBad pair5_EA pair5_EB (5 :: L)))) = true := by
  decide +kernel
private theorem pair5_hm21_6 : (((List.finRange 7).erase 6).permutations'.all fun L =>
    !Nat.testBit pair5_m21 (SVC.lehmerAux (6 :: L)) || (exclOK [] pair5_D pair5_EA (6 :: L) || pair5_B2.all (gramBad pair5_EA pair5_EB (6 :: L)))) = true := by
  decide +kernel

theorem pair5_hm21 : (List.finRange 7).permutations'.all (fun L =>
    !Nat.testBit pair5_m21 (SVC.lehmerAux L) || (exclOK [] pair5_D pair5_EA L || pair5_B2.all (gramBad pair5_EA pair5_EB L))) = true := by
  refine perms7_split _ (fun a => ?_)
  fin_cases a
  exacts [pair5_hm21_0, pair5_hm21_1, pair5_hm21_2, pair5_hm21_3, pair5_hm21_4, pair5_hm21_5, pair5_hm21_6]

end Minimality.PL29
