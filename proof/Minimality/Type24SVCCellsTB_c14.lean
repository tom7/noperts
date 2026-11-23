module

public import Minimality.SVCTieBreak
public import Minimality.Type24SVCCells
public import Minimality.Type24TBData_c14

@[expose] public section

set_option autoImplicit false
open scoped RealInnerProductSpace
open Minimality Minimality.H21 Minimality.SVCC Minimality.SVCC.Cells Minimality.T24.SAT Minimality.SVC

namespace Minimality.SVCC.CellsTB

theorem c14_tbCheck :
    tbCheck s0x_S24 c14_P c14_sw [] c14_D c14_R c14_vacs c14_certs = true := by
  decide +kernel

end Minimality.SVCC.CellsTB
