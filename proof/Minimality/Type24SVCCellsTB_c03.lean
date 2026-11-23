module

public import Minimality.SVCTieBreak
public import Minimality.Type24SVCCells
public import Minimality.Type24TBData_c03

@[expose] public section

set_option autoImplicit false
open scoped RealInnerProductSpace
open Minimality Minimality.H21 Minimality.SVCC Minimality.SVCC.Cells Minimality.T24.SAT Minimality.SVC

namespace Minimality.SVCC.CellsTB

theorem c03_tbCheck :
    tbCheck s0x_S24 c03_P c03_sw [] c03_D c03_R c03_vacs c03_certs = true := by
  decide +kernel

end Minimality.SVCC.CellsTB
