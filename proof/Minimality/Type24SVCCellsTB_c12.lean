module

public import Minimality.SVCTieBreak
public import Minimality.Type24SVCCells
public import Minimality.Type24TBData_c12

@[expose] public section

set_option autoImplicit false
open scoped RealInnerProductSpace
open Minimality Minimality.H21 Minimality.SVCC Minimality.SVCC.Cells Minimality.T24.SAT Minimality.SVC

namespace Minimality.SVCC.CellsTB

theorem c12_tbCheck :
    tbCheck s0x_S24 c12_P c12_sw [] c12_D c12_R c12_vacs c12_certs = true := by
  decide +kernel

end Minimality.SVCC.CellsTB
