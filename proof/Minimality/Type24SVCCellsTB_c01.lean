module

public import Minimality.SVCTieBreak
public import Minimality.Type24SVCCells
public import Minimality.Type24TBData_c01

@[expose] public section

set_option autoImplicit false
open scoped RealInnerProductSpace
open Minimality Minimality.H21 Minimality.SVCC Minimality.SVCC.Cells Minimality.T24.SAT Minimality.SVC

namespace Minimality.SVCC.CellsTB

theorem c01_tbCheck :
    tbCheck s0x_S24 c01_P c01_sw [] c01_D c01_R c01_vacs c01_certs = true := by
  decide +kernel

end Minimality.SVCC.CellsTB
