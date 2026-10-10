import Pipeline.FundamentalChart3
import PentagonalHexecontahedron
import SnubDodecahedron

/-!
# The four-row chart-3 table, checked by the kernel

The executables check `Pipeline.FundamentalChart3.table` natively, with the
other charts. Here the kernel checks it too, for each solid that uses it (the
table is the same; its validity reads the solid's model).
-/

open Noperts.Pipeline AtlasProjectiveSolutionTree FundamentalChart3

section
open PentagonalHexecontahedron

theorem pentagonalHexecontahedron_chart3_valid : table.Valid := by
  refine ⟨by decide, rowsValidAt_of_range (by decide +kernel), ?_, ?_, ?_⟩
  · decide +kernel
  · decide +kernel
  · trivial

end

section
open SnubDodecahedron

theorem snubDodecahedron_chart3_valid : table.Valid := by
  refine ⟨by decide, rowsValidAt_of_range (by decide +kernel), ?_, ?_, ?_⟩
  · decide +kernel
  · decide +kernel
  · trivial

end
