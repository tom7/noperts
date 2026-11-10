module

public import SeptopertShell.Parse

/-!
# The shell certificate data

The certificate of the watertight Rupert shell (27 slabs and the closure), inlined from `data/shell.txt` at compile
time. It is untrusted: `checkSeptopertShell` parses it (`parseShell`) and evaluates `ClosureData.checkPar` natively;
on success it instantiates `islandEnclosed_of_closureData`. Regenerate with nopert229
`out/bottleneck/famcensus/islandmap/bnd/shell_build.sh` (then `merge.py`).
-/

@[expose] public section

namespace SeptopertShell

/-- The certificate text. -/
def shellText : String := include_str "data/shell.txt"

end SeptopertShell

end
