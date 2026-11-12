module

public import Minimality.Type24SAT.Tie.TCore

@[expose] public section

/-! Scoped ASCII name shorthands for the generated type 24 `Data*` files over `W` (`open scoped Minimality.SatNotation24`).
    All expand to the explicit terms (untrusted data, checked by `Chk*`).
    `#B x` is `W.base x`; `#y a b c d e` is `W.base (V.yv a b c d e)`; `#P`, `#Q` are `tp`, `tq` (two arguments);
    `#F a b c` is `fv`, `#NF a b c` its `ng`, `#Z` is `tpv`; `#nf`, `#nb`, `#nn` are `V.ng` of `fv`, `br`, `nv`;
    `#mfp`, `#mfq`, `#mbp`, `#mbq` are the multiplexer `(fv/br A AND tp/tq P) NOR (ng (fv/br A) AND tq/tp Q)` under `W.base`. -/

open Minimality.H24.SAT Minimality.H29.SAT Minimality.H24T.SAT

namespace Minimality.SatNotation24

scoped notation:max "#nf " a:max b:max c:max => V.ng (V.fv a b c)
scoped notation:max "#nb " a:max b:max c:max d:max => V.ng (V.br a b c d)
scoped notation:max "#nn " a:max b:max c:max => V.ng (V.nv a b c)
scoped notation:max "#B " x:35 => W.base x
scoped notation:max "#y " a:max b:max c:max d:max e:max => W.base (V.yv a b c d e)
scoped notation:max "#P " a:max b:max => W.base (V.tp a b)
scoped notation:max "#Q " a:max b:max => W.base (V.tq a b)
scoped notation:max "#F " a:max b:max c:max => W.base (V.fv a b c)
scoped notation:max "#NF " a:max b:max c:max => W.base (V.ng (V.fv a b c))
scoped notation:max "#Z " a:max b:max c:max => W.base (V.tpv a b c)
scoped notation:max "#mfp " a:max b:max c:max d:max e:max f:max g:max =>
  W.base (V.gate false (V.gate true (V.fv a b c) true (V.tp d e)) false (V.gate true (V.ng (V.fv a b c)) true (V.tq f g)))
scoped notation:max "#mfq " a:max b:max c:max d:max e:max f:max g:max =>
  W.base (V.gate false (V.gate true (V.fv a b c) true (V.tq d e)) false (V.gate true (V.ng (V.fv a b c)) true (V.tp f g)))
scoped notation:max "#mbp " a:max b:max c:max d:max e:max f:max g:max h:max =>
  W.base (V.gate false (V.gate true (V.br a b c d) true (V.tp e f)) false (V.gate true (V.ng (V.br a b c d)) true (V.tq g h)))
scoped notation:max "#mbq " a:max b:max c:max d:max e:max f:max g:max h:max =>
  W.base (V.gate false (V.gate true (V.br a b c d) true (V.tq e f)) false (V.gate true (V.ng (V.br a b c d)) true (V.tp g h)))

end Minimality.SatNotation24
