module

public import Minimality.Type16SAT.KDec16

@[expose] public section

/-! Scoped ASCII notations for the generated type 16 `Data*` files (`open scoped Minimality.SatNotation16`).
    All expand to the explicit terms (untrusted data: a wrong rewrite cannot prove anything, `Chk*` checks it).
    * `#x a b ..` is the literal `((true, W.base (V.x a b ..)) : LitW)`, `#nx ..` the same with `V.ng`;
    * `##x a b ..` is the `W` entry `W.base (V.x a b ..)`, `##nx ..` with `V.ng`;
    * `a & b` is `andW a b`, `a ~| b` is `andW a.neg b.neg` (NOR), `NOT a` is `LitW.neg a`. -/

open Minimality.H16K.SAT Minimality.H16T.SAT Minimality.H16.SAT Minimality.H29.SAT

namespace Minimality.SatNotation16

scoped notation:max "NOT " a:max => LitW.neg a
scoped notation:35 a:36 " & " b:36 => andW a b
scoped notation:35 a:36 " ~| " b:36 => andW (LitW.neg a) (LitW.neg b)
scoped notation:max "#br " a:max b:max c:max d:max => ((true, W.base (V.br a b c d)) : LitW)
scoped notation:max "#nbr " a:max b:max c:max d:max => ((true, W.base (V.ng (V.br a b c d))) : LitW)
scoped notation:max "##br " a:max b:max c:max d:max => W.base (V.br a b c d)
scoped notation:max "##nbr " a:max b:max c:max d:max => W.base (V.ng (V.br a b c d))
scoped notation:max "#fv " a:max b:max c:max => ((true, W.base (V.fv a b c)) : LitW)
scoped notation:max "#nfv " a:max b:max c:max => ((true, W.base (V.ng (V.fv a b c))) : LitW)
scoped notation:max "##fv " a:max b:max c:max => W.base (V.fv a b c)
scoped notation:max "##nfv " a:max b:max c:max => W.base (V.ng (V.fv a b c))
scoped notation:max "#kv " a:max b:max c:max => ((true, W.base (V.kv a b c)) : LitW)
scoped notation:max "#nkv " a:max b:max c:max => ((true, W.base (V.ng (V.kv a b c))) : LitW)
scoped notation:max "##kv " a:max b:max c:max => W.base (V.kv a b c)
scoped notation:max "##nkv " a:max b:max c:max => W.base (V.ng (V.kv a b c))
scoped notation:max "#lv " a:max b:max c:max d:max e:max => ((true, W.base (V.lv a b c d e)) : LitW)
scoped notation:max "#nlv " a:max b:max c:max d:max e:max => ((true, W.base (V.ng (V.lv a b c d e))) : LitW)
scoped notation:max "##lv " a:max b:max c:max d:max e:max => W.base (V.lv a b c d e)
scoped notation:max "##nlv " a:max b:max c:max d:max e:max => W.base (V.ng (V.lv a b c d e))
scoped notation:max "#mv " a:max b:max c:max => ((true, W.base (V.mv a b c)) : LitW)
scoped notation:max "#nmv " a:max b:max c:max => ((true, W.base (V.ng (V.mv a b c))) : LitW)
scoped notation:max "##mv " a:max b:max c:max => W.base (V.mv a b c)
scoped notation:max "##nmv " a:max b:max c:max => W.base (V.ng (V.mv a b c))
scoped notation:max "#nv " a:max b:max c:max => ((true, W.base (V.nv a b c)) : LitW)
scoped notation:max "#nnv " a:max b:max c:max => ((true, W.base (V.ng (V.nv a b c))) : LitW)
scoped notation:max "##nv " a:max b:max c:max => W.base (V.nv a b c)
scoped notation:max "##nnv " a:max b:max c:max => W.base (V.ng (V.nv a b c))
scoped notation:max "#tp " a:max b:max => ((true, W.base (V.tp a b)) : LitW)
scoped notation:max "#ntp " a:max b:max => ((true, W.base (V.ng (V.tp a b))) : LitW)
scoped notation:max "##tp " a:max b:max => W.base (V.tp a b)
scoped notation:max "##ntp " a:max b:max => W.base (V.ng (V.tp a b))
scoped notation:max "#tpv " a:max b:max c:max => ((true, W.base (V.tpv a b c)) : LitW)
scoped notation:max "#ntpv " a:max b:max c:max => ((true, W.base (V.ng (V.tpv a b c))) : LitW)
scoped notation:max "##tpv " a:max b:max c:max => W.base (V.tpv a b c)
scoped notation:max "##ntpv " a:max b:max c:max => W.base (V.ng (V.tpv a b c))
scoped notation:max "#tq " a:max b:max => ((true, W.base (V.tq a b)) : LitW)
scoped notation:max "#ntq " a:max b:max => ((true, W.base (V.ng (V.tq a b))) : LitW)
scoped notation:max "##tq " a:max b:max => W.base (V.tq a b)
scoped notation:max "##ntq " a:max b:max => W.base (V.ng (V.tq a b))
scoped notation:max "#yv " a:max b:max c:max d:max e:max => ((true, W.base (V.yv a b c d e)) : LitW)
scoped notation:max "#nyv " a:max b:max c:max d:max e:max => ((true, W.base (V.ng (V.yv a b c d e))) : LitW)
scoped notation:max "##yv " a:max b:max c:max d:max e:max => W.base (V.yv a b c d e)
scoped notation:max "##nyv " a:max b:max c:max d:max e:max => W.base (V.ng (V.yv a b c d e))

end Minimality.SatNotation16
