import re, sys
# Switch a type file's plain vertex views (isRupert_of_facets_vertex, one face a triangle) to the
# tie version, weakening that view's TriGenFar hypothesis to TriGenTri.
fn = sys.argv[1]; s = open(fn).read()
sets = dict(re.findall(r"set (Q\w+) := (\(\{[\d, ]+\} : Finset \(Fin 7\)\))\.image x", s))
pat = re.compile(r"( *)refine isRupert_of_facets_vertex V hgen (Q\w+) (Q\w+) \(sub _\) \(sub _\) (\(isFacet_of_index x _ \w+ \w+\))\n *(\(isFacet_of_index x _ \w+ \w+\)) \(x (\d)\) \?_\n *(⟨.*⟩)\n *(⟨.*⟩) (hT\d) \?_\n *· rw \[inter, show (\(\{[\d, ]+\} ∩ \{[\d, ]+\} : Finset \(Fin 7\)\)) = \{\d\} by decide\]\n *simp\n")
changed = []
def sub(m):
    ind, QX, QY, FX, FY, k, n1, n2, hT, inter = m.groups()
    sx, sy = sets[QX], sets[QY]
    size = lambda st: len(re.search(r"\{([\d, ]+)\}", st).group(1).split(','))
    if size(sx) == 3: card, st = 'Or.inl', sx
    elif size(sy) == 3: card, st = 'Or.inr', sy
    else: return m.group(0)
    changed.append(hT)
    I = ind; J = ind + '  '
    return (f"{I}have hiv{hT} : {QX} ∩ {QY} = {{x {k}}} := by\n{J}rw [inter, show {inter} = {{{k}}} by decide]\n{J}simp\n"
            f"{I}refine isRupert_of_facets_vertex_tie V hgen {QX} {QY} (sub _) (sub _) {FX}\n"
            f"{J}{FY} (x {k}) hiv{hT}\n{J}{n1}\n{J}{n2}\n"
            f"{J}({hT}.tie (sub _) (sub _) hiv{hT}\n{J}  ({card} (by show ({st}.image x).card = 3; rw [Finset.card_image_of_injective _ hx]; decide))) ?_\n")
s = pat.sub(sub, s)
for hT in changed:
    s = re.sub(r"\((" + hT + r") : TriGenFar ", r"(\1 : TriGenTri ", s)
if changed and 'Minimality.TriTie' not in s:
    s = s.replace("public import Minimality.TriFacetsChord\n", "public import Minimality.TriFacetsChord\npublic import Minimality.TriTie\n", 1)
    if 'Minimality.TriTie' not in s:
        s = re.sub(r"(public import Minimality\.\w+\n)", r"\1public import Minimality.TriTie\n", s, count=1)
open(fn, 'w').write(s)
print(fn, 'tie views:', changed)
