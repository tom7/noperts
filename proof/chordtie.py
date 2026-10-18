import re, sys
# Split a type's chord branch (c <= 0) into c < 0 (tie version, TriGenTri) and c = 0 (chord,
# TriGenFar only then); the view's hypothesis becomes TriGenTri ∧ (special → TriGenFar).
fn = sys.argv[1]; s = open(fn).read()
sets = dict(re.findall(r"set (Q\w+) := (\(\{[\d, ]+\} : Finset \(Fin 7\)\))\.image x", s))
a = s.index("  rcases le_or_gt c 0 with hcl | hcg\n")
b = s.index("\n  · --", a + 50) + 1
br = s[a:b]
m = re.search(r"refine isRupert_of_facets_vertex_chord V hgen (Q\w+) (Q\w+) \(sub _\) \(sub _\)\n *(\(isFacet_of_index x _ \w+ \w+\)) (\(isFacet_of_index x _ \w+ \w+\)) \(x (\d)\) \?_\n *(⟨.*⟩)\n *(⟨.*⟩) (hT\d) \(x (\d)\) \(x (\d)\)\n.*\n.*\(x (\d)\) \(hxV \d\)\n.*\?_\n *· rw \[inter, show (\(.*\)) = \{\d\} by decide\]\n *simp\n *intro (\S+) (\S+) z1 (\S+) z2 (\S+)\n", br)
assert m, 'chord refine'
QX, QY, FX, FY, k, ne1, ne2, hT, xa, xb, yc, inter, f1, f2, n1, n2 = m.groups()
rb = br[br.index("    have e2' :"):]
rw = re.search(r"    rw \[e1', e2', (h\w+)\]\n    nlinarith\n", rb)
assert rw, 'value rw'
hV = rw.group(1); ratio = rb[:rw.start()]
spec = re.search(r"have " + hV + r" : (.*) = 1 \+ \w+ \* c", s).group(1)
size = lambda st: len(re.search(r"\{([\d, ]+)\}", st).group(1).split(','))
if size(sets[QX]) == 3: card, st = 'Or.inl', sets[QX]
elif size(sets[QY]) == 3: card, st = 'Or.inr', sets[QY]
else: raise SystemExit('no triangle')
ind = lambda t: "\n".join(("  " + l if l.strip() else l) for l in t.rstrip("\n").split("\n")) + "\n"
new = f'''  have hiP : {QX} ∩ {QY} = {{x {k}}} := by
    rw [inter, show {inter} = {{{k}}} by decide]
    simp
  rcases le_or_gt c 0 with hcl | hcg
  · rcases hcl.lt_or_eq with hlt | heq
    · -- `c < 0`: the plain view, the tie allowed
      refine isRupert_of_facets_vertex_tie V hgen {QX} {QY} (sub _) (sub _)
        {FX} {FY} (x {k}) hiP
        {ne1}
        {ne2}
        ({hT}.1.tie (sub _) (sub _) hiP
          ({card} (by show ({st}.image x).card = 3
                      rw [Finset.card_image_of_injective _ hx]; decide)))
        ⟨x {xa}, (memQ _ {xa}).mpr (by decide), x {xb}, (memQ _ {xb}).mpr (by decide),
          fun h => by have := hx h; omega, fun h => by have := hx h; omega, ?_⟩
      intro {f1} {f2} z1 {n1} z2 {n2} y hy hy1 hy2
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hy
      rw [memQ] at hy1 hy2
      have hi : i = {yc} := by clear * - hy1 hy2; fin_cases i <;> simp_all
      subst hi
{ind(ratio)}      rw [e1', e2', {hV}]
      nlinarith
    · -- `c = 0`: Lemma T′ (`x{yc}` on the far side)
      refine isRupert_of_facets_vertex_chord V hgen {QX} {QY} (sub _) (sub _)
        {FX} {FY} (x {k}) hiP
        {ne1}
        {ne2} ({hT}.2 (by rw [{hV}, heq]; ring)) (x {xa}) (x {xb})
        ((memQ _ {xa}).mpr (by decide)) ((memQ _ {xb}).mpr (by decide))
        (fun h => by have := hx h; omega) (fun h => by have := hx h; omega) (x {yc}) (hxV {yc})
        (by rw [memQ]; decide) (by rw [memQ]; decide) ?_
      intro {f1} {f2} z1 {n1} z2 {n2}
      refine ⟨fun y hy hy1 hy2 hne => ?_, ?_⟩
      · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hy
        rw [memQ] at hy1 hy2
        have hi : i = {yc} := by clear * - hy1 hy2; fin_cases i <;> simp_all
        exact absurd (by rw [hi]) hne
{ind(ratio)}      rw [e1', e2', {hV}]
      nlinarith
'''
s = s[:a] + new + s[b:]
sig = re.search(r"    \(" + hT + r" : TriGenFar (\(univ\.image x\) \(\(\{[\d, ]+\} : Finset \(Fin 7\)\)\.image x\))\n      (\(\(\{[\d, ]+\} : Finset \(Fin 7\)\)\.image x\) \(x \d\))\)", s)
assert sig, 'sig'
A1, A2 = sig.groups()
s = s[:sig.start()] + f"""    ({hT} : TriGenTri {A1}
        {A2} ∧
      ({spec} = 1 →
        TriGenFar {A1}
          {A2}))""" + s[sig.end():]
open(fn, 'w').write(s)
print(fn, hT, 'special:', spec)
