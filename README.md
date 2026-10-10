# Noperts

TODO(tom7): Write about this repository

## The Septopert

![The Septopert, spinning around with confidence](septopert.gif)

These seven vertices:

```
(-940638,   327651,   327651)
( 327651,  -940638,   327651)
( 327651,   327651,  -940638)
( 703968,    47788,    47788)
(  47788,   703968,    47788)
(  47788,    47788,   703968)
(-514207,  -514207,  -514207)
```

In the proof (`proof/Septopert.lean`) we divide everything by 2^20
(1048576) so that the radius of the solid is close to 1, which you
might want to do too, unless you want a REALLY BIG nopert. Rupertness
is invariant of scale and rigid transformations.

- Every coordinate is exactly representable in binary. A float32 file (e.g.
  STL) only approximates them.
- Symmetry: C3v, with the 3-fold axis along (1,1,1). Vertices 0–2 are the
  permutations of (a, b, b), and vertices 3–5 the permutations of (c, d, d).
  Vertex 6 is e·(1,1,1).
- Combinatorics: 10 triangular faces, vertex degrees 5,5,5 (0–2), 4,4,4
  (3–5) and 3 (vertex 6). It is a gyroelongated triangular pyramid: a
  triangular antiprism (0–5) with a pyramid (apex 6) on the larger face
  0-1-2.
- Viewed down the axis from the small face: a triforce. Triangle 3-4-5
  projects to within 3.5% of the medial triangle of 0-1-2, and vertex 6 is
  hidden behind the centre.

See BUILDING.md for building and verifying.



## Credits and brief history

This work builds heavily on the [Noperthedron formalization](https://github.com/jcreedcmu/Noperthedron) by Jason Reed, David Renshaw, and others. That is a formalization of Jakob Steininger and Sergey Yurkevich's paper [*A convex polyhedron without Rupert's property*](https://arxiv.org/abs/2508.18475) ("SY25") which introduces the Noperthedron and its original verification.

AI: Embarrasingly much AI is involved here. David did the initial attempt at proving my "Candidate 214" (as well as some other unsolved solids). This required extending the mathematics to deal with non–point-symmetric solids, among other things. He used **(TODO: what models?)** for that. But he actually ended up discovering that my #214 [is Rupert](https://youtu.be/XFeKRSN9l9w). I picked it up from there with the goal of repairing #214 to redeem myself. Using Antigravity (Gemini 3.7 and 3.8 Flash) and Claude Code (Opus 5.5) I verified a repaired, identical-looking shape #231. This proof was not easy, and does use ideas from my [original attempt at proving the snub cube the first Nopert](https://youtu.be/QH4MviUE0_s) but you can tell how much of it is actually AI by the fact that I completed it while on vacationing in Greece! It was briefly the smallest proven Nopert with 20 vertices and 27 faces. 

Meanwhile we learned that earlier this year, Tony Zeng [proposed](https://arxiv.org/pdf/2604.26531) a much smaller solid (8 vertices) as a candidate Nopert. David was able to [verify it](https://github.com/dwrensha/StellatedTetrahedron/tree/main) in Lean using the improved machinery. 

This stood as the smallest proven Nopert for about one day. I had been simultaneously racing to verify a 7-vertex shape, the Septopert described above, that I found with computer search using my adversarial solvers. It is only just barely Nopert, so the proof requires a large certificate (7 gigabytes of packed data). I verified that on Oct 9, taking about 4 hours on a 64-core behemoth.

The natural question is then: Can we find a six-vertex Nopert? Could we prove that every tetrahedron or pentahedron is Rupert? Starting from some ideas of Jason's from 2025 and I like to think some wise guidance from its academic advisor (me), Opus 5.5 was able to prove this in about a day (Lean kernel-only proof): All convex solids with six or fewer vertices are Rupert. That means that the Septopert is a minimal (by vertex count) Nopert.
