# Noperts

<!-- TODO(tom7): prose. Everything below is just raw facts as a starting point. -->

## The Septopert

The convex hull of these 7 points. Each coordinate is an integer divided by
1048576 (2^20):

```
-940638   327651   327651
 327651  -940638   327651
 327651   327651  -940638
 703968    47788    47788
  47788   703968    47788
  47788    47788   703968
-514207  -514207  -514207
```

These are exactly the points `vertexQ` in
`proof/Noperthedron/Septopert/ModelData.lean`, the vertices the proof is
about. In lowest terms:

| vertex | x | y | z |
|---|---|---|---|
| 0 | −470319/524288 | 327651/1048576 | 327651/1048576 |
| 1 | 327651/1048576 | −470319/524288 | 327651/1048576 |
| 2 | 327651/1048576 | 327651/1048576 | −470319/524288 |
| 3 | 21999/32768 | 11947/262144 | 11947/262144 |
| 4 | 11947/262144 | 21999/32768 | 11947/262144 |
| 5 | 11947/262144 | 11947/262144 | 21999/32768 |
| 6 | −514207/1048576 | −514207/1048576 | −514207/1048576 |

- Every coordinate is exactly representable in binary. A float32 file (e.g.
  STL) only approximates them.
- The Lean statement is about these points unscaled (max |v| ≈ 0.99999935).
  The integer form is the same solid scaled by 2^20.
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
- In the code: `Septopert` (Lean) and `septopert` (file names, search code).

See BUILDING.md for building and verifying.
