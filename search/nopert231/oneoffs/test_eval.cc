#include <cstdio>
#include <vector>

// Forward declare evaluation from lean228.cc
#include "lean228.cc"

int main() {
  ProjectiveTriangle tri;
  tri.corners[0] = {1.0, 0.0, 0.0};
  tri.corners[1] = {10.0 / 41.0, 31.0 / 41.0, 0.0};
  tri.corners[2] = {0.0, 0.0, 1.0};

  auto pool = BuildCandidatesForTriangle(tri);
  printf("Pool at root tri: %zu contacts, %zu triples\n", pool.contacts.size(), pool.triples.size());

  GpuBox box;
  box.cx = -0.8157; box.cy = -0.5077; box.cz = 0.1485;
  box.rx = 0.01; box.ry = 0.01; box.rz = 0.01;
  for (int c = 0; c < 3; c++) {
    box.tri[c][0] = tri.corners[c].x;
    box.tri[c][1] = tri.corners[c].y;
    box.tri[c][2] = tri.corners[c].z;
  }
  box.chart = 0;
  box.triple_offset = 0;
  box.num_triples = pool.triples.size();

  auto res = EvaluateBoxCPU(box, pool.contacts, pool.triples);
  printf("Res: certified=%d, winning_triple=%d, margin=%.8f, inner=(%d, %d, %d)\n",
         res.certified, res.winning_triple, res.margin,
         res.inner[0], res.inner[1], res.inner[2]);
  return 0;
}
