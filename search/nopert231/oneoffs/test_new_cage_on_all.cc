#include <iostream>
#include <vector>
#include "tube229.h"
#include "tubetree229.h"
#include "bignum/big-overloads.h"

using namespace tubetree229;

static ContactInfo MakeContact(int start, int finish, int start2, int finish2, int mix, int v) {
  ContactInfo c;
  c.edge_start = start; c.edge_finish = finish;
  c.edge_start2 = start2; c.edge_finish2 = finish2;
  c.mix = mix; c.vertex = v;
  return c;
}

int main() {
  ContactInfo contacts[4][3] = {
    // Axis 0 (annular, with v14)
    {MakeContact(3, 2, 2, 1, 800, 2), MakeContact(1, 4, 4, 8, 800, 4), MakeContact(13, 14, 14, 15, 200, 14)},
    // Axis 1
    {MakeContact(2, 1, 1, 4, 0, 1), MakeContact(10, 15, 15, 19, 800, 15), MakeContact(3, 2, 2, 1, 1000, 2)},
    // Axis 2
    {MakeContact(2, 1, 1, 4, 0, 1), MakeContact(8, 9, 9, 10, 1000, 9), MakeContact(15, 19, 19, 3, 0, 19)},
    // Axis 3
    {MakeContact(2, 1, 1, 4, 0, 1), MakeContact(9, 10, 10, 15, 200, 10), MakeContact(10, 15, 15, 19, 0, 15)}
  };

  std::vector<std::string> leaves = {
    "03121300",
    "03121303021",
    "03121303022",
    "03121303023",
    "03121303200",
    "0312130332"
  };

  for (const auto &path : leaves) {
    std::cout << "\n========================================\n";
    std::cout << "Testing leaf " << path << ":\n";
    TriangleQ tri = TriangleFromPath(path);
    AxisCertificate axes[4];
    BigVecQ3 centers[4];
    BigRat deltas[4];
    bool ok = true;
    for (int a = 0; a < 4; a++) {
      std::string err;
      BigRat max_def = (a == 0 ? BigRat(5, 1000) : BigRat(0));
      if (!Tube229::AuditAxis(tri, contacts[a], &axes[a], &centers[a], &deltas[a], &err, max_def)) {
        std::cout << "  Axis " << a << " audit failed: " << err << "\n";
        ok = false;
        break;
      }
    }
    if (!ok) continue;

    BigRat max_delta = deltas[0];
    for (int a = 1; a < 4; a++) if (deltas[a] > max_delta) max_delta = deltas[a];

    BigRat inrad = Tube229::ExactTetrahedronAxisRadius(centers);
    std::cout << "  Exact inradius: " << inrad.ToDouble() << "\n";
    std::cout << "  Max delta: " << max_delta.ToDouble() << "\n";
    BigRat c_eff = inrad * BigRat(4, 7) - max_delta;
    std::cout << "  Effective margin c_eff: " << c_eff.ToDouble() << "\n";
  }

  return 0;
}
