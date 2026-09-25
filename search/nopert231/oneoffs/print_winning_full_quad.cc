#include <iostream>
#include <iomanip>
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
  std::string path = "03121303200";
  TriangleQ tri = TriangleFromPath(path);

  int m[12] = {
    150, 1000, 882,
    50, 800, 950,
    1000, 1000, 343,
    113, 320, 150
  };

  ContactInfo c[4][3] = {
    { MakeContact(3, 2, 2, 1, m[0], 2),
      MakeContact(1, 4, 4, 8, m[1], 4),
      MakeContact(13, 14, 14, 15, m[2], 14) },
    { MakeContact(2, 1, 1, 4, m[3], 1),
      MakeContact(10, 15, 15, 19, m[4], 15),
      MakeContact(19, 3, 3, 2, m[5], 3) },
    { MakeContact(2, 1, 1, 4, m[6], 1),
      MakeContact(8, 9, 9, 10, m[7], 9),
      MakeContact(9, 10, 10, 15, m[8], 10) },
    { MakeContact(3, 2, 2, 1, m[9], 2),
      MakeContact(1, 4, 4, 8, m[10], 4),
      MakeContact(10, 15, 15, 19, m[11], 15) }
  };

  std::string err;
  AxisCertificate ax[4];
  BigVecQ3 cnt[4];
  BigRat var_radius[4];

  std::cout << "Auditing all 4 axes with exact arithmetic:\n";
  for (int a = 0; a < 4; a++) {
    BigRat max_def = (a == 0 ? BigRat(1, 1000) : BigRat(0));
    bool ok = Tube229::AuditAxis(tri, c[a], &ax[a], &cnt[a], &var_radius[a], &err, max_def);
    std::cout << "Axis " << a << ": Audit = " << (ok ? "OK" : ("FAIL: " + err)) << "\n";
    std::cout << "  B = " << ax[a].B.ToString() << " (" << ax[a].B.ToDouble() << ")\n";
    std::cout << "  max_defect (delta) = " << var_radius[a].ToString() << " (" << var_radius[a].ToDouble() << ")\n";
    std::cout << "  witnesses = [" << ax[a].nonzero_witness[0] << ", "
              << ax[a].nonzero_witness[1] << ", " << ax[a].nonzero_witness[2] << "]\n";
  }

  std::cout << "\n--- LEAN DEFINITIONS ---\n";
  for (int a = 0; a < 4; a++) {
    std::cout << "def ax" << a << " : AxisCertificate := {\n"
              << "  edgeStart := ![" << c[a][0].edge_start << ", " << c[a][1].edge_start << ", " << c[a][2].edge_start << "],\n"
              << "  edgeFinish := ![" << c[a][0].edge_finish << ", " << c[a][1].edge_finish << ", " << c[a][2].edge_finish << "],\n"
              << "  edgeStart₂ := ![" << c[a][0].edge_start2 << ", " << c[a][1].edge_start2 << ", " << c[a][2].edge_start2 << "],\n"
              << "  edgeFinish₂ := ![" << c[a][0].edge_finish2 << ", " << c[a][1].edge_finish2 << ", " << c[a][2].edge_finish2 << "],\n"
              << "  mix := ![" << c[a][0].mix << ", " << c[a][1].mix << ", " << c[a][2].mix << "],\n"
              << "  index := ![" << c[a][0].vertex << ", " << c[a][1].vertex << ", " << c[a][2].vertex << "],\n"
              << "  nonzeroWitness := ![" << ax[a].nonzero_witness[0] << ", "
              << ax[a].nonzero_witness[1] << ", " << ax[a].nonzero_witness[2] << "],\n"
              << "  B := " << ax[a].B.ToString() << "\n"
              << "}\n\n";
  }

  return 0;
}
