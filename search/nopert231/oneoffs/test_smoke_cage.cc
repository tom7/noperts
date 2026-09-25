#include <iostream>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

static ContactInfo MakeContact(int start, int finish, int start2, int finish2, int mix, int v) {
  ContactInfo c;
  c.edge_start = start;
  c.edge_finish = finish;
  c.edge_start2 = start2;
  c.edge_finish2 = finish2;
  c.mix = mix;
  c.vertex = v;
  return c;
}

int main() {
  std::string path = "031213002112122012121";
  TriangleQ tri = TriangleFromPath(path);

  TubeCertificate cert;

  // Axis 0: cert_hull
  // edgeStart := ![3, 1, 10], edgeFinish := ![2, 4, 15], edgeStart₂ := ![2, 4, 15], edgeFinish₂ := ![1, 8, 19]
  // mix := ![800, 800, 800], index := ![2, 4, 15], nonzeroWitness := ![9, 15, 1], B := 18061 / 10000
  cert.axes[0].contacts[0] = MakeContact(3, 2, 2, 1, 800, 2);
  cert.axes[0].contacts[1] = MakeContact(1, 4, 4, 8, 800, 4);
  cert.axes[0].contacts[2] = MakeContact(10, 15, 15, 19, 800, 15);
  cert.axes[0].nonzero_witness[0] = 9; cert.axes[0].nonzero_witness[1] = 15; cert.axes[0].nonzero_witness[2] = 1;
  cert.axes[0].B = BigRat(18061, 10000);

  // Axis 1: cert1
  // edgeStart := ![15, 2, 8], edgeFinish := ![19, 1, 9], edgeStart₂ := ![19, 1, 9], edgeFinish₂ := ![3, 4, 10]
  // mix := ![200, 200, 200], index := ![19, 1, 9], nonzeroWitness := ![8, 15, 2], B := 898481993 / 1000000000
  cert.axes[1].contacts[0] = MakeContact(15, 19, 19, 3, 200, 19);
  cert.axes[1].contacts[1] = MakeContact(2, 1, 1, 4, 200, 1);
  cert.axes[1].contacts[2] = MakeContact(8, 9, 9, 10, 200, 9);
  cert.axes[1].nonzero_witness[0] = 8; cert.axes[1].nonzero_witness[1] = 15; cert.axes[1].nonzero_witness[2] = 2;
  cert.axes[1].B = BigRat(898481993, 1000000000);

  // Axis 2: cert2
  // edgeStart := ![2, 10, 10], edgeFinish := ![1, 15, 15], edgeStart₂ := ![1, 15, 15], edgeFinish₂ := ![4, 19, 19]
  // mix := ![0, 333, 0], index := ![1, 15, 15], nonzeroWitness := ![15, 1, 4], B := 254450361 / 500000000
  cert.axes[2].contacts[0] = MakeContact(2, 1, 1, 4, 0, 1);
  cert.axes[2].contacts[1] = MakeContact(10, 15, 15, 19, 333, 15);
  cert.axes[2].contacts[2] = MakeContact(10, 15, 15, 19, 0, 15);
  cert.axes[2].nonzero_witness[0] = 15; cert.axes[2].nonzero_witness[1] = 1; cert.axes[2].nonzero_witness[2] = 4;
  cert.axes[2].B = BigRat(254450361, 500000000);

  // Axis 3: cert3
  // edgeStart := ![3, 4, 14], edgeFinish := ![2, 8, 15], edgeStart₂ := ![2, 8, 15], edgeFinish₂ := ![1, 9, 19]
  // mix := ![800, 800, 800], index := ![2, 8, 15], nonzeroWitness := ![9, 19, 1], B := 264825469 / 200000000
  cert.axes[3].contacts[0] = MakeContact(3, 2, 2, 1, 800, 2);
  cert.axes[3].contacts[1] = MakeContact(4, 8, 8, 9, 800, 8);
  cert.axes[3].contacts[2] = MakeContact(14, 15, 15, 19, 800, 15);
  cert.axes[3].nonzero_witness[0] = 9; cert.axes[3].nonzero_witness[1] = 19; cert.axes[3].nonzero_witness[2] = 1;
  cert.axes[3].B = BigRat(264825469, 200000000);

  for (int a = 0; a < 4; a++) {
    AxisCertificate ax;
    BigVecQ3 center;
    BigRat delta;
    std::string err;
    bool ok = Tube229::AuditAxis(tri, cert.axes[a].contacts, &ax, &center, &delta, &err);
    std::cout << "Axis " << a << " audit ok=" << ok << " err=" << err << "\n";
    std::cout << "  center = (" << center.x.ToDouble() << ", " << center.y.ToDouble() << ", " << center.z.ToDouble() << ")\n";
  }

  // Now check if {cert_hull, cert1, cert2, cert3} cage the origin
  TubeCertificate test_c = cert;
  TubeCertificate out_c;
  std::string fail;
  bool cage_ok = Tube229::AuditCertificateAdaptive(tri, test_c, &out_c, &fail);
  std::cout << "Adaptive cage of {cert_hull, sib1, sib2, sib3}: ok=" << cage_ok
            << " err=" << fail
            << " c=" << out_c.c.ToString() << " (" << out_c.c.ToDouble() << ")"
            << " r=" << out_c.r.ToString() << " (" << out_c.r.ToDouble() << ")\n";
  return 0;

  return 0;
}
