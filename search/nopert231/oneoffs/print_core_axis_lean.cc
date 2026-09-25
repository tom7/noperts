#include <iostream>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

static ContactInfo MakeContact(int start, int finish, int start2, int finish2, int mix, int v) {
  ContactInfo c;
  c.edge_start = start; c.edge_finish = finish;
  c.edge_start2 = start2; c.edge_finish2 = finish2;
  c.mix = mix; c.vertex = v;
  return c;
}

int main() {
  std::string target_path = "03121303200";
  TriangleQ tri = TriangleFromPath(target_path);

  ContactInfo c_core[3] = {
    MakeContact(1, 4, 4, 8, 1000, 4),
    MakeContact(10, 15, 15, 19, 400, 15),
    MakeContact(10, 15, 15, 19, 0, 15)
  };

  AxisCertificate ax;
  BigVecQ3 ctr; BigRat del; std::string err;
  bool ok = Tube229::AuditAxis(tri, c_core, &ax, &ctr, &del, &err, BigRat(0));
  std::cout << "audit ok=" << ok << " err=" << err << "\n";
  std::cout << "B = " << ax.B.ToString() << "\n";
  std::cout << "delta = " << del.ToString() << "\n";
  std::cout << "nonzeroWitness = ![" << ax.nonzero_witness[0] << ", " << ax.nonzero_witness[1] << ", " << ax.nonzero_witness[2] << "]\n";
  std::cout << "ctr = (" << ctr.x.ToString() << ", " << ctr.y.ToString() << ", " << ctr.z.ToString() << ")\n";

  std::cout << "\nLean definition:\n";
  std::cout << "def coreAxis : AxisCertificate := {\n";
  std::cout << "  edgeStart := ![" << c_core[0].edge_start << ", " << c_core[1].edge_start << ", " << c_core[2].edge_start << "],\n";
  std::cout << "  edgeFinish := ![" << c_core[0].edge_finish << ", " << c_core[1].edge_finish << ", " << c_core[2].edge_finish << "],\n";
  std::cout << "  edgeStart₂ := ![" << c_core[0].edge_start2 << ", " << c_core[1].edge_start2 << ", " << c_core[2].edge_start2 << "],\n";
  std::cout << "  edgeFinish₂ := ![" << c_core[0].edge_finish2 << ", " << c_core[1].edge_finish2 << ", " << c_core[2].edge_finish2 << "],\n";
  std::cout << "  mix := ![" << c_core[0].mix << ", " << c_core[1].mix << ", " << c_core[2].mix << "],\n";
  std::cout << "  index := ![" << c_core[0].vertex << ", " << c_core[1].vertex << ", " << c_core[2].vertex << "],\n";
  std::cout << "  nonzeroWitness := ![" << ax.nonzero_witness[0] << ", " << ax.nonzero_witness[1] << ", " << ax.nonzero_witness[2] << "],\n";
  std::cout << "  B := " << ax.B.ToString() << "\n";
  std::cout << "}\n";

  return 0;
}
