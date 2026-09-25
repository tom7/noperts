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

static void PrintLeanCert(int idx, const AxisCertificate &ax) {
  std::cout << "def compAxis" << idx << " : AxisCertificate := {\n";
  std::cout << "  edgeStart := ![" << ax.contacts[0].edge_start << ", " << ax.contacts[1].edge_start << ", " << ax.contacts[2].edge_start << "]\n";
  std::cout << "  edgeFinish := ![" << ax.contacts[0].edge_finish << ", " << ax.contacts[1].edge_finish << ", " << ax.contacts[2].edge_finish << "]\n";
  std::cout << "  edgeStart₂ := ![" << ax.contacts[0].edge_start2 << ", " << ax.contacts[1].edge_start2 << ", " << ax.contacts[2].edge_start2 << "]\n";
  std::cout << "  edgeFinish₂ := ![" << ax.contacts[0].edge_finish2 << ", " << ax.contacts[1].edge_finish2 << ", " << ax.contacts[2].edge_finish2 << "]\n";
  std::cout << "  mix := ![" << ax.contacts[0].mix << ", " << ax.contacts[1].mix << ", " << ax.contacts[2].mix << "]\n";
  std::cout << "  index := ![" << ax.contacts[0].vertex << ", " << ax.contacts[1].vertex << ", " << ax.contacts[2].vertex << "]\n";
  std::cout << "  nonzeroWitness := ![" << ax.nonzero_witness[0] << ", " << ax.nonzero_witness[1] << ", " << ax.nonzero_witness[2] << "]\n";
  std::cout << "  B := " << ax.B.ToString() << "\n";
  std::cout << "}\n\n";
}

int main() {
  std::string target = "031213002112122012121";
  TriangleQ tri = TriangleFromPath(target);

  ContactInfo c1[3] = {
    MakeContact(2, 1, 1, 4, 500, 1),
    MakeContact(10, 15, 15, 19, 666, 15),
    MakeContact(3, 2, 2, 1, 0, 2)
  };
  ContactInfo c2[3] = {
    MakeContact(3, 2, 2, 1, 500, 2),
    MakeContact(8, 9, 9, 10, 200, 9),
    MakeContact(3, 2, 2, 1, 666, 2)
  };
  ContactInfo c3[3] = {
    MakeContact(2, 1, 1, 4, 333, 1),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(10, 15, 15, 19, 200, 15)
  };

  AxisCertificate ax1, ax2, ax3;
  BigVecQ3 ctr1, ctr2, ctr3;
  BigRat del1, del2, del3;
  std::string err;

  if (Tube229::AuditAxis(tri, c1, &ax1, &ctr1, &del1, &err)) PrintLeanCert(1, ax1);
  else std::cout << "ax1 failed: " << err << "\n";
  if (Tube229::AuditAxis(tri, c2, &ax2, &ctr2, &del2, &err)) PrintLeanCert(2, ax2);
  else std::cout << "ax2 failed: " << err << "\n";
  if (Tube229::AuditAxis(tri, c3, &ax3, &ctr3, &del3, &err)) PrintLeanCert(3, ax3);
  else std::cout << "ax3 failed: " << err << "\n";

  return 0;
}
