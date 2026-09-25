#include <iostream>
#include <vector>
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

static void PrintLeanAxis(const std::string &name, const AxisCertificate &ax) {
  std::cout << "def " << name << " : AxisCertificate := {\n";
  std::cout << "  edgeStart := ![" << ax.contacts[0].edge_start << ", " << ax.contacts[1].edge_start << ", " << ax.contacts[2].edge_start << "],\n";
  std::cout << "  edgeFinish := ![" << ax.contacts[0].edge_finish << ", " << ax.contacts[1].edge_finish << ", " << ax.contacts[2].edge_finish << "],\n";
  std::cout << "  edgeStart₂ := ![" << ax.contacts[0].edge_start2 << ", " << ax.contacts[1].edge_start2 << ", " << ax.contacts[2].edge_start2 << "],\n";
  std::cout << "  edgeFinish₂ := ![" << ax.contacts[0].edge_finish2 << ", " << ax.contacts[1].edge_finish2 << ", " << ax.contacts[2].edge_finish2 << "],\n";
  std::cout << "  mix := ![" << ax.contacts[0].mix << ", " << ax.contacts[1].mix << ", " << ax.contacts[2].mix << "],\n";
  std::cout << "  index := ![" << ax.contacts[0].vertex << ", " << ax.contacts[1].vertex << ", " << ax.contacts[2].vertex << "],\n";
  std::cout << "  nonzeroWitness := ![" << ax.nonzero_witness[0] << ", " << ax.nonzero_witness[1] << ", " << ax.nonzero_witness[2] << "],\n";
  std::cout << "  B := " << ax.B.ToString() << "\n";
  std::cout << "}\n\n";
}

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);

  ContactInfo c0[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(13, 14, 14, 15, 200, 14)
  };
  std::string err;
  AxisCertificate ax0; BigVecQ3 ctr0; BigRat del0;
  Tube229::AuditAxis(tri, c0, &ax0, &ctr0, &del0, &err, BigRat(5, 1000));

  auto axes = Tube229::FindAllHullSupportAxes(tri, 500);
  PrintLeanAxis("ax0", ax0);
  PrintLeanAxis("ax1", axes[0].cert);
  PrintLeanAxis("ax2", axes[24].cert);
  PrintLeanAxis("ax3", axes[210].cert);

  return 0;
}
