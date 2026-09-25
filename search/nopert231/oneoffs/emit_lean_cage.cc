#include <iostream>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

void EmitLeanAxis(const std::string &name, const AxisCertificate &ax) {
  std::cout << "def " << name << " : AxisCertificate := {\n";
  std::cout << "  edgeStart := ![" << (int)ax.contacts[0].edge_start << ", "
                                  << (int)ax.contacts[1].edge_start << ", "
                                  << (int)ax.contacts[2].edge_start << "],\n";
  std::cout << "  edgeFinish := ![" << (int)ax.contacts[0].edge_finish << ", "
                                   << (int)ax.contacts[1].edge_finish << ", "
                                   << (int)ax.contacts[2].edge_finish << "],\n";
  std::cout << "  edgeStart₂ := ![" << (int)ax.contacts[0].edge_start2 << ", "
                                   << (int)ax.contacts[1].edge_start2 << ", "
                                   << (int)ax.contacts[2].edge_start2 << "],\n";
  std::cout << "  edgeFinish₂ := ![" << (int)ax.contacts[0].edge_finish2 << ", "
                                    << (int)ax.contacts[1].edge_finish2 << ", "
                                    << (int)ax.contacts[2].edge_finish2 << "],\n";
  std::cout << "  mix := ![" << ax.contacts[0].mix << ", "
                             << ax.contacts[1].mix << ", "
                             << ax.contacts[2].mix << "],\n";
  std::cout << "  index := ![" << (int)ax.contacts[0].vertex << ", "
                               << (int)ax.contacts[1].vertex << ", "
                               << (int)ax.contacts[2].vertex << "],\n";
  std::cout << "  nonzeroWitness := ![" << (int)ax.nonzero_witness[0] << ", "
                                        << (int)ax.nonzero_witness[1] << ", "
                                        << (int)ax.nonzero_witness[2] << "],\n";
  std::cout << "  B := " << ax.B.Numerator().ToString() << " / " << ax.B.Denominator().ToString() << "\n";
  std::cout << "}\n\n";
}

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);

  ContactInfo c0[3] = {
    {3, 2, 2, 1, 800, 2},
    {1, 4, 4, 8, 800, 4},
    {13, 14, 14, 15, 200, 14}
  };
  ContactInfo c1[3] = {
    {2, 10, 10, 2, 0, 10},
    {1, 15, 15, 1, 333, 15},
    {4, 19, 19, 4, 333, 19}
  };
  ContactInfo c2[3] = {
    {2, 10, 10, 3, 0, 10},
    {1, 15, 15, 2, 666, 15},
    {4, 19, 19, 1, 0, 19}
  };
  ContactInfo c3[3] = {
    {2, 1, 1, 15, 0, 1},
    {1, 4, 4, 19, 333, 4},
    {4, 8, 8, 3, 1000, 8}
  };

  AxisCertificate ax[4];
  BigVecQ3 ctr[4];
  BigRat del[4];
  std::string err;
  Tube229::AuditAxis(tri, c0, &ax[0], &ctr[0], &del[0], &err, BigRat(1, 1000));
  Tube229::AuditAxis(tri, c1, &ax[1], &ctr[1], &del[1], &err, BigRat(0));
  Tube229::AuditAxis(tri, c2, &ax[2], &ctr[2], &del[2], &err, BigRat(0));
  Tube229::AuditAxis(tri, c3, &ax[3], &ctr[3], &del[3], &err, BigRat(0));

  EmitLeanAxis("ax0", ax[0]);
  EmitLeanAxis("ax1", ax[1]);
  EmitLeanAxis("ax2", ax[2]);
  EmitLeanAxis("ax3", ax[3]);

  return 0;
}
