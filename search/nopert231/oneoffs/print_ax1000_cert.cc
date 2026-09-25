#include <iostream>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);
  ContactInfo c_1000[3] = {
    {3, 2, 2, 1, 800, 2},
    {1, 4, 4, 8, 800, 4},
    {13, 14, 14, 15, 1000, 14}
  };
  AxisCertificate ax; BigVecQ3 ctr; BigRat del; std::string err;
  Tube229::AuditAxis(tri, c_1000, &ax, &ctr, &del, &err, BigRat(1, 1000));

  std::cout << "-- delta = " << del.ToDouble() << " = " << del.Numerator().ToString() << " / " << del.Denominator().ToString() << "\n";
  std::cout << "def coreAxSingle : AxisCertificate := {\n";
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
  std::cout << "}\n";

  return 0;
}
