#include <iostream>
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
  std::string target = "031213002112122012121";
  TriangleQ tri = TriangleFromPath(target);

  ContactInfo contacts[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(10, 15, 15, 19, 500, 15)
  };

  AxisCertificate cert;
  BigVecQ3 center;
  BigRat delta;
  std::string err;
  if (!Tube229::AuditAxis(tri, contacts, &cert, &center, &delta, &err, BigRat(0))) {
    std::cerr << "Audit failed: " << err << "\n";
    return 1;
  }

  std::cout << "def candidate2CoreAxis : AxisCertificate := {\n";
  std::cout << "  edgeStart := fun | 0 => " << cert.contacts[0].edge_start
            << " | 1 => " << cert.contacts[1].edge_start
            << " | 2 => " << cert.contacts[2].edge_start << "\n";
  std::cout << "  edgeFinish := fun | 0 => " << cert.contacts[0].edge_finish
            << " | 1 => " << cert.contacts[1].edge_finish
            << " | 2 => " << cert.contacts[2].edge_finish << "\n";
  std::cout << "  edgeStart₂ := fun | 0 => " << cert.contacts[0].edge_start2
            << " | 1 => " << cert.contacts[1].edge_start2
            << " | 2 => " << cert.contacts[2].edge_start2 << "\n";
  std::cout << "  edgeFinish₂ := fun | 0 => " << cert.contacts[0].edge_finish2
            << " | 1 => " << cert.contacts[1].edge_finish2
            << " | 2 => " << cert.contacts[2].edge_finish2 << "\n";
  std::cout << "  mix := fun | 0 => ⟨" << cert.contacts[0].mix << ", by decide⟩"
            << " | 1 => ⟨" << cert.contacts[1].mix << ", by decide⟩"
            << " | 2 => ⟨" << cert.contacts[2].mix << ", by decide⟩\n";
  std::cout << "  index := fun | 0 => " << cert.contacts[0].vertex
            << " | 1 => " << cert.contacts[1].vertex
            << " | 2 => " << cert.contacts[2].vertex << "\n";
  std::cout << "  nonzeroWitness := fun | 0 => " << cert.nonzero_witness[0]
            << " | 1 => " << cert.nonzero_witness[1]
            << " | 2 => " << cert.nonzero_witness[2] << "\n";
  std::cout << "  B := " << cert.B.ToString() << "\n";
  std::cout << "}\n";

  std::cout << "// center = (" << center.x.ToString() << ", " << center.y.ToString() << ", " << center.z.ToString() << ")\n";
  std::cout << "// delta = " << delta.ToString() << "\n";
  return 0;
}
