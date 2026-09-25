#include <iostream>
#include <string>
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
  std::string parent = "03121303200";
  for (int child = 0; child < 4; child++) {
    std::string path = parent + std::to_string(child);
    TriangleQ tri = TriangleFromPath(path);
    TubeCertificate cert;
    if (Tube229::SynthesizeCertificate(tri, 11, &cert, {}, {}, false)) {
      std::cout << "Child " << path << ": DIRECT CERTIFICATE FOUND! c=" << cert.c.ToDouble() << " r=" << cert.r.ToDouble() << "\n";
    } else {
      std::cout << "Child " << path << ": Direct certificate failed.\n";
    }
  }
  return 0;
}

