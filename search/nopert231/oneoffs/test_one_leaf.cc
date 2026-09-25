#include <iostream>
#include <chrono>
#include "ruperts/tubetree229.h"
#include "ruperts/tube229.h"

using namespace tubetree229;

int main(int argc, char **argv) {
  std::string path = (argc > 1) ? argv[1] : "031213032001010300300";
  TriangleQ tri = TriangleFromPath(path);
  std::cout << "Testing path: " << path << " (depth " << path.size() << ")\n";

  auto t0 = std::chrono::steady_clock::now();
  TubeCertificate cert;
  bool ok = Tube229::SynthesizeCertificateIterative(tri, (int)path.size(), &cert);
  auto t1 = std::chrono::steady_clock::now();
  double dt = std::chrono::duration<double>(t1 - t0).count();

  std::cout << "Result: " << (ok ? "SUCCESS" : "FAIL") << " in " << dt << " s\n";
  if (ok) {
    std::cout << "  r = " << cert.r.ToString() << "  c = " << cert.c.ToString() << "\n";
  }
  return 0;
}
