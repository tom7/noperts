#include <iostream>
#include <fstream>
#include <vector>
#include <string>
#include "bignum/big-overloads.h"
#include "tubetree229.h"
#include "tube229.h"

using namespace tubetree229;

static inline vec3 ToVec3(const BigVecQ3 &v) {
  return vec3{v.x.ToDouble(), v.y.ToDouble(), v.z.ToDouble()};
}

bool SynthesizeStandardCage(
    const TriangleQ &tri,
    TubeCertificate *out_cert,
    std::string *fail_reason) {
  auto axes = Tube229::FindAllHullSupportAxes(tri, 200);
  int N = axes.size();
  for (int i0 = 0; i0 < N; i0++) {
    vec3 c0 = ToVec3(axes[i0].center);
    for (int i1 = i0 + 1; i1 < N; i1++) {
      vec3 c1 = ToVec3(axes[i1].center);
      for (int i2 = i1 + 1; i2 < N; i2++) {
        vec3 c2 = ToVec3(axes[i2].center);
        for (int i3 = i2 + 1; i3 < N; i3++) {
          vec3 c3 = ToVec3(axes[i3].center);

          double V0 = yocto::dot(c1, yocto::cross(c2, c3));
          double V1 = -yocto::dot(c0, yocto::cross(c2, c3));
          double V2 = yocto::dot(c0, yocto::cross(c1, c3));
          double V3 = -yocto::dot(c0, yocto::cross(c1, c2));

          double total = V0 + V1 + V2 + V3;
          if (std::abs(total) < 1e-6) continue;

          double l0 = V0 / total;
          double l1 = V1 / total;
          double l2 = V2 / total;
          double l3 = V3 / total;

          if (l0 > 0.05 && l1 > 0.05 && l2 > 0.05 && l3 > 0.05) {
            TubeCertificate test_cert;
            test_cert.axes[0] = axes[i0].cert;
            test_cert.axes[1] = axes[i1].cert;
            test_cert.axes[2] = axes[i2].cert;
            test_cert.axes[3] = axes[i3].cert;

            TubeCertificate verified_cert;
            std::string fail;
            if (Tube229::AuditCertificateAdaptive(tri, test_cert, &verified_cert, &fail)) {
              *out_cert = verified_cert;
              return true;
            }
          }
        }
      }
    }
  }
  if (fail_reason) *fail_reason = "No valid 4-axis cage found";
  return false;
}

std::string CertToJson(const TubeCertificate &cert) {
  std::string s = "{\n";
  s += "  \"r\": \"" + cert.r.ToString() + "\",\n";
  s += "  \"c\": \"" + cert.c.ToString() + "\",\n";
  s += "  \"delta\": \"" + cert.delta.ToString() + "\",\n";
  s += "  \"symmetry_index\": 0,\n";
  s += "  \"axes\": [\n";
  for (int a = 0; a < 4; a++) {
    const auto &ax = cert.axes[a];
    s += "    {\n";
    s += "      \"B\": \"" + ax.B.ToString() + "\",\n";
    s += "      \"nonzero_witness\": [" + std::to_string(ax.nonzero_witness[0]) + ", "
         + std::to_string(ax.nonzero_witness[1]) + ", " + std::to_string(ax.nonzero_witness[2]) + "],\n";
    s += "      \"contacts\": [\n";
    for (int m = 0; m < 3; m++) {
      const auto &c = ax.contacts[m];
      s += "        {\"edge_start\": " + std::to_string(c.edge_start)
         + ", \"edge_finish\": " + std::to_string(c.edge_finish)
         + ", \"edge_start2\": " + std::to_string(c.edge_start2)
         + ", \"edge_finish2\": " + std::to_string(c.edge_finish2)
         + ", \"mix\": " + std::to_string(c.mix)
         + ", \"vertex\": " + std::to_string(c.vertex) + "}"
         + (m < 2 ? ",\n" : "\n");
    }
    s += "      ]\n";
    s += "    }" + std::string(a < 3 ? ",\n" : "\n");
  }
  s += "  ]\n";
  s += "}";
  return s;
}

int main() {
  std::vector<std::string> paths = {
    "03121303021",
    "03121303022",
    "03121303023",
    "03121303200",
    "0312130332",
    "031213000",
    "031213001",
    "031213002",
    "031213003"
  };

  std::ofstream out("canyon_standard_certs.json");
  out << "{\n";
  for (size_t i = 0; i < paths.size(); i++) {
    const std::string &p = paths[i];
    TriangleQ tri = TriangleFromPath(p);
    TubeCertificate cert;
    std::string fail;
    if (!SynthesizeStandardCage(tri, &cert, &fail)) {
      std::cerr << "FAILED to synthesize standard cage for " << p << ": " << fail << "\n";
      return 1;
    }
    std::cout << "Successfully certified " << p << ": c = " << cert.c.ToDouble()
              << ", r = " << cert.r.ToDouble() << "\n";

    out << "  \"" << p << "\": " << CertToJson(cert);
    if (i + 1 < paths.size()) out << ",\n";
    else out << "\n";
  }
  out << "}\n";
  out.close();

  std::cout << "Wrote canyon_standard_certs.json successfully.\n";
  return 0;
}
