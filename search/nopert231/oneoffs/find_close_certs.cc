#include <iostream>
#include <vector>
#include <cmath>
#include <fstream>
#include <sstream>
#include <string>
#include <map>
#include <set>
#include "yocto-math.h"
#include "tubetree229.h"
#include "tube229.h"
#include "rapidjson/document.h"
#include "rapidjson/filereadstream.h"

using namespace tubetree229;
using vec3 = yocto::vec<double, 3>;

int main(int argc, char **argv) {
  std::string target_path = "031213002112121221112212122211";
  if (argc > 1) target_path = argv[1];

  std::cout << "Target path: " << target_path << "\n";
  TriangleQ target_tri = TriangleFromPath(target_path);
  vec3 tf[3] = {target_tri.corners[0].ToDouble(), target_tri.corners[1].ToDouble(), target_tri.corners[2].ToDouble()};
  vec3 target_centroid = (tf[0] + tf[1] + tf[2]) / 3.0;

  FILE *fp = fopen(".artifacts/nopert229/tree_0.json", "rb");
  if (!fp) {
    std::cerr << "Cannot open tree_0.json\n";
    return 1;
  }
  char readBuffer[65536];
  rapidjson::FileReadStream is(fp, readBuffer, sizeof(readBuffer));
  rapidjson::Document doc;
  std::cout << "Parsing tree_0.json...\n";
  doc.ParseStream(is);
  fclose(fp);

  if (doc.HasParseError()) {
    std::cerr << "JSON parse error\n";
    return 1;
  }

  struct CertNode {
    std::string path;
    vec3 centroid;
    double dist;
    rapidjson::Value const* cert_val;
  };
  std::vector<CertNode> nearby;

  // DFS to collect certificates
  auto dfs = [&](auto &self, const rapidjson::Value &node) -> void {
    if (node.HasMember("certificate") && node["certificate"].IsObject()) {
      std::string path = node["path"].GetString();
      TriangleQ tri = TriangleFromPath(path);
      vec3 cf[3] = {tri.corners[0].ToDouble(), tri.corners[1].ToDouble(), tri.corners[2].ToDouble()};
      vec3 centroid = (cf[0] + cf[1] + cf[2]) / 3.0;
      double d = yocto::length(centroid - target_centroid);
      if (d < 0.05) {
        nearby.push_back({path, centroid, d, &node["certificate"]});
      }
    }
    if (node.HasMember("children") && node["children"].IsArray()) {
      for (const auto &c : node["children"].GetArray()) {
        self(self, c);
      }
    }
  };

  if (doc.HasMember("tree") && doc["tree"].IsObject()) {
    dfs(dfs, doc["tree"]);
  } else {
    dfs(dfs, doc);
  }
  std::cout << "Found " << nearby.size() << " certified nodes within dist 0.01\n";

  std::sort(nearby.begin(), nearby.end(), [](const CertNode &a, const CertNode &b) {
    return a.dist < b.dist;
  });

  struct CertKey {
    int v[4][3];
    int m[4][3];
    bool operator<(const CertKey &o) const {
      for (int a = 0; a < 4; a++) {
        for (int c = 0; c < 3; c++) {
          if (v[a][c] != o.v[a][c]) return v[a][c] < o.v[a][c];
          if (m[a][c] != o.m[a][c]) return m[a][c] < o.m[a][c];
        }
      }
      return false;
    }
  };

  std::map<CertKey, TubeCertificate> unique_certs;
  std::vector<std::array<ContactInfo, 3>> all_valid_axes;

  for (const auto &cn : nearby) {
    TubeCertificate cert;
    cert.c = BigRat(cn.cert_val->operator[]("c").GetString());
    cert.r = BigRat(cn.cert_val->operator[]("r").GetString());
    cert.delta = BigRat(cn.cert_val->operator[]("delta").GetString());
    const auto &axes = cn.cert_val->operator[]("axes").GetArray();
    CertKey key;
    for (int a = 0; a < 4; a++) {
      const auto &contacts = axes[a]["contacts"].GetArray();
      for (int c = 0; c < 3; c++) {
        cert.axes[a].contacts[c].edge_start = contacts[c]["edge_start"].GetInt();
        cert.axes[a].contacts[c].edge_finish = contacts[c]["edge_finish"].GetInt();
        cert.axes[a].contacts[c].edge_start2 = contacts[c]["edge_start2"].GetInt();
        cert.axes[a].contacts[c].edge_finish2 = contacts[c]["edge_finish2"].GetInt();
        cert.axes[a].contacts[c].mix = contacts[c]["mix"].GetInt();
        cert.axes[a].contacts[c].vertex = contacts[c]["vertex"].GetInt();
        key.v[a][c] = cert.axes[a].contacts[c].vertex;
        key.m[a][c] = cert.axes[a].contacts[c].mix;
      }
    }
    unique_certs[key] = cert;
  }
  std::cout << "Found " << unique_certs.size() << " unique certificates across all nearby nodes!\n";

  int match_idx = 0;
  for (const auto &[key, cert] : unique_certs) {
    TubeCertificate out_cert;
    std::string fail_reason;
    if (Tube229::AuditCertificateAdaptive(target_tri, cert, &out_cert, &fail_reason)) {
      std::cout << "  MATCH! Unique cert " << match_idx << " c=" << out_cert.c.ToString() << "\n";
      return 0;
    }
    match_idx++;
  }
  std::cout << "None of the " << unique_certs.size() << " unique certificates matched directly.\n";

  // Now audit individual axes across target_tri!
  std::cout << "Auditing individual axes from all unique certificates on target_tri...\n";
  struct ValidAxis {
    std::array<ContactInfo, 3> contacts;
    Vec3Q center;
    BigRat delta;
  };
  std::vector<ValidAxis> valid_axes;
  std::set<std::pair<int, int>> seen_axis;

  for (const auto &[key, cert] : unique_certs) {
    for (int a = 0; a < 4; a++) {
      std::array<ContactInfo, 3> ax = {cert.axes[a].contacts[0], cert.axes[a].contacts[1], cert.axes[a].contacts[2]};
      AxisCertificate ac;
      Vec3Q center;
      BigRat delta;
      std::string fail;
      if (Tube229::AuditAxis(target_tri, ax.data(), &ac, &center, &delta, &fail)) {
        valid_axes.push_back({ax, center, delta});
      }
    }
  }
  std::cout << "Found " << valid_axes.size() << " valid axes for target_tri!\n";

  // Convert valid_axes to CandidateTriple for Wolfe & Extremal search
  std::vector<Tube229::CandidateTriple> cands;
  std::vector<vec3> pts;
  for (const auto &va : valid_axes) {
    Tube229::CandidateTriple ct;
    ct.contacts[0] = va.contacts[0];
    ct.contacts[1] = va.contacts[1];
    ct.contacts[2] = va.contacts[2];
    ct.normalized_a = va.center.ToDouble();
    cands.push_back(ct);
    pts.push_back(ct.normalized_a);
  }

  std::cout << "Testing Wolfe balanced tetrahedron on " << cands.size() << " axes...\n";
  std::array<int, 4> simplex;
  vec3 sep_norm;
  bool enclosed = Tube229::FindBalancedTetrahedron(cands, &simplex, &sep_norm);
  std::cout << "  Wolfe enclosed: " << (enclosed ? "YES" : "NO") << "\n";
  if (!enclosed) {
    std::cout << "  sep_norm: (" << sep_norm.x << ", " << sep_norm.y << ", " << sep_norm.z << ")\n";
  } else {
    TubeCertificate comb_cert;
    for (int a = 0; a < 4; a++) {
      comb_cert.axes[a].contacts[0] = cands[simplex[a]].contacts[0];
      comb_cert.axes[a].contacts[1] = cands[simplex[a]].contacts[1];
      comb_cert.axes[a].contacts[2] = cands[simplex[a]].contacts[2];
    }
    TubeCertificate out_cert;
    std::string fail;
    if (Tube229::AuditCertificateAdaptive(target_tri, comb_cert, &out_cert, &fail)) {
      std::cout << "  WOLFE COMBINED CERTIFICATE AUDITED SUCCESSFULLY!\n";
      std::cout << "  c = " << out_cert.c.ToString() << " (" << out_cert.c.ToDouble() << ")\n";
      std::cout << "  r = " << out_cert.r.ToString() << " (" << out_cert.r.ToDouble() << ")\n";
      return 0;
    } else {
      std::cout << "  Wolfe audit failed: " << fail << "\n";
    }
  }

  // Extreme points pool search
  std::cout << "Testing extreme points pool search on valid axes...\n";
  std::set<int> pool_set;
  for (int d = 0; d < 2000; d++) {
    double y = 1.0 - (d / 1999.0) * 2.0;
    double radius = std::sqrt(std::max(0.0, 1.0 - y * y));
    double theta = 2.39996322972865332 * d;
    vec3 dir = {std::cos(theta) * radius, y, std::sin(theta) * radius};
    int best_hi = 0, best_lo = 0;
    double max_v = yocto::dot(pts[0], dir);
    double min_v = max_v;
    for (size_t i = 1; i < pts.size(); i++) {
      double v = yocto::dot(pts[i], dir);
      if (v > max_v) { max_v = v; best_hi = i; }
      if (v < min_v) { min_v = v; best_lo = i; }
    }
    pool_set.insert(best_hi);
    pool_set.insert(best_lo);
  }
  std::vector<int> pool(pool_set.begin(), pool_set.end());
  std::cout << "Extreme points pool size: " << pool.size() << "\n";

  int P = pool.size();
  for (int i0 = 0; i0 < P; i0++) {
    for (int i1 = i0 + 1; i1 < P; i1++) {
      for (int i2 = i1 + 1; i2 < P; i2++) {
        for (int i3 = i2 + 1; i3 < P; i3++) {
          double margin = 0;
          if (Tube229::PointInTetrahedron(vec3{0, 0, 0}, pts[pool[i0]], pts[pool[i1]], pts[pool[i2]], pts[pool[i3]], &margin) && margin > 1e-6) {
            TubeCertificate comb_cert;
            int idx[4] = {pool[i0], pool[i1], pool[i2], pool[i3]};
            for (int a = 0; a < 4; a++) {
              comb_cert.axes[a].contacts[0] = cands[idx[a]].contacts[0];
              comb_cert.axes[a].contacts[1] = cands[idx[a]].contacts[1];
              comb_cert.axes[a].contacts[2] = cands[idx[a]].contacts[2];
            }
            TubeCertificate out_cert;
            std::string fail;
            if (Tube229::AuditCertificateAdaptive(target_tri, comb_cert, &out_cert, &fail)) {
              std::cout << "  EXTREME POOL COMBINED CERTIFICATE AUDITED SUCCESSFULLY!\n";
              std::cout << "  c = " << out_cert.c.ToString() << " (" << out_cert.c.ToDouble() << ")\n";
              std::cout << "  r = " << out_cert.r.ToString() << " (" << out_cert.r.ToDouble() << ")\n";
              return 0;
            }
          }
        }
      }
    }
  }

  return 0;
}
