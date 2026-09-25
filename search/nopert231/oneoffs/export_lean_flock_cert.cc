#include <iostream>
#include <vector>
#include <set>
#include <map>
#include <cmath>
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

struct CertTriangle {
  vec3 p1, p2, p3;
  int axis_idx;
  int m_idx;
};

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);
  auto axes = Tube229::FindAllHullSupportAxes(tri, 5000);

  ContactInfo c0[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(13, 14, 14, 15, 200, 14)
  };
  AxisCertificate ax0;
  BigVecQ3 ctr0;
  BigRat del0;
  std::string err;
  Tube229::AuditAxis(tri, c0, &ax0, &ctr0, &del0, &err, BigRat(1, 1000));
  vec3 u0 = yocto::normalize(vec3{ctr0.x.ToDouble() / ax0.B.ToDouble(),
                                  ctr0.y.ToDouble() / ax0.B.ToDouble(),
                                  ctr0.z.ToDouble() / ax0.B.ToDouble()});
  double norm_u0 = yocto::length(vec3{ctr0.x.ToDouble() / ax0.B.ToDouble(),
                                      ctr0.y.ToDouble() / ax0.B.ToDouble(),
                                      ctr0.z.ToDouble() / ax0.B.ToDouble()});

  vec3 ex = yocto::normalize(yocto::cross(u0, std::abs(u0.z) < 0.9 ? vec3{0,0,1} : vec3{1,0,0}));
  vec3 ey = yocto::cross(u0, ex);

  double c_cone = 0.027;
  double cos_alpha = c_cone / norm_u0;
  double alpha = std::acos(cos_alpha);
  double c_core = 0.0003;

  int N = 20;
  double tan_alpha = std::tan(alpha);
  double tan_outer = tan_alpha / std::cos(M_PI / N);
  double psi_outer = std::atan(tan_outer);

  auto get_pt = [&](double psi, double phi) {
    return yocto::normalize(std::cos(psi) * u0 + std::sin(psi) * (std::cos(phi) * ex + std::sin(phi) * ey));
  };

  auto find_axis = [&](vec3 p1, vec3 p2, vec3 p3) {
    for (size_t a = 0; a < axes.size(); a++) {
      vec3 v = vec3{axes[a].center.x.ToDouble() / axes[a].cert.B.ToDouble(),
                    axes[a].center.y.ToDouble() / axes[a].cert.B.ToDouble(),
                    axes[a].center.z.ToDouble() / axes[a].cert.B.ToDouble()};
      if (yocto::dot(p1, v) >= c_core && yocto::dot(p2, v) >= c_core && yocto::dot(p3, v) >= c_core) {
        return (int)a;
      }
    }
    return -1;
  };

  std::vector<CertTriangle> all_triangles;

  auto add_quad = [&](vec3 A, vec3 B, vec3 C, vec3 D) {
    int t1 = find_axis(A, B, C);
    int t2 = find_axis(A, C, D);
    if (t1 >= 0 && t2 >= 0) {
      all_triangles.push_back({A, B, C, t1, -1});
      all_triangles.push_back({A, C, D, t2, -1});
      return true;
    }
    int t3 = find_axis(B, C, D);
    int t4 = find_axis(B, D, A);
    if (t3 >= 0 && t4 >= 0) {
      all_triangles.push_back({B, C, D, t3, -1});
      all_triangles.push_back({B, D, A, t4, -1});
      return true;
    }
    return false;
  };

  // 1. Apex
  for (int k = 0; k < N; k++) {
    double phi1 = k * 2.0 * M_PI / N;
    double phi2 = (k + 1) * 2.0 * M_PI / N;
    vec3 A = u0;
    vec3 B = get_pt(0.5 * psi_outer, phi1);
    vec3 C = get_pt(0.5 * psi_outer, phi2);
    int ax = find_axis(A, B, C);
    all_triangles.push_back({A, B, C, ax, -1});
  }

  // 2. Outer quads
  for (int k = 0; k < N; k++) {
    double phi1 = k * 2.0 * M_PI / N;
    double phi2 = (k + 1) * 2.0 * M_PI / N;
    if (k != 17) {
      vec3 A = get_pt(0.5 * psi_outer, phi1);
      vec3 B = get_pt(psi_outer, phi1);
      vec3 C = get_pt(psi_outer, phi2);
      vec3 D = get_pt(0.5 * psi_outer, phi2);
      add_quad(A, B, C, D);
    } else {
      double p_lo = 0.5 * psi_outer;
      double p_hi = psi_outer;
      int m = 4, n = 4;
      for (int i = 0; i < m; i++) {
        for (int j = 0; j < n; j++) {
          double pa = p_lo + (p_hi - p_lo) * i / m;
          double pb = p_lo + (p_hi - p_lo) * (i + 1) / m;
          double fa = phi1 + (phi2 - phi1) * j / n;
          double fb = phi1 + (phi2 - phi1) * (j + 1) / n;
          vec3 A = get_pt(pa, fa);
          vec3 B = get_pt(pb, fa);
          vec3 C = get_pt(pb, fb);
          vec3 D = get_pt(pa, fb);
          if (!add_quad(A, B, C, D)) {
            for (int ii = 0; ii < 2; ii++) {
              for (int jj = 0; jj < 2; jj++) {
                double paa = pa + (pb - pa) * ii / 2.0;
                double pbb = pa + (pb - pa) * (ii + 1) / 2.0;
                double faa = fa + (fb - fa) * jj / 2.0;
                double fbb = fa + (fb - fa) * (jj + 1) / 2.0;
                vec3 AA = get_pt(paa, faa);
                vec3 BB = get_pt(pbb, faa);
                vec3 CC = get_pt(pbb, fbb);
                vec3 DD = get_pt(paa, fbb);
                add_quad(AA, BB, CC, DD);
              }
            }
          }
        }
      }
    }
  }

  std::set<int> unique_axes;
  for (const auto& t : all_triangles) unique_axes.insert(t.axis_idx);

  std::vector<int> core_axes_list(unique_axes.begin(), unique_axes.end());
  std::map<int, int> axis_to_m;
  for (size_t i = 0; i < core_axes_list.size(); i++) {
    axis_to_m[core_axes_list[i]] = (int)i;
  }
  for (auto& t : all_triangles) {
    t.m_idx = axis_to_m[t.axis_idx];
  }

  std::cout << "import Noperthedron.Nopert229.AtlasProjectiveAnnularCertificate\n\n";
  std::cout << "open Noperthedron.Nopert229\n";
  std::cout << "open Noperthedron.Nopert229.AtlasProjectiveAnnularCertificate\n";
  std::cout << "open Noperthedron.Nopert229.AtlasProjectiveLocalCertificate\n\n";

  // Print Lean code for the 15 core axes
  std::cout << "-- 15 Core Axes Definitions\n";
  for (size_t m = 0; m < core_axes_list.size(); m++) {
    int idx = core_axes_list[m];
    const auto& ca = axes[idx];
    std::cout << "def coreAxis_" << m << " : AxisCertificate := {\n";
    std::cout << "  edgeStart := ![" << ca.cert.contacts[0].edge_start << ", " << ca.cert.contacts[1].edge_start << ", " << ca.cert.contacts[2].edge_start << "],\n";
    std::cout << "  edgeFinish := ![" << ca.cert.contacts[0].edge_finish << ", " << ca.cert.contacts[1].edge_finish << ", " << ca.cert.contacts[2].edge_finish << "],\n";
    std::cout << "  edgeStart₂ := ![" << ca.cert.contacts[0].edge_start2 << ", " << ca.cert.contacts[1].edge_start2 << ", " << ca.cert.contacts[2].edge_start2 << "],\n";
    std::cout << "  edgeFinish₂ := ![" << ca.cert.contacts[0].edge_finish2 << ", " << ca.cert.contacts[1].edge_finish2 << ", " << ca.cert.contacts[2].edge_finish2 << "],\n";
    std::cout << "  mix := ![" << ca.cert.contacts[0].mix << ", " << ca.cert.contacts[1].mix << ", " << ca.cert.contacts[2].mix << "],\n";
    std::cout << "  index := ![" << ca.cert.contacts[0].vertex << ", " << ca.cert.contacts[1].vertex << ", " << ca.cert.contacts[2].vertex << "],\n";
    std::cout << "  nonzeroWitness := ![" << ca.cert.nonzero_witness[0] << ", " << ca.cert.nonzero_witness[1] << ", " << ca.cert.nonzero_witness[2] << "],\n";
    std::cout << "  B := " << ca.cert.B.ToString() << "\n";
    std::cout << "}\n\n";
  }

  std::cout << "def coreAxes (m : Fin 15) : AxisCertificate :=\n";
  std::cout << "  match m.val with\n";
  for (size_t m = 0; m < core_axes_list.size(); m++) {
    std::cout << "  | " << m << " => coreAxis_" << m << "\n";
  }
  std::cout << "  | _ => coreAxis_0\n\n";

  return 0;
}
