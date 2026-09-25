#include <iostream>
#include <vector>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string target = "031213002112122012121";
  TriangleQ tri = TriangleFromPath(target);

  ContactInfo c_ann[3] = {
    {3, 2, 2, 1, 800, 2},
    {1, 4, 4, 8, 800, 4},
    {13, 14, 14, 15, 200, 14}
  };
  AxisCertificate ann_cert;
  BigVecQ3 ann_center;
  BigRat ann_del;
  std::string err;
  Tube229::AuditAxis(tri, c_ann, &ann_cert, &ann_center, &ann_del, &err, BigRat(1, 1000));
  vec3 u0 = yocto::normalize(vec3{ann_center.x.ToDouble(), ann_center.y.ToDouble(), ann_center.z.ToDouble()});
  vec3 e1 = yocto::normalize(yocto::cross(u0, std::abs(u0.z) < 0.9 ? vec3{0,0,1} : vec3{1,0,0}));
  vec3 e2 = yocto::cross(u0, e1);

  double x = 1.26511, y = -0.969618;
  vec3 p = yocto::normalize(u0 + x * e1 + y * e2);

  // Find all edges of the Noperthedron
  // In nopert229, there are 24 vertices. What are the edges?
  // Let's find all pairs of vertices (u, v) that form an edge (connected by a face).
  // Face list from Tube229 / Nopert229:
  std::vector<std::pair<int, int>> edges;
  for (int v = 0; v < NUM_VERTICES; v++) {
    for (int u = v + 1; u < NUM_VERTICES; u++) {
      // Check if distance between Vertex(v) and Vertex(u) matches edge length:
      double d = yocto::length(Vertex(v) - Vertex(u));
      // In Noperthedron, edge length is around 0.43 - 0.45 or so.
      // Let's check:
      if (d < 0.55 && d > 0.3) {
        edges.push_back({v, u});
      }
    }
  }
  std::cout << "Found " << edges.size() << " edges.\n";

  // Build adjacency list for each vertex:
  std::vector<std::vector<int>> adj(NUM_VERTICES);
  for (auto e : edges) {
    adj[e.first].push_back(e.second);
    adj[e.second].push_back(e.first);
  }

  // Generate ALL possible contacts:
  std::vector<ContactInfo> all_contacts;
  std::vector<int> mixes = {0, 250, 500, 750, 1000};
  for (int v = 0; v < NUM_VERTICES; v++) {
    for (size_t i = 0; i < adj[v].size(); i++) {
      for (size_t j = i + 1; j < adj[v].size(); j++) {
        int e1_nbr = adj[v][i];
        int e2_nbr = adj[v][j];
        for (int mix : mixes) {
          ContactInfo ci;
          ci.vertex = v;
          ci.edge_start = e1_nbr; ci.edge_finish = v;
          ci.edge_start2 = v; ci.edge_finish2 = e2_nbr;
          ci.mix = mix;
          all_contacts.push_back(ci);
        }
      }
    }
  }
  std::cout << "Total candidate contacts across all vertices: " << all_contacts.size() << "\n";

  // Now test variation vectors tau for each contact:
  // Is there any contact whose variation vector tau has dot(p, tau) > 0?
  int pos_count = 0;
  for (const auto &ci : all_contacts) {
    // Audit a single contact variation:
    // How is tau computed?
    // Let's test a sample of triples or screen valid triples!
  }

  return 0;
}
