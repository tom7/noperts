#include <iostream>
#include <vector>

#include "ruperts/tubetree229.h"
#include "ruperts/nopert231.h"
#include "ruperts/tube229.h"

using namespace tubetree229;
using vec2 = Tube229::vec2;

int main() {
  std::string path = "031213002112122012121";
  TriangleQ tri = TriangleFromPath(path);
  vec3 u = yocto::normalize(vec3{tri.corners[2].x.ToDouble(), tri.corners[2].y.ToDouble(), tri.corners[2].z.ToDouble()});

  vec3 axis = vec3{0, 1, 0};
  vec3 first = yocto::normalize(yocto::cross(u, axis));
  vec3 second = yocto::cross(u, first);

  std::vector<vec2> projected(NUM_VERTICES);
  for (int k = 0; k < NUM_VERTICES; k++) {
    projected[k] = vec2{yocto::dot(Vertex(k), first), yocto::dot(Vertex(k), second)};
  }
  std::vector<int> hull = Tube229::ConvexHull2D(projected);
  int H = hull.size();

  vec3 sep_norm = yocto::normalize(vec3{-5.32008e-07, 6.40865e-07, 1.0327e-06});

  // Collect candidate contacts (n2_i, tau_i)
  struct Contact {
    vec2 n;
    vec3 tau;
    int v;
    int mix;
  };
  std::vector<Contact> contacts;

  for (int pos = 0; pos < H; pos++) {
    int v = hull[pos];
    int prev = hull[(pos - 1 + H) % H];
    int next = hull[(pos + 1) % H];

    for (int mix = 0; mix <= 1000; mix += 100) {
      ContactInfo ci;
      ci.vertex = v;
      ci.edge_start = prev;
      ci.edge_finish = v;
      ci.edge_start2 = v;
      ci.edge_finish2 = next;
      ci.mix = mix;

      vec3 edge = Tube229::GetDoubleEdge(ci);
      vec3 lift = yocto::cross(u, edge);
      vec3 tau = yocto::cross(Vertex(v), lift);
      vec2 n2 = vec2{yocto::dot(lift, first), yocto::dot(lift, second)};

      contacts.push_back({n2, tau, v, mix});
    }
  }

  // We want to find w_i >= 0 such that:
  // sum w_i * n2_i.x = 0
  // sum w_i * n2_i.y = 0
  // and dot(sum w_i * tau_i, -sep_norm) > 0.
  // We can test this by checking combinations of 3 contacts (which span 2D zero)
  // or testing 4 contacts.
  // Notice: ANY conic combination of contacts balancing in 2D is a positive linear combination
  // of 3-contact balances! Because by Carathéodory's theorem in R^2, any point in the cone
  // of balances is a combination of 3-contact balances!
  
  double max_opposing_torque = -1e9;
  int best_triplet[3] = {-1, -1, -1};

  for (size_t i = 0; i < contacts.size(); i++) {
    for (size_t j = i + 1; j < contacts.size(); j++) {
      for (size_t k = j + 1; k < contacts.size(); k++) {
        vec2 n0 = contacts[i].n;
        vec2 n1 = contacts[j].n;
        vec2 n2 = contacts[k].n;

        // Weights that balance n0, n1, n2:
        double w0 = n1.x * n2.y - n1.y * n2.x;
        double w1 = n2.x * n0.y - n2.y * n0.x;
        double w2 = n0.x * n1.y - n0.y * n1.x;

        if (w0 < 0 && w1 < 0 && w2 < 0) {
          w0 = -w0; w1 = -w1; w2 = -w2;
        }

        if (w0 > 1e-9 && w1 > 1e-9 && w2 > 1e-9) {
          // Normal vector A:
          vec3 A = w0 * contacts[i].tau + w1 * contacts[j].tau + w2 * contacts[k].tau;
          double opp = yocto::dot(A, -sep_norm) / yocto::length(A);
          if (opp > max_opposing_torque) {
            max_opposing_torque = opp;
            best_triplet[0] = i;
            best_triplet[1] = j;
            best_triplet[2] = k;
          }
        }
      }
    }
  }

  std::cout << "Max opposing torque among ALL 2D balanced contact systems on the hull: "
            << max_opposing_torque << "\n";

  if (max_opposing_torque > 0) {
    std::cout << "SUCCESS! A balanced contact system exists that opposes the separating normal!\n";
    std::cout << "Best triplet contacts:\n";
    for (int idx : best_triplet) {
      std::cout << "  Vertex " << contacts[idx].v << " mix=" << contacts[idx].mix << "\n";
    }
  } else {
    std::cout << "NO! Every balanced contact system has opposing torque <= 0!\n";
  }

  return 0;
}
