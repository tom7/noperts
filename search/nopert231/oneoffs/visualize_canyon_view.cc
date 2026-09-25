#include <iostream>
#include <fstream>
#include <vector>
#include <string>
#include <cmath>
#include <iomanip>
#include <sstream>
#include "image.h"
#include "ruperts/tube229.h"
#include "ruperts/tubetree229.h"
#include "geom/hull-2d.h"

using namespace tubetree229;
using uint32 = uint32_t;

// Color palette (0xRRGGBBAA)
static constexpr uint32 COLOR_BG        = 0x14171FFF;
static constexpr uint32 COLOR_PANEL     = 0x1D222EFF;
static constexpr uint32 COLOR_BORDER    = 0x2E384DFF;
static constexpr uint32 COLOR_TEXT_HI   = 0xFFFFFFFF;
static constexpr uint32 COLOR_TEXT_MID  = 0xA0B0C8FF;
static constexpr uint32 COLOR_TEXT_MUT  = 0x607088FF;

static constexpr uint32 COLOR_EDGE_3D   = 0x3A4860AA; // Polytope internal 3D edges
static constexpr uint32 COLOR_HULL_LINE = 0x00E5FFFF; // 2D Projected Silhouette Hull
static constexpr uint32 COLOR_V_INT     = 0x48556CFF; // Interior vertex
static constexpr uint32 COLOR_V_HULL    = 0x00E676FF; // Silhouette vertex

static constexpr uint32 COLOR_V10       = 0xFF9100FF; // Vertex 10 (Amber)
static constexpr uint32 COLOR_V13       = 0xFFD600FF; // Vertex 13 (Gold)
static constexpr uint32 COLOR_V14       = 0xFF1744FF; // Vertex 14 (Red/Coral)
static constexpr uint32 COLOR_V15       = 0xD500F9FF; // Vertex 15 (Purple)

static constexpr uint32 COLOR_SEAM_BOX  = 0xFF525288;
static constexpr uint32 COLOR_NORM_VEC  = 0xFF3D00FF;

int main() {
  std::cout << "Generating visualization...\n";

  // Triangle tri1 and tri0
  TriangleQ tri0 = TriangleFromPath("031213002112122012120");
  TriangleQ tri1 = TriangleFromPath("031213002112122012121");

  vec3 tri1_f[3] = {
    vec3{tri1.corners[0].x.ToDouble(), tri1.corners[0].y.ToDouble(), tri1.corners[0].z.ToDouble()},
    vec3{tri1.corners[1].x.ToDouble(), tri1.corners[1].y.ToDouble(), tri1.corners[1].z.ToDouble()},
    vec3{tri1.corners[2].x.ToDouble(), tri1.corners[2].y.ToDouble(), tri1.corners[2].z.ToDouble()}
  };
  vec3 centroid1 = (tri1_f[0] + tri1_f[1] + tri1_f[2]) / 3.0;
  vec3 u1 = centroid1 / yocto::length(centroid1);

  vec3 up = {0, 0, 1};
  if (std::abs(yocto::dot(u1, up)) > 0.99) up = {0, 1, 0};
  vec3 e1 = yocto::normalize(yocto::cross(up, u1));
  vec3 e2 = yocto::cross(u1, e1);

  // 3D vertices and 2D projections
  std::vector<vec3> v3d(20);
  std::vector<yocto::vec<double, 2>> v2d(20);
  for (int i = 0; i < 20; i++) {
    v3d[i] = {Tube229::VertexQ(i).x.ToDouble(), Tube229::VertexQ(i).y.ToDouble(), Tube229::VertexQ(i).z.ToDouble()};
    v2d[i] = {yocto::dot(v3d[i], e1), yocto::dot(v3d[i], e2)};
  }

  // 3D wireframe edges
  std::vector<std::pair<int, int>> edges_3d = {
    {0, 1}, {0, 4}, {0, 8}, {0, 12}, {0, 16}, {0, 17},
    {1, 2}, {1, 3}, {1, 4}, {1, 5}, {1, 17}, {1, 18},
    {2, 3}, {2, 5}, {2, 6}, {2, 7}, {2, 18},
    {3, 7}, {3, 11}, {3, 15}, {3, 18}, {3, 19},
    {4, 5}, {4, 8}, {4, 12}, {4, 16},
    {5, 6}, {5, 7}, {5, 8}, {5, 9},
    {6, 7}, {6, 9}, {6, 10}, {6, 11},
    {7, 11}, {7, 15}, {7, 19},
    {8, 9}, {8, 12}, {8, 16},
    {9, 10}, {9, 11}, {9, 12}, {9, 13},
    {10, 11}, {10, 13}, {10, 14}, {10, 15},
    {11, 15}, {11, 19},
    {12, 13}, {12, 16},
    {13, 14}, {13, 15}, {13, 16}, {13, 17},
    {14, 15}, {14, 17}, {14, 18}, {14, 19},
    {15, 19},
    {16, 17}, {17, 18}, {17, 19}, {18, 19}
  };

  // 2D convex hull cycle
  std::vector<int> cycle = Hull2D::GrahamScan(v2d);
  std::vector<bool> is_hull(20, false);
  for (int idx : cycle) is_hull[idx] = true;

  // Initialize Canvas
  const int W = 2400;
  const int H = 1400;
  ImageRGBA img(W, H);
  img.Clear32(COLOR_BG);

  // Helper drawing functions
  auto draw_panel = [&](int x, int y, int w, int h, const std::string &title, const std::string &sub) {
    img.BlendRect32(x, y, w, h, COLOR_PANEL);
    img.BlendBox32(x, y, w, h, COLOR_BORDER, std::nullopt);
    img.BlendText2x32(x + 20, y + 20, COLOR_TEXT_HI, title);
    if (!sub.empty()) {
      img.BlendText32(x + 20, y + 50, COLOR_TEXT_MID, sub);
    }
  };

  // Panel 1: Main Projection
  draw_panel(30, 30, 1320, 1340,
             "RUPERT POLYTOPE #229: PROJECTED SILHOUETTE & ECLIPSE SEAM",
             "View vector u = (0.916020, 0.203403, 0.345737) at canyon leaf 031213002112122012121");

  // Panel 2: Top Right (Sibling tri0)
  draw_panel(1380, 30, 990, 640,
             "CERTIFIED SIBLING tri0 (031213...20) - r = 1/1000",
             "Vertex 14 is outside chord (10->15). Silhouette touches v14. Axis 0 valid!");

  // Panel 3: Bottom Right (Uncertified leaf tri1)
  draw_panel(1380, 700, 990, 670,
             "UNCERTIFIED LEAF tri1 (031213...21) - ECLIPSED",
             "Vertex 10 pokes out; v14 dips inside chord (10->15). Support fails by 8.68e-7!");

  // Main plot coordinate transform:
  // v2d ranges roughly x in [-0.85, 1.0], y in [-1.0, 0.75]
  // Center of panel: (690, 720), scale ~ 580 px/unit
  double scale_main = 580.0;
  double cx_main = 690.0;
  double cy_main = 730.0;

  auto to_screen_main = [&](yocto::vec<double, 2> p) -> std::pair<float, float> {
    return { (float)(cx_main + p.x * scale_main), (float)(cy_main - p.y * scale_main) };
  };

  // 1. Draw 3D wireframe edges
  for (const auto &e : edges_3d) {
    auto p1 = to_screen_main(v2d[e.first]);
    auto p2 = to_screen_main(v2d[e.second]);
    img.BlendLineAA32(p1.first, p1.second, p2.first, p2.second, COLOR_EDGE_3D);
  }

  // 2. Draw 2D silhouette hull
  for (size_t i = 0; i < cycle.size(); i++) {
    int u = cycle[i];
    int v = cycle[(i + 1) % cycle.size()];
    auto p1 = to_screen_main(v2d[u]);
    auto p2 = to_screen_main(v2d[v]);
    img.BlendThickLine32(p1.first, p1.second, p2.first, p2.second, 2.5f, COLOR_HULL_LINE);
  }

  // 3. Highlight Seam Bounding Box (around v10, v13, v14, v15)
  {
    auto p10 = to_screen_main(v2d[10]);
    auto p15 = to_screen_main(v2d[15]);
    float bx = std::min(p10.first, p15.first) - 45.0f;
    float by = std::min(p10.second, p15.second) - 40.0f;
    float bw = std::abs(p10.first - p15.first) + 120.0f;
    float bh = std::abs(p10.second - p15.second) + 90.0f;
    img.BlendBox32((int)bx, (int)by, (int)bw, (int)bh, 0xFF5252AA, std::nullopt);
    img.BlendTextOutline32((int)bx + 10, (int)by + 10, 0x000000FF, 0xFF5252FF, "ECLIPSE SEAM [v10 - v15]");

    // Draw connecting line to right panels
    img.BlendLineAA32(bx + bw, by + 40, 1380, 200, 0xFF525266);
    img.BlendLineAA32(bx + bw, by + bh - 40, 1380, 850, 0xFF525266);
  }

  // 4. Draw separating normal vector n from origin
  {
    vec3 sep_norm = {-0.401011, 0.483067, 0.778355};
    double sep_2d_x = yocto::dot(sep_norm, e1);
    double sep_2d_y = yocto::dot(sep_norm, e2);
    float ox = (float)cx_main;
    float oy = (float)cy_main;
    float nx = ox + (float)(sep_2d_x * 260.0);
    float ny = oy - (float)(sep_2d_y * 260.0);
    img.BlendThickLine32(ox, oy, nx, ny, 2.0f, COLOR_NORM_VEC);
    img.BlendFilledCircleAA32(nx, ny, 5.0f, COLOR_NORM_VEC);
    img.BlendTextOutline32((int)nx + 10, (int)ny - 8, 0x000000FF, COLOR_NORM_VEC, "Separating Normal n");
    img.BlendTextOutline32((int)nx + 10, (int)ny + 6, 0x000000FF, COLOR_TEXT_MID, "All valid triples satisfy a . n > 0");
  }

  // 5. Draw Vertices and Labels on Main Plot
  for (int i = 0; i < 20; i++) {
    auto pt = to_screen_main(v2d[i]);
    uint32 v_col = COLOR_V_INT;
    float r = 5.0f;
    if (is_hull[i]) {
      v_col = COLOR_V_HULL;
      r = 7.0f;
    }
    if (i == 10) { v_col = COLOR_V10; r = 9.0f; }
    else if (i == 13) { v_col = COLOR_V13; r = 8.0f; }
    else if (i == 14) { v_col = COLOR_V14; r = 9.0f; }
    else if (i == 15) { v_col = COLOR_V15; r = 9.0f; }

    img.BlendFilledCircleAA32(pt.first, pt.second, r + 2.0f, 0x000000CC);
    img.BlendFilledCircleAA32(pt.first, pt.second, r, v_col);

    // Label offset
    int lx = (int)pt.first + 10;
    int ly = (int)pt.second - 6;
    if (v2d[i].x < -0.3) lx = (int)pt.first - 32;
    if (v2d[i].y < -0.7) ly = (int)pt.second + 10;
    if (i == 19) { lx = (int)pt.first - 15; ly = (int)pt.second + 12; }
    if (i == 10) { lx = (int)pt.first - 42; ly = (int)pt.second - 4; }
    if (i == 13) { lx = (int)pt.first - 42; ly = (int)pt.second + 8; }
    if (i == 14) { lx = (int)pt.first - 42; ly = (int)pt.second - 4; }
    if (i == 15) { lx = (int)pt.first - 42; ly = (int)pt.second - 4; }

    std::string lbl = "v" + std::to_string(i);
    img.BlendTextOutline32(lx, ly, 0x000000FF, is_hull[i] ? COLOR_TEXT_HI : COLOR_TEXT_MUT, lbl);
  }

  // Draw Legend on Main Panel
  {
    int lx = 60, ly = 1240;
    img.BlendFilledCircleAA32(lx, ly, 6.0f, COLOR_V_HULL);
    img.BlendTextOutline32(lx + 15, ly - 4, 0x000000FF, COLOR_TEXT_HI, "Silhouette Hull Vertex");

    img.BlendFilledCircleAA32(lx + 260, ly, 5.0f, COLOR_V_INT);
    img.BlendTextOutline32(lx + 275, ly - 4, 0x000000FF, COLOR_TEXT_MID, "Interior Polytope Vertex");

    img.BlendFilledCircleAA32(lx + 540, ly, 7.0f, COLOR_V14);
    img.BlendTextOutline32(lx + 555, ly - 4, 0x000000FF, COLOR_V14, "Critical Eclipsed Vertex (v14)");

    img.BlendFilledCircleAA32(lx + 850, ly, 7.0f, COLOR_V10);
    img.BlendTextOutline32(lx + 865, ly - 4, 0x000000FF, COLOR_V10, "Eclipsing Vertices (v10, v15)");
  }

  // =========================================================================
  // RIGHT PANELS: SCHEMATIC ZOOM OF THE MICROSCOPIC SEAM
  // We represent the relative geometry of v9 -> v10 -> v13 -> v14 -> v15
  // with an exaggerated microscopic deviation to clearly show the topology.
  // =========================================================================

  // Coordinates for the zoom views (schematic layout across 800x480 box):
  // v9 top-left, v10 mid-left, v15 bottom-right
  auto draw_zoom_panel = [&](int px, int py, int pw, int ph, bool is_sibling) {
    float x9  = px + 120.0f, y9  = py + 120.0f;
    float x10 = px + 220.0f, y10 = py + 260.0f;
    float x13 = px + 360.0f, y13 = py + 330.0f;
    // For v14:
    // In sibling (is_sibling=true), v14 pokes OUTWARD (to the left/outside the 10->15 chord)
    // In uncertified leaf (is_sibling=false), v14 dips INWARD (to the right/inside the 10->15 chord)
    float x14 = is_sibling ? (px + 450.0f) : (px + 550.0f);
    float y14 = py + 420.0f;
    float x15 = px + 760.0f, y15 = py + 520.0f;

    // Chord line from v10 to v15 (dashed / thin)
    img.BlendThickLine32(x10, y10, x15, y15, 1.5f, 0x8899AA66);
    img.BlendTextOutline32(px + 400, py + 250, 0x000000FF, 0x8899AAFF, "Chord (v10 -> v15)");

    if (is_sibling) {
      // Hull path: v9 -> v10 -> v14 -> v15
      img.BlendThickLine32(x9, y9, x10, y10, 3.5f, COLOR_HULL_LINE);
      img.BlendThickLine32(x10, y10, x14, y14, 3.5f, COLOR_HULL_LINE);
      img.BlendThickLine32(x14, y14, x15, y15, 3.5f, COLOR_HULL_LINE);

      // Annotation
      img.BlendTextOutline32(px + 280, py + 480, 0x000000FF, 0x00FF88FF,
                             "<-- v14 pokes OUTSIDE chord: ON SILHOUETTE");
      img.BlendTextOutline32(px + 100, py + 570, 0x000000FF, COLOR_TEXT_HI,
                             "Support condition: s_upper <= 0  [VALID]");
      img.BlendTextOutline32(px + 100, py + 595, 0x000000FF, 0x00E5FFFF,
                             "Axis 0 = {v2, v4, v14} successfully cages the origin!");
    } else {
      // Hull path: v9 -> v10 -> v15 (v14 is bypassed/eclipsed!)
      img.BlendThickLine32(x9, y9, x10, y10, 3.5f, COLOR_HULL_LINE);
      img.BlendThickLine32(x10, y10, x15, y15, 3.5f, COLOR_HULL_LINE);

      // Internal edges to eclipsed v14
      img.BlendLineAA32(x10, y10, x14, y14, 0xFF174466);
      img.BlendLineAA32(x14, y14, x15, y15, 0xFF174466);

      // Annotation
      img.BlendTextOutline32(px + 420, py + 470, 0x000000FF, 0xFF1744FF,
                             "--> v14 dips INSIDE chord: ECLIPSED!");
      img.BlendTextOutline32(px + 100, py + 570, 0x000000FF, 0xFF5252FF,
                             "Support condition: s_upper = +8.68e-7 > 0  [REJECTED]");
      img.BlendTextOutline32(px + 100, py + 595, 0x000000FF, 0xFF9100FF,
                             "Without v14, candidate pool lacks opposing axis -> Wolfe fails!");
    }

    // Draw vertices
    auto draw_v = [&](float x, float y, int idx, uint32 col, const std::string &name) {
      img.BlendFilledCircleAA32(x, y, 11.0f, 0x000000EE);
      img.BlendFilledCircleAA32(x, y, 9.0f, col);
      img.BlendTextOutline32((int)x - 12, (int)y - 26, 0x000000FF, COLOR_TEXT_HI, name);
    };

    draw_v(x9, y9, 9, COLOR_V_HULL, "v9");
    draw_v(x10, y10, 10, COLOR_V10, "v10");
    draw_v(x13, y13, 13, COLOR_V13, "v13");
    draw_v(x14, y14, 14, COLOR_V14, "v14 (Target)");
    draw_v(x15, y15, 15, COLOR_V15, "v15");
  };

  draw_zoom_panel(1410, 80, 930, 560, true);
  draw_zoom_panel(1410, 750, 930, 590, false);

  // Save PNG
  std::string png_path = "ruperts/canyon_polygon_view.png";
  if (img.Save(png_path)) {
    std::cout << "Successfully saved PNG to " << png_path << "\n";
  } else {
    std::cerr << "Failed to save PNG!\n";
  }

  // Also write SVG for scalable vector inspection
  std::ofstream svg("ruperts/canyon_polygon_view.svg");
  if (svg.is_open()) {
    svg << "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n";
    svg << "<svg xmlns=\"http://www.w3.org/2000/svg\" viewBox=\"0 0 2400 1400\" width=\"2400\" height=\"1400\">\n";
    svg << "<style>\n";
    svg << "  text { font-family: 'DejaVu Sans', 'Helvetica Neue', Arial, sans-serif; }\n";
    svg << "  .title { font-size: 24px; font-weight: bold; fill: #FFFFFF; }\n";
    svg << "  .sub { font-size: 16px; fill: #A0B0C8; }\n";
    svg << "  .lbl { font-size: 15px; font-weight: bold; fill: #E0E8F5; }\n";
    svg << "  .lbl-mut { font-size: 13px; fill: #7A8CA5; }\n";
    svg << "</style>\n";
    svg << "<rect width=\"2400\" height=\"1400\" fill=\"#14171F\"/>\n";

    // Panel backgrounds
    svg << "<rect x=\"30\" y=\"30\" width=\"1320\" height=\"1340\" rx=\"8\" fill=\"#1D222E\" stroke=\"#2E384D\" stroke-width=\"2\"/>\n";
    svg << "<text x=\"50\" y=\"70\" class=\"title\">RUPERT POLYTOPE #229: PROJECTED SILHOUETTE &amp; ECLIPSE SEAM</text>\n";
    svg << "<text x=\"50\" y=\"100\" class=\"sub\">View vector u = (0.916020, 0.203403, 0.345737) at canyon leaf 031213002112122012121</text>\n";

    svg << "<rect x=\"1380\" y=\"30\" width=\"990\" height=\"640\" rx=\"8\" fill=\"#1D222E\" stroke=\"#2E384D\" stroke-width=\"2\"/>\n";
    svg << "<text x=\"1400\" y=\"70\" class=\"title\">CERTIFIED SIBLING tri0 (031213...20) - r = 1/1000</text>\n";
    svg << "<text x=\"1400\" y=\"100\" class=\"sub\">Vertex 14 is outside chord (10->15). Silhouette touches v14. Axis 0 valid!</text>\n";

    svg << "<rect x=\"1380\" y=\"700\" width=\"990\" height=\"670\" rx=\"8\" fill=\"#1D222E\" stroke=\"#2E384D\" stroke-width=\"2\"/>\n";
    svg << "<text x=\"1400\" y=\"740\" class=\"title\">UNCERTIFIED LEAF tri1 (031213...21) - ECLIPSED</text>\n";
    svg << "<text x=\"1400\" y=\"770\" class=\"sub\">Vertex 10 pokes out; v14 dips inside chord (10->15). Support fails by 8.68e-7!</text>\n";

    // 3D wireframe edges
    for (const auto &e : edges_3d) {
      auto p1 = to_screen_main(v2d[e.first]);
      auto p2 = to_screen_main(v2d[e.second]);
      svg << "<line x1=\"" << p1.first << "\" y1=\"" << p1.second
          << "\" x2=\"" << p2.first << "\" y2=\"" << p2.second
          << "\" stroke=\"#3A4860\" stroke-width=\"1.5\" opacity=\"0.6\"/>\n";
    }

    // 2D silhouette hull
    svg << "<polygon points=\"";
    for (int idx : cycle) {
      auto p = to_screen_main(v2d[idx]);
      svg << p.first << "," << p.second << " ";
    }
    svg << "\" fill=\"none\" stroke=\"#00E5FF\" stroke-width=\"3.5\"/>\n";

    // Callout box on main
    auto p10 = to_screen_main(v2d[10]);
    auto p15 = to_screen_main(v2d[15]);
    float bx = std::min(p10.first, p15.first) - 45.0f;
    float by = std::min(p10.second, p15.second) - 40.0f;
    float bw = std::abs(p10.first - p15.first) + 120.0f;
    float bh = std::abs(p10.second - p15.second) + 90.0f;
    svg << "<rect x=\"" << bx << "\" y=\"" << by << "\" width=\"" << bw << "\" height=\"" << bh
        << "\" fill=\"none\" stroke=\"#FF5252\" stroke-width=\"2\" stroke-dasharray=\"6,6\" opacity=\"0.8\"/>\n";
    svg << "<text x=\"" << bx + 10 << "\" y=\"" << by + 25 << "\" fill=\"#FF5252\" font-size=\"14\" font-weight=\"bold\">ECLIPSE SEAM [v10 - v15]</text>\n";

    // Separating normal
    vec3 sep_norm = {-0.401011, 0.483067, 0.778355};
    double sep_2d_x = yocto::dot(sep_norm, e1);
    double sep_2d_y = yocto::dot(sep_norm, e2);
    float ox = (float)cx_main;
    float oy = (float)cy_main;
    float nx = ox + (float)(sep_2d_x * 260.0);
    float ny = oy - (float)(sep_2d_y * 260.0);
    svg << "<line x1=\"" << ox << "\" y1=\"" << oy << "\" x2=\"" << nx << "\" y2=\"" << ny
        << "\" stroke=\"#FF3D00\" stroke-width=\"3\" stroke-dasharray=\"4,4\"/>\n";
    svg << "<circle cx=\"" << nx << "\" cy=\"" << ny << "\" r=\"6\" fill=\"#FF3D00\"/>\n";
    svg << "<text x=\"" << nx + 12 << "\" y=\"" << ny << "\" fill=\"#FF3D00\" font-size=\"14\" font-weight=\"bold\">Separating Normal n</text>\n";

    // Vertices on main
    for (int i = 0; i < 20; i++) {
      auto pt = to_screen_main(v2d[i]);
      std::string fill = is_hull[i] ? "#00E676" : "#48556C";
      float r = is_hull[i] ? 7.0f : 5.0f;
      if (i == 10) { fill = "#FF9100"; r = 9.0f; }
      else if (i == 13) { fill = "#FFD600"; r = 8.0f; }
      else if (i == 14) { fill = "#FF1744"; r = 10.0f; }
      else if (i == 15) { fill = "#D500F9"; r = 9.0f; }

      svg << "<circle cx=\"" << pt.first << "\" cy=\"" << pt.second << "\" r=\"" << r
          << "\" fill=\"" << fill << "\" stroke=\"#000000\" stroke-width=\"2\"/>\n";

      int lx = (int)pt.first + 12;
      int ly = (int)pt.second + 5;
      if (v2d[i].x < -0.3) lx = (int)pt.first - 38;
      if (v2d[i].y < -0.7) ly = (int)pt.second + 15;
      if (i == 19) { lx = (int)pt.first - 15; ly = (int)pt.second + 20; }
      if (i == 10) { lx = (int)pt.first - 42; ly = (int)pt.second; }
      if (i == 13) { lx = (int)pt.first - 42; ly = (int)pt.second + 12; }
      svg << "<text x=\"" << lx << "\" y=\"" << ly << "\" class=\""
          << (is_hull[i] ? "lbl" : "lbl-mut") << "\">v" << i << "</text>\n";
    }

    // SVG Zoom panels
    auto svg_zoom_panel = [&](float px, float py, bool is_sibling) {
      float x9  = px + 120.0f, y9  = py + 120.0f;
      float x10 = px + 220.0f, y10 = py + 260.0f;
      float x13 = px + 360.0f, y13 = py + 330.0f;
      float x14 = is_sibling ? (px + 450.0f) : (px + 550.0f);
      float y14 = py + 420.0f;
      float x15 = px + 760.0f, y15 = py + 520.0f;

      // Chord line
      svg << "<line x1=\"" << x10 << "\" y1=\"" << y10 << "\" x2=\"" << x15 << "\" y2=\"" << y15
          << "\" stroke=\"#8899AA\" stroke-width=\"1.5\" stroke-dasharray=\"4,4\" opacity=\"0.5\"/>\n";
      svg << "<text x=\"" << px + 400 << "\" y=\"" << py + 250 << "\" fill=\"#8899AA\" font-size=\"14\">Chord (v10 -> v15)</text>\n";

      if (is_sibling) {
        svg << "<polyline points=\"" << x9 << "," << y9 << " " << x10 << "," << y10 << " " << x14 << "," << y14 << " " << x15 << "," << y15
            << "\" fill=\"none\" stroke=\"#00E5FF\" stroke-width=\"4\"/>\n";
        svg << "<text x=\"" << px + 260 << "\" y=\"" << py + 480 << "\" fill=\"#00FF88\" font-size=\"15\" font-weight=\"bold\">&lt;-- v14 pokes OUTSIDE chord: ON SILHOUETTE</text>\n";
        svg << "<text x=\"" << px + 100 << "\" y=\"" << py + 570 << "\" fill=\"#FFFFFF\" font-size=\"15\">Support condition: s_upper &lt;= 0  [VALID]</text>\n";
        svg << "<text x=\"" << px + 100 << "\" y=\"" << py + 595 << "\" fill=\"#00E5FF\" font-size=\"15\">Axis 0 = {v2, v4, v14} successfully cages the origin!</text>\n";
      } else {
        svg << "<polyline points=\"" << x9 << "," << y9 << " " << x10 << "," << y10 << " " << x15 << "," << y15
            << "\" fill=\"none\" stroke=\"#00E5FF\" stroke-width=\"4\"/>\n";
        svg << "<line x1=\"" << x10 << "\" y1=\"" << y10 << "\" x2=\"" << x14 << "\" y2=\"" << y14
            << "\" stroke=\"#FF1744\" stroke-width=\"1.5\" stroke-dasharray=\"3,3\" opacity=\"0.6\"/>\n";
        svg << "<line x1=\"" << x14 << "\" y1=\"" << y14 << "\" x2=\"" << x15 << "\" y2=\"" << y15
            << "\" stroke=\"#FF1744\" stroke-width=\"1.5\" stroke-dasharray=\"3,3\" opacity=\"0.6\"/>\n";
        svg << "<text x=\"" << px + 420 << "\" y=\"" << py + 470 << "\" fill=\"#FF1744\" font-size=\"15\" font-weight=\"bold\">--&gt; v14 dips INSIDE chord: ECLIPSED!</text>\n";
        svg << "<text x=\"" << px + 100 << "\" y=\"" << py + 570 << "\" fill=\"#FF5252\" font-size=\"15\">Support condition: s_upper = +8.68e-7 &gt; 0  [REJECTED]</text>\n";
        svg << "<text x=\"" << px + 100 << "\" y=\"" << py + 595 << "\" fill=\"#FF9100\" font-size=\"15\">Without v14, candidate pool lacks opposing axis -&gt; Wolfe fails!</text>\n";
      }

      auto svg_v = [&](float x, float y, const std::string &col, const std::string &name) {
        svg << "<circle cx=\"" << x << "\" cy=\"" << y << "\" r=\"9\" fill=\"" << col << "\" stroke=\"#000000\" stroke-width=\"2\"/>\n";
        svg << "<text x=\"" << x - 12 << "\" y=\"" << y - 18 << "\" fill=\"#FFFFFF\" font-size=\"14\" font-weight=\"bold\">" << name << "</text>\n";
      };

      svg_v(x9, y9, "#00E676", "v9");
      svg_v(x10, y10, "#FF9100", "v10");
      svg_v(x13, y13, "#FFD600", "v13");
      svg_v(x14, y14, "#FF1744", "v14 (Target)");
      svg_v(x15, y15, "#D500F9", "v15");
    };

    svg_zoom_panel(1410, 80, true);
    svg_zoom_panel(1410, 750, false);

    svg << "</svg>\n";
    std::cout << "Successfully saved SVG to ruperts/canyon_polygon_view.svg\n";
  }

  return 0;
}
