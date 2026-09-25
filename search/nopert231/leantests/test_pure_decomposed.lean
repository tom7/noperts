import Noperthedron.Nopert229.AtlasProjectiveLocalViewTree
import Noperthedron.Nopert229.AtlasProjectiveAnnularCertificate

open Noperthedron.Nopert229
open Noperthedron.Nopert229.AtlasProjectiveLocalViewTree
open Noperthedron.Nopert229.AtlasProjectiveLocalCertificate
open Noperthedron.SnubCube.ProjectiveView

def getTriangleForPath (digits : List (Fin 4)) : AtlasProjectiveView.Triangle ℚ :=
  digits.foldl (fun t d => split t d) AtlasProjectiveView.upperWedgeTriangle

def main : IO Unit := do
  let pathDigits : List (Fin 4) := [0, 3, 1, 2, 1, 3, 0, 3, 2, 0, 0]
  let tri := getTriangleForPath pathDigits

  let ax0 : AxisCertificate := {
    edgeStart := ![3, 1, 13],
    edgeFinish := ![2, 4, 14],
    edgeStart₂ := ![2, 4, 14],
    edgeFinish₂ := ![1, 8, 15],
    mix := ![800, 800, 200],
    index := ![2, 4, 14],
    nonzeroWitness := ![9, 15, 1],
    B := 349290553/250000000
  }
  let ax1 : AxisCertificate := {
    edgeStart := ![15, 2, 8],
    edgeFinish := ![19, 1, 9],
    edgeStart₂ := ![19, 1, 9],
    edgeFinish₂ := ![3, 4, 10],
    mix := ![200, 200, 200],
    index := ![19, 1, 9],
    nonzeroWitness := ![8, 15, 2],
    B := 898810711/1000000000
  }
  let ax2 : AxisCertificate := {
    edgeStart := ![2, 10, 10],
    edgeFinish := ![1, 15, 15],
    edgeStart₂ := ![1, 15, 15],
    edgeFinish₂ := ![4, 19, 19],
    mix := ![0, 333, 0],
    index := ![1, 15, 15],
    nonzeroWitness := ![15, 1, 4],
    B := 509162627/1000000000
  }
  let ax3 : AxisCertificate := {
    edgeStart := ![3, 4, 14],
    edgeFinish := ![2, 8, 15],
    edgeStart₂ := ![2, 8, 15],
    edgeFinish₂ := ![1, 9, 19],
    mix := ![800, 800, 800],
    index := ![2, 8, 15],
    nonzeroWitness := ![9, 19, 1],
    B := 1324415559/1000000000
  }
  let coreAxis : AxisCertificate := {
    edgeStart := ![3, 1, 14],
    edgeFinish := ![2, 4, 15],
    edgeStart₂ := ![2, 4, 15],
    edgeFinish₂ := ![1, 8, 19],
    mix := ![800, 800, 400],
    index := ![2, 4, 15],
    nonzeroWitness := ![9, 15, 1],
    B := 638283927/500000000
  }

  let box : Box := {
    interval := AtlasPose.rootInterval ℚ,
    chart := 0, symmetryIndex := 0, root := 0,
    triangle := tri,
    certificate := fun | 0 => ax0 | 1 => ax1 | 2 => ax2 | 3 => ax3,
    c := 22779/500000,
    δ := 50071/200000000,
    r := 1 / 500
  }

  let defect0 : Fin 3 → ℚ := fun | 0 => 0 | 1 => 0 | 2 => 0
  let D0 : ℚ := 40453116150493257294382818402404626020428339063662464854174529123912781/550830080000000000000000000000000000000000000000000000000000000000000000000
  let r_min : ℚ := 1 / 500
  let c_cone : ℚ := 10 / 1000
  let c_core : ℚ := 5 / 1000
  let lam : ℚ := 355161298350422525201926151892561115655967306140122874382384900293863818411537970852843919373338177741324191748230970763655916408997093542441816101352778623261405666924/1679202715260663402801952180776723561640990951190812124274315836581582456216564033979701660338782291007405739539039983517685070851915220690655908491983989592451138822947
  let w : Fin 3 → ℚ := fun | 0 => -461944023894444648398609976019424473864019529910981970554684100300600622531065105137042695070456084194939707545968819551923078061344981367889980665859977615275344562663374980627060882266968753370721201557205159828710926806841/88795715134391850529773268213768041753272829784676269217183168084111999124899180559567531258292250539986488073863861495447534303247948399960158335402773153209186706617760177192960000000000000000000000000000000000000000000000000 | 1 => 814682187688528402696751208346901300793266019697453987868258224380204813934160345209930060437736309357535442038626101409642177960436686469156422159509790767879352467269519100000663450732941626285155390404264159503017996948011/142073144215026960847637229142028866805236527655482030747493068934579198599838688895308050013267600863978380918182178392716054885196717439936253336644437045134698730588416283508736000000000000000000000000000000000000000000000000 | 2 => 471761600139551161088544119503344519561158000216022928134477564915649294227812857419772846078863163395330501678682529354298108586396643577244432351078257981985411314989408330878205410387200313200681708565127398659658269866081/177591430268783701059546536427536083506545659569352538434366336168223998249798361119135062516584501079972976147727722990895068606495896799920316670805546306418373413235520354385920000000000000000000000000000000000000000000000000

  let cbox := box.withCoreAxis coreAxis c_core r_min

  IO.println s!"r_min_pos: {decide (0 < r_min)}"
  IO.println s!"r_pos: {decide (0 < box.r)}"
  IO.println s!"r_min_le_r: {decide (r_min ≤ box.r)}"
  IO.println s!"r_le_two: {decide (box.r ≤ 2)}"
  IO.println s!"delta_nonneg: {decide (0 ≤ box.δ)}"
  IO.println s!"c_nonneg: {decide (0 ≤ box.c)}"
  IO.println s!"bary: {decide (box.decomposedBarycentricValid c_cone)}"
  IO.println s!"D0_nonneg: {decide (0 ≤ D0)}"
  IO.println s!"defect0_nonneg: {decide (∀ i, 0 ≤ defect0 i)}"
  IO.println s!"defect_budget0: {decide ((∑ i, box.weightUpper 0 i * defect0 i) ≤ D0)}"
  IO.println s!"c_cone_margin: {decide (box.δ ≤ c_cone)}"
  IO.println s!"annular_dominance: {decide (((1 / 2 : ℚ) * box.r ^ 2 * (box.certificate 0).B + D0) ^ 2 ≤ r_min ^ 2 * (1 - (1 / 4 : ℚ) * box.r ^ 2) * ((c_cone - box.δ) ^ 2 * (box.certificate 0).B ^ 2))}"
  IO.println s!"B_pos: {decide (∀ j, 0 < (box.certificate j).B)}"
  IO.println s!"var: {decide (∀ j, box.variationRadiusSum j + 3 * variationError ≤ (box.certificate j).B * box.δ)}"
  IO.println s!"supp: {decide (∀ j i k, box.supportUpper j i k ≤ if j = 0 then defect0 i else 0)}"
  IO.println s!"dir_nonzero: {decide (∀ j i, box.supportUpper j i ((box.certificate j).nonzeroWitness i) < 0)}"
  IO.println s!"budget: {decide (∀ j, box.weightBudget j ≤ (box.certificate j).B)}"
  IO.println s!"weight_nonneg: {decide (∀ j i, 0 ≤ box.weightLower j i)}"
  IO.println s!"weight_pos: {decide (∀ j, ∃ i, 0 < box.weightLower j i)}"
  IO.println s!"comp_angle: {decide (box.r ^ 2 * (1 + (box.c - box.δ) ^ 2) ≤ 4 * (box.c - box.δ) ^ 2)}"
  IO.println s!"c_core_margin: {decide (box.δ ≤ c_core)}"
  IO.println s!"core_B_pos: {decide (0 < (cbox.certificate 0).B)}"
  IO.println s!"core_var: {decide (cbox.variationRadiusSum 0 + 3 * variationError ≤ (cbox.certificate 0).B * cbox.δ)}"
  IO.println s!"core_supp: {decide (∀ i k, cbox.supportUpper 0 i k ≤ 0)}"
  IO.println s!"core_dir_nonzero: {decide (∀ i, cbox.supportUpper 0 i ((cbox.certificate 0).nonzeroWitness i) < 0)}"
  IO.println s!"core_budget: {decide (cbox.weightBudget 0 ≤ (cbox.certificate 0).B)}"
  IO.println s!"core_weight_nonneg: {decide (∀ i, 0 ≤ cbox.weightLower 0 i)}"
  IO.println s!"core_weight_pos: {decide (∃ i, 0 < cbox.weightLower 0 i)}"
  IO.println s!"core_angle: {decide (cbox.r ^ 2 * (1 + (cbox.c - cbox.δ) ^ 2) ≤ 4 * (cbox.c - cbox.δ) ^ 2)}"
  IO.println s!"c_cone_pos: {decide (0 < c_cone)}"
  IO.println s!"c_margin: {decide (box.δ ≤ box.c)}"
  IO.println s!"c_sum_pos: {decide (0 < box.c + box.δ)}"
  IO.println s!"hdecomp: {decide (cbox.approxNormalizedCenter 0 = lam • box.approxNormalizedCenter 0 + w)}"
  IO.println s!"hortho: {decide ((∑ i, box.approxNormalizedCenter 0 i * w i) = 0)}"
  IO.println s!"hmargin: {decide (0 ≤ lam * c_cone - c_core)}"
  IO.println s!"hineq: {decide ((∑ i, w i ^ 2) * ((∑ i, box.approxNormalizedCenter 0 i ^ 2) - c_cone ^ 2) ≤ (∑ i, box.approxNormalizedCenter 0 i ^ 2) * (lam * c_cone - c_core) ^ 2)}"
