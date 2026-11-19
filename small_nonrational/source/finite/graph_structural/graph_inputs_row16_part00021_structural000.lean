module
prelude
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow16Part00021Data
public import GraphInputsRow16Part00021Frames
public import GraphInputsRow16Part00021Leaves
public import GraphInputsRow16Part00021Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00021.record000
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record000
def vertexColumn : Fields := ⟨10, hexnat% "2d8a716a968e62d92e1b91eb86d1b2569a6659365a5396952d68d3352d1b61d4749d58ce394cd32ce4b52d2b1ae1b46c5b31ca719d1725c3713c2f4990e07ac13869192619494a52550d0752318d0b12c1b41c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "36db69a49349a49369a4926da49249a492489249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨46, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨62, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [5766400890382581760, 6755399441055744, 18014471523926016, 1008806316530991104, 36028797018963968]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [6827542929318346752, 17596481011712, 2252899593748480, 1688849860263936, 4503599644147712]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [5908804138568777728, 18014471523926016, 578713651628736512, 5066549866004480, 325385073077518336, 21990232555520]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c3 c0
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [1736805084064382976, 4611686027017322496, 325385073077518336, 104152956928, 162129586585337856]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [5766963843557228544, 5066549580791808, 1008806316530991104, 18014468302700544, 37154696925806592]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [5766962709266432000, 104152956928, 1688849860263936, 576461851815051264, 4503600046800896, 486388759756013568]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c7 c6
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c8 c5
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [4616838356217626624, 578713651628736512, 1152921506754330624, 37172289111851008, 108447924224, 450359962737049600]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [5764690118707249152, 7318349662912512, 1008806316530991104, 54060792009457664, 1130297986908160]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [1064006231628185600, 103087603712, 7318349662912512, 5764607523105538048, 3298669101056, 70368744177664]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [1062880434775392256, 1688849893818368, 5764607523105538048, 3298937536512, 4573968371548160, 2251799813685248]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [4618541503990464512, 1008806316530991104, 1152921506754330624, 1693247940329472, 104152956928, 54043195528445952]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [1722999669522432, 4573968371548160, 5764607523034234880, 578712552117108736, 486388759756013568, 71949090816]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [306274598305923072, 5764607523101343744, 37159094972317696, 720575940379279360, 4573968371548160, 2814749767106560]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [5764634047942754304, 4573968639983616, 3298534883328, 1693247906775040, 486388759756013568, 578712552117108736]
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [2219180633547079680, 105235087360, 5066549849227264, 4611756387242868736, 2199023255552]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [1190669969134714880, 450359962737049600, 4611756387242868736, 3298803318784, 578712552117108736, 105235087360, 4503599627370496]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c19 c18
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c20 c17
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c21 c16
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c22 c15
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c23 c14
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c24 c13
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c25 c12
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c26 c11
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨24, by decide⟩ c27 c10
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c28 c9
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c29 c4
  c30
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record000_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record000_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record000_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record000_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record000_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record000_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record000_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record000_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record000_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00021.record000

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00021.record002
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record002
def vertexColumn : Fields := ⟨10, hexnat% "b8ad25aa5a39a962d92e1b91eb86d15a659365a5396952d4cd4b46d4749db0ea398d6338e9394cd32ce4b52d2b1ae1b46c5ba1cc729c6785d1725c3713c2f4990e07ac138691494a52550d0764348c6384d0b12c1b41c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "6db6da6926da4934d24d24936924926d2492489249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨51, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨64, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1400a007f0cc00000", 1153068839164968960, 27303072774488064, 61572919590912, 2341871806232657920, 72057594591576064]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [4693612855675584512, 1170940301162840064, 2341880602325680128, hexnat% "10008001800000000", 35600983916544, 142936511610880]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "121a8bc7b37c00000", 4612248968380809216, 2216337342464, 1170935903116328960, 281474976710656]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [2423143695114043392, 1152923707925069824, 154627211264, 18295873620410368, hexnat% "10008000004400000", 4612248968380809216]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [108148510070669312, hexnat% "10008000000000000", 3458905251308896256, 4612248968380809216, 27303072774488064, 6597203984384]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [3476988279394402304, 117093590848503808, 17414750208, hexnat% "10008001000400000", 4612248968380809216, 281474976710656]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1400a383b15c00000", 2491081031680, 117093590848503808, 3458905251308896256, 18295873653964800, 4398046511104]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [4648339884413550592, hexnat% "10008000000000000", 3458905251308896256, 81064793292668928, 6597203984384, 18295873519747072]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [3458973945884049408, 117093590311632896, 18295873620410368, 21474836480, hexnat% "14000000004000000", 2814749767106560]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1410aa81a35c00000", 18004502904832, 2341871806232657920, 27303072774488064, 1152923707925069824, 4415360598016]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [2344308401602822144, 81064793829539840, hexnat% "14000000004400000", 18038862643200, 844424963686400, 1170940301162840064, 2220632309760]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c11 c10
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c12 c9
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨23, by decide⟩ c13 c8
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c14 c7
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c15 c6
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c16 c5
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c17 c4
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨24, by decide⟩ c18 c1
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c19 c0
  c20
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record002_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record002_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record002_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record002_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record002_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record002_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record002_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record002_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record002_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00021.record002

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00021.record006
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record006
def vertexColumn : Fields := ⟨10, hexnat% "2cc4f0f2b2aaa4eac695936a3a4e3392e4783e3c6c96a539b15554d68d934cd4b51d0f6c338cd34ccb31ce8b92ccb4ad1b0ee8791cc749d170de0f43c8f13c2f07ec2a28aa91856839314a4a945455434c328c530cc8b0ac4705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "36d269349b6db49a4db49a49249a4d349a492491249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨33, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [6825768453668864, 54183967376539648, hexnat% "64000000080000000", hexnat% "308000004000000000", 3857014849536, 30856118796288, 132120576]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record006_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record006_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record006_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record006_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record006_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record006_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record006_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record006_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record006_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00021.record006

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00021.record010
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record010
def vertexColumn : Fields := ⟨10, hexnat% "2d4b30f22e9369392e0fad13c6c9aa5a92e6c5a565535535c368d934cd4b49d0f4e334d332cc7392ccb2ac9b0ee4751d2745c3783c4f0bc1f4a85643ac1344b1a25292a6451560d4352314c3342c2b41c4705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "db6da6924926934934db4926d3492492489249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨33, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨43, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨60, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [1179952390585974784, 108156759801069568, 432909063936802816, 1795162112, 175921860444160, 5629499534213120]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [1226289720795856896, 481036337152, 5136918324969472, 63050403373121536, 432346113983381504]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [1162078310453215232, 420906795008, 54043195528445952, 76666746781564928, 432909063936802816, 1125899906842624]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [438609426132238336, 1152930300699869184, 63050394783186944, 72092778410016768, 140737488355328]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [510702057464791040, 9007345283629056, 149533623320576, 54043195528445952, 1152921504942391296, 671088640]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [1153493253165678592, 246290638176256, 63050403373121536, 364791569817010176, 144115943990099968, 1125901517455360, 275012124672]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨22, by decide⟩ c7 c2
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨24, by decide⟩ c8 c1
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c9 c0
  c10
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record010_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record010_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record010_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record010_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record010_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record010_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record010_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record010_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record010_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00021.record010

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00021.record019
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record019
def vertexColumn : Fields := ⟨10, hexnat% "b88f24eac6a58b69391e0fae13c4e94e6c5a55952d64d334ad4743db0ea398ce3a4cd34ccb31ce4b52d2b46c3bc1e8791cc729e1725c3783c4f0bc1f1a91643ac1384b11a685454954364318d130cd0b12c2b81d0705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "1b6db69a49a4936d34d26d24924924da492489249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨47, by decide⟩, ⟨49, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨62, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [639514461186555904, 1225119836133130240, 4612249019920416768, 481036337152, 288283702465658880]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [4621257258955702272, 3298669101056, 54043195528445952, 175924007927808, 2017630225248026624, 72057598332895232]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [63050395194228736, 2017630225248026624, 4612249011334676480, 72198337968734208, 481086668800, 3865537675264, 35184372088832]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨23, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c3 c0
  c4
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record019_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record019_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record019_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record019_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record019_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record019_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record019_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record019_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record019_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00021.record019

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00021.record026
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "26c4f13ab1aa6999364b86e4789e1783e9a539b16a5996954d64d8b52d1b51d2745d0f6c3a8e6364d3352c6b26c5b0ee8791cc789d2729c6745c570dd0f23d2a468961382e0792946685916252544d0b41d48d1324d0b12c2b06c8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "369b6d249269249a4924936d2492492492492449249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record026 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record026 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record026.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record026.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record026.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 29), (facetIndex 31), (facetIndex 39), (facetIndex 41), (facetIndex 44), (facetIndex 45)]))
 (.leaf ([(facetIndex 27), (facetIndex 38), (facetIndex 51), (facetIndex 58)])))
 (.branch 3
 (.leaf ([(facetIndex 28), (facetIndex 43), (facetIndex 62), (facetIndex 74)]))
 (.leaf ([(facetIndex 64), (facetIndex 65), (facetIndex 66), (facetIndex 67), (facetIndex 68)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 55), (facetIndex 56), (facetIndex 59), (facetIndex 60), (facetIndex 61)]))
 (.leaf ([(facetIndex 40), (facetIndex 50), (facetIndex 52)])))
 (.branch 7
 (.leaf ([(facetIndex 30), (facetIndex 32), (facetIndex 33), (facetIndex 35), (facetIndex 36), (facetIndex 37)]))
 (.branch 8
 (.leaf ([(facetIndex 34), (facetIndex 42), (facetIndex 54), (facetIndex 69)]))
 (.leaf ([(facetIndex 49), (facetIndex 53)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "200007333330244410447851580000027050166676606021z1b;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 9
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 57)]))
 (.branch 2
 (.leaf ([(facetIndex 70)]))
 (.leaf ([(facetIndex 75)]))))
 (.branch 5
 (.branch 4
 (.leaf ([(facetIndex 46), (facetIndex 63)]))
 (.leaf ([(facetIndex 71), (facetIndex 76)])))
 (.branch 6
 (.leaf ([(facetIndex 47), (facetIndex 48)]))
 (.leaf ([(facetIndex 72), (facetIndex 73)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "4436840000600000000005acz22;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 7
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped3_0000 : List Nat := [0, 1, 2]
def grouped3_0002 : List Nat := [3]
def grouped3_0003 : List Nat := [3, 4]
def grouped3_0004 : List Nat := [3, 4, 5, 6]
def grouped3_0005 : List Nat := [4]
def grouped3_0006 : List Nat := [5]
def grouped3_0007 : List Nat := [5, 6]
def grouped3_0008 : List Nat := [6]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record026 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record026_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00021.record026" "{\"atoms\":[{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0003\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0003\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0007\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0007\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0004\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00021.record026" 31

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00021.record026" "{\"ridges\":[[16,545],[17,577],[18,641],[18,644],[35,548],[37,580],[38,641],[46,610],[47,641],[55,545],[56,577],[58,641],[58,644],[59,545],[60,548],[60,641],[60,644],[61,580],[61,641],[61,644],[63,616],[72,674],[76,616]],\"owners\":[[16,545,[46,47,63],[35,55,59,60]],[55,545,[46,47],[16,35,59,60,63]],[59,545,[47],[16,35,46,55,60,63]],[35,548,[76],[16,55,59,60,71,72]],[60,548,[71,76],[16,35,55,59,72]],[17,577,[46,48,63],[37,56,59,61]],[56,577,[46,48],[17,37,59,61,63]],[37,580,[76],[17,56,59,61,71,73]],[61,580,[71,76],[17,37,56,59,73]],[18,641,[47,48],[38,58,60,61]],[38,641,[],[18,47,48,58,60,61]],[47,641,[18,58,61],[38,48,60]],[58,641,[47,48],[18,38,60,61]],[60,641,[48],[18,38,47,58,61]],[61,641,[47],[18,38,48,58,60]],[18,644,[72,73],[38,58,60,61]],[58,644,[72,73],[18,38,60,61]],[60,644,[73],[18,38,58,61,72]],[61,644,[72],[18,38,58,60,73]],[46,610,[71],[]],[72,674,[47],[]],[63,616,[76],[]],[76,616,[63],[]]],\"edges\":[[38,[16,35,46,47,55,59,60,63,71,72,76]],[41,[17,37,46,48,56,59,61,63,71,73,76]],[43,[18,38,47,48,58,60,61,72,73]]],\"groupings\":[3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00021.record026" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00021.record026\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-9,-8],[-11,-10],[-13,-3],[-13,-12],[-17,-8],[-17,-9],[-18,-9],[-18,-17],[-19,-8],[-19,-17],[-1,7,8,16],[-10,7,8],[-13,8],[-4,20],[-14,17,20],[-2,7,9,16],[-11,7,9],[-5,20],[-15,17,20],[-3,8,9],[-6],[-8,3,12,15],[-12,8,9],[-14,9],[-15,8],[-3,18,19],[-12,18,19],[-14,19],[-15,18],[-7,17],[-18,8],[-16,20],[-20,16],[-21,10,11,13,14,15],[-10,21],[-22,7,16],[-7,22],[-16,22],[-23,17,20],[-17,23],[-20,23],[-8,24],[-9,24],[-18,25],[-19,25],[-26,22,23],[-23,26],[-22,26],[-22,-23,27],[-25,28],[-24,28],[-24,-25,29],[-26,-29,30],[-27,-28,30],[-30,31],[-31],[1,4,7,8,10,13,14,16,17,18,20],[2,5,7,9,11,13,15,16,17,19,20],[3,6,8,9,12,14,15,18,19]],\"atoms\":[{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":48,\"b\":47},{\"tag\":\"incompatible\",\"a\":56,\"b\":55},{\"tag\":\"incompatible\",\"a\":59,\"b\":18},{\"tag\":\"incompatible\",\"a\":59,\"b\":58},{\"tag\":\"incompatible\",\"a\":71,\"b\":47},{\"tag\":\"incompatible\",\"a\":71,\"b\":48},{\"tag\":\"incompatible\",\"a\":72,\"b\":48},{\"tag\":\"incompatible\",\"a\":72,\"b\":71},{\"tag\":\"incompatible\",\"a\":73,\"b\":47},{\"tag\":\"incompatible\",\"a\":73,\"b\":71},{\"tag\":\"mate\",\"ridge\":545,\"a\":16,\"owners\":[46,47,63]},{\"tag\":\"mate\",\"ridge\":545,\"a\":55,\"owners\":[46,47]},{\"tag\":\"mate\",\"ridge\":545,\"a\":59,\"owners\":[47]},{\"tag\":\"mate\",\"ridge\":548,\"a\":35,\"owners\":[76]},{\"tag\":\"mate\",\"ridge\":548,\"a\":60,\"owners\":[71,76]},{\"tag\":\"mate\",\"ridge\":577,\"a\":17,\"owners\":[46,48,63]},{\"tag\":\"mate\",\"ridge\":577,\"a\":56,\"owners\":[46,48]},{\"tag\":\"mate\",\"ridge\":580,\"a\":37,\"owners\":[76]},{\"tag\":\"mate\",\"ridge\":580,\"a\":61,\"owners\":[71,76]},{\"tag\":\"mate\",\"ridge\":641,\"a\":18,\"owners\":[47,48]},{\"tag\":\"mate\",\"ridge\":641,\"a\":38,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":641,\"a\":47,\"owners\":[18,58,61]},{\"tag\":\"mate\",\"ridge\":641,\"a\":58,\"owners\":[47,48]},{\"tag\":\"mate\",\"ridge\":641,\"a\":60,\"owners\":[48]},{\"tag\":\"mate\",\"ridge\":641,\"a\":61,\"owners\":[47]},{\"tag\":\"mate\",\"ridge\":644,\"a\":18,\"owners\":[72,73]},{\"tag\":\"mate\",\"ridge\":644,\"a\":58,\"owners\":[72,73]},{\"tag\":\"mate\",\"ridge\":644,\"a\":60,\"owners\":[73]},{\"tag\":\"mate\",\"ridge\":644,\"a\":61,\"owners\":[72]},{\"tag\":\"mate\",\"ridge\":610,\"a\":46,\"owners\":[71]},{\"tag\":\"mate\",\"ridge\":674,\"a\":72,\"owners\":[47]},{\"tag\":\"mate\",\"ridge\":616,\"a\":63,\"owners\":[76]},{\"tag\":\"mate\",\"ridge\":616,\"a\":76,\"owners\":[63]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[55,56,59,60,61],\"full_literals\":[-21,10,11,13,14,15]},{\"tag\":\"group_take\",\"kind\":2,\"index\":4,\"member\":55,\"full_literals\":[-10,21]},{\"tag\":\"group_or\",\"kind\":3,\"index\":3,\"members\":[46,63],\"full_literals\":[-22,7,16]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":46,\"full_literals\":[-7,22]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":63,\"full_literals\":[-16,22]},{\"tag\":\"group_or\",\"kind\":3,\"index\":4,\"members\":[71,76],\"full_literals\":[-23,17,20]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":71,\"full_literals\":[-17,23]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":76,\"full_literals\":[-20,23]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":47,\"full_literals\":[-8,24]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":48,\"full_literals\":[-9,24]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":72,\"full_literals\":[-18,25]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":73,\"full_literals\":[-19,25]},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0003\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-26,22,23],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0003\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-23,26],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0003\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-22,false,26],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0003\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-22,-23,27],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0006\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"grouped3_0007\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-25,28],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0006\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"grouped3_0007\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-24,false,28],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0006\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"grouped3_0007\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-24,-25,29],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0003\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0004\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-26,-29,30],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0003\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0004\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-27,-28,30],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"groupKind3\",\"a\":0,\"b\":3,\"direction\":\"forward\",\"full_literals\":[false,-30,31],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":38,\"owners\":[16,35,46,47,55,59,60,63,71,72,76]},{\"tag\":\"edge\",\"edge\":41,\"owners\":[17,37,46,48,56,59,61,63,71,73,76]},{\"tag\":\"edge\",\"edge\":43,\"owners\":[18,38,47,48,58,60,61,72,73]}]}"
  "p cnf 31 59\n-9 -8 0\n-11 -10 0\n-13 -3 0\n-13 -12 0\n-17 -8 0\n-17 -9 0\n-18 -9 0\n-18 -17 0\n-19 -8 0\n-19 -17 0\n-1 7 8 16 0\n-10 7 8 0\n-13 8 0\n-4 20 0\n-14 17 20 0\n-2 7 9 16 0\n-11 7 9 0\n-5 20 0\n-15 17 20 0\n-3 8 9 0\n-6 0\n-8 3 12 15 0\n-12 8 9 0\n-14 9 0\n-15 8 0\n-3 18 19 0\n-12 18 19 0\n-14 19 0\n-15 18 0\n-7 17 0\n-18 8 0\n-16 20 0\n-20 16 0\n-21 10 11 13 14 15 0\n-10 21 0\n-22 7 16 0\n-7 22 0\n-16 22 0\n-23 17 20 0\n-17 23 0\n-20 23 0\n-8 24 0\n-9 24 0\n-18 25 0\n-19 25 0\n-26 22 23 0\n-23 26 0\n-22 26 0\n-22 -23 27 0\n-25 28 0\n-24 28 0\n-24 -25 29 0\n-26 -29 30 0\n-27 -28 30 0\n-30 31 0\n-31 0\n1 4 7 8 10 13 14 16 17 18 20 0\n2 5 7 9 11 13 15 16 17 19 20 0\n3 6 8 9 12 14 15 18 19 0\n"
  "60 -30 0 56 55 0\n61 3 8 9 12 14 15 18 19 0 21 59 0\n62 -13 15 0 3 4 13 22 0\n63 11 -21 26 0 47 40 41 19 62 15 18 48 38 37 34 12 1 9 16 58 0\n64 -11 26 0 47 40 41 19 62 15 14 48 38 37 2 17 1 7 11 57 0\n65 8 26 0 64 63 35 47 40 41 19 62 15 14 48 38 37 31 11 57 0\n66 26 0 47 48 40 41 37 38 18 19 62 64 65 1 9 16 58 0\n67 -29 0 66 60 53 0\n68 17 20 0 66 32 30 39 36 46 0\n69 -17 14 0 5 6 8 10 25 20 23 61 0\n70 14 0 60 69 68 33 41 38 49 54 50 51 44 45 42 43 29 26 27 61 0\n71 9 0 70 24 0\n72 19 0 70 28 0\n73 24 0 71 43 0\n74 25 0 72 45 0\n75 0 73 74 67 52 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record026.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record026.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record026.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record026.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record026 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record026.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record026.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record026.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record026.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record026 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record026_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record026_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record026_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record026_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record026_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record026_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record026_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record026 Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record026_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record026_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record026_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00021.record026

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00021.record031
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "2ac9713c4eac64da8e9392e2b91e1783eaa6594e6c5a96554d68d9362d4b4ad8751d1743db0da354d33a2e4b2ac5b0ee8791cc749c6745c970de0f43c8f13d2a468a61582e0792946685914a51560d0b41d48ca344c5342c2b06c8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "36d36da4926d249a4924926926d2492492492449249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record031 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record031 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record031.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record031.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record031.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 57)]))
 (.leaf ([(facetIndex 71)])))
 (.branch 3
 (.leaf ([(facetIndex 74)]))
 (.leaf ([(facetIndex 42), (facetIndex 62)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 43), (facetIndex 63)]))
 (.leaf ([(facetIndex 69), (facetIndex 75)])))
 (.branch 7
 (.leaf ([(facetIndex 70), (facetIndex 76)]))
 (.branch 8
 (.leaf ([(facetIndex 47)]))
 (.leaf ([(facetIndex 72)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "65208165000004300000000000000700043z2a;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 9
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped3_0000 : List Nat := [0, 1]
def grouped3_0001 : List Nat := [0, 1, 2, 3]
def grouped3_0003 : List Nat := [2]
def grouped3_0004 : List Nat := [2, 3]
def grouped3_0005 : List Nat := [3]
def grouped3_0006 : List Nat := [4]
def grouped3_0007 : List Nat := [4, 5]
def grouped3_0008 : List Nat := [4, 5, 6, 7, 8]
def grouped3_0009 : List Nat := [5]
def grouped3_0010 : List Nat := [6]
def grouped3_0011 : List Nat := [6, 7, 8]
def grouped3_0012 : List Nat := [7]
def grouped3_0013 : List Nat := [7, 8]
def grouped3_0014 : List Nat := [8]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record031 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record031_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00021.record031" "{\"atoms\":[{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0004\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0007\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0007\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0011\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0011\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00021.record031" 39

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00021.record031" "{\"ridges\":[[14,521],[17,577],[17,580],[18,644],[30,521],[37,577],[38,641],[42,586],[51,521],[54,521],[55,521],[55,577],[55,580],[56,521],[56,644],[58,577],[58,580],[59,644],[60,577],[60,641],[62,600],[63,680],[69,586],[70,650],[75,600],[76,680]],\"owners\":[[14,521,[42,43,62,63],[30,51,54,55,56]],[30,521,[62,63],[14,42,43,51,54,55,56]],[51,521,[42,43,63],[14,30,54,55,56,62]],[54,521,[42,43,62],[14,30,51,55,56,63]],[55,521,[43,63],[14,30,42,51,54,56,62]],[56,521,[42,62],[14,30,43,51,54,55,63]],[17,577,[42,47,62],[37,55,58,60]],[37,577,[62],[17,42,47,55,58,60]],[55,577,[47],[17,37,42,58,60,62]],[58,577,[42,47],[17,37,55,60,62]],[60,577,[42,62],[17,37,47,55,58]],[17,580,[69,72,75],[37,55,58,60]],[55,580,[72],[17,37,58,60,69,75]],[58,580,[69,72],[17,37,55,60,75]],[38,641,[63],[18,43,47,56,59,60]],[60,641,[43,63],[18,38,47,56,59]],[18,644,[70,72,76],[38,56,59,60]],[56,644,[72],[18,38,59,60,70,76]],[59,644,[70,72],[18,38,56,60,76]],[42,586,[69],[]],[69,586,[42],[]],[70,650,[43],[]],[62,600,[75],[]],[75,600,[62],[]],[63,680,[76],[]],[76,680,[63],[]]],\"edges\":[[29,[14,30,42,43,51,54,55,56,62,63,69,70,75,76]],[41,[17,37,42,47,55,58,60,62,69,72,75]],[43,[18,38,43,47,56,59,60,63,70,72,76]]],\"groupings\":[3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00021.record031" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00021.record031\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-9,-8],[-21,-8],[-1,7,8,17,18],[-4,17,18],[-10,7,8,18],[-11,7,8,17],[-12,8,18],[-13,7,17],[-2,7,9,17],[-5,17],[-12,9],[-14,7,9],[-16,7,17],[-2,19,21,22],[-12,21],[-14,19,21],[-6,18],[-16,8,18],[-3,20,21,23],[-13,21],[-15,20,21],[-7,19],[-19,7],[-20,8],[-17,22],[-22,17],[-18,23],[-23,18],[-24,7,17],[-7,24],[-17,24],[-25,8,18],[-8,25],[-18,25],[-19,26],[-22,26],[-23,27],[-9,28],[-21,29],[-24,30],[-30,31],[-26,32],[-25,32],[-25,-26,33],[-29,34],[-28,34],[-34,35],[-27,-34,36],[-32,-35,37],[-32,-36,38],[-33,37],[-38,39],[-31,-37,39],[-39],[1,4,7,8,10,11,12,13,17,18,19,20,22,23],[2,5,7,9,12,14,16,17,19,21,22],[3,6,8,9,13,15,16,18,20,21,23]],\"atoms\":[{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":47,\"b\":43},{\"tag\":\"incompatible\",\"a\":72,\"b\":43},{\"tag\":\"mate\",\"ridge\":521,\"a\":14,\"owners\":[42,43,62,63]},{\"tag\":\"mate\",\"ridge\":521,\"a\":30,\"owners\":[62,63]},{\"tag\":\"mate\",\"ridge\":521,\"a\":51,\"owners\":[42,43,63]},{\"tag\":\"mate\",\"ridge\":521,\"a\":54,\"owners\":[42,43,62]},{\"tag\":\"mate\",\"ridge\":521,\"a\":55,\"owners\":[43,63]},{\"tag\":\"mate\",\"ridge\":521,\"a\":56,\"owners\":[42,62]},{\"tag\":\"mate\",\"ridge\":577,\"a\":17,\"owners\":[42,47,62]},{\"tag\":\"mate\",\"ridge\":577,\"a\":37,\"owners\":[62]},{\"tag\":\"mate\",\"ridge\":577,\"a\":55,\"owners\":[47]},{\"tag\":\"mate\",\"ridge\":577,\"a\":58,\"owners\":[42,47]},{\"tag\":\"mate\",\"ridge\":577,\"a\":60,\"owners\":[42,62]},{\"tag\":\"mate\",\"ridge\":580,\"a\":17,\"owners\":[69,72,75]},{\"tag\":\"mate\",\"ridge\":580,\"a\":55,\"owners\":[72]},{\"tag\":\"mate\",\"ridge\":580,\"a\":58,\"owners\":[69,72]},{\"tag\":\"mate\",\"ridge\":641,\"a\":38,\"owners\":[63]},{\"tag\":\"mate\",\"ridge\":641,\"a\":60,\"owners\":[43,63]},{\"tag\":\"mate\",\"ridge\":644,\"a\":18,\"owners\":[70,72,76]},{\"tag\":\"mate\",\"ridge\":644,\"a\":56,\"owners\":[72]},{\"tag\":\"mate\",\"ridge\":644,\"a\":59,\"owners\":[70,72]},{\"tag\":\"mate\",\"ridge\":586,\"a\":42,\"owners\":[69]},{\"tag\":\"mate\",\"ridge\":586,\"a\":69,\"owners\":[42]},{\"tag\":\"mate\",\"ridge\":650,\"a\":70,\"owners\":[43]},{\"tag\":\"mate\",\"ridge\":600,\"a\":62,\"owners\":[75]},{\"tag\":\"mate\",\"ridge\":600,\"a\":75,\"owners\":[62]},{\"tag\":\"mate\",\"ridge\":680,\"a\":63,\"owners\":[76]},{\"tag\":\"mate\",\"ridge\":680,\"a\":76,\"owners\":[63]},{\"tag\":\"group_or\",\"kind\":3,\"index\":3,\"members\":[42,62],\"full_literals\":[-24,7,17]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":42,\"full_literals\":[-7,24]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":62,\"full_literals\":[-17,24]},{\"tag\":\"group_or\",\"kind\":3,\"index\":4,\"members\":[43,63],\"full_literals\":[-25,8,18]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":43,\"full_literals\":[-8,25]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":63,\"full_literals\":[-18,25]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":69,\"full_literals\":[-19,26]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":75,\"full_literals\":[-22,26]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":76,\"full_literals\":[-23,27]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":47,\"full_literals\":[-9,28]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":72,\"full_literals\":[-21,29]},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0003\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0004\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-24,30],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-30,31],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0006\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0007\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-26,32],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0006\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0007\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-25,false,32],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0006\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0007\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-25,-26,33],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-29,34],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-28,false,34],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0011\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-34,35],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0011\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-27,-34,36],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0008\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-32,-35,37],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0008\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-32,-36,38],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0008\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-33,false,37],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"groupKind3\",\"a\":0,\"b\":3,\"direction\":\"forward\",\"full_literals\":[false,-38,39],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-31,-37,39],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":29,\"owners\":[14,30,42,43,51,54,55,56,62,63,69,70,75,76]},{\"tag\":\"edge\",\"edge\":41,\"owners\":[17,37,42,47,55,58,60,62,69,72,75]},{\"tag\":\"edge\",\"edge\":43,\"owners\":[18,38,43,47,56,59,60,63,70,72,76]}]}"
  "p cnf 39 57\n-9 -8 0\n-21 -8 0\n-1 7 8 17 18 0\n-4 17 18 0\n-10 7 8 18 0\n-11 7 8 17 0\n-12 8 18 0\n-13 7 17 0\n-2 7 9 17 0\n-5 17 0\n-12 9 0\n-14 7 9 0\n-16 7 17 0\n-2 19 21 22 0\n-12 21 0\n-14 19 21 0\n-6 18 0\n-16 8 18 0\n-3 20 21 23 0\n-13 21 0\n-15 20 21 0\n-7 19 0\n-19 7 0\n-20 8 0\n-17 22 0\n-22 17 0\n-18 23 0\n-23 18 0\n-24 7 17 0\n-7 24 0\n-17 24 0\n-25 8 18 0\n-8 25 0\n-18 25 0\n-19 26 0\n-22 26 0\n-23 27 0\n-9 28 0\n-21 29 0\n-24 30 0\n-30 31 0\n-26 32 0\n-25 32 0\n-25 -26 33 0\n-29 34 0\n-28 34 0\n-34 35 0\n-27 -34 36 0\n-32 -35 37 0\n-32 -36 38 0\n-33 37 0\n-38 39 0\n-31 -37 39 0\n-39 0\n1 4 7 8 10 11 12 13 17 18 19 20 22 23 0\n2 5 7 9 12 14 16 17 19 21 22 0\n3 6 8 9 13 15 16 18 20 21 23 0\n"
  "58 -38 0 54 52 0\n59 25 24 0 30 31 8 26 23 33 34 24 3 6 28 4 7 5 55 0\n60 -8 24 0 30 31 13 26 10 23 1 2 11 12 9 56 0\n61 24 0 58 30 31 23 10 26 13 59 43 50 60 32 27 37 48 45 46 39 38 15 16 14 56 0\n62 30 0 61 40 0\n63 31 0 62 41 0\n64 -37 0 63 54 53 0\n65 -33 0 64 51 0\n66 26 0 61 35 36 22 25 29 0\n67 32 0 66 42 0\n68 -25 0 66 65 44 0\n69 -35 0 67 64 49 0\n70 -8 0 68 33 0\n71 -18 0 68 34 0\n72 -34 0 69 47 0\n73 -20 0 70 24 0\n74 -6 0 71 17 0\n75 -23 0 71 28 0\n76 -16 0 71 70 18 0\n77 -29 0 72 45 0\n78 -28 0 72 46 0\n79 -21 0 77 39 0\n80 -9 0 78 38 0\n81 -13 0 79 20 0\n82 -15 0 79 73 21 0\n83 -3 0 79 73 75 19 0\n84 0 83 80 74 70 81 82 76 71 73 79 75 57 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record031.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record031.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record031.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record031.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record031 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record031.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record031.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record031.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record031.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record031 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record031_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record031_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record031_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record031_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record031_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record031_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record031_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record031 Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record031_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record031_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00021.record031_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00021.record031
