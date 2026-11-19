module
prelude
public import FacetCliqueRaw
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow16Part00035Data
public import GraphInputsRow16Part00035Frames
public import GraphInputsRow16Part00035Leaves
public import GraphInputsRow16Part00035Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00035.record007
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record007
def vertexColumn : Fields := ⟨10, hexnat% "9d26c5a99a56a362b91e27b519c6695a599564d999695956351d64d8b4ad1b51d2745d58d9354e331cd8b52d2b2ac6b46c9b16e2729e1745c3743c1f2588e0ba619455152469896152548d0b51324d0b22c2b21c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "1b6db4d24934d249b4934da4da49249a492489249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨43, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨55, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨63, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [11570004195318693888, 120259084288, 588845651278692352, 432345564227567616, 1152921504606846976]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [10969898991994535936, 432345564227567616, 2341871809453883392, 584115552256, 85899345920]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [9231508436317896704, 873698327709876224, 1188950851381624832, 2305843012434919424, 144115239615463424, 1168231104512]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c3 c0
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [12111517504182943744, 11294183440515072, 1188950851381624832, 8799314247680, 432345568522534912, 128849018880]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [9655823290727399424, 2341880602325680128, 1649300996096, 10273836918374400, 1731634056723955712, 4503599694479360]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [11565324205343899648, 588410519552, 7881299415007232, 1729382256910270464, 432380748599656448, 9147937011531776]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [4232513432936513536, 1099545182208, 288230380446679040, 9223372036863164416, 85899345920]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [12864612096511311872, 1168231104512, 4503599728033792, 873698327709876224, 35205846925312, 1266637663633408]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [1767733232167550976, 11529215046206881792, 432380752894623744, 1651448479744, 4512395787501568, 10273836918374400, 120267472896]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c11 c10
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c12 c7
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c13 c6
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨24, by decide⟩ c14 c5
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c15 c4
  c16
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record007_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record007_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record007_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record007_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record007_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record007_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record007_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record007_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record007_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00035.record007

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00035.record013
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record013
def vertexColumn : Fields := ⟨10, hexnat% "26c9a8bad1a6665a369394e8b86e2783e5c6692e74599595556351d64d534cd8b46d2743dd0e6358d938cd332ce4b52e2b2ac6b26c3bc1e8761e4751e2719e170de0f43c4f0bc1f4589623a611a645515152548d1362344c930cc8b0ae0741c8705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "db6d36db4da6924da49a4da6924da49249249a492489249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨48, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨64, by decide⟩, ⟨67, by decide⟩, ⟨73, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2005980780fdfc00000", hexnat% "80008003000000000", 1924145348608, hexnat% "12001000000000000", 22517998136852480]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "149c0018fdfc00000", hexnat% "2001000400000000000", 317002946183168, hexnat% "80008002000000000", 2310346608841064448, 26388279066624]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "208100858b61cc00000", 317759934169088, 54043195578777600, hexnat% "10010004000000000", 5188146807238033408, 2377900607546589184]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [8755279630937620480, hexnat% "10010000000000000", 20266198323167232, hexnat% "2080000000000000000", 36902367395840, 96757157462016]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "169d121ffdfc00000", 96757023244288, hexnat% "80008000000000000", hexnat% "2001000000000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2083919613fdec00000", 26388279066624, hexnat% "10000004000000000", 549772591104, 4665729213955833856]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "13111217f5ec00000", 96757023244288, hexnat% "2080000000000000000", 549772591104, 20266198323167232, 5224175569897259008]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c7 c4
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [1785678007625580544, 6994090221306380288, hexnat% "2080000000000000000", 132010114809856, hexnat% "10001014000000000"]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20179d8406fdfc00000", hexnat% "80000001000000000", 317758860427264, 9345848836096, 17592186044416]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "179d0006bdf800000", 317827579904000, hexnat% "2080000000000400000", 9345848836096, 2251816993554432, 87960930222080]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c11 c10
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [5318751365541920768, hexnat% "2001000400000000000", hexnat% "80008001000000000", hexnat% "12001000000000000", 37108517437440, 26388279066624]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2081818402fde400000", 62740882259968, 4737786808010539008, hexnat% "12001000000000000", 824642109440]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [6453658445705904128, hexnat% "12001000000000000", hexnat% "2080000000200400000", 132010249027584, 20266198339944448, 17188257792, 1924145348608]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c15 c14
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c16 c13
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨52, by decide⟩ c17 c12
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c18 c9
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c19 c8
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c20 c3
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c21 c2
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c22 c1
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c23 c0
  c24
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record013_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record013_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record013_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record013_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record013_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record013_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record013_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record013_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record013_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00035.record013

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00035.record014
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record014
def vertexColumn : Fields := ⟨10, hexnat% "1729a8bad19968da4e53a2e2783e5c6692e745656359354d8b49d0f74358d9354e334ccb31ce4b52ccb8acab26c3bc1e8761e4751e2785c3783d0f13c2f07e621a9162588e98469454952364350e2318d1324c3322c4b0ae0741c8705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "d369b6d369b4db69a492492492492492492491249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨54, by decide⟩, ⟨59, by decide⟩, ⟨62, by decide⟩, ⟨65, by decide⟩, ⟨70, by decide⟩, ⟨73, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "420845c0fffe000000", 7379922045632512, hexnat% "2004000020000000000", 5497558138880]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20040193a3fba000000", 6322258968576, 594475150812905472, hexnat% "420000000000000000", 1899957166538752]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20040097fc4be000000", hexnat% "20040001800000000", 4503741361291264, 1829595938553856, hexnat% "400800000040000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "400804010cc2000000", hexnat% "2004008320000000000", hexnat% "20040009000000000", 4516793901121536, 492856087150592, 563096250744832, 4898947072]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c4 c1
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c5 c0
  c6
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record014_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record014_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record014_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record014_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record014_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record014_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record014_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record014_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record014_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00035.record014

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00035.record019
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record019
def vertexColumn : Fields := ⟨10, hexnat% "34a9aa3a999662d98e5391e27b499a6391e665594b51d58d534cd4749d1774398d638ccb3c2e8b62e4b52e2b1ae1b46c3b61e4751e2749ca719d1743c8f13c1f268960da619254926545194950d62324c3382d0b22c1b41c8709c17"⟩
def kindColumn : Fields := ⟨3, hexnat% "36db4db4936924d369b4d249249a493492492689249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨47, by decide⟩, ⟨50, by decide⟩, ⟨53, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨67, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [6917599241820962816, 9233505136016359424, hexnat% "80100000014000000", 288371114848026624, 11274289152, 180143985094819840]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "881a43012ff400000", 432345564227567616, 2305985121091584000, 4611695364276224000, 6648609374208]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [5089225464510152704, 2305843301271470080, 9214885888, 9224515528947662848, hexnat% "80100000000000000", 35185445830656]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [6917530745896435712, hexnat% "80100100004400000", 468374361380749312, 9233505136066691072, 176197812092928, 11274289152, 15444702396416]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c4 c1
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c5 c0
  c6
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record019_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record019_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record019_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record019_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record019_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record019_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record019_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record019_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record019_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00035.record019

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00035.record037
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record037
def vertexColumn : Fields := ⟨10, hexnat% "971726aa5a958b69392e2ba1e17971d25a9966558d4b5a364d4b4ad8745d68d6394d534ccb31cd8b92ccb4acab86c5b91d2785c9715e0f43c4f0bc1f528a60d88e94649524a5854358348d50d2328c530cd0b22c4b21c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "6db69b4db4d249269349249249269a492492249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨34, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨59, by decide⟩, ⟨63, by decide⟩, ⟨66, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [9233577658132987904, 725079540006649856, 156130651144192, hexnat% "40040000000000000", 52777095004160, 108649343157796864]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [9440952150868885504, 580964351930793984, hexnat% "40040000000000000", 9570149224939520, 36028797018963968]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "48044ad714e000000", 90177133346816, 14073749103968256, 720576490135093248, 108086393741246464, 16777216]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [54322565585305600, hexnat% "48000000002000000", 221239331694575616, 576461577004253184, 1236950581248, 10133099430019072]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [126931973095555072, 10133099161583616, 725079540006649856, hexnat% "48000000000000000", 13198434500608]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [842951535678717952, 52777095004160, 9224497937835360256, 13198434500608, hexnat% "40040000000000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [46940299393499136, 725079540006649856, 26388815937536, hexnat% "48000000040000000", 72092780557500416, 18018800850960384]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c7 c6
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c8 c5
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [261810580598292480, 580964901686607872, 19140298416324608, hexnat% "48000000000000000", 224437811019776, 17592186044416]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "400c4fff5ef000000", 9223372036854775808, 725079540006649856, 9570149476597760, 72057594037927936]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "480c41731cb000000", 219902325555200, 14073749103968256, 72092778946887680, 576461594184122368, 144115188075855872]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c12 c11
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [126667109072633856, hexnat% "48000000042000000", 224442105987072, 10133099430019072, 725080089762463744, 17884310929408, 35184908959744]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c14 c13
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨24, by decide⟩ c15 c10
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c16 c9
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c17 c4
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c18 c3
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c19 c0
  c20
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record037_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record037_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record037_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record037_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record037_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record037_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record037_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record037_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record037_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00035.record037

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00035.record005
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "15caaa6a969568b8ae2785e0faa99a659565555362d4749d1743dd0ea398e53a2e4b32e2b2ac6b86c9b16c3b61d4789d2725c570de0f23c4f0bc1f2b15229916546498a4a9164a54548d0b41d90d4388ca344c5341c8709c17"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "db69a6da49269249249a6936d34924934d2249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record005 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record005 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record005.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 30), (facetIndex 34), (facetIndex 51), (facetIndex 56), (facetIndex 66)]))
 (.leaf ([(facetIndex 44), (facetIndex 46), (facetIndex 47), (facetIndex 49)])))
 (.branch 3
 (.leaf ([(facetIndex 37), (facetIndex 57), (facetIndex 58)]))
 (.leaf ([(facetIndex 42), (facetIndex 54), (facetIndex 59), (facetIndex 60)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 24), (facetIndex 25), (facetIndex 27), (facetIndex 41), (facetIndex 64)]))
 (.leaf ([(facetIndex 50), (facetIndex 52), (facetIndex 53)])))
 (.branch 7
 (.leaf ([(facetIndex 29), (facetIndex 31), (facetIndex 32), (facetIndex 33), (facetIndex 35)]))
 (.leaf ([(facetIndex 48)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "40036900ed14f2410e0010c36c30824z12;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def grouped2_0000 : List Nat := [0]
def grouped2_0001 : List Nat := [0, 1]
def grouped2_0002 : List Nat := [0, 1, 2, 3]
def grouped2_0004 : List Nat := [1]
def grouped2_0005 : List Nat := [2, 3]
def grouped2_0006 : List Nat := [4, 5]
def grouped2_0007 : List Nat := [4, 5, 6, 7]
def grouped2_0008 : List Nat := [6]
def grouped2_0009 : List Nat := [6, 7]
def grouped2_0010 : List Nat := [7]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record005 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record005_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00035.record005" "{\"atoms\":[{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00035.record005" 16

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00035.record005" "{\"ridges\":[[44,578],[46,578],[48,546],[49,578],[68,106]],\"owners\":[[48,546,[65,68],[7,33,42,47,69]],[44,578,[],[9,46,47,49,67,68]],[46,578,[68],[9,44,47,49,67]],[49,578,[67,68],[9,44,46,47]],[68,106,[40],[]]],\"edges\":[],\"groupings\":[2]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00035.record005" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00035.record005\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":false,\"clauses\":[[-5,-1],[-5,-4],[-8,-7],[-5,7,9],[-2],[-3,9],[-6,8,9],[-9,1],[-10,2,3,4,6],[-11,5],[-12,10],[-13,12],[-14,11],[-15,14],[-16,13],[-16,15],[16]],\"atoms\":[{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2}],\"rules\":[{\"tag\":\"incompatible\",\"a\":48,\"b\":40},{\"tag\":\"incompatible\",\"a\":48,\"b\":47},{\"tag\":\"incompatible\",\"a\":67,\"b\":65},{\"tag\":\"mate\",\"ridge\":546,\"a\":48,\"owners\":[65,68]},{\"tag\":\"mate\",\"ridge\":578,\"a\":44,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":578,\"a\":46,\"owners\":[68]},{\"tag\":\"mate\",\"ridge\":578,\"a\":49,\"owners\":[67,68]},{\"tag\":\"mate\",\"ridge\":106,\"a\":68,\"owners\":[40]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[44,46,47,49],\"full_literals\":[-10,2,3,4,6]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[48],\"full_literals\":[-11,5]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-12,false,10],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-13,12,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"grouped2_0009\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-14,false,11],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-15,false,14],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-16,13,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-16,false,15],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true}]}"
  "p cnf 16 17\n-5 -1 0\n-5 -4 0\n-8 -7 0\n-5 7 9 0\n-2 0\n-3 9 0\n-6 8 9 0\n-9 1 0\n-10 2 3 4 6 0\n-11 5 0\n-12 10 0\n-13 12 0\n-14 11 0\n-15 14 0\n-16 13 0\n-16 15 0\n16 0\n"
  "18 -10 3 4 6 0 5 9 0\n19 13 0 17 15 0\n20 15 0 17 16 0\n21 12 0 19 12 0\n22 14 0 20 14 0\n23 10 0 21 11 0\n24 11 0 22 13 0\n25 5 0 24 10 0\n26 -1 0 25 1 0\n27 -4 0 25 2 0\n28 -9 0 26 8 0\n29 -3 0 28 6 0\n30 7 0 28 25 4 0\n31 6 0 29 23 27 18 0\n32 -8 0 30 3 0\n33 0 31 32 28 7 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record005.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record005.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record005.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record005.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record005 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS noSame
  exact boundary_unsat S HS noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record005.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record005.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record005.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record005.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record005 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record005_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record005_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record005_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record005_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record005_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record005_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record005_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record005 Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record005_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record005_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record005_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00035.record005

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00035.record030
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "25a699662d94e1ba1e27a59695652d54d1b61d2774368e6338e9394cb352c6b26c5b61d4719e1745c3783d0f23c4f0bd6292a1a498a62581e5864986525294950764350d2328c6384c9382c4b06d0721c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "924da4924da492492492492492491249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record030 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record030 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record030.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 33), (facetIndex 40), (facetIndex 45), (facetIndex 58), (facetIndex 66)]))
 (.leaf ([(facetIndex 37), (facetIndex 38), (facetIndex 49), (facetIndex 56), (facetIndex 64)])))
 (.branch 3
 (.leaf ([(facetIndex 34), (facetIndex 36), (facetIndex 41), (facetIndex 44), (facetIndex 46)]))
 (.branch 4
 (.leaf ([(facetIndex 31), (facetIndex 51), (facetIndex 55)]))
 (.leaf ([(facetIndex 59), (facetIndex 60)])))))
 (.branch 7
 (.branch 6
 (.leaf ([(facetIndex 39), (facetIndex 63), (facetIndex 65)]))
 (.leaf ([(facetIndex 42), (facetIndex 43), (facetIndex 47), (facetIndex 48), (facetIndex 50)])))
 (.branch 8
 (.leaf ([(facetIndex 29), (facetIndex 30), (facetIndex 32), (facetIndex 35)]))
 (.branch 9
 (.leaf ([(facetIndex 57)]))
 (.leaf ([(facetIndex 52)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "5150044081300936166202662051127207377z1d;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 10
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 1
 (.leaf ([(facetIndex 53), (facetIndex 54)]))
 (.leaf ([(facetIndex 61), (facetIndex 62)])))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨1, 6917529027641081856⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 2
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped2_0000 : List Nat := [0]
def grouped2_0001 : List Nat := [0, 1]
def grouped2_0002 : List Nat := [0, 1, 2, 3, 4]
def grouped2_0004 : List Nat := [1]
def grouped2_0005 : List Nat := [2]
def grouped2_0006 : List Nat := [2, 3, 4]
def grouped2_0007 : List Nat := [3]
def grouped2_0008 : List Nat := [3, 4]
def grouped2_0009 : List Nat := [4]
def grouped2_0010 : List Nat := [5]
def grouped2_0011 : List Nat := [5, 6]
def grouped2_0012 : List Nat := [5, 6, 7, 8, 9]
def grouped2_0013 : List Nat := [6]
def grouped2_0014 : List Nat := [7]
def grouped2_0015 : List Nat := [7, 8, 9]
def grouped2_0016 : List Nat := [8]
def grouped2_0017 : List Nat := [8, 9]
def grouped2_0018 : List Nat := [9]
def grouped3_0019 : List Nat := [0]
def grouped3_0021 : List Nat := [1]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record030 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record030_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00035.record030" "{\"atoms\":[{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group\",\"kind\":2,\"index\":8},{\"tag\":\"group\",\"kind\":2,\"index\":9},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0008\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0008\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0011\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0017\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0017\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0015\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0015\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0015\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0012\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0012\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0012\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00035.record030" 52

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00035.record030" "{\"ridges\":[[24,38],[29,37],[29,38],[31,13],[32,13],[35,261],[35,262],[51,13],[52,13],[53,13],[54,13],[54,261],[55,37],[55,164],[56,37],[56,261],[57,261],[62,262],[63,38],[64,38],[65,262]],\"owners\":[[56,261,[4,32,35,39],[18,38,54,57]],[55,164,[24,65],[17,57,63]]],\"edges\":[],\"groupings\":[2,3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00035.record030" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00035.record030\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":false,\"clauses\":[[-3,-1],[-8,-3],[-9,-3],[-10,-3],[-10,-4],[-10,-5],[-10,-6],[-10,-7],[-11,-3],[-12,-7],[-13,-12],[-14,-4],[-15,-4],[-15,-6],[-15,-9],[-16,-10],[-18,-3],[-18,-8],[-18,-10],[-18,-11],[-18,-14],[-18,-16],[-18,-17],[-19,-5],[-19,-7],[-20,-13],[-22,-4],[-22,-6],[-22,-9],[-22,-17],[-23,-5],[-23,-10],[-23,-16],[-23,-19],[-24,-15],[-25,-3],[-25,-8],[-25,-11],[-25,-18],[-25,-21],[-25,-24],[-5,-13,-15],[-6,-12,-14],[-6,-13,-14],[-3,-16,-17],[-2,-3,-24],[-3,-23,-24],[-17,1,6,7,10],[-7,-15,-18],[-7,-22,-25],[-16,2,25],[-26,8,9,11,17,24],[-27,5,12,16],[-28,19,20],[-29,10,23,25],[-30,3,4,6,7],[-31,18],[-32,13],[-33,26],[-34,27,28],[-35,27],[-35,28],[-36,34],[-37,35],[-39,33],[-38,36],[-39,37],[-40,29],[-41,31,32],[-42,31],[-42,32],[-43,30,41],[-44,30,42],[-45,30],[-44,41],[-45,42],[-46,40,44],[-47,40,45],[-46,43],[-47,44],[-48,45],[-49,38,48],[-49,39,47],[-49,46],[49],[-50,14,15],[-51,21,22],[-52,50],[-52,51],[52]],\"atoms\":[{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group\",\"index\":8,\"kind\":2},{\"tag\":\"group\",\"index\":9,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":29,\"b\":4},{\"tag\":\"incompatible\",\"a\":37,\"b\":29},{\"tag\":\"incompatible\",\"a\":38,\"b\":29},{\"tag\":\"incompatible\",\"a\":39,\"b\":29},{\"tag\":\"incompatible\",\"a\":39,\"b\":30},{\"tag\":\"incompatible\",\"a\":39,\"b\":31},{\"tag\":\"incompatible\",\"a\":39,\"b\":32},{\"tag\":\"incompatible\",\"a\":39,\"b\":35},{\"tag\":\"incompatible\",\"a\":49,\"b\":29},{\"tag\":\"incompatible\",\"a\":51,\"b\":35},{\"tag\":\"incompatible\",\"a\":52,\"b\":51},{\"tag\":\"incompatible\",\"a\":53,\"b\":30},{\"tag\":\"incompatible\",\"a\":54,\"b\":30},{\"tag\":\"incompatible\",\"a\":54,\"b\":32},{\"tag\":\"incompatible\",\"a\":54,\"b\":38},{\"tag\":\"incompatible\",\"a\":55,\"b\":39},{\"tag\":\"incompatible\",\"a\":57,\"b\":29},{\"tag\":\"incompatible\",\"a\":57,\"b\":37},{\"tag\":\"incompatible\",\"a\":57,\"b\":39},{\"tag\":\"incompatible\",\"a\":57,\"b\":49},{\"tag\":\"incompatible\",\"a\":57,\"b\":53},{\"tag\":\"incompatible\",\"a\":57,\"b\":55},{\"tag\":\"incompatible\",\"a\":57,\"b\":56},{\"tag\":\"incompatible\",\"a\":59,\"b\":31},{\"tag\":\"incompatible\",\"a\":59,\"b\":35},{\"tag\":\"incompatible\",\"a\":60,\"b\":52},{\"tag\":\"incompatible\",\"a\":62,\"b\":30},{\"tag\":\"incompatible\",\"a\":62,\"b\":32},{\"tag\":\"incompatible\",\"a\":62,\"b\":38},{\"tag\":\"incompatible\",\"a\":62,\"b\":56},{\"tag\":\"incompatible\",\"a\":63,\"b\":31},{\"tag\":\"incompatible\",\"a\":63,\"b\":39},{\"tag\":\"incompatible\",\"a\":63,\"b\":55},{\"tag\":\"incompatible\",\"a\":63,\"b\":59},{\"tag\":\"incompatible\",\"a\":64,\"b\":54},{\"tag\":\"incompatible\",\"a\":65,\"b\":29},{\"tag\":\"incompatible\",\"a\":65,\"b\":37},{\"tag\":\"incompatible\",\"a\":65,\"b\":49},{\"tag\":\"incompatible\",\"a\":65,\"b\":57},{\"tag\":\"incompatible\",\"a\":65,\"b\":61},{\"tag\":\"incompatible\",\"a\":65,\"b\":64},{\"tag\":\"three\",\"ridge\":13,\"vertices\":[31,52,54]},{\"tag\":\"three\",\"ridge\":13,\"vertices\":[32,51,53]},{\"tag\":\"three\",\"ridge\":13,\"vertices\":[32,52,53]},{\"tag\":\"three\",\"ridge\":37,\"vertices\":[29,55,56]},{\"tag\":\"three\",\"ridge\":38,\"vertices\":[24,29,64]},{\"tag\":\"three\",\"ridge\":38,\"vertices\":[29,63,64]},{\"tag\":\"mate\",\"ridge\":261,\"a\":56,\"owners\":[4,32,35,39]},{\"tag\":\"three\",\"ridge\":261,\"vertices\":[35,54,57]},{\"tag\":\"three\",\"ridge\":262,\"vertices\":[35,62,65]},{\"tag\":\"mate\",\"ridge\":164,\"a\":55,\"owners\":[24,65]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[37,38,49,56,64],\"full_literals\":[-26,8,9,11,17,24]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[31,51,55],\"full_literals\":[-27,5,12,16]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[59,60],\"full_literals\":[-28,19,20]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[39,63,65],\"full_literals\":[-29,10,23,25]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[29,30,32,35],\"full_literals\":[-30,3,4,6,7]},{\"tag\":\"group_or\",\"kind\":2,\"index\":8,\"members\":[57],\"full_literals\":[-31,18]},{\"tag\":\"group_or\",\"kind\":2,\"index\":9,\"members\":[52],\"full_literals\":[-32,13]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-33,false,26],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0008\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-34,27,28],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0008\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-35,27,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0008\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-35,false,28],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"grouped2_0006\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-36,false,34],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"grouped2_0006\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-37,false,35],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-39,33,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-38,false,36],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-39,false,37],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0011\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-40,29,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped2_0016\",\"right_name\":\"grouped2_0018\",\"joined_name\":\"grouped2_0017\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-41,31,32],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped2_0016\",\"right_name\":\"grouped2_0018\",\"joined_name\":\"grouped2_0017\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-42,31,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped2_0016\",\"right_name\":\"grouped2_0018\",\"joined_name\":\"grouped2_0017\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-42,false,32],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped2_0014\",\"right_name\":\"grouped2_0017\",\"joined_name\":\"grouped2_0015\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-43,30,41],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped2_0014\",\"right_name\":\"grouped2_0017\",\"joined_name\":\"grouped2_0015\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-44,30,42],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped2_0014\",\"right_name\":\"grouped2_0017\",\"joined_name\":\"grouped2_0015\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-45,30,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped2_0014\",\"right_name\":\"grouped2_0017\",\"joined_name\":\"grouped2_0015\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-44,false,41],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped2_0014\",\"right_name\":\"grouped2_0017\",\"joined_name\":\"grouped2_0015\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-45,false,42],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0011\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0012\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-46,40,44],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0011\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0012\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-47,40,45],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0011\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0012\",\"a\":2,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-46,false,43],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0011\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0012\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-47,false,44],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0011\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0012\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-48,false,45],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-49,38,48],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-49,39,47],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"groupKind2\",\"a\":5,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-49,false,46],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":3,\"index\":0,\"members\":[53,54],\"full_literals\":[-50,14,15]},{\"tag\":\"group_or\",\"kind\":3,\"index\":1,\"members\":[61,62],\"full_literals\":[-51,21,22]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"groupKind3\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-52,50,false],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-52,false,51],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_lower\",\"kind\":3,\"quota\":2,\"grouped\":true}]}"
  "p cnf 52 90\n-3 -1 0\n-8 -3 0\n-9 -3 0\n-10 -3 0\n-10 -4 0\n-10 -5 0\n-10 -6 0\n-10 -7 0\n-11 -3 0\n-12 -7 0\n-13 -12 0\n-14 -4 0\n-15 -4 0\n-15 -6 0\n-15 -9 0\n-16 -10 0\n-18 -3 0\n-18 -8 0\n-18 -10 0\n-18 -11 0\n-18 -14 0\n-18 -16 0\n-18 -17 0\n-19 -5 0\n-19 -7 0\n-20 -13 0\n-22 -4 0\n-22 -6 0\n-22 -9 0\n-22 -17 0\n-23 -5 0\n-23 -10 0\n-23 -16 0\n-23 -19 0\n-24 -15 0\n-25 -3 0\n-25 -8 0\n-25 -11 0\n-25 -18 0\n-25 -21 0\n-25 -24 0\n-5 -13 -15 0\n-6 -12 -14 0\n-6 -13 -14 0\n-3 -16 -17 0\n-2 -3 -24 0\n-3 -23 -24 0\n-17 1 6 7 10 0\n-7 -15 -18 0\n-7 -22 -25 0\n-16 2 25 0\n-26 8 9 11 17 24 0\n-27 5 12 16 0\n-28 19 20 0\n-29 10 23 25 0\n-30 3 4 6 7 0\n-31 18 0\n-32 13 0\n-33 26 0\n-34 27 28 0\n-35 27 0\n-35 28 0\n-36 34 0\n-37 35 0\n-39 33 0\n-38 36 0\n-39 37 0\n-40 29 0\n-41 31 32 0\n-42 31 0\n-42 32 0\n-43 30 41 0\n-44 30 42 0\n-45 30 0\n-44 41 0\n-45 42 0\n-46 40 44 0\n-47 40 45 0\n-46 43 0\n-47 44 0\n-48 45 0\n-49 38 48 0\n-49 39 47 0\n-49 46 0\n49 0\n-50 14 15 0\n-51 21 22 0\n-52 50 0\n-52 51 0\n52 0\n"
  "91 46 0 85 84 0\n92 43 0 91 79 0\n93 50 0 90 88 0\n94 51 0 90 89 0\n95 -45 0 93 74 76 70 57 17 21 86 13 14 49 56 0\n96 -48 0 95 81 0\n97 38 0 96 85 82 0\n98 36 0 97 66 0\n99 34 0 98 63 0\n100 -42 -29 0 93 99 70 71 57 58 19 21 22 39 11 26 86 55 42 34 53 54 60 0\n101 -23 -27 12 0 31 33 53 0\n102 -10 -27 12 0 6 16 53 0\n103 -25 -30 0 94 36 40 87 27 28 50 56 0\n104 -10 -30 0 4 5 7 8 56 0\n105 -13 -23 0 99 34 11 26 101 54 60 0\n106 -47 0 95 93 78 80 68 75 100 73 103 104 55 105 58 69 57 17 21 86 13 14 49 56 0\n107 39 0 106 85 83 0\n108 33 0 107 65 0\n109 37 0 107 67 0\n110 26 0 108 59 0\n111 35 0 109 64 0\n112 27 0 111 61 0\n113 28 0 111 62 0\n114 -4 0 93 12 13 86 0\n115 -6 -12 0 93 14 43 86 0\n116 -3 -23 0 112 110 101 115 10 32 1 2 3 9 47 48 52 0\n117 -18 0 93 110 18 20 21 23 86 15 35 52 0\n118 -31 0 117 57 0\n119 -42 0 118 70 0\n120 -23 0 112 114 118 92 105 101 116 58 10 115 56 69 72 0\n121 -25 0 94 110 37 38 40 41 87 29 30 52 0\n122 30 0 92 119 118 91 121 120 112 72 73 69 77 58 68 11 55 102 0\n123 -10 0 122 104 0\n124 -29 0 123 120 121 55 0\n125 -40 0 124 68 0\n126 44 0 125 91 77 0\n127 41 0 126 75 0\n128 32 0 127 118 69 0\n129 13 0 128 58 0\n130 -12 0 129 11 0\n131 -20 0 129 26 0\n132 19 0 131 113 54 0\n133 -5 0 132 24 0\n134 -7 0 132 25 0\n135 16 0 133 112 130 53 0\n136 2 0 135 121 51 0\n137 -3 0 135 136 110 2 3 9 45 46 52 0\n138 6 0 137 134 122 114 56 0\n139 -15 0 138 14 0\n140 -14 0 138 129 44 0\n141 0 140 139 93 86 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record030.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record030.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record030.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record030.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record030 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS noSame
  exact boundary_unsat S HS noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record030.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record030.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record030.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record030.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record030 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record030_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record030_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record030_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record030_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record030_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record030_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record030_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record030 Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record030_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record030_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record030_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00035.record030
