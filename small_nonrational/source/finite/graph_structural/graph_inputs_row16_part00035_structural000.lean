module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow16Part00035Data
public import GraphInputsRow16Part00035Frames
public import GraphInputsRow16Part00035Leaves
public import GraphInputsRow16Part00035Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

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
