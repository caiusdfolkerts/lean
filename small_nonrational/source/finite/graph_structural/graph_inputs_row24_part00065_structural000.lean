module
prelude
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow24Part00065Data
public import GraphInputsRow24Part00065Frames
public import GraphInputsRow24Part00065Leaves
public import GraphInputsRow24Part00065Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00065.record002
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record002
def vertexColumn : Fields := ⟨10, hexnat% "f4ab0bc3ca6a1e8e6358b61d92e0fad13c6a99a699964b91e6a539595354b51d68d8b52d2b49d0f66338d5334cb31ce4b8ad2b1ac5b0ecc749ca719c9715c37b811c469164382e07ac1a8661384d18a519295152550d0b41d18d1314d0b0ac1b41c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "36db6db6924936da4926d24924934d2493492489249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨43, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "380b03e8e2c0000000", 289356280353521664, hexnat% "400010010800000000", hexnat% "60020020000000000", 1155173321600401408]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "64193e0a0e40000000", 432345570670018560, 2061584302080, hexnat% "20001800000000000", hexnat% "180000200000000000", 70368744177664]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "68013a4beac0000000", 433471468429377536, hexnat% "60001000000000000", hexnat% "100000a00000000000", 1729382274090139648]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1a1809e8e7c0000000", hexnat% "40020020000000000", 505529058172338176, hexnat% "600000000000000000", 4504733498736640, 562949953421312]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1c1b09e86780000000", hexnat% "600000000000000000", 289919227085717504, hexnat% "20020028000000000", 4504733498736640]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "618298bee40000000", hexnat% "400010000000000000", 105559558717440, hexnat% "180200000000000000", hexnat% "200102000000000000", 289356276058554368]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "400f3f8bafc0000000", hexnat% "280000000000000000", 105827994173440, hexnat% "100000000000000000", hexnat% "61000000000000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "460c3f8bac00000000", hexnat% "180200200000000000", hexnat% "200100000040000000", 10737418240, 1152921504606846976, 70647917051904]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c7 c6
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "180a18a8a000000000", hexnat% "600000000000000000", 70651138277376, hexnat% "60001020000000000", 1142461300736, 1161928721041457152, 361976820049903616]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨52, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c10 c5
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c11 c4
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c12 c3
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c13 c2
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c14 c1
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c15 c0
  c16
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record002_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record002_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record002_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record002_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record002_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record002_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record002_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record002_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record002_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00065.record002

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00065.record004
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record004
def vertexColumn : Fields := ⟨10, hexnat% "3e0f43b0dc2f07cb8ad23caaa668ba998e6358b61d92e2b89e0fae1b44f1aa4e9364b91e665554754b46d1743db0ea398ce3a4e5334cb31ce8b8ad2b2ac9b0ee4789d2719c570dee0472a22a91a269164382e07a6146465454554342d0762344d0b0ac1b41c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "6db6d36926db69249b6db6924926936db6d2493492449249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨77, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [14355224214896640, hexnat% "3018000000600000000", 4629735601308958720, hexnat% "24000000400000000000", hexnat% "40008001040000000", 1125902591197184, hexnat% "20000002800000000"]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record004_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record004_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record004_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record004_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record004_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record004_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record004_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record004_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record004_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00065.record004

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00065.record005
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record005
def vertexColumn : Fields := ⟨10, hexnat% "3d0ec4f0bcb8ab23caaa3a99a2ea66398d62d876338ae1b89e0fae1ac4f1aa4e94e4b9995351d52d1b6c3a8e6338e9334e332cc73a2ccb8acab1ac9b0ee4751e2719c570dc4f0bee02e11c0f2c24689a4590e07a6146439195150d50d0b41d90d1342c1b41c4705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "6d24db6936db6da49b6d249249a6db6db6da493492449249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨48, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "6018000001800000000", 29259464704, 4684869512372158464, 47287796087390208, hexnat% "200000250000000000000", hexnat% "100000000000000000000", hexnat% "80000001000028000000"]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record005_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record005_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record005_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record005_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record005_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record005_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record005_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record005_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record005_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00065.record005

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00065.record009
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record009
def vertexColumn : Fields := ⟨10, hexnat% "dc2f2e2b4aaa368ba999564b85e0fae1b46a9664d92e66539555354b53352d2b49d1743db0ea398ce3a4e5354cd32ce8b32e2b4acab26c5b0ee4751e2749c670dc4f4711a458564382e07ac1a84d12a519265151550d0b41d90e2344c5342c2b06d0711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "db6db6924924936936924924da49b692492492489249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "38e67c0c7e6c0000000", hexnat% "4000000000800000000", hexnat% "500010000000000000", hexnat% "200021000000000000", 2251872828129280]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "75c67f9c7ffc0000000", hexnat% "200000000000000000", hexnat% "820000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "57c65f9c7fcc0000000", 12884901888, hexnat% "20200000000000000", hexnat% "2800000000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "17c65f9c5e4c0000000", hexnat% "20200000000000000", hexnat% "4800000000000000000", hexnat% "2000000020200000000", 107374182400]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "16c65f040e0c0000000", hexnat% "2800000000000000000", hexnat% "4000000800800000000", hexnat% "120200010000000000", 6622839570432, 2533347804839936]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨52, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c7 c0
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7fe03f9c7f4c0000000", 288230384741646336, 6917529027641081856, 38654705664]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1fa03f9c7f4c0000000", hexnat% "42000000000000000", 47244640256, hexnat% "2000400000000000000", hexnat% "4004000000000000000"]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨72, by decide⟩ c10 c9
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "68a47e187ffc0000000", hexnat% "400018000000000000", hexnat% "100000000000000000", hexnat% "1040000000000000000", hexnat% "202000400000000000"]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "28a07e087eec0000000", hexnat% "500010000000000000", hexnat% "4004000000000000000", hexnat% "1040000000000000000", 2533347804839936, hexnat% "202000400000000000"]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c13 c12
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c14 c11
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "38e67c1c3f2c0000000", hexnat% "4000000000800000000", hexnat% "600020000000000000", hexnat% "100010040000000000", 2251821288521728]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2ee67c9c7ffc0000000", 13510798882111488, hexnat% "100000000000000000", hexnat% "5000000000000000000"]
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2ca67c907ffc0000000", hexnat% "100010000000000000", hexnat% "4000000800000000000", hexnat% "200020400000000000", hexnat% "1040000000000000000"]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨61, by decide⟩ c18 c17
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "da47d001e1c0000000", hexnat% "3000000000000000000", hexnat% "4000000800800000000", 6622839570432, hexnat% "242000400000000000", 11540542764613632]
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c20 c19
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c21 c16
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2e63e9c0ffc0000000", hexnat% "500010000000000000", hexnat% "5800000000000000000", hexnat% "2000400020000000000", 5497558138880]
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40060e9c07fc0000000", hexnat% "600000000000000000", hexnat% "e0100008000000000", hexnat% "3800000000000000000", hexnat% "100010050000000000", 432347763250823168]
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨61, by decide⟩ c24 c23
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7fe21f9c7f4c0000000", 432345564227567616, 4611686052787126272, 12884901888]
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1fc21f9c7f4c0000000", hexnat% "20200000000000000", 47244640256, hexnat% "4004000000000000000", hexnat% "2000400000000000000"]
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨71, by decide⟩ c27 c26
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "70c65d1c6ffc0000000", hexnat% "400028000000000000", hexnat% "200000000000000000", hexnat% "820000000000000000", hexnat% "100200010000000000"]
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "50c61d1c2fac0000000", hexnat% "600020000000000000", hexnat% "2000400000000000000", hexnat% "820000000000000000", 2256219335032832, hexnat% "100200010000000000"]
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c30 c29
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨52, by decide⟩ c31 c28
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "78004c0067fc0000000", hexnat% "400038000000000000", hexnat% "e0100008000000000", hexnat% "100200010000000000", 6917740133873614848, hexnat% "200001000000000000"]
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1e07f047f600000000", hexnat% "400008000100000000", hexnat% "3800000000040000000", hexnat% "202001000000000000", hexnat% "4004000800880000000"]
  let c35 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40e61c1c1fa80000000", hexnat% "600020000000000000", hexnat% "3800000000040000000", 2256219335032832, 432347763250823168, hexnat% "100010000000000000"]
  let c36 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "22467d9c77fc0000000", hexnat% "400020000000000000", hexnat% "a0000008000000000", hexnat% "100000000000000000", hexnat% "5800000000000000000"]
  let c37 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "6463f9c5ffc0000000", hexnat% "2000400020000000000", hexnat% "a0000000000000000", hexnat% "100000000000000000", hexnat% "5800000000000000000"]
  let c38 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2e63c1c1f700000000", hexnat% "4000000000880000000", hexnat% "2000400020040000000", hexnat% "400038000000000000", hexnat% "100000040000000000", hexnat% "1800000000000000000"]
  let c39 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c38 c37
  let c40 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c39 c36
  let c41 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7020f9c5f600000000", hexnat% "e0100000000000000", 41875931136, 432347763250823168, hexnat% "4004000000000000000", hexnat% "3800000000000000000"]
  let c42 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "78426d08372c0000000", 4611686052787126272, hexnat% "a0100008000000000", hexnat% "500000000000000000", hexnat% "200021400000000000", 2256219335032832]
  let c43 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "11e27d087f200000000", hexnat% "2800000000040000000", hexnat% "4004000000880000000", hexnat% "400028000000000000", 21474836480, hexnat% "200001400000000000"]
  let c44 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "15022d0817200000000", hexnat% "2000400020040000000", hexnat% "e0100008000000000", hexnat% "4004000000880000000", hexnat% "200021400000000000", hexnat% "800000000000000000", 2256219335032832]
  let c45 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c44 c43
  let c46 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨72, by decide⟩ c45 c42
  let c47 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨52, by decide⟩ c46 c41
  let c48 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨61, by decide⟩ c47 c40
  let c49 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c48 c35
  let c50 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c49 c34
  let c51 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c50 c33
  let c52 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c51 c32
  let c53 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c52 c25
  let c54 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c53 c22
  let c55 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c54 c15
  let c56 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c55 c8
  c56
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record009_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record009_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record009_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record009_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record009_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record009_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record009_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record009_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record009_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00065.record009

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00065.record010
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record010
def vertexColumn : Fields := ⟨10, hexnat% "2d4370bcb8ad29a95ab1aa6a5a56358b693a2e4b85e0fae13a559364b9b16a5654d52d4cd4b4ad2745d0f6c3a8e6338d5334cb352d2b1ac3ba1e4731e2749ca725c570dc4fa911c4685a899164382e078d146459295152550d0b41d44c5342c4b0ac1b41c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "db6da69b6da4936936924d24936da4d249b692492249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨74, by decide⟩, ⟨76, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "412069a1047f0000000", 3848290697216, hexnat% "80020000000000000", hexnat% "10040000000000000000", 2379035299251486720, 4611686018427387904]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "242be03c1b0000000", hexnat% "4000400000400000000", hexnat% "10040000000000000000", 2377909400418385920, hexnat% "180000000200000000", 17592186044416]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "100e010603c070000000", 182395787055988736, hexnat% "4100000000500000000", 6917555415920148480, 13510807472046080, 288230376151711744]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4632e0bc0f0000000", hexnat% "10000000100000000000", 328762777093013504, hexnat% "4100000000400000000", hexnat% "a0000000000000000", 8589934592]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4000603c030000000", 254453381093916672, hexnat% "4000400000500000000", hexnat% "10004000100000000000", hexnat% "1a0000000000000000", 13510807472046080, 2305851806380457984]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨66, by decide⟩ c5 c2
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c6 c1
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c7 c0
  c8
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record010_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record010_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record010_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record010_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record010_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record010_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record010_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record010_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record010_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00065.record010

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00065.record019
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record019
def vertexColumn : Fields := ⟨10, hexnat% "2e4b8ac6a9a66399563592e2b85e0fae1b16a5994e5554d54b4ad1743d98ce394d5334e2b4acab16c3ba1d8791d4789d2719c970dc8f13d1cb0aa2468c6299161590e0b81eb06a1464c5295151550d0b41da0e4330e2328d1314d0b0ac1b41c8711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "349349249249a492492492492492492491249249249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2, 3]
def candidates : List (Fin raw.n) := [⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1fa9f031daa0000000000", 63613344736608256, 94420561035264, 3746994889972252672, 14411518807585587200, hexnat% "1600000000000000000", hexnat% "4000000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1f81f531daa0000000000", 63613344736608256, 94420561035264, hexnat% "1a00000000000000000", hexnat% "6400000000000000000", 3170534137668829184, 9223372036854775808]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .size 3
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨65, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨76, by decide⟩ c3 c0
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨76, by decide⟩ c2 c0
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨80, by decide⟩ c5 c4
  c6
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record019_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record019_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record019_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record019_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record019_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record019_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record019_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record019_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record019_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00065.record019

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00065.record017
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "2e4ab2e236ac6a9a66399563392e2b85e0fae1aa4d9b16a5994e595555a34cd8b52d2b45d0f6c3a8e6338d5334d8b32d2b26c5b0ee8791d4731e2749ca719c3723c4f470aa469161590e0b81eb06a12a51991625454554342d074c328d1314d0b22c2b06d0711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "36db6da69249349349b4924934924924d2492492249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record017 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record017 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record017.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record017.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record017.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 34), (facetIndex 40), (facetIndex 50), (facetIndex 62), (facetIndex 76)]))
 (.leaf ([(facetIndex 53), (facetIndex 66), (facetIndex 69), (facetIndex 70)])))
 (.branch 3
 (.leaf ([(facetIndex 32), (facetIndex 33), (facetIndex 43), (facetIndex 44), (facetIndex 45), (facetIndex 46), (facetIndex 47), (facetIndex 48)]))
 (.leaf ([(facetIndex 71), (facetIndex 72), (facetIndex 74)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 39), (facetIndex 49), (facetIndex 51), (facetIndex 54)]))
 (.leaf ([(facetIndex 41), (facetIndex 63), (facetIndex 65), (facetIndex 67)])))
 (.branch 7
 (.leaf ([(facetIndex 55), (facetIndex 56), (facetIndex 58)]))
 (.branch 8
 (.leaf ([(facetIndex 36), (facetIndex 57), (facetIndex 73)]))
 (.leaf ([(facetIndex 35), (facetIndex 37), (facetIndex 38), (facetIndex 59)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "3733110515050008676641040422222205048878022z20;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 9
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 60), (facetIndex 68)]))
 (.branch 2
 (.leaf ([(facetIndex 75), (facetIndex 81)]))
 (.leaf ([(facetIndex 42), (facetIndex 52), (facetIndex 64)]))))
 (.branch 5
 (.branch 4
 (.leaf ([(facetIndex 77), (facetIndex 78), (facetIndex 79)]))
 (.leaf ([(facetIndex 80), (facetIndex 82), (facetIndex 84)])))
 (.branch 6
 (.leaf ([(facetIndex 61)]))
 (.leaf ([(facetIndex 83)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "4d0c6d820000000202800000200000008z1f;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 7
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped2_0000 : List Nat := [0]
def grouped2_0001 : List Nat := [0, 1]
def grouped2_0002 : List Nat := [0, 1, 2, 3]
def grouped2_0004 : List Nat := [1]
def grouped2_0005 : List Nat := [2]
def grouped2_0006 : List Nat := [2, 3]
def grouped2_0007 : List Nat := [3]
def grouped2_0008 : List Nat := [4]
def grouped2_0009 : List Nat := [4, 5]
def grouped2_0010 : List Nat := [4, 5, 6, 7, 8]
def grouped2_0011 : List Nat := [5]
def grouped2_0012 : List Nat := [6]
def grouped2_0013 : List Nat := [6, 7, 8]
def grouped2_0014 : List Nat := [7]
def grouped2_0015 : List Nat := [7, 8]
def grouped2_0016 : List Nat := [8]
def grouped3_0017 : List Nat := [0]
def grouped3_0018 : List Nat := [0, 1, 2]
def grouped3_0020 : List Nat := [1]
def grouped3_0021 : List Nat := [1, 2]
def grouped3_0022 : List Nat := [2]
def grouped3_0023 : List Nat := [3]
def grouped3_0024 : List Nat := [3, 4]
def grouped3_0025 : List Nat := [3, 4, 5, 6]
def grouped3_0026 : List Nat := [4]
def grouped3_0027 : List Nat := [5]
def grouped3_0028 : List Nat := [5, 6]
def grouped3_0029 : List Nat := [6]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record017 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record017_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00065.record017" "{\"atoms\":[{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group\",\"kind\":2,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0015\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0015\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0021\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0018\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0024\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0024\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0028\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0028\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0025\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0025\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00065.record017" 100

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00065.record017" "{\"ridges\":[[12,194],[18,548],[19,580],[22,545],[23,704],[25,38],[26,14],[34,38],[35,35],[35,38],[35,70],[37,38],[37,259],[37,262],[38,38],[38,548],[40,70],[41,70],[41,580],[47,194],[48,259],[49,193],[49,194],[50,259],[51,194],[53,672],[54,194],[54,704],[55,44],[57,44],[61,652],[63,517],[63,580],[64,228],[65,548],[65,580],[66,548],[67,580],[67,704],[69,545],[70,672],[70,704],[71,38],[72,14],[72,70],[73,14],[73,38],[74,38],[77,38],[77,70],[77,228],[78,38],[78,610],[79,38],[80,70],[82,610],[83,652],[84,228]],\"owners\":[[35,35,[6,11,43,46,53],[2,34,37,38,51,52]],[37,262,[26,28,76],[4,40,74]],[49,193,[23,60,64,67,70],[12,39,47,51,68]],[12,194,[75,77,80,81,82],[39,47,49,51,54]],[47,194,[77,80,82],[12,39,49,51,54,75,81]],[49,194,[75,77,80,82],[12,39,47,51,54,81]],[51,194,[75,80,81],[12,39,47,49,54,77,82]],[54,194,[75,77,81],[12,39,47,49,51,80,82]],[55,44,[25,73,74,83],[14,57,58,59,71]],[57,44,[25,71,74],[14,55,58,59,73,83]],[63,517,[18,38,42,59,61,66],[19,41,67]],[22,545,[18,38,52,59,65],[53,69,70]],[69,545,[18,38,52,65],[22,53,59,70]],[18,548,[78,79,83,84],[38,59,65,66]],[38,548,[83,84],[18,59,65,66,78,79]],[65,548,[79,83],[18,38,59,66,78,84]],[66,548,[78],[18,38,59,65,79,83,84]],[19,580,[78,80,84],[41,63,65,67]],[41,580,[84],[19,63,65,67,78,80]],[63,580,[78,80,84],[19,41,65,67]],[65,580,[80],[19,41,63,67,78,84]],[67,580,[78],[19,41,63,65,80,84]],[53,672,[83,84],[22,66,69,70,79,82]],[70,672,[79,83],[22,53,66,69,82,84]],[23,704,[80,82,84],[54,67,70]],[54,704,[84],[23,67,70,80,82]],[67,704,[82],[23,54,70,80,84]],[70,704,[80],[23,54,67,82,84]],[78,610,[52,82],[]],[82,610,[52,78],[]],[61,652,[83],[]],[83,652,[61],[]],[64,228,[77,84],[]],[77,228,[64,84],[]],[84,228,[64,77],[]]],\"edges\":[[23,[18,19,38,41,42,59,61,63,65,66,67,78,79,80,83,84]],[38,[18,22,38,52,53,59,65,66,69,70,78,79,82,83,84]],[39,[12,23,39,47,49,51,54,60,64,67,68,70,75,77,80,81,82,84]]],\"groupings\":[2,3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00065.record017" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00065.record017\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-16,-15],[-25,-16],[-28,-19],[-29,-22],[-29,-24],[-29,-28],[-31,-21],[-32,-20],[-33,-17],[-37,-16],[-38,-15],[-38,-34],[-38,-36],[-38,-37],[-40,-18],[-42,-14],[-42,-18],[-42,-35],[-42,-39],[-42,-41],[-43,-32],[-43,-33],[-44,-38],[-45,-15],[-45,-36],[-45,-38],[-46,-40],[-48,-2],[-48,-15],[-48,-36],[-48,-38],[-49,-40],[-50,-34],[-51,-10],[-51,-11],[-51,-13],[-51,-23],[-51,-26],[-51,-35],[-52,-1],[-52,-18],[-52,-22],[-52,-25],[-52,-43],[-52,-45],[-52,-46],[-52,-50],[-53,-16],[-53,-37],[-53,-52],[-55,-51],[-56,-21],[-56,-40],[-56,-44],[-56,-45],[-56,-46],[-57,-30],[-57,-56],[-58,-52],[-58,-56],[-59,-15],[-59,-36],[-59,-40],[-59,-52],[-59,-56],[-61,-14],[-61,-21],[-61,-30],[-61,-44],[-61,-49],[-63,-12],[-63,-14],[-63,-15],[-63,-18],[-63,-30],[-63,-36],[-63,-40],[-63,-44],[-63,-46],[-63,-49],[-63,-52],[-63,-54],[-63,-59],[-63,-61],[-9,-51,-52],[-14,1,2,22,25,32],[-8,-16,-57],[-8,-16,-58],[-13,-52,-57],[-14,-50,-58],[-14,-53,-58],[-16,-50,-56],[-16,-50,-57],[-16,-50,-58],[-16,-52,-57],[-17,-50,-56],[-17,-53,-56],[-14,-51,-59],[-19,-51,-56],[-20,-51,-56],[-16,-27,-29],[-16,9,10,55],[-28,7,39,43,46,49],[-3,54,56,59,60,61],[-26,56,59,61],[-28,54,56,59,61],[-30,54,59,60],[-33,54,56,60],[-34,8,52,53,62],[-36,8,50,53],[-42,4,17,21,38,40,45],[-6,4,17,31,38,44],[-48,4,17,31,44],[-4,57,58,62,63],[-17,62,63],[-44,58,62],[-45,57],[-5,57,59,63],[-20,63],[-42,57,59,63],[-44,59],[-46,57],[-32,62,63],[-49,58,62],[-7,59,61,63],[-33,63],[-46,61],[-49,59],[-57,31,61],[-61,31,57],[-40,62],[-62,40],[-43,56,63],[-56,43,63],[-63,43,56],[-64,13,19,29,41,55],[-65,32,45,48,49],[-66,11,12,22,23,24,25,26,27],[-67,50,51,53],[-50,67],[-53,67],[-68,18,28,30,33],[-69,20,42,44,46],[-70,34,35,37],[-71,15,36,52],[-72,14,16,17,38],[-73,64],[-73,65],[-74,66],[-74,67],[-75,73,74],[-76,73],[-76,74],[-77,68],[-77,69],[-78,71,72],[-79,71],[-79,72],[-80,70,79],[-81,70],[-80,78],[-81,79],[-82,77,81],[-83,77],[-82,80],[-83,81],[-84,75],[-84,76,83],[-84,82],[84],[-39,85],[-47,85],[-54,86],[-60,86],[-31,87],[-43,87],[-88,56,57,58],[-56,88],[-57,88],[-58,88],[-89,59,61,63],[-59,89],[-61,89],[-63,89],[-90,40],[-40,90],[-91,62],[-62,91],[-87,92],[-86,92],[-92,93],[-85,93],[-89,94],[-95,88],[-95,89],[-88,-89,95],[-96,90,91],[-97,90],[-90,-91,97],[-97,98],[-98,95,96],[-94,-97,99],[-95,98],[-99,100],[-93,-98,100],[-100],[4,5,17,20,21,38,40,42,44,45,46,57,58,59,62,63],[4,6,17,31,32,38,44,45,48,49,57,58,61,62,63],[3,7,18,26,28,30,33,39,43,46,47,49,54,56,59,60,61,63]],\"atoms\":[{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group\",\"index\":8,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":37,\"b\":36},{\"tag\":\"incompatible\",\"a\":46,\"b\":37},{\"tag\":\"incompatible\",\"a\":49,\"b\":40},{\"tag\":\"incompatible\",\"a\":50,\"b\":43},{\"tag\":\"incompatible\",\"a\":50,\"b\":45},{\"tag\":\"incompatible\",\"a\":50,\"b\":49},{\"tag\":\"incompatible\",\"a\":52,\"b\":42},{\"tag\":\"incompatible\",\"a\":53,\"b\":41},{\"tag\":\"incompatible\",\"a\":54,\"b\":38},{\"tag\":\"incompatible\",\"a\":58,\"b\":37},{\"tag\":\"incompatible\",\"a\":59,\"b\":36},{\"tag\":\"incompatible\",\"a\":59,\"b\":55},{\"tag\":\"incompatible\",\"a\":59,\"b\":57},{\"tag\":\"incompatible\",\"a\":59,\"b\":58},{\"tag\":\"incompatible\",\"a\":61,\"b\":39},{\"tag\":\"incompatible\",\"a\":63,\"b\":35},{\"tag\":\"incompatible\",\"a\":63,\"b\":39},{\"tag\":\"incompatible\",\"a\":63,\"b\":56},{\"tag\":\"incompatible\",\"a\":63,\"b\":60},{\"tag\":\"incompatible\",\"a\":63,\"b\":62},{\"tag\":\"incompatible\",\"a\":64,\"b\":53},{\"tag\":\"incompatible\",\"a\":64,\"b\":54},{\"tag\":\"incompatible\",\"a\":65,\"b\":59},{\"tag\":\"incompatible\",\"a\":66,\"b\":36},{\"tag\":\"incompatible\",\"a\":66,\"b\":57},{\"tag\":\"incompatible\",\"a\":66,\"b\":59},{\"tag\":\"incompatible\",\"a\":67,\"b\":61},{\"tag\":\"incompatible\",\"a\":69,\"b\":11},{\"tag\":\"incompatible\",\"a\":69,\"b\":36},{\"tag\":\"incompatible\",\"a\":69,\"b\":57},{\"tag\":\"incompatible\",\"a\":69,\"b\":59},{\"tag\":\"incompatible\",\"a\":70,\"b\":61},{\"tag\":\"incompatible\",\"a\":71,\"b\":55},{\"tag\":\"incompatible\",\"a\":72,\"b\":28},{\"tag\":\"incompatible\",\"a\":72,\"b\":32},{\"tag\":\"incompatible\",\"a\":72,\"b\":34},{\"tag\":\"incompatible\",\"a\":72,\"b\":44},{\"tag\":\"incompatible\",\"a\":72,\"b\":47},{\"tag\":\"incompatible\",\"a\":72,\"b\":56},{\"tag\":\"incompatible\",\"a\":73,\"b\":6},{\"tag\":\"incompatible\",\"a\":73,\"b\":39},{\"tag\":\"incompatible\",\"a\":73,\"b\":43},{\"tag\":\"incompatible\",\"a\":73,\"b\":46},{\"tag\":\"incompatible\",\"a\":73,\"b\":64},{\"tag\":\"incompatible\",\"a\":73,\"b\":66},{\"tag\":\"incompatible\",\"a\":73,\"b\":67},{\"tag\":\"incompatible\",\"a\":73,\"b\":71},{\"tag\":\"incompatible\",\"a\":74,\"b\":37},{\"tag\":\"incompatible\",\"a\":74,\"b\":58},{\"tag\":\"incompatible\",\"a\":74,\"b\":73},{\"tag\":\"incompatible\",\"a\":76,\"b\":72},{\"tag\":\"incompatible\",\"a\":77,\"b\":42},{\"tag\":\"incompatible\",\"a\":77,\"b\":61},{\"tag\":\"incompatible\",\"a\":77,\"b\":65},{\"tag\":\"incompatible\",\"a\":77,\"b\":66},{\"tag\":\"incompatible\",\"a\":77,\"b\":67},{\"tag\":\"incompatible\",\"a\":78,\"b\":51},{\"tag\":\"incompatible\",\"a\":78,\"b\":77},{\"tag\":\"incompatible\",\"a\":79,\"b\":73},{\"tag\":\"incompatible\",\"a\":79,\"b\":77},{\"tag\":\"incompatible\",\"a\":80,\"b\":36},{\"tag\":\"incompatible\",\"a\":80,\"b\":57},{\"tag\":\"incompatible\",\"a\":80,\"b\":61},{\"tag\":\"incompatible\",\"a\":80,\"b\":73},{\"tag\":\"incompatible\",\"a\":80,\"b\":77},{\"tag\":\"incompatible\",\"a\":82,\"b\":35},{\"tag\":\"incompatible\",\"a\":82,\"b\":42},{\"tag\":\"incompatible\",\"a\":82,\"b\":51},{\"tag\":\"incompatible\",\"a\":82,\"b\":65},{\"tag\":\"incompatible\",\"a\":82,\"b\":70},{\"tag\":\"incompatible\",\"a\":84,\"b\":33},{\"tag\":\"incompatible\",\"a\":84,\"b\":35},{\"tag\":\"incompatible\",\"a\":84,\"b\":36},{\"tag\":\"incompatible\",\"a\":84,\"b\":39},{\"tag\":\"incompatible\",\"a\":84,\"b\":51},{\"tag\":\"incompatible\",\"a\":84,\"b\":57},{\"tag\":\"incompatible\",\"a\":84,\"b\":61},{\"tag\":\"incompatible\",\"a\":84,\"b\":65},{\"tag\":\"incompatible\",\"a\":84,\"b\":67},{\"tag\":\"incompatible\",\"a\":84,\"b\":70},{\"tag\":\"incompatible\",\"a\":84,\"b\":73},{\"tag\":\"incompatible\",\"a\":84,\"b\":75},{\"tag\":\"incompatible\",\"a\":84,\"b\":80},{\"tag\":\"incompatible\",\"a\":84,\"b\":82},{\"tag\":\"three\",\"ridge\":14,\"vertices\":[26,72,73]},{\"tag\":\"mate\",\"ridge\":35,\"a\":35,\"owners\":[6,11,43,46,53]},{\"tag\":\"three\",\"ridge\":38,\"vertices\":[25,37,78]},{\"tag\":\"three\",\"ridge\":38,\"vertices\":[25,37,79]},{\"tag\":\"three\",\"ridge\":38,\"vertices\":[34,73,78]},{\"tag\":\"three\",\"ridge\":38,\"vertices\":[35,71,79]},{\"tag\":\"three\",\"ridge\":38,\"vertices\":[35,74,79]},{\"tag\":\"three\",\"ridge\":38,\"vertices\":[37,71,77]},{\"tag\":\"three\",\"ridge\":38,\"vertices\":[37,71,78]},{\"tag\":\"three\",\"ridge\":38,\"vertices\":[37,71,79]},{\"tag\":\"three\",\"ridge\":38,\"vertices\":[37,73,78]},{\"tag\":\"three\",\"ridge\":38,\"vertices\":[38,71,77]},{\"tag\":\"three\",\"ridge\":38,\"vertices\":[38,74,77]},{\"tag\":\"three\",\"ridge\":70,\"vertices\":[35,72,80]},{\"tag\":\"three\",\"ridge\":70,\"vertices\":[40,72,77]},{\"tag\":\"three\",\"ridge\":70,\"vertices\":[41,72,77]},{\"tag\":\"three\",\"ridge\":259,\"vertices\":[37,48,50]},{\"tag\":\"mate\",\"ridge\":262,\"a\":37,\"owners\":[26,28,76]},{\"tag\":\"mate\",\"ridge\":193,\"a\":49,\"owners\":[23,60,64,67,70]},{\"tag\":\"mate\",\"ridge\":194,\"a\":12,\"owners\":[75,77,80,81,82]},{\"tag\":\"mate\",\"ridge\":194,\"a\":47,\"owners\":[77,80,82]},{\"tag\":\"mate\",\"ridge\":194,\"a\":49,\"owners\":[75,77,80,82]},{\"tag\":\"mate\",\"ridge\":194,\"a\":51,\"owners\":[75,80,81]},{\"tag\":\"mate\",\"ridge\":194,\"a\":54,\"owners\":[75,77,81]},{\"tag\":\"mate\",\"ridge\":44,\"a\":55,\"owners\":[25,73,74,83]},{\"tag\":\"mate\",\"ridge\":44,\"a\":57,\"owners\":[25,71,74]},{\"tag\":\"mate\",\"ridge\":517,\"a\":63,\"owners\":[18,38,42,59,61,66]},{\"tag\":\"mate\",\"ridge\":545,\"a\":22,\"owners\":[18,38,52,59,65]},{\"tag\":\"mate\",\"ridge\":545,\"a\":69,\"owners\":[18,38,52,65]},{\"tag\":\"mate\",\"ridge\":548,\"a\":18,\"owners\":[78,79,83,84]},{\"tag\":\"mate\",\"ridge\":548,\"a\":38,\"owners\":[83,84]},{\"tag\":\"mate\",\"ridge\":548,\"a\":65,\"owners\":[79,83]},{\"tag\":\"mate\",\"ridge\":548,\"a\":66,\"owners\":[78]},{\"tag\":\"mate\",\"ridge\":580,\"a\":19,\"owners\":[78,80,84]},{\"tag\":\"mate\",\"ridge\":580,\"a\":41,\"owners\":[84]},{\"tag\":\"mate\",\"ridge\":580,\"a\":63,\"owners\":[78,80,84]},{\"tag\":\"mate\",\"ridge\":580,\"a\":65,\"owners\":[80]},{\"tag\":\"mate\",\"ridge\":580,\"a\":67,\"owners\":[78]},{\"tag\":\"mate\",\"ridge\":672,\"a\":53,\"owners\":[83,84]},{\"tag\":\"mate\",\"ridge\":672,\"a\":70,\"owners\":[79,83]},{\"tag\":\"mate\",\"ridge\":704,\"a\":23,\"owners\":[80,82,84]},{\"tag\":\"mate\",\"ridge\":704,\"a\":54,\"owners\":[84]},{\"tag\":\"mate\",\"ridge\":704,\"a\":67,\"owners\":[82]},{\"tag\":\"mate\",\"ridge\":704,\"a\":70,\"owners\":[80]},{\"tag\":\"mate\",\"ridge\":610,\"a\":78,\"owners\":[52,82]},{\"tag\":\"mate\",\"ridge\":610,\"a\":82,\"owners\":[52,78]},{\"tag\":\"mate\",\"ridge\":652,\"a\":61,\"owners\":[83]},{\"tag\":\"mate\",\"ridge\":652,\"a\":83,\"owners\":[61]},{\"tag\":\"mate\",\"ridge\":228,\"a\":64,\"owners\":[77,84]},{\"tag\":\"mate\",\"ridge\":228,\"a\":77,\"owners\":[64,84]},{\"tag\":\"mate\",\"ridge\":228,\"a\":84,\"owners\":[64,77]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[34,40,50,62,76],\"full_literals\":[-64,13,19,29,41,55]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[53,66,69,70],\"full_literals\":[-65,32,45,48,49]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[32,33,43,44,45,46,47,48],\"full_literals\":[-66,11,12,22,23,24,25,26,27]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[71,72,74],\"full_literals\":[-67,50,51,53]},{\"tag\":\"group_take\",\"kind\":2,\"index\":3,\"member\":71,\"full_literals\":[-50,67]},{\"tag\":\"group_take\",\"kind\":2,\"index\":3,\"member\":74,\"full_literals\":[-53,67]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[39,49,51,54],\"full_literals\":[-68,18,28,30,33]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[41,63,65,67],\"full_literals\":[-69,20,42,44,46]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[55,56,58],\"full_literals\":[-70,34,35,37]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[36,57,73],\"full_literals\":[-71,15,36,52]},{\"tag\":\"group_or\",\"kind\":2,\"index\":8,\"members\":[35,37,38,59],\"full_literals\":[-72,14,16,17,38]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-73,64,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-73,false,65],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-74,66,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-74,false,67],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-75,73,74],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-76,73,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-76,false,74],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-77,68,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-77,false,69],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0014\",\"right_name\":\"grouped2_0016\",\"joined_name\":\"grouped2_0015\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-78,71,72],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0014\",\"right_name\":\"grouped2_0016\",\"joined_name\":\"grouped2_0015\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-79,71,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0014\",\"right_name\":\"grouped2_0016\",\"joined_name\":\"grouped2_0015\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-79,false,72],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0013\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-80,70,79],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0013\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-81,70,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0013\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-80,false,78],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0013\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-81,false,79],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-82,77,81],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":1,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-83,77,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-82,false,80],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-83,false,81],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":2,\"b\":5,\"direction\":\"backward\",\"full_literals\":[-84,75,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-84,76,83],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-84,false,82],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":60,\"full_literals\":[-39,85]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":68,\"full_literals\":[-47,85]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":75,\"full_literals\":[-54,86]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":81,\"full_literals\":[-60,86]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":52,\"full_literals\":[-31,87]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":64,\"full_literals\":[-43,87]},{\"tag\":\"group_or\",\"kind\":3,\"index\":3,\"members\":[77,78,79],\"full_literals\":[-88,56,57,58]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":77,\"full_literals\":[-56,88]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":78,\"full_literals\":[-57,88]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":79,\"full_literals\":[-58,88]},{\"tag\":\"group_or\",\"kind\":3,\"index\":4,\"members\":[80,82,84],\"full_literals\":[-89,59,61,63]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":80,\"full_literals\":[-59,89]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":82,\"full_literals\":[-61,89]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":84,\"full_literals\":[-63,89]},{\"tag\":\"group_or\",\"kind\":3,\"index\":5,\"members\":[61],\"full_literals\":[-90,40]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":61,\"full_literals\":[-40,90]},{\"tag\":\"group_or\",\"kind\":3,\"index\":6,\"members\":[83],\"full_literals\":[-91,62]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":83,\"full_literals\":[-62,91]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0021\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-87,92],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0021\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-86,false,92],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0018\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-92,93],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0018\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-85,false,93],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0024\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-89,94],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0024\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-95,88,false],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0024\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-95,false,89],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0024\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-88,-89,95],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0027\",\"right_name\":\"grouped3_0029\",\"joined_name\":\"grouped3_0028\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-96,90,91],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0027\",\"right_name\":\"grouped3_0029\",\"joined_name\":\"grouped3_0028\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-97,90,false],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0027\",\"right_name\":\"grouped3_0029\",\"joined_name\":\"grouped3_0028\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-90,-91,97],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0024\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0025\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-97,98],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0024\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0025\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-98,95,96],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0024\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0025\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-94,-97,99],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0024\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0025\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-95,false,98],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0025\",\"joined_name\":\"groupKind3\",\"a\":0,\"b\":3,\"direction\":\"forward\",\"full_literals\":[false,-99,100],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0025\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-93,-98,100],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":23,\"owners\":[18,19,38,41,42,59,61,63,65,66,67,78,79,80,83,84]},{\"tag\":\"edge\",\"edge\":38,\"owners\":[18,22,38,52,53,59,65,66,69,70,78,79,82,83,84]},{\"tag\":\"edge\",\"edge\":39,\"owners\":[12,23,39,47,49,51,54,60,64,67,68,70,75,77,80,81,82,84]}]}"
  "p cnf 100 209\n-16 -15 0\n-25 -16 0\n-28 -19 0\n-29 -22 0\n-29 -24 0\n-29 -28 0\n-31 -21 0\n-32 -20 0\n-33 -17 0\n-37 -16 0\n-38 -15 0\n-38 -34 0\n-38 -36 0\n-38 -37 0\n-40 -18 0\n-42 -14 0\n-42 -18 0\n-42 -35 0\n-42 -39 0\n-42 -41 0\n-43 -32 0\n-43 -33 0\n-44 -38 0\n-45 -15 0\n-45 -36 0\n-45 -38 0\n-46 -40 0\n-48 -2 0\n-48 -15 0\n-48 -36 0\n-48 -38 0\n-49 -40 0\n-50 -34 0\n-51 -10 0\n-51 -11 0\n-51 -13 0\n-51 -23 0\n-51 -26 0\n-51 -35 0\n-52 -1 0\n-52 -18 0\n-52 -22 0\n-52 -25 0\n-52 -43 0\n-52 -45 0\n-52 -46 0\n-52 -50 0\n-53 -16 0\n-53 -37 0\n-53 -52 0\n-55 -51 0\n-56 -21 0\n-56 -40 0\n-56 -44 0\n-56 -45 0\n-56 -46 0\n-57 -30 0\n-57 -56 0\n-58 -52 0\n-58 -56 0\n-59 -15 0\n-59 -36 0\n-59 -40 0\n-59 -52 0\n-59 -56 0\n-61 -14 0\n-61 -21 0\n-61 -30 0\n-61 -44 0\n-61 -49 0\n-63 -12 0\n-63 -14 0\n-63 -15 0\n-63 -18 0\n-63 -30 0\n-63 -36 0\n-63 -40 0\n-63 -44 0\n-63 -46 0\n-63 -49 0\n-63 -52 0\n-63 -54 0\n-63 -59 0\n-63 -61 0\n-9 -51 -52 0\n-14 1 2 22 25 32 0\n-8 -16 -57 0\n-8 -16 -58 0\n-13 -52 -57 0\n-14 -50 -58 0\n-14 -53 -58 0\n-16 -50 -56 0\n-16 -50 -57 0\n-16 -50 -58 0\n-16 -52 -57 0\n-17 -50 -56 0\n-17 -53 -56 0\n-14 -51 -59 0\n-19 -51 -56 0\n-20 -51 -56 0\n-16 -27 -29 0\n-16 9 10 55 0\n-28 7 39 43 46 49 0\n-3 54 56 59 60 61 0\n-26 56 59 61 0\n-28 54 56 59 61 0\n-30 54 59 60 0\n-33 54 56 60 0\n-34 8 52 53 62 0\n-36 8 50 53 0\n-42 4 17 21 38 40 45 0\n-6 4 17 31 38 44 0\n-48 4 17 31 44 0\n-4 57 58 62 63 0\n-17 62 63 0\n-44 58 62 0\n-45 57 0\n-5 57 59 63 0\n-20 63 0\n-42 57 59 63 0\n-44 59 0\n-46 57 0\n-32 62 63 0\n-49 58 62 0\n-7 59 61 63 0\n-33 63 0\n-46 61 0\n-49 59 0\n-57 31 61 0\n-61 31 57 0\n-40 62 0\n-62 40 0\n-43 56 63 0\n-56 43 63 0\n-63 43 56 0\n-64 13 19 29 41 55 0\n-65 32 45 48 49 0\n-66 11 12 22 23 24 25 26 27 0\n-67 50 51 53 0\n-50 67 0\n-53 67 0\n-68 18 28 30 33 0\n-69 20 42 44 46 0\n-70 34 35 37 0\n-71 15 36 52 0\n-72 14 16 17 38 0\n-73 64 0\n-73 65 0\n-74 66 0\n-74 67 0\n-75 73 74 0\n-76 73 0\n-76 74 0\n-77 68 0\n-77 69 0\n-78 71 72 0\n-79 71 0\n-79 72 0\n-80 70 79 0\n-81 70 0\n-80 78 0\n-81 79 0\n-82 77 81 0\n-83 77 0\n-82 80 0\n-83 81 0\n-84 75 0\n-84 76 83 0\n-84 82 0\n84 0\n-39 85 0\n-47 85 0\n-54 86 0\n-60 86 0\n-31 87 0\n-43 87 0\n-88 56 57 58 0\n-56 88 0\n-57 88 0\n-58 88 0\n-89 59 61 63 0\n-59 89 0\n-61 89 0\n-63 89 0\n-90 40 0\n-40 90 0\n-91 62 0\n-62 91 0\n-87 92 0\n-86 92 0\n-92 93 0\n-85 93 0\n-89 94 0\n-95 88 0\n-95 89 0\n-88 -89 95 0\n-96 90 91 0\n-97 90 0\n-90 -91 97 0\n-97 98 0\n-98 95 96 0\n-94 -97 99 0\n-95 98 0\n-99 100 0\n-93 -98 100 0\n-100 0\n4 5 17 20 21 38 40 42 44 45 46 57 58 59 62 63 0\n4 6 17 31 32 38 44 45 48 49 57 58 61 62 63 0\n3 7 18 26 28 30 33 39 43 46 47 49 54 56 59 60 61 63 0\n"
  "210 75 0 170 167 0\n211 82 0 170 169 0\n212 80 0 211 165 0\n213 78 0 212 161 0\n214 -99 0 206 204 0\n215 -97 93 0 214 191 190 174 173 189 176 192 172 171 198 202 185 193 15 27 32 53 63 77 183 105 106 108 104 125 107 209 0\n216 -90 97 0 185 199 131 188 0\n217 -16 -67 -70 52 -58 62 0 10 48 88 94 109 139 144 39 0\n218 -51 16 -59 17 0 213 212 62 61 64 145 157 159 156 39 98 146 12 14 144 0\n219 -50 16 -69 -70 -72 -58 46 17 20 0 33 90 146 14 23 144 143 18 0\n220 61 63 -98 0 206 213 212 211 170 205 215 216 186 132 115 191 189 176 134 119 187 197 201 195 194 175 127 129 181 177 61 62 64 145 156 157 162 159 166 163 168 155 153 150 217 218 219 139 49 91 146 12 23 144 143 18 0\n221 -38 52 49 32 0 170 11 13 26 31 145 137 157 148 162 152 166 168 0\n222 52 -67 -70 -72 -57 49 14 17 32 62 0 221 146 10 48 87 93 139 109 39 144 0\n223 -67 -70 62 -72 -57 49 14 17 32 0 222 47 50 95 139 146 39 12 14 144 0\n224 -52 -65 -72 -57 49 14 17 32 0 45 95 137 146 31 0\n225 67 -72 -57 49 14 17 32 0 210 170 140 141 150 153 151 168 148 166 162 157 224 221 146 1 87 145 110 0\n226 -67 -72 62 32 -57 49 14 17 0 170 212 223 159 160 157 166 168 152 148 224 221 146 1 48 87 93 145 110 0\n227 -72 -57 49 14 17 32 62 0 225 226 0\n228 -36 -65 49 32 0 25 30 137 0\n229 -15 -65 49 32 0 24 29 137 0\n230 63 -98 0 206 213 211 170 205 215 216 186 132 191 189 175 119 126 123 115 220 66 68 69 70 130 227 158 156 162 166 163 168 154 155 152 153 147 148 150 228 229 145 41 46 47 50 89 142 143 139 3 6 20 51 136 0\n231 -51 38 -98 0 206 213 211 170 230 73 76 81 145 157 162 166 168 153 149 152 147 163 155 154 156 205 191 189 176 135 79 78 75 74 72 71 35 36 37 38 51 99 100 143 20 136 4 5 6 142 9 146 2 101 138 0\n232 -50 38 -98 0 206 213 230 73 76 81 145 156 205 191 189 176 135 72 92 96 146 0\n233 38 -98 0 206 213 170 230 73 76 81 145 157 162 166 168 153 150 156 205 191 189 176 135 72 231 232 139 48 97 146 0\n234 -98 0 212 211 230 73 76 78 79 80 81 145 157 162 159 163 155 233 12 14 221 144 8 18 143 0\n235 -97 0 234 200 0\n236 -95 0 234 203 0\n237 -90 0 235 216 0\n238 -40 0 237 186 0\n239 -62 0 238 132 0\n240 -63 43 0 236 135 184 178 196 0\n241 -32 0 239 21 123 240 0\n242 -56 38 0 236 239 238 52 54 55 56 58 60 65 178 196 184 119 115 118 120 114 207 0\n243 77 49 52 0 211 170 241 163 164 162 168 157 152 148 228 229 145 0\n244 89 43 63 -69 -68 49 0 126 119 182 183 121 125 127 143 17 19 120 103 57 142 0\n245 63 -69 -68 38 49 0 236 238 239 241 242 119 115 133 244 196 179 180 117 122 116 114 143 111 7 67 113 112 208 0\n246 49 52 0 241 221 242 243 154 155 245 74 75 82 83 84 240 106 22 142 0\n247 -49 0 239 236 124 128 180 182 196 0\n248 52 0 247 246 0\n249 -1 0 248 40 0\n250 -22 0 248 42 0\n251 -25 0 248 43 0\n252 -43 0 248 44 0\n253 -45 0 248 45 0\n254 -46 0 248 46 0\n255 -50 0 248 47 0\n256 -53 0 248 50 0\n257 -58 0 248 59 0\n258 -59 0 248 64 0\n259 -63 0 248 81 0\n260 -44 0 257 239 116 0\n261 -20 0 259 119 0\n262 -17 0 259 239 115 0\n263 -69 0 260 261 254 258 239 241 262 236 247 252 259 211 143 16 120 179 227 196 158 244 162 154 163 0\n264 -77 0 263 155 0\n265 81 0 264 211 163 0\n266 -83 0 264 164 0\n267 79 0 265 162 0\n268 76 0 266 170 168 0\n269 72 0 267 158 0\n270 73 0 268 152 0\n271 74 0 268 153 0\n272 65 0 270 148 0\n273 67 0 271 150 0\n274 48 0 272 241 247 253 137 0\n275 51 0 273 256 255 139 0\n276 -2 0 274 28 0\n277 -38 0 274 31 0\n278 -10 0 275 34 0\n279 -55 0 275 51 0\n280 -9 0 275 248 85 0\n281 -14 0 276 249 250 251 241 86 0\n282 -16 0 280 278 279 102 0\n283 0 282 281 262 269 277 146 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record017.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record017.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record017.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record017.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record017 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record017.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record017.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record017.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record017.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record017 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record017_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record017_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record017_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record017_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record017_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record017_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record017_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record017 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record017_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record017_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record017_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00065.record017

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00065.record018
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "b8aaa36a66399563392e2b85e0fae1aa4d9994e5554cd4b4ad1743d98ce394d5334e8b62ccb8ad2b26c5b0ee4751cc789d2729c670dc8f13d1cb0aa22a91a458564382e07ac1a84a9465151550d0b41da0e4330e2328d1314d0b22c2b06d0711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "49b69a4924db4d2492492492492492492449249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record018 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record018 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record018.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record018.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record018.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 37), (facetIndex 58), (facetIndex 59), (facetIndex 63)]))
 (.leaf ([(facetIndex 38), (facetIndex 56), (facetIndex 57), (facetIndex 68), (facetIndex 79)])))
 (.branch 3
 (.leaf ([(facetIndex 39), (facetIndex 49), (facetIndex 52), (facetIndex 67), (facetIndex 78)]))
 (.leaf ([(facetIndex 36), (facetIndex 48), (facetIndex 60), (facetIndex 61)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 69), (facetIndex 70), (facetIndex 74)]))
 (.leaf ([(facetIndex 35), (facetIndex 45), (facetIndex 46), (facetIndex 47), (facetIndex 50), (facetIndex 51)])))
 (.branch 7
 (.leaf ([(facetIndex 42), (facetIndex 43), (facetIndex 44), (facetIndex 53), (facetIndex 54), (facetIndex 55)]))
 (.branch 8
 (.leaf ([(facetIndex 40), (facetIndex 41)]))
 (.leaf ([(facetIndex 71), (facetIndex 72)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "120004088441200000330011666255235556667721035z23;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 9
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 2
 (.branch 1
 (.leaf ([(facetIndex 64), (facetIndex 65)]))
 (.leaf ([(facetIndex 62), (facetIndex 66)])))
 (.branch 3
 (.leaf ([(facetIndex 75), (facetIndex 76)]))
 (.leaf ([(facetIndex 73), (facetIndex 77)]))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨2, sparse_nat% "e8c00101z1f;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 4
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped2_0000 : List Nat := [0]
def grouped2_0001 : List Nat := [0, 1]
def grouped2_0002 : List Nat := [0, 1, 2, 3]
def grouped2_0004 : List Nat := [1]
def grouped2_0005 : List Nat := [2]
def grouped2_0006 : List Nat := [2, 3]
def grouped2_0007 : List Nat := [3]
def grouped2_0008 : List Nat := [4]
def grouped2_0009 : List Nat := [4, 5]
def grouped2_0010 : List Nat := [4, 5, 6, 7, 8]
def grouped2_0011 : List Nat := [5]
def grouped2_0012 : List Nat := [6]
def grouped2_0013 : List Nat := [6, 7, 8]
def grouped2_0014 : List Nat := [7]
def grouped2_0015 : List Nat := [7, 8]
def grouped2_0016 : List Nat := [8]
def grouped3_0017 : List Nat := [0]
def grouped3_0018 : List Nat := [0, 1]
def grouped3_0020 : List Nat := [1]
def grouped3_0021 : List Nat := [2]
def grouped3_0022 : List Nat := [2, 3]
def grouped3_0023 : List Nat := [3]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record018 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record018_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00065.record018" "{\"atoms\":[{\"tag\":\"facet\",\"index\":3},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group\",\"kind\":2,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0015\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0015\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0018\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0022\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"groupKind3\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00065.record018" 79

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00065.record018" "{\"ridges\":[[15,131],[19,69],[21,25],[28,70],[30,26],[40,37],[41,37],[41,515],[42,131],[43,67],[46,67],[48,265],[51,131],[51,137],[51,138],[51,266],[55,82],[56,67],[58,25],[60,37],[60,137],[61,37],[62,204],[64,37],[64,228],[65,37],[65,612],[66,25],[66,137],[66,216],[69,26],[71,138],[73,204],[74,82],[77,26],[77,82],[77,138],[77,216]],\"owners\":[[19,69,[3,35,38,42,43,44,62,64,65],[59,63]],[28,70,[3,35,38,42,43,44,73,75,76],[70,74]],[48,265,[18,21],[8,51,61]],[51,266,[27,30,72],[8,48]],[41,515,[14,15,52,55],[12,44,49]],[62,204,[73],[]],[73,204,[62],[]],[64,228,[75],[]],[65,612,[76],[]],[66,216,[77],[]],[77,216,[66],[]]],\"edges\":[[20,[3,19,28,35,38,42,43,44,59,62,63,64,65,70,73,74,75,76]]],\"groupings\":[2,3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00065.record018" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00065.record018\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-11,-10],[-12,-1],[-13,-12],[-16,-2],[-16,-12],[-17,-12],[-18,-12],[-18,-15],[-19,-11],[-19,-15],[-20,-11],[-20,-16],[-20,-18],[-21,-11],[-22,-10],[-22,-14],[-22,-15],[-22,-19],[-22,-20],[-22,-21],[-23,-11],[-23,-22],[-24,-11],[-24,-22],[-25,-16],[-26,-20],[-27,-20],[-28,-20],[-31,-4],[-31,-11],[-33,-19],[-33,-31],[-34,-14],[-34,-31],[-35,-11],[-35,-33],[-35,-34],[-37,-13],[-37,-29],[-37,-30],[-37,-33],[-38,-13],[-38,-15],[-38,-29],[-38,-30],[-39,-10],[-39,-20],[-39,-21],[-39,-23],[-39,-26],[-39,-32],[-39,-35],[-40,-37],[-40,-38],[-41,-7],[-41,-19],[-42,-35],[-42,-39],[-43,-19],[-43,-35],[-43,-41],[-44,-11],[-44,-14],[-44,-22],[-44,-34],[-44,-41],[-45,-39],[-45,-44],[-46,-12],[-46,-17],[-46,-27],[-46,-36],[-50,-37],[-50,-38],[-14,-33,-38],[-15,-34,-37],[-17,-20,-29],[-5,1,10,13,16,17,18,35,37,38],[-8,1,10,13,16,17,18,45,47,48],[-6,-31,-39],[-9,-41,-49],[-3,-16,-24],[-24,-33,-39],[-24,-43,-49],[-22,4,6],[-24,7,9,44],[-28,-46,-49],[-15,2,3,25,28],[-35,45],[-45,35],[-37,47],[-38,48],[-39,49],[-49,39],[-51,12,31,32,36],[-52,13,29,30,40,50],[-53,11,22,33,34],[-54,41,42,46],[-55,10,19,20,21,23,24],[-56,16,17,18,26,27,28],[-57,14,15],[-58,43,44],[-44,58],[-59,51],[-59,52],[-60,53],[-61,59,60],[-62,59],[-62,60],[-63,54,55],[-64,54],[-64,55],[-65,57,58],[-66,57],[-66,58],[-68,56],[-67,65],[-68,66],[-69,63],[-69,64,68],[-70,64],[-69,67],[-70,68],[-71,61],[-71,62,70],[-71,69],[71],[-72,37,38],[-73,35,39],[-35,73],[-39,73],[-47,74],[-48,74],[-75,45,49],[-45,75],[-49,75],[-76,72,73],[-73,76],[-77,75],[-74,-75,77],[-78,76,77],[-76,-77,79],[78],[-79],[1,5,8,10,13,16,17,18,32,35,36,37,38,42,45,46,47,48]],\"atoms\":[{\"tag\":\"facet\",\"index\":3},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group\",\"index\":8,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":36,\"b\":35},{\"tag\":\"incompatible\",\"a\":37,\"b\":3},{\"tag\":\"incompatible\",\"a\":38,\"b\":37},{\"tag\":\"incompatible\",\"a\":42,\"b\":14},{\"tag\":\"incompatible\",\"a\":42,\"b\":37},{\"tag\":\"incompatible\",\"a\":43,\"b\":37},{\"tag\":\"incompatible\",\"a\":44,\"b\":37},{\"tag\":\"incompatible\",\"a\":44,\"b\":41},{\"tag\":\"incompatible\",\"a\":45,\"b\":36},{\"tag\":\"incompatible\",\"a\":45,\"b\":41},{\"tag\":\"incompatible\",\"a\":46,\"b\":36},{\"tag\":\"incompatible\",\"a\":46,\"b\":42},{\"tag\":\"incompatible\",\"a\":46,\"b\":44},{\"tag\":\"incompatible\",\"a\":47,\"b\":36},{\"tag\":\"incompatible\",\"a\":48,\"b\":35},{\"tag\":\"incompatible\",\"a\":48,\"b\":40},{\"tag\":\"incompatible\",\"a\":48,\"b\":41},{\"tag\":\"incompatible\",\"a\":48,\"b\":45},{\"tag\":\"incompatible\",\"a\":48,\"b\":46},{\"tag\":\"incompatible\",\"a\":48,\"b\":47},{\"tag\":\"incompatible\",\"a\":50,\"b\":36},{\"tag\":\"incompatible\",\"a\":50,\"b\":48},{\"tag\":\"incompatible\",\"a\":51,\"b\":36},{\"tag\":\"incompatible\",\"a\":51,\"b\":48},{\"tag\":\"incompatible\",\"a\":52,\"b\":42},{\"tag\":\"incompatible\",\"a\":53,\"b\":46},{\"tag\":\"incompatible\",\"a\":54,\"b\":46},{\"tag\":\"incompatible\",\"a\":55,\"b\":46},{\"tag\":\"incompatible\",\"a\":58,\"b\":18},{\"tag\":\"incompatible\",\"a\":58,\"b\":36},{\"tag\":\"incompatible\",\"a\":60,\"b\":45},{\"tag\":\"incompatible\",\"a\":60,\"b\":58},{\"tag\":\"incompatible\",\"a\":61,\"b\":40},{\"tag\":\"incompatible\",\"a\":61,\"b\":58},{\"tag\":\"incompatible\",\"a\":62,\"b\":36},{\"tag\":\"incompatible\",\"a\":62,\"b\":60},{\"tag\":\"incompatible\",\"a\":62,\"b\":61},{\"tag\":\"incompatible\",\"a\":64,\"b\":38},{\"tag\":\"incompatible\",\"a\":64,\"b\":56},{\"tag\":\"incompatible\",\"a\":64,\"b\":57},{\"tag\":\"incompatible\",\"a\":64,\"b\":60},{\"tag\":\"incompatible\",\"a\":65,\"b\":38},{\"tag\":\"incompatible\",\"a\":65,\"b\":41},{\"tag\":\"incompatible\",\"a\":65,\"b\":56},{\"tag\":\"incompatible\",\"a\":65,\"b\":57},{\"tag\":\"incompatible\",\"a\":66,\"b\":35},{\"tag\":\"incompatible\",\"a\":66,\"b\":46},{\"tag\":\"incompatible\",\"a\":66,\"b\":47},{\"tag\":\"incompatible\",\"a\":66,\"b\":50},{\"tag\":\"incompatible\",\"a\":66,\"b\":53},{\"tag\":\"incompatible\",\"a\":66,\"b\":59},{\"tag\":\"incompatible\",\"a\":66,\"b\":62},{\"tag\":\"incompatible\",\"a\":68,\"b\":64},{\"tag\":\"incompatible\",\"a\":68,\"b\":65},{\"tag\":\"incompatible\",\"a\":69,\"b\":27},{\"tag\":\"incompatible\",\"a\":69,\"b\":45},{\"tag\":\"incompatible\",\"a\":70,\"b\":62},{\"tag\":\"incompatible\",\"a\":70,\"b\":66},{\"tag\":\"incompatible\",\"a\":71,\"b\":45},{\"tag\":\"incompatible\",\"a\":71,\"b\":62},{\"tag\":\"incompatible\",\"a\":71,\"b\":69},{\"tag\":\"incompatible\",\"a\":72,\"b\":36},{\"tag\":\"incompatible\",\"a\":72,\"b\":40},{\"tag\":\"incompatible\",\"a\":72,\"b\":48},{\"tag\":\"incompatible\",\"a\":72,\"b\":61},{\"tag\":\"incompatible\",\"a\":72,\"b\":69},{\"tag\":\"incompatible\",\"a\":73,\"b\":66},{\"tag\":\"incompatible\",\"a\":73,\"b\":72},{\"tag\":\"incompatible\",\"a\":74,\"b\":37},{\"tag\":\"incompatible\",\"a\":74,\"b\":43},{\"tag\":\"incompatible\",\"a\":74,\"b\":54},{\"tag\":\"incompatible\",\"a\":74,\"b\":63},{\"tag\":\"incompatible\",\"a\":79,\"b\":64},{\"tag\":\"incompatible\",\"a\":79,\"b\":65},{\"tag\":\"three\",\"ridge\":37,\"vertices\":[40,60,65]},{\"tag\":\"three\",\"ridge\":37,\"vertices\":[41,61,64]},{\"tag\":\"three\",\"ridge\":67,\"vertices\":[43,46,56]},{\"tag\":\"mate\",\"ridge\":69,\"a\":19,\"owners\":[3,35,38,42,43,44,62,64,65]},{\"tag\":\"mate\",\"ridge\":70,\"a\":28,\"owners\":[3,35,38,42,43,44,73,75,76]},{\"tag\":\"three\",\"ridge\":25,\"vertices\":[21,58,66]},{\"tag\":\"three\",\"ridge\":26,\"vertices\":[30,69,77]},{\"tag\":\"three\",\"ridge\":131,\"vertices\":[15,42,51]},{\"tag\":\"three\",\"ridge\":137,\"vertices\":[51,60,66]},{\"tag\":\"three\",\"ridge\":138,\"vertices\":[51,71,77]},{\"tag\":\"mate\",\"ridge\":265,\"a\":48,\"owners\":[18,21]},{\"tag\":\"mate\",\"ridge\":266,\"a\":51,\"owners\":[27,30,72]},{\"tag\":\"three\",\"ridge\":82,\"vertices\":[55,74,77]},{\"tag\":\"mate\",\"ridge\":515,\"a\":41,\"owners\":[14,15,52,55]},{\"tag\":\"mate\",\"ridge\":204,\"a\":62,\"owners\":[73]},{\"tag\":\"mate\",\"ridge\":204,\"a\":73,\"owners\":[62]},{\"tag\":\"mate\",\"ridge\":228,\"a\":64,\"owners\":[75]},{\"tag\":\"mate\",\"ridge\":612,\"a\":65,\"owners\":[76]},{\"tag\":\"mate\",\"ridge\":216,\"a\":66,\"owners\":[77]},{\"tag\":\"mate\",\"ridge\":216,\"a\":77,\"owners\":[66]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[37,58,59,63],\"full_literals\":[-51,12,31,32,36]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[38,56,57,68,79],\"full_literals\":[-52,13,29,30,40,50]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[36,48,60,61],\"full_literals\":[-53,11,22,33,34]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[69,70,74],\"full_literals\":[-54,41,42,46]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[35,45,46,47,50,51],\"full_literals\":[-55,10,19,20,21,23,24]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[42,43,44,53,54,55],\"full_literals\":[-56,16,17,18,26,27,28]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[40,41],\"full_literals\":[-57,14,15]},{\"tag\":\"group_or\",\"kind\":2,\"index\":8,\"members\":[71,72],\"full_literals\":[-58,43,44]},{\"tag\":\"group_take\",\"kind\":2,\"index\":8,\"member\":72,\"full_literals\":[-44,58]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-59,51,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-59,false,52],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-60,false,53],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-61,59,60],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-62,59,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-62,false,60],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-63,54,55],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-64,54,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-64,false,55],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0014\",\"right_name\":\"grouped2_0016\",\"joined_name\":\"grouped2_0015\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-65,57,58],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0014\",\"right_name\":\"grouped2_0016\",\"joined_name\":\"grouped2_0015\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-66,57,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0014\",\"right_name\":\"grouped2_0016\",\"joined_name\":\"grouped2_0015\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-66,false,58],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0013\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-68,56,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0013\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-67,false,65],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0013\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-68,false,66],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":0,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-69,63,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-69,64,68],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":1,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-70,64,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-69,false,67],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-70,false,68],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":2,\"b\":5,\"direction\":\"backward\",\"full_literals\":[-71,61,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-71,62,70],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-71,false,69],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":3,\"index\":0,\"members\":[64,65],\"full_literals\":[-72,37,38]},{\"tag\":\"group_or\",\"kind\":3,\"index\":1,\"members\":[62,66],\"full_literals\":[-73,35,39]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":62,\"full_literals\":[-35,73]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":66,\"full_literals\":[-39,73]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":75,\"full_literals\":[-47,74]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":76,\"full_literals\":[-48,74]},{\"tag\":\"group_or\",\"kind\":3,\"index\":3,\"members\":[73,77],\"full_literals\":[-75,45,49]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":73,\"full_literals\":[-45,75]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":77,\"full_literals\":[-49,75]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0018\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-76,72,73],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0018\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-73,76],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"grouped3_0022\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-77,false,75],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"grouped3_0022\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-74,-75,77],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"groupKind3\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-78,76,77],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-76,-77,79],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_lower\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":20,\"owners\":[3,19,28,35,38,42,43,44,59,62,63,64,65,70,73,74,75,76]}]}"
  "p cnf 79 145\n-11 -10 0\n-12 -1 0\n-13 -12 0\n-16 -2 0\n-16 -12 0\n-17 -12 0\n-18 -12 0\n-18 -15 0\n-19 -11 0\n-19 -15 0\n-20 -11 0\n-20 -16 0\n-20 -18 0\n-21 -11 0\n-22 -10 0\n-22 -14 0\n-22 -15 0\n-22 -19 0\n-22 -20 0\n-22 -21 0\n-23 -11 0\n-23 -22 0\n-24 -11 0\n-24 -22 0\n-25 -16 0\n-26 -20 0\n-27 -20 0\n-28 -20 0\n-31 -4 0\n-31 -11 0\n-33 -19 0\n-33 -31 0\n-34 -14 0\n-34 -31 0\n-35 -11 0\n-35 -33 0\n-35 -34 0\n-37 -13 0\n-37 -29 0\n-37 -30 0\n-37 -33 0\n-38 -13 0\n-38 -15 0\n-38 -29 0\n-38 -30 0\n-39 -10 0\n-39 -20 0\n-39 -21 0\n-39 -23 0\n-39 -26 0\n-39 -32 0\n-39 -35 0\n-40 -37 0\n-40 -38 0\n-41 -7 0\n-41 -19 0\n-42 -35 0\n-42 -39 0\n-43 -19 0\n-43 -35 0\n-43 -41 0\n-44 -11 0\n-44 -14 0\n-44 -22 0\n-44 -34 0\n-44 -41 0\n-45 -39 0\n-45 -44 0\n-46 -12 0\n-46 -17 0\n-46 -27 0\n-46 -36 0\n-50 -37 0\n-50 -38 0\n-14 -33 -38 0\n-15 -34 -37 0\n-17 -20 -29 0\n-5 1 10 13 16 17 18 35 37 38 0\n-8 1 10 13 16 17 18 45 47 48 0\n-6 -31 -39 0\n-9 -41 -49 0\n-3 -16 -24 0\n-24 -33 -39 0\n-24 -43 -49 0\n-22 4 6 0\n-24 7 9 44 0\n-28 -46 -49 0\n-15 2 3 25 28 0\n-35 45 0\n-45 35 0\n-37 47 0\n-38 48 0\n-39 49 0\n-49 39 0\n-51 12 31 32 36 0\n-52 13 29 30 40 50 0\n-53 11 22 33 34 0\n-54 41 42 46 0\n-55 10 19 20 21 23 24 0\n-56 16 17 18 26 27 28 0\n-57 14 15 0\n-58 43 44 0\n-44 58 0\n-59 51 0\n-59 52 0\n-60 53 0\n-61 59 60 0\n-62 59 0\n-62 60 0\n-63 54 55 0\n-64 54 0\n-64 55 0\n-65 57 58 0\n-66 57 0\n-66 58 0\n-68 56 0\n-67 65 0\n-68 66 0\n-69 63 0\n-69 64 68 0\n-70 64 0\n-69 67 0\n-70 68 0\n-71 61 0\n-71 62 70 0\n-71 69 0\n71 0\n-72 37 38 0\n-73 35 39 0\n-35 73 0\n-39 73 0\n-47 74 0\n-48 74 0\n-75 45 49 0\n-45 75 0\n-49 75 0\n-76 72 73 0\n-73 76 0\n-77 75 0\n-74 -75 77 0\n-78 76 77 0\n-76 -77 79 0\n78 0\n-79 0\n1 5 8 10 13 16 17 18 32 35 36 37 38 42 45 46 47 48 0\n"
  "146 61 0 127 124 0\n147 69 0 127 126 0\n148 63 0 147 119 0\n149 67 0 147 122 0\n150 65 0 149 117 0\n151 -77 0 144 139 142 138 130 131 90 94 134 0\n152 76 0 151 143 141 0\n153 -41 -58 0 61 66 102 0\n154 -42 -73 0 57 58 129 0\n155 39 -58 -75 0 151 152 140 132 91 133 92 128 137 94 129 134 60 68 102 0\n156 -43 -49 23 21 20 10 -55 0 59 84 99 0\n157 -70 -75 0 151 152 140 132 91 133 92 128 137 154 121 123 111 112 116 118 114 115 153 98 70 71 155 46 47 48 49 50 93 87 156 102 63 101 8 10 100 99 4 25 82 88 0\n158 -33 41 -39 -75 0 151 152 127 148 51 49 48 47 46 157 125 108 104 140 132 91 133 92 128 137 154 31 32 83 99 110 98 69 72 95 0\n159 -31 33 -39 -53 0 29 30 34 80 97 85 0\n160 36 31 -39 -75 0 151 152 127 67 52 51 46 157 125 108 104 140 132 91 133 92 128 137 154 95 2 3 5 6 7 69 79 78 145 0\n161 -58 -39 -75 0 151 152 127 148 93 49 48 47 46 157 125 109 106 140 132 91 133 92 128 137 154 153 158 159 160 72 98 110 156 102 62 64 65 97 0\n162 -41 -55 44 -49 23 21 20 10 0 55 56 81 99 86 0\n163 -39 -75 0 151 152 127 147 157 125 109 106 140 132 91 133 92 128 137 154 46 47 48 49 93 161 103 115 118 120 111 112 162 158 98 159 72 160 0\n164 -75 0 151 152 127 150 140 132 133 91 92 128 137 157 125 109 106 163 129 155 35 36 37 113 97 16 17 101 0\n165 -45 0 164 135 0\n166 -49 0 164 136 0\n167 -35 0 165 89 0\n168 -39 0 166 93 0\n169 -73 0 168 167 129 0\n170 72 0 169 152 137 0\n171 -19 34 33 -53 0 9 18 97 0\n172 -20 33 34 -53 0 11 19 97 0\n173 -21 33 34 -53 0 14 20 97 0\n174 -30 0 170 40 45 128 0\n175 -40 0 170 53 54 128 0\n176 -50 0 170 73 74 128 0\n177 -13 0 170 38 42 128 0\n178 -33 -57 0 170 41 128 43 75 101 0\n179 -24 33 -53 34 0 23 24 97 0\n180 60 -20 0 146 127 175 174 177 176 28 27 26 13 12 109 107 125 105 123 96 116 77 100 0\n181 -34 -57 0 170 33 101 43 76 128 0\n182 -20 34 33 0 180 172 106 0\n183 -29 0 170 39 44 128 0\n184 -52 0 183 176 177 174 175 96 0\n185 -59 0 184 105 0\n186 60 0 185 146 107 0\n187 -62 0 185 108 0\n188 53 0 186 106 0\n189 70 0 187 127 125 0\n190 64 0 189 121 0\n191 68 0 189 123 0\n192 55 0 190 112 0\n193 66 0 191 118 0\n194 34 33 10 0 192 188 182 179 171 173 99 21 22 97 0\n195 57 0 193 114 0\n196 -34 0 195 181 0\n197 -33 0 195 178 0\n198 10 0 197 196 194 0\n199 -11 0 198 1 0\n200 -22 0 198 15 0\n201 0 199 200 196 188 197 97 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record018.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record018.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record018.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record018.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record018 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record018.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record018.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record018.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record018.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record018 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record018_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record018_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record018_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record018_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record018_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record018_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record018_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record018 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record018_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record018_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record018_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00065.record018
