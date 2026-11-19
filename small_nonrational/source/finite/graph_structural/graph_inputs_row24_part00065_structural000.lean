module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow24Part00065Data
public import GraphInputsRow24Part00065Frames
public import GraphInputsRow24Part00065Leaves
public import GraphInputsRow24Part00065Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

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
