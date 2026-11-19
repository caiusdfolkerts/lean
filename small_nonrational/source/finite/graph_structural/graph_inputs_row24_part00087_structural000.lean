module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow24Part00087Data
public import GraphInputsRow24Part00087Frames
public import GraphInputsRow24Part00087Leaves
public import GraphInputsRow24Part00087Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00087.record002
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00087.record002
def vertexColumn : Fields := ⟨10, hexnat% "b2aaa3aa5a8e87a55936a394e338ae8785e0fad1ac4f1b26a93a6598e47971695554d54d4b5a354d3361d1743db0ea338f1394e334cc73a2e4b52ccb8acab1ae1b16c3ba1d4731d2729e1715e0f43c8f13c1f2b152458360b951a24c92a4a5454352342d50e1344c530ce0b12c2b41c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "6db6d26da6d36d24db6d34934da6da49249249249a692492489249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨36, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨56, by decide⟩, ⟨59, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨65, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨77, by decide⟩, ⟨80, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [13907115675089895424, hexnat% "120000000000000000000", hexnat% "2000020012001080000000", hexnat% "1000000000000104000000", hexnat% "3802800940010000000", 116549977374720, 3661098842587136]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00087.record002_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00087.record002_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00087.record002_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00087.record002_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00087.record002_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00087.record002_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00087.record002_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00087.record002_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00087.record002_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00087.record002

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00087.record009
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00087.record009
def vertexColumn : Fields := ⟨10, hexnat% "ae2d4ad0f4ab29c8f0bcb4ab23c95a8eac6a98e6a5a5635a362d876c394e8b92e8785e0f8f1a65592e5c539695354b51d68d5352d2b61d2745d0f4e3a4d5334cb31cd4b4ae1b46c5ba1cc749ca719e1725c570de0f13c1f8683a51a0e4382e344b10e545314a54342d50c530cd0b0ac1b41c4709c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "1b6db6db6d36db6db4924d26d24d26d24db4da4924926924da492249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2, 3]
def candidates : List (Fin raw.n) := [⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fffff2fdecf7a7fff000000", hexnat% "d00000000000000000", 9008298766368768, 2378045738786488320, 4504149383184384]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fffffffdcdf72ffff000000", 9008298766368768, 144123984168878080, 2378045738786488320]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fffffbfdffff2cfff000000", 2305847407260205056, 1305670057984, 8796093022208, hexnat% "400000000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fffffbfffcff64fff000000", 8864812498944, 4504149383184384, 1236950581248, hexnat% "400020000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fffffffdccf720fff000000", 1030792151040, 144123984168878080, 13510798882111488, 2378045738786488320, 1099511627776]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨67, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨65, by decide⟩ c5 c2
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨68, by decide⟩ c6 c1
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨81, by decide⟩ c7 c0
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ffdff0fe7cfee9bfb000000", hexnat% "200000000006000000000", 13510798882111488, 1729382274090139648, 18691697672192, hexnat% "f00000000004000000"]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fffffbedfc7e0ccfd000000", 2308094809027379200, 18897889656832, 4503612512272384, hexnat% "100000e0000000000", hexnat% "400020000000000000"]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fffffbec7d7fbfeff000000", 1161928703861587968, hexnat% "400000000000000000", hexnat% "12000040000000000", 578712556412076032]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fffffbedfc7f04cfd000000", 2308094809027379200, 1855459426304, hexnat% "100000e0000000000", hexnat% "400020000200000000", 4503603922337792]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c12 c11
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ffdfffec4ffe08bef000000", hexnat% "200000000007000000000", 1873497462165995520, hexnat% "12100040000000000", 18691966107648, 10995116277760]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ffdfffec4ff618fff000000", 1873497444986126336, hexnat% "200000000007000000000", 28587302322176, 2378045738786488320, hexnat% "10000000000000000"]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fffff2fecd77e7af9000000", 74450135634935808, 1649300996096, 1297036709862572032, hexnat% "400020000000000000", hexnat% "900000000004000000"]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fffff4ec4f773fafb000000", 1873497462165995520, hexnat% "b00000000004000000", hexnat% "100000c0000000000", 2380293140553662464, 4294967296]
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ffdff5fdfffe3ffef000000", 2305847407260205056, hexnat% "200200000000000000000", 26388547502080, hexnat% "800000000000000000"]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .size 3
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .size 2
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c20 c19
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c20 c21
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c20 c22
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨81, by decide⟩ c20 c23
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c20 c19
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c20 c25
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c20 c26
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨81, by decide⟩ c20 c27
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ffdffffffdffbfeff000000", 9007199254740992, hexnat% "200000000000000000000", 4402341478400]
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c29 c28
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨61, by decide⟩ c30 c24
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ffdff9fdfd7fbfeff000000", hexnat% "400020000000000000", hexnat% "200200000000000000000", 4402341478400, 2308094809027379200]
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨71, by decide⟩ c32 c31
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ffdff1ecfdfffffff000000", hexnat% "12000000000000000", hexnat% "200200000000000000000", 1161928703861587968, hexnat% "c00000000000000000"]
  let c35 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fffff3eced7e3fbef000000", 2380152403065307136, hexnat% "c00000000000000000", 26405727371264, 1161928703861587968, hexnat% "10000040000000000"]
  let c36 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c35 c34
  let c37 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c36 c33
  let c38 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c37 c18
  let c39 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fffff0ec4d763fae9000000", 2380293140553662464, 1161928721075011584, 26388547502080, hexnat% "10a00000000000000", hexnat% "f00000000004000000", 4402341478400]
  let c40 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c39 c38
  let c41 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c40 c17
  let c42 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c41 c16
  let c43 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c42 c15
  let c44 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨52, by decide⟩ c43 c14
  let c45 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨67, by decide⟩ c44 c13
  let c46 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨65, by decide⟩ c45 c10
  let c47 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c46 c9
  let c48 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c47 c8
  c48
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00087.record009_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00087.record009_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00087.record009_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00087.record009_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00087.record009_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00087.record009_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00087.record009_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00087.record009_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00087.record009_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00087.record009
