module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow24Part00092Data
public import GraphInputsRow24Part00092Frames
public import GraphInputsRow24Part00092Leaves
public import GraphInputsRow24Part00092Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00092.record006
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record006
def vertexColumn : Fields := ⟨10, hexnat% "5d29c970dc8f0bc1f16aa6a5a36a3a2e87a59a96958d68d8b61da8e938ce8b8ae1ba1e2785e0f9715a699364b91e565a5555355352d475a34cd2b46d8749d1743d58e9334cb31ce8b52ccb4acab1ae1b26c5b0ee8761cc729c6785c9715c3783c8f13c2f07e98a528aa1946498991643951525254550d54348c8b12c2b41c8711c27"⟩
def kindColumn : Fields := ⟨3, hexnat% "69b6db4db6d26db69b6db6db6924924926db6924db692493492492692692649249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨82, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨95, by decide⟩, ⟨102, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "81000005f03020ef73000000", hexnat% "20000080008020000000000", hexnat% "420000401000000000", 30786325577728, hexnat% "300040000000000000", hexnat% "40000400000000000004000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "81000005f03008ef73000000", hexnat% "20000080008020000000000", hexnat% "420000401000000000", 57174604644352, hexnat% "300040000000000000", hexnat% "40000400000000000004000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "400004000100783e6f37000000", hexnat% "200000c1000000000000000", 16140901064495857664, hexnat% "420000401000000000", hexnat% "300000008000000000", hexnat% "810000000000000040000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "400004000040783e6f37000000", hexnat% "200000c1000000000000000", hexnat% "1a000000000000000", hexnat% "420000401000000000", hexnat% "300000008000000000", hexnat% "810000000000000040000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "400004007ff070008177000000", hexnat% "810000000000006000000000", 70437463654400, hexnat% "20000000008000800000000", 25769803776, 68169720922112]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8100007800487ee177000000", hexnat% "40000400000030000000000000", hexnat% "20000001000000000", hexnat% "20000040000000800000000", 25769803776, hexnat% "1f000000000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "400204003df0787ee337000000", hexnat% "800000400000000000000000", 121332826112, hexnat% "10000020000000000000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "400004003df07002c137000000", hexnat% "420000401000000000", hexnat% "20000000008000800000000", hexnat% "810000000000002040000000", 65970697666560, 25769803776]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c7 c6
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "81000007f06000ff77000000", hexnat% "40000400000010000000000000", hexnat% "20000080008020000000000", 65970697666560, hexnat% "400000400000000000", hexnat% "300000000000000000"]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "400004003df07000a177000000", hexnat% "420000401000000000", hexnat% "810000000000004000000000", hexnat% "20000000008000800000000", 25769803776, 68169720922112]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40810400000070008073000000", hexnat% "1f000000000000000", hexnat% "20000040008000900000000", 68169720922112, hexnat% "420000401000000000", hexnat% "380000006000000000", 25836912640]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨52, by decide⟩ c11 c10
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c12 c9
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c13 c8
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c14 c5
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c15 c4
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨24, by decide⟩ c16 c3
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c17 c2
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c18 c1
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c19 c0
  c20
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record006_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record006_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record006_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record006_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record006_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record006_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record006_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record006_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record006_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00092.record006

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00092.record016
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record016
def vertexColumn : Fields := ⟨10, hexnat% "a72aaa6a5a59a96558b61da8e538ae1ba1e2785e3c6a93a699964d959695655552d475a354d1b61d2745da8d63c4e9394cb31ce8b92d4b8acab86c9b16e8751d2729c6785c9715c3783d0f23c4f07cac5486a4582ea4551a24a91a4a5454952342d50c6384d1314e0b12c2b41c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "1b6db4db6936da49b6924d34d36924d24924d3492492492449249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2, 3]
def candidates : List (Fin raw.n) := [⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ffbfb97dc7ffd3f8000000", hexnat% "40000010002400000000", 11259033428164608, hexnat% "68200000000000000", hexnat% "400000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3f7ffb85d95ff34f8000000", hexnat% "442200000000000000", hexnat% "800010020008200000000", 18014673387388928, 2814788421812224, hexnat% "28000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ffdfb9ffbfbfeff8000000", hexnat% "60000000000000000", hexnat% "400000000000000000", hexnat% "20000000001000000000", 18084767253659648]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .size 3
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .size 2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨70, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨77, by decide⟩ c4 c5
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ffdebdfffffffff8000000", hexnat% "20000000000000000", hexnat% "20000000000000000000", hexnat% "1400000000000000000"]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨71, by decide⟩ c7 c6
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fffe39dfbf3ffff8000000", hexnat% "60000000000000000", 18225504742014976, hexnat% "1802000000000000000", hexnat% "400000000000000000"]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ff9e3fd7be2faf38000000", 18014742106865664, hexnat% "1800800100000000000", hexnat% "60000000000000000000", 211109453758464, hexnat% "402001000000000000"]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c11 c10
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c12 c2
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3f79fb875a4350010000000", hexnat% "820010800009200000000", hexnat% "40000011002420000000", 21042453532377088, hexnat% "68200000000000000", hexnat% "400000080008000000", 316753838080]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c14 c13
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c15 c1
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c16 c0
  c17
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record016_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record016_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record016_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record016_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record016_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record016_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record016_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record016_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092.record016_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00092.record016
