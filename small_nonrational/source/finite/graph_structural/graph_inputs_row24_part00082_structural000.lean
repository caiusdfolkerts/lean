module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow24Part00082Data
public import GraphInputsRow24Part00082Frames
public import GraphInputsRow24Part00082Leaves
public import GraphInputsRow24Part00082Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00082.record000
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record000
def vertexColumn : Fields := ⟨10, hexnat% "2b4730dc2f0dab1a9635a36538ce4b86e4789e1783eac5c9aa4d92e6c5716a5a54d58d4b56354d3352d2b46d4749d1743db0e9334e33a2ccb8ad2b1ad1b26c5bc1e8791cc749c6785d1725c5743c8f13c2f07d4a0e94689836524c926439a1545316252543550e230cd0b12c2b06e0741c4709c17"⟩
def kindColumn : Fields := ⟨3, hexnat% "36db6da4db6da69a4924926936da69b69a4924924924924d2449249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨50, by decide⟩, ⟨54, by decide⟩, ⟨56, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨74, by decide⟩, ⟨76, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1250000f7ffb8000000", hexnat% "580000000000000000", hexnat% "4006001000000000000", hexnat% "1000020004000000000000", hexnat% "800140080000000000", hexnat% "810000000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1800145fd7318000000", hexnat% "4206000000020000000", hexnat% "5d0000000000000000", hexnat% "810000000000080000000", hexnat% "1000020000000800000000", 2765958938624]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "10007a00040bffb8000000", 268280837177344, hexnat% "810006140000000000000", hexnat% "50000000000000000", hexnat% "1800000000000000000", hexnat% "4000001000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "10001b0044fdbb10000000", 2491617902592, hexnat% "642000000000000000", hexnat% "1800100000000000000", hexnat% "810004000000088000000", hexnat% "4000001000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "5026005fdf330000000", hexnat% "6c0000000000000000", hexnat% "910000000000000000", hexnat% "810000140000088000000", hexnat% "1000000000000800000000", 2216203124736]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "50200010c8100000000", hexnat% "1010000004000010000000", 263882790666240, hexnat% "910000000000000000", hexnat% "6c2000004000000000", hexnat% "8000041400000a8000000", 3564822855680]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨65, by decide⟩ c6 c3
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c7 c2
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c8 c1
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c9 c0
  c10
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record000_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record000_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record000_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record000_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record000_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record000_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record000_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record000_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record000_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00082.record000

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00082.record001
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record001
def vertexColumn : Fields := ⟨10, hexnat% "2b4372b236ac671aa6a58d68d8b6538ce8b92e1b91e2785e0fab1366c5716a5a54d58d4b53362d4b46d4749d176c370ea3a4cd38ccb332e2b4ac6b46c9b16f07a1d8791d4731e2749ca719e1745c9715c3783d0f23c4f0bc1f5303c5283a52439a154531625254354344d0b41da0d4330e2324c3342c4b0ac1b"⟩
def kindColumn : Fields := ⟨3, hexnat% "36db6db6d36db6d36924924924924924924924d36926db69a69a489249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨30, by decide⟩, ⟨32, by decide⟩, ⟨34, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨45, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨77, by decide⟩, ⟨85, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7fc67dea30508000000", 1162210178838298624, 576465150618370048, hexnat% "38000000044000000", hexnat% "2020000000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7d87750a20400000000", 585472349873111040, hexnat% "78000000008000000", hexnat% "200080010100000000", hexnat% "2020000000000044000000", 4222124650659840]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨52, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "5ffe021010504000000", hexnat% "2000800060010000000", 1675339061381824512, 8584986923892736, 36028797018963968, hexnat% "2020000000200040000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "6cbfb21060010000000", hexnat% "1340000000000000000", 8584986923892736, hexnat% "2020000000210544000000", 342273571680157696]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4857ff810504000000", hexnat% "2000800060010000000", hexnat% "5900000000000000000", hexnat% "7a000000008000000", hexnat% "200000000000000000", hexnat% "2020000000200040000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "6c84001020000000000", hexnat% "1100440000000000000", 1954562238278795264, hexnat% "7a000000008000000", 8584986789675008, hexnat% "200080010100000000", hexnat% "2020000000240454000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨67, by decide⟩ c7 c4
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨62, by decide⟩ c8 c3
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨70, by decide⟩ c9 c2
  c10
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record001_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record001_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record001_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record001_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record001_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record001_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record001_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record001_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record001_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00082.record001

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00082.record006
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record006
def vertexColumn : Fields := ⟨10, hexnat% "5b2ca5aa9a568daa9966a59362d94e4b86e8791e785d16c6c95a699564d9a9565a55352d70d5352d1b61db0ea358e9354cd34ccb3a2e4b52ccb4ac6b86d1b26c5ba1d4789d2729c6785d1725c3743c4f0bd1c38a0e0796138549465254560d4341da0cc328c6324e0b12c1b81c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "1b6db6db6db4936d34da69a49a49269a492692493492492491249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨50, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨62, by decide⟩, ⟨64, by decide⟩, ⟨67, by decide⟩, ⟨69, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [60187176142372864, hexnat% "c000100000008000000", hexnat% "2000020040100000000", 6629298651489370112, hexnat% "280000200000000000", hexnat% "10000000400000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "629082077456c000000", 6052837899185946624, hexnat% "8000100000082000000", 180657061888, 60095457283538944]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "c0001d5f2e8ac000000", hexnat% "2200020040000000000", 30366760960, hexnat% "81c00000000000000", 1100585369600, hexnat% "14000000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2290c61b40fb6000000", 5764607523168452608, 41658433992130560, hexnat% "c000100000000000000", 1650341183488, 72842645340160]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "a211520e66ffe000000", hexnat% "4000000010000000000", 5188146770730811392, hexnat% "80004000000000000", 58846412074385408]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4085d20e3c56e000000", hexnat% "8000010000080000000", hexnat% "2210000000000000000", 180657061888, 37176687158362112, 18295873486192640]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "c000130a3affe000000", 92633854640128, 55450570411999232, 6629298651489370112, hexnat% "2210000000000000000", hexnat% "80000000000000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2214ca4f743a6000000", hexnat% "81000000008000000", hexnat% "c000100000000000000", 18014570308173824, 4785624359895040, 18522046464]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2210020a501a2000000", hexnat% "c000100000008000000", hexnat% "81c00000000000000", 18014578898108416, 90984654307328, 41939771529887744, 4611686036949434368]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c9 c6
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c10 c5
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c11 c4
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c12 c3
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c13 c2
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c14 c1
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c15 c0
  c16
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record006_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record006_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record006_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record006_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record006_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record006_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record006_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record006_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record006_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00082.record006
