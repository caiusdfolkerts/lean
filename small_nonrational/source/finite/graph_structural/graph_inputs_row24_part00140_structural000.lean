module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow24Part00140Data
public import GraphInputsRow24Part00140Frames
public import GraphInputsRow24Part00140Leaves
public import GraphInputsRow24Part00140Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00140.record002
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00140.record002
def vertexColumn : Fields := ⟨10, hexnat% "bcd4a725cb4a9a96ac6a9a66a3a4e8ba959562d8769394e2b86e8791e2783ed46715c7499a569c6699666394e4b9955552d4759354d2b46d8751d2743dd0e6358f13a4d9394d538cd332cc73c2e8b62e4b52e2b4acab1ae1b46c9b0ee4751cc729e1745c5783d0f13c1f198960d88e0b865254352342d90d4318e1344c930ce0b42c8b0ac8711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "db6db6db6db49b49b49b6db6db6db49b49b492492492492492492492492492489249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨94, by decide⟩, ⟨95, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "cc4000000200000000", hexnat% "cc4000000000000000000000", hexnat% "8000008000004404000000", 4035333121476919296, 1017736255766528, 575334859912773632]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00140.record002_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00140.record002_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00140.record002_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00140.record002_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00140.record002_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00140.record002_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00140.record002_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00140.record002_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00140.record002_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00140.record002

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00140.record012
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00140.record012
def vertexColumn : Fields := ⟨10, hexnat% "d326c5b25c570dc2f07cd2a6a5aa5a568ba1eb4699966959562d876c3a8e63a4e53a2e4b8ae1ba1e4789e1783ed26695a659564b91e74599565955552d475c368d6364d5362d4b4ad1b61d4749d1743d2cf0ba2d8b8ad2b2ae1b46f07a1d8789d2729e1745e0f43c8f0bc1f1e0742683a25836264392543524c3382d0b22c2b06e0741c8709c17"⟩
def kindColumn : Fields := ⟨3, hexnat% "6db6da6db6936db49b6db6db69a6db6936db49b6db6db69a492492492492492489249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨46, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨72, by decide⟩, ⟨74, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩, ⟨100, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "10000001020400100000000000", hexnat% "204000000000000000000000", hexnat% "4000000480001c00000", 34326183936, 8761733283840, hexnat% "408000040800000000000000"]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00140.record012_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00140.record012_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00140.record012_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00140.record012_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00140.record012_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00140.record012_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00140.record012_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00140.record012_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00140.record012_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00140.record012

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00140.record018
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00140.record018
def vertexColumn : Fields := ⟨10, hexnat% "5e2e49d0f49b0ec1f1723c9aa5a8ea5693a1ea563591e17ae1cc6713c5a99a4e94e479b16a5994e5954d58d4b51d64d3362d2b46d4745d0f5a338e5334d332cc7362ccb4acab1ad1b16c3b91cc785d1725c5743c4f07e703a254330ca318562384e8c5314a4a98548d44d0b22c8705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "1b4da6db69b6934d269a4db6d34db4d36db6da6d249a6da492491249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨32, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨40, by decide⟩, ⟨49, by decide⟩, ⟨51, by decide⟩, ⟨55, by decide⟩, ⟨57, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨66, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨71, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨78, by decide⟩, ⟨84, by decide⟩, ⟨87, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "42958208013d1fe00000", hexnat% "200080000000000000", hexnat% "8004000000000000000000", hexnat% "1000000002000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "691020800381be00000", 1103873703936, hexnat% "40002000400000000", hexnat% "208000000000000000", hexnat% "1040000000000000000000", hexnat% "8000000080000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "904415028a003d19e00000", 100663296, hexnat% "208000010000000000", hexnat% "2800000000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8006910288003d1fe00000", hexnat% "40002000000000000", hexnat% "208000010000000000", hexnat% "1040000000000000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "904415028a013c19c00000", hexnat% "208000000000000000", hexnat% "2000000000002000000", 4364173312, hexnat% "800000000000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "904411028a003019c00000", hexnat% "208000010000000000", hexnat% "2000000000002000000", 4364173312, hexnat% "40000000c00000000", hexnat% "800000000000000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨78, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨23, by decide⟩ c7 c4
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c8 c3
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "104695820a003d11e00000", hexnat% "8000000080000000000000", 234881024, hexnat% "200000010000000000"]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "104095820a003c11c00000", hexnat% "6000000000000000000", hexnat% "8000000080000000000000", hexnat% "200000010000000000", 236978176, 4294967296]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨71, by decide⟩ c11 c10
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "904015028a001411400000", hexnat% "208000010000000000", hexnat% "6800000000000000000", 176102047744, 236978176]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "a58200013d00e00000", hexnat% "1040000008000000000000", 251658240, hexnat% "6000000000000000000", hexnat% "100000000010000000", hexnat% "8000000082000000000000"]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "900035828a003400400000", hexnat% "40000000010800000000", hexnat% "4000000000009000000", 4372561920, hexnat% "2800000000010000000", 33554432]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "295820a013d17e00000", hexnat% "200080000000000000", hexnat% "4000000000008000000", hexnat% "1040000000000000000000", hexnat% "8000000000000000000000"]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "858202013d14e00000", hexnat% "300080000000000000", hexnat% "2000000000003000000", hexnat% "1040000008000000000000", hexnat% "4000000000008000000", hexnat% "8000000000000000000000"]
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c17 c16
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2b1828a001113600000", hexnat% "4000000000008000000", 75497472, hexnat% "40000002c00000000", hexnat% "9000000000000000000000", hexnat% "40000000010000000000"]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "904411828a00151f600000", hexnat% "200000010000000000", hexnat% "2800000000000000000", 171807080448, hexnat% "40000000000000000"]
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "681828a00111f600000", hexnat% "300000000000000000", hexnat% "9000000000000000000000", 188986949632, hexnat% "40000000000000000", hexnat% "40000000010000000000"]
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c21 c20
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "58202003d18400000", hexnat% "300080000000000000", hexnat% "6800000000001000000", hexnat% "9000000000000000000000", 111149056, hexnat% "40000000010000000000", 2251799813685248]
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c23 c22
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c24 c19
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c25 c18
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c26 c15
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c27 c14
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨64, by decide⟩ c28 c13
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c29 c12
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c30 c9
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨22, by decide⟩ c31 c2
  c32
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00140.record018_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00140.record018_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00140.record018_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00140.record018_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00140.record018_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00140.record018_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00140.record018_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00140.record018_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00140.record018_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00140.record018
