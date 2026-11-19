module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow24Part00103Data
public import GraphInputsRow24Part00103Frames
public import GraphInputsRow24Part00103Leaves
public import GraphInputsRow24Part00103Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00103.record002
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00103.record002
def vertexColumn : Fields := ⟨10, hexnat% "b52acc707cb4aaac687ab1aa639b16a5a56558d61db0ea3a2e4b8ae1ba1e4785e0f879a555535475a352d2b46d8745d0f69354cd31ce8b4acab1ae1b16c3ba1d8751cc749ca719e1745c9715c3783d0f23c4f0bc1f3921c470e28691a38519314a5195151550d0b41d30ca318d1314d0b0ac1b"⟩
def kindColumn : Fields := ⟨3, hexnat% "6d36d36d36db6db6da4db69269249349349249b69a4d34da6d2249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨24, by decide⟩, ⟨25, by decide⟩, ⟨28, by decide⟩, ⟨31, by decide⟩, ⟨33, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨38, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨81, by decide⟩, ⟨85, by decide⟩, ⟨89, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [8317599067324547072, 246290638176256, 324259173187452928, hexnat% "22000180000000000000000", hexnat% "200000000001210000000", 17592186044416]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "200181620c45a93000000", hexnat% "22000000000000000000000", 36046389205008384, 6935543426150563840, 3949445766971392, 72092778410016768]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "200000075e0bc0291000000", 3940649673949184, 144185659932803072, hexnat% "2000180000000000000000", hexnat% "200000000004000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [8088464933173329920, hexnat% "22000180000000001000000", 513410357553790976, 250688651132928, 3949445766971392, 36046389205008384, hexnat% "200000000005a00000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c4 c1
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c5 c0
  c6
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00103.record002_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00103.record002_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00103.record002_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00103.record002_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00103.record002_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00103.record002_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00103.record002_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00103.record002_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00103.record002_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00103.record002

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00103.record003
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00103.record003
def vertexColumn : Fields := ⟨10, hexnat% "b50eca70dc1f2d23aa9a3687ab1aa639b16a5a56558d61da8e638ce4b8ae1ba1e4789e1783e3a479b16a539715955551d68d3352d2b46d8745d0f6c3a8ce3c4e5354c73a2ccb4acab1ae1b16c3bc1e8791d4731e2749ca719e1745c570de0f43c8f13c2f07ce42b11c388aa4691919615454554342d0746384d1314d0b0ac1b"⟩
def kindColumn : Fields := ⟨3, hexnat% "1a6db4db6d36db6db69b4db6db4924da4924da4926d24926db6db4926d3691249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨21, by decide⟩, ⟨22, by decide⟩, ⟨25, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨75, by decide⟩, ⟨78, by decide⟩, ⟨89, by decide⟩, ⟨95, by decide⟩, ⟨100, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "80810100000000000", 1152956689018781696, hexnat% "200480000000000f0000000", hexnat% "108000000005000a0000000000", 4227622208798720, hexnat% "78280000000000000"]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00103.record003_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00103.record003_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00103.record003_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00103.record003_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00103.record003_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00103.record003_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00103.record003_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00103.record003_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00103.record003_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00103.record003

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00103.record017
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00103.record017
def vertexColumn : Fields := ⟨10, hexnat% "3e2d43d0ec3c8ea668da4e8ba1e8e6c5a96658d68d9362d876a398e3392e2b86eb4559365391e6c5c569595555356354d475a354d3352dc4e9334e334cc73a2ccb4ac6b46c9b16c3bc1e8731e2749c6785d1725c570de0f23c4f3306ca4a864388e0b8711a4654344d0b61344c3342c2b81d0709c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "1b69b6db6da6db6d24926db4db6db69a4926926d24da49a4926d2489249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨54, by decide⟩, ⟨63, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨80, by decide⟩, ⟨90, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40001f0001c110041c00000", 9241386435364257792, hexnat% "102000000000400000000", 949978583269376, 2819646029824, 38956695552]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40000100018000000400000", 9241405128135671808, hexnat% "3e00000000000800000", hexnat% "100000001000420000000", 669121544978432, 1128101094359040, 38956695552]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨68, by decide⟩ c1 c0
  c2
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00103.record017_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00103.record017_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00103.record017_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00103.record017_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00103.record017_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00103.record017_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00103.record017_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00103.record017_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00103.record017_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00103.record017

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00103.record026
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00103.record026
def vertexColumn : Fields := ⟨10, hexnat% "3e13c3c8ea668da4e8ba1eac6558d64d876c3a2e4b91e0f8f13a699664d94e4b91e6c5a555535535c362d4b61d4743db0ce364d5334d332cc73c2d8b32e2b4acab1ad1b26c5b0ef07a1e4751cc789d2745c9715c3783d0f0bc1f1d28a198d11c689464990e465454550d68330c6382d0b22c2b81d0711c27"⟩
def kindColumn : Fields := ⟨3, hexnat% "6db6db6db69b6da6924936926db4926d36924924934924924d2493249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨53, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨76, by decide⟩, ⟨82, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "406000227fe80be000000", hexnat% "c00c00000000000000", hexnat% "11220000000000000000", 545460846592, 72057594037927936, hexnat% "50000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "17c10327fe9d2e000000", hexnat% "400000000000090000000", 420906795008, hexnat% "40c00000000000000", hexnat% "220000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7c10103fe810e000000", 144115411414155264, hexnat% "40c00000000000000", hexnat% "4000000240000b0000000", 317827579904, hexnat% "10220000000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "17e30405ba8010000000", hexnat% "40800000080000000", hexnat% "400000020040020000000", 216172868013129728, 633456270770176, 322223210496]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "a50c01287fbe000000", 216331111788183552, hexnat% "11020020000000000000", hexnat% "400000004068000000000", 633318697598976, hexnat% "6400000000000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "270301207fbe000000", hexnat% "400000024068000000000", 800444465020928, hexnat% "2c00c00000000000000", hexnat% "5000000000000000000", hexnat% "10000000000000000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "200323fef50e000000", hexnat% "7c00000000000000000", 45902462976, hexnat% "400000004000000000000", hexnat% "50c00000000000000", hexnat% "10020000000000000000"]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "10260727a87f20000000", hexnat% "400000000068090000000", 87961165103104, hexnat% "810800000000000000", hexnat% "7400000000000000000"]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "13e70c2720951e000000", hexnat% "4000000920000000000", 455266533376, hexnat% "4000000000400a0000000", 79164837199872, 216172782113783808]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7e50c03a6158e000000", 455266533376, 216190374299828224, hexnat% "10020024000020000000", hexnat% "400000000008010000000", 79164837199872]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "270c03201520000000", 144115325649027072, hexnat% "7c00000020000000000", hexnat% "400000024048090000000", 317928243200, hexnat% "10000100100000000000", 219902325555200]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c11 c10
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c12 c9
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c13 c8
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c14 c7
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c15 c6
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c16 c5
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨69, by decide⟩ c17 c4
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c18 c3
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c19 c0
  c20
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00103.record026_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00103.record026_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00103.record026_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00103.record026_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00103.record026_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00103.record026_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00103.record026_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00103.record026_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00103.record026_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00103.record026
