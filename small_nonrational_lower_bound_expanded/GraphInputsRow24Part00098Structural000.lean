module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow24Part00098Data
public import GraphInputsRow24Part00098Frames
public import GraphInputsRow24Part00098Leaves
public import GraphInputsRow24Part00098Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00098.record002
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record002
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨32, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨38, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨64, by decide⟩, ⟨68, by decide⟩, ⟨70, by decide⟩, ⟨72, by decide⟩, ⟨77, by decide⟩, ⟨89, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), 180145084623224832, 648518346341351424, (certNat% 3), (certNat% 4), (certNat% 5)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 6), (certNat% 7), 3332928176128, (certNat% 8), 272679353450496, (certNat% 9), 22517998149435392]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c1 c0
  c2
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record002_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record002_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record002_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record002_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record002_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record002_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record002_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record002_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record002_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00098.record002

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00098.record014
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record014
def vertexColumn : Fields := ⟨10, (certNat% 10)⟩
def kindColumn : Fields := ⟨3, (certNat% 11)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨27, by decide⟩, ⟨29, by decide⟩, ⟨32, by decide⟩, ⟨37, by decide⟩, ⟨44, by decide⟩, ⟨50, by decide⟩, ⟨56, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨71, by decide⟩, ⟨74, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨89, by decide⟩, ⟨92, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 12), (certNat% 13), (certNat% 14), (certNat% 15), (certNat% 16), (certNat% 17)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 18), (certNat% 19), (certNat% 13), (certNat% 14), (certNat% 20), (certNat% 21)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 22), 11529215046072664064, (certNat% 23), (certNat% 24), (certNat% 25), 72057594037927936]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 26), (certNat% 27), (certNat% 28), (certNat% 29), (certNat% 30), 72057594037927936]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 31), (certNat% 32), (certNat% 33), (certNat% 14), (certNat% 34), (certNat% 35), 72075186223972352]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨78, by decide⟩ c5 c2
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨23, by decide⟩ c6 c1
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c7 c0
  c8
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record014_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record014_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record014_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record014_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record014_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record014_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record014_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record014_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record014_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00098.record014

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00098.record030
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record030
def vertexColumn : Fields := ⟨10, (certNat% 36)⟩
def kindColumn : Fields := ⟨3, (certNat% 37)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨26, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨36, by decide⟩, ⟨39, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨46, by decide⟩, ⟨48, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨58, by decide⟩, ⟨60, by decide⟩, ⟨63, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨75, by decide⟩, ⟨77, by decide⟩, ⟨80, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 38), 1450159629769113600, (certNat% 39), 4864308160757760, (certNat% 40)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 41), (certNat% 42), 99079191802150912, (certNat% 43), 1441152430514372608]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 44), 1441152430514372608, 4516793766903808, 351843720888320]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 45), 369295169446477824, 4947819102208, 10376293541461622784, (certNat% 46), 4512395720392704]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 47), 10200547328, 4947819102208, 10376293541461622784, (certNat% 48), 4514599038615552]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 49), (certNat% 50), (certNat% 42), (certNat% 51), 4947802324992, 2097152]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 52), (certNat% 53), 4398065385472, (certNat% 54), 4584967782793216, 281474976710656]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 55), 4518992806936576, (certNat% 56), (certNat% 57), (certNat% 58), 4294967296]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 59), (certNat% 42), 4947819102208, (certNat% 54), 90071992549507072, (certNat% 57), 4514599038615552]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c10 c7
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c11 c6
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨72, by decide⟩ c12 c5
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨75, by decide⟩ c13 c4
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c14 c1
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨23, by decide⟩ c15 c0
  c16
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record030_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record030_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record030_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record030_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record030_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record030_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record030_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record030_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record030_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00098.record030

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00098.record041
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record041
def vertexColumn : Fields := ⟨10, (certNat% 60)⟩
def kindColumn : Fields := ⟨3, (certNat% 61)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2, 3]
def candidates : List (Fin raw.n) := [⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 62), (certNat% 63), 13510798882111488, 11529215046068469760, (certNat% 64)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 65), 70385924046848, (certNat% 66), 79938893385826304, (certNat% 67), (certNat% 68)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 69), (certNat% 70), (certNat% 63), 11817445422220181504, 35734127902720, (certNat% 71)]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .size 3
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .size 2
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨61, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 72), 4503599627370496, (certNat% 63), 2594073385365405696]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c7 c6
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 73), (certNat% 63), 2594073385365405696, 7881299347898368, 36028797018963968]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨66, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 74), 16888498602639360, 2594354929061593088, (certNat% 71), (certNat% 70), 36028797018963968]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨68, by decide⟩ c11 c10
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 75), 246290604621824, 6755399457832960, 1120986464256, (certNat% 76)]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 77), 1653562408960, 11835459820729663488, 105553384701952, 79938893402603520, (certNat% 70)]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c14 c13
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 78), 78812993495760896, (certNat% 66), 70385924046848, (certNat% 79), 9008298799923200]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 80), (certNat% 81), (certNat% 82), 79938893402603520, (certNat% 83), (certNat% 84)]
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 85), 2306125033946218496, 126100789566373888, 219902593990656, (certNat% 86), 9223372036854775808]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 87), 282093452001280, (certNat% 88), (certNat% 71), 70369012613120]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 89), 76561193665298432, (certNat% 66), 2306125103202566144, 9259400833873739776]
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 90), 79938893402603520, 11529496521045180416, (certNat% 81), (certNat% 79), 1717986918400, (certNat% 91)]
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c21 c20
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c22 c19
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c23 c18
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c24 c17
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c25 c16
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨68, by decide⟩ c26 c15
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c27 c12
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c28 c3
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c29 c2
  c30
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record041_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record041_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record041_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record041_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record041_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record041_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record041_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record041_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record041_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00098.record041

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00098.record023
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "5e1745b15c4f07caa8ea4e87aa58d64d8763392e1b91e1783eb86d1cc6715c6a95a4e9565391e565a5555355351d58d5352d1b51d1743da8ce3a4cd34cc73a2ccb8ad2b2ac6b46c5b0ee8731d2719e1745c9715c3743c4f0bc1f3323223a314c471325291a4c5454554348d1368388e130cc8b0ac8705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "6db6db6db6d36db6d24d26936924924934d34924926d24da492492249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record023 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record023 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record023.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record023.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record023.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 26), (facetIndex 35), (facetIndex 44), (facetIndex 58), (facetIndex 81)]))
 (.leaf ([(facetIndex 32), (facetIndex 36), (facetIndex 49), (facetIndex 51)])))
 (.branch 3
 (.leaf ([(facetIndex 28), (facetIndex 46), (facetIndex 47), (facetIndex 59), (facetIndex 60), (facetIndex 71), (facetIndex 72), (facetIndex 73)]))
 (.leaf ([(facetIndex 40), (facetIndex 42), (facetIndex 55), (facetIndex 65), (facetIndex 68), (facetIndex 69)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 27), (facetIndex 54), (facetIndex 56), (facetIndex 57)]))
 (.leaf ([(facetIndex 29), (facetIndex 30), (facetIndex 31), (facetIndex 61), (facetIndex 62)])))
 (.branch 7
 (.leaf ([(facetIndex 25), (facetIndex 41), (facetIndex 43), (facetIndex 45)]))
 (.leaf ([(facetIndex 24), (facetIndex 37), (facetIndex 53), (facetIndex 66)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1241b1d816a4247382084b0cf3039001b6a837z12;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 48), (facetIndex 63), (facetIndex 74)]))
 (.leaf ([(facetIndex 50), (facetIndex 70), (facetIndex 75)])))
 (.branch 3
 (.leaf ([(facetIndex 84), (facetIndex 85)]))
 (.branch 4
 (.leaf ([(facetIndex 88), (facetIndex 89)]))
 (.leaf ([(facetIndex 33), (facetIndex 34), (facetIndex 52), (facetIndex 64)])))))
 (.branch 7
 (.branch 6
 (.leaf ([(facetIndex 38), (facetIndex 39), (facetIndex 67), (facetIndex 76)]))
 (.leaf ([(facetIndex 79), (facetIndex 80), (facetIndex 90), (facetIndex 93)])))
 (.branch 8
 (.leaf ([(facetIndex 82), (facetIndex 83), (facetIndex 91), (facetIndex 94)]))
 (.branch 9
 (.leaf ([(facetIndex 77), (facetIndex 78), (facetIndex 92)]))
 (.leaf ([(facetIndex 86), (facetIndex 87), (facetIndex 95)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "976876339922770668851000010050040000000000040100000000005500044z21;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 10
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped2_0000 : List Nat := [0, 1, 2, 3]
def grouped2_0002 : List Nat := [4]
def grouped2_0003 : List Nat := [4, 5]
def grouped2_0004 : List Nat := [4, 5, 6, 7]
def grouped2_0005 : List Nat := [5]
def grouped2_0006 : List Nat := [6, 7]
def grouped3_0007 : List Nat := [0]
def grouped3_0008 : List Nat := [0, 1]
def grouped3_0009 : List Nat := [0, 1, 2, 3, 4]
def grouped3_0011 : List Nat := [1]
def grouped3_0012 : List Nat := [2]
def grouped3_0013 : List Nat := [2, 3, 4]
def grouped3_0014 : List Nat := [3]
def grouped3_0015 : List Nat := [3, 4]
def grouped3_0016 : List Nat := [4]
def grouped3_0017 : List Nat := [5]
def grouped3_0018 : List Nat := [5, 6]
def grouped3_0019 : List Nat := [5, 6, 7, 8, 9]
def grouped3_0020 : List Nat := [6]
def grouped3_0021 : List Nat := [7]
def grouped3_0022 : List Nat := [7, 8, 9]
def grouped3_0023 : List Nat := [8]
def grouped3_0024 : List Nat := [8, 9]
def grouped3_0025 : List Nat := [9]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record023 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record023_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00098.record023" "{\"atoms\":[{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0003\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group\",\"kind\":3,\"index\":9},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0018\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0024\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0022\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0019\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00098.record023" 45

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00098.record023" "{\"ridges\":[[8,641],[8,642],[27,268],[36,641],[36,642],[45,641],[45,642],[49,641],[49,642],[51,641],[51,642],[54,276],[56,296],[57,268],[63,660],[70,680],[74,720],[75,736],[85,660],[89,680]],\"owners\":[[8,641,[63,70,74,75],[36,45,49,51]],[36,641,[70,74,75],[8,45,49,51,63]],[45,641,[63,74,75],[8,36,49,51,70]],[49,641,[70,75],[8,36,45,51,63,74]],[51,641,[63,74],[8,36,45,49,70,75]],[8,642,[85,89],[36,45,49,51]],[36,642,[89],[8,45,49,51,85]],[45,642,[85],[8,36,49,51,89]],[49,642,[89],[8,36,45,51,85]],[51,642,[85],[8,36,45,49,89]],[27,268,[91,92,93],[11,54,56,57,58,78,80]],[57,268,[78,80,91],[11,27,54,56,58,92,93]],[54,276,[83,94],[13,31,60,62,78,91,92]],[56,296,[87,95],[16,42,66,69,80,91,93]],[63,660,[85],[]],[85,660,[63],[]],[70,680,[89],[]],[89,680,[70],[]],[74,720,[],[]],[75,736,[],[]]],\"edges\":[[43,[8,36,45,49,51,63,70,74,75,85,89]]],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00098.record023" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00098.record023\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-1,10,11,12,13],[-3,11,12,13],[-4,10,12,13],[-5,11,13],[-6,10,12],[-1,17,19],[-3,19],[-4,17],[-5,19],[-6,17],[-2,20,21,22],[-9,14,15,20],[-7,16,23],[-8,18,24],[-10,17],[-17,10],[-11,19],[-19,11],[-12],[-13],[-25,2,7,8,9],[-26,25],[-27,26],[-28,27],[28],[-10,29],[-11,30],[-17,31],[-19,32],[-15,33],[-22,33],[-16,34],[-20,34],[-23,34],[-14,35],[-21,35],[-18,36],[-24,36],[-30,37],[-29,37],[-32,38],[-38,39],[-31,39],[-37,-39,40],[-33,41],[-36,42],[-35,42],[-42,43],[-34,43],[-43,44],[-41,44],[-40,-44,45],[-45],[1,3,4,5,6,10,11,12,13,17,19]],\"atoms\":[{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group\",\"index\":9,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"mate\",\"ridge\":641,\"a\":8,\"owners\":[63,70,74,75]},{\"tag\":\"mate\",\"ridge\":641,\"a\":36,\"owners\":[70,74,75]},{\"tag\":\"mate\",\"ridge\":641,\"a\":45,\"owners\":[63,74,75]},{\"tag\":\"mate\",\"ridge\":641,\"a\":49,\"owners\":[70,75]},{\"tag\":\"mate\",\"ridge\":641,\"a\":51,\"owners\":[63,74]},{\"tag\":\"mate\",\"ridge\":642,\"a\":8,\"owners\":[85,89]},{\"tag\":\"mate\",\"ridge\":642,\"a\":36,\"owners\":[89]},{\"tag\":\"mate\",\"ridge\":642,\"a\":45,\"owners\":[85]},{\"tag\":\"mate\",\"ridge\":642,\"a\":49,\"owners\":[89]},{\"tag\":\"mate\",\"ridge\":642,\"a\":51,\"owners\":[85]},{\"tag\":\"mate\",\"ridge\":268,\"a\":27,\"owners\":[91,92,93]},{\"tag\":\"mate\",\"ridge\":268,\"a\":57,\"owners\":[78,80,91]},{\"tag\":\"mate\",\"ridge\":276,\"a\":54,\"owners\":[83,94]},{\"tag\":\"mate\",\"ridge\":296,\"a\":56,\"owners\":[87,95]},{\"tag\":\"mate\",\"ridge\":660,\"a\":63,\"owners\":[85]},{\"tag\":\"mate\",\"ridge\":660,\"a\":85,\"owners\":[63]},{\"tag\":\"mate\",\"ridge\":680,\"a\":70,\"owners\":[89]},{\"tag\":\"mate\",\"ridge\":680,\"a\":89,\"owners\":[70]},{\"tag\":\"mate\",\"ridge\":720,\"a\":74,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":736,\"a\":75,\"owners\":[]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[27,54,56,57],\"full_literals\":[-25,2,7,8,9]},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0003\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-26,25,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0004\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-27,26,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-28,false,27],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":63,\"full_literals\":[-10,29]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":70,\"full_literals\":[-11,30]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":85,\"full_literals\":[-17,31]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":89,\"full_literals\":[-19,32]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":80,\"full_literals\":[-15,33]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":93,\"full_literals\":[-22,33]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":83,\"full_literals\":[-16,34]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":91,\"full_literals\":[-20,34]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":94,\"full_literals\":[-23,34]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":78,\"full_literals\":[-14,35]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":92,\"full_literals\":[-21,35]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":87,\"full_literals\":[-18,36]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":95,\"full_literals\":[-24,36]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0008\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-30,37],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0008\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-29,false,37],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0015\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-32,false,38],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-38,39],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-31,false,39],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-37,-39,40],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0018\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-33,41],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0025\",\"joined_name\":\"grouped3_0024\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-36,42],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0025\",\"joined_name\":\"grouped3_0024\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-35,false,42],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0022\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-42,43],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0022\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-34,false,43],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0019\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-43,44],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0019\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-41,false,44],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-40,-44,45],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":43,\"owners\":[8,36,45,49,51,63,70,74,75,85,89]}]}"
  "55 27 0 25 24 0\n56 26 0 55 23 0\n57 25 0 56 22 0\n58 1 3 4 5 6 10 11 17 19 0 19 20 54 0\n59 37 0 20 19 39 40 27 26 2 4 18 1 3 5 16 58 0\n60 17 19 0 6 8 10 15 7 9 17 58 0\n61 39 0 42 43 41 28 29 60 0\n62 40 0 61 59 44 0\n63 -44 0 62 53 52 0\n64 -43 0 63 50 0\n65 -41 0 63 51 0\n66 -42 0 64 48 0\n67 -34 0 64 49 0\n68 -33 0 65 45 0\n69 -36 0 66 46 0\n70 -35 0 66 47 0\n71 -16 0 67 32 0\n72 -20 0 67 33 0\n73 -23 0 67 34 0\n74 -15 0 68 30 0\n75 -22 0 68 31 0\n76 -18 0 69 37 0\n77 -24 0 69 38 0\n78 -14 0 70 35 0\n79 -21 0 70 36 0\n80 -7 0 71 73 13 0\n81 -8 0 76 77 14 0\n82 -9 0 78 74 72 12 0\n83 -2 0 79 72 75 11 0\n84 0 82 81 57 80 83 21 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record023.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record023.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record023.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record023.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record023 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record023.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record023.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record023.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record023.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record023 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record023_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record023_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record023_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record023_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record023_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record023_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record023_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record023 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record023_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record023_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record023_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00098.record023

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00098.record028
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "2f03e16c3707c1ea964d8764b86e2785e0fae1b46b19c4f1aa5693a4d92e479596954d4756354d4b46d2745d0f723a4d331ce8b8ac6b26c5b0ee8749c6785d1725c570dc8f13c2f07cd4332324a90ea44d18c471325291a4c5254554348d1362348e130cd0b0ad0705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "36d36db4db6d249a49a69a49249a49349b4d3492492449249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record028 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record028 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record028.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 28), (facetIndex 31), (facetIndex 37), (facetIndex 52), (facetIndex 53), (facetIndex 56), (facetIndex 75)]))
 (.leaf ([(facetIndex 27), (facetIndex 39), (facetIndex 50), (facetIndex 51), (facetIndex 60), (facetIndex 62), (facetIndex 81)])))
 (.branch 3
 (.leaf ([(facetIndex 47), (facetIndex 58), (facetIndex 68), (facetIndex 69)]))
 (.leaf ([(facetIndex 42), (facetIndex 43), (facetIndex 45), (facetIndex 46), (facetIndex 48)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 29), (facetIndex 30), (facetIndex 54), (facetIndex 55)]))
 (.leaf ([(facetIndex 63), (facetIndex 64)])))
 (.branch 7
 (.leaf ([(facetIndex 32), (facetIndex 33), (facetIndex 34), (facetIndex 35)]))
 (.leaf ([(facetIndex 66), (facetIndex 67)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "8000000012fc5a410809002434d86c0200db61202z14;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 38), (facetIndex 41), (facetIndex 44)]))
 (.leaf ([(facetIndex 61), (facetIndex 65), (facetIndex 70)])))
 (.branch 3
 (.leaf ([(facetIndex 73), (facetIndex 78)]))
 (.leaf ([(facetIndex 83), (facetIndex 84)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 36), (facetIndex 49), (facetIndex 57), (facetIndex 59)]))
 (.leaf ([(facetIndex 71), (facetIndex 74), (facetIndex 77), (facetIndex 82)])))
 (.branch 7
 (.leaf ([(facetIndex 40), (facetIndex 76), (facetIndex 80)]))
 (.branch 8
 (.leaf ([(facetIndex 72)]))
 (.leaf ([(facetIndex 79)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "3350682560527510000100010404000000040000000060004z24;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 9
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped2_0000 : List Nat := [0, 1]
def grouped2_0001 : List Nat := [0, 1, 2, 3]
def grouped2_0003 : List Nat := [2]
def grouped2_0004 : List Nat := [2, 3]
def grouped2_0005 : List Nat := [3]
def grouped2_0006 : List Nat := [4]
def grouped2_0007 : List Nat := [4, 5]
def grouped2_0008 : List Nat := [4, 5, 6, 7]
def grouped2_0009 : List Nat := [5]
def grouped2_0010 : List Nat := [6, 7]
def grouped3_0011 : List Nat := [0]
def grouped3_0012 : List Nat := [0, 1]
def grouped3_0013 : List Nat := [0, 1, 2, 3]
def grouped3_0015 : List Nat := [1]
def grouped3_0016 : List Nat := [2]
def grouped3_0017 : List Nat := [2, 3]
def grouped3_0018 : List Nat := [3]
def grouped3_0019 : List Nat := [4]
def grouped3_0020 : List Nat := [4, 5]
def grouped3_0021 : List Nat := [4, 5, 6, 7, 8]
def grouped3_0022 : List Nat := [5]
def grouped3_0023 : List Nat := [6]
def grouped3_0024 : List Nat := [6, 7, 8]
def grouped3_0025 : List Nat := [7]
def grouped3_0026 : List Nat := [7, 8]
def grouped3_0027 : List Nat := [8]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record028 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record028_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00098.record028" "{\"atoms\":[{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0008\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0012\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0020\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0026\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0024\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0021\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00098.record028" 40

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00098.record028" "{\"ridges\":[[44,650],[47,641],[47,656],[58,641],[58,656],[63,104],[64,104],[65,680],[68,641],[68,656],[69,641],[69,656],[83,184]],\"owners\":[[63,104,[74,79,80,82],[15,42,52,60,64,83]],[64,104,[74,79,80,83],[15,42,52,60,63,82]],[47,641,[65,70],[21,38,44,58,68,69]],[58,641,[44,65,70],[21,38,47,68,69]],[68,641,[38,44],[21,47,58,65,69,70]],[69,641,[38,44,65],[21,47,58,68,70]],[47,656,[84],[21,58,68,69,78]],[58,656,[84],[21,47,68,69,78]],[68,656,[78],[21,47,58,69,84]],[69,656,[78],[21,47,58,68,84]],[44,650,[],[]],[83,184,[61],[]],[65,680,[],[]]],\"edges\":[],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00098.record028" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00098.record028\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":false,\"clauses\":[[-7,-5],[-6,12,14,15,16],[-7,12,14,15,17],[-3,8,11],[-4,2,8,11],[-9,1,2],[-10,1,2,8],[-3,18],[-4,18],[-9,13],[-10,13],[-2],[-17,5],[-8],[-19,3,4,9,10],[-20,6,7],[-21,19],[-22,21],[-23,20],[-24,23],[-25,22],[-25,24],[25],[-1,26],[-11,27],[-13,28],[-18,29],[-12,30],[-16,30],[-15,31],[-14,32],[-27,33],[-26,33],[-29,34],[-28,34],[-33,-34,35],[-30,36],[-32,37],[-37,38],[-31,38],[-38,39],[-36,39],[-35,-39,40],[-40]],\"atoms\":[{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":64,\"b\":61},{\"tag\":\"mate\",\"ridge\":104,\"a\":63,\"owners\":[74,79,80,82]},{\"tag\":\"mate\",\"ridge\":104,\"a\":64,\"owners\":[74,79,80,83]},{\"tag\":\"mate\",\"ridge\":641,\"a\":47,\"owners\":[65,70]},{\"tag\":\"mate\",\"ridge\":641,\"a\":58,\"owners\":[44,65,70]},{\"tag\":\"mate\",\"ridge\":641,\"a\":68,\"owners\":[38,44]},{\"tag\":\"mate\",\"ridge\":641,\"a\":69,\"owners\":[38,44,65]},{\"tag\":\"mate\",\"ridge\":656,\"a\":47,\"owners\":[84]},{\"tag\":\"mate\",\"ridge\":656,\"a\":58,\"owners\":[84]},{\"tag\":\"mate\",\"ridge\":656,\"a\":68,\"owners\":[78]},{\"tag\":\"mate\",\"ridge\":656,\"a\":69,\"owners\":[78]},{\"tag\":\"mate\",\"ridge\":650,\"a\":44,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":184,\"a\":83,\"owners\":[61]},{\"tag\":\"mate\",\"ridge\":680,\"a\":65,\"owners\":[]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[47,58,68,69],\"full_literals\":[-19,3,4,9,10]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[63,64],\"full_literals\":[-20,6,7]},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0004\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-21,19,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-22,false,21],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-23,false,20],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"grouped2_0008\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-24,23,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-25,22,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-25,false,24],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":38,\"full_literals\":[-1,26]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":70,\"full_literals\":[-11,27]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":78,\"full_literals\":[-13,28]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":84,\"full_literals\":[-18,29]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":74,\"full_literals\":[-12,30]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":82,\"full_literals\":[-16,30]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":80,\"full_literals\":[-15,31]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":79,\"full_literals\":[-14,32]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0012\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-27,33],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0012\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-26,false,33],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0017\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-29,34],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-28,false,34],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-33,-34,35],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0020\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-30,36],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0027\",\"joined_name\":\"grouped3_0026\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-32,37],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0024\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-37,38],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0024\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-31,false,38],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0021\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-38,39],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0021\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-36,false,39],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-35,-39,40],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true}]}"
  "45 22 0 23 21 0\n46 24 0 23 22 0\n47 21 0 45 18 0\n48 23 0 46 20 0\n49 19 0 47 17 0\n50 20 0 48 19 0\n51 34 0 49 34 35 27 26 8 9 10 11 15 0\n52 33 0 14 12 49 32 33 25 24 4 5 6 7 15 0\n53 35 0 52 51 36 0\n54 -39 0 53 44 43 0\n55 -38 0 54 41 0\n56 -36 0 54 42 0\n57 -37 0 55 39 0\n58 -31 0 55 40 0\n59 -30 0 56 37 0\n60 -32 0 57 38 0\n61 -15 0 58 30 0\n62 -12 0 59 28 0\n63 -16 0 59 29 0\n64 -14 0 60 31 0\n65 -6 0 64 62 61 63 2 0\n66 7 0 65 50 16 0\n67 -5 0 66 1 0\n68 17 0 66 62 61 64 3 0\n69 0 68 67 13 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record028.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record028.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record028.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record028.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record028 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS noSame
  exact boundary_unsat S HS noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record028.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record028.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record028.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record028.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record028 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record028_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record028_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record028_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record028_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record028_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record028_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record028_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record028 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record028_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record028_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record028_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00098.record028

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00098.record039
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "3716a36b26a58d61da8e3392e1b91e2785eb8569c96a53969535475a358d3352d1b51d176c3c8e6358e9334c73a2d4b32d2b1ad1b26f07a1cc719e1745c9715c3783c8f13c2f3609c16a264990e078d13249916685895252550d2341d88d2318c5342c4b06e0741c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1349b6da6926d269349269349349a492493492492489249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record039 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record039 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record039.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record039.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record039.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 59), (facetIndex 70)]))
 (.branch 2
 (.leaf ([(facetIndex 56), (facetIndex 71)]))
 (.leaf ([(facetIndex 75), (facetIndex 84)]))))
 (.branch 5
 (.branch 4
 (.leaf ([(facetIndex 40), (facetIndex 49), (facetIndex 52)]))
 (.leaf ([(facetIndex 64), (facetIndex 67), (facetIndex 77)])))
 (.branch 6
 (.leaf ([(facetIndex 78), (facetIndex 80), (facetIndex 81)]))
 (.leaf ([(facetIndex 79)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "202dd60400200804000001003018000003z1e;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 7
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped3_0000 : List Nat := [0]
def grouped3_0001 : List Nat := [0, 1, 2]
def grouped3_0003 : List Nat := [1]
def grouped3_0004 : List Nat := [1, 2]
def grouped3_0005 : List Nat := [2]
def grouped3_0006 : List Nat := [3]
def grouped3_0007 : List Nat := [3, 4]
def grouped3_0008 : List Nat := [3, 4, 5, 6]
def grouped3_0009 : List Nat := [4]
def grouped3_0010 : List Nat := [5]
def grouped3_0011 : List Nat := [5, 6]
def grouped3_0012 : List Nat := [6]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record039 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record039_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00098.record039" "{\"atoms\":[{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0004\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0007\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0011\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0011\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00098.record039" 41

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00098.record039" "{\"ridges\":[[9,97],[18,644],[39,97],[41,644],[45,98],[49,650],[50,97],[52,658],[53,97],[54,97],[56,706],[63,644],[64,116],[66,644],[67,228],[68,644],[71,736],[78,650],[79,116],[80,198],[81,658]],\"owners\":[[9,97,[59,64,67,70,71],[39,45,50,53,54]],[39,97,[70,71],[9,45,50,53,54,59,64,67]],[50,97,[59,67,70,71],[9,39,45,53,54,64]],[53,97,[59,64,67,71],[9,39,45,50,54,70]],[54,97,[59,64,67,70],[9,39,45,50,53,71]],[45,98,[79],[9,39,50,53,54,75,84]],[18,644,[78,81],[41,63,66,68]],[41,644,[],[18,63,66,68,78,81]],[63,644,[81],[18,41,66,68,78]],[66,644,[78],[18,41,63,68,81]],[68,644,[78,81],[18,41,63,66]],[80,198,[40,77],[]],[49,650,[78],[]],[78,650,[49],[]],[52,658,[81],[]],[81,658,[52],[]],[56,706,[],[]],[64,116,[79],[]],[79,116,[64],[]],[67,228,[],[]],[71,736,[],[]]],\"edges\":[[35,[9,39,45,50,53,54,59,64,67,70,71,75,79,84]],[43,[18,41,49,52,56,63,66,68,71,78,81]]],\"groupings\":[3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00098.record039" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00098.record039\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-1,13,15,17,19,20],[-3,19,20],[-8,13,17,19,20],[-10,13,15,17,20],[-11,13,15,17,19],[-6,24],[-2,23,26],[-5],[-14,26],[-16,23],[-18,23,26],[-25,4,22],[-7,23],[-23,7],[-9,26],[-26,9],[-12],[-15,24],[-24,15],[-17],[-20],[-13,28],[-19,28],[-21,29],[-27,29],[-4,30],[-7,30],[-9,30],[-15,31],[-22,31],[-32,23,25,26],[-23,32],[-26,32],[-33,24],[-24,33],[-29,34],[-34,35],[-28,35],[-31,36],[-30,36],[-32,37],[-38,33],[-32,-33,38],[-36,-37,39],[-36,-38,40],[-40,41],[-35,-39,41],[-41],[1,3,6,8,10,11,13,15,17,19,20,21,24,27],[2,5,7,9,12,14,16,18,20,23,26]],\"atoms\":[{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"mate\",\"ridge\":97,\"a\":9,\"owners\":[59,64,67,70,71]},{\"tag\":\"mate\",\"ridge\":97,\"a\":39,\"owners\":[70,71]},{\"tag\":\"mate\",\"ridge\":97,\"a\":50,\"owners\":[59,67,70,71]},{\"tag\":\"mate\",\"ridge\":97,\"a\":53,\"owners\":[59,64,67,71]},{\"tag\":\"mate\",\"ridge\":97,\"a\":54,\"owners\":[59,64,67,70]},{\"tag\":\"mate\",\"ridge\":98,\"a\":45,\"owners\":[79]},{\"tag\":\"mate\",\"ridge\":644,\"a\":18,\"owners\":[78,81]},{\"tag\":\"mate\",\"ridge\":644,\"a\":41,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":644,\"a\":63,\"owners\":[81]},{\"tag\":\"mate\",\"ridge\":644,\"a\":66,\"owners\":[78]},{\"tag\":\"mate\",\"ridge\":644,\"a\":68,\"owners\":[78,81]},{\"tag\":\"mate\",\"ridge\":198,\"a\":80,\"owners\":[40,77]},{\"tag\":\"mate\",\"ridge\":650,\"a\":49,\"owners\":[78]},{\"tag\":\"mate\",\"ridge\":650,\"a\":78,\"owners\":[49]},{\"tag\":\"mate\",\"ridge\":658,\"a\":52,\"owners\":[81]},{\"tag\":\"mate\",\"ridge\":658,\"a\":81,\"owners\":[52]},{\"tag\":\"mate\",\"ridge\":706,\"a\":56,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":116,\"a\":64,\"owners\":[79]},{\"tag\":\"mate\",\"ridge\":116,\"a\":79,\"owners\":[64]},{\"tag\":\"mate\",\"ridge\":228,\"a\":67,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":736,\"a\":71,\"owners\":[]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":59,\"full_literals\":[-13,28]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":70,\"full_literals\":[-19,28]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":75,\"full_literals\":[-21,29]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":84,\"full_literals\":[-27,29]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":40,\"full_literals\":[-4,30]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":49,\"full_literals\":[-7,30]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":52,\"full_literals\":[-9,30]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":64,\"full_literals\":[-15,31]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":77,\"full_literals\":[-22,31]},{\"tag\":\"group_or\",\"kind\":3,\"index\":5,\"members\":[78,80,81],\"full_literals\":[-32,23,25,26]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":78,\"full_literals\":[-23,32]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":81,\"full_literals\":[-26,32]},{\"tag\":\"group_or\",\"kind\":3,\"index\":6,\"members\":[79],\"full_literals\":[-33,24]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":79,\"full_literals\":[-24,33]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0003\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0004\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-29,34],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-34,35],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-28,false,35],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0006\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0007\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-31,36],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0006\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0007\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-30,false,36],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0012\",\"joined_name\":\"grouped3_0011\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-32,false,37],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0012\",\"joined_name\":\"grouped3_0011\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-38,false,33],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0012\",\"joined_name\":\"grouped3_0011\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-32,-33,38],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0008\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-36,-37,39],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0008\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-36,-38,40],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"groupKind3\",\"a\":0,\"b\":3,\"direction\":\"forward\",\"full_literals\":[false,-40,41],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-35,-39,41],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":35,\"owners\":[9,39,45,50,53,54,59,64,67,70,71,75,79,84]},{\"tag\":\"edge\",\"edge\":43,\"owners\":[18,41,49,52,56,63,66,68,71,78,81]}]}"
  "51 -40 0 48 46 0\n52 1 3 6 8 10 11 13 15 19 21 24 27 0 20 21 49 0\n53 2 7 9 14 16 18 23 26 0 8 17 21 50 0\n54 -38 0 51 42 45 34 39 19 29 0\n55 32 0 32 33 10 13 9 15 7 11 53 0\n56 37 0 55 41 0\n57 -33 0 55 54 43 0\n58 -24 0 57 35 0\n59 -6 0 58 6 0\n60 -15 0 58 18 0\n61 35 0 20 21 60 58 59 37 38 36 22 23 24 25 3 1 4 5 2 52 0\n62 -39 0 61 48 47 0\n63 -36 0 62 56 44 0\n64 -31 0 63 39 0\n65 -30 0 63 40 0\n66 -22 0 64 30 0\n67 -4 0 65 26 0\n68 -7 0 65 27 0\n69 -9 0 65 28 0\n70 -25 0 66 67 12 0\n71 -23 0 68 14 0\n72 -26 0 69 16 0\n73 0 70 71 55 72 31 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record039.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record039.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record039.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record039.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record039 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record039.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record039.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record039.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record039.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record039 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record039_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record039_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record039_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record039_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record039_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record039_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record039_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record039 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record039_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record039_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record039_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00098.record039
