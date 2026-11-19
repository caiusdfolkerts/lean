module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow24Part00071Data
public import GraphInputsRow24Part00071Frames
public import GraphInputsRow24Part00071Leaves
public import GraphInputsRow24Part00071Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00071.record001
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record001
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2, 3]
def candidates : List (Fin raw.n) := [⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), (certNat% 3), 2251907187867648, (certNat% 4), (certNat% 5), 9147936743096320]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 6), (certNat% 7), 11399736556781568, (certNat% 8), (certNat% 9), 1409573906808832]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 10), (certNat% 11), 703700326678528, 11259067787902976, 34359738368]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 12), (certNat% 13), (certNat% 14), 2251907187867648, 288234791378092032, 563508299169792]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨66, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 15), (certNat% 16), 47244640256, 562949953421312]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 3 [(certNat% 17)]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨80, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 18), (certNat% 9), 47244640256, (certNat% 19), 703687441776640]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 20), 4947802324992, (certNat% 21), (certNat% 22), 115964116992, 703687441776640]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c10 c7
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 23), (certNat% 24), 563783177076736, 360287987369508864, (certNat% 25), 144121785145622528]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 26), (certNat% 27), (certNat% 28), (certNat% 29), (certNat% 30), 985162418487296]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 31), (certNat% 32), 115964116992, 5222680231936, (certNat% 33), 985162418487296]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 34), (certNat% 35), 133143986176, (certNat% 36), 985712174301184, 432352161297334272, (certNat% 37)]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c15 c14
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c16 c13
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c17 c12
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c18 c11
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨67, by decide⟩ c19 c4
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c20 c1
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c21 c0
  c22
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record001_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record001_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record001_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record001_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record001_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record001_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record001_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record001_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record001_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00071.record001

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00071.record002
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record002
def vertexColumn : Fields := ⟨10, (certNat% 38)⟩
def kindColumn : Fields := ⟨3, (certNat% 39)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨46, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨61, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [4123437039616, 108649344231538688, 2451154470235537408, (certNat% 40), (certNat% 41), 6755425210859520, 18295874023063552]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record002_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record002_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record002_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record002_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record002_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record002_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record002_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record002_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record002_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00071.record002

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00071.record006
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record006
def vertexColumn : Fields := ⟨10, (certNat% 42)⟩
def kindColumn : Fields := ⟨3, (certNat% 43)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨64, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨78, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 44), 2089670228173651968, 2041655653826560, (certNat% 45), (certNat% 46), (certNat% 47), 4529988443308032]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record006_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record006_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record006_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record006_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record006_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record006_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record006_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record006_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record006_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00071.record006

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00071.record008
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record008
def vertexColumn : Fields := ⟨10, (certNat% 48)⟩
def kindColumn : Fields := ⟨3, (certNat% 49)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 50), 16888498871074816, 3458766163087982592, (certNat% 51), (certNat% 52), 280917704704, (certNat% 53)]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record008_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record008_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record008_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record008_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record008_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record008_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record008_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record008_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record008_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00071.record008

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00071.record013
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record013
def vertexColumn : Fields := ⟨10, (certNat% 54)⟩
def kindColumn : Fields := ⟨3, (certNat% 55)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2, 3]
def candidates : List (Fin raw.n) := [⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .size 3
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 56), 4611686024869838848, 3298534883328, 211106232532992]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 57), 211108380016640, 36029896530591744, 2203318222848, 4827858800541171712]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨65, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 58), (certNat% 59), 45405432180637696, (certNat% 60), 3440268804096, 149533581377536]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 61), 140742857064448, 2748779069440, 5764607523034234880]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨69, by decide⟩ c7 c0
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 62), 5764607524107976704, (certNat% 63), 2203318222848, 153931627888640]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 64), (certNat% 59), (certNat% 65), (certNat% 66), 2890512990208, 4755801206503243776]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨64, by decide⟩ c11 c10
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 67), (certNat% 63), 3382097767038976, 2207613190144, (certNat% 68)]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 69), 5764607523034234880, 3856880631808, (certNat% 68), (certNat% 70)]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 71), 5764607526255460352, (certNat% 72), 3852585664512, 10423370231316480, (certNat% 73)]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c15 c14
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c16 c13
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 74), (certNat% 75), (certNat% 73), 9508577630748672, (certNat% 76), 3990024617984, 1125951446450176]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨64, by decide⟩ c18 c17
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨52, by decide⟩ c19 c12
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨66, by decide⟩ c20 c6
  c21
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record013_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record013_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record013_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record013_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record013_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record013_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record013_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record013_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record013_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00071.record013

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00071.record021
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record021
def vertexColumn : Fields := ⟨10, (certNat% 77)⟩
def kindColumn : Fields := ⟨3, (certNat% 78)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨49, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨64, by decide⟩, ⟨67, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 79), 108649342084055040, (certNat% 80), 123145839181824, (certNat% 81), (certNat% 82)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 83), (certNat% 84), 8521215115264, (certNat% 85), (certNat% 86), 131941395333120]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 87), (certNat% 88), 7421837705216, (certNat% 89), (certNat% 90), (certNat% 91)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 92), (certNat% 89), (certNat% 80), 114350014595072, (certNat% 93), (certNat% 94)]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 95), 31525197391593472, (certNat% 96), 108649344231538688, (certNat% 97), (certNat% 91)]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 98), (certNat% 89), (certNat% 99), 105621835743232, 4844723109888, 2748779069440]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 100), 113152943858909184, (certNat% 101), (certNat% 102), 39822970322944, (certNat% 103), 274877906944]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨71, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c7 c4
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c8 c3
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c9 c2
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c10 c1
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c11 c0
  c12
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record021_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record021_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record021_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record021_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record021_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record021_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record021_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record021_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record021_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00071.record021

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00071.record027
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record027
def vertexColumn : Fields := ⟨10, (certNat% 104)⟩
def kindColumn : Fields := ⟨3, (certNat% 105)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨51, by decide⟩, ⟨53, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨89, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 106), (certNat% 107), 1055531162664960, (certNat% 108), 144115188075855872, (certNat% 109)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 110), (certNat% 111), 422762757750784, (certNat% 112), 650910883643392, 216172953912475648]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 113), 422762757750784, 571746180661248, (certNat% 114), (certNat% 115), (certNat% 116)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 117), (certNat% 118), (certNat% 119), (certNat% 120), (certNat% 108), (certNat% 109)]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 121), 216172919552737280, (certNat% 122), 841813590016]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 123), (certNat% 124), 144256063003164672, (certNat% 125), 841813590016]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 126), 979252543488, 216471849276538880, (certNat% 111), 288371113640067072, (certNat% 127)]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨67, by decide⟩ c7 c6
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 128), (certNat% 129), 825170591744, 144484623982788608, 703687441776640]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 130), 72075186223972352, (certNat% 131), (certNat% 111), (certNat% 132)]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 133), 668503606558720, 216172919552737280, (certNat% 122), 841813590016]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 134), (certNat% 111), (certNat% 135), 967570769313792, 216172919552737280, 566935683072]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨67, by decide⟩ c12 c11
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c13 c10
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨61, by decide⟩ c14 c9
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 136), 981400027136, 1090716071624704, 218442174113513472, (certNat% 137), (certNat% 138), (certNat% 139)]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨76, by decide⟩ c16 c15
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c17 c8
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c18 c3
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c19 c2
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c20 c1
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c21 c0
  c22
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record027_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record027_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record027_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record027_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record027_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record027_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record027_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record027_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00071.record027_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00071.record027
