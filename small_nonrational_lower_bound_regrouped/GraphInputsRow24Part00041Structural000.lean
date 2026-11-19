module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow24Part00041Data
public import GraphInputsRow24Part00041Frames
public import GraphInputsRow24Part00041Leaves
public import GraphInputsRow24Part00041Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00041.record006
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record006
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2, 3]
def candidates : List (Fin raw.n) := [⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩, ⟨95, by decide⟩, ⟨96, by decide⟩, ⟨97, by decide⟩, ⟨98, by decide⟩, ⟨99, by decide⟩, ⟨100, by decide⟩, ⟨101, by decide⟩, ⟨102, by decide⟩, ⟨103, by decide⟩, ⟨104, by decide⟩, ⟨105, by decide⟩, ⟨106, by decide⟩, ⟨107, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), (certNat% 3), (certNat% 4), (certNat% 5), (certNat% 6)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .size 3
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨98, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), (certNat% 3), (certNat% 7), (certNat% 8), (certNat% 9)]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨98, by decide⟩ c1 c3
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 10), (certNat% 11), (certNat% 12), (certNat% 13), (certNat% 14), 71635381572861952]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 15), (certNat% 16), 8048768712704, (certNat% 17), (certNat% 18), 69673852828909568]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 19), (certNat% 3), (certNat% 20), (certNat% 21), 9151314442816847872, 48835908459298816]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 22), (certNat% 23), 9079327217523097600, (certNat% 24), (certNat% 25), 71776119061217280]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 26), (certNat% 27), (certNat% 17), (certNat% 28), 8574924059257602048, 69673852828909568]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 29), 8581344657408, 9151384811561025536, (certNat% 18), (certNat% 30), (certNat% 31), 71925652642594816]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨70, by decide⟩ c10 c9
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c11 c8
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨85, by decide⟩ c12 c7
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨97, by decide⟩ c13 c6
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c14 c5
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c15 c4
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c16 c2
  c17
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record006_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record006_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record006_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record006_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record006_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record006_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record006_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record006_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record006_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00041.record006

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00041.record022
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record022
def vertexColumn : Fields := ⟨10, (certNat% 32)⟩
def kindColumn : Fields := ⟨3, (certNat% 33)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨23, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨54, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 34), (certNat% 35), 216172782248001536, (certNat% 36), (certNat% 37), (certNat% 38)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 39), 720575941184585728, (certNat% 40), (certNat% 35), (certNat% 41), (certNat% 42)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 43), (certNat% 36), 288230378433413120, (certNat% 44), (certNat% 37), (certNat% 45)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [9152726292989214720, (certNat% 46), (certNat% 47), (certNat% 48), (certNat% 41), (certNat% 49)]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 50), 720575940647714816, 360287970390966272, (certNat% 35), (certNat% 51), 274877906944]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 52), 720575940647714816, (certNat% 53), (certNat% 54), 360287970390966272, 8070450533321670656]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 55), 360287970256748544, 720575940647714816, (certNat% 56), (certNat% 47), 4611686018427387904]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 57), 360287970256748544, (certNat% 58), 720575940647714816, (certNat% 59), 8070450533321670656]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 60), (certNat% 61), 4899916394646208512, (certNat% 48), (certNat% 62), (certNat% 63)]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 64), (certNat% 48), (certNat% 36), (certNat% 35), 360287970390966272, (certNat% 62), (certNat% 65)]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c10 c7
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c11 c6
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c12 c5
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨71, by decide⟩ c13 c4
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c14 c3
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c15 c2
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c16 c1
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c17 c0
  c18
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record022_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record022_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record022_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record022_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record022_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record022_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record022_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record022_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record022_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00041.record022

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00041.record024
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record024
def vertexColumn : Fields := ⟨10, (certNat% 66)⟩
def kindColumn : Fields := ⟨3, (certNat% 67)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨78, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 68), (certNat% 69), (certNat% 70), 310062279032832, 14073817555009536, 593779228672]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 71), (certNat% 72), (certNat% 73), 661424963584, 14091341021577216, 292472240472064]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 74), (certNat% 75), 14073817555009536, 1729382274090139648, (certNat% 76), 824633720832]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [446910493039263744, (certNat% 77), (certNat% 78), (certNat% 76), 1729382282680074240, 274877906944]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 79), (certNat% 80), 14091341021577216, (certNat% 81), (certNat% 76), 422212465065984]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [446763459128852480, 1765411053929234432, (certNat% 78), (certNat% 76), (certNat% 82), 140737488355328]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [6841454916553146368, 562949953421312, (certNat% 83), (certNat% 76), (certNat% 81)]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [1617841444058300416, (certNat% 84), 833223655424, (certNat% 85), (certNat% 86), (certNat% 87)]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c7 c6
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [446727282619318272, (certNat% 85), (certNat% 78), (certNat% 88), 1152921805254557696, (certNat% 89), 35871566856192]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c10 c5
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c11 c4
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c12 c3
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c13 c2
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c14 c1
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c15 c0
  c16
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record024_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record024_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record024_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record024_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record024_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record024_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record024_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record024_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record024_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00041.record024

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00041.record025
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record025
def vertexColumn : Fields := ⟨10, (certNat% 90)⟩
def kindColumn : Fields := ⟨3, (certNat% 91)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨59, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 92), (certNat% 93), 14483578600646770688, (certNat% 27), (certNat% 94), 3799912185593856, 45861660786688]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record025_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record025_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record025_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record025_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record025_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record025_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record025_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record025_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record025_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00041.record025

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00041.record032
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record032
def vertexColumn : Fields := ⟨10, (certNat% 95)⟩
def kindColumn : Fields := ⟨3, (certNat% 96)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨71, by decide⟩, ⟨75, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 97), 342273575975124992, 9799832789158199296, (certNat% 98), 2836739999662080, 128849018880]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 99), (certNat% 100), (certNat% 101), (certNat% 102), 8444249301319680]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 103), 198158387899269120, 9799832789158199296, (certNat% 98), 5629585433559040, 32985348833280]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 104), (certNat% 105), 562640715776, 486388759756013568, 281474976710656]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 106), (certNat% 107), 486388764050980864, (certNat% 108), 592705486848, 292472240472064, 8444249301319680]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c5 c2
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c6 c1
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c7 c0
  c8
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record032_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record032_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record032_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record032_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record032_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record032_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record032_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record032_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record032_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00041.record032

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00041.record035
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record035
def vertexColumn : Fields := ⟨10, (certNat% 109)⟩
def kindColumn : Fields := ⟨3, (certNat% 110)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨35, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨43, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨70, by decide⟩, ⟨76, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [9015998032117760, (certNat% 111), 4123235713024, 6473924598562816, 432486301715922944, 177435836416]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record035_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record035_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record035_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record035_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record035_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record035_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record035_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record035_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record035_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00041.record035
