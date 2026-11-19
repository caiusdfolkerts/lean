module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow24Part00060Data
public import GraphInputsRow24Part00060Frames
public import GraphInputsRow24Part00060Leaves
public import GraphInputsRow24Part00060Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00060.record009
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00060.record009
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨32, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨78, by decide⟩, ⟨83, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [73113125234147328, (certNat% 2), (certNat% 3), (certNat% 4)]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00060.record009_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00060.record009_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00060.record009_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00060.record009_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00060.record009_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00060.record009_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00060.record009_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00060.record009_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00060.record009_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00060.record009

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00060.record016
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00060.record016
def vertexColumn : Fields := ⟨10, (certNat% 5)⟩
def kindColumn : Fields := ⟨3, (certNat% 6)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨35, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨61, by decide⟩, ⟨64, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨72, by decide⟩, ⟨84, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 7), (certNat% 8), (certNat% 9), (certNat% 10), 288241373415473152, 2305895794361761792]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 11), 1378684502016, 2305897993921888256, (certNat% 12), 469762048, (certNat% 13)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 14), (certNat% 15), 2305878202175717376, (certNat% 10), (certNat% 13)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 16), (certNat% 17), 139586437120, (certNat% 9), 2594090977551450112, (certNat% 18)]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 19), (certNat% 20), (certNat% 21), 2305860601399738368, 8796093022208]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 22), 1099729731584, (certNat% 23), 4831838208, 2594110768760750080, (certNat% 8)]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 24), (certNat% 25), 1374725079040, 2594128370073600000, (certNat% 26), 8803609214976, 167772160]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨23, by decide⟩ c9 c4
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c10 c1
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c11 c0
  c12
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00060.record016_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00060.record016_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00060.record016_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00060.record016_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00060.record016_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00060.record016_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00060.record016_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00060.record016_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00060.record016_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00060.record016

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00060.record023
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00060.record023
def vertexColumn : Fields := ⟨10, (certNat% 27)⟩
def kindColumn : Fields := ⟨3, (certNat% 28)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨39, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨53, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨62, by decide⟩, ⟨64, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨71, by decide⟩, ⟨76, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 29), (certNat% 30), (certNat% 31), 9359043042738176, (certNat% 32), 140737488355328]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 33), 142945101545472, 4612811952693968896, 36033195065475072, (certNat% 34), (certNat% 35)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 36), 4612811952693968896, 72620544259784704, 36310272062783488, (certNat% 37), 140737488355328]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 38), 13194407968768, (certNat% 39), (certNat% 40), 72057594037927936]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 41), 72620544259784704, 142936545165312, (certNat% 42), 36033195132583936, (certNat% 35)]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 43), (certNat% 44), 211106232532992, 9570149476597760, (certNat% 45), 1125934266580992]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 46), 1688850128699392, 4611686069966995456, 422212565729280, (certNat% 47), 4294967296]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 48), (certNat% 49), (certNat% 50), 17626545782784, (certNat% 51)]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 52), 36310271995674624, (certNat% 51), (certNat% 30), (certNat% 32), (certNat% 53)]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 54), 1688849860263936, 4402341478400, 45035996273704960, (certNat% 35)]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 55), 1688884220002304, 13194139533312, (certNat% 56), 45035996273704960]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 57), (certNat% 58), 4402341478400, 9570149208162304, 4612811969873838080, (certNat% 59)]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨76, by decide⟩ c13 c12
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c14 c11
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 60), 36033195132583936, 1759252964179968, (certNat% 34), 9288674231451648, (certNat% 61), 4611686039902224384]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c16 c15
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c17 c10
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨64, by decide⟩ c18 c7
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨24, by decide⟩ c19 c6
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c20 c5
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c21 c2
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨23, by decide⟩ c22 c1
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c23 c0
  c24
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00060.record023_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00060.record023_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00060.record023_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00060.record023_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00060.record023_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00060.record023_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00060.record023_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00060.record023_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00060.record023_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00060.record023
