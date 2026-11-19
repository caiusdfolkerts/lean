module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow23Part00036Data
public import GraphInputsRow23Part00036Frames
public import GraphInputsRow23Part00036Leaves
public import GraphInputsRow23Part00036Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00036.record000
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00036.record000
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩, ⟨95, by decide⟩, ⟨96, by decide⟩, ⟨97, by decide⟩, ⟨98, by decide⟩, ⟨99, by decide⟩, ⟨100, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), (certNat% 3), (certNat% 4), (certNat% 5), (certNat% 6), 4251398048237748224]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 7), (certNat% 8), (certNat% 9), (certNat% 10), 4179340454199820288, (certNat% 11)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 12), (certNat% 13), (certNat% 14), (certNat% 15), (certNat% 16), 4179340454199820288, (certNat% 17)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨72, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c3 c0
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 18), (certNat% 3), (certNat% 19), (certNat% 20), (certNat% 21), 4251398048237748224]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 22), (certNat% 8), (certNat% 9), (certNat% 10), 4107282860161892352, (certNat% 11)]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 23), (certNat% 24), (certNat% 14), (certNat% 15), (certNat% 16), 4107282860161892352, (certNat% 17)]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨72, by decide⟩ c7 c6
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c8 c5
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 25), 452998790643712, (certNat% 26), (certNat% 27), (certNat% 28), (certNat% 29), (certNat% 30), 4032973466310279168]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 31), (certNat% 3), (certNat% 4), (certNat% 32), (certNat% 33), 4251398048237748224]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 34), (certNat% 35), (certNat% 36), (certNat% 37), 4179340454199820288, (certNat% 11)]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 38), (certNat% 39), (certNat% 15), (certNat% 40), (certNat% 16), 4179340454199820288, (certNat% 41)]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨88, by decide⟩ c13 c12
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c14 c11
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 42), (certNat% 43), (certNat% 44), 1124800395214848, (certNat% 45), (certNat% 46), (certNat% 41), 4314448443020935168, (certNat% 47)]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨74, by decide⟩ c16 c15
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨82, by decide⟩ c17 c10
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨89, by decide⟩ c18 c9
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨90, by decide⟩ c19 c4
  c20
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00036.record000_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00036.record000_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00036.record000_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00036.record000_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00036.record000_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00036.record000_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00036.record000_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00036.record000_validity Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00036.record000_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00036.record000

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00036.record003
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00036.record003
def vertexColumn : Fields := ⟨10, (certNat% 48)⟩
def kindColumn : Fields := ⟨3, (certNat% 49)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩, ⟨95, by decide⟩, ⟨96, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 50), (certNat% 51), (certNat% 52), (certNat% 53), (certNat% 54), (certNat% 55), (certNat% 56), 1783425452438716416, (certNat% 57)]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00036.record003_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00036.record003_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00036.record003_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00036.record003_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00036.record003_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00036.record003_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00036.record003_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00036.record003_validity Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00036.record003_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00036.record003

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00036.record006
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00036.record006
def vertexColumn : Fields := ⟨10, (certNat% 58)⟩
def kindColumn : Fields := ⟨3, (certNat% 59)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩, ⟨95, by decide⟩, ⟨96, by decide⟩, ⟨97, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 60), 141864212895891456, 9079260147313803264, (certNat% 61), (certNat% 62), (certNat% 63), (certNat% 64), (certNat% 65), 136339441844224]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00036.record006_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00036.record006_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00036.record006_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00036.record006_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00036.record006_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00036.record006_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00036.record006_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00036.record006_validity Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00036.record006_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00036.record006

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00036.record008
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00036.record008
def vertexColumn : Fields := ⟨10, (certNat% 66)⟩
def kindColumn : Fields := ⟨3, (certNat% 67)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩, ⟨95, by decide⟩, ⟨96, by decide⟩, ⟨97, by decide⟩, ⟨98, by decide⟩, ⟨99, by decide⟩, ⟨100, by decide⟩, ⟨101, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 68), (certNat% 69), (certNat% 70), (certNat% 71), (certNat% 72), (certNat% 73), (certNat% 74), 70087269200953344, (certNat% 75)]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00036.record008_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00036.record008_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00036.record008_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00036.record008_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00036.record008_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00036.record008_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00036.record008_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00036.record008_validity Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00036.record008_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00036.record008

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00036.record012
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00036.record012
def vertexColumn : Fields := ⟨10, (certNat% 76)⟩
def kindColumn : Fields := ⟨3, (certNat% 77)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩, ⟨95, by decide⟩, ⟨96, by decide⟩, ⟨97, by decide⟩, ⟨98, by decide⟩, ⟨99, by decide⟩, ⟨100, by decide⟩, ⟨101, by decide⟩, ⟨102, by decide⟩, ⟨103, by decide⟩, ⟨104, by decide⟩, ⟨105, by decide⟩, ⟨106, by decide⟩, ⟨107, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [2305702684042199040, (certNat% 78), (certNat% 79), (certNat% 80), (certNat% 81), (certNat% 82), (certNat% 83), 130841883705344, (certNat% 84)]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00036.record012_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00036.record012_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00036.record012_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00036.record012_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00036.record012_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00036.record012_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00036.record012_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00036.record012_validity Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00036.record012_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00036.record012

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00036.record009
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "32a36a3a4e8ba1eb2635a364d8b61da2e4b89e1783eca4d98e5392e479c94d58d5352d4758b52d2745d0f72334e334ccb31cf0ba2d8b92d4b32cab1ae1b46f07a1d8791d4731ca719e1745e0f43c8f13c2f07e2a4a89a1683a89926258560da294a4991643989525254550d62348c9314c3382d0b22c4b0ac1b81d0721c4709c17"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "92492492492492492492492492492492492492492492492491249249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00036.record009 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00036.record009 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00036.record009.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00036.record009.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00036.record009.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 37), (facetIndex 38), (facetIndex 39), (facetIndex 40), (facetIndex 41), (facetIndex 42), (facetIndex 43), (facetIndex 44), (facetIndex 45), (facetIndex 46), (facetIndex 47), (facetIndex 48), (facetIndex 49), (facetIndex 50), (facetIndex 51), (facetIndex 52)]))
 (.leaf ([(facetIndex 53), (facetIndex 54), (facetIndex 55), (facetIndex 56), (facetIndex 57), (facetIndex 58), (facetIndex 59), (facetIndex 60), (facetIndex 61), (facetIndex 62)])))
 (.branch 3
 (.leaf ([(facetIndex 69), (facetIndex 74), (facetIndex 75), (facetIndex 76), (facetIndex 77), (facetIndex 78)]))
 (.branch 4
 (.leaf ([(facetIndex 68), (facetIndex 72), (facetIndex 73), (facetIndex 79), (facetIndex 85)]))
 (.leaf ([(facetIndex 80), (facetIndex 81), (facetIndex 82), (facetIndex 83), (facetIndex 84)])))))
 (.branch 7
 (.branch 6
 (.leaf ([(facetIndex 86), (facetIndex 91), (facetIndex 92), (facetIndex 93), (facetIndex 94), (facetIndex 96)]))
 (.leaf ([(facetIndex 97), (facetIndex 98), (facetIndex 99), (facetIndex 100), (facetIndex 102)])))
 (.branch 8
 (.leaf ([(facetIndex 63), (facetIndex 64), (facetIndex 65), (facetIndex 66), (facetIndex 67)]))
 (.branch 9
 (.leaf ([(facetIndex 87), (facetIndex 88), (facetIndex 95), (facetIndex 101)]))
 (.leaf ([(facetIndex 70), (facetIndex 71), (facetIndex 89), (facetIndex 90)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "68666658555599885344444322222339923777771111111111z35;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 10
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def grouped2_0000 : List Nat := [0, 1]
def grouped2_0001 : List Nat := [0, 1, 2, 3, 4]
def grouped2_0003 : List Nat := [2]
def grouped2_0004 : List Nat := [2, 3, 4]
def grouped2_0005 : List Nat := [3]
def grouped2_0006 : List Nat := [3, 4]
def grouped2_0007 : List Nat := [4]
def grouped2_0008 : List Nat := [5]
def grouped2_0009 : List Nat := [5, 6]
def grouped2_0010 : List Nat := [5, 6, 7, 8, 9]
def grouped2_0011 : List Nat := [6]
def grouped2_0012 : List Nat := [7]
def grouped2_0013 : List Nat := [7, 8, 9]
def grouped2_0014 : List Nat := [8]
def grouped2_0015 : List Nat := [8, 9]
def grouped2_0016 : List Nat := [9]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00036.record009 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00036.record009_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00036.record009" "{\"atoms\":[{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":102},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":9},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0015\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":10,\"list_name\":\"groupKind2\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00036.record009" 76

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00036.record009" "{\"ridges\":[[4,262],[10,266],[11,522],[20,292],[23,73],[25,296],[26,552],[30,290],[33,74],[35,290],[41,266],[42,522],[43,262],[48,262],[50,262],[53,266],[54,522],[58,266],[59,522],[60,266],[61,522],[68,290],[70,73],[72,296],[73,552],[76,292],[80,56],[80,73],[81,56],[82,56],[82,296],[83,56],[83,552],[84,73],[85,296],[85,552],[86,52],[87,74],[91,52],[92,52],[93,52],[93,290],[94,52],[97,56],[97,74],[98,56],[101,74]],\"owners\":[[4,262,[30,89,93,96],[41,43,48,50,52]],[43,262,[30,89,96],[4,41,48,50,52,93]],[48,262,[30,89,93,96],[4,41,43,50,52]],[50,262,[30,89,93,96],[4,41,43,48,52]],[23,73,[8,39,55,57,58,59],[70,80,84]],[70,73,[8,55,57,58,59],[23,39,80,84]],[80,73,[8,39,57,58,59],[23,55,70,84]],[84,73,[8,39,55,58,59],[23,57,70,80]],[33,74,[8,39,55,57,58,59],[87,97,101]],[87,74,[8,55,57,58,59],[33,39,97,101]],[97,74,[8,39,57,58,59],[33,55,87,101]],[101,74,[8,39,55,58,59],[33,57,87,97]],[10,266,[35,89,99,102],[41,53,58,60,62]],[41,266,[35,99,102],[10,53,58,60,62,89]],[53,266,[35,89,102],[10,41,58,60,62,99]],[58,266,[35,89,99,102],[10,41,53,60,62]],[60,266,[35,89,99,102],[10,41,53,58,62]],[11,522,[36,90,100,102],[42,54,59,61,62]],[42,522,[36,100,102],[11,54,59,61,62,90]],[54,522,[36,90,102],[11,42,59,61,62,100]],[59,522,[36,90,100,102],[11,42,54,61,62]],[61,522,[36,90,100,102],[11,42,54,59,62]],[86,52,[17,74,75,76,77],[27,69,91,92,93,94]],[91,52,[17,69,75,76,77],[27,74,86,92,93,94]],[92,52,[17,69,74,76,77],[27,75,86,91,93,94]],[93,52,[17,69,74,75,77],[27,76,86,91,92,94]],[94,52,[17,69,74,75,76],[27,77,86,91,92,93]],[20,292,[30,89,93,96],[72,76,79]],[76,292,[30,89,96],[20,72,79,93]],[80,56,[32,86,98,99,100],[22,69,81,82,83,97]],[81,56,[32,86,97,99,100],[22,69,80,82,83,98]],[82,56,[32,86,97,98,100],[22,69,80,81,83,99]],[83,56,[32,86,97,98,99],[22,69,80,81,82,100]],[97,56,[22,69,81,82,83],[32,80,86,98,99,100]],[98,56,[22,69,80,82,83],[32,81,86,97,99,100]],[25,296,[35,89,99,102],[72,82,85]],[72,296,[35,99,102],[25,82,85,89]],[82,296,[35,89,102],[25,72,85,99]],[85,296,[35,89,99],[25,72,82,102]],[26,552,[36,90,100,102],[73,83,85]],[73,552,[36,100,102],[26,83,85,90]],[83,552,[36,90,102],[26,73,85,100]],[85,552,[36,90,100],[26,73,83,102]]],\"edges\":[[22,[4,20,30,41,43,48,50,52,72,76,79,89,93,96]],[26,[8,23,33,39,55,57,58,59,70,80,84,87,97,101]],[28,[10,25,35,41,53,58,60,62,72,82,85,89,99,102]],[29,[11,26,36,42,54,59,61,62,73,83,85,90,100,102]]],\"groupings\":[2]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00036.record009" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00036.record009\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-31,-2],[-31,-16],[-31,-25],[-31,-26],[-31,-27],[-31,-28],[-32,-17],[-32,-22],[-36,-34],[-36,-35],[-37,-34],[-37,-35],[-42,-5],[-42,-33],[-42,-38],[-42,-39],[-42,-40],[-42,-41],[-47,-34],[-47,-35],[-48,-7],[-48,-33],[-48,-43],[-48,-44],[-48,-45],[-48,-46],[-51,-14],[-51,-32],[-51,-33],[-51,-37],[-51,-49],[-52,-36],[-52,-37],[-55,-51],[-56,-51],[-57,-32],[-57,-42],[-57,-51],[-58,-12],[-59,-12],[-60,-12],[-60,-15],[-60,-52],[-61,-12],[-61,-14],[-61,-51],[-61,-60],[-63,-12],[-63,-49],[-63,-51],[-63,-52],[-63,-58],[-63,-59],[-63,-60],[-63,-61],[-1,11,51,55,57],[-19,11,51,57],[-20,11,51,55,57],[-21,11,51,55,57],[-8,2,16,25,26,27,28],[-34,2,25,26,27,28],[-43,2,16,26,27,28],[-47,2,16,25,27,28],[-13,2,16,25,26,27,28],[-50,2,25,26,27,28],[-58,2,16,26,27,28],[-62,2,16,25,27,28],[-3,14,51,60,63],[-17,14,60,63],[-23,14,51,63],[-27,14,51,60,63],[-29,14,51,60,63],[-4,15,52,61,63],[-18,15,61,63],[-24,15,52,63],[-28,15,52,61,63],[-30,15,52,61,63],[-11,-14,-32],[-14,-32,-55],[-49,5,38,39,40,41],[-53,5,33,39,40,41],[-54,5,33,38,40,41],[-55,5,33,38,39,41],[-56,5,33,38,39,40],[-6,11,51,55,57],[-40,11,51,57],[-43,12,49,59,60,61],[-44,12,49,58,60,61],[-45,12,49,58,59,61],[-46,12,49,58,59,60],[-58,7,33,44,45,46],[-59,7,33,43,45,46],[-9,14,51,60,63],[-36,14,60,63],[-45,14,51,63],[-48,14,51,60],[-10,15,52,61,63],[-37,15,61,63],[-46,15,52,63],[-48,15,52,61],[-64,32,36,37,42,48],[-65,43,44,45,46,47],[-66,49,53,54,55,56,57],[-67,58,59,60,61,63],[-68,34,35,51,52],[-69,64],[-69,65],[-70,69],[-71,70],[-72,66],[-72,67],[-73,68],[-74,73],[-75,72],[-75,74],[-76,71],[-76,75],[76],[1,6,11,17,19,20,21,22,36,40,42,51,55,57],[2,8,13,16,25,26,27,28,34,43,47,50,58,62],[3,9,14,17,23,27,29,31,36,45,48,51,60,63],[4,10,15,18,24,28,30,31,37,46,48,52,61,63]],\"atoms\":[{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":102},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":9,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2}],\"rules\":[{\"tag\":\"incompatible\",\"a\":62,\"b\":8},{\"tag\":\"incompatible\",\"a\":62,\"b\":39},{\"tag\":\"incompatible\",\"a\":62,\"b\":55},{\"tag\":\"incompatible\",\"a\":62,\"b\":57},{\"tag\":\"incompatible\",\"a\":62,\"b\":58},{\"tag\":\"incompatible\",\"a\":62,\"b\":59},{\"tag\":\"incompatible\",\"a\":68,\"b\":41},{\"tag\":\"incompatible\",\"a\":68,\"b\":52},{\"tag\":\"incompatible\",\"a\":72,\"b\":70},{\"tag\":\"incompatible\",\"a\":72,\"b\":71},{\"tag\":\"incompatible\",\"a\":73,\"b\":70},{\"tag\":\"incompatible\",\"a\":73,\"b\":71},{\"tag\":\"incompatible\",\"a\":79,\"b\":17},{\"tag\":\"incompatible\",\"a\":79,\"b\":69},{\"tag\":\"incompatible\",\"a\":79,\"b\":74},{\"tag\":\"incompatible\",\"a\":79,\"b\":75},{\"tag\":\"incompatible\",\"a\":79,\"b\":76},{\"tag\":\"incompatible\",\"a\":79,\"b\":77},{\"tag\":\"incompatible\",\"a\":84,\"b\":70},{\"tag\":\"incompatible\",\"a\":84,\"b\":71},{\"tag\":\"incompatible\",\"a\":85,\"b\":22},{\"tag\":\"incompatible\",\"a\":85,\"b\":69},{\"tag\":\"incompatible\",\"a\":85,\"b\":80},{\"tag\":\"incompatible\",\"a\":85,\"b\":81},{\"tag\":\"incompatible\",\"a\":85,\"b\":82},{\"tag\":\"incompatible\",\"a\":85,\"b\":83},{\"tag\":\"incompatible\",\"a\":89,\"b\":35},{\"tag\":\"incompatible\",\"a\":89,\"b\":68},{\"tag\":\"incompatible\",\"a\":89,\"b\":69},{\"tag\":\"incompatible\",\"a\":89,\"b\":73},{\"tag\":\"incompatible\",\"a\":89,\"b\":86},{\"tag\":\"incompatible\",\"a\":90,\"b\":72},{\"tag\":\"incompatible\",\"a\":90,\"b\":73},{\"tag\":\"incompatible\",\"a\":93,\"b\":89},{\"tag\":\"incompatible\",\"a\":94,\"b\":89},{\"tag\":\"incompatible\",\"a\":96,\"b\":68},{\"tag\":\"incompatible\",\"a\":96,\"b\":79},{\"tag\":\"incompatible\",\"a\":96,\"b\":89},{\"tag\":\"incompatible\",\"a\":97,\"b\":32},{\"tag\":\"incompatible\",\"a\":98,\"b\":32},{\"tag\":\"incompatible\",\"a\":99,\"b\":32},{\"tag\":\"incompatible\",\"a\":99,\"b\":36},{\"tag\":\"incompatible\",\"a\":99,\"b\":90},{\"tag\":\"incompatible\",\"a\":100,\"b\":32},{\"tag\":\"incompatible\",\"a\":100,\"b\":35},{\"tag\":\"incompatible\",\"a\":100,\"b\":89},{\"tag\":\"incompatible\",\"a\":100,\"b\":99},{\"tag\":\"incompatible\",\"a\":102,\"b\":32},{\"tag\":\"incompatible\",\"a\":102,\"b\":86},{\"tag\":\"incompatible\",\"a\":102,\"b\":89},{\"tag\":\"incompatible\",\"a\":102,\"b\":90},{\"tag\":\"incompatible\",\"a\":102,\"b\":97},{\"tag\":\"incompatible\",\"a\":102,\"b\":98},{\"tag\":\"incompatible\",\"a\":102,\"b\":99},{\"tag\":\"incompatible\",\"a\":102,\"b\":100},{\"tag\":\"mate\",\"ridge\":262,\"a\":4,\"owners\":[30,89,93,96]},{\"tag\":\"mate\",\"ridge\":262,\"a\":43,\"owners\":[30,89,96]},{\"tag\":\"mate\",\"ridge\":262,\"a\":48,\"owners\":[30,89,93,96]},{\"tag\":\"mate\",\"ridge\":262,\"a\":50,\"owners\":[30,89,93,96]},{\"tag\":\"mate\",\"ridge\":73,\"a\":23,\"owners\":[8,39,55,57,58,59]},{\"tag\":\"mate\",\"ridge\":73,\"a\":70,\"owners\":[8,55,57,58,59]},{\"tag\":\"mate\",\"ridge\":73,\"a\":80,\"owners\":[8,39,57,58,59]},{\"tag\":\"mate\",\"ridge\":73,\"a\":84,\"owners\":[8,39,55,58,59]},{\"tag\":\"mate\",\"ridge\":74,\"a\":33,\"owners\":[8,39,55,57,58,59]},{\"tag\":\"mate\",\"ridge\":74,\"a\":87,\"owners\":[8,55,57,58,59]},{\"tag\":\"mate\",\"ridge\":74,\"a\":97,\"owners\":[8,39,57,58,59]},{\"tag\":\"mate\",\"ridge\":74,\"a\":101,\"owners\":[8,39,55,58,59]},{\"tag\":\"mate\",\"ridge\":266,\"a\":10,\"owners\":[35,89,99,102]},{\"tag\":\"mate\",\"ridge\":266,\"a\":41,\"owners\":[35,99,102]},{\"tag\":\"mate\",\"ridge\":266,\"a\":53,\"owners\":[35,89,102]},{\"tag\":\"mate\",\"ridge\":266,\"a\":58,\"owners\":[35,89,99,102]},{\"tag\":\"mate\",\"ridge\":266,\"a\":60,\"owners\":[35,89,99,102]},{\"tag\":\"mate\",\"ridge\":522,\"a\":11,\"owners\":[36,90,100,102]},{\"tag\":\"mate\",\"ridge\":522,\"a\":42,\"owners\":[36,100,102]},{\"tag\":\"mate\",\"ridge\":522,\"a\":54,\"owners\":[36,90,102]},{\"tag\":\"mate\",\"ridge\":522,\"a\":59,\"owners\":[36,90,100,102]},{\"tag\":\"mate\",\"ridge\":522,\"a\":61,\"owners\":[36,90,100,102]},{\"tag\":\"three\",\"ridge\":290,\"vertices\":[30,35,68]},{\"tag\":\"three\",\"ridge\":290,\"vertices\":[35,68,93]},{\"tag\":\"mate\",\"ridge\":52,\"a\":86,\"owners\":[17,74,75,76,77]},{\"tag\":\"mate\",\"ridge\":52,\"a\":91,\"owners\":[17,69,75,76,77]},{\"tag\":\"mate\",\"ridge\":52,\"a\":92,\"owners\":[17,69,74,76,77]},{\"tag\":\"mate\",\"ridge\":52,\"a\":93,\"owners\":[17,69,74,75,77]},{\"tag\":\"mate\",\"ridge\":52,\"a\":94,\"owners\":[17,69,74,75,76]},{\"tag\":\"mate\",\"ridge\":292,\"a\":20,\"owners\":[30,89,93,96]},{\"tag\":\"mate\",\"ridge\":292,\"a\":76,\"owners\":[30,89,96]},{\"tag\":\"mate\",\"ridge\":56,\"a\":80,\"owners\":[32,86,98,99,100]},{\"tag\":\"mate\",\"ridge\":56,\"a\":81,\"owners\":[32,86,97,99,100]},{\"tag\":\"mate\",\"ridge\":56,\"a\":82,\"owners\":[32,86,97,98,100]},{\"tag\":\"mate\",\"ridge\":56,\"a\":83,\"owners\":[32,86,97,98,99]},{\"tag\":\"mate\",\"ridge\":56,\"a\":97,\"owners\":[22,69,81,82,83]},{\"tag\":\"mate\",\"ridge\":56,\"a\":98,\"owners\":[22,69,80,82,83]},{\"tag\":\"mate\",\"ridge\":296,\"a\":25,\"owners\":[35,89,99,102]},{\"tag\":\"mate\",\"ridge\":296,\"a\":72,\"owners\":[35,99,102]},{\"tag\":\"mate\",\"ridge\":296,\"a\":82,\"owners\":[35,89,102]},{\"tag\":\"mate\",\"ridge\":296,\"a\":85,\"owners\":[35,89,99]},{\"tag\":\"mate\",\"ridge\":552,\"a\":26,\"owners\":[36,90,100,102]},{\"tag\":\"mate\",\"ridge\":552,\"a\":73,\"owners\":[36,100,102]},{\"tag\":\"mate\",\"ridge\":552,\"a\":83,\"owners\":[36,90,102]},{\"tag\":\"mate\",\"ridge\":552,\"a\":85,\"owners\":[36,90,100]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[68,72,73,79,85],\"full_literals\":[-64,32,36,37,42,48]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[80,81,82,83,84],\"full_literals\":[-65,43,44,45,46,47]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[86,91,92,93,94,96],\"full_literals\":[-66,49,53,54,55,56,57]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[97,98,99,100,102],\"full_literals\":[-67,58,59,60,61,63]},{\"tag\":\"group_or\",\"kind\":2,\"index\":9,\"members\":[70,71,89,90],\"full_literals\":[-68,34,35,51,52]},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-69,64,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-69,false,65],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0004\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-70,false,69],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-71,false,70],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-72,66,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-72,false,67],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped2_0014\",\"right_name\":\"grouped2_0016\",\"joined_name\":\"grouped2_0015\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-73,false,68],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0013\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-74,false,73],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":1,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-75,72,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-75,false,74],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":5,\"direction\":\"backward\",\"full_literals\":[-76,71,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":5,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-76,false,75],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":10,\"grouped\":true},{\"tag\":\"edge\",\"edge\":22,\"owners\":[4,20,30,41,43,48,50,52,72,76,79,89,93,96]},{\"tag\":\"edge\",\"edge\":26,\"owners\":[8,23,33,39,55,57,58,59,70,80,84,87,97,101]},{\"tag\":\"edge\",\"edge\":28,\"owners\":[10,25,35,41,53,58,60,62,72,82,85,89,99,102]},{\"tag\":\"edge\",\"edge\":29,\"owners\":[11,26,36,42,54,59,61,62,73,83,85,90,100,102]}]}"
  "123 71 0 118 116 0\n124 75 0 118 117 0\n125 70 0 123 109 0\n126 72 0 124 114 0\n127 74 0 124 115 0\n128 69 0 125 108 0\n129 66 0 126 110 0\n130 67 0 126 111 0\n131 73 0 127 113 0\n132 64 0 128 106 0\n133 65 0 128 107 0\n134 68 0 131 112 0\n135 -12 0 130 39 40 41 44 48 104 0\n136 -63 0 135 133 134 49 50 51 52 53 54 55 87 88 89 90 102 19 20 105 0\n137 51 14 31 48 60 0 136 94 69 70 71 72 95 68 93 121 0\n138 14 31 48 60 0 136 132 129 94 137 28 29 30 31 34 35 38 101 13 15 16 17 18 82 81 103 0\n139 -42 49 41 0 129 13 14 15 16 17 37 83 84 82 81 103 0\n140 42 37 36 -14 48 0 132 27 101 7 8 36 79 78 56 85 57 86 58 59 119 0\n141 41 -42 0 17 16 15 13 139 80 0\n142 -42 0 141 18 0\n143 -37 51 0 134 11 12 33 105 0\n144 -14 48 0 142 134 27 143 140 9 10 32 105 0\n145 -31 0 1 2 3 4 5 6 62 61 60 67 66 65 63 64 120 0\n146 48 60 0 145 144 138 0\n147 60 61 0 136 130 146 21 22 23 24 25 26 92 91 104 0\n148 15 61 52 0 145 136 73 74 75 76 77 97 98 99 100 122 0\n149 61 0 147 42 43 148 0\n150 -14 0 149 45 0\n151 -51 0 149 46 0\n152 -60 0 149 47 0\n153 -48 0 151 150 152 96 0\n154 0 153 152 146 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00036.record009.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00036.record009.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00036.record009.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00036.record009.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00036.record009 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00036.record009.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00036.record009.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00036.record009.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00036.record009.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00036.record009 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00036.record009_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00036.record009_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00036.record009_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00036.record009_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00036.record009_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00036.record009_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00036.record009_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00036.record009 Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00036.record009_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00036.record009_validity Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00036.record009_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00036.record009
