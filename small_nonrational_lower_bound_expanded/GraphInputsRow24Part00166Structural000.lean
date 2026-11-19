module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow24Part00166Data
public import GraphInputsRow24Part00166Frames
public import GraphInputsRow24Part00166Leaves
public import GraphInputsRow24Part00166Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00166.record010
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record010
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨30, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨65, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨75, by decide⟩, ⟨77, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), 47287796355825664, 4611703748052385792, (certNat% 3), 1945555039024054272, (certNat% 4)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 5), (certNat% 6), 38280597101084672, 687328985088]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 7), 56294995610566656, (certNat% 8), (certNat% 9), 653036355584, 17592186044416]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 10), 1740641255978696704, 4611703748052385792, (certNat% 3), (certNat% 11)]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 12), 8797166764032, 9224498074200571904, (certNat% 13), 584551759872, 623748548390813696]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 14), 790273982464, (certNat% 15), 43990128787456, 17592186044416]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 16), 790273982464, (certNat% 17), (certNat% 18), 46180562108416, (certNat% 19)]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨71, by decide⟩ c7 c6
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 20), 721990713344, 1740641255978696704, 28657095540736, (certNat% 3), (certNat% 21), (certNat% 22)]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c10 c5
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c11 c4
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c12 c3
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c13 c0
  c14
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record010_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record010_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record010_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record010_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record010_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record010_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record010_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record010_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record010_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00166.record010

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00166.record018
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record018
def vertexColumn : Fields := ⟨10, (certNat% 23)⟩
def kindColumn : Fields := ⟨3, (certNat% 24)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨21, by decide⟩, ⟨25, by decide⟩, ⟨31, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨44, by decide⟩, ⟨50, by decide⟩, ⟨53, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨65, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨73, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨82, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨90, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 25), 8646911284553449472, (certNat% 26), (certNat% 27), (certNat% 28), 10151105845526528]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record018_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record018_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record018_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record018_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record018_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record018_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record018_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record018_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record018_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00166.record018

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00166.record020
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record020
def vertexColumn : Fields := ⟨10, (certNat% 29)⟩
def kindColumn : Fields := ⟨3, (certNat% 30)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨26, by decide⟩, ⟨28, by decide⟩, ⟨30, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨35, by decide⟩, ⟨37, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨58, by decide⟩, ⟨64, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨75, by decide⟩, ⟨81, by decide⟩, ⟨88, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 31), 29273397577908224, (certNat% 32), (certNat% 33), 985162418487296]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 34), 9940500480, (certNat% 35), (certNat% 36), 1020484229529600, 9007199256838144]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨70, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 37), (certNat% 38), 18015498023206912, (certNat% 39), 9007200336871424, (certNat% 40)]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 41), (certNat% 35), (certNat% 36), 35321811042304]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 42), 985162418487296, (certNat% 43), (certNat% 32)]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [33855111216234496, (certNat% 44), (certNat% 45), (certNat% 46), 1037938976620544, (certNat% 47)]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c7 c4
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 48), 4398046511104, (certNat% 49), 11258999068426240]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 50), 297237575406452736, 12884901888, (certNat% 51), 20266198323167232]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨75, by decide⟩ c10 c9
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 52), (certNat% 32), (certNat% 53), 29273397577908224, (certNat% 54)]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 55), 4535502241792, 29273397577908224, 140746413834240, (certNat% 56), 288230376151711744]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c13 c12
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c14 c11
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 57), 288230377225453568, (certNat% 53), (certNat% 58), 8589934592]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 59), (certNat% 60), 297237576480194560, 4398065385472]
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 61), (certNat% 44), 9665773568, 5497574916096, (certNat% 39), 9007199254740992]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c18 c17
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c19 c16
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 62), 1099528404992, (certNat% 53), (certNat% 63), 8589934592]
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 64), (certNat% 53), 9665773568, (certNat% 35), (certNat% 39), 16777216]
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c22 c21
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 65), (certNat% 39), (certNat% 56), 5635013869568, 27021597766320128, 140746413834240, 288247969411497984]
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c24 c23
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c25 c20
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨70, by decide⟩ c26 c15
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨23, by decide⟩ c27 c8
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c28 c3
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c29 c2
  c30
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record020_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record020_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record020_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record020_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record020_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record020_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record020_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record020_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record020_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00166.record020

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00166.record022
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record022
def vertexColumn : Fields := ⟨10, (certNat% 66)⟩
def kindColumn : Fields := ⟨3, (certNat% 67)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨23, by decide⟩, ⟨24, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨35, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨52, by decide⟩, ⟨55, by decide⟩, ⟨57, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨75, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨82, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [1729382261272346624, (certNat% 68), (certNat% 69), (certNat% 70), (certNat% 71), (certNat% 72), (certNat% 73)]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record022_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record022_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record022_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record022_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record022_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record022_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record022_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record022_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record022_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00166.record022

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00166.record023
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record023
def vertexColumn : Fields := ⟨10, (certNat% 74)⟩
def kindColumn : Fields := ⟨3, (certNat% 75)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨23, by decide⟩, ⟨24, by decide⟩, ⟨28, by decide⟩, ⟨30, by decide⟩, ⟨34, by decide⟩, ⟨41, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨60, by decide⟩, ⟨62, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨70, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨75, by decide⟩, ⟨77, by decide⟩, ⟨79, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨87, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨92, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 76), (certNat% 77), (certNat% 78), (certNat% 79), (certNat% 80), (certNat% 81)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 82), (certNat% 83), (certNat% 84), (certNat% 85), (certNat% 86), (certNat% 87)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 88), (certNat% 89), (certNat% 90), (certNat% 91), (certNat% 92), (certNat% 81), (certNat% 87)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c3 c0
  c4
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record023_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record023_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record023_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record023_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record023_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record023_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record023_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record023_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record023_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00166.record023

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00166.record005
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "3b0dcccab26c8f2aa8eaa68da698e6658d63392e2b86e8789e17b319c5713c6693a6593656539555354cd4b4ad1b61d2745dc8ce3c4cd38cd332cc7332d2b2ac6b86c9b16cc749ca719e1725c5783d0f23c4f0bc1f3a0d43322a2a9162588e8a469454551362348e1344e0b0ad0705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "126db49b6d24d369b6da4db6926d36934d26da4936d3692492489249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record005 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record005 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record005.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record005.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record005.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 28), (facetIndex 50), (facetIndex 57), (facetIndex 58)]))
 (.leaf ([(facetIndex 38), (facetIndex 53), (facetIndex 63), (facetIndex 64)])))
 (.branch 3
 (.leaf ([(facetIndex 29), (facetIndex 70), (facetIndex 76), (facetIndex 77)]))
 (.leaf ([(facetIndex 39), (facetIndex 73), (facetIndex 82), (facetIndex 83)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 33), (facetIndex 44), (facetIndex 47), (facetIndex 49)]))
 (.leaf ([(facetIndex 56), (facetIndex 75), (facetIndex 88), (facetIndex 89)])))
 (.branch 7
 (.leaf ([(facetIndex 27), (facetIndex 30), (facetIndex 37), (facetIndex 45)]))
 (.branch 8
 (.leaf ([(facetIndex 23), (facetIndex 26), (facetIndex 40)]))
 (.leaf ([(facetIndex 22), (facetIndex 24), (facetIndex 25)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "55000033000022503002000001100000050010004040640007316000400620678878z16;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 9
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 35), (facetIndex 36), (facetIndex 52), (facetIndex 62), (facetIndex 81)]))
 (.leaf ([(facetIndex 31), (facetIndex 32), (facetIndex 55), (facetIndex 60), (facetIndex 79)])))
 (.branch 3
 (.leaf ([(facetIndex 42), (facetIndex 43), (facetIndex 66), (facetIndex 67), (facetIndex 68), (facetIndex 85), (facetIndex 86)]))
 (.branch 4
 (.leaf ([(facetIndex 51), (facetIndex 69), (facetIndex 71)]))
 (.leaf ([(facetIndex 54), (facetIndex 72), (facetIndex 74)])))))
 (.branch 7
 (.branch 6
 (.leaf ([(facetIndex 65), (facetIndex 84), (facetIndex 87)]))
 (.leaf ([(facetIndex 34), (facetIndex 59), (facetIndex 78)])))
 (.branch 8
 (.leaf ([(facetIndex 41), (facetIndex 61), (facetIndex 80)]))
 (.branch 9
 (.leaf ([(facetIndex 46)]))
 (.leaf ([(facetIndex 48)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "522500071600040430322250007160001400300908002270000006011z1f;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 10
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped2_0000 : List Nat := [0]
def grouped2_0001 : List Nat := [0, 1]
def grouped2_0002 : List Nat := [0, 1, 2, 3]
def grouped2_0004 : List Nat := [1]
def grouped2_0005 : List Nat := [2]
def grouped2_0006 : List Nat := [2, 3]
def grouped2_0007 : List Nat := [3]
def grouped2_0008 : List Nat := [4, 5, 6, 7, 8]
def grouped3_0009 : List Nat := [0]
def grouped3_0010 : List Nat := [0, 1]
def grouped3_0011 : List Nat := [0, 1, 2, 3, 4]
def grouped3_0013 : List Nat := [1]
def grouped3_0014 : List Nat := [2]
def grouped3_0015 : List Nat := [2, 3, 4]
def grouped3_0016 : List Nat := [3]
def grouped3_0017 : List Nat := [3, 4]
def grouped3_0018 : List Nat := [4]
def grouped3_0019 : List Nat := [5]
def grouped3_0020 : List Nat := [5, 6]
def grouped3_0021 : List Nat := [5, 6, 7, 8, 9]
def grouped3_0022 : List Nat := [6]
def grouped3_0023 : List Nat := [7]
def grouped3_0024 : List Nat := [7, 8, 9]
def grouped3_0025 : List Nat := [8]
def grouped3_0026 : List Nat := [8, 9]
def grouped3_0027 : List Nat := [9]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record005 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record005_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00166.record005" "{\"atoms\":[{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group\",\"kind\":3,\"index\":9},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0011\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0011\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0020\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0020\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0026\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0024\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0021\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0021\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00166.record005" 78

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00166.record005" "{\"ridges\":[[6,529],[7,290],[12,97],[21,224],[30,529],[31,102],[32,165],[33,290],[34,195],[37,529],[38,97],[39,162],[40,290],[44,290],[45,529],[45,530],[47,529],[47,530],[49,290],[52,540],[53,97],[55,300],[60,356],[62,600],[63,97],[63,224],[64,97],[66,368],[67,624],[68,816],[74,300],[79,420],[81,664],[82,162],[82,224],[85,432],[86,688],[87,816],[89,224]],\"owners\":[[6,529,[52,62,67,68],[30,37,45,47]],[30,529,[62,67,68],[6,37,45,47,52]],[37,529,[67,68],[6,30,45,47,52,62]],[45,529,[52,62],[6,30,37,47,67,68]],[47,529,[52,62,67],[6,30,37,45,68]],[45,530,[71,81],[6,30,37,47,86,87]],[47,530,[71,81,86],[6,30,37,45,87]],[7,290,[74,79,85,87],[33,40,44,49]],[33,290,[85,87],[7,40,44,49,74,79]],[40,290,[79,85,87],[7,33,44,49,74]],[44,290,[74,79],[7,33,40,49,85,87]],[49,290,[74,79,85],[7,33,40,44,87]],[12,97,[31,42,48,59,60,65,66,67],[38,53,63,64]],[38,97,[59,60,65,66,67],[12,31,42,48,53,63,64]],[53,97,[42,48,65,66,67],[12,31,38,59,60,63,64]],[63,97,[31,42,60,66,67],[12,38,48,53,59,64,65]],[64,97,[31,42,48,59,60,65,66],[12,38,53,63,67]],[39,162,[78,79,84,85,86],[17,32,43,48,73,82,83]],[82,162,[32,43,79,85,86],[17,39,48,73,78,83,84]],[21,224,[48,59,65,78,84],[63,82,89]],[63,224,[78,84],[21,48,59,65,82,89]],[82,224,[59,65],[21,48,63,78,84,89]],[89,224,[48,65,84],[21,59,63,78,82]],[31,102,[72,78],[]],[32,165,[54,59],[]],[34,195,[41,46,48],[]],[52,540,[71],[]],[55,300,[74],[]],[74,300,[55],[]],[60,356,[],[]],[62,600,[],[]],[66,368,[],[]],[67,624,[],[]],[68,816,[87],[]],[87,816,[68],[]],[79,420,[],[]],[81,664,[],[]],[85,432,[],[]],[86,688,[],[]]],\"edges\":[[34,[6,30,37,45,47,52,62,67,68,71,81,86,87]],[35,[12,21,31,38,42,48,53,59,60,63,64,65,66,67,72,78,82,84,89]],[37,[7,33,40,44,49,55,60,66,68,74,79,85,87]]],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00166.record005" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00166.record005\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-31,-26],[-39,-24],[-39,-27],[-39,-38],[-40,-39],[-44,-39],[-48,-15],[-48,-16],[-48,-32],[-48,-45],[-1,23,29,34,35],[-5,29,34,35],[-10,34,35],[-18,23,29],[-20,23,29,34],[-18,36,42],[-20,36,42,47],[-2,39,41,46,48],[-8,46,48],[-13,41,46,48],[-17,39,41],[-22,39,41,46],[-3,6,15,21,27,28,32,33,34],[-11,27,28,32,33,34],[-24,15,21,32,33,34],[-30,6,15,28,33,34],[-31,6,15,21,27,28,32,33],[-12,40,41,45,46,47],[-43,7,16,41,46,47],[-4,21,27,32,40,45],[-30,40,45],[-43,27,32],[-49,21,32,45],[-6,37,40],[-7,25,27],[-9,14,19,21],[-23,36],[-26,39],[-39,26],[-28],[-29],[-33],[-34],[-35,48],[-48,35],[-41],[-42],[-46],[-47],[-50,11,24,30,31],[-51,12,38,43,44],[-52,50],[-53,51],[-54,52,53],[-55,54],[55],[-23,56],[-35,57],[-36,58],[-25,59],[-37,59],[-39,59],[-32,60],[-45,60],[-48,60],[-61,9,27,40],[-27,61],[-40,61],[-14,62],[-19,63],[-21,64],[-56,65],[-59,66],[-58,66],[-58,-59,67],[-66,68],[-67,69],[-57,68],[-57,-66,69],[-68,70],[-69,71],[-65,70],[-72,60,61],[-61,72],[-60,72],[-60,-61,73],[-64,74],[-63,74],[-74,75],[-62,75],[-72,76],[-72,-75,77],[-73,77],[-70,-77,78],[-71,-76,78],[-78],[1,5,10,18,20,23,29,34,35,36,42,47,48],[3,4,6,11,15,21,24,27,28,30,31,32,33,34,37,40,43,45,49],[2,8,13,17,22,26,28,33,35,39,41,46,48]],\"atoms\":[{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group\",\"index\":9,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":64,\"b\":55},{\"tag\":\"incompatible\",\"a\":74,\"b\":53},{\"tag\":\"incompatible\",\"a\":74,\"b\":59},{\"tag\":\"incompatible\",\"a\":74,\"b\":73},{\"tag\":\"incompatible\",\"a\":78,\"b\":74},{\"tag\":\"incompatible\",\"a\":83,\"b\":74},{\"tag\":\"incompatible\",\"a\":87,\"b\":42},{\"tag\":\"incompatible\",\"a\":87,\"b\":43},{\"tag\":\"incompatible\",\"a\":87,\"b\":65},{\"tag\":\"incompatible\",\"a\":87,\"b\":84},{\"tag\":\"mate\",\"ridge\":529,\"a\":6,\"owners\":[52,62,67,68]},{\"tag\":\"mate\",\"ridge\":529,\"a\":30,\"owners\":[62,67,68]},{\"tag\":\"mate\",\"ridge\":529,\"a\":37,\"owners\":[67,68]},{\"tag\":\"mate\",\"ridge\":529,\"a\":45,\"owners\":[52,62]},{\"tag\":\"mate\",\"ridge\":529,\"a\":47,\"owners\":[52,62,67]},{\"tag\":\"mate\",\"ridge\":530,\"a\":45,\"owners\":[71,81]},{\"tag\":\"mate\",\"ridge\":530,\"a\":47,\"owners\":[71,81,86]},{\"tag\":\"mate\",\"ridge\":290,\"a\":7,\"owners\":[74,79,85,87]},{\"tag\":\"mate\",\"ridge\":290,\"a\":33,\"owners\":[85,87]},{\"tag\":\"mate\",\"ridge\":290,\"a\":40,\"owners\":[79,85,87]},{\"tag\":\"mate\",\"ridge\":290,\"a\":44,\"owners\":[74,79]},{\"tag\":\"mate\",\"ridge\":290,\"a\":49,\"owners\":[74,79,85]},{\"tag\":\"mate\",\"ridge\":97,\"a\":12,\"owners\":[31,42,48,59,60,65,66,67]},{\"tag\":\"mate\",\"ridge\":97,\"a\":38,\"owners\":[59,60,65,66,67]},{\"tag\":\"mate\",\"ridge\":97,\"a\":53,\"owners\":[42,48,65,66,67]},{\"tag\":\"mate\",\"ridge\":97,\"a\":63,\"owners\":[31,42,60,66,67]},{\"tag\":\"mate\",\"ridge\":97,\"a\":64,\"owners\":[31,42,48,59,60,65,66]},{\"tag\":\"mate\",\"ridge\":162,\"a\":39,\"owners\":[78,79,84,85,86]},{\"tag\":\"mate\",\"ridge\":162,\"a\":82,\"owners\":[32,43,79,85,86]},{\"tag\":\"mate\",\"ridge\":224,\"a\":21,\"owners\":[48,59,65,78,84]},{\"tag\":\"mate\",\"ridge\":224,\"a\":63,\"owners\":[78,84]},{\"tag\":\"mate\",\"ridge\":224,\"a\":82,\"owners\":[59,65]},{\"tag\":\"mate\",\"ridge\":224,\"a\":89,\"owners\":[48,65,84]},{\"tag\":\"mate\",\"ridge\":102,\"a\":31,\"owners\":[72,78]},{\"tag\":\"mate\",\"ridge\":165,\"a\":32,\"owners\":[54,59]},{\"tag\":\"mate\",\"ridge\":195,\"a\":34,\"owners\":[41,46,48]},{\"tag\":\"mate\",\"ridge\":540,\"a\":52,\"owners\":[71]},{\"tag\":\"mate\",\"ridge\":300,\"a\":55,\"owners\":[74]},{\"tag\":\"mate\",\"ridge\":300,\"a\":74,\"owners\":[55]},{\"tag\":\"mate\",\"ridge\":356,\"a\":60,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":600,\"a\":62,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":368,\"a\":66,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":624,\"a\":67,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":816,\"a\":68,\"owners\":[87]},{\"tag\":\"mate\",\"ridge\":816,\"a\":87,\"owners\":[68]},{\"tag\":\"mate\",\"ridge\":420,\"a\":79,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":664,\"a\":81,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":432,\"a\":85,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":688,\"a\":86,\"owners\":[]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[38,53,63,64],\"full_literals\":[-50,11,24,30,31]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[39,73,82,83],\"full_literals\":[-51,12,38,43,44]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-52,false,50],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-53,false,51],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-54,52,53],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":2,\"b\":5,\"direction\":\"backward\",\"full_literals\":[-55,54,false],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":52,\"full_literals\":[-23,56]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":68,\"full_literals\":[-35,57]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":71,\"full_literals\":[-36,58]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":54,\"full_literals\":[-25,59]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":72,\"full_literals\":[-37,59]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":74,\"full_literals\":[-39,59]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":65,\"full_literals\":[-32,60]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":84,\"full_literals\":[-45,60]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":87,\"full_literals\":[-48,60]},{\"tag\":\"group_or\",\"kind\":3,\"index\":6,\"members\":[34,59,78],\"full_literals\":[-61,9,27,40]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":59,\"full_literals\":[-27,61]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":78,\"full_literals\":[-40,61]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":41,\"full_literals\":[-14,62]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":46,\"full_literals\":[-19,63]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":48,\"full_literals\":[-21,64]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-56,false,65],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0017\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-59,66],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-58,false,66],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-58,-59,67],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0015\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-66,68],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0015\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-67,69],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0015\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-57,false,68],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0015\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-57,-66,69],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0011\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-68,70],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0011\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-69,71],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0011\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-65,false,70],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0020\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-72,60,61],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0020\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-61,72],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0020\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-60,false,72],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0020\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-60,-61,73],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0027\",\"joined_name\":\"grouped3_0026\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-64,74],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0027\",\"joined_name\":\"grouped3_0026\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-63,false,74],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0024\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-74,75],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0024\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-62,false,75],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0021\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-72,false,76],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0021\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-72,-75,77],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0021\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-73,false,77],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-70,-77,78],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-71,-76,78],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":34,\"owners\":[6,30,37,45,47,52,62,67,68,71,81,86,87]},{\"tag\":\"edge\",\"edge\":35,\"owners\":[12,21,31,38,42,48,53,59,60,63,64,65,66,67,72,78,82,84,89]},{\"tag\":\"edge\",\"edge\":37,\"owners\":[7,33,40,44,49,55,60,66,68,74,79,85,87]}]}"
  "100 54 0 56 55 0\n101 1 5 10 18 20 23 35 36 48 0 41 43 47 49 97 0\n102 3 4 6 11 15 21 24 27 30 31 32 37 40 43 45 49 0 40 42 43 98 0\n103 2 8 13 17 22 26 35 39 48 0 40 42 46 48 99 0\n104 70 0 43 41 80 82 76 78 72 74 58 57 59 13 12 45 11 14 15 101 0\n105 -77 0 104 96 94 0\n106 -73 0 105 93 0\n107 39 48 0 48 46 20 19 44 18 21 22 38 103 0\n108 72 0 43 42 40 49 48 46 100 84 85 67 68 63 64 65 24 32 28 31 107 2 4 6 39 51 1 53 50 54 52 0\n109 -75 0 108 105 92 0\n110 -74 0 109 89 0\n111 -62 0 109 90 0\n112 -64 0 110 87 0\n113 -63 0 110 88 0\n114 -14 0 111 69 0\n115 -21 0 112 71 0\n116 -19 0 113 70 0\n117 -9 0 116 114 115 36 0\n118 60 0 108 117 65 83 107 3 5 66 0\n119 -61 0 118 106 86 0\n120 -27 0 119 67 0\n121 -40 0 119 68 0\n122 20 48 18 10 5 23 35 36 0 41 43 101 11 0\n123 -59 69 0 49 47 43 41 77 73 75 79 59 58 16 17 37 13 12 45 122 0\n124 59 0 49 48 46 43 42 40 121 120 115 60 61 62 35 34 107 7 8 9 10 26 27 29 33 24 25 23 30 102 0\n125 76 0 108 91 0\n126 69 0 124 123 0\n127 -71 0 125 96 95 0\n128 0 126 127 81 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record005.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record005.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record005.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record005.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record005 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record005.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record005.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record005.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record005.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record005 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record005_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record005_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record005_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record005_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record005_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record005_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record005_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record005 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record005_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record005_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record005_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00166.record005
