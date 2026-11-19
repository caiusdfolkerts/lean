module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow24Part00166Data
public import GraphInputsRow24Part00166Frames
public import GraphInputsRow24Part00166Leaves
public import GraphInputsRow24Part00166Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

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
#print axioms local_excluded
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
#print axioms local_excluded
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
#print axioms local_excluded
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
#print axioms local_excluded
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
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00166.record023
