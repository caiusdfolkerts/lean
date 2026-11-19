module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow19Part00034Data
public import GraphInputsRow19Part00034Frames
public import GraphInputsRow19Part00034Leaves
public import GraphInputsRow19Part00034Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00034.record020
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record020
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨18, by decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨29, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨44, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨57, by decide⟩, ⟨66, by decide⟩, ⟨72, by decide⟩, ⟨77, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), (certNat% 3), (certNat% 4), 8444249301319680, 637534208]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [148830869540044800, (certNat% 3), 3377699725770752, (certNat% 4), (certNat% 5)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 6), 580610875719680, 962072936448, (certNat% 7), (certNat% 8)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [148830869544239104, (certNat% 3), 3940649674997760, (certNat% 9), 134217728]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [1078045966336, (certNat% 10), 148829893935759360, (certNat% 11), 771751936, 3377699724722176]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨18, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨23, by decide⟩ c5 c2
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨19, by decide⟩ c6 c1
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c7 c0
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c8 c0
  c9
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record020_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record020_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record020_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record020_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record020_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record020_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record020_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record020_validity Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record020_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00034.record020

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00034.record048
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record048
def vertexColumn : Fields := ⟨10, (certNat% 12)⟩
def kindColumn : Fields := ⟨3, (certNat% 13)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2, 3]
def candidates : List (Fin raw.n) := [⟨16, by decide⟩, ⟨17, by decide⟩, ⟨18, by decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 14), 35184405643264, 2251799813685248]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .size 3
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨78, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 15), (certNat% 16), 35184405643264, 1155173304420532224]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 17), (certNat% 18), 1152956688978935808, 79164904308736, 72058143793741824]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨76, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 19), (certNat% 20), (certNat% 21), 105553116266496]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 22), 105553116266496, (certNat% 23), (certNat% 21)]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 24), 571473920, 11258999068426240, (certNat% 20)]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 25), (certNat% 26), 603979776, 11258999069474816, 35218765381632]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨69, by decide⟩ c10 c9
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c11 c8
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c12 c7
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 27), 2251799847239680, (certNat% 28), 9570149208162304]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 29), (certNat% 30), 9570149208162304, 1152956723338674176, 2251799848288256]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c15 c14
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 31), 11258999068426240, 33554432, 1152921504606846976]
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨78, by decide⟩ c1 c17
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 32), 1152956688978935808, 11258999068426240, 704643072]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 33), 9570149208162304, 1155173304420532224, (certNat% 18), 973078528]
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c20 c19
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨23, by decide⟩ c21 c18
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 34), 11258999069474816, (certNat% 35), 35184405643264, 1152921504606846976]
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 36), 11258999069474816, 105561706201088, 34393292800, 1152921504606846976]
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 37), (certNat% 38), 939524096, (certNat% 39), (certNat% 16)]
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 40), (certNat% 41), 974127104, (certNat% 42), 9570149208162304, (certNat% 43)]
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c26 c25
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨23, by decide⟩ c27 c24
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨24, by decide⟩ c28 c23
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨71, by decide⟩ c29 c22
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c30 c16
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c31 c13
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨19, by decide⟩ c32 c6
  c33
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record048_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record048_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record048_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record048_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record048_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record048_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record048_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record048_validity Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record048_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00034.record048
