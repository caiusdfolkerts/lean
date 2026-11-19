module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow24Part00121Data
public import GraphInputsRow24Part00121Frames
public import GraphInputsRow24Part00121Leaves
public import GraphInputsRow24Part00121Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00121.record018
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record018
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨48, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨75, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [7036874820419584, (certNat% 2), 3791650816, 446743707648, 2314867800654479360, (certNat% 3)]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record018_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record018_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record018_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record018_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record018_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record018_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record018_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record018_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record018_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00121.record018

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00121.record023
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record023
def vertexColumn : Fields := ⟨10, (certNat% 4)⟩
def kindColumn : Fields := ⟨3, (certNat% 5)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨77, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [3945064900329472, 1044835117844922368, (certNat% 6), 387620798464, 186919124205568, (certNat% 7), (certNat% 8)]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record023_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record023_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record023_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record023_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record023_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record023_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record023_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record023_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record023_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00121.record023

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00121.record025
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record025
def vertexColumn : Fields := ⟨10, (certNat% 9)⟩
def kindColumn : Fields := ⟨3, (certNat% 10)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨58, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨78, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 11), (certNat% 12), 4611690417820270592, 622904475648, 62822285312, 412434300928]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record025_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record025_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record025_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record025_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record025_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record025_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record025_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record025_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record025_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00121.record025

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00121.record026
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record026
def vertexColumn : Fields := ⟨10, (certNat% 13)⟩
def kindColumn : Fields := ⟨3, (certNat% 14)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨30, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨63, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨75, by decide⟩, ⟨78, by decide⟩, ⟨80, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 15), 10133099295801344, (certNat% 16), 7696581394432, 36028797086072832, (certNat% 17)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [64183997172809728, (certNat% 16), (certNat% 17), 266287972352, (certNat% 18), (certNat% 19)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 20), (certNat% 21), (certNat% 22), (certNat% 23), 2251799813685248]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 24), (certNat% 25), (certNat% 26), 4398046511104, 63050394783186944]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 27), 10133099295801344, (certNat% 26), 4402345672704, 54043195528445952, (certNat% 28)]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨24, by decide⟩ c5 c2
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 29), 9241387534875885568, 163208757248, (certNat% 19), (certNat% 30)]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 31), 63050394850295808, (certNat% 32), 4535485464576, 34359738368, (certNat% 33)]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨24, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 34), 10133099312578560, 9241387534875885568, 36591747043688448, (certNat% 35), (certNat% 36), 4540854173696]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨67, by decide⟩ c10 c9
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c11 c6
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c12 c1
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨23, by decide⟩ c13 c0
  c14
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record026_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record026_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record026_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record026_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record026_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record026_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record026_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record026_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record026_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00121.record026

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00121.record027
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record027
def vertexColumn : Fields := ⟨10, (certNat% 37)⟩
def kindColumn : Fields := ⟨3, (certNat% 38)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨33, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨56, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 39), (certNat% 40), 61572919590912, 2380152404139048960, 1152921505277935616, (certNat% 41)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 42), 1152921505143717888, (certNat% 43), 26388279066624]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 44), (certNat% 45), 18279380811776, 8797166764032, (certNat% 46)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 47), 2017612633061982208, 18279380811776, (certNat% 40)]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 48), (certNat% 43), (certNat% 49), 288256764430778368, 1152921505143717888]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 50), 1224979099315863552, (certNat% 51), 864699924548157440, (certNat% 52), (certNat% 53)]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c7 c4
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨69, by decide⟩ c8 c3
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 54), 61572651155456, 1801439851485069312, (certNat% 55), 2308094810101121024, (certNat% 56)]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 57), 864699924548157440, (certNat% 58), (certNat% 59), 1125908496777216]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 60), 1657857376256, 288256764430778368, (certNat% 61), 1125899906842624]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 62), 2882303761517117440, (certNat% 45), 288256764430778368, (certNat% 63)]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 64), 1726576852992, 864699924548157440, (certNat% 65), (certNat% 66), (certNat% 67)]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨66, by decide⟩ c14 c13
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨70, by decide⟩ c15 c12
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c16 c11
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 68), 1154047404547244032, (certNat% 61), 1717986918400, (certNat% 69)]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 70), 1224979098644774912, (certNat% 56), (certNat% 71), 1125899906842624]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [6708173537527463936, 1855425871872, (certNat% 72), (certNat% 71), 10133099161583616, (certNat% 73)]
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨52, by decide⟩ c20 c19
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c21 c18
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 74), 15762599769538560, (certNat% 71), 1513209475333357568, 52785416503296, 1125899906842624]
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 75), 1649267441664, (certNat% 76), 52776826568704, (certNat% 77)]
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 78), 52776826568704, 2380152404139048960, 1855425871872, (certNat% 41), (certNat% 79)]
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨52, by decide⟩ c25 c24
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 80), 1855425871872, (certNat% 81), (certNat% 82), 15762599769538560, (certNat% 8)]
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 83), 36292473651200, 2089670227636781056, (certNat% 84), (certNat% 85), (certNat% 86), 15762599769538560]
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c28 c27
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c29 c26
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨70, by decide⟩ c30 c23
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c31 c22
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c32 c17
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c33 c10
  let c35 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c34 c9
  let c36 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c35 c0
  c36
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record027_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record027_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record027_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record027_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record027_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record027_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record027_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record027_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record027_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00121.record027
