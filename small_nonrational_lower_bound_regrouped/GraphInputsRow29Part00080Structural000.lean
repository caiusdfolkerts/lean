module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow29Part00080Data
public import GraphInputsRow29Part00080Frames
public import GraphInputsRow29Part00080Leaves
public import GraphInputsRow29Part00080Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00080.record000
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00080.record000
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨66, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨88, by decide⟩, ⟨95, by decide⟩, ⟨97, by decide⟩, ⟨98, by decide⟩, ⟨103, by decide⟩, ⟨104, by decide⟩, ⟨105, by decide⟩, ⟨110, by decide⟩, ⟨111, by decide⟩, ⟨112, by decide⟩, ⟨117, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), (certNat% 3), (certNat% 4), (certNat% 5), (certNat% 6)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 7), (certNat% 8), (certNat% 9), 4132295409664, (certNat% 10)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 11), (certNat% 8), (certNat% 9), 4132832280576, (certNat% 12)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 13), (certNat% 14), 53480245575024640, (certNat% 15), (certNat% 16), 26113401159680, (certNat% 17)]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c4 c1
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c5 c0
  c6
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00080.record000_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00080.record000_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00080.record000_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00080.record000_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00080.record000_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00080.record000_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00080.record000_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00080.record000_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00080.record000_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00080.record000

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00080.record004
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00080.record004
def vertexColumn : Fields := ⟨10, (certNat% 18)⟩
def kindColumn : Fields := ⟨3, (certNat% 19)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨40, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨46, by decide⟩, ⟨48, by decide⟩, ⟨50, by decide⟩, ⟨54, by decide⟩, ⟨57, by decide⟩, ⟨61, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 20), (certNat% 21), 2323857407723175936, 5514872225792, 35701915648, 274877906944]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 22), (certNat% 23), 19140298953195520, (certNat% 24), 1116859269120, 67108864]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 25), (certNat% 21), 5772436045824, 19210667160502272, 2305843009217888256, 1375731712]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 26), (certNat% 23), 2449958334728503296, (certNat% 24), 4419655565312]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 27), 5498631880704, (certNat% 21), 279181262848, 2324138882699886592, 144115188075855872]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 28), (certNat% 29), 1477743627730944, 144119590417334272, 46137344, 1116825714688]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 30), (certNat% 24), 5498766098432, 296361132032, 19492142137212928, 2449958334728503296, 574619648]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c7 c4
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c8 c3
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c9 c2
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c10 c1
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨24, by decide⟩ c11 c0
  c12
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00080.record004_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00080.record004_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00080.record004_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00080.record004_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00080.record004_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00080.record004_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00080.record004_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00080.record004_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00080.record004_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00080.record004

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00080.record009
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00080.record009
def vertexColumn : Fields := ⟨10, (certNat% 31)⟩
def kindColumn : Fields := ⟨3, (certNat% 32)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨55, by decide⟩, ⟨64, by decide⟩, ⟨67, by decide⟩, ⟨69, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨84, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨94, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 33), (certNat% 34), (certNat% 35), 60599304192, 138512695296, (certNat% 36)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 37), 1142796845056, (certNat% 38), (certNat% 39), (certNat% 40), 8934605717504]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 41), (certNat% 42), (certNat% 43), (certNat% 39)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 44), (certNat% 42), (certNat% 45), (certNat% 46), (certNat% 35), (certNat% 47)]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨74, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 48), (certNat% 35), (certNat% 49), (certNat% 50), 1142931062784, (certNat% 51)]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 52), (certNat% 53), (certNat% 54), (certNat% 55), 1160110931968, 8797166764032]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 56), (certNat% 34), (certNat% 57), (certNat% 58), (certNat% 40)]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 59), 43285217280, 36030997115961344, (certNat% 46), (certNat% 60), (certNat% 51)]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 61), 43218108416, (certNat% 60), (certNat% 62)]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 63), (certNat% 64), 43218108416, (certNat% 60), (certNat% 51)]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 65), (certNat% 60), (certNat% 66), (certNat% 43), (certNat% 46), (certNat% 51)]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨86, by decide⟩ c12 c11
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c13 c10
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 67), (certNat% 53), (certNat% 54), (certNat% 55), 9904261693440, 51942260736]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 68), (certNat% 69), (certNat% 39), (certNat% 55), (certNat% 70), 1160110931968, (certNat% 71)]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨86, by decide⟩ c16 c15
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c17 c14
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c18 c9
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c19 c6
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c20 c5
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c21 c4
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c22 c1
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c23 c0
  c24
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00080.record009_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00080.record009_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00080.record009_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00080.record009_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00080.record009_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00080.record009_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00080.record009_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00080.record009_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00080.record009_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00080.record009

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00080.record010
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00080.record010
def vertexColumn : Fields := ⟨10, (certNat% 72)⟩
def kindColumn : Fields := ⟨3, (certNat% 73)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨47, by decide⟩, ⟨49, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨55, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨96, by decide⟩, ⟨97, by decide⟩, ⟨101, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 74), 188743680, 328762772798046208, (certNat% 75), (certNat% 76)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 77), (certNat% 78), 457179136, 328762772798046208, (certNat% 79)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 80), (certNat% 81), (certNat% 76), (certNat% 82), 188743680, 328762772798046208]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 83), 188743680, 328762772798046208, (certNat% 75), 2147483648, (certNat% 76)]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 84), (certNat% 85), 532676608, 40532396646334464, (certNat% 86), 8070450536006025216, (certNat% 87)]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨77, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨89, by decide⟩ c5 c2
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c6 c1
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨88, by decide⟩ c7 c0
  c8
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00080.record010_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00080.record010_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00080.record010_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00080.record010_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00080.record010_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00080.record010_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00080.record010_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00080.record010_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00080.record010_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00080.record010

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00080.record011
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00080.record011
def vertexColumn : Fields := ⟨10, (certNat% 88)⟩
def kindColumn : Fields := ⟨3, (certNat% 89)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨35, by decide⟩, ⟨37, by decide⟩, ⟨40, by decide⟩, ⟨42, by decide⟩, ⟨44, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨85, by decide⟩, ⟨87, by decide⟩, ⟨96, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 90), 36028801850802176, (certNat% 91), (certNat% 92), (certNat% 93)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 94), 4503601774854144, (certNat% 91), (certNat% 92), (certNat% 93)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 95), (certNat% 96), (certNat% 91), (certNat% 97), (certNat% 93)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 98), (certNat% 91), 6442450944, 5348024557502464, (certNat% 99), 72198331526283264]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c4 c1
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c5 c0
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 100), (certNat% 101), 59109745109237760]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 102), (certNat% 103), (certNat% 104), 6755401655648256, 36028801850802176, 844424930131968]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨24, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 105), 18577349133991936, 140738864087040, (certNat% 106), (certNat% 107)]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 108), (certNat% 109), 35467034624, (certNat% 110), (certNat% 107)]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 111), (certNat% 109), 72198340116217856, (certNat% 112), (certNat% 51)]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 113), 54043199823413248, (certNat% 110), 4503601841963008, (certNat% 107), 985162418487296, 35752247296]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c13 c12
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c14 c11
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c15 c10
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨74, by decide⟩ c16 c9
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c17 c6
  c18
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00080.record011_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00080.record011_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00080.record011_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00080.record011_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00080.record011_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00080.record011_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00080.record011_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00080.record011_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00080.record011_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00080.record011
