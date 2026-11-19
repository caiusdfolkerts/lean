module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow26Part00061Data
public import GraphInputsRow26Part00061Frames
public import GraphInputsRow26Part00061Leaves
public import GraphInputsRow26Part00061Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00061.record008
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00061.record008
def vertexColumn : Fields := ⟨10, hexnat% "ce2b49b23c789b25c9aa5aa3a4e8e68d8b61da2e2b86e8783e78731ac5b15c7296a6695a7198e53971695655556364d5361d475c368d6338d9354e334ccb31cd8b52e2b4acab1ae1b46c3b31e1715e0f23c1f6c1682c86a2584e64549854958344d24c4b21c4705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "6db69b4db69b69b6da6db4db6936926db69b69b4db4db492489249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨18, by decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨27, by decide⟩, ⟨31, by decide⟩, ⟨34, by decide⟩, ⟨38, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨55, by decide⟩, ⟨60, by decide⟩, ⟨66, by decide⟩, ⟨70, by decide⟩, ⟨75, by decide⟩, ⟨78, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "48440080604488000000", 1153484454560268288, 1143492097343488, 12058624]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "48441082004488000000", 105553117315072, 1143492097343488, 11010048]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "48440080004488000000", 1153484454560268288, 105553117315072, 15466496, 1143492092887040]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8440000000480000000", 36063981525270528, hexnat% "40001000004000000000", 16515072, 87960930222080, 1688849860263936]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨75, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c4 c1
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
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00061.record008_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00061.record008_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00061.record008_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00061.record008_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00061.record008_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00061.record008_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00061.record008_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00061.record008_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00061.record008_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00061.record008

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00061.record021
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00061.record021
def vertexColumn : Fields := ⟨10, hexnat% "ce178ad1ac5b1d26c9726a96a56a3a4e87a35a362d8768b8ae1b9d1cc6b16c7296a719965598e539716a569695954d58d4b56364d5362d4b4ad70da364d5334e334ccb362d4b8ad2b2ae1b46c5b0ecc789ca785c9715c3783c8f0bdb08b0b22984e0b991545498344d24c5312c8711c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "1b6db4db6db6d34926d36da6db6db6da49b6d24da69b6da69a693491249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨17, by decide⟩, ⟨18, by decide⟩, ⟨19, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩, ⟨24, by decide⟩, ⟨26, by decide⟩, ⟨28, by decide⟩, ⟨34, by decide⟩, ⟨36, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨60, by decide⟩, ⟨65, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨73, by decide⟩, ⟨83, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2e200004010054e0000", 422229644935168, hexnat% "800000000030000000000", 550026346496, hexnat% "101000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "800101001838411280000", hexnat% "20000401000020000", hexnat% "2000000000000400000", 67371008, hexnat% "e00000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "e000014100056e0000", hexnat% "802000000001000000000", 1153062259543506944, hexnat% "100000028000000000", hexnat% "20000000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [1153063359072174080, hexnat% "e00000000000020000", 351843721412608, hexnat% "120000020000000000", hexnat% "802000000001000000000", 549829214208]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨18, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c4 c1
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨24, by decide⟩ c5 c0
  c6
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00061.record021_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00061.record021_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00061.record021_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00061.record021_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00061.record021_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00061.record021_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00061.record021_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00061.record021_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00061.record021_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00061.record021

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00061.record032
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00061.record032
def vertexColumn : Fields := ⟨10, hexnat% "7c2b89e0f8791d46d1743d1cc3b1b25ca3a2e87a69966659564d8b61d98e53a2e2b86e746b19c4f1726a99a4e9a6659366392e479714e565555354b51d58d534cd8b4ad1b71364d538ccb31cd8b52e2b2ac6b86c9b16c3b61d4789ca719d1725c570de0f43c8f13c2f2b06c8ca2a0b991545855148d1361344e0b41c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "6db6db6d369b6db6db6924db6db6db6d349b6926924936da6d36d26da6da492249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨16, by decide⟩, ⟨17, by decide⟩, ⟨18, by decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩, ⟨24, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨33, by decide⟩, ⟨36, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨57, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨86, by decide⟩, ⟨89, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4000000000021200000000", hexnat% "8000001c0001000000", hexnat% "4000000000000110000", 198158384409608192, hexnat% "20003000000600000000000", 1970324837892096]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00061.record032_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00061.record032_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00061.record032_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00061.record032_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00061.record032_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00061.record032_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00061.record032_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00061.record032_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00061.record032_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00061.record032
