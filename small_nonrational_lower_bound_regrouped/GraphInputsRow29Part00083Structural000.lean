module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow29Part00083Data
public import GraphInputsRow29Part00083Frames
public import GraphInputsRow29Part00083Leaves
public import GraphInputsRow29Part00083Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00083.record000
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00083.record000
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨30, by decide⟩, ⟨33, by decide⟩, ⟨39, by decide⟩, ⟨49, by decide⟩, ⟨52, by decide⟩, ⟨58, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨109, by decide⟩, ⟨111, by decide⟩, ⟨112, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), 292733975779082240, (certNat% 3), (certNat% 4), (certNat% 5), 266338304, (certNat% 6)]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00083.record000_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00083.record000_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00083.record000_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00083.record000_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00083.record000_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00083.record000_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00083.record000_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00083.record000_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00083.record000_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00083.record000

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00083.record003
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00083.record003
def vertexColumn : Fields := ⟨10, (certNat% 7)⟩
def kindColumn : Fields := ⟨3, (certNat% 8)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2, 3]
def candidates : List (Fin raw.n) := [⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩, ⟨95, by decide⟩, ⟨96, by decide⟩, ⟨97, by decide⟩, ⟨98, by decide⟩, ⟨99, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 9), 31525231751331840, (certNat% 10), (certNat% 11), (certNat% 12)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 13), (certNat% 14), (certNat% 15), (certNat% 16), (certNat% 12), (certNat% 17)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 18), (certNat% 14), (certNat% 19), (certNat% 16), (certNat% 12), (certNat% 17)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 20), (certNat% 21), (certNat% 22), (certNat% 23), (certNat% 24), (certNat% 25)]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .size 3
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 26), 9223372036854775808, (certNat% 27)]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨95, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 3 [(certNat% 28)]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 29), 71468255805440, (certNat% 27), (certNat% 30)]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨95, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨80, by decide⟩ c9 c6
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 31), (certNat% 27), (certNat% 32), (certNat% 33), (certNat% 34)]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c11 c10
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 35), (certNat% 22), 9078701870284800, (certNat% 36), 5044031582654955520, (certNat% 10)]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c13 c12
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 37), (certNat% 14), (certNat% 33), (certNat% 38), (certNat% 39), 27021632123961344]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 40), (certNat% 41), (certNat% 42), (certNat% 43), (certNat% 27)]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .size 2
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c17 c4
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c17 c18
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c17 c19
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨86, by decide⟩ c17 c20
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c17 c18
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c17 c22
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨86, by decide⟩ c17 c23
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 44), 9223372036854775808, (certNat% 45), 71468255805440]
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨76, by decide⟩ c25 c24
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨80, by decide⟩ c26 c21
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 46), 13835058055282163712, 432345566375051264, (certNat% 32), (certNat% 41)]
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨61, by decide⟩ c28 c27
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 47), (certNat% 32), (certNat% 33), (certNat% 48), (certNat% 49), 2147483648]
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨95, by decide⟩ c30 c29
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c31 c16
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 50), 9078701870284800, (certNat% 14), 8502796096475496448, (certNat% 12), (certNat% 39), (certNat% 51)]
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c33 c32
  let c35 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨94, by decide⟩ c34 c15
  let c36 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c35 c14
  let c37 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c36 c3
  let c38 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c37 c2
  let c39 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c38 c1
  let c40 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c39 c0
  let c41 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c40 c0
  c41
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00083.record003_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00083.record003_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00083.record003_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00083.record003_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00083.record003_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00083.record003_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00083.record003_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00083.record003_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00083.record003_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00083.record003
