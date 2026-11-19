module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow23Part00026Data
public import GraphInputsRow23Part00026Frames
public import GraphInputsRow23Part00026Leaves
public import GraphInputsRow23Part00026Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00026.record001
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00026.record001
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩, ⟨95, by decide⟩, ⟨96, by decide⟩, ⟨97, by decide⟩, ⟨98, by decide⟩, ⟨99, by decide⟩, ⟨100, by decide⟩, ⟨101, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), 17935233672282112, (certNat% 3), (certNat% 4), (certNat% 5), (certNat% 6), (certNat% 7), (certNat% 8), (certNat% 9)]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00026.record001_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00026.record001_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00026.record001_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00026.record001_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00026.record001_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00026.record001_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00026.record001_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00026.record001_validity Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00026.record001_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00026.record001

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00026.record003
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00026.record003
def vertexColumn : Fields := ⟨10, (certNat% 10)⟩
def kindColumn : Fields := ⟨3, (certNat% 11)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩, ⟨95, by decide⟩, ⟨96, by decide⟩, ⟨97, by decide⟩, ⟨98, by decide⟩, ⟨99, by decide⟩, ⟨100, by decide⟩, ⟨101, by decide⟩, ⟨102, by decide⟩, ⟨103, by decide⟩, ⟨104, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 12), (certNat% 13), (certNat% 14), (certNat% 15), (certNat% 16), (certNat% 17), (certNat% 18), (certNat% 19), 16607023625928704]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00026.record003_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00026.record003_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00026.record003_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00026.record003_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00026.record003_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00026.record003_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00026.record003_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00026.record003_validity Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00026.record003_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00026.record003

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00026.record011
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00026.record011
def vertexColumn : Fields := ⟨10, (certNat% 20)⟩
def kindColumn : Fields := ⟨3, (certNat% 21)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 22), 387028092977152, (certNat% 23), 10696323992911872, (certNat% 24)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 25), (certNat% 26), 395824185999360, (certNat% 27), (certNat% 28), (certNat% 29), (certNat% 30), 9024860160262144]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨78, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 31), (certNat% 32), (certNat% 33), (certNat% 34), 10151052124880896, (certNat% 35), 1152921504606846976]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 36), (certNat% 26), (certNat% 37), 432347763250823168, (certNat% 38), (certNat% 39), (certNat% 40), (certNat% 41)]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 42), (certNat% 43), 862017116176384, (certNat% 44), (certNat% 34), 9007491312517120, (certNat% 45), 1152930300699869184]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 46), 9025203757645824, 5764607525181718528, (certNat% 26), 504475726032928768]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 47), (certNat% 48), (certNat% 28), (certNat% 49), 10150983405404160, (certNat% 50), 504406456800378880, (certNat% 51)]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨65, by decide⟩ c7 c6
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 52), (certNat% 53), 504512009916645376, (certNat% 54), (certNat% 55), (certNat% 51), (certNat% 56)]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 57), (certNat% 58), (certNat% 59), (certNat% 60), 72339069014638592, 432347763250823168]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 61), 72902018968059904, 433474779849162752, (certNat% 62), (certNat% 63), (certNat% 64), 9016407664623616, 8589934592]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c11 c10
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 65), 72444622130905088, (certNat% 66), 434037729802584064, (certNat% 32), (certNat% 67), (certNat% 68), 9016270225670144, 10376293554346524672]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨72, by decide⟩ c13 c12
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c14 c9
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c15 c8
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c16 c5
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c17 c4
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c18 c3
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c19 c2
  c20
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00026.record011_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00026.record011_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00026.record011_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00026.record011_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00026.record011_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00026.record011_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00026.record011_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00026.record011_validity Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00026.record011_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00026.record011

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00026.record018
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00026.record018
def vertexColumn : Fields := ⟨10, (certNat% 69)⟩
def kindColumn : Fields := ⟨3, (certNat% 70)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 71), (certNat% 72), (certNat% 73), 11682311045120, 126102163955908608, (certNat% 74), (certNat% 75), (certNat% 76)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 77), 297538979031416832, (certNat% 78), (certNat% 79), (certNat% 80), (certNat% 81), (certNat% 82), 76562842932740096, (certNat% 83)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c1 c0
  c2
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00026.record018_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00026.record018_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00026.record018_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00026.record018_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00026.record018_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00026.record018_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00026.record018_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00026.record018_validity Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00026.record018_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00026.record018

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00026.record028
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00026.record028
def vertexColumn : Fields := ⟨10, (certNat% 84)⟩
def kindColumn : Fields := ⟨3, (certNat% 85)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩, ⟨95, by decide⟩, ⟨96, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 86), (certNat% 87), (certNat% 88), (certNat% 89), (certNat% 90), (certNat% 91), (certNat% 92), 545357767376896, 548313254632357888]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00026.record028_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00026.record028_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00026.record028_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00026.record028_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00026.record028_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00026.record028_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00026.record028_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00026.record028_validity Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00026.record028_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00026.record028
