module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow29Part00023Data
public import GraphInputsRow29Part00023Frames
public import GraphInputsRow29Part00023Leaves
public import GraphInputsRow29Part00023Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00023.record000
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record000
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨61, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨71, by decide⟩, ⟨74, by decide⟩, ⟨77, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨90, by decide⟩, ⟨93, by decide⟩, ⟨96, by decide⟩, ⟨99, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), (certNat% 3), 7486127996928, 3799912185593856, (certNat% 4)]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record000_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record000_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record000_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record000_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record000_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record000_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record000_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record000_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record000_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00023.record000

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00023.record001
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record001
def vertexColumn : Fields := ⟨10, (certNat% 5)⟩
def kindColumn : Fields := ⟨3, (certNat% 6)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨59, by decide⟩, ⟨62, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨79, by decide⟩, ⟨84, by decide⟩, ⟨87, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 7), (certNat% 8), (certNat% 9), (certNat% 10), 246572079598534656, 560750930165760]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record001_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record001_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record001_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record001_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record001_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record001_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record001_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record001_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record001_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00023.record001

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00023.record002
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record002
def vertexColumn : Fields := ⟨10, (certNat% 11)⟩
def kindColumn : Fields := ⟨3, (certNat% 12)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨74, by decide⟩, ⟨77, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨86, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 13), (certNat% 14), (certNat% 15), (certNat% 16), 835628837109760, 842173130318282752]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record002_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record002_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record002_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record002_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record002_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record002_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record002_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record002_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record002_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00023.record002

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00023.record003
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record003
def vertexColumn : Fields := ⟨10, (certNat% 17)⟩
def kindColumn : Fields := ⟨3, (certNat% 18)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨40, by decide⟩, ⟨43, by decide⟩, ⟨47, by decide⟩, ⟨49, by decide⟩, ⟨51, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨88, by decide⟩, ⟨91, by decide⟩, ⟨94, by decide⟩, ⟨97, by decide⟩, ⟨98, by decide⟩, ⟨99, by decide⟩, ⟨100, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 19), (certNat% 20), (certNat% 21), (certNat% 22), 972777777210064896, (certNat% 23), (certNat% 24)]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record003_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record003_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record003_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record003_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record003_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record003_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record003_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record003_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record003_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00023.record003

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00023.record010
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record010
def vertexColumn : Fields := ⟨10, (certNat% 25)⟩
def kindColumn : Fields := ⟨3, (certNat% 26)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨36, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨67, by decide⟩, ⟨70, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨86, by decide⟩, ⟨93, by decide⟩, ⟨96, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 27), 18014398526259200, (certNat% 28), (certNat% 29), (certNat% 30)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 31), (certNat% 28), 9223372039002259456, (certNat% 32), (certNat% 33), (certNat% 34)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨86, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 35), (certNat% 28), 36028797052518400, (certNat% 32), (certNat% 33), (certNat% 34)]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨78, by decide⟩ c3 c0
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 36), 58720256, 144115188075855872, (certNat% 37), (certNat% 38)]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 39), (certNat% 40), (certNat% 41), 125829120, 720575940379279360, (certNat% 42)]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨79, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 43), (certNat% 44), (certNat% 45), (certNat% 46), 3602879701896396800, 3003121664]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 47), (certNat% 48), (certNat% 49), (certNat% 50), (certNat% 51), (certNat% 52)]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 53), (certNat% 28), (certNat% 54), (certNat% 46), (certNat% 55), 3512807709348986880, 3011510272]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c10 c9
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c11 c8
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c12 c7
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨64, by decide⟩ c13 c4
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c14 c2
  c15
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record010_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record010_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record010_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record010_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record010_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record010_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record010_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record010_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record010_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00023.record010

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00023.record027
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record027
def vertexColumn : Fields := ⟨10, (certNat% 56)⟩
def kindColumn : Fields := ⟨3, (certNat% 57)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨53, by decide⟩, ⟨55, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨78, by decide⟩, ⟨83, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨91, by decide⟩, ⟨93, by decide⟩, ⟨95, by decide⟩, ⟨97, by decide⟩, ⟨99, by decide⟩, ⟨101, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 58), (certNat% 59), (certNat% 60), 695784701952, (certNat% 61)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 62), (certNat% 63), (certNat% 64), (certNat% 65), (certNat% 66)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 67), (certNat% 68), (certNat% 60), (certNat% 69), (certNat% 70)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 71), (certNat% 72), (certNat% 73), (certNat% 69)]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 74), (certNat% 75), (certNat% 63), 970662608896, (certNat% 76)]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨93, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 77), (certNat% 78), (certNat% 79), (certNat% 80), (certNat% 81), (certNat% 82)]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨65, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨83, by decide⟩ c7 c2
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c8 c1
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨87, by decide⟩ c9 c0
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 83), (certNat% 84), (certNat% 85), 446676598784, (certNat% 64)]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 86), (certNat% 87), (certNat% 61), (certNat% 82), (certNat% 88)]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 89), (certNat% 68), (certNat% 85), (certNat% 90), (certNat% 91)]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 92), (certNat% 72), (certNat% 93), (certNat% 90)]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 94), (certNat% 95), (certNat% 87), 996432412672, (certNat% 96)]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨91, by decide⟩ c15 c14
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 97), (certNat% 98), (certNat% 99), (certNat% 100), (certNat% 101), (certNat% 65)]
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨65, by decide⟩ c17 c16
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨78, by decide⟩ c18 c13
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c19 c12
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨88, by decide⟩ c20 c11
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 102), (certNat% 103), 354042744143872, (certNat% 104), (certNat% 105)]
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 106), (certNat% 96), (certNat% 107), (certNat% 108), (certNat% 109)]
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 110), (certNat% 111), (certNat% 112), (certNat% 113), (certNat% 105)]
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 114), (certNat% 115), (certNat% 116), (certNat% 117), (certNat% 118), (certNat% 119)]
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨83, by decide⟩ c25 c24
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c26 c23
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨87, by decide⟩ c27 c22
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 120), (certNat% 121), 213305255788544, (certNat% 122), (certNat% 107)]
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 123), (certNat% 76), (certNat% 105), (certNat% 119), (certNat% 113)]
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 124), (certNat% 111), (certNat% 117), (certNat% 109), (certNat% 107)]
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 125), (certNat% 126), (certNat% 127), (certNat% 128), (certNat% 112), (certNat% 108)]
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨78, by decide⟩ c32 c31
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c33 c30
  let c35 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨88, by decide⟩ c34 c29
  let c36 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 129), (certNat% 130), (certNat% 131), (certNat% 132), (certNat% 133), (certNat% 134)]
  let c37 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 135), (certNat% 136), (certNat% 137), (certNat% 63)]
  let c38 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 138), (certNat% 139), (certNat% 63), (certNat% 82)]
  let c39 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 140), (certNat% 131), (certNat% 141), (certNat% 65), (certNat% 142), 549755813888]
  let c40 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨78, by decide⟩ c39 c38
  let c41 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c40 c37
  let c42 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 143), (certNat% 144), (certNat% 145), (certNat% 146), (certNat% 117), 9007199254740992]
  let c43 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 147), (certNat% 128), (certNat% 126), (certNat% 148), (certNat% 108), (certNat% 149)]
  let c44 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 150), (certNat% 151), (certNat% 63), (certNat% 136), 8881992368128, (certNat% 152)]
  let c45 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 153), (certNat% 84), (certNat% 154), (certNat% 155), 141562122076160, (certNat% 156)]
  let c46 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 157), (certNat% 158), (certNat% 151), (certNat% 159), 8864812498944, (certNat% 160)]
  let c47 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 161), (certNat% 162), (certNat% 163), (certNat% 154), 141287244169216, (certNat% 164)]
  let c48 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 165), (certNat% 159), (certNat% 166), (certNat% 117), (certNat% 132), 68719476736]
  let c49 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 167), (certNat% 166), (certNat% 117), (certNat% 142), (certNat% 108), (certNat% 132), 68719476736]
  let c50 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c49 c48
  let c51 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c50 c47
  let c52 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨78, by decide⟩ c51 c46
  let c53 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c52 c45
  let c54 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c53 c44
  let c55 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c54 c43
  let c56 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c55 c42
  let c57 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c56 c41
  let c58 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c57 c36
  let c59 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c58 c35
  let c60 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c59 c28
  let c61 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c60 c21
  let c62 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c61 c10
  c62
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record027_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record027_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record027_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record027_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record027_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record027_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record027_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record027_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record027_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00023.record027

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00023.record015
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "3a8d51ac5713caca724e87a4d8b63392e2b91e1783ee8751ac671e2749b2729aa5a99a5594e479e1745b15a5c5695955554d4b56354d3352d2b51d1743db0ea398e9394e334ccb31cccb4ac6b46c5b0ecc749ca745c970dd0f0bc1fcc0aa1588e13b21a8711946314c5292a5151550d2344d28c530cc8b12c2b21c4705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "36db6db6d34d34926da49b4db6d349349249369b492492692692492249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record015 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record015 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record015.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record015.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record015.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 48), (facetIndex 49), (facetIndex 51)]))
 (.leaf ([(facetIndex 64), (facetIndex 67), (facetIndex 68), (facetIndex 69)])))
 (.branch 3
 (.leaf ([(facetIndex 73), (facetIndex 77), (facetIndex 78), (facetIndex 79)]))
 (.branch 4
 (.leaf ([(facetIndex 94), (facetIndex 95)]))
 (.leaf ([(facetIndex 66), (facetIndex 100)])))))
 (.branch 8
 (.branch 6
 (.leaf ([(facetIndex 35), (facetIndex 52), (facetIndex 60), (facetIndex 98)]))
 (.branch 7
 (.leaf ([(facetIndex 84), (facetIndex 88), (facetIndex 90)]))
 (.leaf ([(facetIndex 39), (facetIndex 91), (facetIndex 96)]))))
 (.branch 9
 (.leaf ([(facetIndex 70), (facetIndex 72), (facetIndex 86)]))
 (.branch 10
 (.leaf ([(facetIndex 92), (facetIndex 93), (facetIndex 97)]))
 (.leaf ([(facetIndex 99)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "4a5973399760608060000222000280811140100050000000500000000000070005z23;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 11
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped3_0000 : List Nat := [0]
def grouped3_0001 : List Nat := [0, 1]
def grouped3_0002 : List Nat := [0, 1, 2, 3, 4]
def grouped3_0004 : List Nat := [1]
def grouped3_0005 : List Nat := [2]
def grouped3_0006 : List Nat := [2, 3, 4]
def grouped3_0007 : List Nat := [3]
def grouped3_0008 : List Nat := [3, 4]
def grouped3_0009 : List Nat := [4]
def grouped3_0010 : List Nat := [5]
def grouped3_0011 : List Nat := [5, 6, 7]
def grouped3_0012 : List Nat := [5, 6, 7, 8, 9, 10]
def grouped3_0013 : List Nat := [6]
def grouped3_0014 : List Nat := [6, 7]
def grouped3_0015 : List Nat := [7]
def grouped3_0016 : List Nat := [8]
def grouped3_0017 : List Nat := [8, 9, 10]
def grouped3_0018 : List Nat := [9]
def grouped3_0019 : List Nat := [9, 10]
def grouped3_0020 : List Nat := [10]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record015 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record015_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00023.record015" "{\"atoms\":[{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group\",\"kind\":3,\"index\":9},{\"tag\":\"group\",\"kind\":3,\"index\":10},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0006\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0014\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0011\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0019\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0012\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0012\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00023.record015" 78

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00023.record015" "{\"ridges\":[[12,268],[14,276],[16,265],[19,592],[21,641],[30,268],[33,276],[41,265],[47,592],[49,610],[50,641],[51,706],[54,268],[56,268],[58,268],[59,268],[61,276],[62,276],[63,592],[64,660],[65,276],[66,420],[67,708],[68,836],[69,900],[70,120],[71,265],[72,344],[73,616],[74,296],[75,641],[76,265],[77,712],[78,840],[80,592],[81,641],[82,592],[83,641],[86,282],[92,120],[93,282],[94,610],[97,344],[99,836]],\"owners\":[[16,265,[12,30,39,54,58,59,72,78,79],[41,71,74,76]],[41,265,[12,54,58,59,72,78,79],[16,30,39,71,74,76]],[71,265,[12,30,58,59,78,79],[16,39,41,54,72,74,76]],[76,265,[12,30,39,54,58,59,72],[16,41,71,74,78,79]],[12,268,[86,88,96,97,98],[30,54,56,58,59]],[30,268,[96,97,98],[12,54,56,58,59,86,88]],[54,268,[88,98],[12,30,56,58,59,86,96,97]],[56,268,[86,97],[12,30,54,58,59,88,96,98]],[58,268,[86,88,96,98],[12,30,54,56,59,97]],[59,268,[86,88,96,97],[12,30,54,56,58,98]],[14,276,[86,91,96,97,99],[33,54,61,62,65]],[33,276,[96,97,99],[14,54,61,62,65,86,91]],[61,276,[86,97,99],[14,33,54,62,65,91,96]],[62,276,[86,91,96],[14,33,54,61,65,97,99]],[65,276,[86,91,96,97],[14,33,54,61,62,99]],[74,296,[88,93,96],[16,41,56,71,76,98,100]],[19,592,[94,99],[47,63,80,82]],[47,592,[99],[19,63,80,82,94]],[63,592,[94],[19,47,80,82,99]],[80,592,[99],[19,47,63,82,94]],[82,592,[94],[19,47,63,80,99]],[21,641,[48,51,64,67,69,77,79],[50,75,81,83]],[50,641,[64,67,69,77,79],[21,48,51,75,81,83]],[75,641,[48,51,64,67,69],[21,50,77,79,81,83]],[81,641,[51,67,69,77,79],[21,48,50,64,75,83]],[83,641,[48,51,64,67,77],[21,50,69,75,79,81]],[86,282,[39,93],[]],[93,282,[39,86],[]],[49,610,[94],[]],[94,610,[49],[]],[51,706,[],[]],[64,660,[],[]],[66,420,[98],[]],[67,708,[],[]],[68,836,[99],[]],[99,836,[68],[]],[69,900,[],[]],[70,120,[92],[]],[92,120,[70],[]],[72,344,[97],[]],[97,344,[72],[]],[73,616,[],[]],[77,712,[],[]],[78,840,[],[]]],\"edges\":[[22,[12,14,30,33,35,54,56,58,59,61,62,65,66,68,69,86,88,91,96,97,98,99]],[28,[12,16,30,39,41,54,56,58,59,71,72,74,76,78,79,86,88,93,96,97,98,100]],[41,[19,47,49,51,63,67,68,73,77,78,80,82,94,99]],[43,[21,48,50,51,64,67,69,75,77,79,81,83,95,100]]],\"groupings\":[3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00023.record015" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00023.record015\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-3,1,6,9,16,18,19,31,37,38],[-10,1,16,18,19,31,37,38],[-30,1,6,18,19,37,38],[-35,1,6,9,16,18,19,31],[-1,43,44,50,51,52],[-6,50,51,52],[-16,44,52],[-17,43,51],[-18,43,44,50,52],[-19,43,44,50,51],[-2,43,45,50,51,53],[-7,50,51,53],[-20,43,51,53],[-21,43,45,50],[-24,43,45,50,51],[-33,44,47,50],[-4,48,53],[-11,53],[-22,48],[-39,53],[-41,48],[-5,12,15,23,26,28,36,38],[-14,23,26,28,36,38],[-34,12,15,23,26,28],[-40,15,26,28,36,38],[-42,12,15,23,26,36],[-43,9,47],[-47,9,43],[-13,48],[-48,13],[-15],[-23],[-25,52],[-26],[-27,53],[-53,27],[-28],[-29,46],[-46,29],[-31,51],[-51,31],[-32],[-36],[-37],[-12,55],[-13,55],[-27,56],[-38,57],[-48,58],[-49,58],[-54,59],[-8,60],[-52,60],[-44,61],[-9,62],[-45,62],[-50,62],[-63,29,31,43],[-29,63],[-31,63],[-43,63],[-64,46,47,51],[-46,64],[-47,64],[-51,64],[-65,53],[-53,65],[-56,66],[-55,66],[-59,67],[-58,67],[-67,68],[-57,68],[-68,69],[-66,69],[-66,-68,70],[-62,71],[-61,71],[-71,72],[-60,72],[-73,64,65],[-65,73],[-64,73],[-74,63,73],[-73,74],[-63,74],[-63,-73,75],[-74,76],[-75,77],[-72,76],[-72,-74,77],[-69,-77,78],[-70,-76,78],[-78],[1,2,6,7,8,16,17,18,19,20,21,24,25,27,28,43,44,45,50,51,52,53],[1,3,6,9,10,16,17,18,19,30,31,33,35,37,38,43,44,47,50,51,52,54],[4,11,13,15,22,26,27,32,36,37,39,41,48,53],[5,12,14,15,23,26,28,34,36,38,40,42,49,54]],\"atoms\":[{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group\",\"index\":9,\"kind\":3},{\"tag\":\"group\",\"index\":10,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"mate\",\"ridge\":265,\"a\":16,\"owners\":[12,30,39,54,58,59,72,78,79]},{\"tag\":\"mate\",\"ridge\":265,\"a\":41,\"owners\":[12,54,58,59,72,78,79]},{\"tag\":\"mate\",\"ridge\":265,\"a\":71,\"owners\":[12,30,58,59,78,79]},{\"tag\":\"mate\",\"ridge\":265,\"a\":76,\"owners\":[12,30,39,54,58,59,72]},{\"tag\":\"mate\",\"ridge\":268,\"a\":12,\"owners\":[86,88,96,97,98]},{\"tag\":\"mate\",\"ridge\":268,\"a\":30,\"owners\":[96,97,98]},{\"tag\":\"mate\",\"ridge\":268,\"a\":54,\"owners\":[88,98]},{\"tag\":\"mate\",\"ridge\":268,\"a\":56,\"owners\":[86,97]},{\"tag\":\"mate\",\"ridge\":268,\"a\":58,\"owners\":[86,88,96,98]},{\"tag\":\"mate\",\"ridge\":268,\"a\":59,\"owners\":[86,88,96,97]},{\"tag\":\"mate\",\"ridge\":276,\"a\":14,\"owners\":[86,91,96,97,99]},{\"tag\":\"mate\",\"ridge\":276,\"a\":33,\"owners\":[96,97,99]},{\"tag\":\"mate\",\"ridge\":276,\"a\":61,\"owners\":[86,97,99]},{\"tag\":\"mate\",\"ridge\":276,\"a\":62,\"owners\":[86,91,96]},{\"tag\":\"mate\",\"ridge\":276,\"a\":65,\"owners\":[86,91,96,97]},{\"tag\":\"mate\",\"ridge\":296,\"a\":74,\"owners\":[88,93,96]},{\"tag\":\"mate\",\"ridge\":592,\"a\":19,\"owners\":[94,99]},{\"tag\":\"mate\",\"ridge\":592,\"a\":47,\"owners\":[99]},{\"tag\":\"mate\",\"ridge\":592,\"a\":63,\"owners\":[94]},{\"tag\":\"mate\",\"ridge\":592,\"a\":80,\"owners\":[99]},{\"tag\":\"mate\",\"ridge\":592,\"a\":82,\"owners\":[94]},{\"tag\":\"mate\",\"ridge\":641,\"a\":21,\"owners\":[48,51,64,67,69,77,79]},{\"tag\":\"mate\",\"ridge\":641,\"a\":50,\"owners\":[64,67,69,77,79]},{\"tag\":\"mate\",\"ridge\":641,\"a\":75,\"owners\":[48,51,64,67,69]},{\"tag\":\"mate\",\"ridge\":641,\"a\":81,\"owners\":[51,67,69,77,79]},{\"tag\":\"mate\",\"ridge\":641,\"a\":83,\"owners\":[48,51,64,67,77]},{\"tag\":\"mate\",\"ridge\":282,\"a\":86,\"owners\":[39,93]},{\"tag\":\"mate\",\"ridge\":282,\"a\":93,\"owners\":[39,86]},{\"tag\":\"mate\",\"ridge\":610,\"a\":49,\"owners\":[94]},{\"tag\":\"mate\",\"ridge\":610,\"a\":94,\"owners\":[49]},{\"tag\":\"mate\",\"ridge\":706,\"a\":51,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":660,\"a\":64,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":420,\"a\":66,\"owners\":[98]},{\"tag\":\"mate\",\"ridge\":708,\"a\":67,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":836,\"a\":68,\"owners\":[99]},{\"tag\":\"mate\",\"ridge\":836,\"a\":99,\"owners\":[68]},{\"tag\":\"mate\",\"ridge\":900,\"a\":69,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":120,\"a\":70,\"owners\":[92]},{\"tag\":\"mate\",\"ridge\":120,\"a\":92,\"owners\":[70]},{\"tag\":\"mate\",\"ridge\":344,\"a\":72,\"owners\":[97]},{\"tag\":\"mate\",\"ridge\":344,\"a\":97,\"owners\":[72]},{\"tag\":\"mate\",\"ridge\":616,\"a\":73,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":712,\"a\":77,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":840,\"a\":78,\"owners\":[]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":48,\"full_literals\":[-12,55]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":49,\"full_literals\":[-13,55]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":68,\"full_literals\":[-27,56]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":79,\"full_literals\":[-38,57]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":94,\"full_literals\":[-48,58]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":95,\"full_literals\":[-49,58]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":100,\"full_literals\":[-54,59]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":35,\"full_literals\":[-8,60]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":98,\"full_literals\":[-52,60]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":88,\"full_literals\":[-44,61]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":39,\"full_literals\":[-9,62]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":91,\"full_literals\":[-45,62]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":96,\"full_literals\":[-50,62]},{\"tag\":\"group_or\",\"kind\":3,\"index\":8,\"members\":[70,72,86],\"full_literals\":[-63,29,31,43]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":70,\"full_literals\":[-29,63]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":72,\"full_literals\":[-31,63]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":86,\"full_literals\":[-43,63]},{\"tag\":\"group_or\",\"kind\":3,\"index\":9,\"members\":[92,93,97],\"full_literals\":[-64,46,47,51]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":92,\"full_literals\":[-46,64]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":93,\"full_literals\":[-47,64]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":97,\"full_literals\":[-51,64]},{\"tag\":\"group_or\",\"kind\":3,\"index\":10,\"members\":[99],\"full_literals\":[-65,53]},{\"tag\":\"group_take\",\"kind\":3,\"index\":10,\"member\":99,\"full_literals\":[-53,65]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-56,66],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-55,false,66],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0008\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-59,67],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0008\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-58,false,67],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"grouped3_0006\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-67,68],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"grouped3_0006\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-57,false,68],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-68,69],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-66,false,69],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-66,-68,70],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0014\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-62,71],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0014\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-61,false,71],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6,7],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0011\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-71,72],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6,7],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0011\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-60,false,72],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[9],\"right\":[10],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0019\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-73,64,65],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[9],\"right\":[10],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0019\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-65,73],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[9],\"right\":[10],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0019\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-64,false,73],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9,10],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0017\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-74,63,73],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9,10],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0017\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-73,74],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9,10],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-63,false,74],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9,10],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-63,-73,75],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6,7],\"right\":[8,9,10],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0012\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-74,76],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6,7],\"right\":[8,9,10],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0012\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-75,77],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6,7],\"right\":[8,9,10],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0012\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-72,false,76],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6,7],\"right\":[8,9,10],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0012\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-72,-74,77],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9,10],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0012\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-69,-77,78],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9,10],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0012\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-70,-76,78],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":22,\"owners\":[12,14,30,33,35,54,56,58,59,61,62,65,66,68,69,86,88,91,96,97,98,99]},{\"tag\":\"edge\",\"edge\":28,\"owners\":[12,16,30,39,41,54,56,58,59,71,72,74,76,78,79,86,88,93,96,97,98,100]},{\"tag\":\"edge\",\"edge\":41,\"owners\":[19,47,49,51,63,67,68,73,77,78,80,82,94,99]},{\"tag\":\"edge\",\"edge\":43,\"owners\":[21,48,50,51,64,67,69,75,77,79,81,83,95,100]}]}"
  "99 1 2 6 7 8 16 17 18 19 20 21 24 25 27 43 44 45 50 51 52 53 0 37 95 0\n100 1 3 6 9 10 16 17 18 19 30 31 33 35 38 43 44 47 50 51 52 54 0 44 96 0\n101 4 11 13 22 27 39 41 48 53 0 31 34 42 43 44 97 0\n102 5 12 14 34 38 40 42 49 54 0 31 32 34 37 43 98 0\n103 69 0 37 43 34 32 31 74 75 72 73 69 70 71 48 45 51 50 25 23 22 24 26 102 0\n104 -77 0 103 94 92 0\n105 -75 0 104 89 0\n106 -73 72 70 0 105 44 79 78 54 80 53 7 77 57 55 87 59 60 61 39 41 5 28 9 8 10 62 6 4 16 81 66 36 47 68 76 72 73 70 48 51 2 1 3 100 0\n107 -74 70 0 104 91 79 77 55 106 83 84 63 64 65 38 27 40 58 0\n108 48 53 0 35 20 18 19 21 29 17 101 0\n109 70 0 107 85 82 67 108 30 49 46 71 69 72 76 0\n110 -76 0 109 94 93 0\n111 -74 0 110 88 0\n112 -72 0 110 90 0\n113 -73 0 111 85 0\n114 -63 0 111 86 0\n115 -71 0 112 79 0\n116 -60 0 112 80 0\n117 -65 0 113 82 0\n118 -64 0 113 83 0\n119 -43 0 114 61 0\n120 -62 0 115 77 0\n121 -61 0 115 78 0\n122 -8 0 116 52 0\n123 -52 0 116 53 0\n124 -53 0 117 67 0\n125 -51 0 118 65 0\n126 -20 0 119 124 125 13 0\n127 -45 0 120 56 0\n128 -50 0 120 57 0\n129 -44 0 121 54 0\n130 -25 0 123 33 0\n131 -16 0 123 129 7 0\n132 -18 0 123 129 128 119 9 0\n133 -6 0 123 125 128 6 0\n134 -1 0 123 119 128 125 129 5 0\n135 -27 0 124 35 0\n136 -17 0 125 119 8 0\n137 -21 0 127 119 128 14 0\n138 -2 0 127 119 128 125 124 11 0\n139 -24 0 127 119 128 125 15 0\n140 -7 0 128 124 125 12 0\n141 -19 0 129 125 128 119 10 0\n142 0 134 137 123 138 122 133 136 132 141 140 131 139 130 135 119 126 127 128 125 129 124 99 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record015.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record015.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record015.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record015.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record015 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record015.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record015.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record015.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record015.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record015 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record015_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record015_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record015_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record015_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record015_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record015_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record015_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record015 Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record015_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record015_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record015_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00023.record015

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00023.record021
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "13c2f3a2e4b52b49b2d2b2a9a95a4e8bab1aa6998d64d8b64b8ae1b91e2783ee8791d46d16c749ca669565392e6c5a9665355352d52d2b46d4749d0f783d0ec3c8ea368e63c4e9364e5354cd34ccb3c2e4b52e2b4acab1ad1b26c5b0ee8791cc789d2729c6745c9715c3743c8f13c2f07c5cc8aa24a91a168a6258561382e07b21a852946459294951544d0b41d"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "369b6da69369a6924924db6d349b4d34924936d26db6db6db6d369a6db6d36936d2449249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record021 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record021 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record021.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record021.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record021.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 6
 (.branch 3
 (.branch 1
 (.leaf ([(facetIndex 35), (facetIndex 74), (facetIndex 76)]))
 (.branch 2
 (.leaf ([(facetIndex 46), (facetIndex 80), (facetIndex 82)]))
 (.leaf ([(facetIndex 37), (facetIndex 97), (facetIndex 99)]))))
 (.branch 4
 (.leaf ([(facetIndex 48), (facetIndex 103), (facetIndex 105)]))
 (.branch 5
 (.leaf ([(facetIndex 28), (facetIndex 72), (facetIndex 77), (facetIndex 83)]))
 (.leaf ([(facetIndex 54), (facetIndex 84), (facetIndex 85), (facetIndex 86)])))))
 (.branch 9
 (.branch 7
 (.leaf ([(facetIndex 39), (facetIndex 95), (facetIndex 100), (facetIndex 106)]))
 (.branch 8
 (.leaf ([(facetIndex 56), (facetIndex 107), (facetIndex 108), (facetIndex 109)]))
 (.leaf ([(facetIndex 50), (facetIndex 111), (facetIndex 112)]))))
 (.branch 10
 (.leaf ([(facetIndex 26), (facetIndex 27), (facetIndex 32), (facetIndex 36), (facetIndex 38), (facetIndex 47), (facetIndex 49), (facetIndex 51), (facetIndex 55), (facetIndex 57)]))
 (.branch 11
 (.leaf ([(facetIndex 31), (facetIndex 41), (facetIndex 43), (facetIndex 52), (facetIndex 53), (facetIndex 59)]))
 (.leaf ([(facetIndex 34), (facetIndex 44), (facetIndex 58), (facetIndex 62), (facetIndex 63), (facetIndex 64)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "880777630300620206000000005554101004000040000000bbb00ab9795aa9893910ba0a069290b09a00499z1a;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 12
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped3_0000 : List Nat := [0]
def grouped3_0001 : List Nat := [0, 1, 2]
def grouped3_0002 : List Nat := [0, 1, 2, 3, 4, 5]
def grouped3_0004 : List Nat := [1]
def grouped3_0005 : List Nat := [1, 2]
def grouped3_0006 : List Nat := [2]
def grouped3_0007 : List Nat := [3]
def grouped3_0008 : List Nat := [3, 4, 5]
def grouped3_0009 : List Nat := [4]
def grouped3_0010 : List Nat := [4, 5]
def grouped3_0011 : List Nat := [5]
def grouped3_0012 : List Nat := [6]
def grouped3_0013 : List Nat := [6, 7, 8]
def grouped3_0014 : List Nat := [6, 7, 8, 9, 10, 11]
def grouped3_0015 : List Nat := [7]
def grouped3_0016 : List Nat := [7, 8]
def grouped3_0017 : List Nat := [8]
def grouped3_0018 : List Nat := [9]
def grouped3_0019 : List Nat := [9, 10, 11]
def grouped3_0020 : List Nat := [10]
def grouped3_0021 : List Nat := [10, 11]
def grouped3_0022 : List Nat := [11]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record021 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record021_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00023.record021" "{\"atoms\":[{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":102},{\"tag\":\"facet\",\"index\":103},{\"tag\":\"facet\",\"index\":105},{\"tag\":\"facet\",\"index\":106},{\"tag\":\"facet\",\"index\":107},{\"tag\":\"facet\",\"index\":108},{\"tag\":\"facet\",\"index\":109},{\"tag\":\"facet\",\"index\":111},{\"tag\":\"facet\",\"index\":112},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group\",\"kind\":3,\"index\":9},{\"tag\":\"group\",\"kind\":3,\"index\":10},{\"tag\":\"group\",\"kind\":3,\"index\":11},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0005\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0016\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0016\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0021\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0019\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0019\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0014\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0014\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00023.record021" 88

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00023.record021" "{\"ridges\":[[4,145],[7,273],[15,146],[18,274],[30,146],[35,519],[37,578],[42,273],[42,274],[48,577],[54,531],[55,387],[58,577],[62,577],[63,577],[66,145],[67,273],[71,145],[72,308],[73,145],[74,612],[76,708],[77,184],[78,273],[79,273],[79,280],[80,616],[82,840],[83,432],[84,720],[85,848],[86,912],[89,146],[90,274],[94,146],[96,146],[97,578],[97,612],[99,578],[99,708],[101,274],[102,274],[103,578],[105,578],[107,720],[108,848],[109,912]],\"owners\":[[4,145,[41,50,52,55,56,77,83,84,86],[30,66,71,73]],[66,145,[50,52,55,56,83,84,86],[4,30,41,71,73,77]],[71,145,[41,52,55,56,84,86],[4,30,50,66,73,77,83]],[73,145,[41,50,55,56,77,83,86],[4,30,52,66,71,84]],[7,273,[31,51,53,55,57,72,83,85,86],[42,67,78,79]],[42,273,[72,83,85,86],[7,31,51,53,55,57,67,78,79]],[67,273,[51,53,55,57,83,85,86],[7,31,42,72,78,79]],[78,273,[31,53,55,57,85,86],[7,42,51,67,72,79,83]],[79,273,[31,51,55,57,72,83,86],[7,42,53,67,78,85]],[79,280,[18,90,101,112],[7,67,78,102]],[15,146,[41,50,52,55,56,100,106,107,109],[30,89,94,96]],[30,146,[100,106,107,109],[15,41,50,52,55,56,89,94,96]],[89,146,[50,52,55,56,106,107,109],[15,30,41,94,96,100]],[94,146,[41,52,55,56,107,109],[15,30,50,89,96,100,106]],[96,146,[41,50,55,56,100,106,109],[15,30,52,89,94,107]],[18,274,[31,51,53,55,57,95,106,108,109],[42,90,101,102]],[42,274,[95,106,108,109],[18,31,51,53,55,57,90,101,102]],[90,274,[51,53,55,57,106,108,109],[18,31,42,95,101,102]],[101,274,[31,53,55,57,108,109],[18,42,51,90,95,102,106]],[102,274,[31,51,55,57,95,106,109],[18,42,53,90,101,108]],[35,519,[37,38],[]],[48,577,[74,76,84,85],[37,54,58,62,63,80,82]],[58,577,[76,82,84,85],[37,48,54,62,63,74,80]],[62,577,[74,80,82,85],[37,48,54,58,63,76,84]],[63,577,[74,76,80,84],[37,48,54,58,62,82,85]],[37,578,[103,105,107,108],[48,54,58,62,63,97,99]],[97,578,[48,54,62,63,105,107,108],[37,58,99,103]],[99,578,[48,54,58,63,103,105,108],[37,62,97,107]],[103,578,[37,54,62,63,99,107,108],[48,58,97,105]],[105,578,[37,54,58,62,97,99,107],[48,63,103,108]],[54,531,[56,57],[]],[55,387,[59,64],[]],[72,308,[95,112],[]],[74,612,[97],[]],[97,612,[74],[]],[76,708,[99],[]],[99,708,[76],[]],[77,184,[100,111],[]],[80,616,[103],[]],[82,840,[105],[]],[83,432,[106],[]],[84,720,[107],[]],[107,720,[84],[]],[85,848,[108],[]],[108,848,[85],[]],[86,912,[109],[]],[109,912,[86],[]]],\"edges\":[[32,[4,15,30,41,50,52,55,56,66,71,73,77,83,84,86,89,94,96,100,106,107,109,111]],[33,[7,18,31,42,51,53,55,57,67,72,78,79,83,85,86,90,95,101,102,106,108,109,112]],[41,[37,48,54,58,62,63,74,76,80,82,84,85,97,99,103,105,107,108]]],\"groupings\":[3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00023.record021" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00023.record021\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-19,-11],[-40,-19],[-41,-19],[-55,-40],[-55,-41],[-56,-19],[-56,-55],[-57,-19],[-57,-40],[-57,-55],[-57,-56],[-1,10,13,15,18,19,33,38,39,41],[-26,13,15,18,19,38,39,41],[-28,10,15,18,19,39,41],[-30,10,13,18,19,33,38,41],[-2,6,14,16,18,20,29,38,40,41],[-11,29,38,40,41],[-27,14,16,18,20,38,40,41],[-34,6,16,18,20,40,41],[-35,6,14,18,20,29,38,41],[-35,4,43,50,59],[-3,10,13,15,18,19,49,54,55,57],[-5,49,54,55,57],[-42,13,15,18,19,54,55,57],[-44,10,15,18,19,55,57],[-46,10,13,18,19,49,54,57],[-4,6,14,16,18,20,45,54,56,57],[-11,45,54,56,57],[-43,14,16,18,20,54,56,57],[-50,6,16,18,20,56,57],[-51,6,14,18,20,45,54,57],[-7,8,9],[-12,31,32,39,40],[-21,32,37,39,40],[-23,31,36,37,40],[-24,31,32,36,39],[-8,52,53,55,56],[-47,12,17,23,24,53,55,56],[-48,12,17,21,24,52,53,56],[-52,8,17,23,24,48,55,56],[-53,8,17,21,23,47,48,55],[-17,19,20],[-18,22,25],[-29,45,59],[-31,47],[-47,31],[-32,48],[-48,32],[-33,49,58],[-36,52],[-37,53],[-38,54],[-39,55],[-55,39],[-40,56],[-56,40],[-41,57],[-57,41],[-60,7,31,32],[-31,60],[-32,60],[-36,61],[-37,61],[-8,62],[-47,62],[-48,62],[-12,63],[-52,63],[-53,63],[-17,64],[-39,64],[-40,64],[-41,64],[-45,65],[-49,65],[-54,65],[-19,66],[-55,66],[-56,66],[-57,66],[-13,67],[-58,67],[-59,67],[-9,68],[-14,68],[-18,68],[-20,68],[-6,69],[-10,69],[-15,69],[-16,69],[-22,69],[-21,70],[-23,70],[-24,70],[-25,70],[-62,71],[-61,71],[-72,60,71],[-71,72],[-60,72],[-60,-71,73],[-64,74],[-74,75],[-63,75],[-63,-74,76],[-77,72,75],[-75,77],[-76,78],[-72,77],[-72,-75,78],[-73,78],[-67,79],[-66,79],[-66,-67,80],[-79,81],[-80,82],[-65,81],[-65,-79,82],[-70,83],[-69,83],[-83,84],[-68,84],[-68,-83,85],[-84,86],[-85,87],[-81,86],[-81,-84,87],[-82,87],[-77,-87,88],[-78,-86,88],[-88],[1,3,5,10,13,15,18,19,26,28,30,33,38,39,41,42,44,46,49,54,55,57,58],[2,4,6,11,14,16,18,20,27,29,34,35,38,40,41,43,45,50,51,54,56,57,59],[8,12,17,21,23,24,31,32,36,37,39,40,47,48,52,53,55,56]],\"atoms\":[{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":102},{\"tag\":\"facet\",\"index\":103},{\"tag\":\"facet\",\"index\":105},{\"tag\":\"facet\",\"index\":106},{\"tag\":\"facet\",\"index\":107},{\"tag\":\"facet\",\"index\":108},{\"tag\":\"facet\",\"index\":109},{\"tag\":\"facet\",\"index\":111},{\"tag\":\"facet\",\"index\":112},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group\",\"index\":9,\"kind\":3},{\"tag\":\"group\",\"index\":10,\"kind\":3},{\"tag\":\"group\",\"index\":11,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":56,\"b\":42},{\"tag\":\"incompatible\",\"a\":85,\"b\":56},{\"tag\":\"incompatible\",\"a\":86,\"b\":56},{\"tag\":\"incompatible\",\"a\":107,\"b\":85},{\"tag\":\"incompatible\",\"a\":107,\"b\":86},{\"tag\":\"incompatible\",\"a\":108,\"b\":56},{\"tag\":\"incompatible\",\"a\":108,\"b\":107},{\"tag\":\"incompatible\",\"a\":109,\"b\":56},{\"tag\":\"incompatible\",\"a\":109,\"b\":85},{\"tag\":\"incompatible\",\"a\":109,\"b\":107},{\"tag\":\"incompatible\",\"a\":109,\"b\":108},{\"tag\":\"mate\",\"ridge\":145,\"a\":4,\"owners\":[41,50,52,55,56,77,83,84,86]},{\"tag\":\"mate\",\"ridge\":145,\"a\":66,\"owners\":[50,52,55,56,83,84,86]},{\"tag\":\"mate\",\"ridge\":145,\"a\":71,\"owners\":[41,52,55,56,84,86]},{\"tag\":\"mate\",\"ridge\":145,\"a\":73,\"owners\":[41,50,55,56,77,83,86]},{\"tag\":\"mate\",\"ridge\":273,\"a\":7,\"owners\":[31,51,53,55,57,72,83,85,86]},{\"tag\":\"mate\",\"ridge\":273,\"a\":42,\"owners\":[72,83,85,86]},{\"tag\":\"mate\",\"ridge\":273,\"a\":67,\"owners\":[51,53,55,57,83,85,86]},{\"tag\":\"mate\",\"ridge\":273,\"a\":78,\"owners\":[31,53,55,57,85,86]},{\"tag\":\"mate\",\"ridge\":273,\"a\":79,\"owners\":[31,51,55,57,72,83,86]},{\"tag\":\"mate\",\"ridge\":280,\"a\":79,\"owners\":[18,90,101,112]},{\"tag\":\"mate\",\"ridge\":146,\"a\":15,\"owners\":[41,50,52,55,56,100,106,107,109]},{\"tag\":\"mate\",\"ridge\":146,\"a\":30,\"owners\":[100,106,107,109]},{\"tag\":\"mate\",\"ridge\":146,\"a\":89,\"owners\":[50,52,55,56,106,107,109]},{\"tag\":\"mate\",\"ridge\":146,\"a\":94,\"owners\":[41,52,55,56,107,109]},{\"tag\":\"mate\",\"ridge\":146,\"a\":96,\"owners\":[41,50,55,56,100,106,109]},{\"tag\":\"mate\",\"ridge\":274,\"a\":18,\"owners\":[31,51,53,55,57,95,106,108,109]},{\"tag\":\"mate\",\"ridge\":274,\"a\":42,\"owners\":[95,106,108,109]},{\"tag\":\"mate\",\"ridge\":274,\"a\":90,\"owners\":[51,53,55,57,106,108,109]},{\"tag\":\"mate\",\"ridge\":274,\"a\":101,\"owners\":[31,53,55,57,108,109]},{\"tag\":\"mate\",\"ridge\":274,\"a\":102,\"owners\":[31,51,55,57,95,106,109]},{\"tag\":\"mate\",\"ridge\":519,\"a\":35,\"owners\":[37,38]},{\"tag\":\"mate\",\"ridge\":577,\"a\":48,\"owners\":[74,76,84,85]},{\"tag\":\"mate\",\"ridge\":577,\"a\":58,\"owners\":[76,82,84,85]},{\"tag\":\"mate\",\"ridge\":577,\"a\":62,\"owners\":[74,80,82,85]},{\"tag\":\"mate\",\"ridge\":577,\"a\":63,\"owners\":[74,76,80,84]},{\"tag\":\"mate\",\"ridge\":578,\"a\":37,\"owners\":[103,105,107,108]},{\"tag\":\"mate\",\"ridge\":578,\"a\":97,\"owners\":[48,54,62,63,105,107,108]},{\"tag\":\"mate\",\"ridge\":578,\"a\":99,\"owners\":[48,54,58,63,103,105,108]},{\"tag\":\"mate\",\"ridge\":578,\"a\":103,\"owners\":[37,54,62,63,99,107,108]},{\"tag\":\"mate\",\"ridge\":578,\"a\":105,\"owners\":[37,54,58,62,97,99,107]},{\"tag\":\"mate\",\"ridge\":531,\"a\":54,\"owners\":[56,57]},{\"tag\":\"mate\",\"ridge\":387,\"a\":55,\"owners\":[59,64]},{\"tag\":\"mate\",\"ridge\":308,\"a\":72,\"owners\":[95,112]},{\"tag\":\"mate\",\"ridge\":612,\"a\":74,\"owners\":[97]},{\"tag\":\"mate\",\"ridge\":612,\"a\":97,\"owners\":[74]},{\"tag\":\"mate\",\"ridge\":708,\"a\":76,\"owners\":[99]},{\"tag\":\"mate\",\"ridge\":708,\"a\":99,\"owners\":[76]},{\"tag\":\"mate\",\"ridge\":184,\"a\":77,\"owners\":[100,111]},{\"tag\":\"mate\",\"ridge\":616,\"a\":80,\"owners\":[103]},{\"tag\":\"mate\",\"ridge\":840,\"a\":82,\"owners\":[105]},{\"tag\":\"mate\",\"ridge\":432,\"a\":83,\"owners\":[106]},{\"tag\":\"mate\",\"ridge\":720,\"a\":84,\"owners\":[107]},{\"tag\":\"mate\",\"ridge\":720,\"a\":107,\"owners\":[84]},{\"tag\":\"mate\",\"ridge\":848,\"a\":85,\"owners\":[108]},{\"tag\":\"mate\",\"ridge\":848,\"a\":108,\"owners\":[85]},{\"tag\":\"mate\",\"ridge\":912,\"a\":86,\"owners\":[109]},{\"tag\":\"mate\",\"ridge\":912,\"a\":109,\"owners\":[86]},{\"tag\":\"group_or\",\"kind\":3,\"index\":0,\"members\":[35,74,76],\"full_literals\":[-60,7,31,32]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":74,\"full_literals\":[-31,60]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":76,\"full_literals\":[-32,60]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":80,\"full_literals\":[-36,61]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":82,\"full_literals\":[-37,61]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":37,\"full_literals\":[-8,62]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":97,\"full_literals\":[-47,62]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":99,\"full_literals\":[-48,62]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":48,\"full_literals\":[-12,63]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":103,\"full_literals\":[-52,63]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":105,\"full_literals\":[-53,63]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":54,\"full_literals\":[-17,64]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":84,\"full_literals\":[-39,64]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":85,\"full_literals\":[-40,64]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":86,\"full_literals\":[-41,64]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":95,\"full_literals\":[-45,65]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":100,\"full_literals\":[-49,65]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":106,\"full_literals\":[-54,65]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":56,\"full_literals\":[-19,66]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":107,\"full_literals\":[-55,66]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":108,\"full_literals\":[-56,66]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":109,\"full_literals\":[-57,66]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":50,\"full_literals\":[-13,67]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":111,\"full_literals\":[-58,67]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":112,\"full_literals\":[-59,67]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":38,\"full_literals\":[-9,68]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":51,\"full_literals\":[-14,68]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":55,\"full_literals\":[-18,68]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":57,\"full_literals\":[-20,68]},{\"tag\":\"group_take\",\"kind\":3,\"index\":10,\"member\":31,\"full_literals\":[-6,69]},{\"tag\":\"group_take\",\"kind\":3,\"index\":10,\"member\":41,\"full_literals\":[-10,69]},{\"tag\":\"group_take\",\"kind\":3,\"index\":10,\"member\":52,\"full_literals\":[-15,69]},{\"tag\":\"group_take\",\"kind\":3,\"index\":10,\"member\":53,\"full_literals\":[-16,69]},{\"tag\":\"group_take\",\"kind\":3,\"index\":10,\"member\":59,\"full_literals\":[-22,69]},{\"tag\":\"group_take\",\"kind\":3,\"index\":11,\"member\":58,\"full_literals\":[-21,70]},{\"tag\":\"group_take\",\"kind\":3,\"index\":11,\"member\":62,\"full_literals\":[-23,70]},{\"tag\":\"group_take\",\"kind\":3,\"index\":11,\"member\":63,\"full_literals\":[-24,70]},{\"tag\":\"group_take\",\"kind\":3,\"index\":11,\"member\":64,\"full_literals\":[-25,70]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0004\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0005\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-62,71],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0004\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0005\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-61,false,71],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-72,60,71],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-71,72],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-60,false,72],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-60,-71,73],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0010\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-64,74],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"grouped3_0008\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-74,75],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"grouped3_0008\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-63,false,75],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"grouped3_0008\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-63,-74,76],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"grouped3_0002\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-77,72,75],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"grouped3_0002\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-75,77],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"grouped3_0002\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-76,78],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-72,false,77],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-72,-75,78],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"grouped3_0002\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-73,false,78],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0016\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-67,79],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0016\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-66,false,79],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0016\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-66,-67,80],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-79,81],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-80,82],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-65,false,81],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-65,-79,82],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[10],\"right\":[11],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0021\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-70,83],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[10],\"right\":[11],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0021\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-69,false,83],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[9],\"right\":[10,11],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0019\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-83,84],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[9],\"right\":[10,11],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0019\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-68,false,84],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[9],\"right\":[10,11],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0019\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-68,-83,85],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6,7,8],\"right\":[9,10,11],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0014\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-84,86],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6,7,8],\"right\":[9,10,11],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0014\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-85,87],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6,7,8],\"right\":[9,10,11],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0014\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-81,false,86],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6,7,8],\"right\":[9,10,11],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0014\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-81,-84,87],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6,7,8],\"right\":[9,10,11],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0014\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-82,false,87],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5],\"right\":[6,7,8,9,10,11],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-77,-87,88],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5],\"right\":[6,7,8,9,10,11],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-78,-86,88],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":32,\"owners\":[4,15,30,41,50,52,55,56,66,71,73,77,83,84,86,89,94,96,100,106,107,109,111]},{\"tag\":\"edge\",\"edge\":33,\"owners\":[7,18,31,42,51,53,55,57,67,72,78,79,83,85,86,90,95,101,102,106,108,109,112]},{\"tag\":\"edge\",\"edge\":41,\"owners\":[37,48,54,58,62,63,74,76,80,82,84,85,97,99,103,105,107,108]}]}"
  "136 77 0 108 110 104 105 100 101 103 67 68 69 97 60 61 70 71 72 50 51 64 65 66 34 36 54 56 35 135 0\n137 -87 0 136 132 130 0\n138 -85 0 137 126 0\n139 -82 0 137 129 0\n140 -80 0 139 117 0\n141 71 7 -72 0 97 99 65 66 45 47 59 0\n142 75 68 66 73 0 136 77 87 42 84 79 55 78 53 105 107 67 68 69 50 37 51 32 141 102 60 61 46 35 34 48 36 135 0\n143 68 66 78 0 79 55 78 53 77 112 87 42 142 111 100 101 97 98 60 61 64 65 66 62 63 35 34 33 36 40 41 135 0\n144 81 78 0 138 116 118 113 114 75 76 81 82 77 78 80 23 49 52 53 57 143 124 120 121 96 89 90 92 43 26 22 25 14 12 15 24 13 133 0\n145 57 19 55 78 0 140 137 139 53 144 128 123 143 114 119 76 52 115 82 75 49 81 122 121 90 89 86 57 23 26 22 24 25 15 14 12 13 133 0\n146 19 55 78 0 137 53 144 128 122 120 95 94 93 123 87 109 42 145 9 11 58 73 103 104 106 111 67 68 69 101 50 37 51 39 38 60 61 135 0\n147 -19 78 0 140 137 139 144 128 123 143 114 119 76 52 74 115 83 44 122 121 91 88 87 86 85 1 2 3 6 8 19 16 18 20 30 27 29 31 134 0\n148 78 0 137 140 139 144 128 122 123 121 85 86 87 143 88 91 114 115 119 83 74 76 44 52 147 146 4 5 7 10 19 16 17 18 20 30 27 29 31 134 0\n149 -86 0 148 132 131 0\n150 -84 0 149 125 0\n151 -81 0 149 127 0\n152 -83 0 150 122 0\n153 -68 0 150 123 0\n154 -79 0 151 116 0\n155 -65 0 151 118 0\n156 -69 0 152 121 0\n157 -14 0 153 85 0\n158 -18 0 153 86 0\n159 -20 0 153 87 0\n160 -67 0 154 113 0\n161 -66 0 154 114 0\n162 -45 0 155 74 0\n163 -54 0 155 76 0\n164 -6 0 156 88 0\n165 -16 0 156 91 0\n166 -59 0 160 83 0\n167 -56 0 161 79 0\n168 -57 0 161 80 0\n169 -38 0 163 52 0\n170 -29 0 166 162 44 0\n171 -40 0 167 55 0\n172 -50 0 167 164 165 158 159 168 30 0\n173 -11 0 167 163 162 168 28 0\n174 -4 0 167 163 157 164 165 158 159 162 168 27 0\n175 -43 0 167 157 165 158 159 163 168 29 0\n176 -41 0 168 57 0\n177 -51 0 168 163 164 158 159 157 162 31 0\n178 -34 0 171 164 165 158 159 176 19 0\n179 -2 0 171 169 164 165 158 159 157 170 176 16 0\n180 -27 0 171 157 165 158 159 169 176 18 0\n181 -35 0 174 175 172 166 21 0\n182 0 174 179 164 173 157 165 158 159 180 170 178 181 169 171 176 175 162 172 177 163 167 168 166 134 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record021.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record021.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record021.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record021.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record021 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record021.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record021.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record021.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record021.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record021 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record021_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record021_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record021_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record021_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record021_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record021_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record021_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record021 Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record021_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record021_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record021_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00023.record021
