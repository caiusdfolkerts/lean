module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow26Part00009Data
public import GraphInputsRow26Part00009Frames
public import GraphInputsRow26Part00009Leaves
public import GraphInputsRow26Part00009Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00009.record011
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00009.record011
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨17, by decide⟩, ⟨18, by decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨31, by decide⟩, ⟨35, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨48, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨54, by decide⟩, ⟨62, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), 281509338546176, 4398113619968, 24779693555187712, (certNat% 3)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 4), 281509336449024, (certNat% 5), 24769800366456832, 9895604649984]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [24780246398926848, 285873090330624, (certNat% 6), (certNat% 7), 34393292800]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 8), 34930163712, 281474978807808, 24769800366456832, (certNat% 9)]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 10), (certNat% 11), 2818572288, 4512945476206592, 20266198591602688]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 12), 2818572288, 13743895347200, (certNat% 13), (certNat% 14), 24769798218973184]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨19, by decide⟩ c6 c3
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c7 c2
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨17, by decide⟩ c8 c1
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨18, by decide⟩ c9 c0
  c10
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00009.record011_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00009.record011_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00009.record011_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00009.record011_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00009.record011_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00009.record011_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00009.record011_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00009.record011_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00009.record011_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00009.record011

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00009.record012
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00009.record012
def vertexColumn : Fields := ⟨10, (certNat% 15)⟩
def kindColumn : Fields := ⟨3, (certNat% 16)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨18, by decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨26, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨35, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨43, by decide⟩, ⟨45, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨52, by decide⟩, ⟨61, by decide⟩, ⟨66, by decide⟩, ⟨71, by decide⟩, ⟨77, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 17), (certNat% 18), 2305843009213693952]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 19), 281509336449024, (certNat% 20), (certNat% 21)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨77, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 22), 2305843009213693952, 2148270080, 2199023255552]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 23), (certNat% 20), 2148270080, 2199023255552, (certNat% 21)]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨77, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c5 c2
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨52, by decide⟩ c6 c2
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c7 c2
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 24), 4503602311987200, (certNat% 25), 1075314688, 11544872091648, (certNat% 26)]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c9 c8
  c10
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00009.record012_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00009.record012_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00009.record012_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00009.record012_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00009.record012_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00009.record012_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00009.record012_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00009.record012_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00009.record012_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00009.record012
