module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow26Part00016Data
public import GraphInputsRow26Part00016Frames
public import GraphInputsRow26Part00016Leaves
public import GraphInputsRow26Part00016Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00016.record033
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record033
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨20, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨38, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨46, by decide⟩, ⟨56, by decide⟩, ⟨58, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨80, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), 74766790688768, (certNat% 3), (certNat% 4), 288241371267989504]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 5), 72058693683773440, 70368744177664, (certNat% 6), (certNat% 7)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 8), (certNat% 9), 13198434500608, 1408816381952, 72127962916323328]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 10), 72058693549555712, 8800387989504, (certNat% 9)]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 11), (certNat% 9), 13198434500608, 1134072692736, 72127962782105600]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨22, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 12), 72127962916323328, (certNat% 13), 288241375562956800, (certNat% 14)]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 15), (certNat% 3), (certNat% 16), 1134005583872, 70368748371968]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 17), 72058693750882304, (certNat% 18), 74766794883072, (certNat% 19), (certNat% 20)]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c9 c6
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c10 c5
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨21, by decide⟩ c11 c2
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c12 c1
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
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record033_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record033_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record033_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record033_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record033_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record033_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record033_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record033_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record033_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00016.record033

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00016.record064
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record064
def vertexColumn : Fields := ⟨10, (certNat% 21)⟩
def kindColumn : Fields := ⟨3, (certNat% 22)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨40, by decide⟩, ⟨45, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨73, by decide⟩, ⟨77, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 23), 99079333536071680, (certNat% 24), 844424930131968, 13402712491054596096]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [143835362114928640, (certNat% 25), (certNat% 26), (certNat% 27), 12682136550675316736]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 28), (certNat% 29), 81067507712, 12103423998558208, 130604560992436224]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 30), 3096225280688128, (certNat% 31), (certNat% 32), 12682136550675316736]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 33), 40532396646334464, (certNat% 32), 14987979559889010688]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 34), (certNat% 29), 123848989752688640, (certNat% 35), 11240984669916758016]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 36), 209782308864, (certNat% 37), (certNat% 38), 13258597302978740224]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 39), (certNat% 29), 140174538401906688, (certNat% 32), 12682136550675316736]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 40), (certNat% 41), (certNat% 42), 103582928868474880]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [18340909757268754432, (certNat% 43), (certNat% 29), 104145741382942720, (certNat% 35)]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c10 c9
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [9510195587761307648, (certNat% 43), (certNat% 44), (certNat% 45), 8646911284551352320]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 46), 139611725887438848, (certNat% 47), (certNat% 35), 72477573120, 8935141660703064064]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c13 c12
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c14 c11
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c15 c8
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c16 c7
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c17 c6
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c18 c3
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c19 c2
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c20 c1
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c21 c0
  c22
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record064_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record064_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record064_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record064_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record064_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record064_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record064_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record064_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record064_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00016.record064

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00016.record065
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record065
def vertexColumn : Fields := ⟨10, (certNat% 48)⟩
def kindColumn : Fields := ⟨3, (certNat% 49)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨19, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨26, by decide⟩, ⟨32, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨50, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨65, by decide⟩, ⟨69, by decide⟩, ⟨87, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 50), 1152956689063346176, (certNat% 51), 2314920852090519552, 34634616274944, 1134907106097364992]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record065_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record065_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record065_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record065_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record065_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record065_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record065_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record065_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record065_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00016.record065
