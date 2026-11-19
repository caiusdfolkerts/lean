module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow24Part00122Data
public import GraphInputsRow24Part00122Frames
public import GraphInputsRow24Part00122Leaves
public import GraphInputsRow24Part00122Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00122.record001
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record001
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨33, by decide⟩, ⟨35, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨46, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨68, by decide⟩, ⟨74, by decide⟩, ⟨76, by decide⟩, ⟨79, by decide⟩, ⟨81, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), 28147497738174464, (certNat% 3), (certNat% 4), 434597364041252864, 3816816640, 549755813888]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record001_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record001_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record001_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record001_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record001_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record001_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record001_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record001_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record001_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00122.record001

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00122.record003
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record003
def vertexColumn : Fields := ⟨10, (certNat% 5)⟩
def kindColumn : Fields := ⟨3, (certNat% 6)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨35, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨46, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨62, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨73, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 7), (certNat% 8), (certNat% 9), (certNat% 10), 274877906944]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 11), 4432406249472, 11258999336861696, (certNat% 12), 1374456643584]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 13), 11258999336861696, (certNat% 14), (certNat% 15), 1374456643584, (certNat% 16)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨69, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨62, by decide⟩ c3 c0
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 17), (certNat% 18), (certNat% 19), (certNat% 20), 72057594037927936]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 21), 13196287016960, 144115188075855872, (certNat% 22), (certNat% 23)]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 24), (certNat% 19), (certNat% 25), 216172782113783808, (certNat% 26), (certNat% 27)]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨52, by decide⟩ c7 c6
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨67, by decide⟩ c8 c5
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 28), (certNat% 29), (certNat% 30), 8796629893120, 85568392920039424, 1374792187904]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 31), 13228499271680, (certNat% 12), 2251800216338432, 1374389534720]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 32), (certNat% 33), 180143985094819840, (certNat% 8)]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 34), (certNat% 35), (certNat% 19), 144115188075855872, 290482175965396992]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c13 c12
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 36), 36033197749829632, 11258999471079424, (certNat% 30), 1374389534720, 144115188075855872]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c15 c14
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c16 c11
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 37), 180143987779174400, (certNat% 38), 4611687667694829568, 11269994184704, (certNat% 39)]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 40), (certNat% 41), (certNat% 42), (certNat% 43), 252201581817102336, 1374792187904, 15393162788864]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c19 c18
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨64, by decide⟩ c20 c17
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨67, by decide⟩ c21 c10
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c22 c9
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c23 c4
  c24
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record003_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record003_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record003_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record003_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record003_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record003_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record003_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record003_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record003_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00122.record003

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00122.record007
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record007
def vertexColumn : Fields := ⟨10, (certNat% 44)⟩
def kindColumn : Fields := ⟨3, (certNat% 45)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨33, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨45, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨59, by decide⟩, ⟨67, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨77, by decide⟩, ⟨79, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 46), 27021598032658432, (certNat% 47), (certNat% 48), (certNat% 49), 3298534883328]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 50), (certNat% 51), (certNat% 52), 27021597764222976]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 53), 18577348462903296, (certNat% 54), (certNat% 55), (certNat% 56)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨72, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 57), 576461164637061120, (certNat% 54), 21110623253299200, (certNat% 55), (certNat% 58)]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 59), 577586789665996800, (certNat% 60), 21110623257493504, (certNat% 54), (certNat% 61), 386555445248]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c7 c0
  c8
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record007_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record007_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record007_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record007_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record007_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record007_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record007_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record007_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record007_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00122.record007

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00122.record008
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record008
def vertexColumn : Fields := ⟨10, (certNat% 62)⟩
def kindColumn : Fields := ⟨3, (certNat% 63)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨58, by decide⟩, ⟨63, by decide⟩, ⟨65, by decide⟩, ⟨67, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 64), (certNat% 65), (certNat% 66), 9225623838815944704, 27866022694354944, (certNat% 67)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 68), (certNat% 69), (certNat% 70), (certNat% 71), 5100273664]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 72), (certNat% 73), 29273397577908224, 5100273664, 68719476736]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 74), (certNat% 75), 5100273664, 29554872554618880, (certNat% 76), 77309411328]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c4 c1
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 77), (certNat% 78), 4630511616, (certNat% 79), 9513854214967656448, 18295873486192640]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 80), (certNat% 81), (certNat% 82), 6979321856, 68987912192]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 83), (certNat% 84), 5100273664, (certNat% 85), (certNat% 86), 2147483648]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 87), (certNat% 88), 81432579932160, (certNat% 89), (certNat% 90)]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 91), 290482178112880640, 19984723363233792, (certNat% 92), 72568102977536, 4831838208]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 93), (certNat% 94), (certNat% 95), (certNat% 96), 844562369085440, 27021597764222976]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 97), (certNat% 98), 70442027057152, 29554872571396096, (certNat% 99), 2751463424, (certNat% 100)]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c13 c12
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨67, by decide⟩ c14 c11
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨23, by decide⟩ c15 c10
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c16 c9
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c17 c6
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c18 c5
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c19 c0
  c20
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record008_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record008_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record008_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record008_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record008_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record008_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record008_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record008_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record008_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00122.record008

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00122.record010
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record010
def vertexColumn : Fields := ⟨10, (certNat% 101)⟩
def kindColumn : Fields := ⟨3, (certNat% 102)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨52, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 103), 68987912192, 4971973988617027584, (certNat% 104), (certNat% 105)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 106), (certNat% 107), (certNat% 108), (certNat% 109), 7566047373982433280, (certNat% 110)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨65, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 111), (certNat% 104), (certNat% 112), 144115188075855872, (certNat% 113)]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [4976486349969293312, (certNat% 114), (certNat% 112), (certNat% 108), (certNat% 115), (certNat% 33)]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 116), (certNat% 117), 16777216000, (certNat% 118), (certNat% 119), 1099511627776]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 120), (certNat% 121), (certNat% 122), (certNat% 123)]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 124), 14545846272, (certNat% 122), (certNat% 125), 7009386627072, (certNat% 126)]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 127), (certNat% 128), 11844714496, (certNat% 129), 144115205322833920, 5260204364902957056]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 130), (certNat% 131), 4503599677702144, 6979321856]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 132), (certNat% 133), 7046430720, (certNat% 129), 7559142440960, 50331648]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c12 c11
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 134), 4503599677702144, (certNat% 135), 7559142440960, (certNat% 136), (certNat% 126)]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [870892064789757952, (certNat% 137), 7133701809754865664, (certNat% 138), (certNat% 139), (certNat% 33)]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 140), (certNat% 141), (certNat% 142), (certNat% 143)]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 144), (certNat% 145), 7559142440960, (certNat% 115), (certNat% 146), (certNat% 105)]
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨71, by decide⟩ c17 c16
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 147), 4402375032832, (certNat% 148), (certNat% 149), (certNat% 150), 9126805504]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 151), 4688247212092686336, 16676552704, (certNat% 122), (certNat% 152), 7559142440960, (certNat% 153)]
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨66, by decide⟩ c20 c19
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c21 c18
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨24, by decide⟩ c22 c15
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c23 c14
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c24 c13
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c25 c10
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c26 c9
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c27 c6
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c28 c5
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨23, by decide⟩ c29 c2
  c30
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record010_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record010_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record010_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record010_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record010_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record010_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record010_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record010_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record010_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00122.record010

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00122.record012
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record012
def vertexColumn : Fields := ⟨10, (certNat% 154)⟩
def kindColumn : Fields := ⟨3, (certNat% 155)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨44, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨61, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨78, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 156), (certNat% 157), 17867667931136, 2314850210615918592, 550829555712, 18014398509481984]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 158), 18577348462903296, (certNat% 159), (certNat% 160), 4303355904, 7146825580544]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 161), 2314867800654479360, (certNat% 162), 18014403412623360, (certNat% 163), 274877906944]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 164), (certNat% 163), 7696598171648, (certNat% 165), (certNat% 166), 1073741824]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 167), 27021597764222976, 2305843009213693952, (certNat% 163), (certNat% 168), (certNat% 169)]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 170), 2314867802801963008, (certNat% 171), 5435817984, 274877906944, 18577348462903296]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 172), (certNat% 159), 4672945389568, (certNat% 162), (certNat% 173), 18014402871558144, 1073741824]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨23, by decide⟩ c7 c4
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c8 c3
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c9 c2
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨65, by decide⟩ c10 c1
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c11 c0
  c12
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record012_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record012_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record012_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record012_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record012_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record012_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record012_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record012_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record012_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00122.record012

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00122.record006
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "1e86b29c671d25c9ca5ab1a66996359361d98e8b92e8791e279e174571725a95a4e9a65993969535475a362d2b61d275c358d9394d5334d331cd8b52ccb8ad2b1ae1b46c9b31e2719c9715c3723c1f741625492a85a0e0b8d1854958348d0b46384c5382c2b81c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "36da4d36db6d24db4db6db6934924d34934db4926da492489249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record006 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record006 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record006.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 33), (facetIndex 34), (facetIndex 68), (facetIndex 77)]))
 (.leaf ([(facetIndex 22), (facetIndex 23), (facetIndex 47), (facetIndex 48), (facetIndex 49), (facetIndex 50), (facetIndex 51)])))
 (.branch 3
 (.leaf ([(facetIndex 41), (facetIndex 42), (facetIndex 63), (facetIndex 80)]))
 (.leaf ([(facetIndex 28), (facetIndex 67), (facetIndex 69)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 39), (facetIndex 45), (facetIndex 79)]))
 (.leaf ([(facetIndex 25), (facetIndex 32), (facetIndex 43)])))
 (.branch 7
 (.leaf ([(facetIndex 26), (facetIndex 53), (facetIndex 54)]))
 (.branch 8
 (.leaf ([(facetIndex 27), (facetIndex 35)]))
 (.leaf ([(facetIndex 24)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "24000000000303000200000000660111110405220400070050003765811z16;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 9
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 29), (facetIndex 52), (facetIndex 55)]))
 (.leaf ([(facetIndex 40), (facetIndex 71), (facetIndex 72)])))
 (.branch 3
 (.leaf ([(facetIndex 30), (facetIndex 31), (facetIndex 57), (facetIndex 66), (facetIndex 76)]))
 (.branch 4
 (.leaf ([(facetIndex 56), (facetIndex 65), (facetIndex 81), (facetIndex 82)]))
 (.leaf ([(facetIndex 37), (facetIndex 58), (facetIndex 60)])))))
 (.branch 7
 (.branch 6
 (.leaf ([(facetIndex 59), (facetIndex 64), (facetIndex 84)]))
 (.leaf ([(facetIndex 70), (facetIndex 83)])))
 (.branch 8
 (.leaf ([(facetIndex 36), (facetIndex 38), (facetIndex 73), (facetIndex 74), (facetIndex 75)]))
 (.branch 9
 (.leaf ([(facetIndex 44), (facetIndex 61), (facetIndex 62)]))
 (.leaf ([(facetIndex 46), (facetIndex 78)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "5633009027771160002350884542300000000090800010747000022z1e;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 10
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped2_0000 : List Nat := [0]
def grouped2_0001 : List Nat := [0, 1]
def grouped2_0002 : List Nat := [0, 1, 2, 3]
def grouped2_0004 : List Nat := [1]
def grouped2_0005 : List Nat := [2]
def grouped2_0006 : List Nat := [2, 3]
def grouped2_0007 : List Nat := [3]
def grouped2_0008 : List Nat := [4]
def grouped2_0009 : List Nat := [4, 5]
def grouped2_0010 : List Nat := [4, 5, 6, 7, 8]
def grouped2_0011 : List Nat := [5]
def grouped2_0012 : List Nat := [6]
def grouped2_0013 : List Nat := [6, 7, 8]
def grouped2_0014 : List Nat := [7]
def grouped2_0015 : List Nat := [7, 8]
def grouped2_0016 : List Nat := [8]
def grouped3_0017 : List Nat := [0]
def grouped3_0018 : List Nat := [0, 1]
def grouped3_0019 : List Nat := [0, 1, 2, 3, 4]
def grouped3_0021 : List Nat := [1]
def grouped3_0022 : List Nat := [2]
def grouped3_0023 : List Nat := [2, 3, 4]
def grouped3_0024 : List Nat := [3]
def grouped3_0025 : List Nat := [3, 4]
def grouped3_0026 : List Nat := [4]
def grouped3_0027 : List Nat := [5]
def grouped3_0028 : List Nat := [5, 6]
def grouped3_0029 : List Nat := [5, 6, 7, 8, 9]
def grouped3_0030 : List Nat := [6]
def grouped3_0031 : List Nat := [7]
def grouped3_0032 : List Nat := [7, 8, 9]
def grouped3_0033 : List Nat := [8]
def grouped3_0034 : List Nat := [8, 9]
def grouped3_0035 : List Nat := [9]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record006 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record006_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00122.record006" "{\"atoms\":[{\"tag\":\"facet\",\"index\":0},{\"tag\":\"facet\",\"index\":3},{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group\",\"kind\":2,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0015\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0015\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group\",\"kind\":3,\"index\":9},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0018\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0025\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0025\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0023\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0023\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0019\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0019\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0028\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0028\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0034\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0032\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0029\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0029\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00122.record006" 93

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00122.record006" "{\"ridges\":[[4,35],[6,19],[7,19],[24,19],[24,35],[31,281],[32,11],[33,97],[34,296],[35,515],[38,392],[39,97],[42,19],[45,35],[45,97],[45,352],[53,81],[55,228],[56,392],[58,232],[60,417],[62,305],[63,448],[64,417],[68,266],[68,296],[74,390],[75,154],[76,792],[77,296],[78,392],[79,274],[79,352],[83,420],[84,232],[84,392]],\"owners\":[[32,11,[0,4,23,33,34,36,37,38],[5,22,30,31]],[35,515,[3,7,43],[5,28]],[53,81,[6,39,42,43,62],[14,25,52,63]],[33,97,[52,55,62,64],[8,27,39,45,58,59]],[39,97,[55,58,59,64],[8,27,33,45,52,62]],[45,97,[52,55,58],[8,27,33,39,59,62,64]],[68,266,[31,37,38,75,76,78],[18,34,66,70,77]],[34,296,[83,84],[18,59,60,68,77]],[68,296,[59,60,84],[18,34,77,83]],[77,296,[60,83],[18,34,59,68,84]],[79,274,[31,44,66,74,75,76],[19,40,42,72,80]],[45,352,[84],[20,59,62,64,77,79]],[79,352,[59,64,84],[20,45,62,77]],[63,448,[78,84],[21,46,61,64,80]],[75,154,[30,65],[]],[31,281,[56],[]],[38,392,[81,83,84],[56,60,61,70,75,78]],[56,392,[70,78,83,84],[38,60,61,75,81]],[78,392,[56,60,81,83],[38,61,70,75,84]],[84,392,[38,56,70,75,81],[60,61,78,83]],[62,305,[40],[]],[55,228,[],[]],[58,232,[84],[]],[84,232,[58],[]],[60,417,[64],[]],[64,417,[60],[]],[74,390,[70],[]],[76,792,[],[]],[83,420,[],[]]],\"edges\":[],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00122.record006" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00122.record006\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":false,\"clauses\":[[-7,-1],[-7,-2],[-7,-6],[-8,-7],[-9,-7],[-10,-7],[-14,-7],[-16,-13],[-20,-7],[-20,-8],[-20,-10],[-22,-8],[-24,-7],[-24,-20],[-24,-22],[-26,-15],[-26,-18],[-29,-7],[-39,-13],[-47,-7],[-47,-23],[-48,-47],[-13,1,3,6,14,15,17,18,19],[-4,-5,-7],[-5,-7,-23],[-3,-7,-26],[-16,2,5,24],[-28,4,20,23,24,35],[-14,27,30,35,37],[-20,30,32,33,37],[-26,27,30,32],[-40,12,18,19,43,44,46],[-15,50,51],[-40,33,34,51],[-45,34,50],[-47,12,25,39,42,43,44],[-26,51],[-47,33,37,51],[-36,46,51],[-43,11,38],[-12,31],[-19,49,50,51],[-31,41,46,50,51],[-46,31,34,49,50],[-51,19,31,41,43,49],[-35,21],[-30],[-32,51],[-51,32],[-34,37],[-37,34],[-42,41],[-44],[-50],[-52,14,15,40,45],[-53,22,23,36,48],[-54,20,26,47],[-55,8,13,24],[-56,9,28,29],[-57,10,16],[-58,7],[-59,52],[-60,53],[-61,59],[-61,60],[-62,54],[-62,55],[-63,57,58],[-64,57],[-64,58],[-66,56],[-65,63],[-66,64],[-67,62,66],[-68,62],[-67,65],[-68,66],[-69,61,68],[-69,67],[69],[-27,70],[-21,71],[-11,72],[-12,72],[-31,73],[-38,73],[-49,73],[-18,74],[-32,74],[-34,74],[-33,75],[-37,75],[-51,75],[-41,76],[-17,77],[-19,77],[-43,77],[-25,78],[-35,78],[-46,79],[-71,80],[-70,80],[-74,81],[-73,81],[-73,-74,82],[-81,83],[-82,84],[-72,83],[-83,85],[-84,86],[-80,85],[-75,87],[-75,-76,88],[-79,89],[-78,89],[-89,90],[-77,90],[-87,91],[-87,-90,92],[-88,92],[-85,-92,93],[-86,-91,93],[-93]],\"atoms\":[{\"tag\":\"facet\",\"index\":0},{\"tag\":\"facet\",\"index\":3},{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group\",\"index\":8,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group\",\"index\":9,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":24,\"b\":0},{\"tag\":\"incompatible\",\"a\":24,\"b\":3},{\"tag\":\"incompatible\",\"a\":24,\"b\":23},{\"tag\":\"incompatible\",\"a\":25,\"b\":24},{\"tag\":\"incompatible\",\"a\":26,\"b\":24},{\"tag\":\"incompatible\",\"a\":27,\"b\":24},{\"tag\":\"incompatible\",\"a\":33,\"b\":24},{\"tag\":\"incompatible\",\"a\":35,\"b\":32},{\"tag\":\"incompatible\",\"a\":39,\"b\":24},{\"tag\":\"incompatible\",\"a\":39,\"b\":25},{\"tag\":\"incompatible\",\"a\":39,\"b\":27},{\"tag\":\"incompatible\",\"a\":41,\"b\":25},{\"tag\":\"incompatible\",\"a\":43,\"b\":24},{\"tag\":\"incompatible\",\"a\":43,\"b\":39},{\"tag\":\"incompatible\",\"a\":43,\"b\":41},{\"tag\":\"incompatible\",\"a\":45,\"b\":34},{\"tag\":\"incompatible\",\"a\":45,\"b\":37},{\"tag\":\"incompatible\",\"a\":54,\"b\":24},{\"tag\":\"incompatible\",\"a\":66,\"b\":32},{\"tag\":\"incompatible\",\"a\":79,\"b\":24},{\"tag\":\"incompatible\",\"a\":79,\"b\":42},{\"tag\":\"incompatible\",\"a\":80,\"b\":79},{\"tag\":\"mate\",\"ridge\":11,\"a\":32,\"owners\":[0,4,23,33,34,36,37,38]},{\"tag\":\"three\",\"ridge\":19,\"vertices\":[6,7,24]},{\"tag\":\"three\",\"ridge\":19,\"vertices\":[7,24,42]},{\"tag\":\"three\",\"ridge\":35,\"vertices\":[4,24,45]},{\"tag\":\"mate\",\"ridge\":515,\"a\":35,\"owners\":[3,7,43]},{\"tag\":\"mate\",\"ridge\":81,\"a\":53,\"owners\":[6,39,42,43,62]},{\"tag\":\"mate\",\"ridge\":97,\"a\":33,\"owners\":[52,55,62,64]},{\"tag\":\"mate\",\"ridge\":97,\"a\":39,\"owners\":[55,58,59,64]},{\"tag\":\"mate\",\"ridge\":97,\"a\":45,\"owners\":[52,55,58]},{\"tag\":\"mate\",\"ridge\":266,\"a\":68,\"owners\":[31,37,38,75,76,78]},{\"tag\":\"mate\",\"ridge\":296,\"a\":34,\"owners\":[83,84]},{\"tag\":\"mate\",\"ridge\":296,\"a\":68,\"owners\":[59,60,84]},{\"tag\":\"mate\",\"ridge\":296,\"a\":77,\"owners\":[60,83]},{\"tag\":\"mate\",\"ridge\":274,\"a\":79,\"owners\":[31,44,66,74,75,76]},{\"tag\":\"mate\",\"ridge\":352,\"a\":45,\"owners\":[84]},{\"tag\":\"mate\",\"ridge\":352,\"a\":79,\"owners\":[59,64,84]},{\"tag\":\"mate\",\"ridge\":448,\"a\":63,\"owners\":[78,84]},{\"tag\":\"mate\",\"ridge\":154,\"a\":75,\"owners\":[30,65]},{\"tag\":\"mate\",\"ridge\":281,\"a\":31,\"owners\":[56]},{\"tag\":\"mate\",\"ridge\":392,\"a\":38,\"owners\":[81,83,84]},{\"tag\":\"mate\",\"ridge\":392,\"a\":56,\"owners\":[70,78,83,84]},{\"tag\":\"mate\",\"ridge\":392,\"a\":78,\"owners\":[56,60,81,83]},{\"tag\":\"mate\",\"ridge\":392,\"a\":84,\"owners\":[38,56,70,75,81]},{\"tag\":\"mate\",\"ridge\":305,\"a\":62,\"owners\":[40]},{\"tag\":\"mate\",\"ridge\":228,\"a\":55,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":232,\"a\":58,\"owners\":[84]},{\"tag\":\"mate\",\"ridge\":232,\"a\":84,\"owners\":[58]},{\"tag\":\"mate\",\"ridge\":417,\"a\":60,\"owners\":[64]},{\"tag\":\"mate\",\"ridge\":417,\"a\":64,\"owners\":[60]},{\"tag\":\"mate\",\"ridge\":390,\"a\":74,\"owners\":[70]},{\"tag\":\"mate\",\"ridge\":792,\"a\":76,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":420,\"a\":83,\"owners\":[]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[33,34,68,77],\"full_literals\":[-52,14,15,40,45]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[41,42,63,80],\"full_literals\":[-53,22,23,36,48]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[39,45,79],\"full_literals\":[-54,20,26,47]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[25,32,43],\"full_literals\":[-55,8,13,24]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[26,53,54],\"full_literals\":[-56,9,28,29]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[27,35],\"full_literals\":[-57,10,16]},{\"tag\":\"group_or\",\"kind\":2,\"index\":8,\"members\":[24],\"full_literals\":[-58,7]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-59,52,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-60,53,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-61,59,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-61,false,60],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-62,54,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-62,false,55],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0014\",\"right_name\":\"grouped2_0016\",\"joined_name\":\"grouped2_0015\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-63,57,58],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0014\",\"right_name\":\"grouped2_0016\",\"joined_name\":\"grouped2_0015\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-64,57,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0014\",\"right_name\":\"grouped2_0016\",\"joined_name\":\"grouped2_0015\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-64,false,58],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0013\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-66,56,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0013\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-65,false,63],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0013\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-66,false,64],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-67,62,66],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":1,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-68,62,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-67,false,65],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-68,false,66],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-69,61,68],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-69,false,67],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":52,\"full_literals\":[-27,70]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":40,\"full_literals\":[-21,71]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":30,\"full_literals\":[-11,72]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":31,\"full_literals\":[-12,72]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":56,\"full_literals\":[-31,73]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":65,\"full_literals\":[-38,73]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":81,\"full_literals\":[-49,73]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":37,\"full_literals\":[-18,74]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":58,\"full_literals\":[-32,74]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":60,\"full_literals\":[-34,74]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":59,\"full_literals\":[-33,75]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":64,\"full_literals\":[-37,75]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":84,\"full_literals\":[-51,75]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":70,\"full_literals\":[-41,76]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":36,\"full_literals\":[-17,77]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":38,\"full_literals\":[-19,77]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":75,\"full_literals\":[-43,77]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":44,\"full_literals\":[-25,78]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":62,\"full_literals\":[-35,78]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":78,\"full_literals\":[-46,79]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0018\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-71,80],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0018\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-70,false,80],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0024\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0025\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-74,81],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0024\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0025\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-73,false,81],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0024\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0025\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-73,-74,82],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0022\",\"right_name\":\"grouped3_0025\",\"joined_name\":\"grouped3_0023\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-81,83],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0022\",\"right_name\":\"grouped3_0025\",\"joined_name\":\"grouped3_0023\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-82,84],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0022\",\"right_name\":\"grouped3_0025\",\"joined_name\":\"grouped3_0023\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-72,false,83],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"grouped3_0019\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-83,85],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"grouped3_0019\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-84,86],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"grouped3_0019\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-80,false,85],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0027\",\"right_name\":\"grouped3_0030\",\"joined_name\":\"grouped3_0028\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-75,false,87],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0027\",\"right_name\":\"grouped3_0030\",\"joined_name\":\"grouped3_0028\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-75,-76,88],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0033\",\"right_name\":\"grouped3_0035\",\"joined_name\":\"grouped3_0034\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-79,89],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0033\",\"right_name\":\"grouped3_0035\",\"joined_name\":\"grouped3_0034\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-78,false,89],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0031\",\"right_name\":\"grouped3_0034\",\"joined_name\":\"grouped3_0032\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-89,90],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0031\",\"right_name\":\"grouped3_0034\",\"joined_name\":\"grouped3_0032\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-77,false,90],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0028\",\"right_name\":\"grouped3_0032\",\"joined_name\":\"grouped3_0029\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-87,false,91],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0028\",\"right_name\":\"grouped3_0032\",\"joined_name\":\"grouped3_0029\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-87,-90,92],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0028\",\"right_name\":\"grouped3_0032\",\"joined_name\":\"grouped3_0029\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-88,false,92],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0029\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-85,-92,93],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0029\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-86,-91,93],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true}]}"
  "124 67 0 80 79 0\n125 65 0 124 76 0\n126 63 0 125 72 0\n127 85 0 47 54 53 80 109 111 106 108 101 102 103 104 83 84 82 81 88 89 90 85 86 87 46 49 31 35 51 44 40 42 29 33 32 55 62 64 78 75 77 66 73 70 61 9 20 57 0\n128 -92 0 127 123 121 0\n129 -88 0 128 120 0\n130 33 51 37 0 80 124 47 54 38 50 37 48 33 35 34 30 57 66 74 75 73 78 70 64 61 62 7 55 0\n131 75 0 91 92 93 130 0\n132 87 0 131 112 0\n133 -76 0 131 129 113 0\n134 -90 0 132 128 119 0\n135 -41 0 133 94 0\n136 -89 0 134 116 0\n137 -77 0 134 117 0\n138 -42 0 135 52 0\n139 -79 0 136 114 0\n140 -78 0 136 115 0\n141 -17 0 137 95 0\n142 -19 0 137 96 0\n143 -43 0 137 97 0\n144 -46 0 139 100 0\n145 -25 0 140 98 0\n146 -35 0 140 99 0\n147 -66 0 146 71 73 69 70 61 2 5 6 9 13 18 60 27 59 24 25 28 0\n148 62 0 147 124 74 0\n149 54 0 148 66 0\n150 55 0 148 67 0\n151 91 0 132 118 0\n152 -68 0 147 77 0\n153 -86 0 151 123 122 0\n154 61 0 152 80 78 0\n155 -84 0 153 110 0\n156 60 0 154 65 0\n157 -82 0 155 107 0\n158 53 0 156 63 0\n159 -7 0 149 150 142 141 1 3 4 7 9 13 20 57 58 16 17 26 23 0\n160 -58 0 159 61 0\n161 57 0 160 126 68 0\n162 -51 0 157 142 143 135 49 89 105 85 87 45 0\n163 -26 0 162 37 0\n164 -31 0 162 135 54 144 43 0\n165 -36 0 162 144 39 0\n166 -12 0 164 41 0\n167 -20 0 161 150 10 11 14 60 58 8 0\n168 47 0 167 149 163 57 0\n169 -23 0 168 21 0\n170 -48 0 168 22 0\n171 39 0 168 145 166 138 143 53 36 0\n172 22 0 170 158 165 169 56 0\n173 -13 0 171 19 0\n174 -8 0 172 12 0\n175 -24 0 172 15 0\n176 0 173 175 174 150 58 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record006.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record006.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record006.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record006.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record006 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS noSame
  exact boundary_unsat S HS noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record006.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record006.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record006.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record006.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record006 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record006_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record006_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record006_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record006_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record006_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record006_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record006_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record006 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record006_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record006_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record006_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00122.record006

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00122.record018
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "2748f07c749aa8e87a59a361da2e1ba1e2785e0f9d19c5a9a66391e665596558d4751b49d1743d70da364d5334e331cd8b8ad2b2ac6b86c5b0ed4789d2785c970de0f23c4f8b21c5889a198560b81e586298649989465854558342d0758350d2318c9314c8b0ac1b11c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "d36db4d24924db49a4924924924d2492492492492249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record018 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record018 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record018.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record018.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record018.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 41), (facetIndex 43), (facetIndex 56), (facetIndex 58), (facetIndex 66), (facetIndex 67)]))
 (.leaf ([(facetIndex 38), (facetIndex 40), (facetIndex 44), (facetIndex 49), (facetIndex 63), (facetIndex 79)])))
 (.branch 3
 (.leaf ([(facetIndex 45), (facetIndex 46), (facetIndex 48), (facetIndex 54)]))
 (.leaf ([(facetIndex 35), (facetIndex 60), (facetIndex 61), (facetIndex 62), (facetIndex 64)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 33), (facetIndex 36), (facetIndex 42), (facetIndex 73)]))
 (.leaf ([(facetIndex 51), (facetIndex 52), (facetIndex 53), (facetIndex 55)])))
 (.branch 7
 (.leaf ([(facetIndex 34), (facetIndex 37), (facetIndex 39), (facetIndex 47), (facetIndex 74), (facetIndex 76)]))
 (.branch 8
 (.leaf ([(facetIndex 71), (facetIndex 77), (facetIndex 85)]))
 (.leaf ([(facetIndex 32), (facetIndex 57), (facetIndex 59), (facetIndex 72), (facetIndex 75)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "700000107686487000000313338080525550126221040161643648z20;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 9
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 68)]))
 (.branch 2
 (.leaf ([(facetIndex 70)]))
 (.leaf ([(facetIndex 82)]))))
 (.branch 5
 (.branch 4
 (.leaf ([(facetIndex 83)]))
 (.leaf ([(facetIndex 50), (facetIndex 65), (facetIndex 69)])))
 (.branch 6
 (.leaf ([(facetIndex 78), (facetIndex 80), (facetIndex 86)]))
 (.leaf ([(facetIndex 81), (facetIndex 84)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1466b51400000600200000000001z26;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 7
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped2_0000 : List Nat := [0]
def grouped2_0001 : List Nat := [0, 1]
def grouped2_0002 : List Nat := [0, 1, 2, 3]
def grouped2_0004 : List Nat := [1]
def grouped2_0005 : List Nat := [2]
def grouped2_0006 : List Nat := [2, 3]
def grouped2_0007 : List Nat := [3]
def grouped2_0008 : List Nat := [4]
def grouped2_0009 : List Nat := [4, 5]
def grouped2_0010 : List Nat := [4, 5, 6, 7, 8]
def grouped2_0011 : List Nat := [5]
def grouped2_0012 : List Nat := [6]
def grouped2_0013 : List Nat := [6, 7, 8]
def grouped2_0014 : List Nat := [7]
def grouped2_0015 : List Nat := [7, 8]
def grouped2_0016 : List Nat := [8]
def grouped3_0017 : List Nat := [0]
def grouped3_0018 : List Nat := [0, 1, 2]
def grouped3_0020 : List Nat := [1]
def grouped3_0021 : List Nat := [1, 2]
def grouped3_0022 : List Nat := [2]
def grouped3_0023 : List Nat := [3]
def grouped3_0024 : List Nat := [3, 4]
def grouped3_0025 : List Nat := [3, 4, 5, 6]
def grouped3_0026 : List Nat := [4]
def grouped3_0027 : List Nat := [5]
def grouped3_0028 : List Nat := [5, 6]
def grouped3_0029 : List Nat := [6]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record018 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record018_matrix_checked

def leafCount : Nat := 2
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaf0000 : List (Fin data.count) := [(facetIndex 10), (facetIndex 19), (facetIndex 26), (facetIndex 29), (facetIndex 47), (facetIndex 48), (facetIndex 62), (facetIndex 63), (facetIndex 67), (facetIndex 70), (facetIndex 73), (facetIndex 75), (facetIndex 83), (facetIndex 85)]
theorem leaf0000_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0000 = true := by
  decide +kernel
theorem leaf0000_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0000 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0000_counts_checked
def leaf0001 : List (Fin data.count) := [(facetIndex 6), (facetIndex 19), (facetIndex 26), (facetIndex 29), (facetIndex 47), (facetIndex 54), (facetIndex 62), (facetIndex 63), (facetIndex 67), (facetIndex 70), (facetIndex 73), (facetIndex 75), (facetIndex 83), (facetIndex 85)]
theorem leaf0001_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0001 = true := by
  decide +kernel
theorem leaf0001_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0001 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0001_counts_checked
def leavesTable : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 1
 (.leaf (leaf0000))
 (.leaf (leaf0001)))
def leaves (j : Fin leafCount) : List (Fin data.count) := leavesTable.get j.val

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00122.record018" "{\"atoms\":[{\"tag\":\"facet\",\"index\":0},{\"tag\":\"facet\",\"index\":1},{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group\",\"kind\":2,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0015\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0021\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0021\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0018\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0018\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0018\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0024\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0024\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0028\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0025\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0025\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00122.record018" 116

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00122.record018" "{\"ridges\":[[0,13],[7,81],[11,321],[12,385],[13,28],[15,517],[16,69],[21,529],[22,521],[22,545],[24,28],[26,22],[26,70],[26,84],[30,524],[30,532],[31,44],[31,524],[31,548],[32,13],[33,7],[33,13],[34,521],[34,524],[36,145],[39,7],[39,517],[40,7],[40,69],[40,70],[42,81],[47,11],[48,259],[48,385],[49,81],[52,81],[53,385],[54,385],[55,385],[57,28],[57,84],[59,41],[59,44],[62,81],[62,517],[63,289],[63,321],[63,352],[64,69],[64,545],[66,41],[66,529],[67,145],[67,521],[67,536],[68,41],[68,424],[70,81],[70,145],[70,321],[70,464],[71,44],[73,22],[73,28],[75,70],[77,84],[79,100],[82,424],[83,464],[85,28],[85,548],[85,552],[86,624]],\"owners\":[[47,11,[0,4,6,32,42,48],[5,34,43,44,46]],[0,13,[13,14,15,57,58,59],[32,33]],[32,13,[13,14,15,58],[0,33,57,59]],[33,13,[13,14,15,57,59],[0,32,58]],[26,22,[1,24,35,36,37,71,73,74,78],[77]],[73,22,[1,26,35,37,77,78],[24,36,71,74]],[7,81,[16,57,60,62,65,69,70],[42,49,51,52]],[49,81,[16,57,62,70],[7,42,51,52,60,65,69]],[52,81,[16,57,60,62,65,69],[7,42,49,51,70]],[70,81,[7,16,42,49,57,60,62,65,69],[51,52]],[48,259,[10,11,38,40,52],[12,46,53]],[63,289,[10,46,54,68],[23,38]],[12,385,[68,70],[48,53,54,55]],[48,385,[70],[12,53,54,55,68]],[53,385,[68],[12,48,54,55,70]],[54,385,[70],[12,48,53,55,68]],[55,385,[68],[12,48,53,54,70]],[62,517,[15,19,34,39],[17,37,64]],[26,84,[16,57,60,62,84,86],[72,77]],[57,84,[26,77,86],[16,60,62,72,84]],[77,84,[16,57,62],[26,60,72,84,86]],[21,529,[17,37,50,61,62,69],[43,66,67]],[66,529,[17,37,62],[21,43,50,61,67,69]],[30,532,[17,37,61,62,78,86],[74,85]],[79,100,[18,59,60,64,84,86],[27,63,75,77]],[22,545,[19,39,50,61,64,69],[47,66]],[64,545,[22,47,50,66],[19,39,61,69]],[31,548,[19,39,61,64,78,86],[76,85]],[85,548,[19,39,64],[31,61,76,78,86]],[67,536,[30,74,81,85],[21,43,66]],[85,552,[22,47],[31,66,76,81]],[63,352,[29],[23,79]],[68,424,[82],[]],[82,424,[68],[]],[86,624,[69],[]],[70,464,[83],[]],[83,464,[70],[]]],\"edges\":[[31,[7,16,26,42,49,51,52,57,60,62,65,69,70,72,77,80,83,84,86]],[34,[17,21,30,37,43,50,61,62,66,67,69,74,78,81,85,86]],[38,[19,22,31,39,47,50,61,64,66,69,76,78,81,85,86]],[42,[12,48,53,54,55,68,70,82,83]]],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00122.record018" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00122.record018\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-25,-23],[-28,-9],[-28,-12],[-28,-26],[-30,-10],[-30,-14],[-30,-15],[-30,-23],[-30,-25],[-30,-26],[-30,-29],[-31,-5],[-32,-25],[-33,-23],[-33,-28],[-34,-25],[-34,-27],[-35,-30],[-38,-10],[-38,-24],[-38,-25],[-38,-29],[-38,-34],[-38,-35],[-38,-36],[-38,-37],[-42,-28],[-45,-6],[-47,-25],[-48,-2],[-48,-13],[-48,-25],[-48,-26],[-48,-27],[-48,-28],[-48,-33],[-48,-34],[-48,-35],[-49,-25],[-49,-27],[-49,-33],[-50,-15],[-50,-29],[-50,-30],[-50,-35],[-50,-38],[-51,-28],[-51,-30],[-51,-48],[-52,-15],[-52,-25],[-52,-28],[-52,-30],[-52,-48],[-52,-50],[-53,-2],[-53,-9],[-53,-27],[-53,-28],[-53,-48],[-53,-49],[-54,-30],[-54,-50],[-55,-10],[-55,-15],[-55,-29],[-55,-30],[-55,-50],[-55,-51],[-55,-52],[-55,-53],[-55,-54],[-57,-25],[-58,-33],[-58,-48],[-59,-36],[-59,-37],[-59,-38],[-59,-39],[-59,-45],[-61,-42],[-61,-43],[-62,-23],[-62,-24],[-62,-25],[-62,-26],[-62,-51],[-62,-52],[-62,-57],[-63,-28],[-63,-33],[-63,-62],[-64,-3],[-64,-33],[-64,-49],[-64,-62],[-64,-63],[-65,-25],[-65,-48],[-65,-62],[-65,-63],[-66,-30],[-66,-33],[-66,-35],[-66,-62],[-67,-25],[-67,-50],[-67,-62],[-67,-66],[-68,-23],[-68,-26],[-68,-31],[-68,-40],[-68,-51],[-68,-52],[-68,-63],[-68,-66],[-70,-66],[-70,-68],[-76,-11],[-76,-25],[-76,-26],[-76,-32],[-76,-40],[-76,-47],[-76,-51],[-76,-52],[-76,-57],[-76,-62],[-76,-65],[-76,-67],[-76,-68],[-24,-30,-31],[-38,1,3,4,23,33,39],[-1,9,10,11,48,49,50],[-23,9,10,11,49],[-24,9,10,11,48,50],[-19,2,18,26,27,28,62,64,65,69],[-64,2,19,26,28,68,69],[-12,-31,-55],[-19,-31,-66],[-50,-57,-59],[-5,12,48,51,53,56,60,61],[-40,12,48,53,61],[-43,12,48,51,53,56,60],[-61,5,12,33,40,48,51,53,56,60],[-33,-53,-61],[-27,-58,-61],[-39,6,7,29,31,43],[-54,6,37,45,59],[-7,-54,-61],[-8,59,61],[-39,61],[-44,59],[-45,61],[-46,59],[-9,-64,-76],[-18,-48,-76],[-48,-64,-76],[-22,-50,-62],[-53,11,15,25,30],[-11,-30,-53],[-17,-25,-58],[-21,-22,-25],[-19,12,48,51,53,75,77],[-48,19,68,77],[-68,12,48,53],[-16,13,28,41,52,53,60],[-57,13,28,53],[-21,13,28,52,53,69,77],[-70,14,50,51,55,75,77],[-17,15,30,41,52,55,60],[-55,17,38,41,57],[-22,15,30,52,55,69,77],[-76,15,30,55],[-58,21,65,72,76],[-76,17,38],[-54,20],[-59,73],[-73,59],[-77,60],[-61,74],[-74,61],[-78,32,34,47,49,57,58],[-79,29,31,35,40,54,70],[-80,36,37,39,45],[-81,26,51,52,53,55],[-82,24,27,33,64],[-83,42,43,44,46],[-84,25,28,30,38,65,67],[-85,62,68,76],[-86,23,48,50,63,66],[-87,78],[-87,79],[-88,80,81],[-89,80],[-89,81],[-91,87],[-90,88],[-91,89],[-92,82,83],[-93,82],[-93,83],[-94,85],[-94,86],[-95,84],[-95,94],[-96,92],[-96,93,95],[-97,93],[-97,95],[-98,90],[-98,91,97],[-98,96],[98],[-99,59],[-59,99],[-100,61],[-61,100],[-101,73],[-73,101],[-74,102],[-41,103],[-56,103],[-60,103],[-69,104],[-71,104],[-77,104],[-72,105],[-75,105],[-106,100,101],[-101,106],[-100,106],[-100,-101,107],[-108,99,106],[-106,108],[-99,108],[-99,-106,109],[-99,-107,110],[-103,111],[-102,111],[-102,-103,112],[-105,113],[-104,113],[-113,114],[-111,114],[-111,-113,115],[-112,115],[-108,-115,116],[-109,-114,116],[-110,116],[-116],[-6,-15,-19,-20,-38,-39,-53,-54,-58,-61,-64,-66,-74,-76],[-4,-15,-19,-20,-38,-45,-53,-54,-58,-61,-64,-66,-74,-76],[5,12,19,33,40,42,43,48,51,53,56,60,61,63,68,71,74,75,77],[13,16,21,28,34,41,52,53,57,58,60,65,69,72,76,77],[15,17,22,30,38,41,52,55,57,60,67,69,72,76,77],[8,39,44,45,46,59,61,73,74]],\"atoms\":[{\"tag\":\"facet\",\"index\":0},{\"tag\":\"facet\",\"index\":1},{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group\",\"index\":8,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":34,\"b\":32},{\"tag\":\"incompatible\",\"a\":37,\"b\":13},{\"tag\":\"incompatible\",\"a\":37,\"b\":16},{\"tag\":\"incompatible\",\"a\":37,\"b\":35},{\"tag\":\"incompatible\",\"a\":39,\"b\":14},{\"tag\":\"incompatible\",\"a\":39,\"b\":18},{\"tag\":\"incompatible\",\"a\":39,\"b\":19},{\"tag\":\"incompatible\",\"a\":39,\"b\":32},{\"tag\":\"incompatible\",\"a\":39,\"b\":34},{\"tag\":\"incompatible\",\"a\":39,\"b\":35},{\"tag\":\"incompatible\",\"a\":39,\"b\":38},{\"tag\":\"incompatible\",\"a\":40,\"b\":7},{\"tag\":\"incompatible\",\"a\":41,\"b\":34},{\"tag\":\"incompatible\",\"a\":42,\"b\":32},{\"tag\":\"incompatible\",\"a\":42,\"b\":37},{\"tag\":\"incompatible\",\"a\":43,\"b\":34},{\"tag\":\"incompatible\",\"a\":43,\"b\":36},{\"tag\":\"incompatible\",\"a\":44,\"b\":39},{\"tag\":\"incompatible\",\"a\":47,\"b\":14},{\"tag\":\"incompatible\",\"a\":47,\"b\":33},{\"tag\":\"incompatible\",\"a\":47,\"b\":34},{\"tag\":\"incompatible\",\"a\":47,\"b\":38},{\"tag\":\"incompatible\",\"a\":47,\"b\":43},{\"tag\":\"incompatible\",\"a\":47,\"b\":44},{\"tag\":\"incompatible\",\"a\":47,\"b\":45},{\"tag\":\"incompatible\",\"a\":47,\"b\":46},{\"tag\":\"incompatible\",\"a\":51,\"b\":37},{\"tag\":\"incompatible\",\"a\":54,\"b\":10},{\"tag\":\"incompatible\",\"a\":56,\"b\":34},{\"tag\":\"incompatible\",\"a\":57,\"b\":1},{\"tag\":\"incompatible\",\"a\":57,\"b\":17},{\"tag\":\"incompatible\",\"a\":57,\"b\":34},{\"tag\":\"incompatible\",\"a\":57,\"b\":35},{\"tag\":\"incompatible\",\"a\":57,\"b\":36},{\"tag\":\"incompatible\",\"a\":57,\"b\":37},{\"tag\":\"incompatible\",\"a\":57,\"b\":42},{\"tag\":\"incompatible\",\"a\":57,\"b\":43},{\"tag\":\"incompatible\",\"a\":57,\"b\":44},{\"tag\":\"incompatible\",\"a\":58,\"b\":34},{\"tag\":\"incompatible\",\"a\":58,\"b\":36},{\"tag\":\"incompatible\",\"a\":58,\"b\":42},{\"tag\":\"incompatible\",\"a\":59,\"b\":19},{\"tag\":\"incompatible\",\"a\":59,\"b\":38},{\"tag\":\"incompatible\",\"a\":59,\"b\":39},{\"tag\":\"incompatible\",\"a\":59,\"b\":44},{\"tag\":\"incompatible\",\"a\":59,\"b\":47},{\"tag\":\"incompatible\",\"a\":60,\"b\":37},{\"tag\":\"incompatible\",\"a\":60,\"b\":39},{\"tag\":\"incompatible\",\"a\":60,\"b\":57},{\"tag\":\"incompatible\",\"a\":61,\"b\":19},{\"tag\":\"incompatible\",\"a\":61,\"b\":34},{\"tag\":\"incompatible\",\"a\":61,\"b\":37},{\"tag\":\"incompatible\",\"a\":61,\"b\":39},{\"tag\":\"incompatible\",\"a\":61,\"b\":57},{\"tag\":\"incompatible\",\"a\":61,\"b\":59},{\"tag\":\"incompatible\",\"a\":62,\"b\":1},{\"tag\":\"incompatible\",\"a\":62,\"b\":13},{\"tag\":\"incompatible\",\"a\":62,\"b\":36},{\"tag\":\"incompatible\",\"a\":62,\"b\":37},{\"tag\":\"incompatible\",\"a\":62,\"b\":57},{\"tag\":\"incompatible\",\"a\":62,\"b\":58},{\"tag\":\"incompatible\",\"a\":63,\"b\":39},{\"tag\":\"incompatible\",\"a\":63,\"b\":59},{\"tag\":\"incompatible\",\"a\":64,\"b\":14},{\"tag\":\"incompatible\",\"a\":64,\"b\":19},{\"tag\":\"incompatible\",\"a\":64,\"b\":38},{\"tag\":\"incompatible\",\"a\":64,\"b\":39},{\"tag\":\"incompatible\",\"a\":64,\"b\":59},{\"tag\":\"incompatible\",\"a\":64,\"b\":60},{\"tag\":\"incompatible\",\"a\":64,\"b\":61},{\"tag\":\"incompatible\",\"a\":64,\"b\":62},{\"tag\":\"incompatible\",\"a\":64,\"b\":63},{\"tag\":\"incompatible\",\"a\":66,\"b\":34},{\"tag\":\"incompatible\",\"a\":67,\"b\":42},{\"tag\":\"incompatible\",\"a\":67,\"b\":57},{\"tag\":\"incompatible\",\"a\":68,\"b\":45},{\"tag\":\"incompatible\",\"a\":68,\"b\":46},{\"tag\":\"incompatible\",\"a\":68,\"b\":47},{\"tag\":\"incompatible\",\"a\":68,\"b\":48},{\"tag\":\"incompatible\",\"a\":68,\"b\":54},{\"tag\":\"incompatible\",\"a\":70,\"b\":51},{\"tag\":\"incompatible\",\"a\":70,\"b\":52},{\"tag\":\"incompatible\",\"a\":71,\"b\":32},{\"tag\":\"incompatible\",\"a\":71,\"b\":33},{\"tag\":\"incompatible\",\"a\":71,\"b\":34},{\"tag\":\"incompatible\",\"a\":71,\"b\":35},{\"tag\":\"incompatible\",\"a\":71,\"b\":60},{\"tag\":\"incompatible\",\"a\":71,\"b\":61},{\"tag\":\"incompatible\",\"a\":71,\"b\":66},{\"tag\":\"incompatible\",\"a\":72,\"b\":37},{\"tag\":\"incompatible\",\"a\":72,\"b\":42},{\"tag\":\"incompatible\",\"a\":72,\"b\":71},{\"tag\":\"incompatible\",\"a\":73,\"b\":4},{\"tag\":\"incompatible\",\"a\":73,\"b\":42},{\"tag\":\"incompatible\",\"a\":73,\"b\":58},{\"tag\":\"incompatible\",\"a\":73,\"b\":71},{\"tag\":\"incompatible\",\"a\":73,\"b\":72},{\"tag\":\"incompatible\",\"a\":74,\"b\":34},{\"tag\":\"incompatible\",\"a\":74,\"b\":57},{\"tag\":\"incompatible\",\"a\":74,\"b\":71},{\"tag\":\"incompatible\",\"a\":74,\"b\":72},{\"tag\":\"incompatible\",\"a\":75,\"b\":39},{\"tag\":\"incompatible\",\"a\":75,\"b\":42},{\"tag\":\"incompatible\",\"a\":75,\"b\":44},{\"tag\":\"incompatible\",\"a\":75,\"b\":71},{\"tag\":\"incompatible\",\"a\":76,\"b\":34},{\"tag\":\"incompatible\",\"a\":76,\"b\":59},{\"tag\":\"incompatible\",\"a\":76,\"b\":71},{\"tag\":\"incompatible\",\"a\":76,\"b\":75},{\"tag\":\"incompatible\",\"a\":77,\"b\":32},{\"tag\":\"incompatible\",\"a\":77,\"b\":35},{\"tag\":\"incompatible\",\"a\":77,\"b\":40},{\"tag\":\"incompatible\",\"a\":77,\"b\":49},{\"tag\":\"incompatible\",\"a\":77,\"b\":60},{\"tag\":\"incompatible\",\"a\":77,\"b\":61},{\"tag\":\"incompatible\",\"a\":77,\"b\":72},{\"tag\":\"incompatible\",\"a\":77,\"b\":75},{\"tag\":\"incompatible\",\"a\":79,\"b\":75},{\"tag\":\"incompatible\",\"a\":79,\"b\":77},{\"tag\":\"incompatible\",\"a\":85,\"b\":15},{\"tag\":\"incompatible\",\"a\":85,\"b\":34},{\"tag\":\"incompatible\",\"a\":85,\"b\":35},{\"tag\":\"incompatible\",\"a\":85,\"b\":41},{\"tag\":\"incompatible\",\"a\":85,\"b\":49},{\"tag\":\"incompatible\",\"a\":85,\"b\":56},{\"tag\":\"incompatible\",\"a\":85,\"b\":60},{\"tag\":\"incompatible\",\"a\":85,\"b\":61},{\"tag\":\"incompatible\",\"a\":85,\"b\":66},{\"tag\":\"incompatible\",\"a\":85,\"b\":71},{\"tag\":\"incompatible\",\"a\":85,\"b\":74},{\"tag\":\"incompatible\",\"a\":85,\"b\":76},{\"tag\":\"incompatible\",\"a\":85,\"b\":77},{\"tag\":\"three\",\"ridge\":7,\"vertices\":[33,39,40]},{\"tag\":\"mate\",\"ridge\":11,\"a\":47,\"owners\":[0,4,6,32,42,48]},{\"tag\":\"mate\",\"ridge\":13,\"a\":0,\"owners\":[13,14,15,57,58,59]},{\"tag\":\"mate\",\"ridge\":13,\"a\":32,\"owners\":[13,14,15,58]},{\"tag\":\"mate\",\"ridge\":13,\"a\":33,\"owners\":[13,14,15,57,59]},{\"tag\":\"mate\",\"ridge\":22,\"a\":26,\"owners\":[1,24,35,36,37,71,73,74,78]},{\"tag\":\"mate\",\"ridge\":22,\"a\":73,\"owners\":[1,26,35,37,77,78]},{\"tag\":\"three\",\"ridge\":69,\"vertices\":[16,40,64]},{\"tag\":\"three\",\"ridge\":70,\"vertices\":[26,40,75]},{\"tag\":\"three\",\"ridge\":41,\"vertices\":[59,66,68]},{\"tag\":\"mate\",\"ridge\":81,\"a\":7,\"owners\":[16,57,60,62,65,69,70]},{\"tag\":\"mate\",\"ridge\":81,\"a\":49,\"owners\":[16,57,62,70]},{\"tag\":\"mate\",\"ridge\":81,\"a\":52,\"owners\":[16,57,60,62,65,69]},{\"tag\":\"mate\",\"ridge\":81,\"a\":70,\"owners\":[7,16,42,49,57,60,62,65,69]},{\"tag\":\"three\",\"ridge\":81,\"vertices\":[42,62,70]},{\"tag\":\"three\",\"ridge\":145,\"vertices\":[36,67,70]},{\"tag\":\"mate\",\"ridge\":259,\"a\":48,\"owners\":[10,11,38,40,52]},{\"tag\":\"mate\",\"ridge\":289,\"a\":63,\"owners\":[10,46,54,68]},{\"tag\":\"three\",\"ridge\":321,\"vertices\":[11,63,70]},{\"tag\":\"mate\",\"ridge\":385,\"a\":12,\"owners\":[68,70]},{\"tag\":\"mate\",\"ridge\":385,\"a\":48,\"owners\":[70]},{\"tag\":\"mate\",\"ridge\":385,\"a\":53,\"owners\":[68]},{\"tag\":\"mate\",\"ridge\":385,\"a\":54,\"owners\":[70]},{\"tag\":\"mate\",\"ridge\":385,\"a\":55,\"owners\":[68]},{\"tag\":\"three\",\"ridge\":28,\"vertices\":[13,73,85]},{\"tag\":\"three\",\"ridge\":28,\"vertices\":[24,57,85]},{\"tag\":\"three\",\"ridge\":28,\"vertices\":[57,73,85]},{\"tag\":\"three\",\"ridge\":44,\"vertices\":[31,59,71]},{\"tag\":\"mate\",\"ridge\":517,\"a\":62,\"owners\":[15,19,34,39]},{\"tag\":\"three\",\"ridge\":517,\"vertices\":[15,39,62]},{\"tag\":\"three\",\"ridge\":521,\"vertices\":[22,34,67]},{\"tag\":\"three\",\"ridge\":524,\"vertices\":[30,31,34]},{\"tag\":\"mate\",\"ridge\":84,\"a\":26,\"owners\":[16,57,60,62,84,86]},{\"tag\":\"mate\",\"ridge\":84,\"a\":57,\"owners\":[26,77,86]},{\"tag\":\"mate\",\"ridge\":84,\"a\":77,\"owners\":[16,57,62]},{\"tag\":\"mate\",\"ridge\":529,\"a\":21,\"owners\":[17,37,50,61,62,69]},{\"tag\":\"mate\",\"ridge\":529,\"a\":66,\"owners\":[17,37,62]},{\"tag\":\"mate\",\"ridge\":532,\"a\":30,\"owners\":[17,37,61,62,78,86]},{\"tag\":\"mate\",\"ridge\":100,\"a\":79,\"owners\":[18,59,60,64,84,86]},{\"tag\":\"mate\",\"ridge\":545,\"a\":22,\"owners\":[19,39,50,61,64,69]},{\"tag\":\"mate\",\"ridge\":545,\"a\":64,\"owners\":[22,47,50,66]},{\"tag\":\"mate\",\"ridge\":548,\"a\":31,\"owners\":[19,39,61,64,78,86]},{\"tag\":\"mate\",\"ridge\":548,\"a\":85,\"owners\":[19,39,64]},{\"tag\":\"mate\",\"ridge\":536,\"a\":67,\"owners\":[30,74,81,85]},{\"tag\":\"mate\",\"ridge\":552,\"a\":85,\"owners\":[22,47]},{\"tag\":\"mate\",\"ridge\":352,\"a\":63,\"owners\":[29]},{\"tag\":\"mate\",\"ridge\":424,\"a\":68,\"owners\":[82]},{\"tag\":\"mate\",\"ridge\":424,\"a\":82,\"owners\":[68]},{\"tag\":\"mate\",\"ridge\":624,\"a\":86,\"owners\":[69]},{\"tag\":\"mate\",\"ridge\":464,\"a\":70,\"owners\":[83]},{\"tag\":\"mate\",\"ridge\":464,\"a\":83,\"owners\":[70]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[41,43,56,58,66,67],\"full_literals\":[-78,32,34,47,49,57,58]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[38,40,44,49,63,79],\"full_literals\":[-79,29,31,35,40,54,70]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[45,46,48,54],\"full_literals\":[-80,36,37,39,45]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[35,60,61,62,64],\"full_literals\":[-81,26,51,52,53,55]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[33,36,42,73],\"full_literals\":[-82,24,27,33,64]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[51,52,53,55],\"full_literals\":[-83,42,43,44,46]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[34,37,39,47,74,76],\"full_literals\":[-84,25,28,30,38,65,67]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[71,77,85],\"full_literals\":[-85,62,68,76]},{\"tag\":\"group_or\",\"kind\":2,\"index\":8,\"members\":[32,57,59,72,75],\"full_literals\":[-86,23,48,50,63,66]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-87,78,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-87,false,79],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-88,80,81],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-89,80,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-89,false,81],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-91,87,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-90,false,88],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-91,false,89],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-92,82,83],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-93,82,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-93,false,83],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0014\",\"right_name\":\"grouped2_0016\",\"joined_name\":\"grouped2_0015\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-94,85,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0014\",\"right_name\":\"grouped2_0016\",\"joined_name\":\"grouped2_0015\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-94,false,86],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0013\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-95,84,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0013\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-95,false,94],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":0,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-96,92,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-96,93,95],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":1,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-97,93,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-97,false,95],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":2,\"b\":5,\"direction\":\"backward\",\"full_literals\":[-98,90,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-98,91,97],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-98,false,96],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":3,\"index\":0,\"members\":[68],\"full_literals\":[-99,59]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":68,\"full_literals\":[-59,99]},{\"tag\":\"group_or\",\"kind\":3,\"index\":1,\"members\":[70],\"full_literals\":[-100,61]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":70,\"full_literals\":[-61,100]},{\"tag\":\"group_or\",\"kind\":3,\"index\":2,\"members\":[82],\"full_literals\":[-101,73]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":82,\"full_literals\":[-73,101]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":83,\"full_literals\":[-74,102]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":50,\"full_literals\":[-41,103]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":65,\"full_literals\":[-56,103]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":69,\"full_literals\":[-60,103]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":78,\"full_literals\":[-69,104]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":80,\"full_literals\":[-71,104]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":86,\"full_literals\":[-77,104]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":81,\"full_literals\":[-72,105]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":84,\"full_literals\":[-75,105]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0021\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-106,100,101],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0021\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-101,106],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0021\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-100,false,106],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0021\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-100,-101,107],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0018\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-108,99,106],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0018\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-106,108],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0018\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-99,false,108],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0018\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-99,-106,109],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0018\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-99,-107,110],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0024\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-103,111],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0024\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-102,false,111],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0024\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-102,-103,112],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0027\",\"right_name\":\"grouped3_0029\",\"joined_name\":\"grouped3_0028\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-105,113],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0027\",\"right_name\":\"grouped3_0029\",\"joined_name\":\"grouped3_0028\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-104,false,113],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0024\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0025\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-113,114],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0024\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0025\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-111,false,114],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0024\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0025\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-111,-113,115],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0024\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0025\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-112,false,115],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0025\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-108,-115,116],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0025\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-109,-114,116],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0025\",\"joined_name\":\"groupKind3\",\"a\":3,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-110,false,116],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"block\",\"leaf\":0,\"vertices\":[10,19,26,29,47,48,62,63,67,70,73,75,83,85]},{\"tag\":\"block\",\"leaf\":1,\"vertices\":[6,19,26,29,47,54,62,63,67,70,73,75,83,85]},{\"tag\":\"edge\",\"edge\":31,\"owners\":[7,16,26,42,49,51,52,57,60,62,65,69,70,72,77,80,83,84,86]},{\"tag\":\"edge\",\"edge\":34,\"owners\":[17,21,30,37,43,50,61,62,66,67,69,74,78,81,85,86]},{\"tag\":\"edge\",\"edge\":38,\"owners\":[19,22,31,39,47,50,61,64,66,69,76,78,81,85,86]},{\"tag\":\"edge\",\"edge\":42,\"owners\":[12,48,53,54,55,68,70,82,83]}]}"
  "259 90 0 215 212 0\n260 96 0 215 214 0\n261 88 0 259 199 0\n262 92 0 260 208 0\n263 -110 0 252 251 0\n264 108 0 236 237 232 233 217 221 219 152 154 156 153 155 183 258 0\n265 -115 0 264 252 249 0\n266 -112 0 265 248 0\n267 106 0 264 232 235 221 216 179 0\n268 -25 15 59 0 266 265 267 215 154 180 220 231 218 82 156 81 189 203 210 213 198 193 182 222 241 247 244 226 243 229 242 225 181 223 9 13 16 21 29 39 51 73 98 106 121 184 176 163 164 173 257 0\n269 -68 55 52 50 23 93 0 260 215 210 213 200 197 209 207 205 111 114 116 117 187 192 60 0\n270 6 -76 -15 59 0 265 262 260 267 215 154 180 220 231 218 82 156 81 189 203 210 213 198 194 209 206 131 130 7 121 122 50 200 197 65 126 187 59 190 24 124 22 42 60 207 205 120 61 57 19 136 201 58 147 20 188 97 192 182 222 241 247 244 226 132 56 139 141 118 185 178 151 93 193 123 125 128 23 184 135 26 149 150 134 254 0\n271 -76 -15 59 0 262 260 265 267 215 65 50 42 7 154 180 220 231 218 82 156 81 189 203 210 213 200 197 196 198 194 193 182 222 241 247 244 226 209 207 205 206 201 120 121 122 123 124 125 126 128 130 131 132 187 56 57 58 59 60 61 147 190 19 20 22 23 24 25 26 136 188 184 97 139 192 141 118 185 178 270 28 253 186 0\n272 23 76 55 52 50 93 0 260 215 210 213 200 197 209 207 205 204 269 191 86 87 92 105 187 192 60 0\n273 -15 59 0 267 260 154 180 220 231 218 82 156 81 189 203 209 207 204 42 50 65 271 272 83 110 191 0\n274 -23 76 -85 0 83 110 191 0\n275 -48 -62 -82 0 96 84 34 36 188 0\n276 38 57 15 77 30 41 22 55 52 60 67 69 72 76 0 257 172 0\n277 -62 76 59 0 262 266 265 267 260 154 180 220 231 218 82 156 81 189 203 209 207 204 274 273 182 222 241 247 244 226 243 229 205 242 225 181 223 201 88 89 92 105 108 275 192 44 46 68 160 276 0\n278 -50 -68 -79 0 119 113 112 43 45 63 185 0\n279 76 59 0 260 267 215 154 180 220 231 218 82 156 81 189 203 210 213 198 194 209 207 205 204 274 277 191 112 113 115 116 117 119 278 272 192 66 72 38 185 0\n280 -48 59 0 266 267 265 279 132 130 129 122 180 220 231 218 182 222 241 247 244 226 242 225 181 30 34 35 158 159 166 138 0\n281 -50 59 0 279 273 44 68 175 0\n282 -38 27 64 59 0 262 267 215 279 128 125 123 154 180 220 231 218 82 156 81 189 203 210 213 198 193 201 20 23 188 41 74 184 0\n283 -30 27 64 59 0 262 266 265 267 215 281 279 127 126 124 122 154 180 220 231 218 82 156 81 189 203 210 213 200 197 198 194 182 222 241 247 243 230 242 225 181 201 6 11 18 62 67 171 187 185 147 188 133 0\n284 27 64 59 0 262 266 267 260 281 280 279 131 130 127 120 273 268 154 180 220 231 218 82 156 81 189 203 209 206 182 222 242 225 223 201 282 177 283 172 190 64 2 15 137 188 0\n285 -27 59 0 267 215 279 128 125 123 154 180 220 231 218 82 156 81 189 203 210 213 198 193 17 40 148 184 0\n286 30 59 0 266 260 267 215 279 285 284 157 97 95 94 281 280 126 124 120 273 268 154 180 220 231 218 82 156 81 189 203 210 213 198 194 209 207 205 182 222 242 225 224 175 161 64 66 72 136 192 104 118 185 12 140 146 0\n287 59 0 267 260 154 156 180 220 231 218 81 82 189 203 209 207 205 280 281 285 284 97 286 8 102 192 0\n288 -36 0 287 76 0\n289 -37 0 287 77 0\n290 -38 0 287 78 0\n291 -39 0 287 79 0\n292 -45 0 287 80 0\n293 73 0 287 179 0\n294 99 0 287 217 0\n295 -80 0 292 289 288 291 186 0\n296 101 0 293 221 0\n297 -107 0 294 263 239 0\n298 109 0 294 267 238 0\n299 81 0 295 261 195 0\n300 -89 0 295 196 0\n301 -100 0 296 297 234 0\n302 -114 0 298 252 250 0\n303 -91 0 300 200 0\n304 -61 0 301 219 0\n305 -113 0 302 245 0\n306 -111 0 302 246 0\n307 97 0 303 215 213 0\n308 -74 0 304 183 0\n309 -105 0 305 243 0\n310 -104 0 305 244 0\n311 -103 0 306 240 0\n312 93 0 307 210 0\n313 95 0 307 211 0\n314 -72 0 309 229 0\n315 -75 0 309 230 0\n316 -69 0 310 226 0\n317 -71 0 310 227 0\n318 -77 0 310 228 0\n319 -41 0 311 223 0\n320 -56 0 311 224 0\n321 -60 0 311 225 0\n322 82 0 312 202 0\n323 84 0 313 206 0\n324 94 0 313 207 0\n325 85 0 324 204 0\n326 86 0 324 205 0\n327 -30 0 299 326 322 5 8 10 44 48 53 67 102 187 57 58 60 162 137 192 91 97 188 0\n328 -76 55 25 0 299 323 327 290 122 126 127 130 131 187 190 59 0\n329 -67 48 76 50 0 325 326 274 108 109 191 192 116 0\n330 -53 76 50 25 0 323 327 290 325 326 274 59 60 329 190 100 101 191 192 117 0\n331 -65 76 50 0 325 326 274 99 100 101 191 192 117 0\n332 -48 53 55 0 299 33 49 54 187 0\n333 55 50 25 0 323 327 290 299 328 330 331 332 329 190 4 47 52 187 0\n334 48 76 50 25 33 0 323 327 290 318 315 308 317 304 321 320 331 333 71 69 329 190 3 27 90 143 167 144 165 145 255 0\n335 76 50 25 33 0 318 314 316 321 319 333 71 70 331 334 31 35 37 75 168 170 169 256 0\n336 50 25 33 0 323 327 290 318 315 308 317 304 321 320 333 69 71 335 124 130 131 132 190 3 27 35 90 143 165 145 255 0\n337 -50 0 287 327 314 316 321 290 319 318 42 55 68 107 142 175 174 276 0\n338 -25 0 325 337 326 1 32 85 121 191 116 117 192 0\n339 33 0 338 337 336 0\n340 -23 0 339 14 0\n341 -48 0 339 36 0\n342 -63 0 339 91 0\n343 -66 0 339 103 0\n344 0 342 343 340 326 341 337 192 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record018.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record018.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record018.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record018.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record018 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeafTable : ConcreteGrowth.Table (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record018.l) :=
(.branch 1
 (.leaf (⟨0, by decide⟩))
 (.leaf (⟨1, by decide⟩)))
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record018.l := originalLeafTable.get j.val
def orbitWordTable : ConcreteGrowth.Table (List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record018.g)) :=
(.branch 1
 (.leaf ([]))
 (.leaf ([])))
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record018.g) := orbitWordTable.get j.val
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record018.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record018.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record018 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record018_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record018_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record018_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record018_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record018_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record018_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record018_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record018 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record018_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record018_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record018_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00122.record018
