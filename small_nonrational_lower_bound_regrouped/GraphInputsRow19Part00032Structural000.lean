module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow19Part00032Data
public import GraphInputsRow19Part00032Frames
public import GraphInputsRow19Part00032Leaves
public import GraphInputsRow19Part00032Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00032.record035
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00032.record035
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨16, by decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩, ⟨22, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨31, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨64, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), 2456721293312, 4504149383184384, 20125460834811904]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 3), 1126037345796096, 2392829359816704, 2302102470656, 18858823439613952]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 4), 240518168576, 274877906944, 549755813888]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 5), 2370821947392, 274877906944, 549755813888]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 6), 1126037345796096, 2252074691592192, 4785074604081152, 2851858284544]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c5 c2
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 7), 4504149383184384, 48395691491328, 576531121047601152, 396457504696958976]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 8), 900719925474099200, 2422361554944, 70918499991552, 39857296506880]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [2796043444486144, (certNat% 9), 972777519512027136, 23080948091322368]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 10), 70920647475200, 377957122048, 972777519512027136, 48378511622144]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 11), 70920647475200, 972777519512027136, 5066549581840384]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [18414913207140352, (certNat% 12), 398709304510644224, 580964354078277632, 2851859333120, 562949953421312]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c12 c11
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c13 c10
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c14 c9
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c15 c8
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨19, by decide⟩ c16 c7
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨22, by decide⟩ c17 c6
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c18 c1
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c19 c0
  c20
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00032.record035_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00032.record035_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00032.record035_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00032.record035_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00032.record035_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00032.record035_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00032.record035_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00032.record035_validity Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00032.record035_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00032.record035
