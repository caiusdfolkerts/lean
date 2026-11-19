module
prelude
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
def vertexColumn : Fields := ⟨10, hexnat% "274d30bc9cb4a2eb469996639a568d8b61db0ea398e9394e2ba1e4789e0f8b9594e5954b51d58d9354d2b61d4749d0f56338e532cc7362e4b52cab86d1b26c3b61e4751cc749ca719e1745c9715c3783d0f23c4f0bc1f8721a514a5194354348d0754328c630cd0b22c1b"⟩
def kindColumn : Fields := ⟨3, hexnat% "36db6db6db6db6da6db49a49a49249349349249b4da4db69a4da249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨16, by decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩, ⟨22, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨31, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨64, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "10d886c4098590000", 2456721293312, 4504149383184384, 20125460834811904]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "10d906c8098590000", 1126037345796096, 2392829359816704, 2302102470656, 18858823439613952]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "10ddfee0498590000", 240518168576, 274877906944, 549755813888]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "10ddfec1498590000", 2370821947392, 274877906944, 549755813888]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "10dc2ec0498590000", 1126037345796096, 2252074691592192, 4785074604081152, 2851858284544]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c5 c2
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1004f027898590000", 4504149383184384, 48395691491328, 576531121047601152, 396457504696958976]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1015f880898590000", 900719925474099200, 2422361554944, 70918499991552, 39857296506880]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [2796043444486144, hexnat% "10004000000000000", 972777519512027136, 23080948091322368]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1005f822418590000", 70920647475200, 377957122048, 972777519512027136, 48378511622144]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1004dae7c18490000", 70920647475200, 972777519512027136, 5066549581840384]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [18414913207140352, hexnat% "10004002000010000", 398709304510644224, 580964354078277632, 2851859333120, 562949953421312]
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
