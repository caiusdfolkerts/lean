module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow24Part00101Data
public import GraphInputsRow24Part00101Frames
public import GraphInputsRow24Part00101Leaves
public import GraphInputsRow24Part00101Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00101.record005
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00101.record005
def vertexColumn : Fields := ⟨10, hexnat% "29c1f29a1eac6598e6a58d61db0ea3a2e4b86e8791e2785e0fa991e6c5594e5a5475c368d8b46d8751d2745d0f6c358ce3a4c73c2e8b8ac6b86d1b26c5b0ef07a1d8791d4731e2749ca719e1745c9715c3783d0f23c4f0bc1f3512c3492a34529a14c549465254558350d0b41da0cc348c6324c5382d0b0ac1b"⟩
def kindColumn : Fields := ⟨3, hexnat% "36db6da6db4db6db6924924924924924924924d36d34d369349b489249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨26, by decide⟩, ⟨27, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨37, by decide⟩, ⟨39, by decide⟩, ⟨41, by decide⟩, ⟨45, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨83, by decide⟩, ⟨88, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3efe81100a60c000000", hexnat% "4100000200000000000", 1513211673819742208, 164944336352444416, hexnat% "108000000000000c0000000", 46302633668902912]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3be8ff8000cc000000", hexnat% "204000000a000000000", 1513211673819742208, hexnat% "800200200400000000", hexnat% "10800000000000200000000", hexnat% "5400000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4fbf662020604000000", hexnat% "3040000002000000000", 44332308831928320, 648518346341351424, hexnat% "108000000002080c8000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7be9ff8000cc000000", hexnat% "3040000002000000000", 1585269267857670144, hexnat% "4800000200400000000", hexnat% "10800000000008200000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "108003be0efa2a6cc000000", 941252322120433664, hexnat% "800200000000000000", hexnat% "3440000000000000000", hexnat% "4001000000000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "108003be0eea2a6cc000000", hexnat% "2000800000000000000", hexnat% "5800000000000000000", hexnat% "40011000000000000", hexnat% "400100000000000000", 1585267068834414592]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "344fd33822244000000", hexnat% "4800000200400000000", 57420897396457472, hexnat% "20200000000000000", hexnat% "10800000000008008000000", hexnat% "390000000000000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4d7ffa00644000000", hexnat% "200080000a008000000", hexnat% "5400000020000000000", hexnat% "920000000000000000", hexnat% "292000000080000000", hexnat% "10800000000000000000000"]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [14785739927702208512, 57983845202395136, hexnat% "4001000220400000000", hexnat% "3440000000000000000", hexnat% "3b2000000080000000", hexnat% "800200000000000000", hexnat% "10800000000008208000000"]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c9 c6
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c10 c5
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c11 c4
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c12 c3
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c13 c2
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c14 c1
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨62, by decide⟩ c15 c0
  c16
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00101.record005_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00101.record005_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00101.record005_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00101.record005_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00101.record005_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00101.record005_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00101.record005_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00101.record005_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00101.record005_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00101.record005
