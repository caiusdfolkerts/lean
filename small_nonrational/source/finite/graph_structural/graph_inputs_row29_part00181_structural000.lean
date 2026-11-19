module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow29Part00181Data
public import GraphInputsRow29Part00181Frames
public import GraphInputsRow29Part00181Leaves
public import GraphInputsRow29Part00181Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00181.record021
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00181.record021
def vertexColumn : Fields := ⟨10, hexnat% "3705e1e49d1747316c6715c4f07cd89e2cc9ca5a99a4e9c669a66598e665a364d98e538ce4b86e4789e0f9e19c5717256966659565391e665396558d4751b49d1743db0dc368e6358ce364d3362e4b52ccb4ac6b86d1b26c3b91cc789ca719e1725c4f0bdc8332324c98a468362381e98631324c5194352344d0762384c3322c1b21c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "db6d36db6d26936db69269b4934d36db69349249b69b69369b492692492449249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨42, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨50, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨69, by decide⟩, ⟨71, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨78, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨101, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "400060027c000b7f8000000", hexnat% "220600000000400000000000", hexnat% "8000000004000000000", hexnat% "804804000000000000", hexnat% "100040200000240000000000", hexnat% "20000100000000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40446006fc044f7f8000000", hexnat% "800004000000000000", hexnat% "220200000000000000000000", hexnat% "100000200000200000000000", hexnat% "20000108000000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2032074a20494044f368000000", hexnat% "40004000000200000000000", hexnat% "800004000000000000", 2449958216885338112, 324259173170675712]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2022060200494040f368000000", hexnat% "800480000000000000", hexnat% "100040200000240000000000", hexnat% "4010c000000000000000000", 2449958216885338112, 1125899906842624]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨101, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c4 c1
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "200060067c00037f8000000", hexnat% "800000000c000000000", hexnat% "800804000000000000", hexnat% "200600000000400000000000", hexnat% "140100000000200000000000", hexnat% "20000040200000040000000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "200020067c00017f8000000", hexnat% "800804000000000000", hexnat% "200600000000400000000000", hexnat% "800000000e000000000", hexnat% "20100040200000040000000000", hexnat% "40104000000200000000000"]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2016034e000fc064f0f8000000", hexnat% "200000000000000000", hexnat% "200400000000000000000000", 2305843030688530432, hexnat% "804004000200000000"]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2014034c806ec42427f8000000", 72057594037927936, hexnat% "200000404000000000", 618475290624, hexnat% "220402000000000000000000"]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2014034c200640646068000000", 618475290624, 108086391325327360, 2305843032836014080, hexnat% "804804000200000000", hexnat% "220402000000000000000000"]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c10 c9
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c11 c8
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "401440027c00425f8000000", hexnat% "800000000d000000000", hexnat% "100000200000200000000000", hexnat% "20000200000000000000000000", hexnat% "804804000200000000", hexnat% "220402000000400000000000"]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "100140806f040407f8000000", 54043195528445952, hexnat% "20000000200000000000000000", hexnat% "800000000f000000000", hexnat% "40004000000200000000000", hexnat% "220602000000400000000000"]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20102804fc40012f8000000", 2305843030688530432, hexnat% "200600000000400000000000", hexnat% "800000000e000000000", hexnat% "40004000000200000000000", hexnat% "20100040200000040000000000"]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1008007c4000068000000", hexnat% "800000000f000000000", 2305843033104449536, hexnat% "220602000000400000000000", hexnat% "20100040200000040000000000", 5188146779320745984, hexnat% "40004000000200000000000"]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c16 c15
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c17 c14
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c18 c13
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨80, by decide⟩ c19 c12
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c20 c7
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c21 c6
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c22 c5
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c23 c0
  c24
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00181.record021_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00181.record021_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00181.record021_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00181.record021_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00181.record021_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00181.record021_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00181.record021_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00181.record021_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00181.record021_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00181.record021
