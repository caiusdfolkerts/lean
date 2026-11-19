module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow26Part00054Data
public import GraphInputsRow26Part00054Frames
public import GraphInputsRow26Part00054Leaves
public import GraphInputsRow26Part00054Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00054.record014
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00054.record014
def vertexColumn : Fields := ⟨10, hexnat% "5e2b43b13c2f07ccca725c9aa5a8ea5693a1eaa639a364d8763392e2b86e4785e0fb31ac6715c699566a5396958d5352d4753351d27723a8da398d6338f1394d538cd331ce8b62d4b32e1b46c5ba1cc789d2729c6785d1715c3743c1f1d05ca88a61988e13919164552344d0768342c8b12c8711c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "1b6da6db6db69369349a6db6d36db6924d36db6db6924d249b49b4d2249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨20, by decide⟩, ⟨21, by decide⟩, ⟨23, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨49, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨61, by decide⟩, ⟨68, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨88, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "22102038001b40b00000", 414464344064, hexnat% "10000c00000000000000000", hexnat% "40000002000008000000", hexnat% "4000040000004000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4102038003b00b00000", hexnat% "10000000040000000000000", 563227113029632, hexnat% "60800000000000000000", hexnat% "2400000000044000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [2321605620795441152, hexnat% "40000002000088000000", 515398172672, hexnat% "10004100040000000800000", hexnat% "22c00000000040000000", 67108864]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c3 c1
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c4 c0
  c5
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00054.record014_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00054.record014_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00054.record014_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00054.record014_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00054.record014_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00054.record014_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00054.record014_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00054.record014_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00054.record014_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00054.record014
