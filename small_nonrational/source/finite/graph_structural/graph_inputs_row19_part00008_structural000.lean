module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow19Part00008Data
public import GraphInputsRow19Part00008Frames
public import GraphInputsRow19Part00008Leaves
public import GraphInputsRow19Part00008Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00008.record084
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record084
def vertexColumn : Fields := ⟨10, hexnat% "358c70f29ab1a96b162d876c38ae1ba1e4785ed44f1d271996559654b51d52d2b46d4745d38f1394cd32cc73c2e4b2ae1b46c5b19d1715c3743c8f13c1f94a4a1a8a62582e1a4a5454954342d28c6324c5312c2b21c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "db4d34da4db6db6d26924d3492693692492489249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2, 3]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7f6ffcd59fefc00000", 2611340115968, 1152956688978935808, 571746314878976, 9223653511831486464]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "757ffff7fbffc00000", 9223372036854775808, hexnat% "20000080000000000", hexnat% "80000000400000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7d7ffdf50faf800000", 9223372243013206016, 571746319073280, 2474974904320, hexnat% "20000008000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7f7ffcb58fe8800000", 79164874948608, 2680126701568, 844425198567424, 9223372036871553024]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .size 3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .size 2
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨22, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c6 c7
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c6 c8
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨67, by decide⟩ c6 c9
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c10 c5
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "75fffff5bbbf800000", 2474974904320, hexnat% "a0000000400000000", 8796097216512]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c12 c11
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "75ffffb53bb5800000", 79164874948608, hexnat% "a0000000440000000", 2473901162496, 549890031616]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c14 c13
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7f6ffda50dc0800000", 87960963776512, 571746319073280, 10376293541545508864, 893487415296, 2345589014528]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c16 c15
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c17 c4
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c18 c3
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨23, by decide⟩ c19 c0
  c20
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record084_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record084_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record084_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record084_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record084_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record084_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record084_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record084_validity Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record084_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00008.record084
