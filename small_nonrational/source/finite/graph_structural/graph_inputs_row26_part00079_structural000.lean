module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow26Part00079Data
public import GraphInputsRow26Part00079Frames
public import GraphInputsRow26Part00079Leaves
public import GraphInputsRow26Part00079Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00079.record016
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00079.record016
def vertexColumn : Fields := ⟨10, hexnat% "1d86e15c3713c2f1e2749b26ab1aa699a4e8ba598e695956359362da2e4b8ae8791e2783e785d1725a9c6699665593656539655554d5534cd8b52d2b61d4749d175c368d6338f13a4d9394d5334f0ba2d8b8ad2b2ae1b46c9b91d4731e2749ca719e1745c9715e0f43c8f0bc1f8715234a16159292a60d0b54330d2328e0711c27"⟩
def kindColumn : Fields := ⟨3, hexnat% "db6db4db6db6d24db6d36db69b6db6db6d249b6924db6936da4db4924926d26d3249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨17, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨70, by decide⟩, ⟨77, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨95, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "10200001458600fb300000", hexnat% "802800000000000000000000", hexnat% "400280000000020000", 563053099745280]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "80000040038780185e020000", hexnat% "20000040000001100000", 2686451712, hexnat% "3800000000000000000000", 6597069766656]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [162692537613549568, hexnat% "2020000000000001000000", 1548112942333952, hexnat% "400180001800020000", hexnat% "801800000000060000200000", 2617245696]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c3 c0
  c4
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00079.record016_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00079.record016_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00079.record016_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00079.record016_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00079.record016_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00079.record016_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00079.record016_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00079.record016_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00079.record016_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00079.record016
