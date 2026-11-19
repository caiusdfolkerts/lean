module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow24Part00047Data
public import GraphInputsRow24Part00047Frames
public import GraphInputsRow24Part00047Leaves
public import GraphInputsRow24Part00047Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00047.record034
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00047.record034
def vertexColumn : Fields := ⟨10, hexnat% "ae1b49b07cb8ab2aaa6aa6a3a2e87a999962d87693a2e1b91e1783eb85b1aa6692e479695954d4b51d51d176c3a8e6338cb31ce8b92e2b2ac6b46c9b16c3b61d4729c6725c570dd0f0be681b03c64a4a4584e079912c4690e465454351342d0758344c9312c1b41c4705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "1b49b69b6da6d349269a49a4924db69b4da49249a492449249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨43, by decide⟩, ⟨46, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨62, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨69, by decide⟩, ⟨72, by decide⟩, ⟨78, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40094dd841f1a8000000", 52881784832, 1152930300699869184, hexnat% "800200000000000000000", hexnat% "1040000000000000000", hexnat% "400020020000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4000b04b8013df8000000", hexnat% "40001000080000000000", hexnat% "1040000008000000000", hexnat% "800200000000000000000", 5188217414352896000, 90071992547409920]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40022042809fcd8000000", hexnat% "840081000000000000000", hexnat% "1040000000000000000", 5242189966259257344, hexnat% "10000400120000000", 76561193665298432]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "c402b1428493168000000", 53955526656, 5188147045608718336, hexnat% "1040000008000000000", 130604389193744384]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40280008093000000000", hexnat% "c00001400000000000000", hexnat% "1000100008880000000", 23488102400, 5188217414352896000, 67553994410557440, hexnat% "70000000000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c5 c2
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c6 c1
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c7 c0
  c8
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00047.record034_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00047.record034_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00047.record034_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00047.record034_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00047.record034_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00047.record034_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00047.record034_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00047.record034_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00047.record034_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00047.record034
