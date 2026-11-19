module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow24Part00142Data
public import GraphInputsRow24Part00142Frames
public import GraphInputsRow24Part00142Leaves
public import GraphInputsRow24Part00142Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00142.record002
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00142.record002
def vertexColumn : Fields := ⟨10, hexnat% "3b19c3aa5a368e68d8b6338ae1b89eb86d1ac4e966659364e5656352d58d334ad1b4e3c4e5334e332ce4b52ccb2ac6b86c9b16cc789d2729c6785c970dc8f13c2f4709c9891a4590e07a61384c946499295152550d2341d90e2318e1344d0b12c1b41c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "1a6db6db69369349349269269a49a493492492489249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨50, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨80, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "100422d604c6f40000000", 5630049290027008, 442005821849600, hexnat% "244000000000000000", 9367487224930631680, 68719476736]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "10042a660ce2d80000000", 903016873984, 5910974510923776, hexnat% "244000000000000000", 648518346341351424, 17592186044416]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "100468710460500000000", 10141938204278784, 2882303761517117440, hexnat% "204040001000000000", 439806798594048, 963146416128]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "100408000040400000000", hexnat% "244040000000000000", 14645529241714688, hexnat% "22400000000000000", 1040455827456, 512374566027264, 792633538712174592]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c4 c1
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c5 c0
  c6
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00142.record002_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00142.record002_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00142.record002_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00142.record002_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00142.record002_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00142.record002_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00142.record002_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00142.record002_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00142.record002_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00142.record002
