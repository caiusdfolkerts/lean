module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow31Part00173Data
public import GraphInputsRow31Part00173Frames
public import GraphInputsRow31Part00173Leaves
public import GraphInputsRow31Part00173Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00173.record011
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00173.record011
def vertexColumn : Fields := ⟨10, hexnat% "cd2b46d2745d0f4cb2ac6b26c5b0ecccab26ca725c8f2c6a9a66a5a568dac9aa669a66598e6c5a9665a56558d68d9362d876c3a8e63a4e538cecc6b16c6715c4f1ca6a96a6695a4e9c669966659564d9c96a569665594e5c569565655554d58d5352d475c368d6364d534cd8b52d2b46dc8ea368e6358ce3c4e9364e5354cd38cd332cc73c2e8b62e4b52ccb86d1b26c5bc1e8761e4751cc789d2729c6785d1725c570de0e4388e13a314c4b11c625494a51960d4348d1361344c9314e0b42c8b12e0741c8711c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "6db6db6db6db6db6db6db6db6db6db4924924926db6db6db49249b6db49249249249b6db492492492492492492492492499249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩, ⟨95, by decide⟩, ⟨108, by decide⟩, ⟨109, by decide⟩, ⟨110, by decide⟩, ⟨111, by decide⟩, ⟨112, by decide⟩, ⟨113, by decide⟩, ⟨114, by decide⟩, ⟨115, by decide⟩, ⟨116, by decide⟩, ⟨117, by decide⟩, ⟨118, by decide⟩, ⟨119, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "fc08ffc003c08ffe00000000", hexnat% "fc0000000000000000000000000000", hexnat% "3f000000700000000000000000000", 17856068835082240, 18158513705074032640]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "fc04ffc003c04ffd00000000", hexnat% "fc0000000000000000000000000000", hexnat% "3f000000b00000000000000000000", 17926437579259904, 18158513709368999936]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "fc0000000000000000003000000000", hexnat% "ffc00000000000000000", 17996806323437568, hexnat% "3f0000000000003c0000000000000", 17368847745024, hexnat% "fc0f00000000000000000000", 18158513713663967232]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c3 c0
  c4
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00173.record011_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00173.record011_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00173.record011_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00173.record011_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00173.record011_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00173.record011_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00173.record011_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00173.record011_validity Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00173.record011_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00173.record011
