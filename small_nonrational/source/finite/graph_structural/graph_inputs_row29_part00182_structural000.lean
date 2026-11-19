module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow29Part00182Data
public import GraphInputsRow29Part00182Frames
public import GraphInputsRow29Part00182Leaves
public import GraphInputsRow29Part00182Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00182.record001
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00182.record001
def vertexColumn : Fields := ⟨10, hexnat% "7a1d8791d46b19cd89d29c9ca5a99a568da8e87a719666595635a361d98e4789e0f9e1b4671725a95a4e9366391e5c569565394d58d4756352d2b43d70d6334e331cd8b52ccb8ad2b1ae1b26c5b0ed8751cc789d2719e1725c570dd0f23d8c4b09c989629492a4990e0b81e98651344992548d0b41d90e2318e1314c2b06c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "6db4934d36db69b6da49349b6d36db69b4926924db4924936d2492491249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨62, by decide⟩, ⟨69, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨86, by decide⟩, ⟨93, by decide⟩, ⟨95, by decide⟩, ⟨97, by decide⟩, ⟨98, by decide⟩, ⟨99, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "aa00124200f58e638e0000000", hexnat% "40000c0000000000000000000", hexnat% "4000004000000100000000", hexnat% "8000020000000000000", 26414048870400]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2204000204458e63980000000", hexnat% "800024000100000000000000", hexnat% "8000020000000000000", 26414048870400, hexnat% "c000000000a00000000000000", hexnat% "1c0000000000060000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "c0001e0000f40601060000000", hexnat% "2204000000000000000000000", hexnat% "800004000018020080000000", 140909287047168, hexnat% "8204020000000000000", 30816390348800]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "c000000000e00200000000000", hexnat% "2204000000040000000000000", hexnat% "8204020000000000000", hexnat% "1e0000000000060000000", hexnat% "800004000118020080000000", 211346750701568, 30816390348800]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c5 c2
  c6
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00182.record001_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00182.record001_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00182.record001_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00182.record001_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00182.record001_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00182.record001_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00182.record001_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00182.record001_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00182.record001_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00182.record001
