module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow31Part00013Data
public import GraphInputsRow31Part00013Frames
public import GraphInputsRow31Part00013Leaves
public import GraphInputsRow31Part00013Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00013.record002
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00013.record002
def vertexColumn : Fields := ⟨10, hexnat% "3a8e63389e3a4e53349d2ac9b29c9723c1f3a2e4b325cb8acaaaa6ab1aa699a8e93a1eb86c9aa669b16a59968d9361da8e33a2e2ba1e2783ee8791cc571e2729aa5a9c6699666394e479e1725a95a5c5695656354d475a34cd8b4ad8749d0f5a358d9354d331cd8b32d2b2ad1b26c3b61cc749ca745c970de8c8b06c8705c1a85a198562384e0b81e1a459194552344d0b41d60d2318d1314c8b12c2b06c8711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "db6db6924936db6db6db4db6db6d249249b6db6db6da6db6db692492492492492492492449249249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨72, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨103, by decide⟩, ⟨117, by decide⟩, ⟨118, by decide⟩, ⟨119, by decide⟩, ⟨120, by decide⟩, ⟨121, by decide⟩, ⟨122, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7e000001fc000000f80000000000000", 3458764513820540928, hexnat% "80200001004006040800000000", 27127975514210304, 6781993878552576, 425510999949312]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2000001c0001007ff7fff800000000", 2251799813685248, hexnat% "400080204000000000000000000000", hexnat% "38000000000000000000000", hexnat% "7800000000000000000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4000000107ffcf800000000", 3298534883328, hexnat% "600080204001004080000000000000", hexnat% "6000000020000000c00000000000000", hexnat% "188000002000000000000000", hexnat% "1800000010000000300000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7e0000007c000003f80400000000000", hexnat% "180000000000000000000000", hexnat% "80200001004006040800000000", 6781993878552576, 27057606770032640, 425510999949312]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "6000802440010042affff800000000", 22517998136852480, hexnat% "7800000000000000000000000000000", hexnat% "180000003000000000000000", 936748722493063168, hexnat% "38000000000000000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4000000027c440000000000", hexnat% "7c00000000000000000000000000000", 483785116221440, 4363686772736, 4431542033332568064, hexnat% "200080204001004002000000000000", hexnat% "1b8000000000000000000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c7 c4
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c8 c3
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨90, by decide⟩ c9 c0
  c10
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00013.record002_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00013.record002_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00013.record002_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00013.record002_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00013.record002_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00013.record002_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00013.record002_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00013.record002_validity Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00013.record002_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00013.record002
