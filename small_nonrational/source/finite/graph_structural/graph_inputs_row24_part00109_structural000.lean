module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow24Part00109Data
public import GraphInputsRow24Part00109Frames
public import GraphInputsRow24Part00109Leaves
public import GraphInputsRow24Part00109Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00109.record010
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00109.record010
def vertexColumn : Fields := ⟨10, hexnat% "6e1e46b19cd49b26aa6a6693a2e9a6599969595663a4e4b8ae1ba1e4789e785b19a6992e5c5695653959595555934ad1b61d68e6358d9394d534ccb392e2b2ac6b26c3b61e4751d2729c6785d1725c5783c8f13c2f6509c58a1a51916078a9864992548d0764318e1382c2b06c4705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "1b69b6db6d269b6da49b6936da6da69a4d36d2492693692492489249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨45, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨50, by decide⟩, ⟨52, by decide⟩, ⟨56, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨74, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨86, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "400000123567fc00000", hexnat% "20000000800000000000", hexnat% "4010040100000000000000", 6918655064986877952, hexnat% "180000000000000000", 4504149383184384]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "24080001a0067fc00000", 3642132267008, hexnat% "4010040100000000000000", hexnat% "100004002000000000", 6922032627268452352, 549755813888]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3004611581f65fc00000", hexnat% "4000080000000000000000", 37383932215296, hexnat% "100000000000000000", hexnat% "4000000000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1004601481b00fc00000", hexnat% "4000000100000000000000", hexnat% "24000000000200000000", 283967131484160, hexnat% "180000000030000000", 35184372088832]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2010601403f067c00000", 316676528668672, hexnat% "40100c0000000008000000", hexnat% "4000000000210000000", 72198331526283264]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40101c600400342f800000", 4504149387378688, 319957883682816, 72198340384653312, hexnat% "24000000000000000000", 275951648768]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [6923158733425999872, hexnat% "4010040100000008000000", hexnat% "24000000000200000000", hexnat% "180000000030000000", 319957883682816, 141030619873280, 549793562624]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c7 c6
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c8 c5
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨24, by decide⟩ c9 c4
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c10 c1
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨23, by decide⟩ c11 c0
  c12
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00109.record010_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00109.record010_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00109.record010_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00109.record010_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00109.record010_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00109.record010_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00109.record010_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00109.record010_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00109.record010_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00109.record010

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00109.record015
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00109.record015
def vertexColumn : Fields := ⟨10, hexnat% "1d86d1ac673526c9aa5a99a569a665a564d8b663a4e4b8ae4789e179d16c5c96a5696655936695954b59349d175a358d9354d332cd8b92d4b4acab1ad1b26c5b91e2729c9715c3783c8f13c1f6a0ac949525292a8582e944a9296152548d0b64384c5312c2b81c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "369a6934da6db49b6db4db69269b6d36d2493692492492249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨45, by decide⟩, ⟨50, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨59, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨72, by decide⟩, ⟨75, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨80, by decide⟩, ⟨82, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "80000540027ff000000", hexnat% "1000020000000000000", 38482906972160, hexnat% "100000000000000000000", hexnat% "60080000008000000000", hexnat% "400040800004000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "109000024232623000000", hexnat% "60080000008000000000", 22517999479029760, 6643777536, hexnat% "400040800004000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "108000000200401000000", hexnat% "440040800004000000000", 23643899117436928, hexnat% "1000020000222000000", hexnat% "2008000000a000000000", 3298534883328, 6912212992]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨24, by decide⟩ c3 c0
  c4
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00109.record015_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00109.record015_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00109.record015_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00109.record015_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00109.record015_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00109.record015_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00109.record015_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00109.record015_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00109.record015_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00109.record015
