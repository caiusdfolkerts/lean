module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow19Part00033Data
public import GraphInputsRow19Part00033Frames
public import GraphInputsRow19Part00033Leaves
public import GraphInputsRow19Part00033Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00033.record006
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record006
def vertexColumn : Fields := ⟨10, hexnat% "5c8ea3693a1eac6c9a5635a2e4b91e279713a4d94e479b1725954d58b52d4749db0f2358ce394d5334d331cccb8ad2b2ac6b46c9b16c3bc1e8761e4731e2749e1725c5783d0f0be624588e07a614548d0764330e2348c6344c5322c2b06e0741c8705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "6db6db6da4db6db6db492492492492492492492492449249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1800c19ff09f800000", 70412230721536, 12983033300779008, 22548578304, 4503599627370496]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8007a8d4f7b800000", hexnat% "100080008004000000", 1145693263626240, 387234251407360]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "80076a84fdf800000", hexnat% "100080048000000000", 21096879357952, 2603644071444480]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [18014337432027136, 54043195662663680, hexnat% "180000000000000000", 60934848512]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8004000514b800000", hexnat% "100080048000000000", 7893393975803904, 62612570112, 9763800693604352, 351844257759232]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c5 c2
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c6 c1
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c7 c0
  c8
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record006_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record006_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record006_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record006_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record006_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record006_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record006_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record006_validity Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00033.record006_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00033.record006
