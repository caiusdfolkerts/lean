module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow29Part00001Data
public import GraphInputsRow29Part00001Frames
public import GraphInputsRow29Part00001Leaves
public import GraphInputsRow29Part00001Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00001.record007
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00001.record007
def vertexColumn : Fields := ⟨10, hexnat% "358f1394d52b4ab25c8f3c2e4b526cb4ac6a5a56b86d1ac671b16a5996959562da8e938ae1ba1e17bc1e47516c749c665956785d16c571715a5595955552d68d934ad1b61d175c368d9354d332cd4b2ac6b46c5b61d4731c6745c9715c8f9321c0f03a298361382e07839294351342d0758350ca344c3312c2b06c8711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "db6da4db6db6db6db6d34924db6db6db6db6d3492492492492492492249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨53, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨77, by decide⟩, ⟨95, by decide⟩, ⟨96, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "100000e80000ea0dff0000000", hexnat% "20000020120000000000", hexnat% "800001000001000000000000", 80401787781120, 4398046511104]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [105003092017152, 35734127902720, hexnat% "20000020000000000000", hexnat% "4000004000000000000", hexnat% "1800001800001800000000000", hexnat% "a00000a000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1000000800000fd3ff0000000", hexnat% "800001000001000000000000", 3023656976384, hexnat% "4000004000000000000", hexnat% "a00000a000000000000", hexnat% "20000020000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [139362830385152, 1374389534720, hexnat% "20000020000000000000", hexnat% "4000004000000000000", hexnat% "1800001800001800000000000", hexnat% "a00000a000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "18000018000018404b0000000", 71476845740032, hexnat% "4000004008100000000", hexnat% "a00000a000000000000", hexnat% "20000020120040000000", 481036337152, 44014824849408]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c5 c1
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c6 c2
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c7 c1
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c8 c0
  c9
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00001.record007_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00001.record007_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00001.record007_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00001.record007_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00001.record007_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00001.record007_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00001.record007_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00001.record007_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00001.record007_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00001.record007
