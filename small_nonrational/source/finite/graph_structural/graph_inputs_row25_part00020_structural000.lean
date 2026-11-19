module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow25Part00020Data
public import GraphInputsRow25Part00020Frames
public import GraphInputsRow25Part00020Leaves
public import GraphInputsRow25Part00020Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00020.record046
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00020.record046
def vertexColumn : Fields := ⟨10, hexnat% "dc2f07c368d62e4b526c3b25c571e2749b25c8f25a8ea568e6558d6538ce8b8ae1ba1e4785ed86e178751b45d1cc6b16c6715c4f1d27299a5693a71996559b16a5994e5a5655554d59354d3362d2b46d8751d175a364e334ccb38acab86d1b89ca785d1783d0f23c2f07e685a2543524c4a8968a529854958352328d1324d0b0ac8705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "1b69b49a6db6d36da6db6db6db6db6db6926db6db49a4da6d369349269a492491249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨30, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨41, by decide⟩, ⟨44, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨84, by decide⟩, ⟨89, by decide⟩, ⟨96, by decide⟩, ⟨98, by decide⟩, ⟨99, by decide⟩, ⟨102, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "d00100000300d920002000000", hexnat% "40020000004000000000000000", 8724152320, 21751660544, 35517366272, 412316860416, 6291456]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1000000000000826d55e00000", 8757706752, hexnat% "21000000000000000000000", hexnat% "44000000002000000000000000", hexnat% "800000000000d000000000000", 4611703610613432320, 1152921504606846976]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4000000000000906d55e00000", hexnat% "1000000000004020000000000", 8757706752, hexnat% "21000000000000000000000", hexnat% "40000000007000000000000000", hexnat% "8000000000009000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "800100000000d82225ea00000", hexnat% "5000000000000000000000000", 38671482880, 292057776128, 6917546619827126272, hexnat% "40020000001000000000000000", 4194304]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "21000000000800058000000", 463856467968, hexnat% "5000000000000000000000000", hexnat% "800000000000d000000000000", hexnat% "40000000007000000000000000", 19791242854400, 94371840, 12889096192]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c5 c2
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c6 c1
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c7 c0
  c8
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00020.record046_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00020.record046_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00020.record046_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00020.record046_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00020.record046_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00020.record046_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00020.record046_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00020.record046_validity Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00020.record046_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00020.record046
