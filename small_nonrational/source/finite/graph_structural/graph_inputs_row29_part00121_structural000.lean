module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow29Part00121Data
public import GraphInputsRow29Part00121Frames
public import GraphInputsRow29Part00121Leaves
public import GraphInputsRow29Part00121Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00121.record006
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00121.record006
def vertexColumn : Fields := ⟨10, hexnat% "1785b07c5a87a719a659a96958d68d8b61d98e5392e1ba1e2785e0f9d16c5715a599565391e785715a559695954d58d4b51d58d1b61d2745d0f5c368d6394cd38ccb31cd8b52d2b1ae1b26d8791d4731e2749ca719e1725c570de0f43c8f07d4c4b2921683aa184e0ba915252916439a1585515254344d0b68384c9314c3312c2b06e0721c4709c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "34da6da6db6d24da4db4d249249b6da4da4db4924d2492492492492491249249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨83, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨100, by decide⟩, ⟨104, by decide⟩, ⟨107, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "310b80098039484a00000000", hexnat% "78100000000000000000", hexnat% "1000800400000001a000000000", hexnat% "900080000000080020000000000", 197997992345600, 1082552760429182976]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8007818002bfffe00000000", hexnat% "b80000000000000000000", 1118018607494725632, hexnat% "10018004018000000000000000", hexnat% "300000000010000000000000", hexnat% "900000000000000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "308b80098039482e00000000", hexnat% "78100000000000000000", hexnat% "1001000400000001c000000000", hexnat% "900080000000080020000000000", 197980812476416, 1082552760429182976]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "b80080038000400000000", hexnat% "78100001000000000000", hexnat% "800380000000000000800000000", hexnat% "1001800401800001e200000000", 1118581557448146944, hexnat% "100000000000000020000000000", 277145649676288]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨52, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c4 c1
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c5 c0
  c6
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00121.record006_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00121.record006_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00121.record006_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00121.record006_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00121.record006_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00121.record006_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00121.record006_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00121.record006_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00121.record006_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00121.record006
