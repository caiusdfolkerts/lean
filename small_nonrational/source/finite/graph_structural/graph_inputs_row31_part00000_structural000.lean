module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow31Part00000Data
public import GraphInputsRow31Part00000Frames
public import GraphInputsRow31Part00000Leaves
public import GraphInputsRow31Part00000Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00000.record003
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00000.record003
def vertexColumn : Fields := ⟨10, hexnat% "f83d0ec3687a358763386e36479354753346d16c5713cb89e2b49d2ac9b2729aa5a8ea6695a3693a2e9c66996639996558d64d8b65392e1b91e1783ef07a1d86e178791d46d174731ac5b1d25c9ca5a99a5693a71966659564d98e5392e7457172569665594e5c559595555356354d4b55352d1b51d1743db0ea398ce3a4e5334e332cccb2ac6b26c5b0ecc729c6725c570dfc0e83905312c4704e0b81eb06a1a444d0b41d30ca324c4b0ac1b11c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "124db6db6db6926db6db6db6db6db6db49249269a69b4db6db6db6db6db6db6db6db4924926934d2492492491249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨39, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨83, by decide⟩, ⟨86, by decide⟩, ⟨88, by decide⟩, ⟨90, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩, ⟨95, by decide⟩, ⟨96, by decide⟩, ⟨97, by decide⟩, ⟨98, by decide⟩, ⟨99, by decide⟩, ⟨124, by decide⟩, ⟨125, by decide⟩, ⟨126, by decide⟩, ⟨139, by decide⟩, ⟨140, by decide⟩, ⟨141, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "38007000000fb5480000000fb6bf7c000000", hexnat% "400000000000400082000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "300060000002844000000002b6bf7c000000", hexnat% "80010000000400800000000400082000000", hexnat% "d000000000000000000000000", hexnat% "31000000000d000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨125, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨126, by decide⟩ c1 c0
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "38007000000f75480000000f76befa000000", hexnat% "800000000000800104000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "28005000000244080000000276befa000000", hexnat% "100020000000804000000000800104000000", hexnat% "d000000000000000000000000", hexnat% "31000000000d000000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨126, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4480000000036a000000000", 2113929216, 135291469824, hexnat% "fc00000000000000000000000", hexnat% "380000000000310000000000000000000000", 4433230883192832, hexnat% "70000000000000000000000000000000"]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c7 c6
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c8 c3
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c9 c2
  c10
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00000.record003_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00000.record003_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00000.record003_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00000.record003_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00000.record003_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00000.record003_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00000.record003_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00000.record003_validity Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00000.record003_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00000.record003
