module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow26Part00036Data
public import GraphInputsRow26Part00036Frames
public import GraphInputsRow26Part00036Leaves
public import GraphInputsRow26Part00036Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00036.record063
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00036.record063
def vertexColumn : Fields := ⟨10, hexnat% "1741f3925c9ca6a96a96a3a1e9c669966a5996559361da8e338ae1ba1e1783ee4571725a95a6598e479715a559695655554d475a34cd2b46d8745d0f78370da358f13a4d9394d538cd331ce8b62e4b52ccb8ad2b2ac6b86c5b0ee8761d4731d2729c6785d1725c570de0f23c4f0bc1f54932a28560d88e1382e54531a24550d48d1342d"⟩
def kindColumn : Fields := ⟨3, hexnat% "36d36db6db6d24924d269b6db6db6924926936db6da69a6db6db6db6db6db693493249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨17, by decide⟩, ⟨18, by decide⟩, ⟨19, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩, ⟨44, by decide⟩, ⟨46, by decide⟩, ⟨48, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨78, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨101, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7a0000f4015000006e0000", hexnat% "100000200000000000000", hexnat% "40070000000000000000", hexnat% "20038000000000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "790000f2015000006e0000", hexnat% "200000400000000000000", hexnat% "40070000000000000000", hexnat% "20038000000000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40000080001000000e0000", 8502796096475496448, hexnat% "3b00000000000000000000", hexnat% "30000060000000000000000", hexnat% "20000040000001400000000000", hexnat% "8000010000000000600000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨17, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨18, by decide⟩ c3 c0
  c4
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00036.record063_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00036.record063_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00036.record063_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00036.record063_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00036.record063_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00036.record063_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00036.record063_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00036.record063_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00036.record063_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00036.record063
