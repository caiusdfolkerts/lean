module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow29Part00223Data
public import GraphInputsRow29Part00223Frames
public import GraphInputsRow29Part00223Leaves
public import GraphInputsRow29Part00223Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00223.record005
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00223.record005
def vertexColumn : Fields := ⟨10, hexnat% "1b45d0f49b13c2f07c6c9723ca6a4e8ba1eb26a99a69996639996558d64d8b61da4e8b92e2b86e8791e2785e0fa69c96a569665594e5554d59362d4b4ad1b61d4749dc8ea368e6358ce354cd392e2b4acab1ae1b46c9bc1e8761e4751cc789d2729c6785d1725c5783d0f23c4f0bc1f691948b06c171a264a2a1a85a6445961515254558344d0758344c9314e0b12c1b"⟩
def kindColumn : Fields := ⟨3, hexnat% "9b4da4da6d369b69b6db4da6da6db4db4926d249b4db4926d249b4db6db6924da689249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨26, by decide⟩, ⟨28, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨43, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨59, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨75, by decide⟩, ⟨80, by decide⟩, ⟨84, by decide⟩, ⟨87, by decide⟩, ⟨94, by decide⟩, ⟨98, by decide⟩, ⟨101, by decide⟩, ⟨104, by decide⟩, ⟨107, by decide⟩, ⟨108, by decide⟩, ⟨111, by decide⟩, ⟨114, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "41820000000000000000000000000", hexnat% "8100000000200020000000000000", 54535776804798464, hexnat% "8120812000000000000", hexnat% "c1c000000000000000", hexnat% "4409100000000080790000000"]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00223.record005_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00223.record005_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00223.record005_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00223.record005_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00223.record005_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00223.record005_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00223.record005_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00223.record005_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00223.record005_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00223.record005
