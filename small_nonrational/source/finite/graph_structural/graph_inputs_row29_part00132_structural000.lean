module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow29Part00132Data
public import GraphInputsRow29Part00132Frames
public import GraphInputsRow29Part00132Leaves
public import GraphInputsRow29Part00132Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00132.record030
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00132.record030
def vertexColumn : Fields := ⟨10, hexnat% "7c2e8b60f8b92d43d2aca70bcb8ad25c8f2b2aaa9a8eaa6a5a3693a2e87ab1aa6998e6a5a56359362d876a3a2e2ba1e2783e785d16c5713c6c93a4d94e4b91e6c5394d54d4b51d68d0f6c338cd34ccb31ce8b92ccb4acab1ad1b26c5b0ee8791cc749ca719d1725c570de0f23e8c2b09c589528382e0796138551344a9264a52548d0b41d50d2318d1314c2b06c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "6db6da49b4db6db6db6db6db6d249249a4d269b49a6934934db4924936d2492491249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨51, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨60, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨66, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨103, by decide⟩, ⟨106, by decide⟩, ⟨107, by decide⟩, ⟨108, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2adb0c0c8e83a20000000", hexnat% "150000000000040000000", hexnat% "1c00000000000400000000000000", 9031412132872192, hexnat% "80000000041200000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "480000019a492a8fe2de0000000", hexnat% "4104040000000000000", hexnat% "18000002a0000400000000000000", hexnat% "140000000000000000000", 77309411328]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "cb4d0c02e0a00000000", 11276614876790784, hexnat% "480000011000200000000000000", 211312390963200, hexnat% "3e0000000000060000000", hexnat% "1800000000000400000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "480000019b492a8b63fe0000000", hexnat% "4004040000000000000", hexnat% "18000002a0000400000000000000", hexnat% "140000000000000000000", 79164837199872]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "cb4d0c02a0b80000000", 11281006480850944, hexnat% "480000011000200000000000000", 211312390963200, hexnat% "3e0000000000060000000", hexnat% "1800000000000400000000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "d904088020080000000", 246531122790400, hexnat% "3f0000000000060000000", hexnat% "1c00000000000400000000000000", 18045214899830784, hexnat% "249000000000000000", hexnat% "80000000000220000000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨62, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c6 c3
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨68, by decide⟩ c7 c2
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c8 c1
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c9 c0
  c10
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00132.record030_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00132.record030_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00132.record030_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00132.record030_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00132.record030_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00132.record030_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00132.record030_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00132.record030_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00132.record030_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00132.record030
