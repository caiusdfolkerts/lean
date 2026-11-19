module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow29Part00193Data
public import GraphInputsRow29Part00193Frames
public import GraphInputsRow29Part00193Leaves
public import GraphInputsRow29Part00193Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00193.record000
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00193.record000
def vertexColumn : Fields := ⟨10, hexnat% "3389e2b49d1ac9b332ac9b2ca9aac6a5a56a3a4eaa669a96958d68d8b663a2e4b8ae9c5a99a659566394e47969665954d58d4b51d58d9362d4b4ad1b5a394d5334e334ccb362e4b52e2b4acab86d1b16c3b61e4731e2749ca785c9715c3783d0f23c2f6c24c8b19294a4a91a0e139a1645312c5292944d0b58344c9314d0b12c8711c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "36db4da6da6db6d36da6da6db4d36da6d24924934924d369349369a4d2489249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨34, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨45, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨64, by decide⟩, ⟨69, by decide⟩, ⟨71, by decide⟩, ⟨76, by decide⟩, ⟨80, by decide⟩, ⟨85, by decide⟩, ⟨92, by decide⟩, ⟨96, by decide⟩, ⟨99, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "10a00d4aa48118000000", hexnat% "1000100000004000404000000", 9009537864433664, hexnat% "2000010000000000000000", hexnat% "8000000003200000020000000", hexnat% "100000000081004000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8000100203a03a6a03c000000", hexnat% "10010400000000000000", hexnat% "100000800000000000000000", hexnat% "100000000010c000400000000", hexnat% "2000000080004080000000", 27021602059190272]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "800011000360280e5bc000000", hexnat% "a00800000000000000", hexnat% "2000010000000000000000", hexnat% "100000000010c200000000000", hexnat% "100000000081020000000000", 27025995810734080]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "102010a039eba640bc000000", hexnat% "8000000000200000000000000", 708669603840, hexnat% "10400000000000000", hexnat% "1000100000004000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8102010a03b8ba640b8000000", 28147501966032896, hexnat% "10400000400000000", hexnat% "1000100000000000004000000", 687194767360]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "102010a10daf26a598000000", 18155135997837312, hexnat% "1000100000000000004000000", 3458764789235318784, hexnat% "8000000000200000000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "102010a1098b264098000000", 18155135997837312, 1585267068901523456, hexnat% "1000100000004000400000000", 9007890744475648, hexnat% "8000000002000000020000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨64, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c7 c4
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c8 c3
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8000000803202000038000000", hexnat% "102000000081004000000000", hexnat% "10200c00000000000000", hexnat% "100010000010c200404000000", 18161733067603968, 9007890744475648, hexnat% "10000000080000000"]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨71, by decide⟩ c10 c9
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c11 c2
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c12 c1
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c13 c0
  c14
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00193.record000_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00193.record000_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00193.record000_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00193.record000_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00193.record000_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00193.record000_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00193.record000_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00193.record000_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00193.record000_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00193.record000
