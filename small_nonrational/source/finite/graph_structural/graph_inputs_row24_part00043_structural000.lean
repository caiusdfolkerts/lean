module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow24Part00043Data
public import GraphInputsRow24Part00043Frames
public import GraphInputsRow24Part00043Leaves
public import GraphInputsRow24Part00043Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00043.record042
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record042
def vertexColumn : Fields := ⟨10, hexnat% "1b45b13c5aa9ab19c6699662d94e4b86e1783ef05b1e27495a69966539b15c569565655352d54d4b46d4745d0f6c370da358e932ce8b62d4b8ad2b1ae1b26c5ba1d8791d4731d2729c6715d0f13c2f07e4a0e8960da49525290e5855152525435a0e4324c3382c4b0ac1b21c4709c17"⟩
def kindColumn : Fields := ⟨3, hexnat% "36db6db4db69b69369a4924936d26da49a492492492493491249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨66, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨74, by decide⟩, ⟨79, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "46416209f43ee000000", hexnat% "80008800000000000000", 352530915655680, 4503633987108864, hexnat% "14000001400000000", 2305843009213693952]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "5fa211437e4000000", hexnat% "84000000800002000000", 4574002731286528, hexnat% "600400000000000000", 12919261626368, 134217728]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "46406301f5eee000000", 352530915655680, hexnat% "80008800800000000000", hexnat% "15000000100000000", 2305843009213693952]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "465d62016510e000000", 2882303763664601088, hexnat% "80000000800020000000", 61203283968, 4583863976198144, 282162171478016]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "61c600161fec000000", 4035225266123964416, hexnat% "84000000800002000000", 4855580787212288, hexnat% "40020000000000000", 10720238370816]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "5fa201417ec000000", hexnat% "84000000800002000000", hexnat% "600400000000000000", 4574140170240000, 283124244152320, 11269994184704]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "41f611dfffae000000", hexnat% "240000000000000000", hexnat% "4000020000000000000", 1073741824, hexnat% "80000800000000000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "410211dfff2e000000", hexnat% "84000000000000000000", hexnat% "240000000000000000", 297237575406452736, 5764607524107976704, 12105675800519376896]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨64, by decide⟩ c7 c6
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8420fe20827fee000000", hexnat% "10010000000000000", hexnat% "400000c0000000000", hexnat% "400000100000000000", 353492988329984]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "605e00127fee000000", hexnat% "1a000000000000000", hexnat% "84000000800000000000", hexnat% "40020040000000000", 353492988329984, 4512395720392704]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c10 c9
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8404be30dfd5ee000000", 180388626432, 281474976710656, hexnat% "600000000000000000", hexnat% "14000000000000000"]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8400be208855ee000000", hexnat% "240000060000000000", hexnat% "14000000000000000", hexnat% "400000100000000000", 4503780015996928, 353492988329984]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c13 c12
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "644a115fff4e000000", hexnat% "4000420000000000000", hexnat% "800000008000a0000000", hexnat% "1b000000000000000"]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8400be21827fee000000", 80814104641536, hexnat% "14000000000000000", hexnat% "600000100000000000", 4503599627370496, hexnat% "40000040000000000"]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "600e001255cc000000", hexnat% "84000000800002000000", 180925497344, hexnat% "40020040000000000", hexnat% "1f000000000000000", 80814104641536, 4785074604081152]
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c17 c16
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c18 c15
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c19 c14
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c20 c11
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c21 c8
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c22 c5
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c23 c4
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c24 c3
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c25 c2
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c26 c1
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c27 c0
  c28
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record042_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record042_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record042_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record042_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record042_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record042_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record042_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record042_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00043.record042_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00043.record042
