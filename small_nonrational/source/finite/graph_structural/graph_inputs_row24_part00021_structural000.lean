module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow24Part00021Data
public import GraphInputsRow24Part00021Frames
public import GraphInputsRow24Part00021Leaves
public import GraphInputsRow24Part00021Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00021.record005
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record005
def vertexColumn : Fields := ⟨10, hexnat% "1d43d31c1f392749aac699a719a639b166595635b0e4b86e8791e17b913c719664b91e4e5c5595354b51d70d1b61d4745d0f783c4e9364e5334f0b62e2b2ac6b86d1b26c5bc1d8731ca785d1725c5783d0f13c1fc611c38b0a1990e0b8e134619194550b41d30ca318e0b0ac4709c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "369b6d36d36da49a6d26da6d34d24936db49a4936db49b692489249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨55, by decide⟩, ⟨57, by decide⟩, ⟨60, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨68, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨77, by decide⟩, ⟨81, by decide⟩, ⟨86, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "400181001a05e003c00000", hexnat% "200100000080004000000", hexnat% "20400000000040000000", hexnat% "21280000080000000", 10133099161583616]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20090003e09e047c00000", hexnat% "10000040000000000", hexnat% "4001000000000000000000", hexnat% "20400000000000000000", hexnat% "21280000080000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2001212a6082086c00000", 1925219090432, hexnat% "c00000000001000000", hexnat% "20000000000000000000", hexnat% "4000010018000000000000", hexnat% "1000000040000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [1925323948032, hexnat% "1900000000001000000", hexnat% "21200080080000000", hexnat% "20400000000000000000", hexnat% "4000010018000000000000", hexnat% "200000000042000000000", 46724846142357504]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨22, by decide⟩ c4 c1
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c5 c0
  c6
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record005_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record005_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record005_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record005_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record005_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record005_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record005_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record005_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record005_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00021.record005

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00021.record009
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record009
def vertexColumn : Fields := ⟨10, hexnat% "761b4c707c749b23c9ca6695a3687a699964d8b61d86e4785e0fb19664d91e715654b51d70d1b61d4745d0f78364cd32cc73c2d8b92ccb1ad1b26c5b0ef0761e2729c6745c9715c3743c4f0bc1f3c30c470e2c2b068390e384d12c471164358341d30ca318e0b12e0709c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "1b4db4db6db6db4db6936926924da49349369a6926da492249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨36, by decide⟩, ⟨38, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨67, by decide⟩, ⟨79, by decide⟩, ⟨83, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [7356997503171952640, 140750641692672, hexnat% "80080000000001000000", 81100046518452224, hexnat% "800000040000000000000", 17179869184]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [7356841127976108032, 288346924384256, hexnat% "80080000000001000000", 81100046518452224, hexnat% "800000040000000000000", 8796093022208]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "80008637800410d000000", 15393162788864, 35253091565568, 288441491242614784, 17213423616, hexnat% "80000001000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [7066504331989614592, 290482176233832448, hexnat% "800000160000008000000", 35253091565568, hexnat% "80080000800001000000", 30098325504, 10995183386624]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨52, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c4 c1
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨61, by decide⟩ c5 c0
  c6
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record009_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record009_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record009_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record009_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record009_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record009_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record009_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record009_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record009_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00021.record009

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00021.record025
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record025
def vertexColumn : Fields := ⟨10, hexnat% "3d13c1f39272b1a66a3a4e9c639b16659362d94e4b86e4783ee44f1c6599366391e4e5c5595354b51d46d4745d0f78338f13a4d938ccb3c2d8b92ccb8ae1b46c9b0ef0761ca785d1725c3743c4f0bc1fc6194c286a618c61986986439314652543530c6382c4b0ac8711c27"⟩
def kindColumn : Fields := ⟨3, hexnat% "1b6da6da4d36da6db4da49a4926d34db6d34926d349b49a4c9249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨23, by decide⟩, ⟨24, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨33, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨41, by decide⟩, ⟨47, by decide⟩, ⟨49, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨63, by decide⟩, ⟨68, by decide⟩, ⟨73, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨80, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "180004e080e0cd800000", hexnat% "100012000000000000", hexnat% "2000100000000000000", 1729382265500205056, hexnat% "100008000021000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "10187200e245800000", hexnat% "8000400800000000000", 108086393338593280, hexnat% "12000000000000000000", hexnat% "100008000021000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "81004f280004d800000", 962072674304, hexnat% "12000000000080000000", 9295431829915959296, 1729382265500205056, hexnat% "100000000001000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1120085c20212cc000000", 589971551193923584, 1152921642045800448, hexnat% "8100000800001000000", 824633720832]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "18101c7282f2cd800000", 108086391056891904, hexnat% "100008000000000000000", hexnat% "2000000000000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8101c1282f249800000", hexnat% "12000000000080000000", hexnat% "100008000000000000000", 63050394783186944, 67108864, 72057594037927936]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨75, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [288935026890899456, hexnat% "18000000000080000000", 1729382265500205056, 63050394783186944, hexnat% "100010000000800000", 9295431829915959296, hexnat% "102000000001004000000"]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c7 c6
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c8 c3
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c9 c2
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c10 c1
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c11 c0
  c12
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record025_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record025_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record025_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record025_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record025_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record025_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record025_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record025_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record025_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00021.record025
