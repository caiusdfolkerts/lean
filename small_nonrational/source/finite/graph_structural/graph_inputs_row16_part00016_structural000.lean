module
prelude
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow16Part00016Data
public import GraphInputsRow16Part00016Frames
public import GraphInputsRow16Part00016Leaves
public import GraphInputsRow16Part00016Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00016.record006
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00016.record006
def vertexColumn : Fields := ⟨10, hexnat% "332caa5a8e87a69b164d8b6c38ce4b8ae8785e0fb31ca6598e479697154d4b5c34cd4b4ad8745d0f72368f1394e334ccb31cf0ba2e4b32e2b4ac6b86c5b0ef0761d4731d2729e1745c970de0f43c2f07caa1588e138a91548d1370348ca384c530ce0b22c4b0ad0721c4705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "db6db6da69a6db6db6da69a692492492492492492492492449249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨56, by decide⟩, ⟨58, by decide⟩, ⟨60, by decide⟩, ⟨72, by decide⟩, ⟨74, by decide⟩, ⟨76, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [1467760199581302784, hexnat% "14000000000000000000", 9296508251799552, hexnat% "100010000c000000000", 123145302310912]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1000100004620800000", hexnat% "4000400280081000000", hexnat% "10001000000006000000", 27021705138405376, 6843910127091712, 1548113848303616, 570783973769216]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c1 c0
  c2
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00016.record006_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00016.record006_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00016.record006_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00016.record006_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00016.record006_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00016.record006_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00016.record006_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00016.record006_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00016.record006_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00016.record006

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00016.record012
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00016.record012
def vertexColumn : Fields := ⟨10, hexnat% "31cc693a39b162d876c38ae1ba1e4783ec66394e4e5c56952d475c364d2b46d8751d0f4e3c4d934cc73c2d4b4acab86d1b0ef0731ca719e1745c570de0f43c8f0bc1f2c86a2584ec44b1c2469854958344d28c6344c930cd0b12c2b21c4705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "36db4db4db4db49349a4da492492693492492492249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨63, by decide⟩, ⟨67, by decide⟩, ⟨71, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "804117f6fff000000", hexnat% "800200000000000000", 9799973526646554624, 56294995342131200]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [288642899153780736, 22517998136852480, hexnat% "880200000000000000", 9799973526646554624, 36037593111986176, 2252074691592192]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [18356552767373312, hexnat% "880210000000000000", 866942928268820480, 9259409629966761984, 211381110439936]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "800e08f065e5000000", 9259409629966761984, hexnat% "80010040202000000", 281509336449024, 3298669101056, 18014398777917440]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [56365365495595008, 864691134897586176, hexnat% "880210000622000000", 9223521845314060288, 281509336449024, 56212531970048, 4398197506048]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c6 c3
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c7 c2
  c8
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00016.record012_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00016.record012_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00016.record012_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00016.record012_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00016.record012_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00016.record012_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00016.record012_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00016.record012_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00016.record012_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00016.record012

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00016.record016
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00016.record016
def vertexColumn : Fields := ⟨10, hexnat% "31c2f07c3ab1aa68bac59362db0e2b86e8791e2783e3a719a64b91e7154d4b51d70d2b46d8751d2745d0f4e3c4e9364e334ccb3c2e8b92ccb2ac6b86d1b26c3bc1d4749ca785d1725c3783d0f23c2f07c6613b112c61926465454351341dc0ca318e0b22c4b41c4709c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "36db6db6da6db6926924da4924936da4924934d249a692491249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨28, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨35, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨72, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "10761fe1fea42e00000", 1729382256977379328, 6727663616]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "760fe11ead6600000", 1729382256910270464, hexnat% "1000100000100000000", 15393187954688]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "760fe10aa16200000", hexnat% "1000100004100400000", 1729382257984012288, 16492699582464, 2147483648]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c3 c0
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "660ea102b95600000", 1126725614305280, 1729382256910270464, hexnat% "1010100000000000000", 16492716359680, 4503599627370496]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "728e61fabd7e00000", 1155173304420532224, hexnat% "1000100004000000000", 4503599627370496, 4611686018427387904]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "300a617e8d6e00000", hexnat% "40040080001000000", 4611686027017322496, 4037477065937649664, hexnat% "1000100000100000000", 4503599627370496]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c7 c6
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "10339fc17c857e00000", 15032385536, hexnat% "44002000000000000", 8933531975680]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "669fa008813e00000", hexnat% "1010000004000000000", 1152939097933742080, 15032385536, 16630113370112, 1125899906842624]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c10 c9
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [4652781408245252096, hexnat% "101010800c000400000", 1143493233737728, hexnat% "60060000000000000", 4035225266123964416, 16630155313152, 6461325312]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨52, by decide⟩ c12 c11
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c13 c8
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c14 c5
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c15 c4
  c16
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00016.record016_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00016.record016_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00016.record016_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00016.record016_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00016.record016_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00016.record016_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00016.record016_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00016.record016_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00016.record016_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00016.record016

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00016.record022
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00016.record022
def vertexColumn : Fields := ⟨10, hexnat% "f82f07c3c8ea368ba1eb162d876c38ae1b89e1783e3c4e9364b91e7158d4b51d70d4b4ad1b49d1743d38f13a4e5334cb31cf0b62d4b32cab1ac9b16c3b29c6745c9715c3783c8f13c2f07f068590e2c4712a469c16150d50d0b70384c9314d0b22c4b81d0705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "db6db69b4db6d269249249369a4924924924db492492449249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨50, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨71, by decide⟩, ⟨74, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [7531680596154646528, 1224979098644774912, hexnat% "4800000000000000000", hexnat% "10060006000000000", hexnat% "20600180000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [6919208913610997760, hexnat% "4800000000000000000", 8933817188352, hexnat% "100e0000000000000", hexnat% "20e00000000000000", 1224979098644774912]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "22e04f87871800000", hexnat% "14060000000000000", hexnat% "4001001000088000000", hexnat% "800100040000000000", 3848391360512, 36028797018963968]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "120e41bf817800000", hexnat% "24600000000000000", hexnat% "800100040088000000", hexnat% "4001001000000000000", 246292215234560, 576460752303423488]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "25e00f870f1800000", hexnat% "4000001000008000000", hexnat% "12064000000000000", hexnat% "800100040000000000", 3882751098880, 36028797018963968]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "141e01bf01f800000", hexnat% "800000040080000000", hexnat% "22604000000000000", hexnat% "4001001000000000000", 246326574972928, 576460752303423488]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4800000187088800000", 1224979098644774912, 8246437871616, 527767191945216, hexnat% "100e4000001000000", hexnat% "20e00000010000000", 6917529062000820224]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c7 c4
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c8 c3
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c9 c2
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c10 c1
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨23, by decide⟩ c11 c0
  c12
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00016.record022_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00016.record022_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00016.record022_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00016.record022_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00016.record022_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00016.record022_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00016.record022_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00016.record022_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00016.record022_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00016.record022

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00016.record025
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00016.record025
def vertexColumn : Fields := ⟨10, hexnat% "31c3ab1a2e87a39b162d876c398e538ce8791e2785e3a7192e479397158d4b51d70da358d9354d3361d4749d174e3c4cb31cf0b62d4b32cab1ae1b46c9b16c3bc1d8751cc749e1745c9715e0f43c8f13c1f298660db0986705294658543528c630cd0b22c4b06d0721c4709c17"⟩
def kindColumn : Fields := ⟨3, hexnat% "db6d349b6db6da6d24926db69b69a4924924924924924d2489249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨50, by decide⟩, ⟨54, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨68, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨81, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "111040000000000000", hexnat% "2c0000000000080000000", hexnat% "2e000000000000000", 71503689285632, 1554778161152000, 31067209728, 62534723829760]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00016.record025_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00016.record025_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00016.record025_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00016.record025_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00016.record025_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00016.record025_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00016.record025_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00016.record025_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00016.record025_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00016.record025

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00016.record008
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "31c3cb1a66b162d876c38ae1ba1e4789e3c719a6599c56552d475c362d2b46d8751d274e3c4d9354cd32cc73c2d8b4ac6b86d1b26f0729e1745c970de0f43c8f13c1f2a8661582ec47092a465854558342d28c6344c9314d0b22c2b11c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "36db69a4db69b49a4924da49249249a4d2492492249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00016.record008 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00016.record008 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00016.record008.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00016.record008.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00016.record008.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 57), (facetIndex 63)]))
 (.branch 2
 (.leaf ([(facetIndex 71), (facetIndex 75)]))
 (.leaf ([(facetIndex 34), (facetIndex 37), (facetIndex 50)]))))
 (.branch 5
 (.branch 4
 (.leaf ([(facetIndex 65), (facetIndex 66), (facetIndex 69)]))
 (.leaf ([(facetIndex 72), (facetIndex 74), (facetIndex 76)])))
 (.branch 6
 (.leaf ([(facetIndex 49), (facetIndex 60), (facetIndex 61)]))
 (.leaf ([(facetIndex 64), (facetIndex 73)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "43342180de02d0000000a800000001008z19;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 7
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped3_0000 : List Nat := [0]
def grouped3_0001 : List Nat := [0, 1, 2]
def grouped3_0003 : List Nat := [1]
def grouped3_0004 : List Nat := [1, 2]
def grouped3_0005 : List Nat := [2]
def grouped3_0006 : List Nat := [3]
def grouped3_0007 : List Nat := [3, 4]
def grouped3_0008 : List Nat := [3, 4, 5, 6]
def grouped3_0009 : List Nat := [4]
def grouped3_0010 : List Nat := [5]
def grouped3_0011 : List Nat := [5, 6]
def grouped3_0012 : List Nat := [6]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00016.record008 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00016.record008_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00016.record008" "{\"atoms\":[{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0004\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0007\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0007\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0011\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00016.record008" 50

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00016.record008" "{\"ridges\":[[8,146],[13,524],[15,532],[28,524],[30,146],[32,532],[34,774],[35,145],[35,146],[43,146],[44,146],[46,146],[51,532],[54,524],[55,776],[57,180],[58,532],[59,784],[61,664],[63,240],[65,284],[66,538],[69,774],[71,180],[72,774],[74,538],[75,240],[76,284]],\"owners\":[[35,145,[57,63],[8,30,43,44,46,49,60,61]],[8,146,[64,71,73,75],[30,35,43,44,46]],[30,146,[73,75],[8,35,43,44,46,64,71]],[35,146,[71,75],[8,30,43,44,46,64,73]],[43,146,[64,73],[8,30,35,44,46,71,75]],[44,146,[64,71,73],[8,30,35,43,46,75]],[46,146,[64,71,75],[8,30,35,43,44,73]],[13,524,[66,69,76],[28,51,54,55]],[28,524,[76],[13,51,54,55,66,69]],[54,524,[66,69,76],[13,28,51,55]],[15,532,[66,72,76],[32,51,58,59]],[32,532,[76],[15,51,58,59,66,72]],[51,532,[72],[15,32,58,59,66,76]],[58,532,[66,72,76],[15,32,51,59]],[55,776,[74],[18,41,62,69,76]],[59,784,[74],[19,47,62,72,76]],[34,774,[69,72],[]],[69,774,[34,72],[]],[72,774,[34,69],[]],[66,538,[37,74],[]],[74,538,[37,66],[]],[65,284,[50,76],[]],[76,284,[50,65],[]],[57,180,[71],[]],[71,180,[57],[]],[61,664,[],[]],[63,240,[75],[]],[75,240,[63],[]]],\"edges\":[[23,[13,15,28,32,34,51,54,55,58,59,66,69,72,76]],[32,[8,30,35,43,44,46,49,57,60,61,63,64,71,73,75]]],\"groupings\":[3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00016.record008" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00016.record008\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-8,18,23],[-1,24,28,30,32],[-5,30,32],[-8,28,32],[-10,24,30],[-11,24,28,30],[-12,24,28,32],[-2,26,27,33],[-4,33],[-16,26,27,33],[-3,26,29,33],[-6,33],[-15,29],[-19,26,29,33],[-17,31],[-20,31],[-7,27,29],[-27,7,29],[-29,7,27],[-26,9,31],[-31,9,26],[-25,14,33],[-33,14,25],[-18,28],[-28,18],[-22],[-23,32],[-32,23],[-18,34],[-23,34],[-28,35],[-32,35],[-7,36],[-9,36],[-14,36],[-37,25,26,27],[-25,37],[-26,37],[-27,37],[-38,29,31,33],[-29,38],[-31,38],[-33,38],[-13,39],[-21,39],[-24,40],[-30,40],[-36,41],[-35,41],[-41,42],[-34,42],[-34,-41,43],[-44,37,38],[-38,44],[-37,44],[-37,-38,45],[-40,46],[-39,46],[-44,47],[-44,-46,48],[-45,-46,49],[-49,50],[-42,-48,50],[-43,-47,50],[-50],[2,3,4,6,7,15,16,17,19,20,26,27,29,33],[1,5,8,10,11,12,13,18,21,22,23,24,28,30,32]],\"atoms\":[{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"mate\",\"ridge\":145,\"a\":35,\"owners\":[57,63]},{\"tag\":\"mate\",\"ridge\":146,\"a\":8,\"owners\":[64,71,73,75]},{\"tag\":\"mate\",\"ridge\":146,\"a\":30,\"owners\":[73,75]},{\"tag\":\"mate\",\"ridge\":146,\"a\":35,\"owners\":[71,75]},{\"tag\":\"mate\",\"ridge\":146,\"a\":43,\"owners\":[64,73]},{\"tag\":\"mate\",\"ridge\":146,\"a\":44,\"owners\":[64,71,73]},{\"tag\":\"mate\",\"ridge\":146,\"a\":46,\"owners\":[64,71,75]},{\"tag\":\"mate\",\"ridge\":524,\"a\":13,\"owners\":[66,69,76]},{\"tag\":\"mate\",\"ridge\":524,\"a\":28,\"owners\":[76]},{\"tag\":\"mate\",\"ridge\":524,\"a\":54,\"owners\":[66,69,76]},{\"tag\":\"mate\",\"ridge\":532,\"a\":15,\"owners\":[66,72,76]},{\"tag\":\"mate\",\"ridge\":532,\"a\":32,\"owners\":[76]},{\"tag\":\"mate\",\"ridge\":532,\"a\":51,\"owners\":[72]},{\"tag\":\"mate\",\"ridge\":532,\"a\":58,\"owners\":[66,72,76]},{\"tag\":\"mate\",\"ridge\":776,\"a\":55,\"owners\":[74]},{\"tag\":\"mate\",\"ridge\":784,\"a\":59,\"owners\":[74]},{\"tag\":\"mate\",\"ridge\":774,\"a\":34,\"owners\":[69,72]},{\"tag\":\"mate\",\"ridge\":774,\"a\":69,\"owners\":[34,72]},{\"tag\":\"mate\",\"ridge\":774,\"a\":72,\"owners\":[34,69]},{\"tag\":\"mate\",\"ridge\":538,\"a\":66,\"owners\":[37,74]},{\"tag\":\"mate\",\"ridge\":538,\"a\":74,\"owners\":[37,66]},{\"tag\":\"mate\",\"ridge\":284,\"a\":65,\"owners\":[50,76]},{\"tag\":\"mate\",\"ridge\":284,\"a\":76,\"owners\":[50,65]},{\"tag\":\"mate\",\"ridge\":180,\"a\":57,\"owners\":[71]},{\"tag\":\"mate\",\"ridge\":180,\"a\":71,\"owners\":[57]},{\"tag\":\"mate\",\"ridge\":664,\"a\":61,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":240,\"a\":63,\"owners\":[75]},{\"tag\":\"mate\",\"ridge\":240,\"a\":75,\"owners\":[63]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":57,\"full_literals\":[-18,34]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":63,\"full_literals\":[-23,34]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":71,\"full_literals\":[-28,35]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":75,\"full_literals\":[-32,35]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":34,\"full_literals\":[-7,36]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":37,\"full_literals\":[-9,36]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":50,\"full_literals\":[-14,36]},{\"tag\":\"group_or\",\"kind\":3,\"index\":3,\"members\":[65,66,69],\"full_literals\":[-37,25,26,27]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":65,\"full_literals\":[-25,37]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":66,\"full_literals\":[-26,37]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":69,\"full_literals\":[-27,37]},{\"tag\":\"group_or\",\"kind\":3,\"index\":4,\"members\":[72,74,76],\"full_literals\":[-38,29,31,33]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":72,\"full_literals\":[-29,38]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":74,\"full_literals\":[-31,38]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":76,\"full_literals\":[-33,38]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":49,\"full_literals\":[-13,39]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":60,\"full_literals\":[-21,39]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":64,\"full_literals\":[-24,40]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":73,\"full_literals\":[-30,40]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0003\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0004\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-36,41],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0003\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0004\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-35,false,41],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-41,42],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-34,false,42],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-34,-41,43],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0006\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0007\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-44,37,38],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0006\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0007\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-38,44],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0006\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0007\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-37,false,44],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0006\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0007\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-37,-38,45],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0012\",\"joined_name\":\"grouped3_0011\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-40,46],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0012\",\"joined_name\":\"grouped3_0011\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-39,false,46],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0008\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-44,false,47],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0008\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-44,-46,48],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0008\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-45,-46,49],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"groupKind3\",\"a\":0,\"b\":3,\"direction\":\"forward\",\"full_literals\":[false,-49,50],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-42,-48,50],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-43,-47,50],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":23,\"owners\":[13,15,28,32,34,51,54,55,58,59,66,69,72,76]},{\"tag\":\"edge\",\"edge\":32,\"owners\":[8,30,35,43,44,46,49,57,60,61,63,64,71,73,75]}]}"
  "p cnf 50 67\n-8 18 23 0\n-1 24 28 30 32 0\n-5 30 32 0\n-8 28 32 0\n-10 24 30 0\n-11 24 28 30 0\n-12 24 28 32 0\n-2 26 27 33 0\n-4 33 0\n-16 26 27 33 0\n-3 26 29 33 0\n-6 33 0\n-15 29 0\n-19 26 29 33 0\n-17 31 0\n-20 31 0\n-7 27 29 0\n-27 7 29 0\n-29 7 27 0\n-26 9 31 0\n-31 9 26 0\n-25 14 33 0\n-33 14 25 0\n-18 28 0\n-28 18 0\n-22 0\n-23 32 0\n-32 23 0\n-18 34 0\n-23 34 0\n-28 35 0\n-32 35 0\n-7 36 0\n-9 36 0\n-14 36 0\n-37 25 26 27 0\n-25 37 0\n-26 37 0\n-27 37 0\n-38 29 31 33 0\n-29 38 0\n-31 38 0\n-33 38 0\n-13 39 0\n-21 39 0\n-24 40 0\n-30 40 0\n-36 41 0\n-35 41 0\n-41 42 0\n-34 42 0\n-34 -41 43 0\n-44 37 38 0\n-38 44 0\n-37 44 0\n-37 -38 45 0\n-40 46 0\n-39 46 0\n-44 47 0\n-44 -46 48 0\n-45 -46 49 0\n-49 50 0\n-42 -48 50 0\n-43 -47 50 0\n-50 0\n2 3 4 6 7 15 16 17 19 20 26 27 29 33 0\n1 5 8 10 11 12 13 18 21 22 23 24 28 30 32 0\n"
  "68 -49 0 65 62 0\n69 1 5 8 10 11 12 13 18 21 23 24 28 30 32 0 26 67 0\n70 44 7 0 54 55 41 42 43 38 39 13 15 16 9 12 8 10 11 14 66 0\n71 38 36 0 33 70 35 34 41 42 43 53 18 20 22 36 0\n72 46 42 0 51 30 29 1 50 49 32 31 57 58 46 47 44 45 2 5 6 7 3 69 0\n73 42 0 68 50 48 33 34 35 71 72 61 56 37 38 39 23 21 19 40 0\n74 -48 0 73 65 63 0\n75 44 0 54 55 70 41 39 17 0\n76 47 0 75 59 0\n77 -46 0 75 74 60 0\n78 -43 0 76 65 64 0\n79 -40 0 77 57 0\n80 -39 0 77 58 0\n81 -24 0 79 46 0\n82 -30 0 79 47 0\n83 -13 0 80 44 0\n84 -21 0 80 45 0\n85 -10 0 81 82 5 0\n86 28 32 0 82 81 84 83 85 3 27 4 24 2 6 7 69 0\n87 -28 0 78 25 31 29 49 52 0\n88 32 0 87 86 0\n89 23 0 88 28 0\n90 35 0 88 32 0\n91 34 0 89 30 0\n92 41 0 90 49 0\n93 0 91 92 78 52 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00016.record008.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00016.record008.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00016.record008.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00016.record008.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00016.record008 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00016.record008.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00016.record008.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00016.record008.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00016.record008.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00016.record008 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00016.record008_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00016.record008_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00016.record008_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00016.record008_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00016.record008_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00016.record008_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00016.record008_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00016.record008 Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00016.record008_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00016.record008_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00016.record008_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00016.record008
