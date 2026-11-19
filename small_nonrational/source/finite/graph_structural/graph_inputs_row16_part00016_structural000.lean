module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow16Part00016Data
public import GraphInputsRow16Part00016Frames
public import GraphInputsRow16Part00016Leaves
public import GraphInputsRow16Part00016Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

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
