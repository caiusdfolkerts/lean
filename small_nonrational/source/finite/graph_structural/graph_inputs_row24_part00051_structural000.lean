module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow24Part00051Data
public import GraphInputsRow24Part00051Frames
public import GraphInputsRow24Part00051Leaves
public import GraphInputsRow24Part00051Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00051.record005
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00051.record005
def vertexColumn : Fields := ⟨10, hexnat% "1f2e2b48f2e2aaa6aa6aa699a968ba1e9a6658b61da4e4b86e4785e0fae1b44f1e26a96a669a6599964b91e5a5654b51d64d4b46d4745d0f783b0ea368e6338e9364e5334cb31cf0ba2d8b92e2b4acab1ae1b46c9b16c3b61e4751d2729d1725c3783c4f198564382e078651550d0b41da0d8390ca318c9314e0b42c2b06d0711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "1b6db6db6db6d34924db6db6db6db4d2492492492492492492492492492489249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨67, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨89, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "50000157fffffffc000000", 576460752303423488, hexnat% "2a000000000000000", hexnat% "20800080000000000000000", hexnat% "a000000000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "5000015ffffff5fc000000", 42949672960, hexnat% "2a000000000000000", hexnat% "a800000000000000000000", hexnat% "20000080000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "d00003479f7ff59c000000", 1756544592162848768, hexnat% "20000080000000200000000", 11529215046068469760, hexnat% "2800000000000000000000", 35970351104]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c3 c1
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c4 c0
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "700001c1ff7ff47c000000", 2161868558626193408, hexnat% "20000080000000200000000", hexnat% "22000000000000000", hexnat% "8800000000000000000000", 40802189312]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c6 c1
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c7 c1
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c8 c0
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20800083ffec67eb4000000", 344697029525504, hexnat% "3c000000000000000", hexnat% "f000000000000000000000", 5368709120]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "500003fd57bbb40c000000", hexnat% "20800080000000010000000", hexnat% "a000000000000000000000", 191402984163246080, 75041668595712, 51002736640]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "c000030fddfffffc000000", 1161928703861587968, 16140901064495857664, hexnat% "3800000000000000000000", hexnat% "20000080002000000000000"]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "d0000342846f2ffc000000", hexnat% "2000008020008000000000", hexnat% "20800082002001000000000", 576900556954533888, 78812993478983680, 1459166554145947648]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c13 c12
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "300000cdfdfffffc000000", 1297036692682702848, hexnat% "32000000000000000", hexnat% "c800000000000000000000", hexnat% "20000080002000000000000"]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "700001c02c72effc000000", hexnat% "8000020200080000000000", hexnat% "20800082002001000000000", 576884064280117248, 112589990684262400, 1459170677314551808]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c16 c15
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3e004222144000000", hexnat% "f800000000000000000000", hexnat% "20000080002000610000000", 691302542801371136, 1153273382687473664, 173516812976128, 459367164676145152]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c18 c17
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c19 c14
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c20 c11
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c21 c10
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c22 c9
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c23 c5
  c24
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00051.record005_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00051.record005_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00051.record005_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00051.record005_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00051.record005_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00051.record005_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00051.record005_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00051.record005_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00051.record005_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00051.record005

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00051.record008
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00051.record008
def vertexColumn : Fields := ⟨10, hexnat% "e325c2e9a6a398e938ae4785e0fae1e26592e785a95a599655c368d6364d2b61d4745d0f6c368ce32ce8b92cab46c9b16c3ba1d8791d4749ca745e0f23c4f0bc741c98a198560d90e07871a258991465154358350d0758328c6314c3342c8b06d0711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "1b6da6d24d36db49249a49349269249a492492449249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨69, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨76, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "28021af75ff80000000", hexnat% "10001800000000000000", hexnat% "1000440080000000000", 13835058055282163712, hexnat% "200000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "180f5e00c8d80000000", 1589137899520, hexnat% "200801000000000000", hexnat% "12000000200000000000", 4011018418126848, 17592186044416]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [14123289262510047232, 3940855832379392, hexnat% "3800000000800000000", hexnat% "200001500200000000", hexnat% "10001800010000000000", 48378511622144, 2440951015214678016]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c3 c0
  c4
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00051.record008_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00051.record008_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00051.record008_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00051.record008_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00051.record008_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00051.record008_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00051.record008_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00051.record008_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00051.record008_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00051.record008

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00051.record009
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00051.record009
def vertexColumn : Fields := ⟨10, hexnat% "2e2e2a5a2e9a663a4e2b91e1783eb8789964b96958d934ad4745d0f783b0ea368e6338e532cf0b92cab86d1b26c5b0ed8791d4749ca745e0f23c4f0bc741ca8a62866158364381e1c68962465154354341da0d8390ca318c530ce0b42c8b06d0711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "34db4da49a6da6d2492492492492492492491249249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨64, by decide⟩, ⟨68, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨75, by decide⟩, ⟨79, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "941282deffe00000000", 540431955284459520, hexnat% "801002100000000000", hexnat% "80100000000000000000", 22517998136852480]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "9c027eb67fe00000000", 1729382256910270464, hexnat% "110004000000000000", hexnat% "80000000000000000000", 4670725394792448]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1013feb67fe00000000", hexnat% "80100004000000000000", hexnat% "c00000000000000000", hexnat% "8000000000000000000", 4670725394792448]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "811027ef244a00000000", hexnat% "400800082000000000", hexnat% "8010000400000000000", 3934190043136, hexnat% "801000100000000000", 4644337115725824]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨61, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨72, by decide⟩ c4 c1
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "80100717f81e00000000", 4035225403562917888, hexnat% "1c00000000000000000", 18017697044365312, hexnat% "8010000044000000000", 47288345843204096]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "9c03ff7c23e00000000", hexnat% "80100000200000000000", 6322191859712, hexnat% "10000000000000000", 2278188092751872]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "81113ff7e23e00000000", hexnat% "c00000000000000000", 6322191859712, hexnat% "8000000000000000000", 2278188092751872]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1402ff78a3200000000", hexnat% "80100000200800000000", 2252624447406080, hexnat% "801000100400000000", 5497558138880, hexnat% "8010000400000000000"]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨61, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨72, by decide⟩ c10 c7
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "400b01880200000000", hexnat% "801002100400000000", hexnat% "80100404200800000000", 22521296671735808, hexnat% "8010000044000000000", 47288345843204096, hexnat% "1002000403000000000"]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c12 c11
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c13 c6
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c14 c5
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c15 c0
  c16
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00051.record009_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00051.record009_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00051.record009_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00051.record009_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00051.record009_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00051.record009_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00051.record009_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00051.record009_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00051.record009_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00051.record009

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00051.record011
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00051.record011
def vertexColumn : Fields := ⟨10, hexnat% "7cb8b8aaa9aa9aa5a1eac6398b61da8e63a4e2b86e4785e0fae1e26a96a66996479b14e52d475a358d934ad1b51d1743de0ec3a8da398ce394cb3c2e8b62e4b8ad2b2ac6b86d1b16e8791d4731ca719d1725c3783c8f13c2f1c83a618564381e1c439614554341da0d8390ca318c530ce0b42c2b06d0721c4705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "db6db4db4d36d24db6da6da69b692492492492492492492492492249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨66, by decide⟩, ⟨68, by decide⟩, ⟨72, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨85, by decide⟩, ⟨87, by decide⟩, ⟨91, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "300006b1007fff0000000", hexnat% "2000040006200000000000", hexnat% "1101000000000000000", hexnat% "88080000000000000000000", 351280770934898688, 2770769301995520]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "881811033f9fe9bb0000000", 864692365405716480, hexnat% "200004000000440000000", hexnat% "2000040002004000000000", 1125899906842624]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2000040002104640000000", hexnat% "2000040000400b0000000", hexnat% "80101002001020000000000", hexnat% "8080101000001900000000", 815187816437776384, 333267059620184064, 3597602046083072]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c3 c0
  c4
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00051.record011_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00051.record011_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00051.record011_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00051.record011_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00051.record011_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00051.record011_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00051.record011_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00051.record011_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00051.record011_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00051.record011
