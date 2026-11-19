module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow24Part00091Data
public import GraphInputsRow24Part00091Frames
public import GraphInputsRow24Part00091Leaves
public import GraphInputsRow24Part00091Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00091.record001
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00091.record001
def vertexColumn : Fields := ⟨10, hexnat% "ae16c570bc1f2b29c8f2aa96aa6a3a2e87a59a362d8765392e2b86e2785e0fab19c4f1aa699566392e479556352d475534ad1b51d2745d0f6a398ce3a4e5334e332cc73a2d8b52e2b2ac6b86c9b16c3b89ca719e1725c570dc8f13c2f07eb02e0740f2a22a9461990e0ba91265451550d0768350d0b22d0711c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "136926d36d34da4926d26da6d34da4da4926d36db4934da6db4da692449249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨28, by decide⟩, ⟨31, by decide⟩, ⟨36, by decide⟩, ⟨39, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨49, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨63, by decide⟩, ⟨65, by decide⟩, ⟨68, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨83, by decide⟩, ⟨85, by decide⟩, ⟨89, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩, ⟨97, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "9f3021130048097800000", hexnat% "200000000840020000000000", 9223372036854775808, hexnat% "400000000080000000000000", hexnat% "2020000100000080000000000", hexnat% "102000000002001000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1021420099e2041097800000", hexnat% "200090000000020000000000", hexnat% "800000000000000000000", hexnat% "400020000000000000000000", hexnat% "2020000100000080000000000", hexnat% "1020010008000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "21221021200820c9015800000", hexnat% "400020000000000000000000", hexnat% "1001030000080000000", 9889904781739163648, hexnat% "8d0000000000000000000", hexnat% "200000000000020000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4009f31291f0009097800000", 6597069766656, hexnat% "200000000800000000000000", 571746046443520, hexnat% "2122000000000000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "9910290b0069097800000", 666532744850833408, hexnat% "62000000000000000000", hexnat% "100002080000000000", hexnat% "2122000000000000000000000", hexnat% "600000000000000000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "27221b21099f00e9087800000", hexnat% "1020000000000000000", hexnat% "840000000000000000000", 562950221856768]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "27221b21019700e9087800000", 9223372037123211264, hexnat% "1000002000000000000", hexnat% "20080000000000000", hexnat% "840000000000000000000"]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c7 c6
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "27221f31218e00e9087800000", 5066549580791808, 9295429630892703744, hexnat% "800000000000010000000"]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "27221b31218600e9087800000", 5066549580791808, 108086391056891904, 9223372037123211264, hexnat% "840000000000000000000"]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨77, by decide⟩ c10 c9
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "27201931218720e9087800000", 9223372037123211264, hexnat% "840000000000000000000", hexnat% "2020000000000000000000", 108086391056891904]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "26221f30018e00e9087800000", 9295429630892703744, hexnat% "800000000000010000000", hexnat% "120000000000000000", hexnat% "100000000012000000000000"]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "26201b3009960021083800000", hexnat% "840000000000000000000", 13743962456064, hexnat% "120080000000000000", hexnat% "102000000002000010000000", 4503599627370496]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨77, by decide⟩ c14 c13
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨72, by decide⟩ c15 c12
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨97, by decide⟩ c16 c11
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨89, by decide⟩ c17 c8
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "200000000000061087800000", 9889904781705609216, hexnat% "8d0000000000000000000", hexnat% "2020000100000080000000000", hexnat% "400020000080000000000000", hexnat% "102102000002000010000000", hexnat% "1021030008000000000"]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨93, by decide⟩ c19 c18
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c20 c5
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c21 c2
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨23, by decide⟩ c22 c1
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨24, by decide⟩ c23 c0
  c24
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00091.record001_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00091.record001_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00091.record001_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00091.record001_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00091.record001_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00091.record001_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00091.record001_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00091.record001_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00091.record001_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00091.record001

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00091.record006
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00091.record006
def vertexColumn : Fields := ⟨10, hexnat% "5715aa9966a59562d876a394e2b86e4789e178f13a55936565a55552d475a358d534ad1b51d176a398d63a4d532cc73a2cab1ad1b26f07a1d4749ca719e1745c9715c3783c8f13c2fa909c5285a8990e07aa15249916685894a52550d2341d50e2318c5342c4b06e0741c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "6936db69b4936934d349269249a69b492492492492489249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨50, by decide⟩, ⟨52, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨65, by decide⟩, ⟨67, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨78, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "600600600000000000", hexnat% "2004000100091100000000", 59813982306828288, hexnat% "ad000000000000000", hexnat% "404a000000000080000000", 2305847441619943424, 20230369705984]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00091.record006_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00091.record006_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00091.record006_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00091.record006_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00091.record006_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00091.record006_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00091.record006_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00091.record006_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00091.record006_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00091.record006

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00091.record014
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00091.record014
def vertexColumn : Fields := ⟨10, hexnat% "ae2b45d2aca723c2f1b25c96a3aa9a2e966a59564d8b61da8e938ae1ba1e2783e6c5715a4e9a64b959695555352d475a34ad8749d0f5a358ce3a4d9354d332cc73a2d4b32d2b2ac6b86c9b0ee8751d2729c6785d1725c570de0f23c2f07c6ca4a8a85a0e139614c4b12a469194351342d50d1324c8b12c4705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "1b6db6db69b4db69349b49269369269b4d34924d24d269b4da492492449249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2, 3]
def candidates : List (Fin raw.n) := [⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩, ⟨95, by decide⟩, ⟨96, by decide⟩, ⟨97, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fff7b70d8bdc6cffff800000", 9587741394206720, hexnat% "840002400000000000000", hexnat% "320000010000000000", hexnat% "8000001820000000000", hexnat% "c05000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ffbff33baf507ff637800000", hexnat% "4004040080000000000000", 3377702941753344, hexnat% "8000021800108000000", 562984313159680, hexnat% "c05000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ffb793ffffffd5fffa800000", 46179488366592, hexnat% "28000000000005000000", hexnat% "4844000000000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fff797ffffffc4fffb800000", hexnat% "840000000000000000000", 27487790694400, hexnat% "28000000000004000000", 37383395344384]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ffb7bb2bcbffdfffff800000", hexnat% "4040000000200000000000", hexnat% "140400000000000000", hexnat% "c03000000000000000", hexnat% "804000000000000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ffffdfbfefdfc6fefa800000", hexnat% "401000000000000000", 43980532219904, hexnat% "20000000000001000000", 9025895247380480]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ffb79beffbdfc4fefa800000", 9025895247380480, hexnat% "64000000000004000000", hexnat% "4000000000200000000000", hexnat% "1000000a0001000000", hexnat% "800000400000000000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨66, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨75, by decide⟩ c7 c4
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c8 c3
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨69, by decide⟩ c9 c2
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fff79ffffff7d7f76b800000", hexnat% "60000000000004000000", 34628173824, hexnat% "800000008000080000000", 43980465111040]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fff797fffff755ffff800000", hexnat% "60000000000000000000", hexnat% "800000008000000000000", 46179488366592, hexnat% "8000000800000000000"]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fff79ffffffdc7f77b800000", hexnat% "60000000000004000000", hexnat% "800000000000080000000", 580576499204096, 43980465111040]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fff797fffff7d5ff7b800000", hexnat% "28000000000004000000", hexnat% "800000008000080000000", 46179488366592, hexnat% "40000000000000000000"]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fff797fffff3c4f75b800000", 3377702404882432, hexnat% "28000000000004000000", 27522150432768, hexnat% "840000000000000000000", 37383395344384]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c15 c14
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c16 c13
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c17 c12
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c18 c11
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ffbfdbffffffd7fffb800000", 43980532219904, hexnat% "24000000000000000000", hexnat% "4000000000000000000000"]
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ffffdffffffff7ff7b800000", 2214592512, 8796093022208, hexnat% "20000000000000000000"]
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .size 3
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨95, by decide⟩ c22 c21
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ffffdb7fbff7d7bf7b800000", hexnat% "804000000000000000", hexnat% "24000000000004000000", 44255343017984, 2251801961168896]
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨86, by decide⟩ c24 c23
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c25 c20
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ffffff7dbfffffffff800000", hexnat% "24000000000000000", hexnat% "800000000000000000"]
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨97, by decide⟩ c22 c27
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ffffdb7dbffffffff7800000", hexnat% "24000000000000000", hexnat% "24000000000000000000", hexnat% "800000000008000000"]
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨75, by decide⟩ c29 c28
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .size 2
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨86, by decide⟩ c31 c22
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .classes 3 [hexnat% "3ffffffffffffffffff800000"]
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨65, by decide⟩ c31 c33
  let c35 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fffffffdbfffffffff800000", hexnat% "24000000000000000"]
  let c36 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨71, by decide⟩ c35 c34
  let c37 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨75, by decide⟩ c31 c22
  let c38 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fffff7fdbfffffffff800000", hexnat% "8000000000000000000", hexnat% "24000000000000000"]
  let c39 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨71, by decide⟩ c38 c37
  let c40 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨77, by decide⟩ c39 c36
  let c41 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ffffd77dbfffffffff800000", hexnat% "24000000000000000", hexnat% "800000000000000000", hexnat% "28000000000000000000"]
  let c42 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨86, by decide⟩ c41 c40
  let c43 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c42 c32
  let c44 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ffbffb7fffffd7bfff800000", hexnat% "800000000000000000", 44255343017984, hexnat% "4004000000000000000000"]
  let c45 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ffbfdb7fffff57bff3800000", hexnat% "24000000000004000000", hexnat% "800000800008000000", 44255343017984, hexnat% "4000000000000000000000"]
  let c46 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨75, by decide⟩ c45 c44
  let c47 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c46 c43
  let c48 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c47 c30
  let c49 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ffbfff7fbffff7bfff800000", 9070970929152, hexnat% "804000000000000000", hexnat% "4000000000000000000000"]
  let c50 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ffbfff3dbffe67b7ff800000", hexnat% "4000000000004000000000", 26422638804992, hexnat% "424000000000000000", hexnat% "800001800000000000"]
  let c51 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c50 c49
  let c52 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ffbfdbfffff3d7bfeb800000", 1125900175278080, hexnat% "24000000000004000000", 44255343017984, hexnat% "4000000008000000000000"]
  let c53 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨65, by decide⟩ c31 c22
  let c54 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨75, by decide⟩ c31 c53
  let c55 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ffbfd7fdfff7ffffff800000", hexnat% "20000000000000000", hexnat% "4000000008000000000000", hexnat% "28000000000000000000"]
  let c56 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨74, by decide⟩ c55 c54
  let c57 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ffbfd3fffff7cfbfeb800000", 17592454479872, hexnat% "28000000000004000000", hexnat% "4000000008204000000000", hexnat% "4000000000000000000"]
  let c58 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c57 c56
  let c59 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ffbfd3bdbff25fbfe3800000", hexnat% "424000000000000000", hexnat% "24000000000004000000", hexnat% "4000000008204000000000", hexnat% "8000001800008000000", 1125900175278080]
  let c60 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨71, by decide⟩ c59 c58
  let c61 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c60 c52
  let c62 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c61 c51
  let c63 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c62 c48
  let c64 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c63 c26
  let c65 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fff7ff89fffdeff7ff800000", hexnat% "800000000000000000000", hexnat% "140000000000000000", 580576499204096, hexnat% "620000000000000000"]
  let c66 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ffb79bc9fff7e7b7fb800000", hexnat% "64000000000004000000", 26422638804992, hexnat% "4800000008000000000000", hexnat% "320000000000000000", hexnat% "40000004000000000"]
  let c67 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c66 c65
  let c68 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ffbfdbebffffd7fffb800000", hexnat% "100000080000000000", hexnat% "24000000000004000000", hexnat% "4000000000200000000000", hexnat% "40000000000000000"]
  let c69 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ffbfd37bffffddfffa800000", hexnat% "840000000000000000", hexnat% "4000000000200000000000", hexnat% "24000000000004000000", hexnat% "8000000020001000000"]
  let c70 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ffbffb1baffffffeff800000", hexnat% "4004040000000000000000", hexnat% "201000000100000000", hexnat% "c04000000000000000"]
  let c71 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fffffb1bbfffeff7ff800000", 17626545782784, hexnat% "600000000000000000", hexnat% "4040000000000000000", hexnat% "804000000000000000"]
  let c72 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ffbfd37bffffddfffb800000", hexnat% "840000000000000000", 37383395344384, hexnat% "28000000000004000000", hexnat% "4004000000000000000000"]
  let c73 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ffbfd32bafffddfffb800000", hexnat% "4000000000200000000000", hexnat% "140000020000000000", hexnat% "c05000000000000000", hexnat% "24000000000004000000", hexnat% "8000000000000000000"]
  let c74 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨69, by decide⟩ c73 c72
  let c75 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨24, by decide⟩ c74 c71
  let c76 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c75 c70
  let c77 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨65, by decide⟩ c76 c69
  let c78 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c77 c68
  let c79 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ffb79bfbfff3ffff7f800000", 3377701868011520, hexnat% "4004040000000000000000", hexnat% "60000000000000000000", hexnat% "800000000000000000000"]
  let c80 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ffb79bffffffcff77b800000", 17626545782784, hexnat% "64000000000004000000", 35186519572480, hexnat% "4800000000000000000000"]
  let c81 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ffb793ebfff3ddbf7a800000", 3377701868011520, hexnat% "140000020000000000", hexnat% "28000000000005000000", hexnat% "4844000000000000000000", 35459249995776]
  let c82 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c81 c80
  let c83 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c82 c79
  let c84 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ffb79b6b9ff7d7bf7b800000", hexnat% "100000080000000000", hexnat% "846000000000000000", hexnat% "64000000000004000000", hexnat% "800000008000080000000", hexnat% "4000000000204000000000"]
  let c85 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fff79ffffff3d7ff7b800000", 43980532219904, hexnat% "60000000000000000000", 3377701868011520, hexnat% "800000000000000000000"]
  let c86 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fff797ddfff6feffff800000", hexnat% "8000001010000000000", hexnat% "800000008000000000000", hexnat% "220000000000000000", hexnat% "60000000000000000000"]
  let c87 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fff79ffffff3dfff7b800000", hexnat% "60000000000004000000", 3377701868011520, hexnat% "800000000000000000000", 35184372088832]
  let c88 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fff797fffff0c7f77a800000", hexnat% "840000000000000000000", 26422638804992, 1970324836974592, hexnat% "28000000000005000000", 2286986333257728]
  let c89 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c88 c87
  let c90 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c89 c86
  let c91 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c90 c85
  let c92 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ffb79bffeffdc7f76b800000", hexnat% "64000000000004000000", 1153484454828703744, hexnat% "4800000000000000000000", 35186519572480, 26422638804992]
  let c93 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ffffff5d9ffdeff7ff800000", hexnat% "806000000000000000", hexnat% "200000100000000000", 562984313159680, hexnat% "20000000000000000"]
  let c94 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fff7fbdd9fffeff7ff800000", hexnat% "200000100000000000", hexnat% "804000000000000000000", hexnat% "24000000800000000", 2305843009213693952]
  let c95 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fff7bb5d9ff7dfbf7f800000", hexnat% "220000000000000000", hexnat% "806000000000000000", 2287259063681024, hexnat% "804000000000080000000", hexnat% "40000000000000000000"]
  let c96 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c95 c94
  let c97 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨86, by decide⟩ c96 c93
  let c98 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ffb79beffff7c7b76b800000", hexnat% "100000080000000000", hexnat% "64000000000004000000", 17626814218240, hexnat% "4000000008204000000000", hexnat% "800000000000080000000"]
  let c99 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fffff74dafdde4b7ef800000", hexnat% "805000000000000000", hexnat% "8000020030000000000", 9070970929152, hexnat% "320000000000000000", 580576767639552]
  let c100 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ffb7db7f8ff3dfbf6b800000", hexnat% "24000000000004000000", hexnat% "807000000000000000", 1125902322761728, hexnat% "4800000008000000000000", 35459249995776]
  let c101 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ffb7fb4d8ff1c4b76f800000", hexnat% "807000000000000000", 580576767639552, hexnat% "320000010000000000", hexnat% "4804000000000000000000", 46454366273536, 3377701868011520]
  let c102 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c101 c100
  let c103 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨78, by decide⟩ c102 c99
  let c104 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c103 c98
  let c105 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨24, by decide⟩ c104 c97
  let c106 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c105 c92
  let c107 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨66, by decide⟩ c106 c91
  let c108 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c107 c84
  let c109 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨70, by decide⟩ c108 c83
  let c110 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c109 c78
  let c111 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c110 c67
  let c112 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c111 c64
  let c113 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c112 c19
  let c114 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c113 c10
  let c115 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c114 c1
  let c116 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨23, by decide⟩ c115 c0
  c116
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00091.record014_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00091.record014_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00091.record014_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00091.record014_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00091.record014_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00091.record014_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00091.record014_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00091.record014_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00091.record014_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00091.record014
