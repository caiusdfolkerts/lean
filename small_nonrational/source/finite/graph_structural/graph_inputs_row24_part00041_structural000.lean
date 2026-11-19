module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow24Part00041Data
public import GraphInputsRow24Part00041Frames
public import GraphInputsRow24Part00041Leaves
public import GraphInputsRow24Part00041Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00041.record006
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record006
def vertexColumn : Fields := ⟨10, hexnat% "370bc1f29a968da8e8ba1eb16358b61db0e6394e3392e2b86e8789e1783ea6659366392e479c54d52d475c358d534cd4b4ad1b61d2745d0f713a4e5334e332cc73a2d8b92d4b32e2b4acab1ae1b26c5b0ef0761d4731d2729c6785d1783c1fc2896158364388e1382ec2495154354348d1342dc0e1324c530ce0b42c8b12c2b41c8711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "6db6db6d24924926926db6da4924924d2492492492492492492492492249249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2, 3]
def candidates : List (Fin raw.n) := [⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩, ⟨95, by decide⟩, ⟨96, by decide⟩, ⟨97, by decide⟩, ⟨98, by decide⟩, ⟨99, by decide⟩, ⟨100, by decide⟩, ⟨101, by decide⟩, ⟨102, by decide⟩, ⟨103, by decide⟩, ⟨104, by decide⟩, ⟨105, by decide⟩, ⟨106, by decide⟩, ⟨107, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "fffc0ffe207ffffffff00000000", hexnat% "1c000000000000000000", hexnat% "200001000000000000000000", hexnat% "f80000000000000000", hexnat% "1f0000000000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .size 3
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨98, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "fffc0ffe207ffffffff00000000", hexnat% "1c000000000000000000", hexnat% "100000800000000000000000", hexnat% "1780000000000000000", hexnat% "2f0000000000000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨98, by decide⟩ c1 c3
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "ffd02dfe816ff017fff00000000", hexnat% "14010000000000000000", hexnat% "2802000000000000000000000", hexnat% "3e80000000000000000", hexnat% "7d0000000000000000000000", 71635381572861952]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "fff88fff0447f0870ad00000000", hexnat% "c038000000000000000", 8048768712704, hexnat% "770000000000000000000000", hexnat% "3b80000000000000000", 69673852828909568]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "fffbfffe00780007fff00000000", hexnat% "1c000000000000000000", hexnat% "400002000052000000000000", hexnat% "1f80000000000000000", 9151314442816847872, 48835908459298816]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "ffe81bffc0f8100bfff00000000", hexnat% "1024000000000000000000000", 9079327217523097600, hexnat% "3f00000000000000000", hexnat% "7c0000000000000000000000", 71776119061217280]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "ffe08aff3ff880837ff00000000", hexnat% "c000000000000000000", hexnat% "770000000000000000000000", hexnat% "1805000000000000000000000", 8574924059257602048, 69673852828909568]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "fff80ffe0440000303100000000", 8581344657408, 9151384811561025536, hexnat% "3b80000000000000000", hexnat% "1c038000000000000000", hexnat% "7f0000000000000000000000", 71925652642594816]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨70, by decide⟩ c10 c9
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c11 c8
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨85, by decide⟩ c12 c7
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨97, by decide⟩ c13 c6
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c14 c5
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c15 c4
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c16 c2
  c17
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record006_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record006_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record006_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record006_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record006_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record006_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record006_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record006_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record006_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00041.record006

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00041.record022
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record022
def vertexColumn : Fields := ⟨10, hexnat% "f23c48f13cb29caaa99ab19c6999568b91e0fbc1e2749b25c9aa5998e539e1745b15c5995558d535c362d4b61d4743db0dc3a8e6364d53a2d8b92d4b32e2b2ad1b26e8761e4751cc789c6745c5783d0f0bc1f0e836b05c1a25898a5190e645516254543530c3322c2b06c4709c17"⟩
def kindColumn : Fields := ⟨3, hexnat% "6db6db6db6d24d249269249269b4926db49b4924da49249b489249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨23, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨54, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1307c0308c1f4000000", hexnat% "200004c000000c00000", 216172782248001536, hexnat% "a0000002000000000", hexnat% "50000001800000000", hexnat% "800000040000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "13074030491cc000000", 720575941184585728, hexnat% "840000080800000000", hexnat% "200004c000000c00000", hexnat% "a0000006000000000", hexnat% "10100000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2000b4f084134c00000", hexnat% "a0000002000000000", 288230378433413120, hexnat% "1007000000040000000", hexnat% "50000001800000000", hexnat% "b00000048000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [9152726292989214720, hexnat% "1300002008000000000", hexnat% "2000048000000c00000", hexnat% "50000000800000000", hexnat% "a0000006000000000", hexnat% "800000080000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1bc70030ca9e0000000", 720575940647714816, 360287970390966272, hexnat% "200004c000000c00000", hexnat% "30000001000000000", 274877906944]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "28b004f0869a0c00000", 720575940647714816, hexnat% "40000041000000000", hexnat% "1300000008000000000", 360287970390966272, 8070450533321670656]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1bc30030cf9e8000000", 360287970256748544, 720575940647714816, hexnat% "30004000000000000", hexnat% "2000048000000c00000", 4611686018427387904]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "287004d0479a8c00000", 360287970256748544, hexnat% "280000080000000000", 720575940647714816, hexnat% "1100002008000000000", 8070450533321670656]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2820b4d0451b8c00000", hexnat% "80000082000000000", 4899916394646208512, hexnat% "50000000800000000", hexnat% "1003002000040000000", hexnat% "300000008000000000"]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "804a010451b0000000", hexnat% "50000000800000000", hexnat% "a0000002000000000", hexnat% "200004c000000c00000", 360287970390966272, hexnat% "1003002000040000000", hexnat% "300000088000000000"]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c10 c7
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c11 c6
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c12 c5
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨71, by decide⟩ c13 c4
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c14 c3
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c15 c2
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c16 c1
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c17 c0
  c18
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record022_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record022_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record022_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record022_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record022_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record022_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record022_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record022_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record022_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00041.record022

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00041.record024
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record024
def vertexColumn : Fields := ⟨10, hexnat% "7313c72aaa669c6999566394e3391ef05c9aa5994e5c5995554d58d534cd4b5c3a8e6364d538ce8b62d4b32e2b2ad1b26d8791d4731e2719d1715d0f23c4f4703cb083a0d82e07ac17058946439515150d50d0b41da0e4330e230cc8b0ac1b11c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "69b6db6da49a49a4934926d24d2493492492489249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨78, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "dd6c0a42180000000", hexnat% "40000800000000000000", hexnat% "100000004400000000", 310062279032832, 14073817555009536, 593779228672]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "d5ec0206540000000", hexnat% "40008000000000000000", hexnat% "100000840000000000", 661424963584, 14091341021577216, 292472240472064]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1c681be2bc0000000", hexnat% "c0040000000000000", 14073817555009536, 1729382274090139648, hexnat% "40100000000000000000", 824633720832]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [446910493039263744, hexnat% "18080000000000000", hexnat% "c4040000000000000", hexnat% "40100000000000000000", 1729382282680074240, 274877906944]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "41e802affc0000000", hexnat% "84040000000000000", 14091341021577216, hexnat% "18000040000000000", hexnat% "40100000000000000000", 422212465065984]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [446763459128852480, 1765411053929234432, hexnat% "c4040000000000000", hexnat% "40100000000000000000", hexnat% "18000060000000000", 140737488355328]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [6841454916553146368, 562949953421312, hexnat% "c0000000000000000", hexnat% "40100000000000000000", hexnat% "18000040000000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [1617841444058300416, hexnat% "c4000000000000000", 833223655424, hexnat% "40008880000000000000", hexnat% "10000040100000000", hexnat% "100000000400000000"]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c7 c6
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [446727282619318272, hexnat% "40008880000000000000", hexnat% "c4040000000000000", hexnat% "10000860100000000", 1152921805254557696, hexnat% "100000000000000000", 35871566856192]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c10 c5
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c11 c4
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c12 c3
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c13 c2
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c14 c1
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c15 c0
  c16
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record024_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record024_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record024_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record024_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record024_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record024_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record024_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record024_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record024_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00041.record024

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00041.record025
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record025
def vertexColumn : Fields := ⟨10, hexnat% "13ab19c6a9a66659566394e47bc14e5c5a9665655558d58d5362d476c3a8e6364d534cd8b52d2ba1d8791d4789ca719d1725c5743c8f13ec40f1c24683a318360b81eb05c146439a1645316250d42d0758350cc344c3342c2b06c8711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "249b6db49249b4da49b492492492492491249249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨59, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "50040000000000000", hexnat% "10020002400000000000", 14483578600646770688, hexnat% "c000000000000000000", hexnat% "80080144800000000", 3799912185593856, 45861660786688]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record025_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record025_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record025_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record025_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record025_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record025_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record025_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record025_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record025_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00041.record025

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00041.record032
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record032
def vertexColumn : Fields := ⟨10, hexnat% "b32ca6a99a4eac6599564da8e938cef06c96a5994e6c5595554d68d934cd8b61db0da358d9354e8b62e4b32d2b2ad1b26e8791d4731d2719d1715e0f23c4f0f1c24c83a0d82e07ac170531a2439914358342d0758350cc348d130cc8b0ac1b11c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "6db4db4db49b49b4934924924d2493492492489249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨71, by decide⟩, ⟨75, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "c4235aae0c0000000", 342273575975124992, 9799832789158199296, hexnat% "8800000000000000000", 2836739999662080, 128849018880]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "406c12affc0000000", hexnat% "800800000000000000", hexnat% "84020000000000000", hexnat% "8008000940000000000", 8444249301319680]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "c442ba0eac0000000", 198158387899269120, 9799832789158199296, hexnat% "8800000000000000000", 5629585433559040, 32985348833280]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "880881ebe7cc0000000", hexnat% "c4020000000000000", 562640715776, 486388759756013568, 281474976710656]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "c4020302040000000", hexnat% "8008000840000000000", 486388764050980864, hexnat% "800800005400000000", 592705486848, 292472240472064, 8444249301319680]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c5 c2
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c6 c1
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c7 c0
  c8
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record032_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record032_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record032_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record032_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record032_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record032_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record032_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record032_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record032_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00041.record032

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00041.record035
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record035
def vertexColumn : Fields := ⟨10, hexnat% "f12cc731ac6713cf0aca7296a5693ae1b46b19c6a398e9394e3392e47ac9b15c5695954d68d934cd2b49db0dc358d534ce8b92ccb1ac5ba1d8791d4731e2749e1745e0f23c4f4d03c4c83a499160d82e07ac132439a14352342d076430cc4b0ac1b81c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "1b6da6db69b6db6da4936d26924db4d24934da492489249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨35, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨43, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨70, by decide⟩, ⟨76, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [9015998032117760, hexnat% "10401800000000000000", 4123235713024, 6473924598562816, 432486301715922944, 177435836416]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record035_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record035_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record035_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record035_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record035_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record035_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record035_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record035_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record035_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00041.record035
