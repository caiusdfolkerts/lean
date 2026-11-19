module
prelude
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow24Part00041Data
public import GraphInputsRow24Part00041Frames
public import GraphInputsRow24Part00041Leaves
public import GraphInputsRow24Part00041Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

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

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00041.record005
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "31ca725c3723c2f07cc699a568da4e8ba1eb16358b61db0e338ae1ba1e4789e1783ec669966659564d98e5392e479c5695954d58d4b51d70da364d3362d2b46d8751d2745d0f71364d5334d332cc73c2d8b52ccb4acab1ae1b46c9b16c3bc1cc729c6785d1783d0f07c96158362384e0bb11c2615254550d60d2344d0b51324c530cd0b22c4b0ac8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "36db6db6db6d24d24da4936db6db4924924924934924924924924d249a492491249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record005 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record005 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record005.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record005.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record005.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 30), (facetIndex 31), (facetIndex 43), (facetIndex 44), (facetIndex 45), (facetIndex 46), (facetIndex 47), (facetIndex 48), (facetIndex 49)]))
 (.leaf ([(facetIndex 33), (facetIndex 61), (facetIndex 69), (facetIndex 70), (facetIndex 71), (facetIndex 72), (facetIndex 73), (facetIndex 74), (facetIndex 75)])))
 (.branch 3
 (.leaf ([(facetIndex 32), (facetIndex 41), (facetIndex 50), (facetIndex 51), (facetIndex 52), (facetIndex 53), (facetIndex 54), (facetIndex 55), (facetIndex 56)]))
 (.leaf ([(facetIndex 62), (facetIndex 63), (facetIndex 64), (facetIndex 65), (facetIndex 66), (facetIndex 67), (facetIndex 68)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 29), (facetIndex 86), (facetIndex 87), (facetIndex 88), (facetIndex 91), (facetIndex 92), (facetIndex 93)]))
 (.leaf ([(facetIndex 95), (facetIndex 96), (facetIndex 97)])))
 (.branch 7
 (.leaf ([(facetIndex 34), (facetIndex 35), (facetIndex 36)]))
 (.leaf ([(facetIndex 38), (facetIndex 39), (facetIndex 40), (facetIndex 57), (facetIndex 58), (facetIndex 59), (facetIndex 85)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "2da2480493800000024924b6db6c8ffa492480000017fc6d8a02z16;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 37), (facetIndex 42), (facetIndex 60)]))
 (.branch 2
 (.leaf ([(facetIndex 89), (facetIndex 90), (facetIndex 94)]))
 (.leaf ([(facetIndex 98), (facetIndex 105), (facetIndex 112)]))))
 (.branch 4
 (.leaf ([(facetIndex 76), (facetIndex 77), (facetIndex 78), (facetIndex 79), (facetIndex 80), (facetIndex 81), (facetIndex 82), (facetIndex 83), (facetIndex 84)]))
 (.branch 5
 (.leaf ([(facetIndex 99), (facetIndex 100), (facetIndex 101), (facetIndex 102), (facetIndex 103), (facetIndex 104), (facetIndex 108), (facetIndex 110), (facetIndex 111)]))
 (.leaf ([(facetIndex 106), (facetIndex 107), (facetIndex 109)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "292cb549248800400480036db6dbz39;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 6
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped2_0000 : List Nat := [0, 1, 2, 3]
def grouped2_0002 : List Nat := [4]
def grouped2_0003 : List Nat := [4, 5]
def grouped2_0004 : List Nat := [4, 5, 6, 7]
def grouped2_0005 : List Nat := [5]
def grouped2_0006 : List Nat := [6]
def grouped2_0007 : List Nat := [6, 7]
def grouped2_0008 : List Nat := [7]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record005 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record005_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00041.record005" "{\"atoms\":[{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":105},{\"tag\":\"facet\",\"index\":112},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0003\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":2}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00041.record005" 32

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00041.record005" "{\"ridges\":[[21,769],[22,784],[49,776],[56,784],[68,776],[75,784],[85,784],[94,774]],\"owners\":[[21,769,[22,37,56,75],[49,68]],[49,776,[112],[21,68,85,94,105]],[68,776,[105],[21,49,85,94,112]],[22,784,[98,105,112],[56,75,85]],[56,784,[112],[22,75,85,98,105]],[75,784,[105],[22,56,85,98,112]],[85,784,[98],[22,56,75,105,112]],[94,774,[37,98],[]]],\"edges\":[[44,[21,22,37,49,56,68,75,85,94,98,105,112]]],\"groupings\":[2]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00041.record005" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00041.record005\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-6,-3],[-6,-4],[-6,-5],[-22,-19],[-22,-20],[-22,-21],[-23,-7],[-23,-8],[-23,-9],[-23,-12],[-23,-13],[-23,-14],[-24,-7],[-24,-8],[-24,-9],[-24,-12],[-24,-13],[-24,-14],[-24,-17],[-1,2,6,11,16],[-10,24],[-15,23],[-2,22,23,24],[-11,24],[-16,23],[-17,22],[-18,6,22],[-25,19,20,21],[-26,3,4,5],[-27,7,8,9,12,13,14,17],[-28,25],[-29,26],[-29,27],[-30,28],[-30,29],[-31,30],[31],[-32,22,23,24],[-22,32],[-23,32],[-24,32],[1,2,6,10,11,15,16,17,18,22,23,24]],\"atoms\":[{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":105},{\"tag\":\"facet\",\"index\":112},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":37,\"b\":34},{\"tag\":\"incompatible\",\"a\":37,\"b\":35},{\"tag\":\"incompatible\",\"a\":37,\"b\":36},{\"tag\":\"incompatible\",\"a\":98,\"b\":95},{\"tag\":\"incompatible\",\"a\":98,\"b\":96},{\"tag\":\"incompatible\",\"a\":98,\"b\":97},{\"tag\":\"incompatible\",\"a\":105,\"b\":38},{\"tag\":\"incompatible\",\"a\":105,\"b\":39},{\"tag\":\"incompatible\",\"a\":105,\"b\":40},{\"tag\":\"incompatible\",\"a\":105,\"b\":57},{\"tag\":\"incompatible\",\"a\":105,\"b\":58},{\"tag\":\"incompatible\",\"a\":105,\"b\":59},{\"tag\":\"incompatible\",\"a\":112,\"b\":38},{\"tag\":\"incompatible\",\"a\":112,\"b\":39},{\"tag\":\"incompatible\",\"a\":112,\"b\":40},{\"tag\":\"incompatible\",\"a\":112,\"b\":57},{\"tag\":\"incompatible\",\"a\":112,\"b\":58},{\"tag\":\"incompatible\",\"a\":112,\"b\":59},{\"tag\":\"incompatible\",\"a\":112,\"b\":85},{\"tag\":\"mate\",\"ridge\":769,\"a\":21,\"owners\":[22,37,56,75]},{\"tag\":\"mate\",\"ridge\":776,\"a\":49,\"owners\":[112]},{\"tag\":\"mate\",\"ridge\":776,\"a\":68,\"owners\":[105]},{\"tag\":\"mate\",\"ridge\":784,\"a\":22,\"owners\":[98,105,112]},{\"tag\":\"mate\",\"ridge\":784,\"a\":56,\"owners\":[112]},{\"tag\":\"mate\",\"ridge\":784,\"a\":75,\"owners\":[105]},{\"tag\":\"mate\",\"ridge\":784,\"a\":85,\"owners\":[98]},{\"tag\":\"mate\",\"ridge\":774,\"a\":94,\"owners\":[37,98]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[95,96,97],\"full_literals\":[-25,19,20,21]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[34,35,36],\"full_literals\":[-26,3,4,5]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[38,39,40,57,58,59,85],\"full_literals\":[-27,7,8,9,12,13,14,17]},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0003\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-28,false,25],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"grouped2_0007\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-29,26,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"grouped2_0007\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-29,false,27],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0004\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-30,28,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0004\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-30,false,29],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-31,false,30],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":3,\"index\":2,\"members\":[98,105,112],\"full_literals\":[-32,22,23,24]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":98,\"full_literals\":[-22,32]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":105,\"full_literals\":[-23,32]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":112,\"full_literals\":[-24,32]},{\"tag\":\"edge\",\"edge\":44,\"owners\":[21,22,37,49,56,68,75,85,94,98,105,112]}]}"
  "p cnf 32 42\n-6 -3 0\n-6 -4 0\n-6 -5 0\n-22 -19 0\n-22 -20 0\n-22 -21 0\n-23 -7 0\n-23 -8 0\n-23 -9 0\n-23 -12 0\n-23 -13 0\n-23 -14 0\n-24 -7 0\n-24 -8 0\n-24 -9 0\n-24 -12 0\n-24 -13 0\n-24 -14 0\n-24 -17 0\n-1 2 6 11 16 0\n-10 24 0\n-15 23 0\n-2 22 23 24 0\n-11 24 0\n-16 23 0\n-17 22 0\n-18 6 22 0\n-25 19 20 21 0\n-26 3 4 5 0\n-27 7 8 9 12 13 14 17 0\n-28 25 0\n-29 26 0\n-29 27 0\n-30 28 0\n-30 29 0\n-31 30 0\n31 0\n-32 22 23 24 0\n-22 32 0\n-23 32 0\n-24 32 0\n1 2 6 10 11 15 16 17 18 22 23 24 0\n"
  "43 30 0 37 36 0\n44 28 0 43 34 0\n45 29 0 43 35 0\n46 25 0 44 31 0\n47 26 0 45 32 0\n48 27 0 45 33 0\n49 6 32 0 41 24 21 40 25 22 39 26 23 27 20 42 0\n50 -6 0 47 1 2 3 29 0\n51 32 0 50 49 0\n52 -24 0 48 13 14 15 16 17 18 19 30 0\n53 22 0 51 52 48 26 38 7 8 9 10 11 12 30 0\n54 -19 0 53 4 0\n55 -20 0 53 5 0\n56 -21 0 53 6 0\n57 0 54 55 46 56 28 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record005.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record005.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record005.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record005.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record005 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record005.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record005.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record005.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record005.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record005 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record005_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record005_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record005_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record005_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record005_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record005_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record005_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record005 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record005_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record005_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00041.record005_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00041.record005
