module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow29Part00077Data
public import GraphInputsRow29Part00077Frames
public import GraphInputsRow29Part00077Leaves
public import GraphInputsRow29Part00077Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00077.record006
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record006
def vertexColumn : Fields := ⟨10, hexnat% "3b0ea2b89e0f8cd274cb26c9723c1f3a2e4b32ac9b29c8f2e2b2aaa9aa9a8eaa6a5a36a3a2e87ac599695b0e63a4e8789e17b316c4f1ca5a93a4d98e4b91e72559715656354d475c358d8b52d1b61d2745d0f72368d6338f1364cd38cd332cc73c2d8b32e2b4acab1ae1b26c5b0ef0761d4785d1725e0f43c8f07f06858568384e684b11c4a91a4551358324c5322c4b41c4705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "db6db6db6db6db6db6db6db4d26934d26936936db69b6d369b4db49b49a4da4d2692492491249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨51, by decide⟩, ⟨54, by decide⟩, ⟨57, by decide⟩, ⟨62, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨79, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨87, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "b200000000cd037fe00000", hexnat% "204240000000000000", 2251902892900352, hexnat% "480000000000000000000", hexnat% "12000000008000000000", hexnat% "24400000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "280600048cd9b22600000", 4755801206503243776, 1568669696, hexnat% "36000000000000000000", hexnat% "b400000000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "9600000000819b7fe00000", hexnat% "204240000000000000", 2264993953218560, hexnat% "2080000000000000000000", hexnat% "12000000400000000000", hexnat% "24400000000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "204240000302400000", 1956642816, hexnat% "b600000000000000000000", 2265097032433664, 212755499974656, hexnat% "36400000000000000000", hexnat% "80000000000009000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨22, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c4 c1
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
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record006_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record006_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record006_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record006_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record006_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record006_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record006_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record006_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record006_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00077.record006

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00077.record022
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record022
def vertexColumn : Fields := ⟨10, hexnat% "2789d26ce4b329c972e2b2a9aa9a968da8e87ae1b2699a96958d68d876a3a4e33a2e1bb316c571ca5a9366392e479c95a5356352d4753362d2b72358f1354cd38cd331cf0b62ccb8ad2b1ae1b26c5b0ef0761cc789d2719e1725c570de0f0bf308b06cc49928388e139914c4711a4652344d0b58344c9314c8b12c8711c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "36926db6db6db6db6d249249b6da6db6924da49a4d26d349b49b4d2691249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [1, 2, 3, 4]
def candidates : List (Fin raw.n) := [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩, ⟨9, by decide⟩, ⟨10, by decide⟩, ⟨11, by decide⟩, ⟨12, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩, ⟨15, by decide⟩, ⟨16, by decide⟩, ⟨17, by decide⟩, ⟨18, by decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩, ⟨95, by decide⟩, ⟨96, by decide⟩, ⟨97, by decide⟩, ⟨98, by decide⟩, ⟨99, by decide⟩, ⟨100, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1bffffc7fffc7fcf33cbffffff", hexnat% "38000000000004000000", hexnat% "4000000000180000000000000", 17884512256000, 35769024512000, 144115188075855872]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .size 1
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .size 2
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨77, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1ffffffffffff7ffffefffffff", 2251800082120704]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨71, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1fffffcf7fffffffffffffffff", hexnat% "800000000000000000", hexnat% "30000000000000000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨98, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨8, by decide⟩ c1 c2
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨20, by decide⟩ c1 c8
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨71, by decide⟩ c2 c9
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨77, by decide⟩ c2 c10
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨98, by decide⟩ c6 c11
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1bffffcf7ffff7ffffffffffff", hexnat% "800008000000000000", hexnat% "30000000000000000000", hexnat% "4000000000000000000000000"]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c13 c12
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c14 c7
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c11 c3
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1fffffcfffffffdff7ffffffff", 35218731827200, hexnat% "30000000000000000000"]
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨98, by decide⟩ c17 c16
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1bffffcfffffffdf77ffffffff", hexnat% "30000000000000000000", hexnat% "4000000000000000000000000", 35768487641088]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c19 c18
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1bffffff3ffff7df37cfffffff", hexnat% "4000000000000000000000000", hexnat% "c00008000000000000", 275146342400, 35769024512000]
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c21 c20
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨64, by decide⟩ c22 c15
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1dffffde3efbe75f37cfffffff", 35769024512000, hexnat% "1800010000000000000", hexnat% "2000020000000000000000000", 2392812448382976, hexnat% "410400000000000000"]
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨96, by decide⟩ c24 c23
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1affffc0fefa7ffdff79ffffff", hexnat% "10400020080000000", hexnat% "1000001000000000000000000", hexnat% "4000000000180000002000000", hexnat% "3e000000000004000000"]
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1cffffd63ffbeffffffbffffff", hexnat% "400400000000000000", hexnat% "28000000000004000000", hexnat% "1800010000000000000", hexnat% "3000000000000000000000000"]
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1cffffc03ffa6ffffff9ffffff", hexnat% "400400000000000000", hexnat% "3000000000010000000000000", hexnat% "800080000000000000", hexnat% "1000100000004000000", hexnat% "3e000000000002000000"]
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨98, by decide⟩ c28 c27
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "19ffffc7fffe6bdf73dbffffff", hexnat% "2000020000000000000000000", hexnat% "4000000000180000000000000", hexnat% "18000000000004000000", 1161686111223808, 4503599627370496]
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1bfffffe3efa7f5f774fffffff", hexnat% "4000000000180000000000000", 35769024512000, 288371116055986176, hexnat% "1c00000000000000000", hexnat% "10000000000000000"]
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1bffffcffefa7bcf73cbffffff", hexnat% "30000000000004000000", hexnat% "4000000000180000000000000", hexnat% "10400000000000000", 1143510078062592, 35768487641088]
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "19ffffcffffe6bcf77dbffffff", hexnat% "2000020000000000000000000", hexnat% "4000010000000000000000000", 108086391124000768, 1179261117399040, 4503599627370496]
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1ffffffe3efbeb4f73cbffffff", hexnat% "1800010000000000000", hexnat% "410400800000000000", 17609433022464, 1125900712148992, 35768487641088]
  let c35 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1fffffc83efa7b4f73c9ffffff", hexnat% "800080000000000000", hexnat% "410400800000000000", hexnat% "1000100000004000000", hexnat% "36000000000002000000", 1143510078062592, 35768487641088]
  let c36 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨98, by decide⟩ c35 c34
  let c37 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c36 c33
  let c38 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨96, by decide⟩ c37 c32
  let c39 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨75, by decide⟩ c38 c31
  let c40 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c39 c30
  let c41 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c40 c29
  let c42 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c41 c26
  let c43 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c42 c25
  let c44 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c43 c0
  c44
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record022_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record022_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record022_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record022_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record022_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record022_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record022_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record022_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record022_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00077.record022
