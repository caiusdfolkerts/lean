module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow24Part00037Data
public import GraphInputsRow24Part00037Frames
public import GraphInputsRow24Part00037Leaves
public import GraphInputsRow24Part00037Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00037.record009
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00037.record009
def vertexColumn : Fields := ⟨10, hexnat% "bcacb2ac6a3a2eb26c58d68d8b65392e2b86e4789e0fab1ca7198e4b9c9715356352d54d4b4ad1b51d2743dc8ea3c4e9394cd38ccb3c2d4b8ad2b2ac6b86d1b26c3bc1d8751cc789d2719e1745c3723c5c168a6258564384e0b81e164a5254554344d0b41dc0e2328e1324c5342c4b0ac1b41c8711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "36db6da6924924db6db4d2492492492492492492492492491249249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨71, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨88, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3f800ebffffffe00000000", hexnat% "114000000000000000", hexnat% "14000000000000000000000", hexnat% "a00000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "15d8026fffffffe00000000", hexnat% "810000000000000000", hexnat% "2200000000000000000000", hexnat% "180000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "5d0006bffffffe00000000", hexnat% "a04000000000000000", hexnat% "2000100000000000000000", hexnat% "10280000000000000000000", hexnat% "90000000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨86, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨84, by decide⟩ c3 c0
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3f800cbfdff0fe00000000", hexnat% "134000000000000000", hexnat% "10000800000010000000000", 9022592417529856, hexnat% "4000200000000000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "15980a5cfd7f53e00000000", hexnat% "2600000000000000000000", 3461017138267947008, hexnat% "1a0000000000000000", 9018194371018752]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7f801fcfd7f23e00000000", hexnat% "a00000010000000000", 3461017138267947008, hexnat% "10000000000000000000000", 9020393394274304]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "590014bffffffe00000000", hexnat% "b4000000000000000", hexnat% "a00000000000000000", hexnat% "2680000000000000000000", hexnat% "10000000000000000000000"]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "15b80b4cfd7fd3e00000000", hexnat% "b0000000000000000", hexnat% "2400000000000000000000", 9009673155903488, 3461016863390040064]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "590034bfdff8fe00000000", hexnat% "400020000000000000000", hexnat% "10000800000010000000000", hexnat% "2280000000000000000000", 9013796324507648, hexnat% "94000000000000000"]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨69, by decide⟩ c10 c9
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c11 c8
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨68, by decide⟩ c12 c7
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨86, by decide⟩ c13 c6
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨84, by decide⟩ c14 c5
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c15 c4
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "200013fbff89a00000000", hexnat% "10000800000010400000000", hexnat% "1ec000000000000000", hexnat% "3d80000000000000000000", 7009386627072, hexnat% "4000200040000000000000"]
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "9001ff0df70e600000000", hexnat% "3680000000000000000000", 9022626777268224, 1081004716776751104, hexnat% "4000200000010000000000", hexnat% "10000800000000000000000"]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [4089127715574120448, 522558294263332864, hexnat% "10000800000000000000000", hexnat% "1fc000000000000000", hexnat% "3f80000000000000000000", hexnat% "4000200000000000000000"]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "14080a057cafd9e00000000", 2891310960771858432, 5910974510923776, 2611340115968, hexnat% "1f8000000000000000", hexnat% "3f00000000000000000000"]
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4080207ffff89600000000", 8143257993216, hexnat% "10000800000000000000000", hexnat% "1f8000000000000000", hexnat% "3f00000000000000000000"]
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [3458762709934276608, 1152922191801614336, hexnat% "1fc000000200000000", hexnat% "3f80000000000000000000", hexnat% "a00000010000000000", hexnat% "14000000000000000000000"]
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3c001e3efffffe00000000", hexnat% "10000800100000000000000", hexnat% "200010000000000000000", hexnat% "4080204000000000000000", hexnat% "100008000000000000000"]
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "c0006307ffffe00000000", 1116892707587883008, hexnat% "19c000000000000000", hexnat% "a00000000000000000", hexnat% "3380000000000000000000", hexnat% "14000000000000000000000"]
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨61, by decide⟩ c24 c23
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "17f800cb07ffffe00000000", hexnat% "a04000000000000000", hexnat% "130000000000000000", 1116892707587883008]
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "17f800480627ffe00000000", hexnat% "1b4000000000000000", hexnat% "a00000000000000000", 8303511812964352, 1116892707587883008, 3458764513820540928]
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c27 c26
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1900bff07ffffe00000000", hexnat% "14080000000000000000000", hexnat% "2600000000000000000000", 1116892707587883008]
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "900bfc0627ffe00000000", hexnat% "3680000000000000000000", hexnat% "14000000000000000000000", 8303511812964352, 1116892707587883008, 3458764513820540928]
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c30 c29
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "17f803fc0e2782600000000", hexnat% "800100011800000000", 7421703487488, 8303511812964352, 3314649325744685056, 1152921504606846976]
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3f803fc06278e600000000", hexnat% "4000000000050000000000", hexnat% "10000800100001800000000", 4505798650626048, 1156580679304085504, 3350818860252004352]
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "98004b8fffffe00000000", 504403158265495552, hexnat% "4000204000000000000000", hexnat% "3600000000000000000000", hexnat% "10000800000000000000000", hexnat% "1b0000000000000000"]
  let c35 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4180bfc0e27ffe00000000", hexnat% "3e00000000000000000000", hexnat% "10000000100000000000000", 8303511812964352, 3314649325744685056, 1152921504606846976]
  let c36 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "17f80adefe6fdfe00000000", hexnat% "100010020000000000", 1155454779397242880, hexnat% "20000000000000000"]
  let c37 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7f800cffeff8fe00000000", hexnat% "10000800000010000000000", hexnat% "200000040000000000", hexnat% "130000000000000000", 4505798650626048]
  let c38 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨86, by decide⟩ c37 c36
  let c39 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3f801fe26678e200000000", 7177611906121728, 2053641430080946176, hexnat% "4000200000050400000000", 2302102470656, hexnat% "10000800100000000000000"]
  let c40 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c39 c38
  let c41 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "11800cfefff8f200000000", hexnat% "10000800100010c00000000", hexnat% "130000000000000000", hexnat% "4000200000040000000000", hexnat% "2e00000000000000000000", 2199023255552]
  let c42 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "15380a5efe2fffe00000000", hexnat% "1a0000000000000000", hexnat% "2c00000000000000000000", 1156580679304085504, 4503599627370496]
  let c43 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "118004ffeff8fc00000000", hexnat% "1b0000000200000000", hexnat% "2000000010020000000000", hexnat% "4000200000050000000000", hexnat% "e00000000000000000000", hexnat% "10000800000000000000000"]
  let c44 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "59802cf0ee7ffe00000000", 4925812092436480, hexnat% "130000000000000000", hexnat% "10000800100000000000000", hexnat% "2600000000000000000000", 1008806316530991104]
  let c45 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7380bff8f27ffe00000000", hexnat% "c00000000000000000000", hexnat% "10000000100000000000000", 3799912185593856, 432345564227567616]
  let c46 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "31801ff0727ffe00000000", hexnat% "a00000000000000000", hexnat% "e00000000000000000000", 3799912185593856, hexnat% "14000000000000000000000", 1116892707587883008]
  let c47 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨64, by decide⟩ c46 c45
  let c48 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "11800cf0667aea00000000", hexnat% "4000200000050400000000", hexnat% "130000000000000000", hexnat% "2e00000000000000000000", 7177611906121728, 1116892776307359744, hexnat% "10000800000000000000000"]
  let c49 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c48 c47
  let c50 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c49 c44
  let c51 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c50 c43
  let c52 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c51 c42
  let c53 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨61, by decide⟩ c52 c41
  let c54 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨84, by decide⟩ c53 c40
  let c55 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨62, by decide⟩ c54 c35
  let c56 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c55 c34
  let c57 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨66, by decide⟩ c56 c33
  let c58 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨79, by decide⟩ c57 c32
  let c59 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c58 c31
  let c60 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨80, by decide⟩ c59 c28
  let c61 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c60 c25
  let c62 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c61 c22
  let c63 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c62 c21
  let c64 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c63 c20
  let c65 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c64 c19
  let c66 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c65 c18
  let c67 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c66 c17
  let c68 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c67 c16
  c68
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00037.record009_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00037.record009_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00037.record009_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00037.record009_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00037.record009_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00037.record009_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00037.record009_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00037.record009_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00037.record009_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00037.record009
