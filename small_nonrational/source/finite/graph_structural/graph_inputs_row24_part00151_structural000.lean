module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow24Part00151Data
public import GraphInputsRow24Part00151Frames
public import GraphInputsRow24Part00151Leaves
public import GraphInputsRow24Part00151Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00151.record001
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record001
def vertexColumn : Fields := ⟨10, hexnat% "2785d26c4f0bc1f2725ca6a96a3a4e87ac9a6659996558d64d876a3a4e8b92e1b91e2785e0f9719a5392e4799956565555355352d4759362d4b4ad1b51d2745d0f66358d9354cd34cc7392e2b4ac6b46c5b0ed8791d4731e2749c6745c9715c3783d0f13c2f07e648b09a91a0e239311c4990e5251948d0b51324c5322c1b41c8711c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "369b6db6db69b6db4936d369a4926da69a4934d369249b6d24924d2493492449249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨53, by decide⟩, ⟨55, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨62, by decide⟩, ⟨64, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨74, by decide⟩, ⟨77, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨90, by decide⟩, ⟨102, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40040604315e22001301000000", hexnat% "800080008000800000", hexnat% "1400000c00000000000", hexnat% "820000000000008000000", 447314132992, 1410676639662080]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "e201140a74379ee800000", hexnat% "5c00000008000000000", 2161727821154615296, hexnat% "40040000200000000000000000", 140746078289920]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1b15ea0028325800000", hexnat% "820000000000008000000", hexnat% "40040600000000000000000000", 515429629952, hexnat% "4400000c00000000000", 1971427569827840]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "e201148a7835aee800000", hexnat% "800400000000000000", hexnat% "5400000408000000000", hexnat% "40000200000002100000000", hexnat% "40000000001200000000000000", 16777216]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40225d148a7c383e1800000", 1585267068834414592, hexnat% "c0000000000000a000000", hexnat% "40000000200000000000000000", 515463184384]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40000c00701e0001fbef800000", hexnat% "200140a0000000000000", hexnat% "40200000000c00000000000", 1972523860230144, hexnat% "5800000000000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40205d10ca7c383a3800000", hexnat% "40000400000200000000000000", hexnat% "820000000000008000000", hexnat% "201000002000000000", 379097972736, 4611686018427387904]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "25d148a783d8e6800000", hexnat% "e00000000000008000000", 1585267068851191808, hexnat% "40000000000400300000000", hexnat% "200000002000000000", hexnat% "40000000000000000000000000"]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40040e00301800c0a3eb000000", hexnat% "200140a0000000800000", 378024230912, 1973623371857920, 432345564227567616, hexnat% "5c00000000000000000"]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "a201008008080ea800000", 2043992116035584, hexnat% "40000000201200000000000000", hexnat% "8004a0000000000000", hexnat% "40400000000002000000000", hexnat% "5414000000000000000", 390925910016]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨81, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c10 c7
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c11 c6
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c12 c5
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c13 c4
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c14 c3
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c15 c2
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c16 c1
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨68, by decide⟩ c17 c0
  c18
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record001_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record001_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record001_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record001_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record001_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record001_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record001_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record001_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record001_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00151.record001

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00151.record003
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record003
def vertexColumn : Fields := ⟨10, hexnat% "5d26c3713c2f07c9c9729a8da4e87ac9a6659996558d64d876938ce8b92e1b91e2785e0fa719a5392e479c9665655352d4759362d4b4ad1b51d2745d0f72398d9394e334cc7392e2b4ac6b46c5b0ef07a1d8791e2749c6745c9715c3783d0f13c2f07c789906c2685a9188e1393126439895252342d44c9322c1b81d0721c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "1a6da6da69a6db6d26d349b69249a6da4934d369b4db6d249249349b492449249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2, 3]
def candidates : List (Fin raw.n) := [⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩, ⟨95, by decide⟩, ⟨96, by decide⟩, ⟨97, by decide⟩, ⟨98, by decide⟩, ⟨99, by decide⟩, ⟨100, by decide⟩, ⟨101, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .size 2
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .size 3
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨72, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fffffff9bfbfffff7fd800000", hexnat% "600000000000000000", hexnat% "40000000802000000", 288230376151711744]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨81, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ffffcff9bfbfffff7fd800000", hexnat% "200400000000000000", hexnat% "400000000000000000", hexnat% "300000000000002000000", hexnat% "40000000800000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨92, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3feffef38bf95bfcf7bd000000", 1128100012228608, hexnat% "700020000000000000", hexnat% "40200010802000000", 324259173170675712, hexnat% "10010c000000000000000000"]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨96, by decide⟩ c7 c6
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ffeffff97e7fb7ffbff800000", 1266637395197952, hexnat% "81800000400000000", hexnat% "600000000000000000", hexnat% "10000000000000000000000"]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3febffff96e75b7d7b3f800000", hexnat% "140000000000008000000000", 1128102151323648, hexnat% "81800000400000000", hexnat% "2000a0000000000000", hexnat% "410000800000000000"]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨96, by decide⟩ c10 c9
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 3 [hexnat% "3fffffffffffffffffff800000"]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨81, by decide⟩ c0 c12
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ffffcfffffbffffffff800000", 288230376151711744, hexnat% "300000000000000000000"]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨92, by decide⟩ c14 c13
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3feffcfffffbfffffff6800000", hexnat% "100100000000000000000000", 288230376302706688, hexnat% "200000000000000000000"]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c16 c15
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c17 c15
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fefffffdffbfb7d0ffa800000", hexnat% "200400000000000000", hexnat% "100000000000028000000000", 1266637395197952, 481120223232]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨70, by decide⟩ c19 c18
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3feffcfff7e3ffff87f3800000", hexnat% "100100000000000000000000", hexnat% "81c00000000000000", hexnat% "200000000000808000000", 481103446016]
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3feefcff97e3ffff83f2800000", hexnat% "100100000000000000000000", hexnat% "600000000000000000", hexnat% "10200000000000800000000", hexnat% "81c00000001000000", 498417532928]
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c22 c21
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨66, by decide⟩ c23 c20
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2feffdffcbfffffff7ff800000", hexnat% "10000200000000000000000000", hexnat% "100000000000000000000000", hexnat% "300000000000000000", hexnat% "40000000800000000"]
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2ffffcffdbf9ffff87f3800000", hexnat% "200400000000000000", hexnat% "10000000040200000000000000", hexnat% "300000000000008000000", 515463184384]
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2feefcdfcbf9ffff83f3800000", hexnat% "200400000000000000", hexnat% "100100000000000000000000", 532777271296, hexnat% "140200000000000000", hexnat% "10010220000000000000000000"]
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨90, by decide⟩ c27 c26
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨24, by decide⟩ c28 c25
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2ffafddf83e1ff7e73fe800000", hexnat% "700000008000000000", hexnat% "81e00000001000000", hexnat% "10010220000000000000000000", hexnat% "40000010800000000", hexnat% "40000000000800400000000"]
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2ffefcdfb7e3ff7f8bf2800000", hexnat% "400000800000000000", hexnat% "320000000000000000000", hexnat% "10010000000000000000000000", 498434310144, hexnat% "81c00000000000000"]
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2ffafcdfe3e9ffff83f6800000", hexnat% "40000100000000000000000", 532710162432, hexnat% "320000000000000000000", hexnat% "81600000001000000", hexnat% "10010000040000000000000000"]
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2ffffdf7d3ed5fffffff800000", hexnat% "2000a0000000000000", hexnat% "8000000000000000000", hexnat% "10000200001000000000000000", hexnat% "c0200000000000000"]
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ffffcf7ffff7bff8f77000000", hexnat% "300000000000008000000", 1125970782191616, hexnat% "8000080000000000000", 412316860416]
  let c35 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨70, by decide⟩ c0 c1
  let c36 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨100, by decide⟩ c0 c35
  let c37 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨100, by decide⟩ c0 c1
  let c38 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2fffffffffffffffe7ff800000", hexnat% "10000000000000000000000000", 103079215104]
  let c39 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c38 c37
  let c40 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c39 c36
  let c41 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fffffff9ffffbffc77f800000", hexnat% "600000000000000000", 240518168576, 1125902054326272]
  let c42 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c41 c40
  let c43 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2ffffdf7ffff7bffc777000000", hexnat% "10000200000000000008000000", 1125970782191616, hexnat% "8000080000000000000", 171798691840]
  let c44 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨80, by decide⟩ c43 c42
  let c45 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2ffffcf7dfff7fffffff800000", hexnat% "200080000000000000", hexnat% "10000200000000000000000000", hexnat% "108000000000000000000"]
  let c46 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨75, by decide⟩ c0 c35
  let c47 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2ffffef7bbffffffffff800000", hexnat% "400000000000000000", hexnat% "10000000040000000000000000", hexnat% "108000000000000000000"]
  let c48 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨81, by decide⟩ c47 c46
  let c49 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ffffff79bff5fffffff800000", hexnat% "40000000000000000", hexnat% "600020000000000000", hexnat% "8000080000000000000"]
  let c50 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2ffffef79bef5fffffff800000", hexnat% "108000000000000000000", hexnat% "10000000041000000000000000", hexnat% "600020000000000000", 36028797018963968]
  let c51 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨81, by decide⟩ c50 c49
  let c52 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c51 c48
  let c53 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c52 c45
  let c54 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨75, by decide⟩ c0 c1
  let c55 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ffffff7bfffffffcf7f800000", hexnat% "400000000000000000", hexnat% "8000000000080000000", 206158430208]
  let c56 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c55 c54
  let c57 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ffffff79fff5bffcf7f000000", 208314302464, 1125899906842624, hexnat% "600020000000000000", hexnat% "8000080000000000000"]
  let c58 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c57 c56
  let c59 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2ffffef79be35fffd7f7800000", hexnat% "400820000000000000", hexnat% "108000000000000000000", hexnat% "10000000041000000000000000", 171932909568, hexnat% "200480000000000000"]
  let c60 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨81, by decide⟩ c59 c58
  let c61 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c60 c53
  let c62 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨67, by decide⟩ c61 c44
  let c63 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c62 c34
  let c64 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c63 c33
  let c65 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2feefcd383e15fff03f2000000", hexnat% "10010c000000000000800000", hexnat% "700020008000000000", hexnat% "10010220000000000000000000", 532777271296, 324259173187452928, hexnat% "c1a00000000000000"]
  let c66 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨90, by decide⟩ c65 c64
  let c67 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c66 c32
  let c68 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c67 c31
  let c69 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c68 c30
  let c70 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨64, by decide⟩ c69 c29
  let c71 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨96, by decide⟩ c70 c24
  let c72 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c71 c11
  let c73 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c72 c8
  c73
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record003_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record003_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record003_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record003_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record003_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record003_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record003_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record003_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record003_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00151.record003
