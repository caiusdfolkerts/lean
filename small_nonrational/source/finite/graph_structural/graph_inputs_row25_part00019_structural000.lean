module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow25Part00019Data
public import GraphInputsRow25Part00019Frames
public import GraphInputsRow25Part00019Leaves
public import GraphInputsRow25Part00019Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00019.record022
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00019.record022
def vertexColumn : Fields := ⟨10, hexnat% "1e4751ac5b31c6715c748f26695a2e87a718e6a5996959563598e53a2e2b86e8791e2785e785d13c5a95a719665592e479715a5594e5c569565655554d5c358d5362d4b4ad1b61d4749d175c338e9364e5354cd32cc7362d4b8acab1ad1b26c5b0ee8761e4751cc789e1745c9715d0f23c4f07e1a298668382e645518651961545294658350d0b4a318e1324c5382c2b06e0721c4709c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "36db6db6db69b6db6924db69b6926d249b4d34924924db4924926d2492492492692491249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨73, by decide⟩, ⟨75, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨90, by decide⟩, ⟨95, by decide⟩, ⟨96, by decide⟩, ⟨97, by decide⟩, ⟨98, by decide⟩, ⟨106, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "400047348e58ff3fff7e0000000", hexnat% "7000000000000000000000000", hexnat% "1a0000000000000000", hexnat% "82000000000000000000", hexnat% "800000000000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1047348ff8ab3ffe7e0000000", hexnat% "82000000000000000000", hexnat% "406000000000000000000000000", 378302437418598400, hexnat% "800000000000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2047348e58aa1ffe5e0000000", hexnat% "1a0000000000000000", hexnat% "82000000000200000000", hexnat% "405000000000000000000000000", hexnat% "800000000002001000000000", 382805968326492160]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c3 c0
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "43c86e02a047e5c0000000", hexnat% "918000000020000000", hexnat% "407000000000000000000000000", hexnat% "43002000000000000000000", hexnat% "800000000002001000000000", 581395360488882176, 378355153847189504]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨86, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40780000a0185423776e0000000", 590402559743623168, hexnat% "47000000000400000000000", 180144539145601024, hexnat% "1c00e0000000000000000", hexnat% "f00000000000000000", hexnat% "200000000000000000000"]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "280238afd8df1bff7e0000000", hexnat% "4000000000002000000000000", hexnat% "40020000000000000000", hexnat% "41000000200400000000000", hexnat% "4000000000000000000000", hexnat% "401000000000000000000000000"]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "28021cadf8df1bff7e0000000", hexnat% "4000000000002000000000000", hexnat% "200200000000000000000", hexnat% "41000000200400000000000", hexnat% "4000000000000000000000", hexnat% "401000000000000000000000000"]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "80008a458df1bff6e0000000", hexnat% "340080000000000000000", hexnat% "407000000000000000000000000", 633322992566272, hexnat% "43000000200000000000000", hexnat% "4000800000000000000000", hexnat% "320000000000000000"]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨66, by decide⟩ c10 c9
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨70, by decide⟩ c11 c8
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "80010a018f71bf76e0000000", hexnat% "4000000100002000100000000", hexnat% "47000000000400000000000", hexnat% "403000000000000000000000000", 36029346774777856, hexnat% "c00e0000000000000000", hexnat% "200e00000000000000000"]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "680604aff87f37a37e0000000", hexnat% "1001000000000800000000000", 6322191859712, hexnat% "400040200000800000000000000", hexnat% "180000000000000000000"]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4048403caff884222f7e0000000", 5497558138880, hexnat% "3000000000000000000000000", hexnat% "7000000000400000000000", 13941807440199680, 540449547470503936]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "480024aff80022237e0000000", hexnat% "180000000004000000000", hexnat% "403000000000000000000000000", 6047313952768, hexnat% "47000000000400000000000", 590402559743623168, 558463945979985920]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨81, by decide⟩ c16 c15
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c17 c14
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "84700a1187c27a9720000000", 5913096224768, 590393763650600960, hexnat% "407000000000000000000000000", hexnat% "8e0000000000000000", hexnat% "3c0000000000000000000", hexnat% "600000000000000000"]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4008403caf9884242d720000000", 5638218317824, hexnat% "60000000000000000", hexnat% "7000000000000000000000", 540484731842592768, hexnat% "7000000000000000000000000", 13941807440199680]
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "280238afd80036297a0000000", hexnat% "45000000000000000000000", 5910948741120, hexnat% "40020000000000000000", hexnat% "405000000000000000000000000", 558463945979985920, 590121084766912512]
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "50013c0fe0012dff7e0000000", hexnat% "80000a018000000000000000", hexnat% "6000000000200000000000", hexnat% "402000000000000000000000000", 585749426534875136, 558446353793941504, hexnat% "40000000000000000000000"]
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "180138afb8002d29760000000", hexnat% "46000000000000000000000", 5912022482944, hexnat% "40040000000000000000", hexnat% "406000000000000000000000000", 558481538166030336, 590261822255267840]
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4800200700002421660000000", hexnat% "403000000000000002000000000", hexnat% "4000818000000000000000", hexnat% "1c00e0000000000000000", 6328634310656, hexnat% "4300a000000000000000000", 558499130352074752, 590402559743623168]
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨69, by decide⟩ c24 c23
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c25 c22
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨70, by decide⟩ c26 c21
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨81, by decide⟩ c27 c20
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c28 c19
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨68, by decide⟩ c29 c18
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c30 c13
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c31 c12
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c32 c7
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c33 c6
  c34
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00019.record022_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00019.record022_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00019.record022_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00019.record022_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00019.record022_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00019.record022_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00019.record022_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00019.record022_validity Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00019.record022_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00019.record022

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00019.record031
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00019.record031
def vertexColumn : Fields := ⟨10, hexnat% "1b47325c8f07c6c9ca96a3a1e9c669b1665a5655a364d8b61da8e63a4e538ce8b8ae1ba1e1783e6c5c9966391e5c569715656558d5352d475a358d9354d3362d1b61d1743d70da3c4d9394e334ccb31ce8b62e4b52ccb8ac6b86c5b0ef07a1d8791d4731e2749ca719e1745c9715c3783d0f23c4f0bc1f550ac548aa544a96154529615454550d60d2344d0b58350ca384d1314c3382c8b12c2b"⟩
def kindColumn : Fields := ⟨3, hexnat% "db6db6db6db4db6db6da6db6db69249249249249249249249249249369a6da693493493249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨40, by decide⟩, ⟨44, by decide⟩, ⟨46, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨96, by decide⟩, ⟨107, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "5f7ff0000e004200000000", hexnat% "2080000000010000000000", 571957152676052992, hexnat% "3f800000000000000", hexnat% "801000000000000502ce0000000", hexnat% "c0000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fc04ff80e006c00000000", hexnat% "8010000000000005102e0000000", hexnat% "4002000040000000000000", 553942754166571008, hexnat% "29b00000000000000000", hexnat% "14000000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "60324c27fe0002e0000000", hexnat% "801000000000000516c00000000", hexnat% "3d800000000000000", hexnat% "da00000000000000000", hexnat% "17c0100000000000000000", hexnat% "800000000000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "37ebf4264e0104a0000000", hexnat% "4814000000000000000000", 85568402583715840, hexnat% "3d800000000000000", hexnat% "80080100000000000", hexnat% "801000000000000406800000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2015ffa6e406c00000000", hexnat% "1dc0000000000000000000", hexnat% "8010000000000001102e0000000", 400820366835974144, hexnat% "6012000000000000000000", hexnat% "2ca00000000000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fd9ddf7fe4106e0000000", hexnat% "26200000000000000000", hexnat% "20800006800000000", hexnat% "801000000000000100000000000", hexnat% "4000000000000000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "48855f7fe0002e0000000", hexnat% "37800000000000000000", hexnat% "a0000002000000000", hexnat% "801000000000000514c00000000", hexnat% "40000800000000000000", hexnat% "6900000000000000000000", hexnat% "1200200000000000000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨79, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "88057ff7e010420000000", hexnat% "80080100000000000", hexnat% "6100000000000000000000", hexnat% "1640000000006800000000", hexnat% "8010000000000004002c0000000", hexnat% "3f800000000000000000", hexnat% "200000000000000000"]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "5d7340400000000000", hexnat% "2880e000000000000", hexnat% "6012000000000000000000", hexnat% "801000000000000116ee0000000", 337769972052787200, hexnat% "2da00000000000000000", hexnat% "1fc0000000000000000000"]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c10 c7
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨62, by decide⟩ c11 c4
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨68, by decide⟩ c12 c3
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c13 c2
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨61, by decide⟩ c14 c1
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨70, by decide⟩ c15 c0
  c16
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00019.record031_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00019.record031_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00019.record031_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00019.record031_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00019.record031_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00019.record031_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00019.record031_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00019.record031_validity Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00019.record031_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00019.record031
