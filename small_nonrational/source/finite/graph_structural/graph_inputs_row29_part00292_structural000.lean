module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow29Part00292Data
public import GraphInputsRow29Part00292Frames
public import GraphInputsRow29Part00292Leaves
public import GraphInputsRow29Part00292Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00292.record003
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00292.record003
def vertexColumn : Fields := ⟨10, hexnat% "9e2749b31ca719c9715c3723c4f0bc1f2729ab1aa699a9695a36a3a4e8ba1ea66c5a9665a56558d68d9362d876c3a8e63a4e538ce8b92e2b86e8791e2785e0f999564d98e5392e595554d58d5352d58d534cd8b52d2b46d8751d2745d0f59354cd38cd332cc7362d4b32e2b4acab86d1b26c5b0ed8751cc789d2729e1745c9715c3783d0f23c4f0bc1f8e0788d0748a86a898661c469464991643919515254550d46342c8b12c2b41c8711c27"⟩
def kindColumn : Fields := ⟨3, hexnat% "126db6da6d34db6da6d26db6d369b6db4da6db6924924924db6da6924db6da49249a4924924d249a493249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨68, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨92, by decide⟩, ⟨95, by decide⟩, ⟨102, by decide⟩, ⟨105, by decide⟩, ⟨112, by decide⟩, ⟨113, by decide⟩, ⟨116, by decide⟩, ⟨123, by decide⟩, ⟨125, by decide⟩, ⟨128, by decide⟩, ⟨136, by decide⟩, ⟨137, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "30128030240900c301781fde305e0000000", hexnat% "7200000000000000000000", hexnat% "100000000000000000003800000000", hexnat% "1c8000000000000000000", 31336081391616]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "30128130040900a2817811c3fbde0000000", hexnat% "1d0000000000000000000", hexnat% "200000000000001c00000000000", hexnat% "7400000000000000000000", 63050394783186944]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "30128130240900820178119e3bde0000000", 64176294690029568, hexnat% "1d8000000000000000000", hexnat% "7600000000000000000000", 30786325577728]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "301281300409049201781fdf081e0000000", hexnat% "3600000000000000000000", hexnat% "200000000000000020400000000", hexnat% "d8000000003800000000", 14293651161088]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "301281300409028a01781c81fbde0000000", 14671883161042944, hexnat% "158000000000000000000", hexnat% "200000000000001c00000000000", hexnat% "5600000000000000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3012813024090082017819deabde0000000", 23089744183296, 27021597764222976, hexnat% "1d8000000000000000000", hexnat% "7600000000000000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "301281302409008201781880881e0000000", 4505798650626048, 23347442221056, 28675263252398080, hexnat% "1d8000000000000000000", hexnat% "7600000000000000000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨105, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c7 c4
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c8 c3
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨116, by decide⟩ c9 c2
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c10 c1
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c11 c0
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "300281302400001f8108101ffbc20000000", hexnat% "800000010000000000000", 66428102019907584, hexnat% "7600070000000000000000", hexnat% "100000000900000000000000000000000"]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "30128110240900c301780fde305e0000000", hexnat% "20000000000000100003800000000", hexnat% "7200000000000000000000", hexnat% "1c8000000000000000000", 31336081391616]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "30128110200907f20178089f005e0000000", 32651097298436096, hexnat% "20040000000000100003800000000", 17042430230528, hexnat% "d8000000000000000000"]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "30128130240904e381781fdffbde0000000", hexnat% "1c0000000000000000000", hexnat% "3000000000000000000000"]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "30128110240906aa81780fdffbde0000000", hexnat% "20000000000000100000000000000", hexnat% "150000000000000000000", hexnat% "1400000000000000000000"]
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "30128110240904a281780fdeb85e0000000", hexnat% "3400000000000000000000", hexnat% "20000000000000100003800000000", 21990232555520, hexnat% "1d0000000000000000000"]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c18 c17
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c19 c16
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "301281102009068a017804c1fbde0000000", hexnat% "158000000000000000000", 49574780273164288, hexnat% "20040000000000101c00000000000", hexnat% "1600000000000000000000"]
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "301281102009058601780fdec05e0000000", hexnat% "2600000000000000000000", 21440476741632, hexnat% "20040000000000100003800000000", hexnat% "198000000000000000000"]
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "30120100200907ea01780fde805e0000000", hexnat% "8010000000000000000000000000000", hexnat% "20040000000000100003800000000", 25838523252736, hexnat% "158000000000000000000"]
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "301281202409068201781fde83de0000000", hexnat% "10000000000000000038000000000", hexnat% "1600000000000000000000", hexnat% "1d8000000000000000000", 21990232555520]
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "301281302009069201780ac1fbde0000000", 22553182508941312, hexnat% "d8000000000000000000", hexnat% "40000000000101c00000000000", hexnat% "1600000000000000000000"]
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "30120120200907ff81780fdf93de0000000", hexnat% "40000000000100000000000000", 7146825580544, hexnat% "8010000000000000000000000000000"]
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "30120120200907f301780fdf905e0000000", hexnat% "8010000000000000000000000000000", hexnat% "40000000000100003800000000", 7146825580544, hexnat% "c8000000000000000000"]
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨80, by decide⟩ c27 c26
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "30120120200906ff817802c1fbde0000000", hexnat% "8010000000000000000000000000000", 58581979527905280, hexnat% "40000000000101c00000000000", hexnat% "1000000000000000000000"]
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "30120130240906df81781fdfa3de0000000", hexnat% "8000000000000000000000000000000", 6047313952768, hexnat% "1200000000000000000000"]
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "30120130240907f6817812dffbde0000000", hexnat% "90000000000000000000", hexnat% "8000000000000000010000000000000", 54043195528445952]
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "30128130240906d2817813dfe3de0000000", 1649267441664, 54043195528445952, hexnat% "1200000000000000000000", hexnat% "d0000000000000000000"]
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c32 c31
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨80, by decide⟩ c33 c30
  let c35 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "30128130240907c6817802c1fbde0000000", hexnat% "190000000000000000000", 58581979527905280, 72550175247171584, hexnat% "200000000000000000000"]
  let c36 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "30120130240906df81780ac1fbde0000000", hexnat% "8000000000000000010200000000000", 72550175247171584, 18014398509481984, hexnat% "1200000000000000000000"]
  let c37 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "30120120240906d281781fdfc3de0000000", hexnat% "1200000000000000000000", hexnat% "8010000000000000000000000000000", hexnat% "d0000000000000000000", 3848290697216]
  let c38 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "30128130240906d2817812c1c05e0000000", 4505798650626048, 54570961109778432, hexnat% "d0000000003800000000", hexnat% "1200000000000000000000", 1649267441664]
  let c39 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c38 c37
  let c40 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨80, by decide⟩ c39 c36
  let c41 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c40 c35
  let c42 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨102, by decide⟩ c41 c34
  let c43 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨75, by decide⟩ c42 c29
  let c44 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨82, by decide⟩ c43 c28
  let c45 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c44 c25
  let c46 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨113, by decide⟩ c45 c24
  let c47 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨85, by decide⟩ c46 c23
  let c48 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c47 c22
  let c49 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c48 c21
  let c50 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c49 c20
  let c51 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨86, by decide⟩ c50 c15
  let c52 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c51 c14
  let c53 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "120120240907ff8178111ffbde0000000", hexnat% "30008010000000000000000000000000000", 66428094503714816]
  let c54 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "101201202400001f8158101fdbc40000000", hexnat% "10000900000000000020020000000", hexnat% "20000000000000e00000000000000000000", hexnat% "7000020000000000000000", 66428100946165760, hexnat% "8000000000000000010000000000000"]
  let c55 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨66, by decide⟩ c54 c53
  let c56 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "30128010000907ff8178100200de0000000", 34634616274944, 70931694131085312, hexnat% "120240000000000001c03000000000"]
  let c57 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "101201202400001f8048101fdbd00000000", hexnat% "20008010000000000000000000000000000", hexnat% "800000010020000000000", hexnat% "9000001300000000e0000000", hexnat% "7600000000000000000000", 66428094503714816]
  let c58 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "30128130000907ff81781fc622de0000000", hexnat% "240000000000001801000000000", 32435593019392]
  let c59 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "120000000907ff8178110422de0000000", hexnat% "30008010000000000000000000000000000", 32504312496128, 66885491340869632, hexnat% "120240000000000000000000000000"]
  let c60 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨52, by decide⟩ c59 c58
  let c61 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "101201202400001f8038101fdbc80000000", hexnat% "900000140000000160000000", hexnat% "20008010000000000000000000000000000", hexnat% "800000010020000000000", hexnat% "7600000000000000000000", 66428094503714816]
  let c62 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20120120240007e000581ede03d00000000", hexnat% "9000001200000000e0000000", hexnat% "10008010000000000000000000000000000", hexnat% "20000010020000000000", hexnat% "1d8000000000000000000", 32435593019392]
  let c63 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "30128010000000000018001003c00000000", hexnat% "1f8000000000000000000", hexnat% "120240000000000100e00000000000", 34635153145856, hexnat% "7e00000000000000000000", hexnat% "9000001600000001c0000000", 70931694131085312]
  let c64 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c63 c62
  let c65 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c64 c61
  let c66 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨64, by decide⟩ c65 c60
  let c67 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c66 c57
  let c68 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c67 c56
  let c69 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c68 c55
  let c70 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨128, by decide⟩ c69 c52
  let c71 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c70 c13
  let c72 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨125, by decide⟩ c71 c12
  c72
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00292.record003_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00292.record003_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00292.record003_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00292.record003_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00292.record003_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00292.record003_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00292.record003_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00292.record003_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00292.record003_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00292.record003
