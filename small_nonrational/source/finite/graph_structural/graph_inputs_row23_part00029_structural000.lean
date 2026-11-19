module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow23Part00029Data
public import GraphInputsRow23Part00029Frames
public import GraphInputsRow23Part00029Leaves
public import GraphInputsRow23Part00029Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00029.record004
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00029.record004
def vertexColumn : Fields := ⟨10, hexnat% "19c9a99a99996558d61d98e8b92e2b86e1783e9a59999595554d51d58d8b52d2b46d1743d64e5354cd31cf0ba2d8b92d2b2ac6b86c5b0ed8791d4731e2749ca70de0f13d1c272628a91a26866458961590e2382e07a618a51926465454951550d2342d0764388c6344c9314e0b42c8b0ac1b41c8711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "2492492492492492492492492492492492492492449249249249249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩, ⟨95, by decide⟩, ⟨96, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "e003807801ff80000000000", hexnat% "208082000100000000000000", hexnat% "5f00000000000000000", hexnat% "17c00000000000000000000", 9142307243562106880, hexnat% "800200000000000000000000", hexnat% "1500140080000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "17f5d7d7895fff80000000000", 7638104968020361216, hexnat% "70000000000000000", hexnat% "2000800000000000000000", hexnat% "282000000000000000000", hexnat% "808000000000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "17f1d7c3890fea80000000000", hexnat% "70000000000000000", hexnat% "4001000400100000000000", 7710162562058289152, hexnat% "2000800000400000000000", hexnat% "800200400001000000000000", hexnat% "8082000000000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3e5d7ff0842eb80000000000", hexnat% "280000101000000000000", hexnat% "2000000200400000000000", hexnat% "f00c0000000000000", hexnat% "808000000000000000000000", hexnat% "1410000001010000000000000", 7493989779944505344]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ebf8bd0ffef780000000000", hexnat% "4000000000800000000000", hexnat% "f0000000000000000", hexnat% "800000200000000000000000", hexnat% "70000000000000000000", hexnat% "1410004000010000000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "17f1d7ff8923e380000000000", hexnat% "2000000000400000000000", hexnat% "280000101000000000000", hexnat% "4000000400800000000000", hexnat% "700c0000000000000", 7493989779944505344, hexnat% "808000000000000000000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3e1d7d30822e280000000000", hexnat% "f00c0000000000000", hexnat% "2000800000500000000000", hexnat% "4000000400800000000000", hexnat% "282400101000000000000", hexnat% "1410000001010000000000000", 7493989779944505344, hexnat% "808000000000000000000000"]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨74, by decide⟩ c7 c6
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c8 c5
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨72, by decide⟩ c9 c4
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨80, by decide⟩ c10 c3
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "15f5dfd7895fff80000000000", 7638104968020361216, hexnat% "70000000000000000", hexnat% "2000800000000000000000", hexnat% "800200000000000000000000", hexnat% "208002000000000000000000"]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1f39ffe7899ffb80000000000", hexnat% "c0000000000000000000000", hexnat% "2000800200400000000000", hexnat% "70000000000000000", hexnat% "4001000400000000000000", 6917529027641081856]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "17f0dfc7890fea80000000000", hexnat% "70000000000000000", hexnat% "3800000100000000000", 7998392938210000896, hexnat% "801200000001000000000000", hexnat% "e000000000000000000000", 70368744177664]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨93, by decide⟩ c14 c13
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c15 c12
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "5ffcf970842eb80000000000", hexnat% "800200400000000000", hexnat% "a00000000101000000000000", hexnat% "f00c0000000000000", hexnat% "202000000000000000000", hexnat% "1000104001010000000000000", 7493989779944505344]
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "42e4fbf0ffeff80000000000", hexnat% "a01000000000000000000000", hexnat% "f0000000000000000", hexnat% "a00000000000000000000", hexnat% "1c0000000000000000000000", hexnat% "1010104000010000000000000"]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "15ffdfc78923e380000000000", hexnat% "800000400000000000", hexnat% "1000400800000000000", hexnat% "a00000000101000000000000", hexnat% "700c0000000000000", 7493989779944505344, hexnat% "202000000000000000000"]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "e3defa708b6f380000000000", hexnat% "1c0000000000000000000000", hexnat% "f0080000000000000", hexnat% "2000800000400000000000", hexnat% "1000400800000000000", 8070450532247928832, hexnat% "1000104000010000000000000"]
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "5f4ef870822e280000000000", hexnat% "f00c0000000000000", hexnat% "7800000100000000000", hexnat% "3000000000400000000000", hexnat% "a08000000101000000000000", hexnat% "1000100001010000000000000", 288371113640067072, 7493989779944505344]
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨81, by decide⟩ c21 c20
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨88, by decide⟩ c22 c19
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c23 c18
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨86, by decide⟩ c24 c17
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨94, by decide⟩ c25 c16
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "22d08b40051ff80000000000", hexnat% "2000800200000000000000", hexnat% "70300000000000000000", hexnat% "1c0c00000000000000000000", 8709961679334539264, hexnat% "f8000000000000000", hexnat% "800200000000000000000000", hexnat% "1410104000000000000000000"]
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "15ffc78308024b80000000000", hexnat% "7c00000000000000000", hexnat% "200080000109000000000000", 5136918324969472, hexnat% "f00c0000000000000", 9079256848778919936, hexnat% "100000000000000000000", hexnat% "800200000000000000000000"]
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "11e0d7ff08024b80000000000", hexnat% "208080000109000000000000", hexnat% "17000000000000000000000", 5136918324969472, hexnat% "f00c0000000000000", 9079256848778919936, hexnat% "800200000000000000000000", hexnat% "400000000000000000000000"]
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "a3f48ff0072d980000000000", 5172102697058304, 8700954480079798272, hexnat% "80020020000000000000000", hexnat% "a00000000000000000000", hexnat% "40010010000000000000000", hexnat% "c8000000000000000", hexnat% "1500140000000000000000000"]
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "a8428120004a00000000000", hexnat% "40010010002000000000000", hexnat% "4001000400180000000000", hexnat% "200082000109000000000000", hexnat% "2000800200400000000000", 8709961679334539264, hexnat% "c8000000000000000", hexnat% "801a00600000000000000000", hexnat% "1510144000010000000000000"]
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨87, by decide⟩ c31 c30
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨68, by decide⟩ c32 c29
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨82, by decide⟩ c33 c28
  let c35 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c34 c27
  let c36 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨75, by decide⟩ c35 c26
  let c37 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨89, by decide⟩ c36 c11
  let c38 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c37 c0
  c38
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00029.record004_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00029.record004_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00029.record004_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00029.record004_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00029.record004_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00029.record004_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00029.record004_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00029.record004_validity Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00029.record004_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00029.record004

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00029.record013
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00029.record013
def vertexColumn : Fields := ⟨10, hexnat% "1b29a93a2e87a659362d86e8791e2785e0f9b19a5392e479655352d46d8751d2745d0f5a398d6338d931ce2b4acab86d1b26c5bc1e8761d4731d2729c6785c570dd0f23c2f931322ca4a1a83a9191625a0e1381e4c4b1924690e645454958344d0764348ca318d1324c3382c4b0ac1b81d0721c4705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "92492492492492492492492492492492492492492249249249249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "53bf4cfc7bc93f0000000000", hexnat% "200080020000000000000000", hexnat% "80020000400000000000000", 15410754974908416, hexnat% "18000000000000000", hexnat% "4003000000000000000000", hexnat% "40010000000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "37f6d7587bc1fd0000000000", hexnat% "8a00000000000000000", 17453647579316224, hexnat% "78400000000000000", hexnat% "80820000000000000000000", hexnat% "400100000000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "137244c87bc13f0000000000", hexnat% "200080020000000000000000", 17662554788593664, hexnat% "58400000000000000", hexnat% "400108000000000000000000", hexnat% "40410100000000000000000", hexnat% "8003000000000000000000", hexnat% "80820200000000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨86, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨89, by decide⟩ c3 c0
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4bbf2afc77c8bf0000000000", hexnat% "200080020000000000000000", hexnat% "100040000800000000000000", 15551492463263744, hexnat% "18000000000000000", hexnat% "4005000000000000000000", hexnat% "40010000000000000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2feeb73877c1fb0000000000", hexnat% "8c00000000000000000", 17455846602571776, hexnat% "78800000000000000", hexnat% "101040000000000000000000", hexnat% "400100000000000000000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "aea22a877c0bf0000000000", hexnat% "200080020000000000000000", 17803292276948992, hexnat% "58800000000000000", hexnat% "400108000000000000000000", hexnat% "40410100000000000000000", hexnat% "10005000000000000000000", hexnat% "101040400000000000000000"]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨86, by decide⟩ c7 c6
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨89, by decide⟩ c8 c5
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "63818e0673c9b80000000000", 15277714067947520, hexnat% "18c00000000000000", hexnat% "70080000000000000000", hexnat% "1c0200000000000000000000", hexnat% "f00000000000000000", hexnat% "4001000000000000000000", hexnat% "3c00000000000000000000"]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2000800251c0000000000000", hexnat% "2000800200270000000000", 17970418044370944, hexnat% "5ac00000000000000", hexnat% "170080000000000000000", hexnat% "5c0200000000000000000000", hexnat% "8700000000000000000", hexnat% "21c00000000000000000000", hexnat% "1c007000000000000000000"]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨62, by decide⟩ c11 c10
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c12 c9
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c13 c4
  c14
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00029.record013_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00029.record013_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00029.record013_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00029.record013_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00029.record013_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00029.record013_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00029.record013_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00029.record013_validity Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00029.record013_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00029.record013
