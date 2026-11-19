module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow26Part00014Data
public import GraphInputsRow26Part00014Frames
public import GraphInputsRow26Part00014Leaves
public import GraphInputsRow26Part00014Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00014.record022
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00014.record022
def vertexColumn : Fields := ⟨10, hexnat% "3c8d323cf0b8aca99a8e8bad1a6635a36c3a2e8789e0fb4972729664b9d16653570d9354d3362d27743c8e6364cd32cf0b62e2b4acab46c9b0ef0791d4731e2719c9715e0f43c8f0bc1f8b03cd09c291a260d9c1624990e4350b41d60d4330c930cc4709c17"⟩
def kindColumn : Fields := ⟨3, hexnat% "36936db49a69b4d349b6db6926d24d36da4d24924db489249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨23, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨41, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨61, by decide⟩, ⟨63, by decide⟩, ⟨66, by decide⟩, ⟨68, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20c000050003e8000000", 2882341144912461824, hexnat% "40148000000000800000", 26457266978816, 288793360469065728]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4014ac043a1a78c00000", hexnat% "c00000000000000000", 562952100904960, hexnat% "20000001000100000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40548405381a78c00000", 562952100904960, 2882305960540372992, hexnat% "20800000000100000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40548405381a78c00000", 2882305960540372992, 562952100904960, hexnat% "20800000000100000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20900403381bf8c00000", 2882305960540372992, hexnat% "440000000000000000", hexnat% "40008004000000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "100c02381ad8c00000", hexnat% "400000000020000000", 2305845208236949504, hexnat% "20800001000100000000", hexnat% "40048004000000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨68, by decide⟩ c6 c3
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c7 c2
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨23, by decide⟩ c8 c1
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [2882349949595418624, hexnat% "20800001000100000000", 288793429188542464, hexnat% "500000000060000000", hexnat% "40048004000000800000", 17594736181248]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c10 c9
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c11 c0
  c12
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00014.record022_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00014.record022_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00014.record022_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00014.record022_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00014.record022_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00014.record022_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00014.record022_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00014.record022_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00014.record022_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00014.record022

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00014.record042
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00014.record042
def vertexColumn : Fields := ⟨10, hexnat% "3a8d325c2f3a274b8acaaaa6a99a2eb4699a562db0e8b8ae8789e0f9d1d27296a599564b9d16652d70d9354d8b4ad2745d0f74370f2368e6364d5334cb3c2d8b8ad2b2ad1b26c3bc1e4751e2729c6725c3783d0f23c2f07e2cd0a4689856624a9264550b41d60d4328c9314c4709c17"⟩
def kindColumn : Fields := ⟨3, hexnat% "36db6db6da49b4db6db49a6db6d24924d349269b4d36924926da449249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2, 3]
def candidates : List (Fin raw.n) := [⟨19, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1ffe37fbfc7fffffff80000", 4618441417868443648, hexnat% "800020000000000000", hexnat% "1c000000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1ffff7f3fc673b5fff80000", 9288674231451648, 153931627888640, 13841813454723219456, hexnat% "800000004a00000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1ffe3ff6fffffffdbf80000", 10376293541461622784, hexnat% "14000000000020000000", hexnat% "8000000000004000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1ffe37f6feeffff8be80000", 10380797141088993280, hexnat% "10000001000060000000", hexnat% "800000000010100000", hexnat% "c000000000004000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1ffefffffc0fffffff80000", hexnat% "10000001000000000000", 3940649673949184, 13510798882111488]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1fff3ffffe1fffff7f80000", hexnat% "c000000000000000000", 6755399575273472, 1688849860263936]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1ffe3ffffffffff8ff80000", hexnat% "8000000000050000000", hexnat% "14000000000020000000"]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1ffe3ffffc1ffffa7f80000", 3940649673949184, 402653184, 13510798882111488, hexnat% "1c000000000040000000"]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c10 c7
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c11 c6
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1ffefffffc9fffffff80000", 1688849860263936, hexnat% "10000000000000000000", 13510798882111488]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1ffff7f2fc15cf7fff80000", 3940649673949184, hexnat% "800020000000000000", 179220395327488, 14992483193876119552]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c14 c13
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1ffe3ffffce7bff87f80000", 4503599761588224, 426611048448000, hexnat% "1c000000000040000000", 9007199523176448]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .size 3
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .size 2
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c18 c17
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨74, by decide⟩ c18 c19
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .classes 3 [hexnat% "13fffffffbffffffff80000", hexnat% "4000000040000000000000", hexnat% "8000000000000000000000"]
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c18 c17
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨62, by decide⟩ c18 c22
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨74, by decide⟩ c18 c23
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c24 c17
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c25 c21
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c26 c20
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1fff3ff2ff9fffffff80000", hexnat% "c000000000000000000", 1688849860263936, 14987979559889010688]
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨71, by decide⟩ c28 c27
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1ffff7f2fe1dcf7fde00000", 38482940526592, 3940649674473472, hexnat% "800000000800100000", 14992483159516381184]
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c30 c29
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1ffe37f2fcf58f785e80000", hexnat% "1c000000000040000000", 147335094992896, hexnat% "800020000010100000", 14992483193876119552, 36284051488768]
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c32 c31
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c33 c16
  let c35 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c34 c15
  let c36 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c35 c12
  let c37 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c36 c5
  let c38 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨24, by decide⟩ c37 c2
  c38
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00014.record042_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00014.record042_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00014.record042_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00014.record042_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00014.record042_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00014.record042_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00014.record042_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00014.record042_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00014.record042_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00014.record042

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00014.record061
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00014.record061
def vertexColumn : Fields := ⟨10, hexnat% "f23343c98e93a2e2b91e17bc1e86e1d45d1cc5b19c4f1e2749b25c9aa559c95a5c56558d5356364d8b4ad4745d98ce364cd32cc7362e4b8acab46c5b61e4789ca745c5783d0f23c4f0bc1fc30ca0db096264932705895150d60d434c328c530cc8b12c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "1b6db6db6db6db4926d34d24934da69249a69b492492489249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨34, by decide⟩, ⟨36, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨44, by decide⟩, ⟨47, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨55, by decide⟩, ⟨57, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [16336386831681585152, 24257975287808, 1155173854176346112]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [17441879232010518528, 13510801029595136, 23106924052480, 36169535044190208, 2268824862720]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨22, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [9421108760698421248, 8070450807125835776, 5515006443520, 19861002518528]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [2306995110027460608, 14990231359702695936, 40673134671560704, 153685339431501824]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [10721428072562688, 184788322210545664, 8070450807125835776, 9225624386424274944]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [17333370646477930496, 563018672898048, 157625989105451008, 1100321128448, 24189255811072]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [2309387097439469568, 10376294091217436672, 4612248968515026944, 49539596437946368, 144115190223339520]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [17306374408218083328, 144678138163494912, 4503600432676864, 36028797018963968]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [9235782314116513792, 3458765063576354816, 144678138163494912, 40673134671560704, 4611686293305294848]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [17297200287169118208, 7696849829888, 18210694889472, 189714134302982144, 277159608320, 4644337656791040]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c11 c10
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c12 c7
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c13 c6
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨23, by decide⟩ c14 c5
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨24, by decide⟩ c15 c4
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c16 c3
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c17 c2
  c18
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00014.record061_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00014.record061_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00014.record061_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00014.record061_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00014.record061_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00014.record061_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00014.record061_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00014.record061_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00014.record061_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00014.record061
