module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow29Part00161Data
public import GraphInputsRow29Part00161Frames
public import GraphInputsRow29Part00161Leaves
public import GraphInputsRow29Part00161Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00161.record001
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00161.record001
def vertexColumn : Fields := ⟨10, hexnat% "2b42f07cac95a2e87aa9a96958d68d8b61d92e2b86e8789e1783eac5592e479a9695954d58d4b51d52d2b46d8749d1743da8e5354cd38cc734acab1ae1b46c9bc1d8791cc789d2719e1725c570de0f23c1f532922c94a1683aa19462990e1382ea44b1524590e685514a54344d0b68350ca384c9314c3342c4b0ac1b81d0721c4709c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "36d24926da6926d249249b69a49b492492492492492492492249249249249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2, 3]
def candidates : List (Fin raw.n) := [⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩, ⟨95, by decide⟩, ⟨96, by decide⟩, ⟨97, by decide⟩, ⟨98, by decide⟩, ⟨99, by decide⟩, ⟨100, by decide⟩, ⟨101, by decide⟩, ⟨102, by decide⟩, ⟨103, by decide⟩, ⟨104, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .size 3
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1f3f8fcfe3ea282790000000000", 17317308137472000, hexnat% "15140000000000000", hexnat% "40001000800000000000000", hexnat% "8020200800400000000000000", hexnat% "4010100400000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1c9fef27fbc0c417f0000000000", hexnat% "10000400008280000000000000", 17592186044416000, hexnat% "17100000000000000", hexnat% "22000880020000000000000000", hexnat% "4010100400000000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1d5f9f57e7c9280f90000000000", hexnat% "40001000801060000000000", 17451448556060672, hexnat% "16140000000000000", hexnat% "8020200800400000000000000", hexnat% "22000880020000000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1d5fff57e7d9288ff0000000000", hexnat% "1000801000000000000", 15199648742375424, 7007601020188491776, hexnat% "8000200800400000000000000", hexnat% "22000880020000000000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1cffff37ffdffcbff0000000000", hexnat% "10000400000000000000000000", 14636698788954112, hexnat% "20000880020000000000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1d5fbf57e3dfbc87d0000000000", hexnat% "40001000001020000000000", hexnat% "c00000800000000000", hexnat% "8000200000400000000000000", 15199648742375424, hexnat% "22000880020000000000000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨89, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1d1f9f47e3d8388790000000000", hexnat% "40001000801060000000000", 15340386230730752, hexnat% "20000800026040000000000000", hexnat% "4000100401000000000000000", hexnat% "2000080000000000000000000", hexnat% "8020200800400000000000000"]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨88, by decide⟩ c9 c4
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨77, by decide⟩ c0 c10
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1f3f8f47e3cc284790000000000", hexnat% "880022002000000000000", 16191408230629376, hexnat% "11140000000000000", hexnat% "40001000800000000000000", hexnat% "8020200800400000000000000", hexnat% "4010100400000000000000000"]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1ebfafafebe24427b0000000000", hexnat% "10000400008280000000000000", hexnat% "40001000801040000000000", 17029236090994688, hexnat% "15100000000000000", hexnat% "4010100400000000000000000"]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1ddfbf57e7c9280f90000000000", hexnat% "40001000801060000000000", hexnat% "200800440000000000000", 17451448556060672, hexnat% "16100000000000000", hexnat% "22000880020000000000000000"]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1d5fdf47e3c83807d0000000000", hexnat% "1000801020000000000", 17592186044416000, hexnat% "17040000000000000", hexnat% "100400000000000000000", hexnat% "22000880020000000000000000", hexnat% "8020200800400000000000000"]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1effff27fbc0c417f0000000000", hexnat% "10000400008280000000000000", hexnat% "880022002000000000000", 17029236090994688, hexnat% "15100000000000000", hexnat% "100400000000000000000"]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .classes 3 [hexnat% "1ffffffffffffffff0000000000"]
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨86, by decide⟩ c17 c16
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨87, by decide⟩ c18 c15
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨91, by decide⟩ c19 c14
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨93, by decide⟩ c20 c13
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨94, by decide⟩ c21 c12
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨95, by decide⟩ c22 c11
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨102, by decide⟩ c23 c3
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨103, by decide⟩ c24 c2
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨104, by decide⟩ c25 c1
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨66, by decide⟩ c26 c0
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨84, by decide⟩ c27 c0
  c28
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00161.record001_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00161.record001_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00161.record001_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00161.record001_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00161.record001_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00161.record001_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00161.record001_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00161.record001_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00161.record001_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00161.record001

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00161.record004
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00161.record004
def vertexColumn : Fields := ⟨10, hexnat% "2ac570bc1f2aa568ba1eaa6558b61db0ea398e9394e33a2e4b8ae1ba1e4789e1783eaa5592e479a95552d475c368d6364d534cd8b52d2b46d8751d2745d0f6a354cb31cf0b62e4b32e2b4ac6b86d1b26f0761e4731e2749c6785d1725e0f43c8f13c2f07e8a528aa1683aa1946298560da89524a916439a1545294550d68350ca314c3382d0b22c4b0ac1b81d0721c4709c17"⟩
def kindColumn : Fields := ⟨3, hexnat% "36da4924934da6da6db49249249a6d36d36da492492492492492492492491249249249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2, 3]
def candidates : List (Fin raw.n) := [⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩, ⟨95, by decide⟩, ⟨96, by decide⟩, ⟨97, by decide⟩, ⟨98, by decide⟩, ⟨99, by decide⟩, ⟨100, by decide⟩, ⟨101, by decide⟩, ⟨102, by decide⟩, ⟨103, by decide⟩, ⟨104, by decide⟩, ⟨105, by decide⟩, ⟨106, by decide⟩, ⟨107, by decide⟩, ⟨108, by decide⟩, ⟨109, by decide⟩, ⟨110, by decide⟩, ⟨111, by decide⟩, ⟨112, by decide⟩, ⟨113, by decide⟩, ⟨114, by decide⟩, ⟨115, by decide⟩, ⟨116, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1f11fffe23fffc041fffe000000000", 8926134461448323072, hexnat% "4400008800010000000000000000", hexnat% "8800011000020000000000000000", hexnat% "2200004400008000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1e89fffd13fffa005fffe000000000", 9196350439090552832, hexnat% "2200004400008000000000000000", hexnat% "11000022000040000000000000000", hexnat% "4400008800010000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1f55fffeabfffd04210fe000000000", 8708132091985920, 8917127262193582080, hexnat% "2200004400008000000000000000", hexnat% "8800011000020000000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1eabfffd57fffa814057e000000000", 8910442231496704, 9124292845052624896, hexnat% "4400008800010000000000000000", hexnat% "11000022000040000000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1f55fffeabfffdc731cfe000000000", hexnat% "2200004400000000000000000000", 3993426232082432, 4089268461652410368, hexnat% "8800011000020000000000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1f55fffeabfffd6c3b0fe000000000", 144255925564211200, 1249045209153536, 1279022294173220864, hexnat% "8800011000020000000000000000", hexnat% "2200004400008000000000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1f11fffe23fffd441107e000000000", hexnat% "4400008800000020080000000000", hexnat% "8800011000020040100000000000", 4186940278571008, 4287426845256712192, hexnat% "2200004400008000000000000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨66, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨64, by decide⟩ c7 c4
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .size 3
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨81, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1f11fffe23fffc240907e000000000", 4616189618054758400, hexnat% "8800011000020040100000000000", hexnat% "4400008800010020080000000000", hexnat% "2200004400008100400000000000", 1864771720708096, 1909526242005090304]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1e89fffd13fffa104417e000000000", 4616189618054758400, hexnat% "11000022000040401000000000000", hexnat% "2200004400008100400000000000", hexnat% "4400008800010020080000000000", 2990671627550720, 3062447746611937280]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1fddffffbbffff9f27cfe000000000", 6808175999188992, 6971572223169527808, hexnat% "2200004400000000000000000000"]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1fb9ffff73ffffffeb1fe000000000", hexnat% "4400008800000000000000000000", hexnat% "200000400000000600000000000", 5770237022568448]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1f9dffff3bffff1d5fffe000000000", hexnat% "2200004400008000000000000000", hexnat% "4000008000000220000000000000", 6953557824660045824]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1f9bffff37fffb99dfffe000000000", hexnat% "42420000000000000", hexnat% "4400008800000000000000000000", hexnat% "2000004000000000000000000000", 4755801206503243776]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1fb9ffff73fffdffeb2fe000000000", hexnat% "20004500000000000", hexnat% "4400008800000000000000000000", hexnat% "200000400000000000000000000", 4644337115725824]
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1f99ffff33fffd28cb27e000000000", hexnat% "21004000000000000", 4616189618054758400, hexnat% "400000800000000c80000000000", hexnat% "2200004400008100000000000000", hexnat% "4000008000000620000000000000", 17592186044416]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c18 c17
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c19 c16
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c20 c15
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c21 c14
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨64, by decide⟩ c22 c13
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨76, by decide⟩ c9 c23
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1f55fffeabfffd04210fe000000000", 8708132091985920, 8917127262193582080, hexnat% "8800011000020000000000000000", hexnat% "2200004400008000000000000000"]
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1e45fffc8bfff902208fe000000000", 4616189618054758400, hexnat% "11000022000040401000000000000", hexnat% "8800011000020040100000000000", hexnat% "2200004400008100400000000000", 3975834046038016, 4071254063142928384]
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1eeffffd57fffa814057e000000000", hexnat% "8800010020080000000000", 8901646138474496, 9115285645797883904, hexnat% "11000022000040000000000000000"]
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1e23fffc47fff8818067e000000000", 4616189618054758400, hexnat% "8800011000020040100000000000", hexnat% "11000022000040401000000000000", hexnat% "4400008800010020080000000000", 4081387162304512, 4179340454199820288]
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1eabfffd57fffa814057e000000000", 8910442231496704, 9124292845052624896, hexnat% "11000022000040000000000000000", hexnat% "4400008800010000000000000000"]
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1f77fffeabfffd04210fe000000000", hexnat% "4400008100400000000000", 8637763347808256, 8845069668155654144, hexnat% "8800011000020000000000000000"]
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .classes 3 [hexnat% "1fffffffffffffffffffe000000000"]
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨92, by decide⟩ c31 c30
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨93, by decide⟩ c32 c29
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨94, by decide⟩ c33 c28
  let c35 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨95, by decide⟩ c34 c27
  let c36 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨97, by decide⟩ c35 c26
  let c37 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨98, by decide⟩ c36 c25
  let c38 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨99, by decide⟩ c37 c24
  let c39 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨101, by decide⟩ c38 c12
  let c40 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨102, by decide⟩ c39 c11
  let c41 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨104, by decide⟩ c40 c10
  let c42 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨113, by decide⟩ c41 c3
  let c43 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨114, by decide⟩ c42 c2
  let c44 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨115, by decide⟩ c43 c1
  let c45 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨116, by decide⟩ c44 c0
  c45
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00161.record004_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00161.record004_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00161.record004_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00161.record004_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00161.record004_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00161.record004_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00161.record004_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00161.record004_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00161.record004_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00161.record004
