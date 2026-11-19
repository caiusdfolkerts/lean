module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow24Part00095Data
public import GraphInputsRow24Part00095Frames
public import GraphInputsRow24Part00095Leaves
public import GraphInputsRow24Part00095Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00095.record000
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00095.record000
def vertexColumn : Fields := ⟨10, hexnat% "3e2b43d0eca70dc2f07caca9a568ba1eaa659a968d8b61da8e6394e2b86e8789e1783eac699564b91e6a559695956352d475a34ad1b61d2745d0f6a358e9354e332cc73a2d4b2ac6b86d1b26c5b0ef07a1d4789d2729c6785c9715c3783c8f13c2f07d4ca48b226a862990e2387152459514654344d84c3342c1b81d0709c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "1b6db6d269a69a6924da6db4d34db69b4da6da69269b4924924924da492449249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨46, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨52, by decide⟩, ⟨56, by decide⟩, ⟨59, by decide⟩, ⟨62, by decide⟩, ⟨67, by decide⟩, ⟨69, by decide⟩, ⟨71, by decide⟩, ⟨76, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨84, by decide⟩, ⟨86, by decide⟩, ⟨88, by decide⟩, ⟨90, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "355690084900021196800000", 5066695609679872, hexnat% "a00000010000000000", hexnat% "100000001400000000000", 1139643802189824, 326568509440]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "5210a049044fcc9f800000", hexnat% "80000001100000000", hexnat% "100000001000000000000", hexnat% "10480000000002200000000", hexnat% "340000000012000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "15790a84912436f9f800000", 281543696187392, 1139643802189824, hexnat% "340000000000000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "51590a8491347ff1f800000", hexnat% "200000000000000000000", 1134698147348480, hexnat% "304000000000000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "51490a8491343ff1f800000", hexnat% "300000000000000000000", hexnat% "4000000000000080000000", 1139094046375936, hexnat% "300000000000000000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "11790200112026f1f800000", hexnat% "84800000000000000", hexnat% "344000000000000000000000", 1135247903162368, hexnat% "800000450000000000", 281543696187392]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨69, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c7 c2
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "501008491408ff9b800000", hexnat% "10680000000000004000000", hexnat% "340000000002020000000000", hexnat% "800000450000000000", hexnat% "200001000000000000", hexnat% "100000000000000000000"]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "14790800113477f8f800000", hexnat% "84800000000000000", 1135246024114176, hexnat% "40000200000000000000000", hexnat% "301000000000000000000000"]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "14790000012426e8f800000", hexnat% "341000000000000000000000", hexnat% "800000050000000000", hexnat% "80800001100000000", 1416721000824832, hexnat% "204100000000000000"]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c11 c10
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "501008490708ff9b800000", hexnat% "340000000010020000000000", hexnat% "a00000010000000000", hexnat% "10680000000000004000000", 74766790688768, hexnat% "100000000000000000000"]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2100108001174faa92800000", hexnat% "105400000000000000000000", hexnat% "300000000000004000000", 365223215104, hexnat% "84800000000000000", hexnat% "40080200000000000000000"]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "355490a049170baa99800000", hexnat% "80000001502000000", 74766790688768, hexnat% "300000000000004000000", 274877906944]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "240090a8490501b793800000", 74766790688768, hexnat% "15400000000000000000000", hexnat% "1000000000120a0000000000", hexnat% "300000000000004000000", 309371863040]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨93, by decide⟩ c16 c15
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "11028490749b392800000", hexnat% "800000040000000000", 326635618304, hexnat% "340000000010020000000000", hexnat% "10680000000000000000000", hexnat% "5000000000000000000000"]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "10284905002290800000", hexnat% "800000450002000000", hexnat% "300000000000004000000", 399582953472, hexnat% "15480000000000000000000", 5078094452883456, hexnat% "340000000000000000000000"]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c19 c18
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨69, by decide⟩ c20 c17
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c21 c14
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c22 c13
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c23 c12
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c24 c9
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c25 c8
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨23, by decide⟩ c26 c1
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨76, by decide⟩ c27 c0
  c28
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00095.record000_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00095.record000_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00095.record000_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00095.record000_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00095.record000_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00095.record000_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00095.record000_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00095.record000_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00095.record000_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00095.record000

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00095.record003
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00095.record003
def vertexColumn : Fields := ⟨10, hexnat% "2a659a96558b61db0ea394e2b86e2785e3c4e9366a55969555475c358d534ad1b49d176a358e9354cb3c2e8b92cab1ac9b16f07a1d4789d2729c6785d1725c5723c4f0bc1f2d28c1c94a0da0e438b11c68952685294950d60d4348d50c6314c3382d0b12e0741c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "36da4926db4da69a49269b4d24934d2492492492489249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨47, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨55, by decide⟩, ⟨58, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨66, by decide⟩, ⟨68, by decide⟩, ⟨71, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "6014f40c1fffc0000000", hexnat% "810010000000000000", hexnat% "90000000000000000000", hexnat% "100000000000000000000", 45774868087570432]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "5010a0aebfffc0000000", hexnat% "810010000000000000", hexnat% "120000000000000000000", hexnat% "45400000000000000", hexnat% "80000000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "9180181fffc0000000", hexnat% "50000000000000000000", hexnat% "45400000000000000", hexnat% "120000004000000000000", 45774868087570432, hexnat% "80002000000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c3 c0
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "6081f41c1a03c0000000", hexnat% "140000008800000000", 45774868087570432, hexnat% "90000000044400000000", hexnat% "100000000000000000000", 1305670057984]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "5000a0aebfffc0000000", hexnat% "810010000000000000", hexnat% "120000000000000000000", hexnat% "80000000000000000000", hexnat% "145400000000000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "19081a0981fffc0000000", hexnat% "60000000000000000000", 1688849860263936, 9183121115185152, hexnat% "145400000000000000"]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "808180981fffc0000000", hexnat% "50000000000000000000", 9746071068606464, 6917529027641081856, hexnat% "120000004000000000000", hexnat% "141400000000000000"]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨79, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c9 c6
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "5081a01eb703c0000000", 45036288331481088, hexnat% "145400000000000000", hexnat% "120000000088800000000", hexnat% "80000000000000000000", 206158430208]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "818018030000000000", hexnat% "50000000000100000000", 45774868087570432, hexnat% "145400000200000000", hexnat% "120000004088800000000", hexnat% "80002000044400000000", 17801565700096]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c12 c11
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c13 c10
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c14 c5
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c15 c4
  c16
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00095.record003_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00095.record003_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00095.record003_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00095.record003_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00095.record003_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00095.record003_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00095.record003_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00095.record003_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00095.record003_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00095.record003

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00095.record007
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00095.record007
def vertexColumn : Fields := ⟨10, hexnat% "f4ab29c2f2aa5aa9a568ba1eaa659a96558b61db0ea3a2e4b8ae8791e2783e3c6a95a699564b91e6a5594e5a5555354b51d70da358d8b52d2b61d4749d0f6a358e9354cb31cf0ba2d4b8ad2b2ac6b86d1b26c5b0ef07a1e4789d2729e1745c970de0f43c8f0bc1f5186615a892a499a1545294652545550c6314e0b42c2b06e0741c4709c17"⟩
def kindColumn : Fields := ⟨3, hexnat% "db6db6db4d34db6db6da69a6924924d36d369b4d34924924924924924924d2249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨24, by decide⟩, ⟨25, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨53, by decide⟩, ⟨55, by decide⟩, ⟨58, by decide⟩, ⟨61, by decide⟩, ⟨65, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨76, by decide⟩, ⟨78, by decide⟩, ⟨80, by decide⟩, ⟨91, by decide⟩, ⟨93, by decide⟩, ⟨95, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8001378000811fffb000000", hexnat% "a00000000000000000000000", 45317471250415616, hexnat% "4822400000000000000", 1950533627674624, hexnat% "140000000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "a000034000a1547ffb000000", hexnat% "380000000000000000", hexnat% "80010000008008000000000", 1278732023103488, hexnat% "4822400000000000000", hexnat% "140000002200000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "10224adfddfbb000000", hexnat% "800002000000000000000000", hexnat% "280000000000000000000000", hexnat% "150000002020000000000", hexnat% "4900000002040000000", hexnat% "680000000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "88001218008fff943b000000", hexnat% "200000400020000080000000", hexnat% "140022400000000000000", 460635242496, hexnat% "5a00000000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "a000024000a7ff94bb000000", 460635242496, hexnat% "80010180008000000000000", hexnat% "140022400000000000000", hexnat% "5a00000000000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "800106000087ff9c3b000000", 428422987776, hexnat% "200000400020000000000000", hexnat% "50022400000000000000", hexnat% "80000180008000000000000", hexnat% "1a00000000000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "a000024000a7ff94bb000000", hexnat% "80010180008000000000000", 460635242496, hexnat% "140022400000000000000", hexnat% "5a00000000000000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7f80402e7ffe3000000", hexnat% "a80000000000000000000000", hexnat% "150022000000000000000", 1134696402518016, 47586863250145280]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40800007fffffb000000", hexnat% "800002000080000000000000", hexnat% "200000400020000000000000", hexnat% "110022400000000000000", hexnat% "80000180008000000000000", hexnat% "5200000000000000000"]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "a80000000000cc9462000000", hexnat% "3680000000000000000", 47587962761773056, 1726233255608320, hexnat% "150022400000000000000", 316099526656, hexnat% "4900000002200000000"]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c10 c7
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c11 c6
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c12 c5
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c13 c4
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c14 c3
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c15 c2
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c16 c1
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c17 c0
  c18
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00095.record007_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00095.record007_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00095.record007_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00095.record007_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00095.record007_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00095.record007_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00095.record007_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00095.record007_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00095.record007_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00095.record007
