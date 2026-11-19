module
prelude
public import FacetCliqueRaw
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow24Part00095Data
public import GraphInputsRow24Part00095Frames
public import GraphInputsRow24Part00095Leaves
public import GraphInputsRow24Part00095Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

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

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00095.record004
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "f23a8daa9966a59562d876c3a8e538ae1b89e178f13a4d9a9565a55552d475c368d534ad1b49d176a358ce3a4d5334f0b62e4b32cab1ac9b16f07a1d4789d2729c6785d1725c5723c4f0bc1f2c872a294a0da0e438b11c689524358350da0d4328c6324c530ce0b42c8b12e0741c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "9b6db4924db69b6db4924db692492492492492492492489249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00095.record004 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00095.record004 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00095.record004.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 49), (facetIndex 53), (facetIndex 56), (facetIndex 74), (facetIndex 90)]))
 (.branch 2
 (.leaf ([(facetIndex 30), (facetIndex 31), (facetIndex 32), (facetIndex 33), (facetIndex 44), (facetIndex 52), (facetIndex 65), (facetIndex 81)]))
 (.leaf ([(facetIndex 34), (facetIndex 38), (facetIndex 42), (facetIndex 63), (facetIndex 66), (facetIndex 79), (facetIndex 82)]))))
 (.branch 5
 (.branch 4
 (.leaf ([(facetIndex 35), (facetIndex 39), (facetIndex 43), (facetIndex 64), (facetIndex 67), (facetIndex 80), (facetIndex 83)]))
 (.leaf ([(facetIndex 45), (facetIndex 47), (facetIndex 50), (facetIndex 54), (facetIndex 57)])))
 (.branch 6
 (.leaf ([(facetIndex 46), (facetIndex 48), (facetIndex 51), (facetIndex 55), (facetIndex 58)]))
 (.leaf ([(facetIndex 36), (facetIndex 37), (facetIndex 40), (facetIndex 41)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "68b40000000068b400160b01b059616b66b668924z16;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 7
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00095.record004 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00095.record004_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00095.record004" "{\"atoms\":[]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00095.record004" 0

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00095.record004" "{\"ridges\":[],\"owners\":[],\"edges\":[],\"groupings\":[2]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00095.record004" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00095.record004\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":false,\"clauses\":[[]],\"atoms\":[],\"rules\":[{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true}]}"
  "p cnf 0 1\n 0\n"
  "2 0 1 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00095.record004.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00095.record004.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00095.record004.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00095.record004.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00095.record004 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS noSame
  exact boundary_unsat S HS noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00095.record004.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00095.record004.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00095.record004.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00095.record004.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00095.record004 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00095.record004_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00095.record004_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00095.record004_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00095.record004_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00095.record004_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00095.record004_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00095.record004_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00095.record004 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00095.record004_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00095.record004_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00095.record004_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00095.record004

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00095.record008
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "3caaa5aa9a568ba1eaa659a96558b61db0e8b92e8791e0f8f1aa569a65592e479a9565a55552d475c362d4b61d4743da8d6338e9354cd32cc73c2d8b52e2b4ac6b86d1b16c3bc1e8791e2749ca785d1725c3783d0f0bc1fa28aa2694619856a24a92654519455a0d4328c6324c5382d0b22c2b06e0741c4709c17"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1a69a6d34d36db6d34d369a69b6db492492492492492492492492249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00095.record008 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00095.record008 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00095.record008.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 39), (facetIndex 66), (facetIndex 68), (facetIndex 70)]))
 (.leaf ([(facetIndex 50), (facetIndex 73), (facetIndex 75), (facetIndex 77)])))
 (.branch 3
 (.leaf ([(facetIndex 85), (facetIndex 87), (facetIndex 89)]))
 (.leaf ([(facetIndex 92), (facetIndex 94), (facetIndex 96)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 32), (facetIndex 33), (facetIndex 34), (facetIndex 35), (facetIndex 36), (facetIndex 37), (facetIndex 38), (facetIndex 40), (facetIndex 41)]))
 (.leaf ([(facetIndex 53), (facetIndex 54), (facetIndex 56), (facetIndex 57), (facetIndex 59)])))
 (.branch 7
 (.leaf ([(facetIndex 43), (facetIndex 46), (facetIndex 49), (facetIndex 52), (facetIndex 55), (facetIndex 58)]))
 (.leaf ([(facetIndex 28), (facetIndex 29), (facetIndex 30), (facetIndex 31), (facetIndex 42), (facetIndex 44), (facetIndex 45), (facetIndex 47), (facetIndex 48), (facetIndex 51)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "30c3010410000008208000000000badd6ee77fbfde4124924fffz15;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def grouped2_0000 : List Nat := [0]
def grouped2_0001 : List Nat := [0, 1]
def grouped2_0002 : List Nat := [0, 1, 2, 3]
def grouped2_0004 : List Nat := [1]
def grouped2_0005 : List Nat := [2]
def grouped2_0006 : List Nat := [2, 3]
def grouped2_0007 : List Nat := [3]
def grouped2_0008 : List Nat := [4, 5, 6, 7]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00095.record008 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00095.record008_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00095.record008" "{\"atoms\":[{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00095.record008" 31

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00095.record008" "{\"ridges\":[[39,70],[50,138],[75,152],[77,168],[87,84],[89,100],[94,648],[96,648]],\"owners\":[[39,70,[22,23,24],[2]],[50,138,[25,26,27],[7]],[87,84,[16,66],[22,68,85]],[89,100,[17,66],[23,70,85]],[75,152,[25,92],[19,73,94]],[77,168,[26,92],[20,73,96]],[94,648,[21,77],[27,75,96]],[96,648,[21,75],[27,77,94]]],\"edges\":[],\"groupings\":[2]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00095.record008" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00095.record008\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":false,\"clauses\":[[-12,-1],[-12,-2],[-13,-1],[-13,-2],[-14,-1],[-14,-2],[-15,-3],[-16,-3],[-17,-3],[-18,-4],[-18,-5],[-18,-6],[-19,-4],[-19,-5],[-19,-6],[-20,-4],[-20,-5],[-20,-6],[-21,-7],[-21,-8],[-21,-9],[-21,-12],[-21,-18],[-22,-7],[-22,-8],[-22,-9],[-23,-7],[-23,-8],[-23,-9],[-10,4,5,6],[-11,7,8,9],[-19,1,12],[-20,2,12],[-16,7,21],[-17,8,21],[-22,3,17],[-23,3,16],[-24,10,12,13,14],[-25,11,15,16,17],[-26,18,19,20],[-27,21,22,23],[-28,24],[-28,25],[-29,26],[-29,27],[-30,28],[-30,29],[-31,30],[31]],\"atoms\":[{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2}],\"rules\":[{\"tag\":\"incompatible\",\"a\":66,\"b\":16},{\"tag\":\"incompatible\",\"a\":66,\"b\":17},{\"tag\":\"incompatible\",\"a\":68,\"b\":16},{\"tag\":\"incompatible\",\"a\":68,\"b\":17},{\"tag\":\"incompatible\",\"a\":70,\"b\":16},{\"tag\":\"incompatible\",\"a\":70,\"b\":17},{\"tag\":\"incompatible\",\"a\":73,\"b\":21},{\"tag\":\"incompatible\",\"a\":75,\"b\":21},{\"tag\":\"incompatible\",\"a\":77,\"b\":21},{\"tag\":\"incompatible\",\"a\":85,\"b\":22},{\"tag\":\"incompatible\",\"a\":85,\"b\":23},{\"tag\":\"incompatible\",\"a\":85,\"b\":24},{\"tag\":\"incompatible\",\"a\":87,\"b\":22},{\"tag\":\"incompatible\",\"a\":87,\"b\":23},{\"tag\":\"incompatible\",\"a\":87,\"b\":24},{\"tag\":\"incompatible\",\"a\":89,\"b\":22},{\"tag\":\"incompatible\",\"a\":89,\"b\":23},{\"tag\":\"incompatible\",\"a\":89,\"b\":24},{\"tag\":\"incompatible\",\"a\":92,\"b\":25},{\"tag\":\"incompatible\",\"a\":92,\"b\":26},{\"tag\":\"incompatible\",\"a\":92,\"b\":27},{\"tag\":\"incompatible\",\"a\":92,\"b\":66},{\"tag\":\"incompatible\",\"a\":92,\"b\":85},{\"tag\":\"incompatible\",\"a\":94,\"b\":25},{\"tag\":\"incompatible\",\"a\":94,\"b\":26},{\"tag\":\"incompatible\",\"a\":94,\"b\":27},{\"tag\":\"incompatible\",\"a\":96,\"b\":25},{\"tag\":\"incompatible\",\"a\":96,\"b\":26},{\"tag\":\"incompatible\",\"a\":96,\"b\":27},{\"tag\":\"mate\",\"ridge\":70,\"a\":39,\"owners\":[22,23,24]},{\"tag\":\"mate\",\"ridge\":138,\"a\":50,\"owners\":[25,26,27]},{\"tag\":\"mate\",\"ridge\":84,\"a\":87,\"owners\":[16,66]},{\"tag\":\"mate\",\"ridge\":100,\"a\":89,\"owners\":[17,66]},{\"tag\":\"mate\",\"ridge\":152,\"a\":75,\"owners\":[25,92]},{\"tag\":\"mate\",\"ridge\":168,\"a\":77,\"owners\":[26,92]},{\"tag\":\"mate\",\"ridge\":648,\"a\":94,\"owners\":[21,77]},{\"tag\":\"mate\",\"ridge\":648,\"a\":96,\"owners\":[21,75]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[39,66,68,70],\"full_literals\":[-24,10,12,13,14]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[50,73,75,77],\"full_literals\":[-25,11,15,16,17]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[85,87,89],\"full_literals\":[-26,18,19,20]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[92,94,96],\"full_literals\":[-27,21,22,23]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-28,24,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-28,false,25],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-29,26,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-29,false,27],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-30,28,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-30,false,29],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-31,30,false],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true}]}"
  "p cnf 31 49\n-12 -1 0\n-12 -2 0\n-13 -1 0\n-13 -2 0\n-14 -1 0\n-14 -2 0\n-15 -3 0\n-16 -3 0\n-17 -3 0\n-18 -4 0\n-18 -5 0\n-18 -6 0\n-19 -4 0\n-19 -5 0\n-19 -6 0\n-20 -4 0\n-20 -5 0\n-20 -6 0\n-21 -7 0\n-21 -8 0\n-21 -9 0\n-21 -12 0\n-21 -18 0\n-22 -7 0\n-22 -8 0\n-22 -9 0\n-23 -7 0\n-23 -8 0\n-23 -9 0\n-10 4 5 6 0\n-11 7 8 9 0\n-19 1 12 0\n-20 2 12 0\n-16 7 21 0\n-17 8 21 0\n-22 3 17 0\n-23 3 16 0\n-24 10 12 13 14 0\n-25 11 15 16 17 0\n-26 18 19 20 0\n-27 21 22 23 0\n-28 24 0\n-28 25 0\n-29 26 0\n-29 27 0\n-30 28 0\n-30 29 0\n-31 30 0\n31 0\n"
  "50 30 0 49 48 0\n51 28 0 50 46 0\n52 29 0 50 47 0\n53 24 0 51 42 0\n54 25 0 51 43 0\n55 26 0 52 44 0\n56 27 0 52 45 0\n57 -8 0 56 20 25 28 41 0\n58 -9 0 56 21 26 29 41 0\n59 -6 0 55 12 15 18 40 0\n60 -7 0 56 19 24 27 41 0\n61 -11 0 60 57 58 31 0\n62 -3 0 61 54 7 8 9 39 0\n63 -4 0 55 10 13 16 40 0\n64 -5 0 55 11 14 17 40 0\n65 -10 0 64 63 59 30 0\n66 -1 0 65 53 1 3 5 38 0\n67 -2 0 65 53 2 4 6 38 0\n68 -21 0 66 67 55 22 23 32 33 40 0\n69 -17 0 68 57 35 0\n70 -16 0 68 60 34 0\n71 -22 0 69 62 36 0\n72 -23 0 70 62 37 0\n73 0 71 72 56 68 41 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00095.record008.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00095.record008.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00095.record008.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00095.record008.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00095.record008 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS noSame
  exact boundary_unsat S HS noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00095.record008.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00095.record008.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00095.record008.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00095.record008.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00095.record008 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00095.record008_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00095.record008_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00095.record008_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00095.record008_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00095.record008_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00095.record008_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00095.record008_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00095.record008 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00095.record008_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00095.record008_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00095.record008_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00095.record008
