module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow24Part00088Data
public import GraphInputsRow24Part00088Frames
public import GraphInputsRow24Part00088Leaves
public import GraphInputsRow24Part00088Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00088.record000
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record000
def vertexColumn : Fields := ⟨10, hexnat% "3e2d4ad0f43b0dc2f07cac95a368ba71aa6a58d68d8b6538ce4b8ae8789e1783eb46b13c5591e6c5a94e5a5655356352d4754b46d8745d0f6a3a4d5334e332cd4b4ae1b46c5bc1e8751cc789d2729e1725c570de0f13c1f532922c83aa18a64382e524590e5454344d0b6130cd0b0ac1b81d0709c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "1b6db6d369a4da4d26da6da4db6db6d26934da4924924d249b492249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨47, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨68, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨82, by decide⟩, ⟨85, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "19b1080368e7bcf000000", 19241453486080, hexnat% "10000000000000000", hexnat% "2400000000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1981080368e7bcf000000", 19241453486080, hexnat% "10000000000000000", hexnat% "3000000000000000000", hexnat% "2400000000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "9011803606d0cb000000", hexnat% "a000000000000000000", 184750702592, 168225279049728, hexnat% "101000000000000000000", hexnat% "2400000000000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c3 c0
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "24931000069a00c9000000", hexnat% "100000000001200000000", hexnat% "18010000000000000", hexnat% "8000020040802000000", 141801029632, 1924145348608]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "249010000699334d000000", hexnat% "101000000000080000000", hexnat% "18010000000000000", hexnat% "8000020040802000000", 3023656976384, hexnat% "2000000000000000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "811803617c847000000", hexnat% "2080000000800000000000", hexnat% "3000000000180000000", hexnat% "410000000080008000000", 214748364800, hexnat% "100000000000000000000"]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "219b100022127bc7000000", 150633093005312, hexnat% "400000000000008000000", hexnat% "18014000000000000", 4947802324992]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "10b100022026bc7000000", hexnat% "18014000000000000", 4947802324992, hexnat% "80000000801000000000", hexnat% "2410000000080000000000", 18691831889920]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨80, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "250211801699c249000000", hexnat% "11000000000080000000", hexnat% "80000000001000000000", hexnat% "8000020040802000000", 2203385331712, 137438953472]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "a100022144842000000", hexnat% "411000000000008000000", hexnat% "2000000000880000000000", hexnat% "18014000000000000", hexnat% "180000000001000000000", 3848374583296, 152471339008]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c12 c11
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨73, by decide⟩ c13 c10
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c14 c7
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c15 c6
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨68, by decide⟩ c16 c5
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c17 c4
  c18
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record000_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record000_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record000_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record000_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record000_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record000_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record000_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record000_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record000_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00088.record000

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00088.record003
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record003
def vertexColumn : Fields := ⟨10, hexnat% "2c6a98e6a58d62db0e9394e8b92e1ba1e4785e0fac9aa4e9a64d92e6c5716a5396953570d9354d8b52d1b61d4745d0f6c3a8ce3a4cd32cf0b92e2b4ac6b86d1b16f07a1e4731e2749ca719e1745c9715e0f43c4f0bc1f2d14a0e9460d8b152439a1545314a52543550c3382d0b12c2b06e0741c4709c17"⟩
def kindColumn : Fields := ⟨3, hexnat% "db6d369b6db4db6d24924da6db6d36db492492492492492492489249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨57, by decide⟩, ⟨64, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨79, by decide⟩, ⟨86, by decide⟩, ⟨89, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2000208000000000000", hexnat% "20080000000000000000000", hexnat% "400001000000007c000000", hexnat% "1f80000008000000000", 2243003720663040, 8244189724672]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record003_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record003_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record003_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record003_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record003_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record003_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record003_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record003_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record003_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00088.record003

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00088.record005
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record005
def vertexColumn : Fields := ⟨10, hexnat% "f83d2cc732ac3b15c370bc1f1caaa95a368ba71aa6558d62db0ea398e538ce8b92e2ba1e4789e1783eb26a93a5591e6c5a94e555475c368d9354d3362d4b4ad1b61d4745d0f6a354f0ba2d4b32e2b4acab86d1b16f07a1d4731e2749ca785d1715e0f43c8f13c2f07e8a2a83aa18a60d94916439514550d43382d0b0ac1b81d0709c17"⟩
def kindColumn : Fields := ⟨3, hexnat% "36db6db6d369a6d34db6d36da6da4db49b69b6db69369269249249a492493691249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨21, by decide⟩, ⟨22, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨58, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨72, by decide⟩, ⟨77, by decide⟩, ⟨83, by decide⟩, ⟨85, by decide⟩, ⟨88, by decide⟩, ⟨90, by decide⟩, ⟨93, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4082118c40677e486600000", hexnat% "210000000000000100000000", hexnat% "2000000000000040000000", 69659000832, 34359738368]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4000018040477e086600000", hexnat% "210820000000000000000000", hexnat% "2001000000000040000000", 9223372054437298176, 107911053312, 4612248968380809216]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "82118c40602601e600000", hexnat% "42000000000000000000000", 17609365913600, hexnat% "210000000000040100000000", 107202383708160, 106837311488]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "25000018000677e106600000", hexnat% "2021000000000040000000", hexnat% "800000000000800000000", 13835058055684816896, 88583700480, 288230376151711744]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "18c00206fdfe600000", 87960930222080, hexnat% "12020000000000000000000", hexnat% "200000000000210000000000", hexnat% "801000404000000000000", hexnat% "40000000000000000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "252821000406070156600000", 13835058055416381440, 35218731827200, hexnat% "180000006000000000", 88583700480, 88510686035968]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "108c00677e03e600000", hexnat% "100400000000000000", hexnat% "240020000000000000000000", 92341796864, hexnat% "10800000000000800000000", hexnat% "2000000000000040000000"]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "118c00677e01e600000", hexnat% "240020000000000000000000", 288230393331580928, hexnat% "10800000000000800000000", hexnat% "20000000000001c0000000", 69256347648]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "82100040667d9f6600000", hexnat% "84000000000000000", hexnat% "12000000000000000000000", hexnat% "240000000000000000000000", 17746939084800, hexnat% "108000000000000000"]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "82100040656f5be600000", 13835058055282163712, hexnat% "180000000000000000", hexnat% "42000000000000000000000", 36319317196800, hexnat% "210000000000000000000000"]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "118c00616f5be200000", 106652627894272, hexnat% "820000400000000400000", hexnat% "10000000000000840000000", hexnat% "42000000000000000000000", hexnat% "200000000000000000000000"]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "82118840616e41e600000", 4611686018964258816, hexnat% "42000000000000000000000", 106652627894272, hexnat% "210000000000000100000000", 106300440576]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "25202100040227d9fe400000", 17746804867072, 70368746274816, hexnat% "800000004000000000000", 13835058055282163712, hexnat% "180000000000000000"]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "25082100040227d9fe000000", 17746804867072, hexnat% "2000000000000000400000", 70368746274816, 13836183955189006336, hexnat% "180000000000000000"]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "24282100040667d9fe600000", hexnat% "10000000000000000000000", 13835058055282163712, 17746804867072, hexnat% "180000000000000000"]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "110040216e85e400000", 106652627894272, 13836183955189006336, hexnat% "42020000000000000000000", hexnat% "80000000000200000", hexnat% "210800000000000000000000", 92878667776]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨22, by decide⟩ c16 c15
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c17 c14
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c18 c13
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c19 c12
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c20 c11
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c21 c10
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c22 c9
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c23 c8
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c24 c7
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨72, by decide⟩ c25 c6
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c26 c5
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c27 c4
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c28 c3
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c29 c2
  c30
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record005_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record005_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record005_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record005_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record005_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record005_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record005_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record005_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record005_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00088.record005

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00088.record008
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record008
def vertexColumn : Fields := ⟨10, hexnat% "f4ab15c3caaa56ac671aa639956358b61db0ea394e8b92e2ba1e4785e0f8f1aa559b15c5a94e5554d52d475c368d5362d4b4ad8751d176c370ea338d5334cb31cf0ba2d4b8ad2b2ae1b46c5bc1e8761e4751cc789d2729c6785d1725c570de0f43c8f13c2f07c3c0e839a1545314a5154358350d0b41da0d4330ca314c3382d0b0ac1b"⟩
def kindColumn : Fields := ⟨3, hexnat% "36db6db6db6db6db6d36d249249249249249249249249269b49b4db6924da449249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨23, by decide⟩, ⟨24, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨35, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨42, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨81, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fcf20c0008821000000", hexnat% "30c000000010000000", hexnat% "200000000044048800000", 1587659606136455168, 657543137782136832, 6579477580611584]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3dc01fe8844800000000", hexnat% "200000000008079800000", hexnat% "37c000000000000000", hexnat% "2000000200000000000", 6561885394567168, hexnat% "82000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2cf7d6c8800821000000", hexnat% "20000000004c058800000", hexnat% "13082000000000000000", 6597069766656000, 657525545596092416]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "28157fff00019800000", hexnat% "2ea000000000000000", hexnat% "20000000004c860000000", hexnat% "10000800000000000000", hexnat% "5400000000000000000", hexnat% "28100000000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3f9196fff44819800000", hexnat% "200000000008060000000", hexnat% "406000000000000000", 648518346341351424, hexnat% "2e0000000000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3d9596fff44819800000", hexnat% "200000000008060000000", hexnat% "2a6000000000000000", 648518346341351424, hexnat% "2400000000000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "288196fff00019800000", hexnat% "364000000000000000", hexnat% "20000000004c860000000", 648518346341351424, hexnat% "17400000000000000000", hexnat% "82000000000000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨75, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨77, by decide⟩ c7 c4
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "13efeba4700060800000", 7740561859543040, hexnat% "2c100000040000000000", hexnat% "20000000000c819000000", 1459166279268040704]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2cb7e21fe40018000000", 1459166313627779072, hexnat% "13080000008000000000", hexnat% "400020000060800000", hexnat% "200000000004001000000", 684564735546359808]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "37ffe35ff0c059800000", 9007199791611904, hexnat% "200000000040800000000", 2053641430080946176, hexnat% "8000000000000000000"]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "37ffe31ff0c059800000", hexnat% "200000000040820000000", 621496748577128448, hexnat% "8000400000000000000", 1170935903116328960]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "37d96b9570c040000000", hexnat% "8040402000000000000", 1155314041908887552, 27021598301093888, hexnat% "228000000019800000", hexnat% "200000000040800000000"]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨52, by decide⟩ c13 c12
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c14 c11
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3f953ecae44800000000", 73201086130814976, hexnat% "400020000060800000", hexnat% "200000000008019000000", 4785074604081152, hexnat% "2ac000000000000000"]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "39136fbf00831000000", hexnat% "3c000000004000000000", 649644796004007936, hexnat% "40c000000000800000", hexnat% "200000000040048000000", hexnat% "2e0000000000000000"]
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2913648e00000000000", hexnat% "3d000000004000000000", hexnat% "400020000060800000", 685690635453202432, hexnat% "2ec000000008000000", hexnat% "200000000048811000000", 5348024557502464]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c18 c17
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c19 c16
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨73, by decide⟩ c20 c15
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨68, by decide⟩ c21 c10
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨61, by decide⟩ c22 c9
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c23 c8
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c24 c3
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨64, by decide⟩ c25 c2
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c26 c1
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨71, by decide⟩ c27 c0
  c28
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record008_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record008_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record008_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record008_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record008_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record008_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record008_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record008_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record008_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00088.record008
