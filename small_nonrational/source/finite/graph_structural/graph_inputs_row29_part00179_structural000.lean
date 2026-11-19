module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow29Part00179Data
public import GraphInputsRow29Part00179Frames
public import GraphInputsRow29Part00179Leaves
public import GraphInputsRow29Part00179Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00179.record006
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00179.record006
def vertexColumn : Fields := ⟨10, hexnat% "6d1743d2ac4f0bc1f1b25c8f2a693a2e87a6996639996558d64d8b61da8e9392e2b86e4789e1783e6c5713c6a9a65392e6a56956539595554d54d4b51d68d9362d4b4ad4749d1743d68d6338e9364d5334d332cc73a2e4b4acab1ae1b46c9b0ef0761e4751cc749ca719d1725c570dd0f23c2f07c781b05aa1a0e139312c4711a4590e685494a51960d1342da0d1324c5382c4b06e0741c8711c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "6db6d36db69b6db6da4da6d34936924936d249249b49b69249249b492492492492692449249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨93, by decide⟩, ⟨96, by decide⟩, ⟨99, by decide⟩, ⟨100, by decide⟩, ⟨110, by decide⟩, ⟨117, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4001001e17cc4708ffa780000000", hexnat% "18000000000000000000000000", 55450570411999232, hexnat% "e6028000000000000000000", hexnat% "200000200000000000005000000000", 4035788216077385728]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4001001e0fc80708ff9700000000", hexnat% "18000000000000000000000000", 55450572559482880, hexnat% "200000200030040000006000000000", 8647474234504773632, hexnat% "e6000000000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2000002010380c7acffdf780000000", hexnat% "18000000000000000000000000", hexnat% "7400000000000000000", hexnat% "4001000000000500020000000000", hexnat% "e00800000000000000000", hexnat% "e6000000000000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2000002000380c79cf7df680000000", hexnat% "18000000000000000000000000", hexnat% "4001000000000600820100000000", hexnat% "7400000000000000000", hexnat% "1e00800000000000000000", hexnat% "e6000000000000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "100e603c447f8781b200000000", hexnat% "1e01800000000000000000", hexnat% "204001200000080008000000000000", hexnat% "8000002000040100580000000", 121221156962304]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2000002e7e3fcc000881f380000000", hexnat% "4001000000000700020000000000", hexnat% "18000000000000100000000000", 118764435668992, 55450570411999232, 8647474234504773632]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40010e60000c7fcf83b380000000", hexnat% "200000200038000000004000000000", hexnat% "18000000000000100000000000", 118764435668992, hexnat% "7400000000000000000", hexnat% "1e00800000000000000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2000082e7e3fcc04cf93f780000000", hexnat% "10000000000000400000000000", hexnat% "4001000000000300000000000000", 48378511622144, 8646911284551352320]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2000002e7e3fcc6440fff780000000", hexnat% "18000000000000000000000000", 37436171902517248, hexnat% "4001000000000308000000000000", 1729945206863691776]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2000092e7e3fcc0448b7f780000000", hexnat% "4000000000000300000000000000", 79164837199872, hexnat% "10000000000081000000000000", 8648600134411616256]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2000002e7e3fcc0440a3f280000000", hexnat% "4001000000000308000100000000", hexnat% "18000000000000100000000000", 83580063580160, 4649122190329905152, 4035788216077385728]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨73, by decide⟩ c10 c9
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c11 c8
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c12 c7
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "e7e39c47f47a3f580000000", 101163659689984, hexnat% "10000004000080000000000000", hexnat% "204001200000080008000000000000", hexnat% "8000002000000000000000000"]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "19027e3fcc7fcfd7f780000000", hexnat% "c0000000000000000000000", hexnat% "204000200000000000000000000000", 43980465111040]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "19006a27cc7fcfd1f780000000", hexnat% "204000200000000000000000000000", hexnat% "1000000000240000000000", hexnat% "e0018000000000000000000", hexnat% "4000000000a0000000000"]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨81, by decide⟩ c16 c15
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "e683a847f4781f480000000", hexnat% "10000004000080500200000000", hexnat% "9200000000000000000000000", hexnat% "204000000000080008000000000000", hexnat% "1601400000000000000000", 50581829844992]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨73, by decide⟩ c18 c17
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨83, by decide⟩ c19 c14
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2000002e7e3fcc020281f380000000", hexnat% "4001000000000508020000000000", hexnat% "18000000000000100000000000", 8648318659434905600, 118764435668992, 54043195528445952]
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "100e7e3fc47f87a3f380000000", 101172249624576, hexnat% "8200000000040000000000000", hexnat% "204001000000080008000000000000"]
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "e6838447f07a1f080000000", hexnat% "10000004000080500200000000", hexnat% "204001200000080008000000000000", hexnat% "1601800000000000000000", 15414637625344, hexnat% "8000002000040000000000000"]
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨70, by decide⟩ c23 c22
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40090e7837cc7fcffff780000000", hexnat% "10000000000000000000000000", hexnat% "608000000000000000000", hexnat% "200000200000000000000000000000"]
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40090e6037cc7fcfb3f780000000", hexnat% "200000200008000000000000000000", hexnat% "10000000000000400000000000", 13194139533312, hexnat% "1e00000000000000000000"]
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c26 c25
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2000092e7e3fcc254ab5f780000000", hexnat% "4000000000000200020000000000", hexnat% "10000000000080400000000000", 1152930300699869184, 5189554145614364672]
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20400920203fcc244a91b780000000", hexnat% "10000000000080400000000000", 6342475650221211648, hexnat% "1e00000000000000000000", hexnat% "e4000000300000000000000", 50852412784640]
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨75, by decide⟩ c29 c28
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c30 c27
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4001003e37c4270afff700000000", hexnat% "e4008000000000000000000", hexnat% "18000000000000000000000000", hexnat% "200000200000080000000080000000", 6342475650221211648, 54043195528445952]
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2040012e6e3acc270a83f180000000", hexnat% "1005000000000200000000", 6342475650221211648, hexnat% "18000000000000100000000000", 118764435668992, 54043195528445952]
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "e7c3a047f07fff780000000", hexnat% "10000004400080000000000000", hexnat% "201800000000000000000", hexnat% "8200000000040000000000000", hexnat% "204001000000080008000000000000"]
  let c35 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "e7a3a047f07fff780000000", hexnat% "10000004400080000000000000", hexnat% "401800000000000000000", hexnat% "8200000000040000000000000", hexnat% "204001000000080008000000000000"]
  let c36 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8383a0478c7fff780000000", hexnat% "18000000000000000000000000", hexnat% "601c00000000000000000", hexnat% "4000000000000000000", hexnat% "204001200000080008000000000000", hexnat% "64000000700000000000000"]
  let c37 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c36 c35
  let c38 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c37 c34
  let c39 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "e643a047f07abf080000000", hexnat% "204001200000080008000000000000", hexnat% "10000004000080500200000000", hexnat% "1a01c00000000000000000", 4419521347584, hexnat% "8000000000040000000000000"]
  let c40 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "820203a0c78cfb7b780000000", hexnat% "10000004000000400000000000", hexnat% "204001000000000000000000000000", 9070970929152, hexnat% "1e01c00000000000000000", hexnat% "e4000000700000000000000"]
  let c41 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "e623a047f47a7f080000000", hexnat% "204001200000080008000000000000", hexnat% "10000004000080500200000000", hexnat% "400000000080100000000", hexnat% "1801c00000000000000000", hexnat% "8000000000000000400000000"]
  let c42 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4009003e3fcc3f4effb780000000", 4647996290423062528, hexnat% "200000200000000000004000000000", hexnat% "10000000000000000000000000", hexnat% "e4000000000000000000000"]
  let c43 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20000820203b0c7acffff780000000", hexnat% "10000004400000000000000000", hexnat% "4001000000000500000000000000", hexnat% "1e00800000000000000000", hexnat% "e4000000000000000000000"]
  let c44 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20001820203a0c3c43fff780000000", 4648840715353194496, hexnat% "4001000000000308000000000000", hexnat% "1005400000000000000000", hexnat% "e4000000000000000000000", hexnat% "e00800000000000000000"]
  let c45 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1000303f4478c7f3f380000000", hexnat% "8000000000000000400000000", 13194139533312, hexnat% "e00800000000000000000", hexnat% "204001200000080008000000000000", hexnat% "e4000000700000000000000"]
  let c46 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20400120203e0c384aa3f180000000", 4649122198919839744, hexnat% "18000000000000100000000000", 83580063580160, hexnat% "80800000000000000000000", hexnat% "1601c00000000000000000", hexnat% "64000000700000000000000"]
  let c47 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨74, by decide⟩ c46 c45
  let c48 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c47 c44
  let c49 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c48 c43
  let c50 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c49 c42
  let c51 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c50 c41
  let c52 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c51 c40
  let c53 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c52 c39
  let c54 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c53 c38
  let c55 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨75, by decide⟩ c54 c33
  let c56 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c55 c32
  let c57 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨73, by decide⟩ c56 c31
  let c58 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨61, by decide⟩ c57 c24
  let c59 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨76, by decide⟩ c58 c21
  let c60 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c59 c20
  let c61 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨77, by decide⟩ c60 c13
  let c62 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c61 c6
  let c63 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨66, by decide⟩ c62 c5
  let c64 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨85, by decide⟩ c63 c4
  let c65 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c64 c3
  let c66 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c65 c2
  let c67 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c66 c1
  let c68 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c67 c0
  c68
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00179.record006_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00179.record006_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00179.record006_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00179.record006_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00179.record006_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00179.record006_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00179.record006_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00179.record006_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00179.record006_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00179.record006
