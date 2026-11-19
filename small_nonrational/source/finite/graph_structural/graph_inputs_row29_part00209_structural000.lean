module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow29Part00209Data
public import GraphInputsRow29Part00209Frames
public import GraphInputsRow29Part00209Leaves
public import GraphInputsRow29Part00209Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00209.record003
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00209.record003
def vertexColumn : Fields := ⟨10, hexnat% "334731ac5b19c5723c4f332729aa5a99a56a3a4e9c6c9aa669966c5996959568d9366394e33a2e4b8ae1ba1e4789e1783e8e5c5a95a559595955558d5353362d1b61d2743d70ea368d6364e5354e334cccb8ac6b86c9b0ee8761e4751cc789d2729c6785d1725c570de0f23c4f0bc1f691542b05c689522a85a2a459894a5854552344d0b41d88ca384c5322c4b0ac1b"⟩
def kindColumn : Fields := ⟨3, hexnat% "da6d36da6d36db4db69b6db69b6d36d26d24d24926936926924936db4d34da6d2489249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨32, by decide⟩, ⟨35, by decide⟩, ⟨37, by decide⟩, ⟨39, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨77, by decide⟩, ⟨82, by decide⟩, ⟨90, by decide⟩, ⟨95, by decide⟩, ⟨101, by decide⟩, ⟨104, by decide⟩, ⟨109, by decide⟩, ⟨112, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1212084042138726000a93c000000", hexnat% "38000000000000000", hexnat% "2000400000000000000", 5242471441235968, 1477743627730944]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "10100840423214677e0a93c000000", hexnat% "2000000000100000000000000000", hexnat% "20000000000000000000000000", hexnat% "81000000000000000", hexnat% "2a000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1210084042130020080a93c000000", hexnat% "20000000000060000000000000", 2075877953241088, hexnat% "2000400000000000000", hexnat% "81010000000000000", hexnat% "3e000000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨69, by decide⟩ c3 c0
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1212084042319962000a93c000000", hexnat% "26000000000000000", hexnat% "200040000000000000", 5242471441235968, 1477743627730944]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2020840422314677e0a93c000000", hexnat% "10000000001000000000000000000", hexnat% "100000000000000000000000000", hexnat% "81000000000000000", hexnat% "2a000000000000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1202084042310002200a93c000000", hexnat% "100000000000600000000000000", 1653665488175104, hexnat% "200040000000000000", hexnat% "81010000000000000", hexnat% "3e000000000000000"]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c7 c6
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨73, by decide⟩ c8 c5
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8404222bf017e0003c000000", 725849473024, hexnat% "1100220000000000000", hexnat% "12120000000000000000000000000", 18014398509481984, 288230376151711744]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "840422095617e0a008000000", hexnat% "12120000000000000000000000000", hexnat% "1100020000000000000", hexnat% "2a000000034000000", hexnat% "200040000900000000"]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "121208404203bf002800904000000", 22553182508941312, hexnat% "1000220000000000000", 1477744567255040, hexnat% "200040000a000000000"]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2020840420385072a0a93c000000", hexnat% "100000000000600000000000000", hexnat% "10000000003000000000000000000", 1477743627730944, hexnat% "3a000000000000000"]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "840420085457e0a93c000000", hexnat% "3a000000000000000", hexnat% "20000000000020000000000000", hexnat% "2000000000300000000000000000", hexnat% "100000000000200000000000000", hexnat% "10000000003000000000000000000"]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8404230bf412a0a108000000", hexnat% "12120000000000000000000000000", hexnat% "100220000000000000", 1477744500146176, hexnat% "200040000800000000"]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "84042203f007e0013c000000", hexnat% "80010008800000000", hexnat% "100000000000600002000000000", hexnat% "2000000000300000000000000000", hexnat% "10000000001000000000000000000", hexnat% "20000000000060000000000000"]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "84042003f047e0013c000000", hexnat% "80010008800000000", hexnat% "20000000000020000000000000", hexnat% "2000000000300000000000000000", hexnat% "100000000000600002000000000", hexnat% "10000000003000000000000000000"]
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "10084042229d61360a908000000", hexnat% "10000000001000000000000000000", hexnat% "2000000000100000000000000000", hexnat% "20000000000060000000000000", 1266637462306816, hexnat% "22000000030000000"]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "84042009d412608900000000", hexnat% "1100220000000000000", hexnat% "12120000000000000000000000000", 1548112439017472, hexnat% "22000000038000000", hexnat% "2000000002000000000", hexnat% "200040000000000000"]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c19 c18
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c20 c17
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c21 c16
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨64, by decide⟩ c22 c15
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c23 c14
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c24 c13
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨62, by decide⟩ c25 c12
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c26 c11
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c27 c10
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨77, by decide⟩ c28 c9
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨82, by decide⟩ c29 c4
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨90, by decide⟩ c30 c9
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨95, by decide⟩ c31 c4
  c32
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00209.record003_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00209.record003_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00209.record003_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00209.record003_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00209.record003_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00209.record003_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00209.record003_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00209.record003_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00209.record003_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00209.record003
