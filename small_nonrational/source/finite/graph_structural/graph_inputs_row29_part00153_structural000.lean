module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow29Part00153Data
public import GraphInputsRow29Part00153Frames
public import GraphInputsRow29Part00153Leaves
public import GraphInputsRow29Part00153Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00153.record006
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00153.record006
def vertexColumn : Fields := ⟨10, hexnat% "ae178ad1742f07ccc9725aa5a56a3a4e87aa99a6599568d9361d8ce2b86e1783ecc6b1aa699965598e5392e6a5696958d5352d4cd2b49d1743dc8ea368f1394d538cd3392d4b32e2b4acab86d1b16c3ba1d8731e2749ca785d1715c3723c4f0bc1faa23855134a8a8a8a8aa5192629951a26191654545455a0d4382c8b12d0721c47"⟩
def kindColumn : Fields := ⟨3, hexnat% "4da6db6da6d249a6d36db4924db6da6db4da6da6d249a4d349349a4d26c9249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨28, by decide⟩, ⟨29, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨41, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨52, by decide⟩, ⟨56, by decide⟩, ⟨59, by decide⟩, ⟨64, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨81, by decide⟩, ⟨84, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨92, by decide⟩, ⟨100, by decide⟩, ⟨103, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1001d00e810103da6d30000000", hexnat% "20000000000008000000000", hexnat% "80100000000000000000000000", hexnat% "200000800000000000000", hexnat% "1000010000080000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1001d009810113d26d90000000", hexnat% "20000000000008000000000", hexnat% "80100000000000000000000000", hexnat% "200000800000020000000", hexnat% "6000000080000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1011d0098109135a6d90000000", hexnat% "6000000000000000000", hexnat% "80000000000000000000000000", 141287781040128, hexnat% "20200000000000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1001d008810113daed30000000", hexnat% "20200000000000000000000", hexnat% "80000004000000000000000000", hexnat% "100000000000000080000000", hexnat% "3000800000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1001d008810113d06d00000000", hexnat% "20000000000008000000000", hexnat% "80000004000000000000000000", hexnat% "200000800000030000000", hexnat% "3000000020000000000", hexnat% "100000000000080080000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨52, by decide⟩ c5 c2
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c6 c1
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c7 c0
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8012500e800112daeda0000000", hexnat% "10000000010000000000000000", hexnat% "1000001000000000000", hexnat% "18000000000000000000000", hexnat% "200000800000010000000"]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8013520e800113daedb0000000", hexnat% "1000800000000000000", hexnat% "10000000010000000000000000", hexnat% "8000000000000000000000"]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8013520e800112daad80000000", hexnat% "10000000010000000000000000", hexnat% "1000001000000000000", hexnat% "8000000000004000000000", 576460753108729856]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c11 c10
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8012500e800013caedb0000000", hexnat% "1000800000000000000", hexnat% "18000000000000000000000", hexnat% "10000000010000000000000000", hexnat% "200000100100000000000"]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8012500e800012caa980000000", hexnat% "1000001000000000000", hexnat% "10008000000000000000000000", hexnat% "200000800000030000000", hexnat% "10100100400000000", hexnat% "10000000000004000000000"]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c14 c13
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨89, by decide⟩ c15 c12
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c16 c9
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8002020c810102d88c20000000", hexnat% "18000000000004000000000", hexnat% "3000800020000000000", hexnat% "10005000000000000100000000", 281614831583232, hexnat% "100000000010000000000000"]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8010500e800013daedb0000000", hexnat% "10000000010000000000000000", hexnat% "1000800000000000000", hexnat% "18000000000000000000000", hexnat% "20200000100000000000000"]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "9013d2088101105aeda0000000", hexnat% "6000002000000000000", 422212733501440, hexnat% "1000800000000000000"]
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8013d208800913daedb0000000", hexnat% "10000000010000000000000000", hexnat% "3000000000000000000", hexnat% "4000000000000000000"]
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "80135208800910daedb0000000", hexnat% "10000000010000000000000000", hexnat% "1000001000000000000", hexnat% "6000002000000000000", hexnat% "8000000000000000000000"]
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c22 c21
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "9011d208810013daedb0000000", hexnat% "20000000100000000000000", hexnat% "6000000000000000000", hexnat% "1000800000000000000"]
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "90105208810113daadb0000000", hexnat% "6000000000000000000", hexnat% "18000000000004000000000", hexnat% "1000800000000000000", hexnat% "20000000000000000000000"]
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨100, by decide⟩ c25 c24
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "90105208810010da2d80000000", hexnat% "6000002000000000000", hexnat% "1000001000000000000", hexnat% "18000000000004000000000", hexnat% "20000000100008000000000", 576460753108729856]
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c27 c26
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨81, by decide⟩ c28 c23
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c29 c20
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c30 c19
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "9010500e810103da0d30000000", hexnat% "18000000000004000000000", 687194767360, hexnat% "1000810000080000000", hexnat% "20200000000000000000000"]
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1010500f8109135a6d90000000", hexnat% "18000000000000000000000", hexnat% "80000000000000000000000000", 141287781040128, hexnat% "20200000000000000000000"]
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "9010500c810103daadb0000000", hexnat% "18000000000004000000000", hexnat% "1000810000000000000", hexnat% "20200000000000000000000", hexnat% "2000000000000000000"]
  let c35 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1011d208810902d8edb0000000", hexnat% "20000000000000000000000", hexnat% "80000004000000000000000000", hexnat% "1000011020000000000", hexnat% "2000000000000000000"]
  let c36 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1010500f810913da0db0000000", hexnat% "80000000000000000000000000", 962072674304, hexnat% "30200000000000000000000", hexnat% "8000000000000000000000"]
  let c37 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "9010500c810112d80da0000000", hexnat% "18000000000004000000000", hexnat% "20000000000008000000000", 281612684099584, hexnat% "3000800020000000000", hexnat% "200000000000000000000"]
  let c38 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨52, by decide⟩ c37 c36
  let c39 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c38 c35
  let c40 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c39 c34
  let c41 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c40 c33
  let c42 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c41 c32
  let c43 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1012d2098109115a8db0000000", hexnat% "80000004000000000000000000", 140874927308800, hexnat% "2000002000000000000", hexnat% "10000000000004000000000"]
  let c44 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1010d0010109111a0990000000", hexnat% "6000002000000000000", hexnat% "30200000000000400000000", hexnat% "80000008800000400000000000", 141425219993600, 274877906944]
  let c45 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c44 c43
  let c46 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1010d0010108111a6990000000", hexnat% "6000002000000000000", 141287781040128, hexnat% "30200000000000400000000", hexnat% "80000008800000400000000000", 72057594037927936]
  let c47 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8012020c810110588ca0000000", hexnat% "18000000000004000000000", hexnat% "3000800020000000000", hexnat% "10005000000000000100000000", 422350172454912, 562949953421312]
  let c48 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "100007010913da08b0000000", hexnat% "80000008800000000000000000", 979252543488, hexnat% "30200000000000000000000", hexnat% "1000d000000000000100000000"]
  let c49 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "13820001011218edb0000000", hexnat% "10005000000000000000000000", 424411488321536, hexnat% "3000800000000000000", hexnat% "8000000c800000400000000000"]
  let c50 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1000010101131a4880000000", hexnat% "20000000000008400000000", hexnat% "1000d000000000000100000000", hexnat% "8000000c800000400000000000", hexnat% "2000800000000000000", hexnat% "10200000000000000000000", 140875732615168]
  let c51 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c50 c49
  let c52 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c51 c48
  let c53 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c52 c47
  let c54 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c53 c46
  let c55 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨52, by decide⟩ c54 c45
  let c56 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨64, by decide⟩ c55 c42
  let c57 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨92, by decide⟩ c56 c31
  let c58 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c57 c18
  let c59 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c58 c17
  let c60 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c59 c8
  c60
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00153.record006_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00153.record006_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00153.record006_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00153.record006_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00153.record006_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00153.record006_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00153.record006_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00153.record006_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00153.record006_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00153.record006
