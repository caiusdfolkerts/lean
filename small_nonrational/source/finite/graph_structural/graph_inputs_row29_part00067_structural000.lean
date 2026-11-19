module
prelude
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow29Part00067Data
public import GraphInputsRow29Part00067Frames
public import GraphInputsRow29Part00067Leaves
public import GraphInputsRow29Part00067Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00067.record007
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00067.record007
def vertexColumn : Fields := ⟨10, hexnat% "338e93347332c6b31c8f13ce88f2ca9aa3aa3a1eb86c9aa669a5635a362db0e638ce8b92e2ba1e0fb313c5c96a4e94e4797172569715356354d4b56354d3352d2b51d0f72368ce334e332cc7362ccb4acab1af0761e2749ca785c970dd0f23c2f172321683a31a161584e079a14a4590e585314554344d074c328c530cc4b0ac1b21c4705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "db6db6db6da4db6926da6da4db4d24d34db49269349249a4934da492489249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2, 3]
def candidates : List (Fin raw.n) := [⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩, ⟨95, by decide⟩, ⟨96, by decide⟩, ⟨97, by decide⟩, ⟨98, by decide⟩, ⟨99, by decide⟩, ⟨100, by decide⟩, ⟨101, by decide⟩, ⟨102, by decide⟩, ⟨103, by decide⟩, ⟨104, by decide⟩, ⟨105, by decide⟩, ⟨106, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .size 3
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .size 2
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨76, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7ffffffeff77fffffffc0000000", hexnat% "10000000000000000000", hexnat% "88000000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨65, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7ffffffffc57ffdffefc0000000", hexnat% "300000000000000000", 9223934986808197120, hexnat% "a0000001000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7ffff9fef757ff9efefc0000000", hexnat% "6010000000000000000000", hexnat% "88000000000000000", hexnat% "820000000000000000", 1706510765785088]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨80, by decide⟩ c7 c6
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7ffff8ee7f57fffffefc0000000", hexnat% "88000000000000000", hexnat% "6100000000000000000000", hexnat% "1008020000001000000000", hexnat% "10000000000000000000"]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7fff7aee74fffffeff7c0000000", hexnat% "100800000100000000000", hexnat% "300000000000000000", hexnat% "80018000000000000000000", hexnat% "5000000000000800000000"]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7fff7deff4ffffbefffc0000000", hexnat% "300000000000000000", hexnat% "2100000000000000000000", hexnat% "80000000004000000000000", hexnat% "800000100000000000"]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7fff7deff4ffff9ebffc0000000", hexnat% "80000100004000000000000", hexnat% "a00000040000000000", hexnat% "2000000002000000000000", hexnat% "100000000100000000000"]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7ffef9fe7f57ffdfff7c0000000", hexnat% "2000008002000000000000", hexnat% "a0000000000000000", hexnat% "100018000000000000000000", hexnat% "4000000000000800000000"]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7ffe7beef4ffffffff7c0000000", hexnat% "300000000000000000", hexnat% "100800000000000000000", hexnat% "180010000000000000000000", hexnat% "4000000000000800000000"]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨65, by decide⟩ c1 c0
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7ffffffffedfffbffffc0000000", hexnat% "20000000000000000", hexnat% "100004000000000000"]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨69, by decide⟩ c16 c15
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7ffffffffc5fff9ffffc0000000", 1688849860263936, hexnat% "a0000000000000000", hexnat% "300000000000000000"]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c18 c17
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7fff7ffe7f57ff9fff7c0000000", hexnat% "18000000000800000000", 9223934986808197120, hexnat% "a0000000000000000", hexnat% "80000000004000000000000"]
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨92, by decide⟩ c20 c19
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7ffef9fe7f57ffffff7c0000000", hexnat% "88000000000000000", hexnat% "100018000000000000000000", hexnat% "20000000000000000", hexnat% "6000000000000800000000"]
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7ffe79fe7457ffffff7c0000000", hexnat% "88000000000000000", hexnat% "300000000000000000", hexnat% "820000000000000000", hexnat% "180018000000000000000000", hexnat% "6000000000000800000000"]
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c23 c22
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨80, by decide⟩ c24 c21
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c25 c14
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c26 c13
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨84, by decide⟩ c27 c12
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c28 c11
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c29 c10
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c30 c9
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c31 c8
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7ffffbeff77f5ffef7740000000", hexnat% "4000000000000800000000", hexnat% "80a00008080000000", hexnat% "100800000100000000000"]
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7ffe79eeff775f8ad7340000000", hexnat% "180000000001400000000000", hexnat% "6010000000000c00000000", hexnat% "88200008000000000", 1708641069563904, hexnat% "100000800000080000000"]
  let c35 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c34 c33
  let c36 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7ffe78fe7f57afdff73c0000000", hexnat% "2000008002000400000000", hexnat% "a0000008000000000", 360287970189639680, hexnat% "180018000000000000000000", hexnat% "5000000000000800000000"]
  let c37 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7ffe78fe7cf7efc37ffc0000000", hexnat% "2000008002800000000000", hexnat% "300000080000000000", hexnat% "5018000000000000000000", 72057594037927936, hexnat% "180000000001400000000000"]
  let c38 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7ffffaee755f0bfef77c0000000", hexnat% "5018000000000800000000", hexnat% "a0800008000000000", hexnat% "100800200100000000000", hexnat% "200140000000000000", 288230376151711744]
  let c39 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c1 c0
  let c40 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c1 c39
  let c41 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c1 c40
  let c42 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7fffffffffffff1ffffc0000000", 1688849860263936, 2251799813685248]
  let c43 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨68, by decide⟩ c42 c41
  let c44 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7ffffffffef7ff1ff7fc0000000", hexnat% "100004000000000000", 9223934986808197120, 2252349569499136]
  let c45 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨67, by decide⟩ c44 c43
  let c46 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c1 c0
  let c47 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c1 c46
  let c48 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c1 c47
  let c49 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7fffffffffffff6fff7c0000000", 2251799813685248, 281509336449024]
  let c50 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨76, by decide⟩ c49 c48
  let c51 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7ffffffefff7ff5ff7fc0000000", 9223934986808197120, 2252349569499136, hexnat% "10000000000000000000"]
  let c52 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨67, by decide⟩ c51 c50
  let c53 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7fff7ffeff77ffcbff7c0000000", hexnat% "88000000000000000", hexnat% "10000000000800000000", hexnat% "80000000001400000000000", 562949953421312]
  let c54 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨68, by decide⟩ c53 c52
  let c55 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨92, by decide⟩ c54 c45
  let c56 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7ffe79fefe775f8bf77c0000000", hexnat% "80000100004400000000000", hexnat% "6010000000000800000000", hexnat% "100000000001000000000000", 9223934986808197120, hexnat% "80a00008000000000"]
  let c57 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨80, by decide⟩ c56 c55
  let c58 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c1 c46
  let c59 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨68, by decide⟩ c1 c58
  let c60 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨80, by decide⟩ c1 c59
  let c61 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7fffffeffeffdf7ff7fc0000000", hexnat% "100000000000000000", 2252349569499136, hexnat% "100000200000000000000"]
  let c62 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨67, by decide⟩ c61 c60
  let c63 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7ffffbefff7fdf7ff7fc0000000", 2252349569499136, hexnat% "4100000000000000000000", hexnat% "80200000000000000"]
  let c64 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c1 c39
  let c65 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨68, by decide⟩ c1 c64
  let c66 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7ffffffffeffff7ff7fc0000000", hexnat% "100000000000000000", 2252349569499136]
  let c67 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨67, by decide⟩ c66 c65
  let c68 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7fff7ffffe7fff7ff7fc0000000", 2252349569499136, hexnat% "80000000000000000", hexnat% "80000100000000000000000"]
  let c69 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨92, by decide⟩ c68 c67
  let c70 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7ffe7ffffe7fdf7ff7fc0000000", 2252349569499136, hexnat% "80000100000000000000000", hexnat% "100000000000000000000000", hexnat% "80200000000000000"]
  let c71 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨80, by decide⟩ c70 c69
  let c72 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c71 c63
  let c73 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨76, by decide⟩ c72 c62
  let c74 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7ffe79eefe77dfeadf3c0000000", hexnat% "180000000001400000000000", hexnat% "88200000000000000", hexnat% "100000020000000000", hexnat% "100000000100000000000", hexnat% "6010000000000c00000000"]
  let c75 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c74 c73
  let c76 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7ffffefe7f57bf7f76fc0000000", hexnat% "1018000000000000000000", 2261145662521344, hexnat% "88400000000000000", hexnat% "20000001000000000"]
  let c77 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7ffff8fe7f571b7ff6fc0000000", hexnat% "6010000000000000000000", 1026820715040473088, hexnat% "20008009000000000", hexnat% "88000000000000000", hexnat% "1008000000000000000000"]
  let c78 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨80, by decide⟩ c77 c76
  let c79 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7fff7deff4fffffedffc0000000", hexnat% "2100000000000000000000", hexnat% "80000100000020000000000", hexnat% "800000100000000000", hexnat% "200000000000000000"]
  let c80 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7fffffeff4ffbbdedffc0000000", 306244774661193728, 582741162721280, hexnat% "100800000000000000000", hexnat% "300000000000000000"]
  let c81 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7ffe7feff4ffffdedffc0000000", hexnat% "180000000000000000000000", 582741162721280, hexnat% "100800000000000000000", hexnat% "300000000000000000"]
  let c82 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7ffff8eff5ffffdefffc0000000", hexnat% "5000000000000000000000", 580542139465728, hexnat% "a00000000000000000", hexnat% "2100000000000000000000"]
  let c83 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7ffef8ef74ffffcedffc0000000", hexnat% "101008000001000000000000", hexnat% "2000000002000000000000", hexnat% "300000020000000000", hexnat% "100800000100000000000", hexnat% "4000000000000000000000"]
  let c84 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨91, by decide⟩ c83 c82
  let c85 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c84 c81
  let c86 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨76, by decide⟩ c85 c80
  let c87 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c86 c79
  let c88 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c1 c0
  let c89 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c1 c88
  let c90 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c1 c89
  let c91 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨80, by decide⟩ c1 c90
  let c92 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7fffffeffdf79fff7ffc0000000", hexnat% "200000080000000000", hexnat% "100000200000000000000", 9511602413006487552]
  let c93 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c92 c91
  let c94 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c1 c88
  let c95 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7ffffffffff7ffefff7c0000000", 9223372036854775808, 281509336449024]
  let c96 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨92, by decide⟩ c95 c94
  let c97 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7ffefffffdf7bfff7ffc0000000", hexnat% "200000080000000000", 9511602413006487552, hexnat% "100000000000000000000000"]
  let c98 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c97 c96
  let c99 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7ffef9fffff79befff7c0000000", hexnat% "100000000001000000000000", hexnat% "6000000000000800000000", 450359962737049600, 9223372036854775808]
  let c100 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨80, by decide⟩ c99 c98
  let c101 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨76, by decide⟩ c100 c93
  let c102 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7ffe79eefff79bceff3c0000000", hexnat% "180000000001000000000000", 450359962737049600, hexnat% "100000000100000000000", hexnat% "6010000000000c00000000", 9223934986808197120]
  let c103 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c102 c101
  let c104 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7ffff9eef4f71bff5f7c0000000", 9655717601082343424, hexnat% "6010000000000800000000", hexnat% "3000000a0000000000", 594475150812905472, hexnat% "100800000000000000000"]
  let c105 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7ffff8fffdf7ffdfff1c0000000", hexnat% "200000000000000000", hexnat% "2000008002000400000000", hexnat% "5000000000000a00000000"]
  let c106 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7fffffeff5ff9b7e7ffc0000000", hexnat% "800008080000000000", 450359962737049600, hexnat% "100000000100000000000", hexnat% "200000000000000000"]
  let c107 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7ffff8effd779bdeff5c0000000", hexnat% "200040000000000000", hexnat% "88600000000000000", hexnat% "5000000000000a00000000", 580542139465728, hexnat% "2100000000000000000000"]
  let c108 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c107 c106
  let c109 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c108 c105
  let c110 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7fffffefff771f1efffc0000000", 3377699720527872, 9223934986808197120, hexnat% "100000a00100000000000", hexnat% "80400000000000000"]
  let c111 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7fffffeff7771bff7ffc0000000", hexnat% "800000080000000000", 1026820715040473088, hexnat% "88000000000000000", hexnat% "100000000000000000000"]
  let c112 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7fffffeff6771b5e5ffc0000000", hexnat% "800008080000000000", 582741162721280, hexnat% "100040000000000000", hexnat% "88600000000000000", hexnat% "100000800000000000000"]
  let c113 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c112 c111
  let c114 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨69, by decide⟩ c113 c110
  let c115 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7ffef8ef7c771b8edf9c0000000", hexnat% "101008000001000200000000", 1026820715040473088, hexnat% "88000000400000000", hexnat% "300000020000000000", hexnat% "6100000000000000000000", 1706442046308352]
  let c116 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c115 c114
  let c117 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨76, by decide⟩ c116 c114
  let c118 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨91, by decide⟩ c117 c109
  let c119 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c118 c104
  let c120 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨65, by decide⟩ c119 c103
  let c121 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c120 c87
  let c122 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c121 c78
  let c123 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c122 c75
  let c124 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c123 c57
  let c125 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c124 c38
  let c126 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c125 c37
  let c127 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c126 c36
  let c128 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c127 c35
  let c129 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c128 c32
  c129
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00067.record007_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00067.record007_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00067.record007_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00067.record007_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00067.record007_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00067.record007_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00067.record007_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00067.record007_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00067.record007_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00067.record007

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00067.record008
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "3383d1ac3b07ce8b3272b2a6ab1a8e93a698d68d8b6638ce4b8ae0fba1cc4f1727296a4e9c66394e479694e5356352d475634cd4b4ad1b78370f23a8da3c4e5334e334ccb3c2d8b52ccb8ad2b2ae1b46c3b61e2749ca785c970dd0f23c2f1703c168c61584e07b21686314a4590e4c5294550d44d0b41dc0d8330e1314d0b12c1b21c4705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "db69b6db6da6da6d24da4da49249269249269249b49269a493692492249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00067.record008 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00067.record008 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00067.record008.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00067.record008.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00067.record008.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 36), (facetIndex 55), (facetIndex 69), (facetIndex 71), (facetIndex 92)]))
 (.leaf ([(facetIndex 63), (facetIndex 68), (facetIndex 72), (facetIndex 74), (facetIndex 102)])))
 (.branch 3
 (.leaf ([(facetIndex 37), (facetIndex 43), (facetIndex 44), (facetIndex 56), (facetIndex 57)]))
 (.leaf ([(facetIndex 70), (facetIndex 75), (facetIndex 76), (facetIndex 83)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 49), (facetIndex 50), (facetIndex 51), (facetIndex 61), (facetIndex 62)]))
 (.leaf ([(facetIndex 65), (facetIndex 73), (facetIndex 79), (facetIndex 80), (facetIndex 84)])))
 (.branch 7
 (.leaf ([(facetIndex 33), (facetIndex 48), (facetIndex 64), (facetIndex 66), (facetIndex 88)]))
 (.branch 8
 (.leaf ([(facetIndex 32), (facetIndex 35), (facetIndex 38), (facetIndex 42), (facetIndex 46), (facetIndex 54), (facetIndex 58), (facetIndex 60), (facetIndex 85)]))
 (.leaf ([(facetIndex 34), (facetIndex 41)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "10000000000000600753005500331510301065614470722070044460702278007207867z20;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 9
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 78), (facetIndex 82)]))
 (.leaf ([(facetIndex 103), (facetIndex 105)])))
 (.branch 3
 (.leaf ([(facetIndex 47), (facetIndex 53), (facetIndex 77)]))
 (.branch 4
 (.leaf ([(facetIndex 94), (facetIndex 95), (facetIndex 96)]))
 (.leaf ([(facetIndex 98), (facetIndex 100), (facetIndex 106)])))))
 (.branch 7
 (.branch 6
 (.leaf ([(facetIndex 45), (facetIndex 67), (facetIndex 81)]))
 (.leaf ([(facetIndex 86), (facetIndex 89), (facetIndex 99)])))
 (.branch 8
 (.leaf ([(facetIndex 39), (facetIndex 40), (facetIndex 52), (facetIndex 59), (facetIndex 97)]))
 (.branch 9
 (.leaf ([(facetIndex 87), (facetIndex 90), (facetIndex 91), (facetIndex 101)]))
 (.leaf ([(facetIndex 93), (facetIndex 104)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "41910846473339088608600005000200000000050000000700000270000205000077z27;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 10
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped2_0000 : List Nat := [0, 1, 2, 3]
def grouped2_0002 : List Nat := [4]
def grouped2_0003 : List Nat := [4, 5]
def grouped2_0004 : List Nat := [4, 5, 6, 7, 8]
def grouped2_0005 : List Nat := [5]
def grouped2_0006 : List Nat := [6]
def grouped2_0007 : List Nat := [6, 7, 8]
def grouped2_0008 : List Nat := [7]
def grouped2_0009 : List Nat := [7, 8]
def grouped2_0010 : List Nat := [8]
def grouped3_0011 : List Nat := [0]
def grouped3_0012 : List Nat := [0, 1]
def grouped3_0013 : List Nat := [0, 1, 2, 3, 4]
def grouped3_0015 : List Nat := [1]
def grouped3_0016 : List Nat := [2]
def grouped3_0017 : List Nat := [2, 3, 4]
def grouped3_0018 : List Nat := [3]
def grouped3_0019 : List Nat := [3, 4]
def grouped3_0020 : List Nat := [4]
def grouped3_0021 : List Nat := [5]
def grouped3_0022 : List Nat := [5, 6]
def grouped3_0023 : List Nat := [5, 6, 7, 8, 9]
def grouped3_0024 : List Nat := [6]
def grouped3_0025 : List Nat := [7]
def grouped3_0026 : List Nat := [7, 8, 9]
def grouped3_0027 : List Nat := [8]
def grouped3_0028 : List Nat := [8, 9]
def grouped3_0029 : List Nat := [9]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00067.record008 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00067.record008_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00067.record008" "{\"atoms\":[{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":103},{\"tag\":\"facet\",\"index\":104},{\"tag\":\"facet\",\"index\":105},{\"tag\":\"facet\",\"index\":106},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group\",\"kind\":2,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0003\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group\",\"kind\":3,\"index\":9},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0012\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0019\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0022\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0028\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0028\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0026\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0026\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0023\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0023\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00067.record008" 90

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00067.record008" "{\"ridges\":[[10,385],[22,560],[23,416],[24,800],[34,266],[38,164],[40,550],[41,385],[41,386],[46,266],[50,386],[54,560],[58,386],[58,416],[59,674],[60,800],[61,385],[62,385],[70,560],[73,416],[76,560],[79,416],[80,800],[83,560],[84,416],[84,800],[87,294],[90,178],[91,550],[93,294],[97,170],[101,674],[104,396]],\"owners\":[[34,266,[94,96,97,98,99],[6,43,46,49,50,51,87,89]],[46,266,[89,96,99],[6,34,43,49,50,51,87,94,97,98]],[10,385,[23,67,73,79,81,84],[41,50,61,62]],[41,385,[23,79,81,84],[10,50,61,62,67,73]],[61,385,[23,67,73,79,84],[10,41,50,62,81]],[62,385,[23,67,73,79,81],[10,41,50,61,84]],[41,386,[97,99,101],[10,50,58,61,62,89,93]],[50,386,[93,101],[10,41,58,61,62,89,97,99]],[58,386,[89,99],[10,41,50,61,62,93,97,101]],[38,164,[103,104,105],[17,64,69,72,73,86,90,93]],[22,560,[91,95,100,106],[54,70,76,83]],[54,560,[106],[22,70,76,83,91,95,100]],[70,560,[95,100,106],[22,54,76,83,91]],[76,560,[91,100],[22,54,70,83,95,106]],[83,560,[91,95],[22,54,70,76,100,106]],[23,416,[93,97,101,104],[58,73,79,84]],[58,416,[104],[23,73,79,84,93,97,101]],[73,416,[97,101],[23,58,79,84,93,104]],[79,416,[93,101],[23,58,73,84,97,104]],[84,416,[93,97,104],[23,58,73,79,101]],[24,800,[98,100,101,106],[60,80,83,84]],[60,800,[106],[24,80,83,84,98,100,101]],[80,800,[100,101],[24,60,83,84,98,106]],[84,800,[98,100,106],[24,60,80,83,101]],[87,294,[39,93],[]],[93,294,[39,87],[]],[40,550,[91],[]],[91,550,[40],[]],[97,170,[45,86],[]],[90,178,[52],[]],[59,674,[101],[]],[101,674,[59],[]],[104,396,[67,89],[]]],\"edges\":[[38,[22,24,40,47,54,59,60,70,76,80,83,84,91,95,98,100,101,106]],[42,[10,23,41,50,58,61,62,67,73,79,81,84,89,93,97,99,101,104]]],\"groupings\":[2,3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00067.record008" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00067.record008\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-10,-5],[-10,-8],[-11,-5],[-11,-8],[-12,-6],[-13,-10],[-13,-11],[-17,-12],[-18,-7],[-20,-7],[-20,-12],[-21,-5],[-21,-8],[-21,-13],[-24,-5],[-24,-8],[-24,-12],[-24,-13],[-26,-6],[-26,-12],[-26,-17],[-27,-7],[-27,-12],[-30,-6],[-30,-7],[-30,-17],[-30,-28],[-30,-29],[-36,-6],[-36,-17],[-36,-28],[-36,-29],[-39,-10],[-39,-11],[-39,-21],[-39,-24],[-42,-30],[-42,-36],[-43,-6],[-43,-17],[-43,-28],[-43,-29],[-43,-42],[-46,-5],[-46,-8],[-46,-12],[-46,-13],[-46,-39],[-50,-5],[-50,-6],[-50,-8],[-50,-9],[-50,-13],[-50,-15],[-50,-17],[-50,-22],[-50,-25],[-50,-28],[-50,-29],[-50,-39],[-50,-42],[-52,-6],[-52,-17],[-52,-18],[-52,-28],[-52,-29],[-52,-42],[-7,47,49,50,51,52],[-15,43,49,52],[-1,3,30,32,34,36,38],[-12,3,34,36,38],[-26,3,30,32,34,38],[-27,3,30,32,34,36],[-12,50,52,54],[-19,46,54],[-23,43,52],[-9,55,56,57],[-2,45,48,53,58],[-22,58],[-31,48,53,58],[-33,45,53],[-37,45,48],[-3,46,50,54,56],[-23,56],[-32,50,54],[-34,46,54],[-38,46,50,56],[-4,51,53,54,58],[-25,58],[-35,53,54],[-38,51,53,58],[-41,10,46],[-46,10,41],[-11,45],[-45,11],[-50,14,40],[-44,21],[-24,54],[-54,24],[-56,30,43],[-59,18,19,20,26,27],[-60,6,17,28,29,42],[-61,5,8,9,13,15,22,23,25,39],[-62,7,12],[-63,59],[-64,61,62],[-65,61],[-65,62],[-66,60,65],[-67,60],[-66,64],[-68,63,67],[-68,66],[-69,68],[69],[-55,70],[-57,70],[-16,71],[-47,72],[-48,72],[-49,72],[-51,73],[-53,73],[-58,73],[-14,74],[-30,74],[-40,75],[-43,75],[-52,75],[-76,10,11,21,24,50],[-10,76],[-11,76],[-21,76],[-24,76],[-77,41,44,45,54],[-41,77],[-45,77],[-54,77],[-78,46,56],[-46,78],[-56,78],[-70,79],[-73,80],[-72,80],[-80,81],[-71,81],[-81,82],[-79,82],[-75,83],[-74,83],[-84,77,78],[-78,84],[-77,84],[-85,78],[-77,-78,85],[-84,86],[-87,76,85],[-85,87],[-76,-84,87],[-87,88],[-83,-86,88],[-83,-87,89],[-89,90],[-82,-88,90],[-90],[2,4,11,16,22,24,25,31,33,35,37,38,45,48,51,53,54,58],[1,3,12,19,23,26,27,30,32,34,36,38,43,46,50,52,54,56]],\"atoms\":[{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":103},{\"tag\":\"facet\",\"index\":104},{\"tag\":\"facet\",\"index\":105},{\"tag\":\"facet\",\"index\":106},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group\",\"index\":8,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group\",\"index\":9,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":39,\"b\":32},{\"tag\":\"incompatible\",\"a\":39,\"b\":35},{\"tag\":\"incompatible\",\"a\":40,\"b\":32},{\"tag\":\"incompatible\",\"a\":40,\"b\":35},{\"tag\":\"incompatible\",\"a\":41,\"b\":33},{\"tag\":\"incompatible\",\"a\":42,\"b\":39},{\"tag\":\"incompatible\",\"a\":42,\"b\":40},{\"tag\":\"incompatible\",\"a\":48,\"b\":41},{\"tag\":\"incompatible\",\"a\":49,\"b\":34},{\"tag\":\"incompatible\",\"a\":51,\"b\":34},{\"tag\":\"incompatible\",\"a\":51,\"b\":41},{\"tag\":\"incompatible\",\"a\":52,\"b\":32},{\"tag\":\"incompatible\",\"a\":52,\"b\":35},{\"tag\":\"incompatible\",\"a\":52,\"b\":42},{\"tag\":\"incompatible\",\"a\":59,\"b\":32},{\"tag\":\"incompatible\",\"a\":59,\"b\":35},{\"tag\":\"incompatible\",\"a\":59,\"b\":41},{\"tag\":\"incompatible\",\"a\":59,\"b\":42},{\"tag\":\"incompatible\",\"a\":61,\"b\":33},{\"tag\":\"incompatible\",\"a\":61,\"b\":41},{\"tag\":\"incompatible\",\"a\":61,\"b\":48},{\"tag\":\"incompatible\",\"a\":62,\"b\":34},{\"tag\":\"incompatible\",\"a\":62,\"b\":41},{\"tag\":\"incompatible\",\"a\":67,\"b\":33},{\"tag\":\"incompatible\",\"a\":67,\"b\":34},{\"tag\":\"incompatible\",\"a\":67,\"b\":48},{\"tag\":\"incompatible\",\"a\":67,\"b\":64},{\"tag\":\"incompatible\",\"a\":67,\"b\":66},{\"tag\":\"incompatible\",\"a\":81,\"b\":33},{\"tag\":\"incompatible\",\"a\":81,\"b\":48},{\"tag\":\"incompatible\",\"a\":81,\"b\":64},{\"tag\":\"incompatible\",\"a\":81,\"b\":66},{\"tag\":\"incompatible\",\"a\":85,\"b\":39},{\"tag\":\"incompatible\",\"a\":85,\"b\":40},{\"tag\":\"incompatible\",\"a\":85,\"b\":52},{\"tag\":\"incompatible\",\"a\":85,\"b\":59},{\"tag\":\"incompatible\",\"a\":88,\"b\":67},{\"tag\":\"incompatible\",\"a\":88,\"b\":81},{\"tag\":\"incompatible\",\"a\":89,\"b\":33},{\"tag\":\"incompatible\",\"a\":89,\"b\":48},{\"tag\":\"incompatible\",\"a\":89,\"b\":64},{\"tag\":\"incompatible\",\"a\":89,\"b\":66},{\"tag\":\"incompatible\",\"a\":89,\"b\":88},{\"tag\":\"incompatible\",\"a\":93,\"b\":32},{\"tag\":\"incompatible\",\"a\":93,\"b\":35},{\"tag\":\"incompatible\",\"a\":93,\"b\":41},{\"tag\":\"incompatible\",\"a\":93,\"b\":42},{\"tag\":\"incompatible\",\"a\":93,\"b\":85},{\"tag\":\"incompatible\",\"a\":97,\"b\":32},{\"tag\":\"incompatible\",\"a\":97,\"b\":33},{\"tag\":\"incompatible\",\"a\":97,\"b\":35},{\"tag\":\"incompatible\",\"a\":97,\"b\":38},{\"tag\":\"incompatible\",\"a\":97,\"b\":42},{\"tag\":\"incompatible\",\"a\":97,\"b\":46},{\"tag\":\"incompatible\",\"a\":97,\"b\":48},{\"tag\":\"incompatible\",\"a\":97,\"b\":54},{\"tag\":\"incompatible\",\"a\":97,\"b\":60},{\"tag\":\"incompatible\",\"a\":97,\"b\":64},{\"tag\":\"incompatible\",\"a\":97,\"b\":66},{\"tag\":\"incompatible\",\"a\":97,\"b\":85},{\"tag\":\"incompatible\",\"a\":97,\"b\":88},{\"tag\":\"incompatible\",\"a\":99,\"b\":33},{\"tag\":\"incompatible\",\"a\":99,\"b\":48},{\"tag\":\"incompatible\",\"a\":99,\"b\":49},{\"tag\":\"incompatible\",\"a\":99,\"b\":64},{\"tag\":\"incompatible\",\"a\":99,\"b\":66},{\"tag\":\"incompatible\",\"a\":99,\"b\":88},{\"tag\":\"mate\",\"ridge\":266,\"a\":34,\"owners\":[94,96,97,98,99]},{\"tag\":\"mate\",\"ridge\":266,\"a\":46,\"owners\":[89,96,99]},{\"tag\":\"mate\",\"ridge\":385,\"a\":10,\"owners\":[23,67,73,79,81,84]},{\"tag\":\"mate\",\"ridge\":385,\"a\":41,\"owners\":[23,79,81,84]},{\"tag\":\"mate\",\"ridge\":385,\"a\":61,\"owners\":[23,67,73,79,84]},{\"tag\":\"mate\",\"ridge\":385,\"a\":62,\"owners\":[23,67,73,79,81]},{\"tag\":\"mate\",\"ridge\":386,\"a\":41,\"owners\":[97,99,101]},{\"tag\":\"mate\",\"ridge\":386,\"a\":50,\"owners\":[93,101]},{\"tag\":\"mate\",\"ridge\":386,\"a\":58,\"owners\":[89,99]},{\"tag\":\"mate\",\"ridge\":164,\"a\":38,\"owners\":[103,104,105]},{\"tag\":\"mate\",\"ridge\":560,\"a\":22,\"owners\":[91,95,100,106]},{\"tag\":\"mate\",\"ridge\":560,\"a\":54,\"owners\":[106]},{\"tag\":\"mate\",\"ridge\":560,\"a\":70,\"owners\":[95,100,106]},{\"tag\":\"mate\",\"ridge\":560,\"a\":76,\"owners\":[91,100]},{\"tag\":\"mate\",\"ridge\":560,\"a\":83,\"owners\":[91,95]},{\"tag\":\"mate\",\"ridge\":416,\"a\":23,\"owners\":[93,97,101,104]},{\"tag\":\"mate\",\"ridge\":416,\"a\":58,\"owners\":[104]},{\"tag\":\"mate\",\"ridge\":416,\"a\":73,\"owners\":[97,101]},{\"tag\":\"mate\",\"ridge\":416,\"a\":79,\"owners\":[93,101]},{\"tag\":\"mate\",\"ridge\":416,\"a\":84,\"owners\":[93,97,104]},{\"tag\":\"mate\",\"ridge\":800,\"a\":24,\"owners\":[98,100,101,106]},{\"tag\":\"mate\",\"ridge\":800,\"a\":60,\"owners\":[106]},{\"tag\":\"mate\",\"ridge\":800,\"a\":80,\"owners\":[100,101]},{\"tag\":\"mate\",\"ridge\":800,\"a\":84,\"owners\":[98,100,106]},{\"tag\":\"mate\",\"ridge\":294,\"a\":87,\"owners\":[39,93]},{\"tag\":\"mate\",\"ridge\":294,\"a\":93,\"owners\":[39,87]},{\"tag\":\"mate\",\"ridge\":550,\"a\":40,\"owners\":[91]},{\"tag\":\"mate\",\"ridge\":550,\"a\":91,\"owners\":[40]},{\"tag\":\"mate\",\"ridge\":170,\"a\":97,\"owners\":[45,86]},{\"tag\":\"mate\",\"ridge\":178,\"a\":90,\"owners\":[52]},{\"tag\":\"mate\",\"ridge\":674,\"a\":59,\"owners\":[101]},{\"tag\":\"mate\",\"ridge\":674,\"a\":101,\"owners\":[59]},{\"tag\":\"mate\",\"ridge\":396,\"a\":104,\"owners\":[67,89]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[49,50,51,61,62],\"full_literals\":[-59,18,19,20,26,27]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[33,48,64,66,88],\"full_literals\":[-60,6,17,28,29,42]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[32,35,38,42,46,54,58,60,85],\"full_literals\":[-61,5,8,9,13,15,22,23,25,39]},{\"tag\":\"group_or\",\"kind\":2,\"index\":8,\"members\":[34,41],\"full_literals\":[-62,7,12]},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0003\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-63,59,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"grouped2_0009\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-64,61,62],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"grouped2_0009\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-65,61,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"grouped2_0009\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-65,false,62],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-66,60,65],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-67,60,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-66,false,64],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0004\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-68,63,67],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0004\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-68,false,66],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-69,false,68],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":103,\"full_literals\":[-55,70]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":105,\"full_literals\":[-57,70]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":47,\"full_literals\":[-16,71]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":94,\"full_literals\":[-47,72]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":95,\"full_literals\":[-48,72]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":96,\"full_literals\":[-49,72]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":98,\"full_literals\":[-51,73]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":100,\"full_literals\":[-53,73]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":106,\"full_literals\":[-58,73]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":45,\"full_literals\":[-14,74]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":67,\"full_literals\":[-30,74]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":86,\"full_literals\":[-40,75]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":89,\"full_literals\":[-43,75]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":99,\"full_literals\":[-52,75]},{\"tag\":\"group_or\",\"kind\":3,\"index\":7,\"members\":[39,40,52,59,97],\"full_literals\":[-76,10,11,21,24,50]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":39,\"full_literals\":[-10,76]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":40,\"full_literals\":[-11,76]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":52,\"full_literals\":[-21,76]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":59,\"full_literals\":[-24,76]},{\"tag\":\"group_or\",\"kind\":3,\"index\":8,\"members\":[87,90,91,101],\"full_literals\":[-77,41,44,45,54]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":87,\"full_literals\":[-41,77]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":91,\"full_literals\":[-45,77]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":101,\"full_literals\":[-54,77]},{\"tag\":\"group_or\",\"kind\":3,\"index\":9,\"members\":[93,104],\"full_literals\":[-78,46,56]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":93,\"full_literals\":[-46,78]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":104,\"full_literals\":[-56,78]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0012\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-70,79],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0019\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-73,80],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0019\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-72,false,80],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0017\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-80,81],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-71,false,81],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-81,82],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-79,false,82],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0022\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-75,83],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0022\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-74,false,83],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0027\",\"right_name\":\"grouped3_0029\",\"joined_name\":\"grouped3_0028\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-84,77,78],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0027\",\"right_name\":\"grouped3_0029\",\"joined_name\":\"grouped3_0028\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-78,84],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0027\",\"right_name\":\"grouped3_0029\",\"joined_name\":\"grouped3_0028\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-77,false,84],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0027\",\"right_name\":\"grouped3_0029\",\"joined_name\":\"grouped3_0028\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-85,false,78],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0027\",\"right_name\":\"grouped3_0029\",\"joined_name\":\"grouped3_0028\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-77,-78,85],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0026\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-84,86],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0026\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-87,76,85],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0026\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-85,87],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0026\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-76,-84,87],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0022\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0023\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-87,88],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0022\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0023\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-83,-86,88],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0022\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0023\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-83,-87,89],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"groupKind3\",\"a\":0,\"b\":3,\"direction\":\"forward\",\"full_literals\":[false,-89,90],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-82,-88,90],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":38,\"owners\":[22,24,40,47,54,59,60,70,76,80,83,84,91,95,98,100,101,106]},{\"tag\":\"edge\",\"edge\":42,\"owners\":[10,23,41,50,58,61,62,67,73,79,81,84,89,93,97,99,101,104]}]}"
  "p cnf 90 167\n-10 -5 0\n-10 -8 0\n-11 -5 0\n-11 -8 0\n-12 -6 0\n-13 -10 0\n-13 -11 0\n-17 -12 0\n-18 -7 0\n-20 -7 0\n-20 -12 0\n-21 -5 0\n-21 -8 0\n-21 -13 0\n-24 -5 0\n-24 -8 0\n-24 -12 0\n-24 -13 0\n-26 -6 0\n-26 -12 0\n-26 -17 0\n-27 -7 0\n-27 -12 0\n-30 -6 0\n-30 -7 0\n-30 -17 0\n-30 -28 0\n-30 -29 0\n-36 -6 0\n-36 -17 0\n-36 -28 0\n-36 -29 0\n-39 -10 0\n-39 -11 0\n-39 -21 0\n-39 -24 0\n-42 -30 0\n-42 -36 0\n-43 -6 0\n-43 -17 0\n-43 -28 0\n-43 -29 0\n-43 -42 0\n-46 -5 0\n-46 -8 0\n-46 -12 0\n-46 -13 0\n-46 -39 0\n-50 -5 0\n-50 -6 0\n-50 -8 0\n-50 -9 0\n-50 -13 0\n-50 -15 0\n-50 -17 0\n-50 -22 0\n-50 -25 0\n-50 -28 0\n-50 -29 0\n-50 -39 0\n-50 -42 0\n-52 -6 0\n-52 -17 0\n-52 -18 0\n-52 -28 0\n-52 -29 0\n-52 -42 0\n-7 47 49 50 51 52 0\n-15 43 49 52 0\n-1 3 30 32 34 36 38 0\n-12 3 34 36 38 0\n-26 3 30 32 34 38 0\n-27 3 30 32 34 36 0\n-12 50 52 54 0\n-19 46 54 0\n-23 43 52 0\n-9 55 56 57 0\n-2 45 48 53 58 0\n-22 58 0\n-31 48 53 58 0\n-33 45 53 0\n-37 45 48 0\n-3 46 50 54 56 0\n-23 56 0\n-32 50 54 0\n-34 46 54 0\n-38 46 50 56 0\n-4 51 53 54 58 0\n-25 58 0\n-35 53 54 0\n-38 51 53 58 0\n-41 10 46 0\n-46 10 41 0\n-11 45 0\n-45 11 0\n-50 14 40 0\n-44 21 0\n-24 54 0\n-54 24 0\n-56 30 43 0\n-59 18 19 20 26 27 0\n-60 6 17 28 29 42 0\n-61 5 8 9 13 15 22 23 25 39 0\n-62 7 12 0\n-63 59 0\n-64 61 62 0\n-65 61 0\n-65 62 0\n-66 60 65 0\n-67 60 0\n-66 64 0\n-68 63 67 0\n-68 66 0\n-69 68 0\n69 0\n-55 70 0\n-57 70 0\n-16 71 0\n-47 72 0\n-48 72 0\n-49 72 0\n-51 73 0\n-53 73 0\n-58 73 0\n-14 74 0\n-30 74 0\n-40 75 0\n-43 75 0\n-52 75 0\n-76 10 11 21 24 50 0\n-10 76 0\n-11 76 0\n-21 76 0\n-24 76 0\n-77 41 44 45 54 0\n-41 77 0\n-45 77 0\n-54 77 0\n-78 46 56 0\n-46 78 0\n-56 78 0\n-70 79 0\n-73 80 0\n-72 80 0\n-80 81 0\n-71 81 0\n-81 82 0\n-79 82 0\n-75 83 0\n-74 83 0\n-84 77 78 0\n-78 84 0\n-77 84 0\n-85 78 0\n-77 -78 85 0\n-84 86 0\n-87 76 85 0\n-85 87 0\n-76 -84 87 0\n-87 88 0\n-83 -86 88 0\n-83 -87 89 0\n-89 90 0\n-82 -88 90 0\n-90 0\n2 4 11 16 22 24 25 31 33 35 37 38 45 48 51 53 54 58 0\n1 3 12 19 23 26 27 30 32 34 36 38 43 46 50 52 54 56 0\n"
  "168 68 0 115 114 0\n169 66 0 168 113 0\n170 64 0 169 111 0\n171 -89 0 165 163 0\n172 -46 9 7 23 15 58 0 170 89 79 44 45 46 47 48 104 103 106 0\n173 -5 -76 50 0 1 3 12 15 130 0\n174 -8 -76 50 0 2 4 13 16 130 0\n175 -13 -76 50 0 6 7 14 18 130 0\n176 -39 -76 50 0 33 34 35 36 130 0\n177 -87 82 0 171 170 147 145 143 124 89 79 144 121 119 122 148 142 117 116 162 149 150 127 128 129 125 126 96 69 76 100 68 77 172 139 154 157 173 174 175 176 103 106 104 17 74 99 0\n178 76 81 0 145 143 124 123 144 120 80 89 79 122 91 146 118 132 134 95 99 81 78 82 88 90 166 0\n179 82 0 147 145 146 143 144 118 122 123 124 120 91 79 89 80 177 178 159 153 137 138 81 78 82 88 90 94 98 166 0\n180 -88 0 179 165 164 0\n181 -87 0 180 160 0\n182 -85 0 181 158 0\n183 -50 23 0 169 49 50 51 52 53 54 55 56 57 58 59 60 61 102 103 109 107 0\n184 -28 84 0 152 141 140 84 183 87 153 138 85 83 86 75 27 31 41 65 70 72 71 73 167 0\n185 -29 84 0 152 141 140 84 183 87 153 138 85 83 86 75 28 32 42 66 70 72 71 73 167 0\n186 -42 84 0 152 141 140 84 183 87 153 138 85 83 86 75 37 38 43 67 70 72 71 73 167 0\n187 -6 84 0 152 141 140 84 183 87 153 138 85 83 86 75 5 19 24 29 39 62 70 73 167 0\n188 -17 84 0 152 141 140 84 183 87 153 138 85 83 86 75 8 21 26 30 40 63 70 73 167 0\n189 -7 84 0 168 184 187 186 185 188 102 110 112 105 152 141 140 84 183 87 153 138 85 83 86 75 9 10 22 25 101 72 0\n190 84 0 169 168 152 153 140 141 138 75 84 183 184 185 186 187 188 102 109 110 108 112 105 189 104 11 20 23 74 101 64 0\n191 86 0 190 156 0\n192 -76 0 190 181 159 0\n193 -83 0 191 180 161 0\n194 -10 0 192 131 0\n195 -11 0 192 132 0\n196 -21 0 192 133 0\n197 -24 0 192 134 0\n198 -75 0 193 149 0\n199 -74 0 193 150 0\n200 -45 0 195 95 0\n201 -44 0 196 97 0\n202 -54 0 197 99 0\n203 -43 0 198 128 0\n204 -30 0 199 126 0\n205 -56 0 203 204 100 0\n206 -46 0 194 182 93 140 136 155 0\n207 -78 0 206 205 139 0\n208 -41 0 206 194 92 0\n209 77 0 207 190 151 0\n210 0 208 209 201 200 202 135 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00067.record008.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00067.record008.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00067.record008.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00067.record008.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00067.record008 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00067.record008.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00067.record008.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00067.record008.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00067.record008.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00067.record008 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00067.record008_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00067.record008_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00067.record008_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00067.record008_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00067.record008_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00067.record008_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00067.record008_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00067.record008 Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00067.record008_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00067.record008_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00067.record008_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00067.record008
