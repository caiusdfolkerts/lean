module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow29Part00067Data
public import GraphInputsRow29Part00067Frames
public import GraphInputsRow29Part00067Leaves
public import GraphInputsRow29Part00067Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

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
