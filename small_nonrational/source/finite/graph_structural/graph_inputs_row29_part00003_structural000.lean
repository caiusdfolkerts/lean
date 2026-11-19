module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow29Part00003Data
public import GraphInputsRow29Part00003Frames
public import GraphInputsRow29Part00003Leaves
public import GraphInputsRow29Part00003Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00003.record000
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00003.record000
def vertexColumn : Fields := ⟨10, hexnat% "398e5274e316cc729c673c29cb8aa68bae1b4699a9695a361db0ea398e5386e8789ef07915a5992e785d1565c5695656551d58d5352d1b51d27783d0ec370e9394cb31cd8b52cab1af07a1d8791d4785c9715d0f23c4fd103ca489a0ea4619a160d82e0798926439514650d50d0b41d18c930cc8b0ac1b11c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "db6db6db49a4924db6926da4d26db4924936da6926936d2492489249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2, 3]
def candidates : List (Fin raw.n) := [⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩, ⟨95, by decide⟩, ⟨96, by decide⟩, ⟨97, by decide⟩, ⟨98, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7ff3bfae7f81ee9ffc0000000", hexnat% "4000280020000000000", hexnat% "8401000001000000000000", hexnat% "4000080000040000000000", 387309567953862656, hexnat% "100000100000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7fffffffcf57fdff7c0000000", hexnat% "20000000800000000", 576495936675512320, hexnat% "10280000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7ffbffdf4fd7ebff7c0000000", hexnat% "4000080000400000000000", hexnat% "2000000000800000000", hexnat% "10280000000000000", hexnat% "20001000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨87, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .size 3
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .size 2
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨74, by decide⟩ c5 c6
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨84, by decide⟩ c5 c7
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7ffeffffffffe9fffc0000000", hexnat% "1000000000000000000000", 105553116266496, 281474976710656]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨67, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨84, by decide⟩ c5 c4
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7ffaffbf7ffffffffc0000000", hexnat% "4000000000000000000", hexnat% "1000000000000000000000", hexnat% "4000080000000000000000"]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨87, by decide⟩ c12 c11
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7ff3e7bf7fffe9fffc0000000", hexnat% "4000080000400000000000", hexnat% "184000000000000000000", 35184372088832, hexnat% "8000000001000000000000"]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c14 c13
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨73, by decide⟩ c15 c10
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7ff6c79fdf57edfc7c0000000", hexnat% "280000800200000000000", hexnat% "4000280000000000000", hexnat% "1000020000003000000000", hexnat% "8000000001000000000000", hexnat% "102000000000800000000"]
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨64, by decide⟩ c17 c16
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨83, by decide⟩ c18 c3
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7ffbffbe6fc3ff9ffc0000000", hexnat% "4000080000040000000000", hexnat% "100040000000000000", hexnat% "4000280020000000000", hexnat% "10100000000000000"]
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c5 c4
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c5 c21
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨86, by decide⟩ c5 c22
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7fffffffffdfffdfec0000000", 144115192370823168, 2199023255552]
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨65, by decide⟩ c24 c23
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7fffffbfdfdfffddec0000000", 144115192370823168, hexnat% "20000002000000000", hexnat% "4000000020000000000"]
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨83, by decide⟩ c26 c25
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c5 c4
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨65, by decide⟩ c5 c28
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7ffffffffffffe9ffc0000000", 6597069766656, 17592186044416]
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨86, by decide⟩ c30 c29
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7ffbffbfdfffffddfc0000000", hexnat% "20000002000000000", hexnat% "4000000000000000000000", hexnat% "4000000020000000000"]
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨83, by decide⟩ c32 c31
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7ffb7fbf7fdffe9fec0000000", hexnat% "804000000000000000000", hexnat% "4000080000040000000000", 17596481011712, 144117387099111424]
  let c35 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c34 c33
  let c36 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨68, by decide⟩ c35 c27
  let c37 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7fff57becfc3fedcec0000000", hexnat% "a80000000002000000000", hexnat% "4000280020000000000", hexnat% "30000001000000000", hexnat% "100000100000000000", 90071996842377216]
  let c38 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c37 c36
  let c39 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨84, by decide⟩ c38 c20
  let c40 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7ffb77bffffff9dffc0000000", hexnat% "4000000000400000000000", 37383395344384, hexnat% "884000000000000000000"]
  let c41 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7ffa77bf7ffff89ffc0000000", hexnat% "884000000000000000000", hexnat% "1000000000100000000000", hexnat% "4000080000440000000000", 37383395344384]
  let c42 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨68, by decide⟩ c41 c40
  let c43 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c5 c4
  let c44 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨65, by decide⟩ c5 c43
  let c45 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨86, by decide⟩ c5 c44
  let c46 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7ffbffffffebfffffc0000000", hexnat% "4000000000000000000000", 90071992547409920]
  let c47 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c46 c45
  let c48 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7ffff7ffdf6bfffdfc0000000", 90071992547409920, hexnat% "20000002000000000", hexnat% "80000800000000000000"]
  let c49 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨83, by decide⟩ c48 c47
  let c50 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨65, by decide⟩ c5 c4
  let c51 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨68, by decide⟩ c5 c50
  let c52 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7ffffffe5ffffffffc0000000", hexnat% "20000000000000000", hexnat% "180000000000000000"]
  let c53 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨86, by decide⟩ c52 c51
  let c54 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7ffbfffe5ffffffdfc0000000", hexnat% "20000002000000000", hexnat% "180000000000000000", hexnat% "4000000000000000000000"]
  let c55 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨83, by decide⟩ c54 c53
  let c56 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7ffbfffe7f6bfffffc0000000", 648518346341351424, hexnat% "4000080000000000000000", hexnat% "100040000000000000"]
  let c57 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7ffef7fedf6bfffcfc0000000", 90071992547409920, hexnat% "100000000000000000", hexnat% "80000800000000000000", hexnat% "1000020000003000000000"]
  let c58 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨83, by decide⟩ c57 c56
  let c59 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c58 c55
  let c60 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c59 c49
  let c61 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7ffe77bedf43fcfce80000000", hexnat% "80000800200000000000", hexnat% "1000020000003000000000", hexnat% "100000100000000000", 270215983010938880, hexnat% "804000000000000000000"]
  let c62 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c61 c60
  let c63 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨64, by decide⟩ c62 c42
  let c64 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7ff3c7ce7f3de8fffc0000000", hexnat% "280000800200000000000", hexnat% "100420100000000000", hexnat% "103000000000000000000", hexnat% "c000000001400000000000", hexnat% "80000000000000000"]
  let c65 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7ff3ffae7fffebdffc0000000", hexnat% "180000000000000000", hexnat% "4000000020000000000", hexnat% "c001000001000000000000", 70368744177664]
  let c66 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7ff3ffee4fa9eabefc0000000", hexnat% "30000001000000000", hexnat% "c001000001000000000000", hexnat% "180000140000000000", 70368744177664, 387309567953862656]
  let c67 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c66 c65
  let c68 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7ff26fce7ffdeabd7c0000000", hexnat% "1800000000002000000000", hexnat% "180020100000000000", hexnat% "103000000000800000000", hexnat% "c000000001400000000000", 4398046511104]
  let c69 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7ff3678fcf7fe9dd7c0000000", 107752139522048, hexnat% "10800000000000000", hexnat% "20001002800000000", hexnat% "984000000000000000000", hexnat% "c003000000000000000000"]
  let c70 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7ff67fbfffffffdffc0000000", hexnat% "8000000000000000000000", hexnat% "4000000020000000000", hexnat% "1800000000000000000000"]
  let c71 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c5 c4
  let c72 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨84, by decide⟩ c5 c71
  let c73 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨87, by decide⟩ c5 c72
  let c74 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7ff6ffffffaffffefc0000000", hexnat% "8000000000000000000000", hexnat% "1000000000001000000000", 360287970189639680]
  let c75 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨64, by decide⟩ c74 c73
  let c76 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7ffe7fffefa7fddefc0000000", 37383395344384, 360287970189639680, hexnat% "1800000000001000000000", hexnat% "10080000000000000"]
  let c77 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨74, by decide⟩ c76 c75
  let c78 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c77 c70
  let c79 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7ffe7fbeef21fc9efc0000000", 41781441855488, hexnat% "804000000000000000000", hexnat% "1000000000101000000000", hexnat% "10980000000000000", hexnat% "100460000000000000"]
  let c80 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨67, by decide⟩ c79 c78
  let c81 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7ff3ffefcfe3effffc0000000", 126100789566373888, hexnat% "30000000000000000", hexnat% "c001000001000000000000"]
  let c82 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7ff3ffee6fa1eb9ffc0000000", 76965813944320, hexnat% "10180000000000000", hexnat% "c001000001000000000000", hexnat% "100460000000000000", hexnat% "80000000000000000"]
  let c83 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c82 c81
  let c84 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c5 c6
  let c85 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨84, by decide⟩ c5 c84
  let c86 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7ff6ffefffbfeffffc0000000", hexnat% "1000000000000000000000", hexnat% "1000400000000000000", hexnat% "8000000001000000000000"]
  let c87 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨73, by decide⟩ c86 c85
  let c88 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7ff66fcfffbfeffffc0000000", hexnat% "1000400000000000000", hexnat% "1800000000000000000000", hexnat% "8000000001000000000000", hexnat% "102000000000000000000"]
  let c89 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨74, by decide⟩ c88 c87
  let c90 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7ff7ffcfffafeffffc0000000", hexnat% "8001000001000000000000", 360287970189639680, hexnat% "2000000000000000000"]
  let c91 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7ff7efcfff27effffc0000000", hexnat% "8001000001000000000000", 360287970189639680, hexnat% "102000000000000000000", 612489549322387456]
  let c92 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨74, by decide⟩ c91 c90
  let c93 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7ff76f8fdf27effcfc0000000", 360287970189639680, hexnat% "20001002000000000", hexnat% "8003000000000000000000", 612489618041864192, hexnat% "904000000000000000000"]
  let c94 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨84, by decide⟩ c93 c92
  let c95 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨64, by decide⟩ c94 c89
  let c96 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7fff7fbfef63fddffc0000000", 37383395344384, 126100789566373888, hexnat% "804000000000000000000", hexnat% "10800000000000000"]
  let c97 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7ff36f8fcf7ff9ddfc0000000", hexnat% "30000002000000000", 107752139522048, hexnat% "904000000000000000000", 576460752303423488, hexnat% "c003000000000000000000"]
  let c98 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c97 c96
  let c99 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7ff26f8ecf21effcfc0000000", hexnat% "100460000000000000", hexnat% "103000000000000000000", hexnat% "1000020000003000000000", hexnat% "10980000000000000", hexnat% "804000000000000000000", hexnat% "c000000001000000000000"]
  let c100 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c99 c98
  let c101 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨67, by decide⟩ c100 c95
  let c102 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨79, by decide⟩ c101 c83
  let c103 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c102 c80
  let c104 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c103 c69
  let c105 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c104 c68
  let c106 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨81, by decide⟩ c105 c67
  let c107 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c106 c64
  let c108 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨82, by decide⟩ c107 c63
  let c109 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c108 c39
  let c110 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c109 c19
  let c111 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c110 c0
  c111
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00003.record000_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00003.record000_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00003.record000_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00003.record000_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00003.record000_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00003.record000_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00003.record000_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00003.record000_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00003.record000_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00003.record000
