module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow29Part00030Data
public import GraphInputsRow29Part00030Frames
public import GraphInputsRow29Part00030Leaves
public import GraphInputsRow29Part00030Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00030.record000
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00030.record000
def vertexColumn : Fields := ⟨10, hexnat% "3c4cd34cb332c5b29c3723cf0b32d2acaca96aa68da8eb86d1ac671b2659b16a58d68d9362db0ea3a4e538ce8b92e1ba1e2785e0f969a64d9e15c559715a54d54d4b5c368d534cd4b46d8749d1778370d63c4e9334d332cf0ba2d4b32d2b1ae1b26c5bc1e8761d4731d2729c6785d1725c570de0f43c8f13c2f07e948703ca4a1a0e839514c5494950d44d0b41d50cc348c930cc4b0ac1b"⟩
def kindColumn : Fields := ⟨3, hexnat% "36db69a6db6d34db6db4db6db6db69b4db6934926d24924d26924da49249b6926db4d36d2449249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨29, by decide⟩, ⟨31, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨79, by decide⟩, ⟨82, by decide⟩, ⟨95, by decide⟩, ⟨103, by decide⟩, ⟨105, by decide⟩, ⟨112, by decide⟩, ⟨114, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40000800484f37b79fc70a3800000", hexnat% "2008000000000000000", hexnat% "280000000000000000000000000", hexnat% "10000000000000000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "50080800484d37a51b470a3800000", 11267795161448448, 72127962782105600, hexnat% "2208000000000000000", hexnat% "200000000000000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨52, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "800486934b79fc70a3800000", hexnat% "401000000000000000", hexnat% "208000000000000000", hexnat% "280000000000000000000000000", hexnat% "50000000000002000000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40280800484d35a79bc70a3800000", hexnat% "10000000000002000000000000000", 72127962782105600, hexnat% "2208000000000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "800484f3fa69ac70a3800000", hexnat% "2000100000000000000", 4573968371548160, hexnat% "50000000000000000000000000000", hexnat% "280000000000000100000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "800484d34a29ac70a3800000", 76631562409476096, hexnat% "2208000000000000000", hexnat% "280000000000000100000000000", 2323857407723175936, hexnat% "50000000000001000000000000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨68, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c7 c4
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c8 c3
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨71, by decide⟩ c9 c2
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "800486f3f9786870a3800000", hexnat% "50000000000000000000000000000", hexnat% "280000000000000100000000000", 144541798587432960]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40280800480d15369bc70a3800000", 4573968371548160, hexnat% "10000000000002800000000000000", hexnat% "2208000000000000000", hexnat% "4020000000000000000"]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "80800480d05b79fc70a3800000", hexnat% "50000000000002000000000000000", hexnat% "200000000010000000000000000", hexnat% "2208000000000000000", hexnat% "4020000000000000000"]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "800486f3d178ec70a3800000", 144396663052566528, hexnat% "10000000000002800000000000000", hexnat% "280000000000000100000000000", hexnat% "40000000000000000000000000000"]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "50200800486d378688c70a3800000", hexnat% "208000000000000000", hexnat% "80000000000000100000000000", 216489441462583296, 4573968371548160]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "800482f150788c70a3800000", hexnat% "4000200000000000000", hexnat% "280000000000000100000000000", hexnat% "50000000000002000000000000000", 72444622130905088, hexnat% "28800000000000000"]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨64, by decide⟩ c16 c15
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨73, by decide⟩ c17 c14
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c18 c13
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c19 c12
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨62, by decide⟩ c20 c11
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40200000006d37878dc60a2800000", 216489441462583296, hexnat% "208000001001000000", hexnat% "10080000480000000000000000000", hexnat% "800000000000000000000000"]
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "50280000486c37848bc6082800000", 153403862307307520, hexnat% "308000000020000000", hexnat% "800000000000001001000000", 76631562409476096]
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "50200800486c378489870a3800000", hexnat% "80000000000000040000000000", 153403862307307520, hexnat% "308000000000000000", 76666746781564928]
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40200800006c37848986082000000", 153408260353818624, hexnat% "10080000480000000000000800000", 76666746781564928, hexnat% "308000000020000000", 68736253952]
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨95, by decide⟩ c25 c24
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c26 c23
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c27 c22
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "50280800482f17b51fc70a3800000", 11258999068426240, hexnat% "28000000000000000", hexnat% "4000000000000000000"]
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "50200800482f3fb51e870a3800000", hexnat% "4000000000000000000", 11263397114937344, hexnat% "80000000000000100000000000"]
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "50200800480f17958e870a3800000", hexnat% "80000000000000140000000000", hexnat% "6020000000000000000", 153403862307307520, 9223372036854775808]
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c31 c30
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c32 c29
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40200800480f3bb79ec70a3800000", hexnat% "10080000000000000000000000000", 17592186044416, hexnat% "6004000000000000000"]
  let c35 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40200800484d39b61e470a3800000", 6764195534077952, hexnat% "2204000000000000000", hexnat% "10080000000000000000000000000", 2305860601399738368]
  let c36 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨68, by decide⟩ c35 c34
  let c37 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40280800486a3f979fc70a3800000", 144115188075855872, hexnat% "10000000000000000000000000000", hexnat% "500000000000000000"]
  let c38 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40280800486a3d179fc70a3800000", 144115188075855872, hexnat% "500800000000000000", hexnat% "10000000000002000000000000000"]
  let c39 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40280800482815379bc70a3800000", hexnat% "308000000000000000", hexnat% "10000000000002800000000000000", hexnat% "20000400000000000", hexnat% "4400000000000000000"]
  let c40 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨73, by decide⟩ c39 c38
  let c41 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨62, by decide⟩ c40 c37
  let c42 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "50280800486a3f9412870a3800000", 6825768185233408, hexnat% "500000000000000000", 21990232555520, 153263124818952192]
  let c43 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40200800486c3db79ec70a3800000", hexnat% "300000000000000000", hexnat% "80000000000000100000000000", hexnat% "10000000000002000000000000000"]
  let c44 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40200800486a3d1596c70a3800000", hexnat% "80000000000000100000000000", 153263124818952192, hexnat% "500800000000000000", hexnat% "10000000000002000000000000000"]
  let c45 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨74, by decide⟩ c44 c43
  let c46 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "50280800480f1f8494870a3800000", 76596378037387264, hexnat% "6020000000000000000", 21990232555520, 153263124818952192]
  let c47 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "50200800486d37a795c70a3800000", hexnat% "208000000000000000", hexnat% "80000000000000000000000000", 72233515898372096]
  let c48 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40200800486f3da494870a3800000", 9152334789607424, hexnat% "10000000000002000000000000000", 76596378037387264, hexnat% "80000000000000100000000000"]
  let c49 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c48 c47
  let c50 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40200800486915379fc70a3800000", hexnat% "208000000000000000", hexnat% "10080000000000000000000000000", 2882303761517117440, hexnat% "420000000000000000"]
  let c51 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40200800484f35b79ec70a3800000", hexnat% "2008000000000000000", 2305860601399738368, hexnat% "10080000000000000000000000000"]
  let c52 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40200800484d358797c70a3800000", 216313519602139136, hexnat% "10000000000002000000000000000", hexnat% "2208000000000000000", hexnat% "80000000000000000000000000"]
  let c53 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨52, by decide⟩ c52 c51
  let c54 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40200800484f150516870a3800000", hexnat% "10000000000002800000000000000", hexnat% "2028000000000000000", hexnat% "80000000000000140000000000", 216313519602139136, 11258999068426240]
  let c55 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨70, by decide⟩ c54 c53
  let c56 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c55 c50
  let c57 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨74, by decide⟩ c56 c49
  let c58 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨68, by decide⟩ c57 c46
  let c59 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c58 c45
  let c60 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨62, by decide⟩ c59 c42
  let c61 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c60 c41
  let c62 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c61 c36
  let c63 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c62 c33
  let c64 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40280800484431379fc70a3800000", hexnat% "902000000000000000", hexnat% "10000000000000800000000000000", hexnat% "220c000000000000000"]
  let c65 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40280800000d11078bc20a2800000", 216454531968401408, hexnat% "10000000480002000000000000000", 9223442474335207424, hexnat% "2204000000000000000", hexnat% "4020800000000000000"]
  let c66 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c65 c64
  let c67 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "50280800480f1f810fc70a3800000", 29273397577908224, hexnat% "2000100000000000000", hexnat% "4020000000000000000", 144396663052566528]
  let c68 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40000800480f1f8787c70a3800000", hexnat% "10080000000000000000000000000", hexnat% "200000000000000800000000000", hexnat% "6020000000000000000", 216454257090494464]
  let c69 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "800482e1db79ec70a3800000", hexnat% "102000000000000000", hexnat% "4020000000000000000", hexnat% "280000000000000100000000000", hexnat% "50000000000000000000000000000"]
  let c70 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40280800480b1d878fc70a3800000", hexnat% "10000000000002000000000000000", 216454257090494464, hexnat% "4420000000000000000", hexnat% "2000000000000000000"]
  let c71 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "50200800480b1f8787c70a3800000", hexnat% "80000000000000000000000000", hexnat% "4420000000000000000", 216594994578849792, hexnat% "2000000000000000000"]
  let c72 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "200800486f3fa386c70a3800000", 72479806502993920, 18031990695526400, hexnat% "10080000000000000000000000000", hexnat% "40000000000000000000000000000"]
  let c73 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "200800484a1f8787c70a3800000", hexnat% "500000000000000000", hexnat% "2020000000000000000", hexnat% "10080000000000000000000000000", hexnat% "40000000000000000800000000000", 216454257090494464]
  let c74 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨74, by decide⟩ c73 c72
  let c75 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨61, by decide⟩ c74 c71
  let c76 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨105, by decide⟩ c75 c70
  let c77 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c76 c69
  let c78 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨71, by decide⟩ c77 c68
  let c79 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c78 c67
  let c80 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40200800000f1bb69bc60a3800000", 4574037091024896, hexnat% "6024000000000000000", hexnat% "10080000480000000000000000000"]
  let c81 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40200800000913361bc6083000000", hexnat% "4420800000000000000", 6825768722104320, hexnat% "10080000480000000000000800000", hexnat% "220c000000000000000", 68719476736]
  let c82 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨68, by decide⟩ c81 c80
  let c83 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1000080048673fb318c70a3800000", hexnat% "280000000000000100000000000", hexnat% "40000000000800000000000000000", 105553116266496, 20266198323167232]
  let c84 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "50280800486937b419870a3800000", hexnat% "208000000000000000", hexnat% "400020040000000000", 4609152743636992, 2251799813685248]
  let c85 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "280800486c32b69bc70a3800000", 4573968371548160, hexnat% "50000000000001000000000000000", hexnat% "20c000000000000000", hexnat% "100000000000000000"]
  let c86 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "80800486632b39fc70a3800000", hexnat% "200000000000040000000000000", hexnat% "50000000000001000000000000000", 13835058055282163712, hexnat% "900000000000000000"]
  let c87 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "10080800486032b019c70a3800000", 4609152743636992, 29273397577908224, hexnat% "20c000000000000000", hexnat% "d01000000000000000", hexnat% "40200000000000000000000000000"]
  let c88 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c87 c86
  let c89 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c88 c85
  let c90 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨61, by decide⟩ c89 c84
  let c91 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c90 c83
  let c92 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "80000633fb79fc60a3800000", hexnat% "c00000000000000000", hexnat% "480000000001000000000", hexnat% "280000000000000000000000000", hexnat% "50000000000000000000000000000"]
  let c93 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "80048663fb39e870a3800000", hexnat% "900000000000000000", hexnat% "50000000000000000000000000000", hexnat% "80000000000000140000000000", hexnat% "200000000000040000000000000"]
  let c94 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "80000623f918e870a3800000", 153408260353818624, hexnat% "d00000000000000000", hexnat% "200000000000040100000000000", hexnat% "50000000400000000000000000000", hexnat% "80000080000000000000000000"]
  let c95 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c94 c93
  let c96 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c95 c92
  let c97 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "80048231d118e870a3800000", hexnat% "280000000000000100000000000", hexnat% "50000000000002000000000000000", hexnat% "800040000000000000", hexnat% "4420800000000000000", 153408260353818624]
  let c98 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1000080000673fb31ec50a3800000", hexnat% "480000000002000000000", 20283790509211648, hexnat% "40000000000800000000000000000", hexnat% "280000000000000000000000000"]
  let c99 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "50280800404d3f9609c40a3800000", 6825768185233408, hexnat% "80000000003000000000", 144431847424655360, hexnat% "2200000000000000000"]
  let c100 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "50200800004d3f9208c40a3800000", 20283790509211648, 144396800491520000, hexnat% "2200000001000000000", hexnat% "80000480000000000000000000", 4609152743636992]
  let c101 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨105, by decide⟩ c100 c99
  let c102 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c101 c98
  let c103 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "50280800484d378609c60a3800000", 6825768185233408, 216489441462583296, hexnat% "2208000001000000000"]
  let c104 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "800004d378689c60a3000000", 216489441462583296, hexnat% "40200000400000000000000000000", hexnat% "2208000001000000000", hexnat% "10080000080000000000000800000", 4573968371548160]
  let c105 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨61, by decide⟩ c104 c103
  let c106 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1008080048043eb39fc70a3800000", hexnat% "6000000000000000000", hexnat% "200000000000040000000000000", hexnat% "301000000000000000", hexnat% "40000000000800000000000000000"]
  let c107 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "50200800480c3f959fc50a3000000", hexnat% "300000000000000000", hexnat% "6000000000000000000", hexnat% "80000000000000000000800000", 153122524769550336]
  let c108 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "5008080048073f919ec50a3800000", hexnat% "6000000000000000000", hexnat% "200000000000040100000000000", 153122524769550336, hexnat% "800000000000000000"]
  let c109 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "5000080008263c919ec50a3000000", 153122524769550336, hexnat% "4000000000000000000", hexnat% "280000400000000100000000000", hexnat% "802040000000000000", hexnat% "101000000000800000"]
  let c110 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨112, by decide⟩ c109 c108
  let c111 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨114, by decide⟩ c110 c107
  let c112 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨79, by decide⟩ c111 c106
  let c113 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40280800484d37a61d870a3800000", hexnat% "10000000000000000000000000000", 2256197860196352, hexnat% "2208000000000000000", 76596378037387264]
  let c114 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "50280800484c37a61d870a3800000", 2256197860196352, 76596378037387264, hexnat% "308000000000000000", hexnat% "2000000000000000000"]
  let c115 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "200800484c34a69d870a3800000", 76596378037387264, hexnat% "2208000000000000000", hexnat% "80000000000000040000000000", hexnat% "50000000000003000000000000000", hexnat% "100000000000000000"]
  let c116 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨105, by decide⟩ c115 c114
  let c117 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨71, by decide⟩ c116 c113
  let c118 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1008080048273f919fc70a3800000", hexnat% "4000200000000000000", 27021597764222976, hexnat% "40000000000800000000000000000", hexnat% "200000000000000000000000000"]
  let c119 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1008080048071f818fc70a3800000", hexnat% "40000000000800000000000000000", hexnat% "200000000000040000000000000", 153403862307307520, hexnat% "6020000000000000000", 72057594037927936]
  let c120 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c119 c118
  let c121 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "80800006434a29fc60a3800000", 76561262384775168, hexnat% "200000000000040000000000000", hexnat% "10000000480002000000000000000", hexnat% "308000000000000000", hexnat% "40000000000801000000000000000"]
  let c122 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "280800482f1f958fc70a3800000", 153403862307307520, hexnat% "4020000000000000000", hexnat% "50000000000000000000000000000"]
  let c123 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "80048261cb11fc70a3800000", hexnat% "4020000000000000000", hexnat% "280000000000000000000000000", 29273397577908224, hexnat% "903000000000000000", hexnat% "50000000000000000000000000000"]
  let c124 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c123 c122
  let c125 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "50200800000f17818cc70a3800000", 27021597764222976, hexnat% "2028000000000000000", hexnat% "4000200000000000000", hexnat% "80000480000000100000000000", 72374253386727424]
  let c126 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "50280800480c17848fc70a3800000", 76561193665298432, 153403862307307520, hexnat% "308000000000000000", hexnat% "6020000000000000000"]
  let c127 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "80000643db21fc70a3800000", 6755399441055744, hexnat% "300000000000000000", hexnat% "802040000000000000", hexnat% "10080000480000000000000000000", hexnat% "40200000000000000000000000000"]
  let c128 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4028080040271d879dc70a3800000", hexnat% "4020000000000000000", hexnat% "802000000000000000", 216207966485872640, hexnat% "10000000080000000000000000000"]
  let c129 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40280800400615869dc70a3800000", hexnat% "902000000000000000", hexnat% "10000000080000000000000000000", 76596378037387264, hexnat% "2028000000000000000", hexnat% "4000200000000000000"]
  let c130 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨69, by decide⟩ c129 c128
  let c131 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "200800000415869dc70a3800000", hexnat% "6020000000000000000", hexnat% "10080000480000000000000000000", 76596378037387264, 144115188075855872, hexnat% "308000000000000000", hexnat% "40000000000802000000000000000"]
  let c132 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨105, by decide⟩ c131 c130
  let c133 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c132 c127
  let c134 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c133 c126
  let c135 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c134 c125
  let c136 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c135 c124
  let c137 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c136 c121
  let c138 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨23, by decide⟩ c137 c120
  let c139 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c138 c117
  let c140 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c139 c112
  let c141 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨70, by decide⟩ c140 c105
  let c142 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c141 c102
  let c143 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c142 c97
  let c144 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨62, by decide⟩ c143 c96
  let c145 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c144 c91
  let c146 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c145 c82
  let c147 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨24, by decide⟩ c146 c79
  let c148 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c147 c66
  let c149 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨95, by decide⟩ c148 c63
  let c150 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨64, by decide⟩ c149 c28
  let c151 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c150 c21
  let c152 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c151 c10
  c152
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00030.record000_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00030.record000_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00030.record000_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00030.record000_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00030.record000_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00030.record000_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00030.record000_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00030.record000_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00030.record000_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00030.record000
