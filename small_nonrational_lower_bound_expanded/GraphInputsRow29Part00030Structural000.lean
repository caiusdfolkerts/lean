module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow29Part00030Data
public import GraphInputsRow29Part00030Frames
public import GraphInputsRow29Part00030Leaves
public import GraphInputsRow29Part00030Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00030.record000
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00030.record000
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨29, by decide⟩, ⟨31, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨79, by decide⟩, ⟨82, by decide⟩, ⟨95, by decide⟩, ⟨103, by decide⟩, ⟨105, by decide⟩, ⟨112, by decide⟩, ⟨114, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), (certNat% 3), (certNat% 4), (certNat% 5)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 6), 11267795161448448, 72127962782105600, (certNat% 7), (certNat% 8)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨52, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 9), (certNat% 10), (certNat% 11), (certNat% 4), (certNat% 12)]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 13), (certNat% 14), 72127962782105600, (certNat% 7)]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 15), (certNat% 16), 4573968371548160, (certNat% 17), (certNat% 18)]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 19), 76631562409476096, (certNat% 7), (certNat% 18), 2323857407723175936, (certNat% 20)]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨68, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c7 c4
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c8 c3
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨71, by decide⟩ c9 c2
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 21), (certNat% 17), (certNat% 18), 144541798587432960]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 22), 4573968371548160, (certNat% 23), (certNat% 7), (certNat% 24)]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 25), (certNat% 12), (certNat% 26), (certNat% 7), (certNat% 24)]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 27), 144396663052566528, (certNat% 23), (certNat% 18), (certNat% 28)]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 29), (certNat% 11), (certNat% 30), 216489441462583296, 4573968371548160]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 31), (certNat% 32), (certNat% 18), (certNat% 12), 72444622130905088, (certNat% 33)]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨64, by decide⟩ c16 c15
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨73, by decide⟩ c17 c14
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c18 c13
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c19 c12
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨62, by decide⟩ c20 c11
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 34), 216489441462583296, (certNat% 35), (certNat% 36), (certNat% 37)]
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 38), 153403862307307520, (certNat% 39), (certNat% 40), 76631562409476096]
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 41), (certNat% 42), 153403862307307520, (certNat% 43), 76666746781564928]
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 44), 153408260353818624, (certNat% 45), 76666746781564928, (certNat% 39), 68736253952]
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨95, by decide⟩ c25 c24
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c26 c23
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c27 c22
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 46), 11258999068426240, (certNat% 47), (certNat% 48)]
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 49), (certNat% 48), 11263397114937344, (certNat% 30)]
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 50), (certNat% 51), (certNat% 52), 153403862307307520, 9223372036854775808]
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c31 c30
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c32 c29
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 53), (certNat% 54), 17592186044416, (certNat% 55)]
  let c35 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 56), 6764195534077952, (certNat% 57), (certNat% 54), 2305860601399738368]
  let c36 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨68, by decide⟩ c35 c34
  let c37 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 58), 144115188075855872, (certNat% 5), (certNat% 59)]
  let c38 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 60), 144115188075855872, (certNat% 61), (certNat% 14)]
  let c39 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 62), (certNat% 43), (certNat% 23), (certNat% 63), (certNat% 64)]
  let c40 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨73, by decide⟩ c39 c38
  let c41 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨62, by decide⟩ c40 c37
  let c42 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 65), 6825768185233408, (certNat% 59), 21990232555520, 153263124818952192]
  let c43 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 66), (certNat% 67), (certNat% 30), (certNat% 14)]
  let c44 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 68), (certNat% 30), 153263124818952192, (certNat% 61), (certNat% 14)]
  let c45 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨74, by decide⟩ c44 c43
  let c46 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 69), 76596378037387264, (certNat% 52), 21990232555520, 153263124818952192]
  let c47 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 70), (certNat% 11), (certNat% 71), 72233515898372096]
  let c48 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 72), 9152334789607424, (certNat% 14), 76596378037387264, (certNat% 30)]
  let c49 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c48 c47
  let c50 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 73), (certNat% 11), (certNat% 54), 2882303761517117440, (certNat% 74)]
  let c51 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 75), (certNat% 3), 2305860601399738368, (certNat% 54)]
  let c52 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 76), 216313519602139136, (certNat% 14), (certNat% 7), (certNat% 71)]
  let c53 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨52, by decide⟩ c52 c51
  let c54 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 77), (certNat% 23), (certNat% 78), (certNat% 51), 216313519602139136, 11258999068426240]
  let c55 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨70, by decide⟩ c54 c53
  let c56 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c55 c50
  let c57 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨74, by decide⟩ c56 c49
  let c58 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨68, by decide⟩ c57 c46
  let c59 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c58 c45
  let c60 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨62, by decide⟩ c59 c42
  let c61 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c60 c41
  let c62 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c61 c36
  let c63 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c62 c33
  let c64 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 79), (certNat% 80), (certNat% 81), (certNat% 82)]
  let c65 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 83), 216454531968401408, (certNat% 84), 9223442474335207424, (certNat% 57), (certNat% 85)]
  let c66 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c65 c64
  let c67 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 86), 29273397577908224, (certNat% 16), (certNat% 24), 144396663052566528]
  let c68 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 87), (certNat% 54), (certNat% 88), (certNat% 52), 216454257090494464]
  let c69 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 89), (certNat% 90), (certNat% 24), (certNat% 18), (certNat% 17)]
  let c70 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 91), (certNat% 14), 216454257090494464, (certNat% 92), (certNat% 93)]
  let c71 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 94), (certNat% 71), (certNat% 92), 216594994578849792, (certNat% 93)]
  let c72 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 95), 72479806502993920, 18031990695526400, (certNat% 54), (certNat% 28)]
  let c73 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 96), (certNat% 59), (certNat% 97), (certNat% 54), (certNat% 98), 216454257090494464]
  let c74 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨74, by decide⟩ c73 c72
  let c75 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨61, by decide⟩ c74 c71
  let c76 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨105, by decide⟩ c75 c70
  let c77 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c76 c69
  let c78 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨71, by decide⟩ c77 c68
  let c79 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c78 c67
  let c80 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 99), 4574037091024896, (certNat% 100), (certNat% 36)]
  let c81 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 101), (certNat% 102), 6825768722104320, (certNat% 45), (certNat% 82), 68719476736]
  let c82 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨68, by decide⟩ c81 c80
  let c83 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 103), (certNat% 18), (certNat% 104), 105553116266496, 20266198323167232]
  let c84 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 105), (certNat% 11), (certNat% 106), 4609152743636992, 2251799813685248]
  let c85 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 107), 4573968371548160, (certNat% 20), (certNat% 108), (certNat% 109)]
  let c86 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 110), (certNat% 111), (certNat% 20), 13835058055282163712, (certNat% 112)]
  let c87 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 113), 4609152743636992, 29273397577908224, (certNat% 108), (certNat% 114), (certNat% 115)]
  let c88 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c87 c86
  let c89 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c88 c85
  let c90 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨61, by decide⟩ c89 c84
  let c91 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c90 c83
  let c92 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 116), (certNat% 117), (certNat% 118), (certNat% 4), (certNat% 17)]
  let c93 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 119), (certNat% 112), (certNat% 17), (certNat% 51), (certNat% 111)]
  let c94 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 120), 153408260353818624, (certNat% 121), (certNat% 122), (certNat% 123), (certNat% 124)]
  let c95 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c94 c93
  let c96 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c95 c92
  let c97 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 125), (certNat% 18), (certNat% 12), (certNat% 126), (certNat% 102), 153408260353818624]
  let c98 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 127), (certNat% 128), 20283790509211648, (certNat% 104), (certNat% 4)]
  let c99 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 129), 6825768185233408, (certNat% 130), 144431847424655360, (certNat% 131)]
  let c100 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 132), 20283790509211648, 144396800491520000, (certNat% 133), (certNat% 134), 4609152743636992]
  let c101 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨105, by decide⟩ c100 c99
  let c102 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c101 c98
  let c103 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 135), 6825768185233408, 216489441462583296, (certNat% 136)]
  let c104 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 137), 216489441462583296, (certNat% 138), (certNat% 136), (certNat% 139), 4573968371548160]
  let c105 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨61, by decide⟩ c104 c103
  let c106 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 140), (certNat% 141), (certNat% 111), (certNat% 142), (certNat% 104)]
  let c107 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 143), (certNat% 67), (certNat% 141), (certNat% 144), 153122524769550336]
  let c108 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 145), (certNat% 141), (certNat% 122), 153122524769550336, (certNat% 146)]
  let c109 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 147), 153122524769550336, (certNat% 48), (certNat% 148), (certNat% 149), (certNat% 150)]
  let c110 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨112, by decide⟩ c109 c108
  let c111 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨114, by decide⟩ c110 c107
  let c112 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨79, by decide⟩ c111 c106
  let c113 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 151), (certNat% 5), 2256197860196352, (certNat% 7), 76596378037387264]
  let c114 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 152), 2256197860196352, 76596378037387264, (certNat% 43), (certNat% 93)]
  let c115 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 153), 76596378037387264, (certNat% 7), (certNat% 42), (certNat% 154), (certNat% 109)]
  let c116 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨105, by decide⟩ c115 c114
  let c117 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨71, by decide⟩ c116 c113
  let c118 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 155), (certNat% 32), 27021597764222976, (certNat% 104), (certNat% 8)]
  let c119 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 156), (certNat% 104), (certNat% 111), 153403862307307520, (certNat% 52), 72057594037927936]
  let c120 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c119 c118
  let c121 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 157), 76561262384775168, (certNat% 111), (certNat% 84), (certNat% 43), (certNat% 158)]
  let c122 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 159), 153403862307307520, (certNat% 24), (certNat% 17)]
  let c123 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 160), (certNat% 24), (certNat% 4), 29273397577908224, (certNat% 161), (certNat% 17)]
  let c124 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c123 c122
  let c125 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 162), 27021597764222976, (certNat% 78), (certNat% 32), (certNat% 163), 72374253386727424]
  let c126 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 164), 76561193665298432, 153403862307307520, (certNat% 43), (certNat% 52)]
  let c127 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 165), 6755399441055744, (certNat% 67), (certNat% 149), (certNat% 36), (certNat% 115)]
  let c128 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 166), (certNat% 24), (certNat% 167), 216207966485872640, (certNat% 168)]
  let c129 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 169), (certNat% 80), (certNat% 168), 76596378037387264, (certNat% 78), (certNat% 32)]
  let c130 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨69, by decide⟩ c129 c128
  let c131 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 170), (certNat% 52), (certNat% 36), 76596378037387264, 144115188075855872, (certNat% 43), (certNat% 171)]
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
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00030.record000

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00030.record002
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "373c2d4ad2cc972e29cac6a9a568da4e966a58d61d94e3392e2b89e17bc1d46d1cc571e25c9c6699564d94e565a54d51d54d3352d2b49d17783d0ec370f2358f13a4e5354cd38cd331cf0ba2d8b52ccb2ae1b46c9b16e8751d2729c6785c9743c4f0f12a0e8c6158362382e079290e4c5154352342d07703a0d4330d2384c530cd0b22c2b06c8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "6db6db6db4da4d24936db6db6d3693492492492492492492492492492489249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00030.record002 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00030.record002 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00030.record002.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00030.record002.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00030.record002.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 72), (facetIndex 76)]))
 (.leaf ([(facetIndex 94), (facetIndex 98)])))
 (.branch 3
 (.leaf ([(facetIndex 75), (facetIndex 78), (facetIndex 80), (facetIndex 86)]))
 (.leaf ([(facetIndex 97), (facetIndex 100), (facetIndex 102), (facetIndex 108)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 82), (facetIndex 83), (facetIndex 88)]))
 (.leaf ([(facetIndex 79), (facetIndex 81), (facetIndex 84), (facetIndex 85), (facetIndex 87)])))
 (.branch 7
 (.leaf ([(facetIndex 104), (facetIndex 105), (facetIndex 110)]))
 (.branch 8
 (.leaf ([(facetIndex 101), (facetIndex 103), (facetIndex 106), (facetIndex 107), (facetIndex 109)]))
 (.leaf ([(facetIndex 111)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "8673776673730130010000045255445252002z4b;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 9
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped3_0000 : List Nat := [0, 1]
def grouped3_0001 : List Nat := [0, 1, 2, 3]
def grouped3_0003 : List Nat := [2]
def grouped3_0004 : List Nat := [2, 3]
def grouped3_0005 : List Nat := [3]
def grouped3_0006 : List Nat := [4]
def grouped3_0007 : List Nat := [4, 5]
def grouped3_0008 : List Nat := [4, 5, 6, 7, 8]
def grouped3_0009 : List Nat := [5]
def grouped3_0010 : List Nat := [6]
def grouped3_0011 : List Nat := [6, 7, 8]
def grouped3_0012 : List Nat := [7]
def grouped3_0013 : List Nat := [7, 8]
def grouped3_0014 : List Nat := [8]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00030.record002 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00030.record002_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00030.record002" "{\"atoms\":[{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":102},{\"tag\":\"facet\",\"index\":103},{\"tag\":\"facet\",\"index\":104},{\"tag\":\"facet\",\"index\":105},{\"tag\":\"facet\",\"index\":106},{\"tag\":\"facet\",\"index\":107},{\"tag\":\"facet\",\"index\":108},{\"tag\":\"facet\",\"index\":109},{\"tag\":\"facet\",\"index\":110},{\"tag\":\"facet\",\"index\":111},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0004\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0007\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0011\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0011\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00030.record002" 57

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00030.record002" "{\"ridges\":[[11,530],[15,642],[16,770],[37,530],[42,642],[46,530],[51,642],[52,770],[55,530],[58,530],[59,530],[59,642],[60,530],[60,770],[62,770],[64,642],[65,770],[66,642],[66,770],[81,792],[83,904],[85,816],[87,848],[88,960],[101,344],[103,792],[104,456],[105,904],[106,368],[107,816],[109,848],[110,960],[111,216]],\"owners\":[[11,530,[97,102,103,107,108,109],[37,46,55,58,59,60]],[37,530,[102,103,107,108,109],[11,46,55,58,59,60,97]],[46,530,[97,107,108,109],[11,37,55,58,59,60,102,103]],[55,530,[97,102,103,108,109],[11,37,46,58,59,60,107]],[58,530,[97,102,103,107],[11,37,46,55,59,60,108,109]],[59,530,[103,107,109],[11,37,46,55,58,60,97,102,108]],[60,530,[97,102,108],[11,37,46,55,58,59,103,107,109]],[15,642,[97,102,105,108,110],[42,51,59,64,66]],[42,642,[102,105,108,110],[15,51,59,64,66,97]],[51,642,[97,108,110],[15,42,59,64,66,102,105]],[59,642,[105,110],[15,42,51,64,66,97,102,108]],[64,642,[97,102,105],[15,42,51,59,66,108,110]],[66,642,[97,102,108],[15,42,51,59,64,105,110]],[16,770,[103,105,107,109,110],[52,60,62,65,66]],[52,770,[107,109,110],[16,60,62,65,66,103,105]],[60,770,[105,110],[16,52,62,65,66,103,107,109]],[62,770,[103,105,109,110],[16,52,60,65,66,107]],[65,770,[103,105,107],[16,52,60,62,66,109,110]],[66,770,[103,107,109],[16,52,60,62,65,105,110]],[111,216,[78,100],[]],[101,344,[79],[]],[81,792,[103],[]],[103,792,[81],[]],[104,456,[82],[]],[83,904,[105],[]],[105,904,[83],[]],[106,368,[84],[]],[85,816,[107],[]],[107,816,[85],[]],[87,848,[109],[]],[109,848,[87],[]],[88,960,[110],[]],[110,960,[88],[]]],\"edges\":[[34,[11,37,46,55,58,59,60,75,80,81,85,86,87,97,102,103,107,108,109]],[43,[15,42,51,59,64,66,75,80,83,86,88,97,102,105,108,110]],[44,[16,52,60,62,65,66,81,83,85,87,88,103,105,107,109,110]]],\"groupings\":[3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00030.record002" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00030.record002\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-1,29,32,33,37,38,39],[-4,32,33,37,38,39],[-6,29,37,38,39],[-9,29,32,33,38,39],[-10,29,32,33,37],[-11,33,37,39],[-12,29,32,38],[-2,29,32,35,38,40],[-5,32,35,38,40],[-7,29,38,40],[-11,35,40],[-14,29,32,35],[-16,29,32,38],[-3,33,35,37,39,40],[-8,37,39,40],[-12,35,40],[-13,33,35,39,40],[-15,33,35,37],[-16,33,37,39],[-41,18,30],[-31,19],[-21,33],[-33,21],[-34,22],[-23,35],[-35,23],[-36,24],[-25,37],[-37,25],[-27,39],[-39,27],[-28,40],[-40,28],[-17,42],[-18,42],[-20,42],[-26,42],[-29,43],[-30,43],[-32,43],[-38,43],[-22,44],[-23,44],[-28,44],[-19,45],[-21,45],[-24,45],[-25,45],[-27,45],[-46,34,35,40],[-35,46],[-40,46],[-47,31,33,36,37,39],[-33,47],[-37,47],[-39,47],[-48,41],[-43,49],[-42,49],[-49,50],[-45,51],[-44,51],[-52,47,48],[-47,52],[-52,53],[-46,53],[-54,52],[-46,-52,54],[-51,-53,55],[-51,-54,56],[-56,57],[-50,-55,57],[-57],[1,4,6,9,10,11,12,17,20,21,25,26,27,29,32,33,37,38,39],[2,5,7,11,14,16,17,20,23,26,28,29,32,35,38,40],[3,8,12,13,15,16,21,23,25,27,28,33,35,37,39,40]],\"atoms\":[{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":102},{\"tag\":\"facet\",\"index\":103},{\"tag\":\"facet\",\"index\":104},{\"tag\":\"facet\",\"index\":105},{\"tag\":\"facet\",\"index\":106},{\"tag\":\"facet\",\"index\":107},{\"tag\":\"facet\",\"index\":108},{\"tag\":\"facet\",\"index\":109},{\"tag\":\"facet\",\"index\":110},{\"tag\":\"facet\",\"index\":111},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"mate\",\"ridge\":530,\"a\":11,\"owners\":[97,102,103,107,108,109]},{\"tag\":\"mate\",\"ridge\":530,\"a\":37,\"owners\":[102,103,107,108,109]},{\"tag\":\"mate\",\"ridge\":530,\"a\":46,\"owners\":[97,107,108,109]},{\"tag\":\"mate\",\"ridge\":530,\"a\":55,\"owners\":[97,102,103,108,109]},{\"tag\":\"mate\",\"ridge\":530,\"a\":58,\"owners\":[97,102,103,107]},{\"tag\":\"mate\",\"ridge\":530,\"a\":59,\"owners\":[103,107,109]},{\"tag\":\"mate\",\"ridge\":530,\"a\":60,\"owners\":[97,102,108]},{\"tag\":\"mate\",\"ridge\":642,\"a\":15,\"owners\":[97,102,105,108,110]},{\"tag\":\"mate\",\"ridge\":642,\"a\":42,\"owners\":[102,105,108,110]},{\"tag\":\"mate\",\"ridge\":642,\"a\":51,\"owners\":[97,108,110]},{\"tag\":\"mate\",\"ridge\":642,\"a\":59,\"owners\":[105,110]},{\"tag\":\"mate\",\"ridge\":642,\"a\":64,\"owners\":[97,102,105]},{\"tag\":\"mate\",\"ridge\":642,\"a\":66,\"owners\":[97,102,108]},{\"tag\":\"mate\",\"ridge\":770,\"a\":16,\"owners\":[103,105,107,109,110]},{\"tag\":\"mate\",\"ridge\":770,\"a\":52,\"owners\":[107,109,110]},{\"tag\":\"mate\",\"ridge\":770,\"a\":60,\"owners\":[105,110]},{\"tag\":\"mate\",\"ridge\":770,\"a\":62,\"owners\":[103,105,109,110]},{\"tag\":\"mate\",\"ridge\":770,\"a\":65,\"owners\":[103,105,107]},{\"tag\":\"mate\",\"ridge\":770,\"a\":66,\"owners\":[103,107,109]},{\"tag\":\"mate\",\"ridge\":216,\"a\":111,\"owners\":[78,100]},{\"tag\":\"mate\",\"ridge\":344,\"a\":101,\"owners\":[79]},{\"tag\":\"mate\",\"ridge\":792,\"a\":81,\"owners\":[103]},{\"tag\":\"mate\",\"ridge\":792,\"a\":103,\"owners\":[81]},{\"tag\":\"mate\",\"ridge\":456,\"a\":104,\"owners\":[82]},{\"tag\":\"mate\",\"ridge\":904,\"a\":83,\"owners\":[105]},{\"tag\":\"mate\",\"ridge\":904,\"a\":105,\"owners\":[83]},{\"tag\":\"mate\",\"ridge\":368,\"a\":106,\"owners\":[84]},{\"tag\":\"mate\",\"ridge\":816,\"a\":85,\"owners\":[107]},{\"tag\":\"mate\",\"ridge\":816,\"a\":107,\"owners\":[85]},{\"tag\":\"mate\",\"ridge\":848,\"a\":87,\"owners\":[109]},{\"tag\":\"mate\",\"ridge\":848,\"a\":109,\"owners\":[87]},{\"tag\":\"mate\",\"ridge\":960,\"a\":88,\"owners\":[110]},{\"tag\":\"mate\",\"ridge\":960,\"a\":110,\"owners\":[88]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":75,\"full_literals\":[-17,42]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":78,\"full_literals\":[-18,42]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":80,\"full_literals\":[-20,42]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":86,\"full_literals\":[-26,42]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":97,\"full_literals\":[-29,43]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":100,\"full_literals\":[-30,43]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":102,\"full_literals\":[-32,43]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":108,\"full_literals\":[-38,43]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":82,\"full_literals\":[-22,44]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":83,\"full_literals\":[-23,44]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":88,\"full_literals\":[-28,44]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":79,\"full_literals\":[-19,45]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":81,\"full_literals\":[-21,45]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":84,\"full_literals\":[-24,45]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":85,\"full_literals\":[-25,45]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":87,\"full_literals\":[-27,45]},{\"tag\":\"group_or\",\"kind\":3,\"index\":6,\"members\":[104,105,110],\"full_literals\":[-46,34,35,40]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":105,\"full_literals\":[-35,46]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":110,\"full_literals\":[-40,46]},{\"tag\":\"group_or\",\"kind\":3,\"index\":7,\"members\":[101,103,106,107,109],\"full_literals\":[-47,31,33,36,37,39]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":103,\"full_literals\":[-33,47]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":107,\"full_literals\":[-37,47]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":109,\"full_literals\":[-39,47]},{\"tag\":\"group_or\",\"kind\":3,\"index\":8,\"members\":[111],\"full_literals\":[-48,41]},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0003\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0004\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-43,49],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0003\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0004\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-42,false,49],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-49,50],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0006\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0007\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-45,51],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0006\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0007\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-44,false,51],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-52,47,48],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-47,false,52],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0011\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-52,53],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0011\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-46,false,53],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0011\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-54,false,52],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0011\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-46,-52,54],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0008\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-51,-53,55],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0008\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-51,-54,56],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"groupKind3\",\"a\":0,\"b\":3,\"direction\":\"forward\",\"full_literals\":[false,-56,57],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-50,-55,57],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":34,\"owners\":[11,37,46,55,58,59,60,75,80,81,85,86,87,97,102,103,107,108,109]},{\"tag\":\"edge\",\"edge\":43,\"owners\":[15,42,51,59,64,66,75,80,83,86,88,97,102,105,108,110]},{\"tag\":\"edge\",\"edge\":44,\"owners\":[16,52,60,62,65,66,81,83,85,87,88,103,105,107,109,110]}]}"
  "77 -56 0 73 71 0\n78 -54 48 0 77 67 70 63 61 45 46 47 48 49 21 23 27 29 31 53 0\n79 46 49 0 58 41 38 40 13 59 37 36 34 51 52 25 9 8 12 32 11 10 75 0\n80 49 0 58 59 38 39 40 41 34 35 36 37 20 7 57 78 79 68 64 54 55 56 22 2 1 4 5 28 6 3 30 74 0\n81 50 0 80 60 0\n82 -55 0 81 73 72 0\n83 -46 0 82 66 69 62 42 43 44 24 26 33 50 0\n84 -35 0 83 51 0\n85 -40 0 83 52 0\n86 -23 0 84 25 0\n87 -28 0 85 32 0\n88 -12 0 85 84 16 0\n89 47 0 84 86 85 88 87 54 55 56 22 14 17 18 28 19 30 15 76 0\n90 52 0 89 64 0\n91 53 0 90 65 0\n92 -51 0 91 82 69 0\n93 -45 0 92 61 0\n94 -19 0 93 45 0\n95 -21 0 93 46 0\n96 -24 0 93 47 0\n97 -25 0 93 48 0\n98 -27 0 93 49 0\n99 -31 0 94 21 0\n100 -33 0 95 23 0\n101 -36 0 96 27 0\n102 -37 0 97 29 0\n103 -39 0 98 31 0\n104 0 103 102 99 100 101 89 53 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00030.record002.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00030.record002.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00030.record002.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00030.record002.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00030.record002 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00030.record002.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00030.record002.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00030.record002.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00030.record002.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00030.record002 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00030.record002_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00030.record002_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00030.record002_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00030.record002_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00030.record002_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00030.record002_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00030.record002_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00030.record002 Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00030.record002_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00030.record002_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00030.record002_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00030.record002
