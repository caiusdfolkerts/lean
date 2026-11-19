module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow24Part00157Data
public import GraphInputsRow24Part00157Frames
public import GraphInputsRow24Part00157Leaves
public import GraphInputsRow24Part00157Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00157.record002
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00157.record002
def vertexColumn : Fields := ⟨10, hexnat% "2745b25c3707c9ca5a4e87a99a9695a362d87663a4e4b86e8789e1783e9c569964d94e47999565a5655356352d4756364d534cd4b46d8749d1743d98e9394e334ccb31cd8b92d2b1ae1b46c5b0ef07a1d8791e2729c6785c9715c3783c4f0bc1f269264388e9447126459915251950d2344d48e1324c3342c8b06e0741c8709c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "db6db6db6db4d369b4d269269b69249269369249269a492492492692489249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2, 3]
def candidates : List (Fin raw.n) := [⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩, ⟨95, by decide⟩, ⟨96, by decide⟩, ⟨97, by decide⟩, ⟨98, by decide⟩, ⟨99, by decide⟩, ⟨100, by decide⟩, ⟨101, by decide⟩, ⟨102, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7fffdfffff5f9bfffffc000000", hexnat% "2000002000000000000000", 28147497671065600, 9223372036854775808]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7fffffeffffffffe77fc000000", hexnat% "10000000000000000000", 1683627180032]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 3 [hexnat% "7ffffffffffffffffffc000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨95, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7fffdfffff5fa3fe57fc000000", 11529215046068469760, hexnat% "2000000000010000000000", 721554505728, 25895697857380352]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c5 c0
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7fff5ffffd5f83a007c4000000", hexnat% "2a000000018000000", hexnat% "a000000000004000000000", 2333163674140672, 32673087530991616, 1890322481152]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c7 c6
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7fff5f49fc0fdfffdffc000000", hexnat% "a000000000000000000000", 9007336693694464, hexnat% "b4000000000000000000", hexnat% "2f000000000000000", hexnat% "2010000000000000000"]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7fffff4dfefff5f3fffc000000", 2260595906707456, hexnat% "2010000000000000000", hexnat% "a0000002040000000000", hexnat% "10000000000000000000"]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7fff5f5bfffff4b3fffc000000", hexnat% "a000000000000000000000", 360639813910528, 2814749767106560, hexnat% "a4000000040000000000"]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7fff5f48fc6ffcfbfbec000000", hexnat% "a000000000000000000000", hexnat% "3019000000000000000", hexnat% "b4000000040000000000", hexnat% "20001000010000000", 562967133290496]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨62, by decide⟩ c12 c11
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨61, by decide⟩ c13 c10
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7fffdbecffc9fffffffc000000", hexnat% "10000600000000000000", hexnat% "400000000000000000000", hexnat% "3001000000000000000", hexnat% "2000002000000000000000"]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7fffdb69bff9a1b9fffc000000", hexnat% "400400600000000000000", hexnat% "2004000000420000000000", 26458647810801664, hexnat% "82000000000000000000", hexnat% "10000000040000000000"]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c16 c15
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7fff5bffbc4ffebffffc000000", hexnat% "8400000001000000000000", hexnat% "2000003000400000000000", hexnat% "38000000000000000", hexnat% "400000000000000000"]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7fffdfdbbc0999a1fffc000000", hexnat% "2004003000420000000000", 19171084741902336, hexnat% "2c600000000000000", hexnat% "20000022000000000000", hexnat% "410000000000000000"]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨76, by decide⟩ c19 c18
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .size 3
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .size 2
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨82, by decide⟩ c22 c21
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨85, by decide⟩ c22 c23
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨73, by decide⟩ c24 c24
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7fffdbfcfffffffefefc000000", hexnat% "3000000000000000000", hexnat% "400000000000100000000", hexnat% "2000000000010000000000"]
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c26 c25
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7fffdbefffffffb676fc000000", hexnat% "10000000080000000000", hexnat% "400000000000100000000", hexnat% "2000000000410000000000", 584115552256]
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c28 c27
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7fff5becfe09fefe36f8000000", hexnat% "10004600000004000000", 1962800054272, hexnat% "3019000000000000000", hexnat% "8400000001000000000000", hexnat% "2000002000000000000000"]
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨65, by decide⟩ c30 c29
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7fffdbfcbfffffbe76fc000000", hexnat% "3000000000000000000", hexnat% "400400000000100000000", hexnat% "2000000000410000000000", 584115552256]
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7fff5bffbffffeb63efc000000", 360639813910528, hexnat% "400400000000100000000", 1924145348608, hexnat% "a000000000000000000000"]
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7fff5bfcbe49febe36f4000000", 1962934272000, hexnat% "3019000000000000000", hexnat% "8400000001000000000000", hexnat% "2000002000400000000000", hexnat% "400600000000000000"]
  let c35 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨62, by decide⟩ c34 c33
  let c36 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨65, by decide⟩ c35 c32
  let c37 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7fffdb4bbfffa3adfefc000000", hexnat% "400400000000100000000", hexnat% "2004000000420000000000", hexnat% "b0000000000000000000", 25913290043424768]
  let c38 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7fffdf48ffffa3a053fc000000", hexnat% "3000000000400000000", hexnat% "2000000000410000000000", 721554505728, hexnat% "b4000000040000000000", 25924285159702528]
  let c39 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7fff5bffbfffaabffefc000000", hexnat% "2000000000400000000000", hexnat% "400400000000100000000", 23643898043695104, hexnat% "8000000001000000000000"]
  let c40 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7fff5b5bbfffaaa5fefc000000", hexnat% "a000000000000000000000", hexnat% "a4400000000000000000", 362838837166080, 23661494524706816, hexnat% "400000000000000000000"]
  let c41 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨76, by decide⟩ c40 c39
  let c42 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7fffff48fe0ff7b3dffc000000", 2330964650885120, 4535485464576, hexnat% "100b000000000000000", hexnat% "b4000000000000000000", hexnat% "2014000000000000000"]
  let c43 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7fff5bffbffff7be3ffc000000", 2322168557862912, hexnat% "400400000000000000000", 1924145348608, hexnat% "a000000000000000000000"]
  let c44 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7fff5ffdfe0ff7be37f4000000", 2251834307641344, 1924145348608, hexnat% "a000000000000000000000", hexnat% "201d000000000000000", 2305913377957871616]
  let c45 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨72, by decide⟩ c44 c43
  let c46 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7fffffeeff3ffffff7fc000000", hexnat% "1000000000800000000", hexnat% "10004000000000000000", 9223372036854775808]
  let c47 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7ffffffeff7febff77fc000000", 584115552256, 5629499534213120, hexnat% "1008000000000000000"]
  let c48 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7ffffffeff3febef77fc000000", 584115552256, 13835058055282163712, 5647091720257536, hexnat% "1000000000000000000"]
  let c49 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨76, by decide⟩ c48 c47
  let c50 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c49 c46
  let c51 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7fffffeeff3ffefffffc000000", 281474976710656, hexnat% "1008000000000000000", hexnat% "10004000000000000000"]
  let c52 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7ffffffeff7ffbff77fc000000", 584115552256, 1125899906842624, hexnat% "1008000000000000000"]
  let c53 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7ffffffeff3ffae7fffc000000", 13835058055282163712, 307863255777280, hexnat% "1000000000000000000", 1125899906842624]
  let c54 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨76, by decide⟩ c53 c52
  let c55 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c54 c51
  let c56 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c55 c46
  let c57 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨93, by decide⟩ c21 c56
  let c58 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7ffffffeff3feaf7fffc000000", 290271069732864, 13835058055282163712, 5629499534213120, hexnat% "1000000000000000000"]
  let c59 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨76, by decide⟩ c58 c47
  let c60 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c59 c51
  let c61 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c60 c46
  let c62 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨86, by decide⟩ c21 c61
  let c63 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨96, by decide⟩ c2 c62
  let c64 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨97, by decide⟩ c63 c57
  let c65 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7fffffeeff1fa3e477fc000000", 16140901064495857664, hexnat% "1000000000800000000", hexnat% "100000001a0000000000", 1649267441664, 25895697857380352]
  let c66 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨85, by decide⟩ c65 c64
  let c67 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c66 c50
  let c68 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7fffdf48fe09a3a417f4000000", hexnat% "b4000200000000000000", 2096078258176, 14123288431433875456, hexnat% "3011000000000000000", 25924285159702528, hexnat% "2000002000400000000000"]
  let c69 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨70, by decide⟩ c68 c67
  let c70 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c69 c45
  let c71 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c70 c42
  let c72 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c71 c41
  let c73 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨65, by decide⟩ c72 c38
  let c74 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c73 c37
  let c75 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c74 c36
  let c76 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c75 c31
  let c77 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c76 c20
  let c78 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c77 c17
  let c79 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c78 c14
  let c80 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c79 c9
  let c81 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨66, by decide⟩ c80 c8
  c81
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00157.record002_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00157.record002_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00157.record002_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00157.record002_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00157.record002_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00157.record002_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00157.record002_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00157.record002_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00157.record002_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00157.record002
