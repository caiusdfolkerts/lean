module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow24Part00003Data
public import GraphInputsRow24Part00003Frames
public import GraphInputsRow24Part00003Leaves
public import GraphInputsRow24Part00003Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00003.record000
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record000
def vertexColumn : Fields := ⟨10, hexnat% "f132c4f2ca6a8dab18764b83ef06c9ca5a9964d94e785d16c571725955351d70d8b52d8751d0f6c368cd31ce8b62e4b32d2b2ac9b16e8761e4731d2719e0f43c2f07f880e8560db81b0709a25894a439c1645494550d4c314c3322c2b06c4709c17"⟩
def kindColumn : Fields := ⟨3, hexnat% "1b6db69a4926d249a49269b49a4934924da493691249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨25, by decide⟩, ⟨26, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨50, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨70, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "502074887066000000", hexnat% "21100000000000000", hexnat% "10000060000000000", 18178449080320, 900719929769066496, hexnat% "c0000400000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1f3d14def9a6000000", hexnat% "400020000000000000", 18014399583223808, 36028797018963968]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "5b1934d8b9a6000000", hexnat% "40000060000000000", 324259173170675712, 2305843284091600896, 18014399583223808]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1f3d14d6f806000000", 27021599374835712, hexnat% "400000080000000000", 36028803461414912]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1f3df4d4a1e6000000", hexnat% "400000080000000000", 103079215104, 2473901162496]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1f3d54d4e186000000", 8899172237312, 45035996810575872, 2200096997376, hexnat% "400000000000000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1b3914d06006000000", hexnat% "400020080020000000", 18014399583223808, 324259179613126656, hexnat% "40000008800000000", 6665789243392]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c9 c4
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c10 c3
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "5000f4880166000000", 1801439850948198400, 18178449080320, hexnat% "32000004000000000", hexnat% "c0400400000000000", 6803228196864]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7207486f044000000", 26422672359424, 1801439850948198400, hexnat% "80400400000000000", hexnat% "500000000000000000", 36028803998285824]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "5034f4dac9e6000000", 4604204941312, 648518346341351424, hexnat% "30000000000000000", hexnat% "c0000000000000000"]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "81cb0da89a4000000", hexnat% "40000040000000000", hexnat% "500000000002000000", 91197893527994368, 481036337152, hexnat% "32000000000000000"]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c15 c14
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "5020748a40e6000000", hexnat% "21100000000000000", hexnat% "10000042000000000", 900719929769066496, 18245021073408, hexnat% "c0000400000000000"]
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "5000f49a01e6000000", 790273982464, 1801439850948198400, hexnat% "c0400400000000000", hexnat% "32000004000000000", 4398046511104]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [914373667914252288, hexnat% "500000080002000000", 91197893527994368, hexnat% "21000000000000000", hexnat% "12000006000000000", hexnat% "c0000440000000000", 18245021073408]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c19 c18
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c20 c17
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c21 c16
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c22 c13
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c23 c12
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨52, by decide⟩ c24 c11
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c25 c0
  c26
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record000_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record000_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record000_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record000_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record000_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record000_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record000_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record000_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record000_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00003.record000

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00003.record015
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record015
def vertexColumn : Fields := ⟨10, hexnat% "e8b524eac6699964d8ae1b83ee87514e6c5695954d4ad1b43dd0ec3c8ea3c4d9394d534ce4b4acab1ad1b0ee8761e4731d2719d1725c3723c5ce09a2168a61584e0b81ee05a1164a51544d0b41dc0e8360e4348ca344c5312c2b06c8711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "136d36924db4da492492492492492492491249249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨63, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨73, by decide⟩, ⟨77, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20083fefffe00000000", 281474976710656, hexnat% "20080000000000000000", 2017612633061982208, hexnat% "700000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "220880fe1efe00000000", 246290604621824, hexnat% "100400000000000000", 216455356602122240, 1729382256910270464, hexnat% "600000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2701ebf597e00000000", 175921860444160, hexnat% "88040020000000000", hexnat% "20000000000000000000", 72062541840252928]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "709ebf597e00000000", 175921860444160, hexnat% "20080040020000000000", hexnat% "2000000000000000000", 72062541840252928]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "5016bf191e00000000", 90079139372990464, hexnat% "20080000000000000000", 246702921482240, hexnat% "200800000000000000", hexnat% "2008000000000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨70, by decide⟩ c6 c3
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "10077ffffe00000000", hexnat% "200800000000000000", hexnat% "20080080000000000000", 10376293541461622784, hexnat% "2400000000000000000"]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [242472816782344192, hexnat% "20080080000000000000", 2017612633061982208, hexnat% "2008000004000000000", hexnat% "700000000000000000", 9728478882562048]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "24091fffffe00000000", 144115188075855872, 864691128455135232, hexnat% "20080000000000000000", hexnat% "300000000000000000"]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "200814d47fe00000000", 194217733930352640, 2017612633061982208, hexnat% "20080000000000000000", hexnat% "700000000000000000", 202310139510784]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c12 c11
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [69522111634341888, hexnat% "20080000020000000000", 218706056904179712, 2017612633061982208, hexnat% "2008000000000000000", hexnat% "700000000000000000"]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "27893edc7f600000000", 4521226173153280, 576495936675512320, hexnat% "20000000000000000000", 288802122198155264]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "27013ffd5fe00000000", 864691128455135232, hexnat% "88000020000000000", hexnat% "20000000000000000000", 43980465111040]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "27013bed7fe00000000", 864691128455135232, hexnat% "88040000000000000", hexnat% "20000000000000000000", 325455441821696]
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2701f24c4f600000000", hexnat% "88040020000000000", 2569558674112512, 4521226173153280, 571746046443520, hexnat% "20000080000000000000"]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c18 c17
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c19 c16
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c20 c15
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "5007bffffe00000000", hexnat% "200800000000000000", 10376293541461622784, hexnat% "20080040000000000000", hexnat% "2000000000000000000"]
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "709fbedef600000000", 1133871366144, 316659348799488, hexnat% "20080040000000000000", hexnat% "2000000000000000000"]
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4013bfbff000000000", hexnat% "20080040000000000000", hexnat% "100400000600000000", hexnat% "2008000400000000000", 34359738368, hexnat% "200800000000000000"]
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c24 c23
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c25 c22
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "600824a4b200000000", hexnat% "200800d0020000000000", hexnat% "100402080400000000", hexnat% "2008000404000000000", 218707156415807488, 17626545782784, 1152921504606846976]
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c27 c26
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨70, by decide⟩ c28 c21
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c29 c14
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c30 c13
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c31 c10
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c32 c7
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c33 c2
  c34
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record015_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record015_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record015_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record015_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record015_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record015_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record015_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record015_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record015_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00003.record015

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00003.record039
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record039
def vertexColumn : Fields := ⟨10, hexnat% "6b07c6a93a1eac669876638ce4b8ae1b89e1783ee2749b25a94e479b15a51d58d3352d2b46d27743b0f2368e534cc7362d4b32d2b2ac6b46c9b16c3ba1d8791cc749ca719c9743c8f13c2f07c5c0f38215836e05894a4590e4550d48d1342d07703a0d8390d2314c3321c4709c17"⟩
def kindColumn : Fields := ⟨3, hexnat% "69b6da6db6d24da49b49249249249369b6d2492492692449249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨46, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨80, by decide⟩, ⟨86, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "410094adfe43ff08000000", hexnat% "81000000010000000", 4755801207576985600, hexnat% "3000000000020000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "41000485fc032b08000000", hexnat% "904002000000000000", hexnat% "81000400010000000", hexnat% "3000000000060000000", 910533066752, 3026418949592973312]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "394a9fe43fc78000000", hexnat% "81400000000000000", hexnat% "100000000000300000000", 4755801206503243776, hexnat% "4000000000000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "394d07e437f78000000", 108086940812705792, hexnat% "4100000400000000000000", hexnat% "80800000000000000", 2449958197289549824]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "30481f6432878000000", hexnat% "904000000000000000", hexnat% "80008000000000000", hexnat% "4100000400000200000000", 914828034048, 4179340454199820288]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c6 c3
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "904006020000000000", 112590128123215872, 29343800681824256, hexnat% "c1000010000000000", hexnat% "4103008000000008000000", 924491710464, 3314649326549991424]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c9 c2
  c10
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record039_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record039_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record039_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record039_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record039_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record039_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record039_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record039_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record039_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00003.record039

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00003.record062
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record062
def vertexColumn : Fields := ⟨10, hexnat% "7331c8f1caa6a3a718766394e3383ef0761b85c9c66998e5c5c9565c56351d70d6354d3362d8751d0f5c3a8ce3a4e331ce8b62d4b32e2b86c9b0ed8751cc715d0f23c4f0bf881983607b8170631c268962619514650d50d074c318c3322c1b11c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "6db6da6da4da49269a4926d249a6924d3493492491249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨37, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨44, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨58, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨72, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "9907151a058000000", 288230378903175168, 4612249019920416768, hexnat% "1100000000002000000", 108092988126658560, 2305983755291983872]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "19e163c7aeba000000", hexnat% "1000080000000000000", 17593326895104, 1445655480385929216]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "11021a2868e2a000000", 13835059154793791488, hexnat% "91000400000000000", 17730765848576, 22799473381998592, 288230378299195392]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "11f17385ae7e000000", hexnat% "80000400000000000", hexnat% "1000080020000000000", 17594333528064, 288230376151711744]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "11031a387ae7e000000", 292733977926565888, 13853072453791645696, hexnat% "90000400000000000", 17592186044416]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "110302181ae7e000000", hexnat% "90000400000000000", 108092988126658560, 17594333528064, 292733975779082240, 13853635403745067008]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨61, by decide⟩ c7 c4
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "11021a3860a3a000000", 13853072453791645696, hexnat% "91000400000000000", 1803886264320, 292733977993674752, 17593259786240]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "95470c1a698000000", 17593863766016, 9224216496144646144, hexnat% "1100000000002000000", 108092988126658560, 2305843009213693952]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "10e12285ae0a000000", hexnat% "91000400000000000", hexnat% "1000080020020000000", 22799473381998592, 17595474378752, 288230376151711744]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "9f173c08218000000", 5531917877248, hexnat% "1100000000022000000", 154685931520, 324259175318159360, 19792283041792]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [16168909672017821696, hexnat% "1100000000020000000", 108092988126658560, hexnat% "91000400000000000", 17595407269888, 292733975779082240]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "93060c08608000000", hexnat% "1100000000022000000", 108092988126658560, 13835059189153529856, 844425198567424, 17730765848576, 292733977926565888]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c14 c13
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c15 c12
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨61, by decide⟩ c16 c11
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c17 c10
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c18 c9
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c19 c8
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c20 c3
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c21 c0
  c22
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record062_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record062_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record062_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record062_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record062_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record062_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record062_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record062_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record062_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00003.record062
