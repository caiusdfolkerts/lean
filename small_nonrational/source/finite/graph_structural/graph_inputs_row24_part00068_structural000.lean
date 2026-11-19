module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow24Part00068Data
public import GraphInputsRow24Part00068Frames
public import GraphInputsRow24Part00068Leaves
public import GraphInputsRow24Part00068Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00068.record002
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00068.record002
def vertexColumn : Fields := ⟨10, hexnat% "2d4970bab18e6358b69391e1783eb46a9a66592e6c5a94e5a5655354b5c364d8b61d4745d0f6c368ce32ce8b92cab46c9b16c3ba1e4751cc729c6745c970de0f13d2c3492a498564382e07ac134529915251560d4342d074c348ca324c5342c2b06d0711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "db6d36924db69b69349249249369249a492492449249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨66, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨77, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "260420c039ff80000000", hexnat% "1000022040000000000", 3448068464705536, 1080863910568919040, hexnat% "800010000000000000", 4611686018427387904]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "70000ea7dff80000000", hexnat% "800014000000000000", hexnat% "20042000000000000000", 1080863910568919040, 4611686018427387904]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2300003e5c6e00000000", hexnat% "4000080200180000000", hexnat% "846000000000000000", 1717986918400, 1098878309078401024]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [4011267526230016, 65987877535744, hexnat% "7000000000080000000", hexnat% "842010004000000000", hexnat% "20000000000000000000", 4611687667694829568, 1143914309647073280]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c4 c1
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c5 c0
  c6
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00068.record002_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00068.record002_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00068.record002_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00068.record002_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00068.record002_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00068.record002_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00068.record002_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00068.record002_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00068.record002_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00068.record002

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00068.record003
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00068.record003
def vertexColumn : Fields := ⟨10, hexnat% "2d2aaa9a968ba398d62da4e4785e0fad1aa699964b9394d52d64d4745d0f6a368ce3a4e532cf0ba2e4b8acab86d1b26c5b0ee4751cc729c6745c970de0f13d2cb08d24a9261590e0b81eb04d14a5251550d0b41da0e4330d2328c9314e0b42c2b06d0711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "9b6da6d249b6da6d2492492492492492492491249249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2, 3]
def candidates : List (Fin raw.n) := [⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7ffffd5fffdbe00000000", 2473901162496, 144115188075855872, 2882303761517117440]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 3 [hexnat% "7fffffffffffe00000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨74, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .size 3
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ffbffdfffd3e00000000", hexnat% "400400000000000000000", 3023656976384, 144115188075855872]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨64, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ff3ffdfffd3e00000000", hexnat% "400400000000000000000", hexnat% "800000000000000000", 3023656976384, 144115188075855872]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨64, by decide⟩ c6 c3
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨73, by decide⟩ c7 c5
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fc3ec7fff8fc00000000", hexnat% "400400000010000000000", 6605659701248, 4035225266123964416, hexnat% "10000000000000000", hexnat% "3800000000000000000"]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨76, by decide⟩ c10 c2
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fd3fd0f6fffe00000000", 2882303761517117440, hexnat% "400400100000000000000", hexnat% "2800000000000000000", 290763650942107648, 144115188075855872]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7fd7fd5e0fbfa00000000", 144959613005987840, 3382114946908160, 2882303761517117440, hexnat% "2800000000000000000", 4503599627370496]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ef3ef4defd3600000000", hexnat% "410000000000000000", hexnat% "410000000000000000000", 3058016714752, hexnat% "800820000000000000", 216454257090494464]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fc3fc044311000000000", 4035225274713899008, hexnat% "400400080800000000000", hexnat% "3800000000000000000", 7679006388256768, 7043746365440, 513410907276050432]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c15 c14
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c16 c13
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c17 c12
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c18 c11
  c19
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00068.record003_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00068.record003_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00068.record003_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00068.record003_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00068.record003_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00068.record003_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00068.record003_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00068.record003_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00068.record003_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00068.record003

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00068.record005
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00068.record005
def vertexColumn : Fields := ⟨10, hexnat% "2d4370bcb4ac6a9a96958d62da4e4785e0fad13a4d92e6c5a95a5a5655354b5934cd2b51d2745d0f6c3a8ce3a4e5334cb392d4b1ad1b0ef07a1e4731e2729e1745c9715c3783c4f4b12a169264382e07ac13452916685494a52550d0b41d90d2314d0b12c2b06e0741c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "db6db6db49269a49349b49249b693492492692492489249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨70, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "55ac346810640000000", hexnat% "40880002100000000", hexnat% "a000000000080000000", 131941395333120, 288230410511450112, 6940667150336]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [9223644718959689728, hexnat% "1400006000000000000", hexnat% "e000000000000000000", hexnat% "e4800002000000000", hexnat% "100040030000000000", 540431972464328704, 4788888535040]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c1 c0
  c2
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00068.record005_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00068.record005_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00068.record005_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00068.record005_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00068.record005_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00068.record005_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00068.record005_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00068.record005_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00068.record005_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00068.record005

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00068.record008
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00068.record008
def vertexColumn : Fields := ⟨10, hexnat% "4f0f2b29aa968da4e8ba399361da4e3392e2b91e1783e3c6c96a659365392e4e54d475934cd4b4ad4745d0f6a368ce394cd34ccb31cf0b62e4b32d2b2ae1b46c9b16c3b91d4731ca719d1783c8f13c2fb0a8a498560d90e07ac1a2525154354341da0e4330d2328c530ce0b42c8b06d0711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "1b4db6da4da69269b6db49b4d2492492492492492492492489249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨63, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨74, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨80, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨91, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "80024001001820080000000", hexnat% "800040108000800000000", hexnat% "110008800610040000000", 54044157601120256, 445856431829155840, hexnat% "1040082000080400000000", 1710852977721344]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00068.record008_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00068.record008_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00068.record008_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00068.record008_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00068.record008_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00068.record008_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00068.record008_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00068.record008_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00068.record008_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00068.record008
