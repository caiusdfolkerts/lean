module
prelude
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow24Part00168Data
public import GraphInputsRow24Part00168Frames
public import GraphInputsRow24Part00168Leaves
public import GraphInputsRow24Part00168Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00168.record002
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record002
def vertexColumn : Fields := ⟨10, hexnat% "c70f23ab168d9362d876c38ae1b8e9c669966659564d9c56354d4b51d70d2b46d8751d2745dc4e9364e5354cd38cd332cc73c2e8b62e4b52cab1af0789d2729c6785d1725c570dc8f13c2f3c0e232a0e438e1344b11c4c9855150d60d434c328c6382d0b22c4b81d0709c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "1a4db6d369b6da49249b49b6db69b4924924924926d2489249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨50, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨74, by decide⟩, ⟨77, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "100c00000000000000", hexnat% "1804000004000000000000", hexnat% "20084000204000000000", 34635086036992, hexnat% "78000000020000000", 257698037760, 211119117434880]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record002_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record002_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record002_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record002_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record002_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record002_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record002_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record002_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record002_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00168.record002

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00168.record004
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record004
def vertexColumn : Fields := ⟨10, hexnat% "f83d31ca719c2f0eac6a9a668dac5a9665a56558d6c3a8e63a2e4b8ae8791e278f13a719364b91e4e5c5655554d52d475c362d4b4ad8751d2743d38f1394d5334f0b32e2b4acab1ae1b46c9b16f0791d4731e2749ca785d1725c5783d0f23c2f07ce4350e22a8c62986686519196154545518e0b42c2b81d0711c27"⟩
def kindColumn : Fields := ⟨3, hexnat% "d36da6db6db69b6da6db69b69249a6db49b4db69a4924da492492692699249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨46, by decide⟩, ⟨51, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨60, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨70, by decide⟩, ⟨76, by decide⟩, ⟨82, by decide⟩, ⟨92, by decide⟩, ⟨97, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "100010000008040040000000", hexnat% "2000400044000000200000000", hexnat% "400000418000000000", 28587306516480, hexnat% "39000000004000000", 54043195578777600, 127506841600]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record004_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record004_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record004_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record004_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record004_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record004_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record004_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record004_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record004_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00168.record004

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00168.record005
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record005
def vertexColumn : Fields := ⟨10, hexnat% "f83d31c3ab1aa699a368e6c5a56558d6c3a2e4ba1e478f13a719a6599364b91e4e5c5655554d52d475c362d4b61d4743dc4e9364e5354cd3c2e8b62ccb8ad2b1ae1b46c9b16f0791d4731e2749ca785d1725c5783d0f0bc1f388aa198e1344a9865192646585515154c328c6382d0b22c2b81d0711c27"⟩
def kindColumn : Fields := ⟨3, hexnat% "db4db69b6db6da49249a49269b6936db69249249269249249a493249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨62, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨86, by decide⟩, ⟨91, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "70e0607b700d8000000", hexnat% "18c00000400000000000", hexnat% "84000000000080100000000", 506906804224, hexnat% "114000000800000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "70e0607b700d4000000", hexnat% "18c00000400000000000", hexnat% "84000000000080100000000", 506973913088, hexnat% "114000000800000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "840189140044e7f10000000", hexnat% "e00000000c0000000", 1037939211501568, hexnat% "7400000010000000000", 432345564227567616]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "840040800020e7fde000000", hexnat% "60600000000000000", 546457279004672, hexnat% "10114000000000000000", hexnat% "8800004000000000000", hexnat% "3400000000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8401fd100044f4900000000", 1037939211501568, hexnat% "e4000000010000000", 432345564227567616, 235149459456]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "840008000000e4900000000", hexnat% "7400000010000000000", hexnat% "18100004000000000000", hexnat% "f4000000010000000", 432345564462448640, 235149459456, 1108307720798208]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨71, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c6 c3
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c7 c2
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c8 c1
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c9 c0
  c10
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record005_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record005_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record005_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record005_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record005_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record005_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record005_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record005_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record005_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00168.record005

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00168.record006
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record006
def vertexColumn : Fields := ⟨10, hexnat% "3d0ecc729c670f23ab1aa699a39b16a599695956358b61db0ea398e33a2e4b8ae1ba1e4789e3c4e9c64e5c5655554d52d475c34cd8b52d2b46d8751d274e3c4e5354cd32cc73c2ccb8ad2b2ac6b86d1b26f0791d4731e2749ca719e1745c9715c3783d0f23c4f0bc1f390d42b0e2348aa19615454558350d0b46384d1314e0b42c2b"⟩
def kindColumn : Fields := ⟨3, hexnat% "49b6936d36db4db6db69b6db69249a4d249269249a4d24926db6db4934d26d3249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨21, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨27, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨78, by decide⟩, ⟨87, by decide⟩, ⟨93, by decide⟩, ⟨97, by decide⟩, ⟨98, by decide⟩, ⟨102, by decide⟩, ⟨103, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2080403803380300eb200000", 206708186021888, hexnat% "84000000010001000000000000", 13546827679130451968, hexnat% "42000000000000000000000000", hexnat% "440044000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "840080007d0845080068000000", 15765897230680064, hexnat% "42200040000000000000000000", 12898309332789100544, 288234776347803648, 193514096820224]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "842080403d003d0000eb200000", 216176080648667136, hexnat% "400840080000000000", hexnat% "42000000000400040000000000", 193514046488576, 12682136550675316736]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20804004b300b300eb200000", hexnat% "390000000000000000", hexnat% "84000000000001000000000000", hexnat% "20000000000400c0000000000", 16888498602639360, hexnat% "40000000400c00000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "c0208040658c64bf00eb200000", hexnat% "6000000000000000000000000", 7036874417766400, 3674937295934324736, hexnat% "180000000000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "c02000007dbf7cbb00eb200000", 285873023221760, hexnat% "8040000000000000000000", hexnat% "6000000000000000000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "c02000007dbf7d8b00eb200000", 57174604644352, hexnat% "8040000000000000000000", hexnat% "6000000000000000000000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "c220000065bf7dbf00eb200000", hexnat% "180000000000000000", hexnat% "8040000000000000000000", hexnat% "4000000000000000000000000"]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "c02000007dbf748e00eb200000", 53876069761024, 2533274790395904, hexnat% "8040000000000000000000", hexnat% "6000000000000000000000000"]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨52, by decide⟩ c9 c6
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c10 c5
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "c4208000658c7d8b00eb000000", hexnat% "180300000000000000", hexnat% "2000040000000000000000000", 57174606741504, 3458764513820540928]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "c020000045bf64bf00eb200000", hexnat% "8040000000000000000000", hexnat% "6000000000000000000000000", 7036874417766400, hexnat% "380000000000000000"]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "c4208000558c7dab00eb000000", 21990234652672, hexnat% "280300000000000000", hexnat% "2000040000000000000000000", 3458764513820540928]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "c0200000459c7dbf00eb200000", 2522015791327477760, hexnat% "8040000000000000000000", hexnat% "6000000000000000000000000", hexnat% "380000000000000000"]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "c0200000458c75bc00eb000000", hexnat% "8040000000000000200000", hexnat% "6000000000000000000000000", 2255098348568576, 3674937295934324736, hexnat% "380000000000000000"]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c16 c15
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨52, by decide⟩ c17 c14
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c18 c13
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c19 c12
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c20 c11
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c21 c4
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4220804045bc000400eb200000", hexnat% "84000000000001000000000000", 202310139510784, 19140298416324608, hexnat% "380300000000000000", 15765897230680064]
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8420804045047d0400eb200000", hexnat% "380300000000000000", hexnat% "42000000000000000000000000", 196812581371904, 576469548396445696, 12682136550675316736]
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "c2200040440c45bc006b200000", hexnat% "8000000000000080000000", 12898309332789100544, hexnat% "4000000010000000000000000", 15765897230680064, hexnat% "380000000000000000"]
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "862080404404450c00eb200000", hexnat% "390000000000000000", hexnat% "40000000000800000000000000", 15765897230680064, 193514046488576, 12898309332789100544]
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8620804065bf658800eb200000", hexnat% "180000000000000000", hexnat% "40000000000000040000000000", 56075093016576, 6755399441055744]
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "400800064bf3d88006b200000", hexnat% "190000000000000000", hexnat% "c0200000000000000000000000", 56075093016576, hexnat% "40000000000080000000", hexnat% "2000000000040040000000000"]
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨98, by decide⟩ c28 c27
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "46208040448c450c00eb000000", hexnat% "80000000010000000000000000", 15765897230680064, 3458764513822638080, 193514046488576, hexnat% "380300000000000000"]
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8400800045844108006b000000", hexnat% "200040000000000080200000", 16888498602639360, hexnat% "42000000000000040000000000", 4035225266123964416, hexnat% "380300000000000000", 196812581371904]
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c31 c30
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c32 c29
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨87, by decide⟩ c33 c26
  let c35 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c34 c25
  let c36 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c35 c24
  let c37 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c36 c23
  let c38 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨70, by decide⟩ c37 c22
  let c39 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨24, by decide⟩ c38 c3
  let c40 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c39 c3
  let c41 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c40 c2
  let c42 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨66, by decide⟩ c41 c1
  let c43 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c42 c0
  let c44 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c43 c0
  c44
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record006_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record006_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record006_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record006_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record006_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record006_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record006_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record006_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record006_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00168.record006

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00168.record007
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record007
def vertexColumn : Fields := ⟨10, hexnat% "f4c70bc1f0f2c68ba1e8e6c5a9665a56558d62d876c3a2e4b8ae1ba1e4789e1783ec6715a5595955553570d8b52d2b46d8751d2745dc4e9364e5354cd3c2e2b4acab1ae1b46c9b16f07a1d8791d4731e2749ca719e1745c9715e0f43c8f13c2f07ce43521c470e234a1a468e1314a51960d4342d30ca318e0b42c2b"⟩
def kindColumn : Fields := ⟨3, hexnat% "9369369b6da6db6da4db6db6d249249b6db6924924db6db4da4db693699249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨35, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨84, by decide⟩, ⟨90, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩, ⟨97, by decide⟩, ⟨98, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4441000000000000800000000", hexnat% "2200000010002000000000000", 527765585526784, 17293822569102704640, hexnat% "20c04180000000000", hexnat% "18000000000186000000"]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record007_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record007_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record007_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record007_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record007_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record007_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record007_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record007_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record007_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00168.record007

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00168.record010
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record010
def vertexColumn : Fields := ⟨10, hexnat% "3d32a9a96ac6a5a568e635a2e4b8ae1ba1e4785ecc6b16c6715c4f1ca6695a71996559394d58d5352d4758b52d2b61d4745dc8ea368e6358ce3c4e9364e5354cd3c2e4b52e2b4acab1ae1b46c5b31e2749ca719e1745e0f43c8f0bc1f1b0961584e8a5291a4a5194951544d0b61344c9314e0b42c4b21c4705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "1b6db6d36d369b6db4936d26d249369b6db4924924934924da492492249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨58, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨82, by decide⟩, ⟨85, by decide⟩, ⟨89, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "232000000000000000", hexnat% "2400000400000080000000", hexnat% "20000100000400861000000", 4363343175352320, hexnat% "e00c000068002000000", 4362076160, 61573053808640]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record010_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record010_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record010_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record010_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record010_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record010_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record010_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record010_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record010_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00168.record010

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00168.record001
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "3b0f23ab1a9695a368e6c5a364d8b6c38ce2b86e3a719a659996559364e5c5695656354d4b5c368d634cd2b46d38f1394d5334e334ccb3c2e4b52ccb2ac6b86d1b26c5bc1cc789d2729c6785d1725c3723c4f0bcf01ca0e438e1344b11c4c92960d4348d18e1344c530ce0b42c4b81d0709c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "69b6db6db4db4db6d26db69249349249249269269349249a491249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record001 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record001 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record001.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record001.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record001.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 27), (facetIndex 33), (facetIndex 44), (facetIndex 48), (facetIndex 51), (facetIndex 55), (facetIndex 90)]))
 (.leaf ([(facetIndex 57), (facetIndex 58), (facetIndex 59), (facetIndex 60), (facetIndex 61)])))
 (.branch 3
 (.leaf ([(facetIndex 37), (facetIndex 47), (facetIndex 54), (facetIndex 79)]))
 (.leaf ([(facetIndex 62), (facetIndex 68), (facetIndex 75)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 38), (facetIndex 40), (facetIndex 41), (facetIndex 69)]))
 (.leaf ([(facetIndex 25), (facetIndex 28), (facetIndex 32), (facetIndex 34), (facetIndex 35)])))
 (.branch 7
 (.leaf ([(facetIndex 26), (facetIndex 42), (facetIndex 45), (facetIndex 46)]))
 (.leaf ([(facetIndex 30), (facetIndex 31), (facetIndex 49), (facetIndex 50), (facetIndex 52), (facetIndex 53)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "4006000230000c92480bf1f85b01a4110b45fc51a8z12;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 36), (facetIndex 43), (facetIndex 56)]))
 (.branch 2
 (.leaf ([(facetIndex 76), (facetIndex 77), (facetIndex 78)]))
 (.leaf ([(facetIndex 84), (facetIndex 89), (facetIndex 91)]))))
 (.branch 5
 (.branch 4
 (.leaf ([(facetIndex 29), (facetIndex 63), (facetIndex 64), (facetIndex 65), (facetIndex 66), (facetIndex 67)]))
 (.leaf ([(facetIndex 39), (facetIndex 70), (facetIndex 71), (facetIndex 72), (facetIndex 73), (facetIndex 74)])))
 (.branch 6
 (.leaf ([(facetIndex 80), (facetIndex 81), (facetIndex 82), (facetIndex 83)]))
 (.leaf ([(facetIndex 85), (facetIndex 86), (facetIndex 87), (facetIndex 88)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "416db2b6d0491249006db6z11;800000018z15;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 7
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped2_0000 : List Nat := [0]
def grouped2_0001 : List Nat := [0, 1]
def grouped2_0002 : List Nat := [0, 1, 2, 3]
def grouped2_0004 : List Nat := [1]
def grouped2_0005 : List Nat := [2]
def grouped2_0006 : List Nat := [2, 3]
def grouped2_0007 : List Nat := [3]
def grouped2_0008 : List Nat := [4, 5, 6, 7]
def grouped3_0009 : List Nat := [0]
def grouped3_0010 : List Nat := [0, 1, 2]
def grouped3_0012 : List Nat := [1]
def grouped3_0013 : List Nat := [1, 2]
def grouped3_0014 : List Nat := [2]
def grouped3_0015 : List Nat := [3]
def grouped3_0016 : List Nat := [3, 4]
def grouped3_0017 : List Nat := [3, 4, 5, 6]
def grouped3_0018 : List Nat := [4]
def grouped3_0019 : List Nat := [5]
def grouped3_0020 : List Nat := [5, 6]
def grouped3_0021 : List Nat := [6]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record001 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record001_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00168.record001" "{\"atoms\":[{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0016\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0020\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00168.record001" 51

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00168.record001" "{\"ridges\":[[9,273],[9,274],[30,273],[30,274],[40,273],[40,274],[49,273],[49,274],[52,273],[52,274],[54,529],[54,530],[57,140],[58,140],[59,140],[60,140],[63,308],[65,404],[66,660],[67,788],[70,344],[72,408],[73,664],[74,792],[81,308],[83,788],[86,344],[88,792]],\"owners\":[[9,273,[63,65,67,70,72,74],[30,40,49,52,54]],[30,273,[70,72,74],[9,40,49,52,54,63,65,67]],[40,273,[63,65,67],[9,30,49,52,54,70,72,74]],[49,273,[65,67,70,72,74],[9,30,40,52,54,63]],[52,273,[63,65,67,72,74],[9,30,40,49,54,70]],[9,274,[81,83,86,88],[30,40,49,52,54]],[30,274,[86,88],[9,40,49,52,54,81,83]],[40,274,[81,83],[9,30,49,52,54,86,88]],[49,274,[83,86,88],[9,30,40,52,54,81]],[52,274,[81,83,88],[9,30,40,49,54,86]],[54,529,[64,66,71,73],[10,31,41,50,53,67,74]],[54,530,[82,87],[10,31,41,50,53,83,88]],[57,140,[78],[12,27,58,59,60,77,91]],[58,140,[77],[12,27,57,59,60,78,91]],[59,140,[77,78,91],[12,27,57,58,60]],[60,140,[77,78,91],[12,27,57,58,59]],[63,308,[81],[]],[81,308,[63],[]],[65,404,[],[]],[66,660,[],[]],[67,788,[83],[]],[83,788,[67],[]],[70,344,[86],[]],[86,344,[70],[]],[72,408,[],[]],[73,664,[],[]],[74,792,[88],[]],[88,792,[74],[]]],\"edges\":[[33,[9,30,40,49,52,54,63,65,67,70,72,74,81,83,86,88]]],\"groupings\":[2,3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00168.record001" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00168.record001\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-13,-3],[-13,-5],[-13,-8],[-26,-13],[-1,14,16,18,19,21,23],[-2,19,21,23],[-4,14,16,18],[-6,16,18,19,21,23],[-7,14,16,18,21,23],[-1,27,29,30,32],[-2,30,32],[-4,27,29],[-6,29,30,32],[-7,27,29,32],[-8,15,17,20,22],[-8,28,31],[-9,25],[-10,24],[-11,24,25,33],[-12,24,25,33],[-14,27],[-27,14],[-16],[-17],[-18,29],[-29,18],[-19,30],[-30,19],[-21],[-22],[-23,32],[-32,23],[-34,9,10,11,12,13],[-35,3,5,8,26],[-36,34],[-37,35],[-38,36],[-38,37],[-39,38],[39],[-24,40],[-25,40],[-33,41],[-14,42],[-15,42],[-18,42],[-19,43],[-20,43],[-23,43],[-27,44],[-28,44],[-29,44],[-30,45],[-31,45],[-32,45],[-41,46],[-40,46],[-46,47],[-43,48],[-42,48],[-45,49],[-44,49],[-48,-49,50],[-47,-50,51],[-51],[1,2,4,6,7,8,14,16,18,19,21,23,27,29,30,32]],\"atoms\":[{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":61,\"b\":37},{\"tag\":\"incompatible\",\"a\":61,\"b\":47},{\"tag\":\"incompatible\",\"a\":61,\"b\":54},{\"tag\":\"incompatible\",\"a\":79,\"b\":61},{\"tag\":\"mate\",\"ridge\":273,\"a\":9,\"owners\":[63,65,67,70,72,74]},{\"tag\":\"mate\",\"ridge\":273,\"a\":30,\"owners\":[70,72,74]},{\"tag\":\"mate\",\"ridge\":273,\"a\":40,\"owners\":[63,65,67]},{\"tag\":\"mate\",\"ridge\":273,\"a\":49,\"owners\":[65,67,70,72,74]},{\"tag\":\"mate\",\"ridge\":273,\"a\":52,\"owners\":[63,65,67,72,74]},{\"tag\":\"mate\",\"ridge\":274,\"a\":9,\"owners\":[81,83,86,88]},{\"tag\":\"mate\",\"ridge\":274,\"a\":30,\"owners\":[86,88]},{\"tag\":\"mate\",\"ridge\":274,\"a\":40,\"owners\":[81,83]},{\"tag\":\"mate\",\"ridge\":274,\"a\":49,\"owners\":[83,86,88]},{\"tag\":\"mate\",\"ridge\":274,\"a\":52,\"owners\":[81,83,88]},{\"tag\":\"mate\",\"ridge\":529,\"a\":54,\"owners\":[64,66,71,73]},{\"tag\":\"mate\",\"ridge\":530,\"a\":54,\"owners\":[82,87]},{\"tag\":\"mate\",\"ridge\":140,\"a\":57,\"owners\":[78]},{\"tag\":\"mate\",\"ridge\":140,\"a\":58,\"owners\":[77]},{\"tag\":\"mate\",\"ridge\":140,\"a\":59,\"owners\":[77,78,91]},{\"tag\":\"mate\",\"ridge\":140,\"a\":60,\"owners\":[77,78,91]},{\"tag\":\"mate\",\"ridge\":308,\"a\":63,\"owners\":[81]},{\"tag\":\"mate\",\"ridge\":308,\"a\":81,\"owners\":[63]},{\"tag\":\"mate\",\"ridge\":404,\"a\":65,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":660,\"a\":66,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":788,\"a\":67,\"owners\":[83]},{\"tag\":\"mate\",\"ridge\":788,\"a\":83,\"owners\":[67]},{\"tag\":\"mate\",\"ridge\":344,\"a\":70,\"owners\":[86]},{\"tag\":\"mate\",\"ridge\":344,\"a\":86,\"owners\":[70]},{\"tag\":\"mate\",\"ridge\":408,\"a\":72,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":664,\"a\":73,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":792,\"a\":74,\"owners\":[88]},{\"tag\":\"mate\",\"ridge\":792,\"a\":88,\"owners\":[74]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[57,58,59,60,61],\"full_literals\":[-34,9,10,11,12,13]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[37,47,54,79],\"full_literals\":[-35,3,5,8,26]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-36,false,34],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-37,35,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-38,36,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-38,false,37],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-39,38,false],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":77,\"full_literals\":[-24,40]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":78,\"full_literals\":[-25,40]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":91,\"full_literals\":[-33,41]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":63,\"full_literals\":[-14,42]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":64,\"full_literals\":[-15,42]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":67,\"full_literals\":[-18,42]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":70,\"full_literals\":[-19,43]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":71,\"full_literals\":[-20,43]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":74,\"full_literals\":[-23,43]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":81,\"full_literals\":[-27,44]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":82,\"full_literals\":[-28,44]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":83,\"full_literals\":[-29,44]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":86,\"full_literals\":[-30,45]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":87,\"full_literals\":[-31,45]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":88,\"full_literals\":[-32,45]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-41,46],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-40,false,46],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-46,47],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0016\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-43,48],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0016\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-42,false,48],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0020\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-45,49],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0020\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-44,false,49],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-48,-49,50],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-47,-50,51],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":33,\"owners\":[9,30,40,49,52,54,63,65,67,70,72,74,81,83,86,88]}]}"
  "p cnf 51 66\n-13 -3 0\n-13 -5 0\n-13 -8 0\n-26 -13 0\n-1 14 16 18 19 21 23 0\n-2 19 21 23 0\n-4 14 16 18 0\n-6 16 18 19 21 23 0\n-7 14 16 18 21 23 0\n-1 27 29 30 32 0\n-2 30 32 0\n-4 27 29 0\n-6 29 30 32 0\n-7 27 29 32 0\n-8 15 17 20 22 0\n-8 28 31 0\n-9 25 0\n-10 24 0\n-11 24 25 33 0\n-12 24 25 33 0\n-14 27 0\n-27 14 0\n-16 0\n-17 0\n-18 29 0\n-29 18 0\n-19 30 0\n-30 19 0\n-21 0\n-22 0\n-23 32 0\n-32 23 0\n-34 9 10 11 12 13 0\n-35 3 5 8 26 0\n-36 34 0\n-37 35 0\n-38 36 0\n-38 37 0\n-39 38 0\n39 0\n-24 40 0\n-25 40 0\n-33 41 0\n-14 42 0\n-15 42 0\n-18 42 0\n-19 43 0\n-20 43 0\n-23 43 0\n-27 44 0\n-28 44 0\n-29 44 0\n-30 45 0\n-31 45 0\n-32 45 0\n-41 46 0\n-40 46 0\n-46 47 0\n-43 48 0\n-42 48 0\n-45 49 0\n-44 49 0\n-48 -49 50 0\n-47 -50 51 0\n-51 0\n1 2 4 6 7 8 14 16 18 19 21 23 27 29 30 32 0\n"
  "67 38 0 40 39 0\n68 36 0 67 37 0\n69 37 0 67 38 0\n70 34 0 68 35 0\n71 35 0 69 36 0\n72 1 2 4 6 7 8 14 18 19 23 27 29 30 32 0 23 29 66 0\n73 -13 0 71 1 2 3 4 34 0\n74 46 0 73 70 56 57 43 41 42 18 19 20 17 33 0\n75 47 0 74 58 0\n76 -50 0 75 65 64 0\n77 48 0 30 24 29 23 59 60 47 48 49 44 45 46 6 28 15 32 5 7 9 22 8 26 72 0\n78 -49 0 77 76 63 0\n79 -45 0 78 61 0\n80 -44 0 78 62 0\n81 -30 0 79 53 0\n82 -31 0 79 54 0\n83 -32 0 79 55 0\n84 -27 0 80 50 0\n85 -28 0 80 51 0\n86 -29 0 80 52 0\n87 -2 0 81 83 11 0\n88 -19 0 81 27 0\n89 -8 0 82 85 16 0\n90 -23 0 83 31 0\n91 -1 0 84 86 81 83 10 0\n92 -4 0 84 86 12 0\n93 -7 0 84 86 83 14 0\n94 -14 0 84 21 0\n95 -6 0 86 81 83 13 0\n96 -18 0 86 25 0\n97 0 91 95 87 92 93 89 94 96 88 90 84 86 81 83 72 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record001.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record001.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record001.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record001.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record001 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record001.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record001.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record001.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record001.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record001 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record001_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record001_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record001_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record001_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record001_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record001_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record001_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record001 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record001_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record001_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record001_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00168.record001

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00168.record011
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "334cb26c5b31cacaaa9a8eaa6a668d9362da4e8b92e2b86e4789e179b16a5693a599596354d4b55362d4b4ad1b61d2745d38e334ccb332e2b4acab1ae1b46c5b89d2729e1745c9715c3783d0f23c2f8711c8689a8986685a0e1381e46499494654550d1341d28c6324c8b12c1b11c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "db69b6d24da4da4936da4d34d34924da4da492492492492249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record011 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record011 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record011.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record011.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record011.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 41), (facetIndex 42), (facetIndex 53), (facetIndex 54), (facetIndex 64)]))
 (.leaf ([(facetIndex 69), (facetIndex 70), (facetIndex 71), (facetIndex 81)])))
 (.branch 3
 (.leaf ([(facetIndex 52), (facetIndex 86)]))
 (.branch 4
 (.leaf ([(facetIndex 37), (facetIndex 44), (facetIndex 48), (facetIndex 51)]))
 (.leaf ([(facetIndex 57), (facetIndex 59), (facetIndex 61), (facetIndex 63)])))))
 (.branch 7
 (.branch 6
 (.leaf ([(facetIndex 75), (facetIndex 76), (facetIndex 79), (facetIndex 80)]))
 (.leaf ([(facetIndex 28), (facetIndex 33), (facetIndex 43), (facetIndex 55), (facetIndex 72)])))
 (.branch 8
 (.leaf ([(facetIndex 32), (facetIndex 34), (facetIndex 35), (facetIndex 36)]))
 (.branch 9
 (.leaf ([(facetIndex 29), (facetIndex 30), (facetIndex 31), (facetIndex 40), (facetIndex 47)]))
 (.leaf ([(facetIndex 38), (facetIndex 39)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "20000155005500611100000404040406002300380036008993777678886z1c;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 10
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 2
 (.branch 1
 (.leaf ([(facetIndex 49), (facetIndex 50), (facetIndex 60), (facetIndex 68), (facetIndex 85), (facetIndex 90)]))
 (.leaf ([(facetIndex 62), (facetIndex 77), (facetIndex 78)])))
 (.branch 3
 (.leaf ([(facetIndex 45), (facetIndex 46), (facetIndex 56), (facetIndex 65), (facetIndex 66), (facetIndex 67), (facetIndex 83), (facetIndex 84), (facetIndex 89)]))
 (.leaf ([(facetIndex 58), (facetIndex 73), (facetIndex 74), (facetIndex 82), (facetIndex 87), (facetIndex 88)]))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨2, sparse_nat% "bc2b0143c00a81032000028z16;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 4
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped2_0000 : List Nat := [0, 1]
def grouped2_0001 : List Nat := [0, 1, 2, 3, 4]
def grouped2_0003 : List Nat := [2]
def grouped2_0004 : List Nat := [2, 3, 4]
def grouped2_0005 : List Nat := [3]
def grouped2_0006 : List Nat := [3, 4]
def grouped2_0007 : List Nat := [4]
def grouped2_0008 : List Nat := [5]
def grouped2_0009 : List Nat := [5, 6]
def grouped2_0010 : List Nat := [5, 6, 7, 8, 9]
def grouped2_0011 : List Nat := [6]
def grouped2_0012 : List Nat := [7]
def grouped2_0013 : List Nat := [7, 8, 9]
def grouped2_0014 : List Nat := [8]
def grouped2_0015 : List Nat := [8, 9]
def grouped2_0016 : List Nat := [9]
def grouped3_0017 : List Nat := [0]
def grouped3_0018 : List Nat := [0, 1]
def grouped3_0020 : List Nat := [1]
def grouped3_0021 : List Nat := [2]
def grouped3_0022 : List Nat := [2, 3]
def grouped3_0023 : List Nat := [3]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record011 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record011_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00168.record011" "{\"atoms\":[{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":9},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0015\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0018\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0018\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0022\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0022\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00168.record011" 69

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00168.record011" "{\"ridges\":[[8,35],[9,35],[9,161],[15,289],[15,292],[23,38],[37,162],[38,35],[38,289],[39,35],[39,546],[44,162],[45,298],[48,35],[48,161],[48,162],[51,161],[51,162],[55,100],[56,172],[57,289],[57,292],[60,180],[61,289],[61,292],[63,289],[63,292],[65,232],[66,97],[67,424],[68,432],[72,100],[73,172],[74,38],[75,546],[77,38],[77,180],[82,232],[83,98],[84,680],[85,688],[87,360],[89,808],[90,816]],\"owners\":[[66,97,[8,14,51],[43,55,63,65]],[83,98,[8,22,51],[43,72,80,82]],[9,161,[56,60,65,67,68],[37,44,48,51]],[48,161,[56,65,67],[9,37,44,51,60,68]],[51,161,[56,60,67,68],[9,37,44,48,65]],[37,162,[82,84,85],[9,44,48,51,73,77]],[44,162,[77,85],[9,37,48,51,73,82,84]],[48,162,[73,82,84],[9,37,44,51,77,85]],[51,162,[73,77,84,85],[9,37,44,48,82]],[55,100,[22,80],[14,63,72,87,88]],[72,100,[14,63],[22,55,80,87,88]],[15,289,[45,49,66,67,68],[38,57,61,63]],[38,289,[66,67,68],[15,45,49,57,61,63]],[57,289,[49,68],[15,38,45,61,63,66,67]],[61,289,[45,66,67],[15,38,49,57,63,68]],[63,289,[45,49,67,68],[15,38,57,61,66]],[15,292,[74,78,87,89,90],[38,57,61,63]],[57,292,[78,90],[15,38,61,63,74,87,89]],[61,292,[74,87,89],[15,38,57,63,78,90]],[63,292,[74,78,89,90],[15,38,57,61,87]],[39,546,[83,84,85],[23,46,50,75,79,80]],[75,546,[50,85],[23,39,46,79,80,83,84]],[45,298,[74],[]],[56,172,[73],[]],[73,172,[56],[]],[60,180,[77],[]],[77,180,[60],[]],[65,232,[82],[]],[82,232,[65],[]],[87,360,[66],[]],[67,424,[],[]],[68,432,[],[]],[84,680,[],[]],[85,688,[],[]],[89,808,[],[]],[90,816,[],[]]],\"edges\":[[36,[9,37,44,48,51,56,60,65,67,68,73,77,82,84,85]],[37,[15,38,45,49,57,61,63,66,67,68,74,78,87,89,90]],[38,[23,39,46,50,58,62,75,79,80,83,84,85,88,89,90]]],\"groupings\":[2,3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00168.record011" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00168.record011\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-9,-1],[-10,-3],[-10,-7],[-10,-8],[-11,-5],[-11,-7],[-11,-8],[-12,-1],[-19,-1],[-19,-10],[-19,-11],[-20,-10],[-26,-10],[-28,-10],[-30,-21],[-30,-24],[-33,-11],[-34,-11],[-34,-30],[-35,-15],[-35,-21],[-35,-23],[-35,-34],[-37,-11],[-37,-17],[-37,-18],[-37,-27],[-38,-37],[-39,-37],[-40,-11],[-40,-37],[-41,-30],[-41,-35],[-42,-29],[-42,-35],[-42,-41],[-46,-35],[-1,-2,-11],[-1,-10,-16],[-1,-11,-16],[-6,-35,-37],[-30,1,3,19],[-42,1,5,19],[-2,21,25,29,31,32],[-16,21,29,31],[-19,21,25,31,32],[-9,41,43,44],[-13,37,44],[-16,34,41,43],[-19,34,37,43,44],[-20,5,40],[-33,3,28],[-4,14,17,30,31,32],[-10,30,31,32],[-22,17,32],[-26,14,30,31],[-28,14,17,31,32],[-4,35,38,45,47,48],[-22,38,48],[-26,35,45,47],[-28,35,38,47,48],[-11,42,43,44],[-36,18,44],[-14,35],[-21,34],[-34,21],[-25,37],[-37,25],[-29,41],[-41,29],[-45,30],[-31],[-32],[-43],[-44],[-47],[-48],[-49,9,13,16,19],[-50,22,24,26,28],[-51,7,8,12,20,33],[-52,10,11],[-10,52],[-53,49,50],[-54,53],[-55,54],[-56,51],[-57,52],[-58,57],[-59,56],[-59,58],[-60,55,59],[60],[-17,61],[-25,61],[-37,62],[-38,62],[-21,63],[-29,63],[-30,63],[-34,64],[-41,64],[-62,65],[-61,65],[-61,-62,66],[-63,67],[-63,-64,68],[-65,-68,69],[-66,-67,69],[-69],[2,9,13,16,19,21,25,29,31,32,34,37,41,43,44],[4,10,14,17,22,26,28,30,31,32,35,38,45,47,48],[6,11,15,18,23,27,36,39,40,42,43,44,46,47,48]],\"atoms\":[{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":9,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":37,\"b\":8},{\"tag\":\"incompatible\",\"a\":38,\"b\":14},{\"tag\":\"incompatible\",\"a\":38,\"b\":28},{\"tag\":\"incompatible\",\"a\":38,\"b\":33},{\"tag\":\"incompatible\",\"a\":39,\"b\":22},{\"tag\":\"incompatible\",\"a\":39,\"b\":28},{\"tag\":\"incompatible\",\"a\":39,\"b\":33},{\"tag\":\"incompatible\",\"a\":43,\"b\":8},{\"tag\":\"incompatible\",\"a\":51,\"b\":8},{\"tag\":\"incompatible\",\"a\":51,\"b\":38},{\"tag\":\"incompatible\",\"a\":51,\"b\":39},{\"tag\":\"incompatible\",\"a\":55,\"b\":38},{\"tag\":\"incompatible\",\"a\":61,\"b\":38},{\"tag\":\"incompatible\",\"a\":63,\"b\":38},{\"tag\":\"incompatible\",\"a\":66,\"b\":56},{\"tag\":\"incompatible\",\"a\":66,\"b\":59},{\"tag\":\"incompatible\",\"a\":72,\"b\":39},{\"tag\":\"incompatible\",\"a\":73,\"b\":39},{\"tag\":\"incompatible\",\"a\":73,\"b\":66},{\"tag\":\"incompatible\",\"a\":74,\"b\":46},{\"tag\":\"incompatible\",\"a\":74,\"b\":56},{\"tag\":\"incompatible\",\"a\":74,\"b\":58},{\"tag\":\"incompatible\",\"a\":74,\"b\":73},{\"tag\":\"incompatible\",\"a\":77,\"b\":39},{\"tag\":\"incompatible\",\"a\":77,\"b\":49},{\"tag\":\"incompatible\",\"a\":77,\"b\":50},{\"tag\":\"incompatible\",\"a\":77,\"b\":62},{\"tag\":\"incompatible\",\"a\":78,\"b\":77},{\"tag\":\"incompatible\",\"a\":79,\"b\":77},{\"tag\":\"incompatible\",\"a\":80,\"b\":39},{\"tag\":\"incompatible\",\"a\":80,\"b\":77},{\"tag\":\"incompatible\",\"a\":82,\"b\":66},{\"tag\":\"incompatible\",\"a\":82,\"b\":74},{\"tag\":\"incompatible\",\"a\":83,\"b\":65},{\"tag\":\"incompatible\",\"a\":83,\"b\":74},{\"tag\":\"incompatible\",\"a\":83,\"b\":82},{\"tag\":\"incompatible\",\"a\":88,\"b\":74},{\"tag\":\"three\",\"ridge\":35,\"vertices\":[8,9,39]},{\"tag\":\"three\",\"ridge\":35,\"vertices\":[8,38,48]},{\"tag\":\"three\",\"ridge\":35,\"vertices\":[8,39,48]},{\"tag\":\"three\",\"ridge\":38,\"vertices\":[23,74,77]},{\"tag\":\"mate\",\"ridge\":97,\"a\":66,\"owners\":[8,14,51]},{\"tag\":\"mate\",\"ridge\":98,\"a\":83,\"owners\":[8,22,51]},{\"tag\":\"mate\",\"ridge\":161,\"a\":9,\"owners\":[56,60,65,67,68]},{\"tag\":\"mate\",\"ridge\":161,\"a\":48,\"owners\":[56,65,67]},{\"tag\":\"mate\",\"ridge\":161,\"a\":51,\"owners\":[56,60,67,68]},{\"tag\":\"mate\",\"ridge\":162,\"a\":37,\"owners\":[82,84,85]},{\"tag\":\"mate\",\"ridge\":162,\"a\":44,\"owners\":[77,85]},{\"tag\":\"mate\",\"ridge\":162,\"a\":48,\"owners\":[73,82,84]},{\"tag\":\"mate\",\"ridge\":162,\"a\":51,\"owners\":[73,77,84,85]},{\"tag\":\"mate\",\"ridge\":100,\"a\":55,\"owners\":[22,80]},{\"tag\":\"mate\",\"ridge\":100,\"a\":72,\"owners\":[14,63]},{\"tag\":\"mate\",\"ridge\":289,\"a\":15,\"owners\":[45,49,66,67,68]},{\"tag\":\"mate\",\"ridge\":289,\"a\":38,\"owners\":[66,67,68]},{\"tag\":\"mate\",\"ridge\":289,\"a\":57,\"owners\":[49,68]},{\"tag\":\"mate\",\"ridge\":289,\"a\":61,\"owners\":[45,66,67]},{\"tag\":\"mate\",\"ridge\":289,\"a\":63,\"owners\":[45,49,67,68]},{\"tag\":\"mate\",\"ridge\":292,\"a\":15,\"owners\":[74,78,87,89,90]},{\"tag\":\"mate\",\"ridge\":292,\"a\":57,\"owners\":[78,90]},{\"tag\":\"mate\",\"ridge\":292,\"a\":61,\"owners\":[74,87,89]},{\"tag\":\"mate\",\"ridge\":292,\"a\":63,\"owners\":[74,78,89,90]},{\"tag\":\"mate\",\"ridge\":546,\"a\":39,\"owners\":[83,84,85]},{\"tag\":\"mate\",\"ridge\":546,\"a\":75,\"owners\":[50,85]},{\"tag\":\"mate\",\"ridge\":298,\"a\":45,\"owners\":[74]},{\"tag\":\"mate\",\"ridge\":172,\"a\":56,\"owners\":[73]},{\"tag\":\"mate\",\"ridge\":172,\"a\":73,\"owners\":[56]},{\"tag\":\"mate\",\"ridge\":180,\"a\":60,\"owners\":[77]},{\"tag\":\"mate\",\"ridge\":180,\"a\":77,\"owners\":[60]},{\"tag\":\"mate\",\"ridge\":232,\"a\":65,\"owners\":[82]},{\"tag\":\"mate\",\"ridge\":232,\"a\":82,\"owners\":[65]},{\"tag\":\"mate\",\"ridge\":360,\"a\":87,\"owners\":[66]},{\"tag\":\"mate\",\"ridge\":424,\"a\":67,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":432,\"a\":68,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":680,\"a\":84,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":688,\"a\":85,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":808,\"a\":89,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":816,\"a\":90,\"owners\":[]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[37,44,48,51],\"full_literals\":[-49,9,13,16,19]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[57,59,61,63],\"full_literals\":[-50,22,24,26,28]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[28,33,43,55,72],\"full_literals\":[-51,7,8,12,20,33]},{\"tag\":\"group_or\",\"kind\":2,\"index\":9,\"members\":[38,39],\"full_literals\":[-52,10,11]},{\"tag\":\"group_take\",\"kind\":2,\"index\":9,\"member\":38,\"full_literals\":[-10,52]},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-53,49,50],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0004\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-54,false,53],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-55,false,54],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-56,false,51],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped2_0014\",\"right_name\":\"grouped2_0016\",\"joined_name\":\"grouped2_0015\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-57,false,52],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0013\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-58,false,57],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":1,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-59,56,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-59,false,58],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-60,55,59],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":49,\"full_literals\":[-17,61]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":60,\"full_literals\":[-25,61]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":77,\"full_literals\":[-37,62]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":78,\"full_literals\":[-38,62]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":56,\"full_literals\":[-21,63]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":65,\"full_literals\":[-29,63]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":66,\"full_literals\":[-30,63]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":73,\"full_literals\":[-34,64]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":82,\"full_literals\":[-41,64]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0018\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-62,65],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0018\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-61,false,65],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0018\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-61,-62,66],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"grouped3_0022\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-63,false,67],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"grouped3_0022\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-63,-64,68],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-65,-68,69],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-66,-67,69],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":36,\"owners\":[9,37,44,48,51,56,60,65,67,68,73,77,82,84,85]},{\"tag\":\"edge\",\"edge\":37,\"owners\":[15,38,45,49,57,61,63,66,67,68,74,78,87,89,90]},{\"tag\":\"edge\",\"edge\":38,\"owners\":[23,39,46,50,58,62,75,79,80,83,84,85,88,89,90]}]}"
  "p cnf 69 112\n-9 -1 0\n-10 -3 0\n-10 -7 0\n-10 -8 0\n-11 -5 0\n-11 -7 0\n-11 -8 0\n-12 -1 0\n-19 -1 0\n-19 -10 0\n-19 -11 0\n-20 -10 0\n-26 -10 0\n-28 -10 0\n-30 -21 0\n-30 -24 0\n-33 -11 0\n-34 -11 0\n-34 -30 0\n-35 -15 0\n-35 -21 0\n-35 -23 0\n-35 -34 0\n-37 -11 0\n-37 -17 0\n-37 -18 0\n-37 -27 0\n-38 -37 0\n-39 -37 0\n-40 -11 0\n-40 -37 0\n-41 -30 0\n-41 -35 0\n-42 -29 0\n-42 -35 0\n-42 -41 0\n-46 -35 0\n-1 -2 -11 0\n-1 -10 -16 0\n-1 -11 -16 0\n-6 -35 -37 0\n-30 1 3 19 0\n-42 1 5 19 0\n-2 21 25 29 31 32 0\n-16 21 29 31 0\n-19 21 25 31 32 0\n-9 41 43 44 0\n-13 37 44 0\n-16 34 41 43 0\n-19 34 37 43 44 0\n-20 5 40 0\n-33 3 28 0\n-4 14 17 30 31 32 0\n-10 30 31 32 0\n-22 17 32 0\n-26 14 30 31 0\n-28 14 17 31 32 0\n-4 35 38 45 47 48 0\n-22 38 48 0\n-26 35 45 47 0\n-28 35 38 47 48 0\n-11 42 43 44 0\n-36 18 44 0\n-14 35 0\n-21 34 0\n-34 21 0\n-25 37 0\n-37 25 0\n-29 41 0\n-41 29 0\n-45 30 0\n-31 0\n-32 0\n-43 0\n-44 0\n-47 0\n-48 0\n-49 9 13 16 19 0\n-50 22 24 26 28 0\n-51 7 8 12 20 33 0\n-52 10 11 0\n-10 52 0\n-53 49 50 0\n-54 53 0\n-55 54 0\n-56 51 0\n-57 52 0\n-58 57 0\n-59 56 0\n-59 58 0\n-60 55 59 0\n60 0\n-17 61 0\n-25 61 0\n-37 62 0\n-38 62 0\n-21 63 0\n-29 63 0\n-30 63 0\n-34 64 0\n-41 64 0\n-62 65 0\n-61 65 0\n-61 -62 66 0\n-63 67 0\n-63 -64 68 0\n-65 -68 69 0\n-66 -67 69 0\n-69 0\n2 9 13 16 19 21 25 29 31 32 34 37 41 43 44 0\n4 10 14 17 22 26 28 30 31 32 35 38 45 47 48 0\n6 11 15 18 23 27 36 39 40 42 43 44 46 47 48 0\n"
  "113 2 9 13 16 19 21 25 29 34 37 41 0 72 73 74 75 110 0\n114 4 10 14 17 22 26 28 30 35 38 45 0 72 73 76 77 111 0\n115 6 11 15 18 23 27 36 39 40 42 46 0 74 75 76 77 112 0\n116 -11 1 0 75 74 5 11 62 43 0\n117 1 -52 0 73 72 116 81 2 10 54 42 0\n118 -16 -52 0 117 39 40 81 0\n119 -10 -59 0 90 88 87 117 8 89 86 2 3 4 12 14 80 52 0\n120 -59 0 89 90 86 88 87 117 8 119 81 5 6 7 17 30 80 51 0\n121 55 0 120 92 91 0\n122 54 0 121 85 0\n123 53 0 122 84 0\n124 -11 -52 65 0 75 74 117 9 1 118 102 95 48 103 94 18 62 38 65 34 36 113 0\n125 -52 65 0 75 77 123 73 72 102 96 59 95 48 117 118 1 9 78 83 124 81 13 14 54 79 16 0\n126 35 26 28 30 65 0 77 76 71 125 82 102 96 59 103 93 64 58 114 0\n127 21 19 13 29 9 41 25 16 34 37 0 72 73 113 44 0\n128 -35 41 65 0 74 75 73 72 69 47 102 95 48 103 94 21 23 46 45 127 0\n129 30 35 65 0 76 77 72 102 96 61 64 126 56 0\n130 41 65 0 75 74 73 72 102 95 48 103 94 47 69 128 129 15 19 46 45 127 0\n131 65 0 130 32 33 129 0\n132 -68 0 131 109 107 0\n133 -41 0 132 70 101 98 106 0\n134 -9 0 133 74 75 47 0\n135 -29 0 133 69 0\n136 -37 35 30 0 76 73 72 71 60 64 54 25 28 55 57 53 114 0\n137 37 25 13 21 16 34 0 74 75 135 134 133 127 50 0\n138 37 34 0 133 74 75 49 65 48 67 137 0\n139 -35 -37 0 75 26 63 31 29 27 24 20 22 35 37 41 115 0\n140 -37 0 109 68 95 94 104 139 108 136 105 99 0\n141 34 0 140 138 0\n142 21 0 141 66 0\n143 64 0 141 100 0\n144 63 0 142 97 0\n145 0 144 143 132 106 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record011.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record011.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record011.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record011.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record011 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record011.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record011.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record011.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record011.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record011 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record011_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record011_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record011_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record011_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record011_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record011_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record011_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record011 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record011_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record011_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00168.record011_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00168.record011
