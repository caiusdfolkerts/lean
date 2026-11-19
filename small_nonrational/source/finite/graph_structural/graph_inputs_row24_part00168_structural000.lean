module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow24Part00168Data
public import GraphInputsRow24Part00168Frames
public import GraphInputsRow24Part00168Leaves
public import GraphInputsRow24Part00168Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

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
