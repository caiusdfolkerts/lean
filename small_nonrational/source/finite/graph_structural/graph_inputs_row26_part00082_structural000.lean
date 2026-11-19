module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow26Part00082Data
public import GraphInputsRow26Part00082Frames
public import GraphInputsRow26Part00082Leaves
public import GraphInputsRow26Part00082Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00082.record012
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record012
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
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "200040047d000419ff7400000", 32985348833280, hexnat% "100010000008000000000000", 54043195528445952]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2000400465000401ff7400000", 28037546508288, hexnat% "100000000008060000000000", hexnat% "180c0000000000000", hexnat% "10000000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨82, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4004380c0019db6000000", hexnat% "2000000045000000200000000", hexnat% "100010000008040040000000", 96757044215808, 2199023255552]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4004380c0019db5000000", hexnat% "2000000045000000200000000", hexnat% "100010000008040040000000", 96757060993024, 2199023255552]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "104000c0599db3400000", hexnat% "100000000008060040000000", hexnat% "3d000000004000000", hexnat% "2000400040000000200000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "200040007d000019fb6000000", hexnat% "4000c0000000000000", hexnat% "100000000008060040000000", 96757044215808, hexnat% "10000000000000000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "200040007d000019e36000000", hexnat% "4000c0000000000000", hexnat% "100010000008040040000000", 6463422464, 98956046499840]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2000400045000001236000000", hexnat% "100010000008040040000000", hexnat% "380c0000000000000", hexnat% "400000418000000000", 58003030016, 28587302322176]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c9 c6
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c10 c5
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c11 c4
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c12 c3
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c13 c2
  c14
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record012_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record012_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record012_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record012_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record012_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record012_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record012_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record012_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record012_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00082.record012

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00082.record013
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record013
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
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1fc84003ff7fde000000", hexnat% "110004000000000000", hexnat% "84000000000000000000000", hexnat% "60600000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8401cd900064f7fde000000", 474989023199232, hexnat% "64000000000000000", hexnat% "3000600000000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "fcf4603077fde000000", hexnat% "84000000000080000000000", 263882790666240, hexnat% "10100004000000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8401fd900064f7fde000000", 474989023199232, hexnat% "60600000000000000", 4611686018427387904]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8400ec800020e7fde000000", hexnat% "1000600000000000000", hexnat% "10110004000000000000", hexnat% "64000000000000000", 546457279004672]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨71, by decide⟩ c7 c6
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨73, by decide⟩ c8 c5
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨75, by decide⟩ c9 c4
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨70, by decide⟩ c10 c3
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8401fd100044f4900000000", 1037939211501568, hexnat% "e4000000010000000", 432345564227567616, 235149459456]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "84018d10007ff4900000000", hexnat% "7000600000000000000", 232163115008, hexnat% "e4000000010000000", 3221225472]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "109f4404477ed8000000", hexnat% "84000000000080100000000", hexnat% "7000200000000000000", hexnat% "8400000000000000000", 1037939077283840]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "84000800603fe7f8e000000", hexnat% "7400000010000000000", hexnat% "e0000000050000000", hexnat% "18100004000000000000", hexnat% "14000000000000000"]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "78e0604477ed6000000", hexnat% "10114000000000000000", hexnat% "84000000000080100000000", 1037939110838272, hexnat% "8400000000000000000"]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8401c9f4007ff49de000000", 231928233984, hexnat% "3000600000000000000", hexnat% "400000000000000000"]
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7cf4603ff68de000000", 98784247808, hexnat% "18100004000000000000", hexnat% "84000000000000000000000"]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1fdd4007ff48de000000", hexnat% "20600000000000000", hexnat% "84000000000000100000000", 231928233984]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7cd0603ff48ce000000", hexnat% "84000000000000100000000", hexnat% "18100004000000000000", 232196669440, hexnat% "24000000000000000"]
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨70, by decide⟩ c20 c19
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨66, by decide⟩ c21 c18
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨64, by decide⟩ c22 c17
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1fd14007c748d2000000", hexnat% "84000000000080100000000", 52776759459840, hexnat% "e0600000000000000", 231928233984]
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "84000c000024e49c2000000", hexnat% "18100004000000000000", hexnat% "7000600000000000000", 476088534827008, hexnat% "f4000000010000000", 232129560576]
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨70, by decide⟩ c25 c24
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c26 c23
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c27 c16
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c28 c15
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c29 c14
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c30 c13
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨71, by decide⟩ c31 c12
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c32 c11
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c33 c2
  let c35 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c34 c1
  let c36 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c35 c0
  c36
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record013_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record013_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record013_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record013_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record013_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record013_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record013_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record013_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record013_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00082.record013

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00082.record015
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record015
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
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record015_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record015_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record015_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record015_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record015_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record015_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record015_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record015_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00082.record015_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00082.record015
