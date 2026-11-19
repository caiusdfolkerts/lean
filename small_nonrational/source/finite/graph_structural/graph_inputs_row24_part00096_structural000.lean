module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow24Part00096Data
public import GraphInputsRow24Part00096Frames
public import GraphInputsRow24Part00096Leaves
public import GraphInputsRow24Part00096Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00096.record010
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record010
def vertexColumn : Fields := ⟨10, hexnat% "ae2b4ab29c9723c2f07caaa5a56a3a1eaa6c5a5655a364d876a3a4e33a2e2b86e8785e0fa99564b91e6954d4b51d68d334ad1b61d2745d0f5534cc73a2d4b32c6b86d1b16c3ba1d8731d2719e1745c570de0f23c4f0bc1f5528a2aa86518a6544a916439514a5454550d54328c8b12c2b41c8711c27"⟩
def kindColumn : Fields := ⟨3, hexnat% "1b6db6d36da6d36d36d36db49349369b6926d249b492493493493249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨54, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨69, by decide⟩, ⟨73, by decide⟩, ⟨77, by decide⟩, ⟨80, by decide⟩, ⟨85, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20000c0100feee000000", hexnat% "2102200000000000000000", 30786325577728, 35184372088832, 11674456134051168256, 4630263366890291200]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [3316360436118454272, 4629700691814776832, 9223654061587300352, hexnat% "20000000000000000000", hexnat% "2102200000000000000000", 43980465111040]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2000000100c6e0000000", hexnat% "2000000000280008000000", hexnat% "100000000003800000000", 1009369266484412416, 6917533425687592960, 9223389629040820224, hexnat% "2200044000006000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c3 c0
  c4
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record010_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record010_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record010_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record010_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record010_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record010_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record010_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record010_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record010_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00096.record010

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00096.record011
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record011
def vertexColumn : Fields := ⟨10, hexnat% "ae0bc1f2aa9695a8e87a559361d8ce2b86e1783eac6a9a6659566392e479a55352d475334ad1b49d1743da8f1394d538cd331ce4b52ccb8ac6b86d1b16c3ba1d8731d2719e1745c570dc8f13c2f07d54a28aa518a6546892a61916439514a5454550d68350ca382c8b12c2b41c8711c27"⟩
def kindColumn : Fields := ⟨3, hexnat% "1b69b6d36d36da49249a49a6d24da6da4924d24924d2492649249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2, 3]
def candidates : List (Fin raw.n) := [⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3bdfe0abfef75fcf8000000", hexnat% "4001100000000000000000", hexnat% "14000000300000000", hexnat% "200010820000000000", hexnat% "c40000080000000000", hexnat% "200000000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fdfffe3fee2f0478000000", hexnat% "200000010000380000000", 510173395288064, 1065151889408, hexnat% "1c000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fdff3abffff72df8000000", 893353197568, hexnat% "200000000080200000000", hexnat% "14000000000000000", hexnat% "c40000000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 3 [hexnat% "3fffffffffffffff8000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ffff1effefff0cf8000000", hexnat% "c00000000000000000", 1030792151040, hexnat% "200010000100000000", hexnat% "10000000200000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨81, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fdff1abfeef504f8000000", hexnat% "14000000300000000", 1065151889408, hexnat% "c00001080000000000", hexnat% "200000010020000000000", hexnat% "240000000000000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c7 c2
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fdfe123cee040458000000", 1065151889408, hexnat% "2000000100b0380000000", hexnat% "1c100000000000000", hexnat% "640200000000000000", hexnat% "1880000200000000000", 510173932158976]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨68, by decide⟩ c10 c1
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c11 c0
  c12
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record011_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record011_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record011_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record011_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record011_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record011_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record011_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record011_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record011_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00096.record011

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00096.record015
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record015
def vertexColumn : Fields := ⟨10, hexnat% "2b4570dc2f07caca9a368ba1eaa6a5a5635a362d8766394e3392e2b86e2785e0fab1a65592e479a9695955558d4b51d54d4b4ad1b51d2745d0f6a3a4e538ccb31ce8b4acab1ae1b26c5b0ef07a1e4789d2729c6785c9715c3743c8f13c2f07cb8a50b4528aaa19462994916439516151543550d0b12c2b81d0711c27"⟩
def kindColumn : Fields := ⟨3, hexnat% "9b4db69a4db4da6d36db6926924926db6936db6d24da4924924d24d2649249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2, 3]
def candidates : List (Fin raw.n) := [⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩, ⟨95, by decide⟩, ⟨96, by decide⟩, ⟨97, by decide⟩, ⟨98, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "37a76df992f9ffeffff800000", hexnat% "401040010000000000", hexnat% "6c000000000000000", hexnat% "800120000020000000000000", hexnat% "4018800000000000000000000", hexnat% "40000200000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fefeffffffffdf81f6800000", hexnat% "4010000000000000800000000", 35201702952960, hexnat% "100000000000000000000", 489626271744]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7fffeffacef9fd7fff5800000", 43980632883200, hexnat% "30040000000000000", hexnat% "500000000000000000", hexnat% "100001020000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fefeffffefffdf93f4800000", hexnat% "4010000000000000800000000", 429496729600, hexnat% "10000100000000b000000", 35184372088832]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .size 3
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7fefffffeefffffffff800000", hexnat% "10000000000000000000000", hexnat% "11000000000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨80, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7fffffffeafffffffff800000", 4611686018427387904, hexnat% "11000000000000000"]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨80, by decide⟩ c7 c4
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fffefffe2fffffffff800000", hexnat% "100001000000000000000", hexnat% "400000000c000000000000000", hexnat% "10000000000000000"]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨88, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨66, by decide⟩ c10 c6
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fefeffba2f9fffffff800000", hexnat% "4010000008000000000000000", hexnat% "44000000000000000", hexnat% "100001060000000000000", hexnat% "410000000000000000"]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨68, by decide⟩ c12 c11
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7fefeffaeef9fd7c3f4800000", hexnat% "500000080000000000", hexnat% "10000000000002800000000", 35201736507392, hexnat% "10000001000000000", hexnat% "100001060000000000000"]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c14 c13
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨65, by decide⟩ c15 c3
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c16 c2
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨61, by decide⟩ c17 c1
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "37e76dfd80f9fcf0144800000", 53326330724352, hexnat% "80012000106000000a000000", hexnat% "4018800000000000000000000", hexnat% "3a000000020000000", hexnat% "244000002200000000", 397552910336]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨90, by decide⟩ c19 c18
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c20 c0
  c21
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record015_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record015_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record015_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record015_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record015_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record015_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record015_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record015_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record015_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00096.record015
