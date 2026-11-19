module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow29Part00054Data
public import GraphInputsRow29Part00054Frames
public import GraphInputsRow29Part00054Leaves
public import GraphInputsRow29Part00054Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00054.record000
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00054.record000
def vertexColumn : Fields := ⟨10, hexnat% "3b0ce1b49b25c8f0bce8b62e4b2a9ab1a969a6998e665a5693a2e2b86e8789e17b61cc5b1ca669c66598e5392e5a5395954d4b52b49d1743dd0f2368e6358ce3c4e53c2e4b8ad2b2ac6b86d1b26c5b61cc749ca719d1715c8f0be681b31264a4a868961381e685911a4a5194951342d0758344c9312c1b21c4705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "db4db6d34936d34da49369a6db69269249b4db4da6da49249a492449249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨44, by decide⟩, ⟨47, by decide⟩, ⟨51, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨68, by decide⟩, ⟨70, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨79, by decide⟩, ⟨81, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨89, by decide⟩, ⟨95, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "22206000180807df8000000", 2756202971950743552, hexnat% "4008000000008000000000", hexnat% "405008000000000000", hexnat% "808090000000010000000000", hexnat% "100000100000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "60067c0003df8000000", hexnat% "401008000000000000", hexnat% "20200000000800000000000", hexnat% "400800000000c000000000", hexnat% "a080000000100000000000", hexnat% "800010100000010000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "80e09e10228891f5f8000000", hexnat% "20200000000000000000000", 378302368699121664, hexnat% "405000000800000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2620e10000090f0f0000000", hexnat% "808090000000010000000000", 2594073406840242176, 270215977776447488, hexnat% "405008000800000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40067c000adf8000000", hexnat% "401008000000000000", hexnat% "20200000000800000000000", hexnat% "4008000000004000000000", hexnat% "808010100000010000000000", hexnat% "2082000000101000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "82628e00020080f070000000", hexnat% "8010100000110000000000", 126100789700591616, hexnat% "405400000800000000", 2305843032836014080, 2251799813685248]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8080185052080189b8000000", 2594073402545274880, 126100789566373888, hexnat% "24000000000804000000000", hexnat% "204000000002040000000", hexnat% "2082000000101000000000"]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "221e0003c801b0f8000000", hexnat% "808080000000000000000000", hexnat% "24000000000804000000000", hexnat% "100000100000000000", 2594073406840242176, hexnat% "405000000800000000"]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20c40578800ad70000000", 2323857407857393664, hexnat% "24000000000804000000000", hexnat% "8010000000010080000000", hexnat% "800000100000000000000000", hexnat% "2082000000101000000000"]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "c4057c800a978000000", 2305843028541046784, hexnat% "20200000000800000000000", hexnat% "4000000000004000000000", hexnat% "2082000000101000000000", hexnat% "808010100000010000000000"]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "84007c8008830000000", hexnat% "204000000002040000000", hexnat% "24000000000804000000000", hexnat% "808010100000010000000000", 2305843032970231808, hexnat% "2082000000101000000000", 5764607523034234880]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c11 c10
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c12 c9
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c13 c8
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c14 c7
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨75, by decide⟩ c15 c6
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c16 c5
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c17 c4
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c18 c1
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c19 c0
  c20
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00054.record000_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00054.record000_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00054.record000_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00054.record000_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00054.record000_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00054.record000_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00054.record000_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00054.record000_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00054.record000_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00054.record000

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00054.record002
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00054.record002
def vertexColumn : Fields := ⟨10, hexnat% "3b0da3386e2789d1ac2f07ce8b62e4b32ac9b29cb4aca9aa9a96ac699a96a3a4e8ba1e9a6998e695a362d8766392e2b86e2785e0fba1d8791cc6b16c671d27296a6695a719666598e5392e47969665396558d4b51d58d4b4ad1b49d1743de0f43c4e9364e53c2d8b92d4b86d1b26c5b61e4731e1715d0f23cb41b03c2584e078951341dc0d8390e1324d0b12c1b21c4705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "36db6d26db6db6db6db6db6db4db6924db6db6db6db6db6db69b6d2492492492492492491249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨50, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨83, by decide⟩, ⟨108, by decide⟩, ⟨109, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "10000000500000002bdab5800000", 137608822784, 22552772608, hexnat% "2000000020000004140000000000", hexnat% "808000000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "200000002000000013fdf9e00000", hexnat% "800000004000000000000", 8690597888, hexnat% "10000000100000002c0000000000", hexnat% "48000000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1000000010000000087fffe00000", 3848290697216, hexnat% "40000000200000000000", hexnat% "2000000020000004140000000000", hexnat% "808000000000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "30000008780000043c1431a00000", 8690597888, 2611474333696, 1140313817088, 1077936128, 549755813888]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "200000083000000418357fe00000", 1694364598272, 2473901162496, hexnat% "1000000000000000240000000000", hexnat% "48000000000000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "300000000b9fffe00000", 412316860416, hexnat% "1000000040000000200000000000", hexnat% "2000000800000004100000000000", hexnat% "8000000040000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2000000820000004101410600000", 8698986496, hexnat% "1000000050000000280000000000", 2370956165120, 1105954078720, hexnat% "8000000040000000000", 826261110784]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨22, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨21, by decide⟩ c7 c4
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨77, by decide⟩ c8 c3
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c9 c2
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c10 c1
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c11 c0
  c12
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00054.record002_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00054.record002_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00054.record002_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00054.record002_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00054.record002_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00054.record002_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00054.record002_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00054.record002_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00054.record002_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00054.record002
