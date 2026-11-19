module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow30Part00016Data
public import GraphInputsRow30Part00016Frames
public import GraphInputsRow30Part00016Leaves
public import GraphInputsRow30Part00016Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow30Part00016.record005
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00016.record005
def vertexColumn : Fields := ⟨10, hexnat% "ea178ad0ec4f07ce8b32aca725cb8acaaaa6a96a3a95a4e87aa98e6a5a364d8b61d8ce4b8ae1b91e1783ee8731ac6715c789ca6a96a5693a5594e479a94e5a56354d4b51d4cd4b4ad1b51d1743de0e9394d53c2e8b62d4b32d1b16e8731e1745c9743c1fcc0742b06cc48562384ec44552344dc0e8384d1314d0b22c4b21c4705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "6da69a6db6db6db6db6d26934da6db6db6db6db6d26934d2492492492492249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨43, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨68, by decide⟩, ⟨71, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨96, by decide⟩, ⟨98, by decide⟩, ⟨100, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "400000080000009dfff000000", 2336462209024, hexnat% "100002600000000000", hexnat% "1000026000000000000000000", hexnat% "10000010000001000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1000001680000163fff3000000", 201326592, hexnat% "1000000100000000000000000", hexnat% "4000020000002080000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "110000169000016202a3000000", hexnat% "4000020000002080000000000", 104152956928, 433791696896, 1649737203712]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "15000036900003680080000000", 78920024064, 193307082752, 3848559132672, 275096010752]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40000128000000bffdf000000", hexnat% "1000024000000000000000000", hexnat% "100002600000000000", hexnat% "10000000000001000020000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "110000129000036bffff000000", hexnat% "24000000000000000000", hexnat% "4000000000000000000000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "110000369000036a13ff000000", hexnat% "4000000000000000000000000", 188978561024, 1924145348608]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c7 c6
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "100000129000010bffff000000", hexnat% "1000024000000000000000000", 668503069687808, hexnat% "4000000000000000000000000"]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "100000129000010a3fff000000", 1924145348608, hexnat% "1000024000000000000000000", 668503069687808, hexnat% "4000000000000000000000000"]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c10 c9
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨68, by decide⟩ c11 c8
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "150000369000036801a0000000", 266321526784, 3848559132672, 275096010752, 1073741824]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1200000023dbfd000000", 154652377088, hexnat% "1000000100000000000000000", hexnat% "4000020800002080000000000", hexnat% "10000004000001400000000000"]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "10000121000002001e0000000", hexnat% "10000004000001400000000000", hexnat% "4000020800002080000000000", 3848559132672, 266321526784, 275096010752]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c15 c14
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c16 c13
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c17 c12
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c18 c5
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨73, by decide⟩ c19 c4
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨76, by decide⟩ c20 c3
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c21 c0
  c22
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00016.record005_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00016.record005_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00016.record005_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00016.record005_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00016.record005_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00016.record005_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00016.record005_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00016.record005_validity Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00016.record005_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow30Part00016.record005

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow30Part00016.record011
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00016.record011
def vertexColumn : Fields := ⟨10, hexnat% "3b06e1783e334ad13c2f07ce89b25c8f2e29aa5a8ea6695a3693a2e87ac9aa6999362d876c3a8e4b8ae1b91e2785e0fba1e4731ac5b15c4f1e2599564d9c96a599715a56354d4b51d70da351d27783c8ea368e6358ce364d5334d332cc73c2e8b62d4b32d1b26c5bc1e8791e2749ca719d1725c570de0f43c8f07c7417322a8a261984e46499164551341dc0e8342c8b12e0711c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "db6db6936db6db6db49369b6d369b6db6da49b6db6d369249b6db6db4924924926d369a491249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨26, by decide⟩, ⟨29, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨61, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨82, by decide⟩, ⟨85, by decide⟩, ⟨90, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩, ⟨95, by decide⟩, ⟨109, by decide⟩, ⟨110, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4000042400000000000004000000", 2359886209573978112, hexnat% "2000e00000000000000000000000", hexnat% "1c00600007000200000", 72057654184247296, 17042442813440]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00016.record011_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00016.record011_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00016.record011_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00016.record011_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00016.record011_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00016.record011_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00016.record011_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00016.record011_validity Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00016.record011_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow30Part00016.record011

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow30Part00016.record012
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00016.record012
def vertexColumn : Fields := ⟨10, hexnat% "3a2e49b25c8f2e29aa5a8ea6695a36b26a9a66c5a964d8b61db0ea392e2b86e4789ee87916c5713c7896a5693a599564d9c96a599715a55352d475c368d4b4ad1b51d27783c8ea368e6358ce3c4e9364d5334d332cc73c2e8b62d4b32d2b2ac6b46c9b16f07a1e4789d2729c6785d1725c570de0f43c8f13c2f07c5cc8aa24689a16a26198561381ec86a14649916625194551341d"⟩
def kindColumn : Fields := ⟨3, hexnat% "9b6db6d24926db4db6924db6db6924936da6db49349b6db6db6db6db6d24db4da6da6db4d1249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨21, by decide⟩, ⟨23, by decide⟩, ⟨28, by decide⟩, ⟨32, by decide⟩, ⟨35, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨72, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩, ⟨99, by decide⟩, ⟨104, by decide⟩, ⟨105, by decide⟩, ⟨106, by decide⟩, ⟨107, by decide⟩, ⟨108, by decide⟩, ⟨109, by decide⟩, ⟨118, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "10840002108c000038910a00000", hexnat% "700060000000000000000", hexnat% "3800300000000000000000000000", hexnat% "800c0000000000000000000", hexnat% "400600000000000000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "21080000000110800000", hexnat% "108400000000000000000000000", hexnat% "800c000c000000800000000", hexnat% "700060000038000200000", hexnat% "400600000000000000000000000000", hexnat% "3800300000000000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨23, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c2 c0
  c3
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00016.record012_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00016.record012_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00016.record012_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00016.record012_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00016.record012_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00016.record012_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00016.record012_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00016.record012_validity Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00016.record012_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow30Part00016.record012
