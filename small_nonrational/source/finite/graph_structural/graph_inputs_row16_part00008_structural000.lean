module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow16Part00008Data
public import GraphInputsRow16Part00008Frames
public import GraphInputsRow16Part00008Leaves
public import GraphInputsRow16Part00008Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00008.record037
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record037
def vertexColumn : Fields := ⟨10, hexnat% "2f34acaa6a2ea662d8ae1b91e2785e0fb49ca6692e6652d4ad1b51d2745d0f743c8ea398f1364cb3c2e4b52e2b4acab1ac9b16c3b91cc789c6745c570dd0f23d1a298961382e07919294951342d0770390e2328d1324d0b12c2b06c8711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "1b6db4924936db492492492492492492492492449249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1c01c0907ff8000000", hexnat% "400400010000000000", 4829055069192192, hexnat% "200202008000000000", hexnat% "820820400000000000", 3384296790294528]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [5066519381803008, 3940658263883776, 279223176896970752, hexnat% "3e0000000000000000", hexnat% "800800000400000000", hexnat% "400400000100000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "ee0c80494768000000", 243194380146442240, hexnat% "100000003080000000", 457396837154816, 7335975940259840, 1133046732423168]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "fe0fe0481078000000", 23622320128, 422487342972928, 7318392344150016, 1134146244050944, 52913997086720]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "5c05e1cbf0f8000000", hexnat% "820800000000000000", hexnat% "200202000100000000", 6812574045700096, 60129542144, 1125899906842624]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "760361fff5f8000000", hexnat% "80480000000000000", hexnat% "800800000000000000", 7318392344150016, 1125899906842624]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "54017bbff8d8000000", 468374361246531584, hexnat% "2a0000000000000000", hexnat% "800800400420000000", 1125912791744512]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "400021a860d0000000", 270215977642229760, hexnat% "3e0000000000000000", hexnat% "800800400428000000", 7335975940259840, 288231488548241408, 1133115451899904]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c7 c6
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c8 c5
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c9 c4
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c10 c3
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨70, by decide⟩ c11 c2
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c12 c1
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c13 c0
  c14
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record037_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record037_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record037_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record037_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record037_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record037_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record037_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record037_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record037_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00008.record037

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00008.record043
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record043
def vertexColumn : Fields := ⟨10, hexnat% "1f0da1eb261d98e4b8ae1b91e2785e0fb49ca66936479c94756352d2b46d4745d0f743c8e5334c7362d4b32d2b2ac6b46c9b16c3bc1d8789d2729c6745c570dd0f23c4f0bc1f2726225a611a499164954348d0b41dc0e4388c6324c5341c8709c17"⟩
def kindColumn : Fields := ⟨3, hexnat% "1b6db6db4db6926d249249249b6da693492492493489249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨23, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨40, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨67, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [1970324836974592, 5764678991290040320, hexnat% "80000006006c00000", 2305983746702049280, 67243081728, 285978576338026496, 1342177280]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record043_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record043_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record043_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record043_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record043_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record043_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record043_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record043_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00008.record043_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00008.record043
