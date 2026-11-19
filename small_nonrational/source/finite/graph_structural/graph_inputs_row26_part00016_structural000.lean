module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow26Part00016Data
public import GraphInputsRow26Part00016Frames
public import GraphInputsRow26Part00016Leaves
public import GraphInputsRow26Part00016Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00016.record033
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record033
def vertexColumn : Fields := ⟨10, hexnat% "3b0793346d32c5b23c788ea36a3a2e9c669966398d62d86e17ba1e4731ac5b1d2729366392e5c5c95a5c5595356354d4b5c354d8b52d8745d0f5c368cd38ccb332e2b2ae1b26c5b0ed8751cc749ca725c570dc2f8e03c2c83a0d84e0b81e706195144d074c324c4b06c4705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "db6da6da4db6d24db6db69a6db6db69b49269a4da49349b492249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨20, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨38, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨46, by decide⟩, ⟨56, by decide⟩, ⟨58, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨80, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2001000159ece00000", 74766790688768, hexnat% "180000000000100000", hexnat% "118000000000000000000", 288241371267989504]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1800000c49e4d00000", 72058693683773440, 70368744177664, hexnat% "110000400020000000000", hexnat% "8200000001000200000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "83804000210e0f00000", hexnat% "110000000000000000000", 13198434500608, 1408816381952, 72127962916323328]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "83804004658ecf00000", 72058693549555712, 8800387989504, hexnat% "110000000000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "83804000250e0f00000", hexnat% "110000000000000000000", 13198434500608, 1134072692736, 72127962782105600]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨22, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1800000558c4f00000", 72127962916323328, hexnat% "18200000000020000000", 288241375562956800, hexnat% "100000000000000000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1180004000e51e0a00000", hexnat% "180000000000100000", hexnat% "200100000004000000", 1134005583872, 70368748371968]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "180000005140b00000", 72058693750882304, hexnat% "8000000000880000000", 74766794883072, hexnat% "10200000000020000000", hexnat% "1000004000a0000000000"]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c9 c6
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c10 c5
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨21, by decide⟩ c11 c2
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c12 c1
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨23, by decide⟩ c13 c0
  c14
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record033_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record033_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record033_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record033_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record033_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record033_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record033_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record033_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record033_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00016.record033

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00016.record064
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record064
def vertexColumn : Fields := ⟨10, hexnat% "dc6c8da2eb46c996635a4e33a2e1ba1e2785e0f9b1e2749727296a569364b9d1725594d5934cd8b46d8749d17783d0f2368d6364cd34ccb3a2e4b32e2b2ac6b86c9b16c3bc1e4751cc789d2719e1725c5783c8f13c2f07c3c70836704c9264390d60d1342d0770360d4330d2324c3381c4709c17"⟩
def kindColumn : Fields := ⟨3, hexnat% "36db6db6db6d36d36d26db4924924924926d36da6924924924d2449249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨40, by decide⟩, ⟨45, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨73, by decide⟩, ⟨77, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "230449c211ef2000000", 99079333536071680, hexnat% "20000000004009800000", 844424930131968, 13402712491054596096]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [143835362114928640, hexnat% "2204000200000000000", hexnat% "2000000000000a800000", hexnat% "100e00000000000000", 12682136550675316736]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "230fe0420051b800000", hexnat% "20000000014000000000", 81067507712, 12103423998558208, 130604560992436224]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "22043f4203fd2000000", 3096225280688128, hexnat% "20000000014009800000", hexnat% "100c00000000000000", 12682136550675316736]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2220236f217ffb800000", 40532396646334464, hexnat% "100c00000000000000", 14987979559889010688]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2206246203ffb800000", hexnat% "20000000014000000000", 123848989752688640, hexnat% "100001000000000000", 11240984669916758016]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "22043ff210f20000000", 209782308864, hexnat% "100400004000800000", hexnat% "20000000000003000000", 13258597302978740224]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "220420d203ffb800000", hexnat% "20000000014000000000", 140174538401906688, hexnat% "100c00000000000000", 12682136550675316736]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2000fe8f215ffb800000", hexnat% "300000000000000000", hexnat% "2000000000000000000", 103582928868474880]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [18340909757268754432, hexnat% "2200004200000000000", hexnat% "20000000014000000000", 104145741382942720, hexnat% "100001000000000000"]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c10 c9
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [9510195587761307648, hexnat% "2200004200000000000", hexnat% "100400010000800000", hexnat% "20000000000002000000", 8646911284551352320]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "220820e200f10000000", 139611725887438848, hexnat% "2000000001400b800000", hexnat% "100001000000000000", 72477573120, 8935141660703064064]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c13 c12
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c14 c11
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c15 c8
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c16 c7
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c17 c6
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c18 c3
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c19 c2
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c20 c1
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c21 c0
  c22
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record064_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record064_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record064_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record064_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record064_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record064_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record064_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record064_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record064_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00016.record064

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00016.record065
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record065
def vertexColumn : Fields := ⟨10, hexnat% "6d34ccb16c371b2d2b2a5a8dae1b4671b2669966658d64d8b6c3a4e538ce8b92e1ba1e2785e0f8d9e17457172569565354b5934cd8b46d8749d17783d0dc3c8da358cd32ce4b32e2b1ae1b26c5bc1e8761e4751cc789d2729c6785c9715c3783c8f13c2f07dc40f1c20e839314950d60d1342d074c324c3382c4b0ac1b"⟩
def kindColumn : Fields := ⟨3, hexnat% "6db6db6db4db6db6db6db6d36d36d249249369b69249249b6da6db69a4d2449249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨19, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨26, by decide⟩, ⟨32, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨50, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨65, by decide⟩, ⟨69, by decide⟩, ⟨87, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8000020004000100000000", 1152956689063346176, hexnat% "200000000000b00000", 2314920852090519552, 34634616274944, 1134907106097364992]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record065_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record065_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record065_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record065_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record065_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record065_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record065_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record065_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00016.record065_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00016.record065
