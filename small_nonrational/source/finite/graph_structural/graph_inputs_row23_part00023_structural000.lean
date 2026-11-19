module
prelude
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow23Part00023Data
public import GraphInputsRow23Part00023Frames
public import GraphInputsRow23Part00023Leaves
public import GraphInputsRow23Part00023Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00023.record063
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00023.record063
def vertexColumn : Fields := ⟨10, hexnat% "1d26a99a959561da2e2b86e879d16a599955551d62d2b46d875c368d6338f13a4e5334cb31cf0ba2d4b8ad2b1ae1b46c9b91d4789ca745c970dd0f23c4f07d925498a2a866858568382e64551624a9196151560d0b58350ca318e1344c9314e0b42c8b0ae0711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "2492492492492492492492492492492492492449249249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "9f07d669ebff800000000", hexnat% "200800000000000000000", hexnat% "1004001000000000000000", 27373441485111296, hexnat% "3008000000000000000", 648518346341351424, hexnat% "408020000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1f27d669ebff800000000", hexnat% "200800000000000000000", hexnat% "1004001000000000000000", 27373441485111296, hexnat% "c00008000000000000000", 648518346341351424, hexnat% "9020000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1b06d6692bed800000000", hexnat% "200800000010000000000", hexnat% "1004001000000000000000", hexnat% "40100008002000000000", 28499341391953920, 9871890383196127232, hexnat% "409020000000000000000", hexnat% "802000000000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨67, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨77, by decide⟩ c3 c0
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "17bcedf78effb800000000", 585749426534875136, hexnat% "40100000004000000000", hexnat% "802000000000000000000", 22517998136852480, hexnat% "1020000000000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "17b42df38effb800000000", hexnat% "802000020000000000000", 22518273014759424, 864972603431845888, hexnat% "40100000000000000000", hexnat% "c00000000000000000", hexnat% "9020000000000000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨81, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "13b0ece78e7ff800000000", hexnat% "40100000000000000000", hexnat% "802000020000000000000", 1729804469375336448, hexnat% "5010000000000000000", 22517998136852480, hexnat% "408020000000000000000"]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "11b02ce18e7db800000000", hexnat% "40100000004000000000", hexnat% "802000020000000000000", hexnat% "200800400020000000000", hexnat% "11050800000000000", 720857415355990016, hexnat% "409020000000000000000", hexnat% "4400000000000000000"]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨80, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨84, by decide⟩ c10 c7
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "a8abecdfffff800000000", hexnat% "100400200000000000000", hexnat% "401010000000000000000", hexnat% "70000000000000000000", hexnat% "1004001000000000000000", 2305843009213693952]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1afcbfe7af7ff800000000", hexnat% "100400000000000000000", hexnat% "3000000000000000000", 1729522994398625792, hexnat% "400000000000000000000", 22517998136852480]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "12fcbfe7bf7ff800000000", hexnat% "100400000000000000000", 1171076640604684288, 576460752303423488, hexnat% "802000000000000000000", hexnat% "401000000000000000000"]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "13bce3e7af7ff800000000", hexnat% "40100000000000000000", 1729522994398625792, hexnat% "802000000000000000000", 22517998136852480, hexnat% "c0000000000000000", hexnat% "401000000000000000000"]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨76, by decide⟩ c15 c14
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨77, by decide⟩ c16 c13
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "288a3fffffff800000000", hexnat% "1c0000000000000000", hexnat% "100400000000000000000", hexnat% "70000000000000000000", hexnat% "3000000000000000000", hexnat% "1004000000000000000000", hexnat% "c00000000000000000000"]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "388e266e13ff800000000", hexnat% "40100008000000000000", hexnat% "10040012000000000000", 1801510219692376064, hexnat% "802008004000000000000", hexnat% "20080000000000000000", hexnat% "5010000800000000000", hexnat% "1400000000000000000000"]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c19 c18
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨61, by decide⟩ c20 c17
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c21 c12
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "107c1f3fdffff800000000", hexnat% "e00000000000000000", hexnat% "401008000000000000000", hexnat% "380000000000000000000", hexnat% "802000020000000000000", 4611686018427387904]
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1bfa5ff69fbff800000000", hexnat% "a00000000000000000", hexnat% "5000000000000000000", 27091966508400640, hexnat% "400000000000000000000", 648518346341351424]
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "bfa3ff79fbff800000000", hexnat% "c00000000000000000", 27091966508400640, 576460752303423488, hexnat% "1004000000000000000000", hexnat% "401000000000000000000"]
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "9fa1ff69fbff800000000", hexnat% "200800000000000000000", 27091966508400640, hexnat% "1004000000000000000000", 648518346341351424, hexnat% "600000000000000000", hexnat% "401000000000000000000"]
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨79, by decide⟩ c26 c25
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨80, by decide⟩ c27 c24
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "5817fffffff800000000", hexnat% "20080000000000000000", hexnat% "e00000000000000000", hexnat% "380000000000000000000", hexnat% "3000000000000000000", hexnat% "1004000000000000000000", hexnat% "c00000000000000000000"]
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "781e780f3ff800000000", hexnat% "200800400000000000000", hexnat% "80200180000000000000", 31665934879948800, hexnat% "1004010200000000000000", hexnat% "100400000000000000000", hexnat% "3008000400000000000", hexnat% "c00000000000000000000"]
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c30 c29
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨62, by decide⟩ c31 c28
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c32 c23
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2a0a89f81ffb800000000", hexnat% "409020000000000000000", hexnat% "100400000004000000000", hexnat% "140000000000000000", hexnat% "802004004000000000000", hexnat% "1004012000000000000000", hexnat% "50000000000000000000", 34339947158700032]
  let c35 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1c00003d0000000000", hexnat% "e00000000000000000", hexnat% "70000000000000000000", hexnat% "380000000000000000000", hexnat% "409020001c00800000000", hexnat% "80200c004000000000000", hexnat% "1004012200000000000000", 2125701772897943552, 34340428195037184]
  let c36 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c35 c34
  let c37 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c36 c33
  let c38 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c37 c22
  let c39 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c38 c11
  let c40 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c39 c4
  c40
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00023.record063_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00023.record063_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00023.record063_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00023.record063_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00023.record063_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00023.record063_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00023.record063_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00023.record063_validity Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00023.record063_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00023.record063

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00023.record062
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "256558768b8ae1ba1e745a966565c559595475c358d5362d4b4ad1b61d474e3a4d9394d5334cb31ce8b62e2b1ae1b26e4751e2729d1725c3743c8f13c1f550aa19a1615a0e0b991545892a54519615454558350d0b4a318e1324c5382c8b0ae0711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "2492492492492492492492492492492492492249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00023.record062 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00023.record062 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00023.record062.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00023.record062.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00023.record062.data.quota

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00023.record062 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00023.record062_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00023.record062" "{\"atoms\":[{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00023.record062" 16

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00023.record062" "{\"ridges\":[[9,146],[14,268],[22,265],[35,268],[37,146],[47,265],[50,146],[51,146],[55,146],[57,268],[61,268],[63,268],[64,268],[65,268],[71,145],[72,265]],\"owners\":[[71,145,[9,37,50,51,55],[24,43,68,73]],[9,146,[],[37,43,50,51,54,55]],[37,146,[],[9,43,50,51,54,55]],[50,146,[],[9,37,43,51,54,55]],[51,146,[],[9,37,43,50,54,55]],[55,146,[],[9,37,43,50,51,54]],[22,265,[14,35,57,61,63,65],[47,71,72]],[47,265,[14,57,61,63,65],[22,35,71,72]],[72,265,[14,35,57,63,65],[22,47,61,71]],[14,268,[],[35,57,61,63,64,65]],[35,268,[],[14,57,61,63,64,65]],[57,268,[],[14,35,61,63,64,65]],[61,268,[],[14,35,57,63,64,65]],[63,268,[],[14,35,57,61,64,65]],[64,268,[],[14,35,57,61,63,65]],[65,268,[],[14,35,57,61,63,64]]],\"edges\":[[28,[14,22,35,47,57,61,63,64,65,71,72]]],\"groupings\":[]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00023.record062" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00023.record062\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-15,1,5,7,8,9],[-1],[-5],[-7],[-8],[-9],[-3,2,4,10,11,12,14],[-6,2,10,11,12,14],[-16,2,4,10,12,14],[-2],[-4],[-10],[-11],[-12],[-13],[-14],[2,3,4,6,10,11,12,13,14,15,16]],\"atoms\":[{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72}],\"rules\":[{\"tag\":\"mate\",\"ridge\":145,\"a\":71,\"owners\":[9,37,50,51,55]},{\"tag\":\"mate\",\"ridge\":146,\"a\":9,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":146,\"a\":37,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":146,\"a\":50,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":146,\"a\":51,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":146,\"a\":55,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":265,\"a\":22,\"owners\":[14,35,57,61,63,65]},{\"tag\":\"mate\",\"ridge\":265,\"a\":47,\"owners\":[14,57,61,63,65]},{\"tag\":\"mate\",\"ridge\":265,\"a\":72,\"owners\":[14,35,57,63,65]},{\"tag\":\"mate\",\"ridge\":268,\"a\":14,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":268,\"a\":35,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":268,\"a\":57,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":268,\"a\":61,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":268,\"a\":63,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":268,\"a\":64,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":268,\"a\":65,\"owners\":[]},{\"tag\":\"edge\",\"edge\":28,\"owners\":[14,22,35,47,57,61,63,64,65,71,72]}]}"
  "p cnf 16 17\n-15 1 5 7 8 9 0\n-1 0\n-5 0\n-7 0\n-8 0\n-9 0\n-3 2 4 10 11 12 14 0\n-6 2 10 11 12 14 0\n-16 2 4 10 12 14 0\n-2 0\n-4 0\n-10 0\n-11 0\n-12 0\n-13 0\n-14 0\n2 3 4 6 10 11 12 13 14 15 16 0\n"
  "18 -15 0 6 2 3 4 5 1 0\n19 -16 0 16 10 11 12 14 9 0\n20 -6 0 16 10 12 13 14 8 0\n21 -3 0 16 10 11 12 13 14 7 0\n22 0 10 21 11 20 12 13 14 15 16 18 19 17 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00023.record062.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00023.record062.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00023.record062.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00023.record062.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00023.record062 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00023.record062.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00023.record062.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00023.record062.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00023.record062.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00023.record062 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00023.record062_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00023.record062_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00023.record062_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00023.record062_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00023.record062_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00023.record062_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00023.record062_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00023.record062 Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00023.record062_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00023.record062_validity Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00023.record062_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00023.record062
