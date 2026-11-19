module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow31Part00088Data
public import GraphInputsRow31Part00088Frames
public import GraphInputsRow31Part00088Leaves
public import GraphInputsRow31Part00088Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00088.record000
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00088.record000
def vertexColumn : Fields := ⟨10, hexnat% "f81d8ae2e4792d4ad1cc6b0dc2f3c2e8b62b89e2b49d2ac9caaa9aaa699a568da8e8bab19c6a99a69996639a96958d68d8b66394e3392e2b89e1783ef07a1d86e1786d1746b1726a96a69966559366392e6c5716a569665594e5a5655356352d58d534cd4b4ad2745d0f743c8e6358d538cd4b8ae1b46c5b0ee4751e2749c6785c3743c4fb41a8350ac272524a8560b81e945291542d0764350e2348e1314d0b0ac1b11c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "1b6da6d24db6d36da6db6db6db6d26db69249b6da6db4db6db6db6da4db6d2492492492492492492249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨75, by decide⟩, ⟨80, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨96, by decide⟩, ⟨97, by decide⟩, ⟨112, by decide⟩, ⟨117, by decide⟩, ⟨123, by decide⟩, ⟨124, by decide⟩, ⟨125, by decide⟩, ⟨128, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "10000000008000000005f6ff30000000", 9898825875456, hexnat% "20010000040008000020000000000000", hexnat% "100000818000000000000", hexnat% "100200003000000001000000000000000", hexnat% "8000000034000000002000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3800000006c10800083f5ffff0000000", 175921860444160, hexnat% "210001010000000000000000000000", hexnat% "100000002000000001000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1000000000c0000000175ffff0000000", 175921860444160, hexnat% "8000000010000000008000000000000", hexnat% "20010000040008000020000000000000", hexnat% "100000002000100001800000000000000", hexnat% "200001020000000000000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨52, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "11800000300c10800181ffff6d0000000", hexnat% "210000030000000000000000000000", 39191576576, hexnat% "20000000040000000020000000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8000000004000000803fff6d0000000", 39191576576, hexnat% "1000000001800000000c000000000000", hexnat% "100200002000100001000000000000000", hexnat% "20000000040008000030000000000000", hexnat% "10001020000000000000000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "280000000440080000328fe6f0000000", 404727653203968, hexnat% "210001030000000000000000000000", hexnat% "1000000000800000080c000000000000", hexnat% "100000002000100001000000000000000"]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "282100030740000010337ffbf0000000", hexnat% "108000808000000000000", 140754668224512, hexnat% "110000000000000000000000000000000", hexnat% "8000000004000000000000"]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "11821000303c10000180f7df990000000", 142963355156480, hexnat% "20000000040000000020000020000000", hexnat% "8000010000000000000"]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1202100030701080018397df990000000", 142963355156480, hexnat% "8000000004000000002000000000000", 536870912, hexnat% "10000000008000000004000000000000"]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20010002074008001031fffff0000000", hexnat% "100200000000100000000000000000000", hexnat% "800000000000000000a000000000000", hexnat% "10000001008000000804000000000000"]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2070008001001ffffd0000000", hexnat% "210001000000000000000000000000", hexnat% "100000000000100000800000000000000", hexnat% "20000000000000000020000020000000", hexnat% "1000000000800000000c000000000000", hexnat% "8000000004000000012000000000000"]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨90, by decide⟩ c12 c11
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨75, by decide⟩ c13 c10
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨88, by decide⟩ c14 c9
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨89, by decide⟩ c15 c8
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1100000020081000018051df8f0000000", 248519692648448, hexnat% "210001030000000000000000000000", hexnat% "800000000400000001a000000000000", hexnat% "20000000040008000020000000000000"]
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "110210003078000001824fff7f0000000", 281509336449024, hexnat% "108000018000000000000", hexnat% "8000000004000000002000000000000", hexnat% "20000000000000000000000000000000"]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1821000107c00000002fffff70000000", hexnat% "20000000000008000010000000000000", hexnat% "100000002000000001000000080000000", hexnat% "100000800000000000000"]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1050000000021ffff70000000", hexnat% "20010000000008000000000000000000", hexnat% "8000000004000080000000", hexnat% "8000000024000000012000000000000", hexnat% "100200002000100001000000000000000", hexnat% "10000000000000000808000000000000"]
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨88, by decide⟩ c20 c19
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨96, by decide⟩ c21 c18
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3000000305c00000082d7ffbf0000000", 140754668224512, hexnat% "8000000020000000012000000000000", hexnat% "10000000008000000000000000000", hexnat% "100200000000100001000000000000000"]
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3000000305c00000082cffeff0000000", 281543696187392, hexnat% "8000000020000000012000000000000", hexnat% "10000000008000000000000000000", hexnat% "100200000000100001000000000000000"]
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1000000301c00000080c1feaf0000000", hexnat% "8000000020000000012000000000000", 527769876299776, hexnat% "100200000000100001000000000000000", hexnat% "20010000040008000020000000000000", 85899345920]
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c25 c24
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c26 c23
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "13821000307c00000183e3feb70000000", 70456791007232, 422212465065984, hexnat% "108000000000000000000"]
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "13800000307c10800183e3feb70000000", 70456791007232, 422212465065984, hexnat% "210000000000000000000000000000"]
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2000000104c000000823ffeb70000000", hexnat% "10000000008000000000000000000", hexnat% "1000000001000000000c000000000000", hexnat% "8000000020000000010000000000000", hexnat% "100000002000000001000001480000000", hexnat% "200000000100000000000000000000"]
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c30 c29
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨96, by decide⟩ c31 c28
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "11800000300c10800181ebffff0000000", 351843720888320, hexnat% "210000030000000000000000000000", hexnat% "20000000040000000020000000000000"]
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "800000000c000000806bffff0000000", 351843720888320, hexnat% "10000000010000000008000000000000", hexnat% "100200002000100001000000000000000", hexnat% "20000000040008000030000000000000", hexnat% "10001020000000000000000000000"]
  let c35 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c34 c33
  let c36 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1102000030081000018001ff4f0000000", hexnat% "1000000000e000000000000", 527769876299776, hexnat% "20010000040008000020000000000000", hexnat% "8000000024000000010000000000000", 42949672960]
  let c37 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "12821000107c0000000321fe0f0000000", hexnat% "108000808000000000000", hexnat% "10000000000000000004000000000000", 105600360906752, 422212465065984, hexnat% "2000000001000001400000000"]
  let c38 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "12800000006c10800083a1fe0f0000000", hexnat% "210001010000000000000000000000", hexnat% "10000000000000000004000000000000", 105600360906752, 422212465065984, hexnat% "2000000001000001400000000"]
  let c39 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1000000020280000010117ffdf0000000", 140746078289920, hexnat% "200000000100000000000000000000", hexnat% "800000001400000000a000000000000", hexnat% "10000001000000000804000000000000", hexnat% "20010000040008000020000000000000"]
  let c40 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "120000000068000000031fe7f70000000", 1651414925312, hexnat% "10000000008000000000000000000", hexnat% "800000001400000000a000000000000", hexnat% "200002000100001000000000000000", hexnat% "10000001000000000804000000000000"]
  let c41 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1000000000280000000101ff8f0000000", 527769876299776, hexnat% "800000001400000000a000000000000", hexnat% "20010000040008000020000000000000", hexnat% "200002000100001000000000000000", hexnat% "10000001000000000804000000000000", 25769803776]
  let c42 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c41 c40
  let c43 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c42 c39
  let c44 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨52, by decide⟩ c43 c38
  let c45 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨89, by decide⟩ c44 c37
  let c46 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨128, by decide⟩ c45 c36
  let c47 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c46 c35
  let c48 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c47 c32
  let c49 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨87, by decide⟩ c48 c27
  let c50 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c49 c22
  let c51 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c50 c17
  let c52 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c51 c16
  let c53 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c52 c7
  let c54 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c53 c6
  let c55 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c54 c3
  let c56 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c55 c0
  c56
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00088.record000_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00088.record000_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00088.record000_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00088.record000_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00088.record000_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00088.record000_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00088.record000_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00088.record000_validity Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00088.record000_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00088.record000
