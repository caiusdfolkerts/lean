module
public meta import NumericProofSchema
public meta section
open Lean Elab Command

elab "cert_badTest " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def badTest_⟪0⟫ (i : Nat) := badTest (i+⟪0⟫)"### args

elab "cert_badTestInterval " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem badTestInterval⟪0⟫ : Interval badTest ⟪0⟫ ⟪1⟫ := by
  intro i hlo hhi
  have h := badTest_⟪0⟫_complete (i-⟪0⟫) (Nat.zero_le _) (by omega)
  simpa only [badTest_⟪0⟫, Nat.sub_add_cancel hlo] using h"### args

elab "cert_badTest_block " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem badTest_⟪0⟫_block_⟪1⟫ : Interval badTest_⟪0⟫ ⟪2⟫ ⟪3⟫ :=
  interval_of_check badTest_⟪0⟫ ⟪2⟫ ⟪4⟫ (by decide +kernel)"### args

elab "cert_badTest_complete " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem badTest_⟪0⟫_complete : Interval badTest_⟪0⟫ 0 ⟪1⟫ :=
  (interval_append badTest_⟪0⟫ 0 72 ⟪1⟫
  (interval_append badTest_⟪0⟫ 0 32 72
  (interval_append badTest_⟪0⟫ 0 16 32
  (interval_append badTest_⟪0⟫ 0 8 16
  badTest_⟪0⟫_block_0
  badTest_⟪0⟫_block_1)
  (interval_append badTest_⟪0⟫ 16 24 32
  badTest_⟪0⟫_block_2
  badTest_⟪0⟫_block_3))
  (interval_append badTest_⟪0⟫ 32 48 72
  (interval_append badTest_⟪0⟫ 32 40 48
  badTest_⟪0⟫_block_4
  badTest_⟪0⟫_block_5)
  (interval_append badTest_⟪0⟫ 48 56 72
  badTest_⟪0⟫_block_6
  (interval_append badTest_⟪0⟫ 56 64 72
  badTest_⟪0⟫_block_7
  badTest_⟪0⟫_block_8))))
  (interval_append badTest_⟪0⟫ 72 112 ⟪1⟫
  (interval_append badTest_⟪0⟫ 72 88 112
  (interval_append badTest_⟪0⟫ 72 80 88
  badTest_⟪0⟫_block_9
  badTest_⟪0⟫_block_10)
  (interval_append badTest_⟪0⟫ 88 96 112
  badTest_⟪0⟫_block_11
  (interval_append badTest_⟪0⟫ 96 104 112
  badTest_⟪0⟫_block_12
  badTest_⟪0⟫_block_13)))
  (interval_append badTest_⟪0⟫ 112 128 ⟪1⟫
  (interval_append badTest_⟪0⟫ 112 120 128
  badTest_⟪0⟫_block_14
  badTest_⟪0⟫_block_15)
  (interval_append badTest_⟪0⟫ 128 136 ⟪1⟫
  badTest_⟪0⟫_block_16
  (interval_append badTest_⟪0⟫ 136 144 ⟪1⟫
  badTest_⟪0⟫_block_17
  badTest_⟪0⟫_block_18)))))"### args

elab "cert_badTest_complete_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem badTest_256_complete : Interval badTest_256 0 240 :=
  (interval_append badTest_256 0 120 240
  (interval_append badTest_256 0 56 120
  (interval_append badTest_256 0 24 56
  (interval_append badTest_256 0 8 24
  badTest_256_block_0
  (interval_append badTest_256 8 16 24
  badTest_256_block_1
  badTest_256_block_2))
  (interval_append badTest_256 24 40 56
  (interval_append badTest_256 24 32 40
  badTest_256_block_3
  badTest_256_block_4)
  (interval_append badTest_256 40 48 56
  badTest_256_block_5
  badTest_256_block_6)))
  (interval_append badTest_256 56 88 120
  (interval_append badTest_256 56 72 88
  (interval_append badTest_256 56 64 72
  badTest_256_block_7
  badTest_256_block_8)
  (interval_append badTest_256 72 80 88
  badTest_256_block_9
  badTest_256_block_10))
  (interval_append badTest_256 88 104 120
  (interval_append badTest_256 88 96 104
  badTest_256_block_11
  badTest_256_block_12)
  (interval_append badTest_256 104 112 120
  badTest_256_block_13
  badTest_256_block_14))))
  (interval_append badTest_256 120 176 240
  (interval_append badTest_256 120 144 176
  (interval_append badTest_256 120 128 144
  badTest_256_block_15
  (interval_append badTest_256 128 136 144
  badTest_256_block_16
  badTest_256_block_17))
  (interval_append badTest_256 144 160 176
  (interval_append badTest_256 144 152 160
  badTest_256_block_18
  badTest_256_block_19)
  (interval_append badTest_256 160 168 176
  badTest_256_block_20
  badTest_256_block_21)))
  (interval_append badTest_256 176 208 240
  (interval_append badTest_256 176 192 208
  (interval_append badTest_256 176 184 192
  badTest_256_block_22
  badTest_256_block_23)
  (interval_append badTest_256 192 200 208
  badTest_256_block_24
  badTest_256_block_25))
  (interval_append badTest_256 208 224 240
  (interval_append badTest_256 208 216 224
  badTest_256_block_26
  badTest_256_block_27)
  (interval_append badTest_256 224 232 240
  badTest_256_block_28
  badTest_256_block_29)))))"### args

elab "cert_badTest_complete_3 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem badTest_⟪0⟫_complete : Interval badTest_⟪0⟫ 0 ⟪1⟫ :=
  (interval_append badTest_⟪0⟫ 0 40 ⟪1⟫
  (interval_append badTest_⟪0⟫ 0 16 40
  (interval_append badTest_⟪0⟫ 0 8 16
  badTest_⟪0⟫_block_0
  badTest_⟪0⟫_block_1)
  (interval_append badTest_⟪0⟫ 16 24 40
  badTest_⟪0⟫_block_2
  (interval_append badTest_⟪0⟫ 24 32 40
  badTest_⟪0⟫_block_3
  badTest_⟪0⟫_block_4)))
  (interval_append badTest_⟪0⟫ 40 56 ⟪1⟫
  (interval_append badTest_⟪0⟫ 40 48 56
  badTest_⟪0⟫_block_5
  badTest_⟪0⟫_block_6)
  (interval_append badTest_⟪0⟫ 56 64 ⟪1⟫
  badTest_⟪0⟫_block_7
  (interval_append badTest_⟪0⟫ 64 72 ⟪1⟫
  badTest_⟪0⟫_block_8
  badTest_⟪0⟫_block_9))))"### args

elab "cert_cellTest " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def cellTest_⟪0⟫ (i : Nat) := cellTest (i+⟪0⟫)"### args

elab "cert_cellTestInterval " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem cellTestInterval⟪0⟫ : Interval cellTest ⟪0⟫ ⟪1⟫ := by
  intro i hlo hhi
  have h := cellTest_⟪0⟫_complete (i-⟪0⟫) (Nat.zero_le _) (by omega)
  simpa only [cellTest_⟪0⟫, Nat.sub_add_cancel hlo] using h"### args

elab "cert_cellTest_block " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem cellTest_⟪0⟫_block_⟪1⟫ : Interval cellTest_⟪0⟫ ⟪2⟫ ⟪3⟫ :=
  interval_of_check cellTest_⟪0⟫ ⟪2⟫ ⟪4⟫ (by decide +kernel)"### args

elab "cert_cellTest_complete " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem cellTest_⟪0⟫_complete : Interval cellTest_⟪0⟫ 0 ⟪1⟫ :=
  (interval_append cellTest_⟪0⟫ 0 72 ⟪1⟫
  (interval_append cellTest_⟪0⟫ 0 32 72
  (interval_append cellTest_⟪0⟫ 0 16 32
  (interval_append cellTest_⟪0⟫ 0 8 16
  cellTest_⟪0⟫_block_0
  cellTest_⟪0⟫_block_1)
  (interval_append cellTest_⟪0⟫ 16 24 32
  cellTest_⟪0⟫_block_2
  cellTest_⟪0⟫_block_3))
  (interval_append cellTest_⟪0⟫ 32 48 72
  (interval_append cellTest_⟪0⟫ 32 40 48
  cellTest_⟪0⟫_block_4
  cellTest_⟪0⟫_block_5)
  (interval_append cellTest_⟪0⟫ 48 56 72
  cellTest_⟪0⟫_block_6
  (interval_append cellTest_⟪0⟫ 56 64 72
  cellTest_⟪0⟫_block_7
  cellTest_⟪0⟫_block_8))))
  (interval_append cellTest_⟪0⟫ 72 112 ⟪1⟫
  (interval_append cellTest_⟪0⟫ 72 88 112
  (interval_append cellTest_⟪0⟫ 72 80 88
  cellTest_⟪0⟫_block_9
  cellTest_⟪0⟫_block_10)
  (interval_append cellTest_⟪0⟫ 88 96 112
  cellTest_⟪0⟫_block_11
  (interval_append cellTest_⟪0⟫ 96 104 112
  cellTest_⟪0⟫_block_12
  cellTest_⟪0⟫_block_13)))
  (interval_append cellTest_⟪0⟫ 112 128 ⟪1⟫
  (interval_append cellTest_⟪0⟫ 112 120 128
  cellTest_⟪0⟫_block_14
  cellTest_⟪0⟫_block_15)
  (interval_append cellTest_⟪0⟫ 128 136 ⟪1⟫
  cellTest_⟪0⟫_block_16
  (interval_append cellTest_⟪0⟫ 136 144 ⟪1⟫
  cellTest_⟪0⟫_block_17
  cellTest_⟪0⟫_block_18)))))"### args

elab "cert_cellTest_complete_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem cellTest_256_complete : Interval cellTest_256 0 240 :=
  (interval_append cellTest_256 0 120 240
  (interval_append cellTest_256 0 56 120
  (interval_append cellTest_256 0 24 56
  (interval_append cellTest_256 0 8 24
  cellTest_256_block_0
  (interval_append cellTest_256 8 16 24
  cellTest_256_block_1
  cellTest_256_block_2))
  (interval_append cellTest_256 24 40 56
  (interval_append cellTest_256 24 32 40
  cellTest_256_block_3
  cellTest_256_block_4)
  (interval_append cellTest_256 40 48 56
  cellTest_256_block_5
  cellTest_256_block_6)))
  (interval_append cellTest_256 56 88 120
  (interval_append cellTest_256 56 72 88
  (interval_append cellTest_256 56 64 72
  cellTest_256_block_7
  cellTest_256_block_8)
  (interval_append cellTest_256 72 80 88
  cellTest_256_block_9
  cellTest_256_block_10))
  (interval_append cellTest_256 88 104 120
  (interval_append cellTest_256 88 96 104
  cellTest_256_block_11
  cellTest_256_block_12)
  (interval_append cellTest_256 104 112 120
  cellTest_256_block_13
  cellTest_256_block_14))))
  (interval_append cellTest_256 120 176 240
  (interval_append cellTest_256 120 144 176
  (interval_append cellTest_256 120 128 144
  cellTest_256_block_15
  (interval_append cellTest_256 128 136 144
  cellTest_256_block_16
  cellTest_256_block_17))
  (interval_append cellTest_256 144 160 176
  (interval_append cellTest_256 144 152 160
  cellTest_256_block_18
  cellTest_256_block_19)
  (interval_append cellTest_256 160 168 176
  cellTest_256_block_20
  cellTest_256_block_21)))
  (interval_append cellTest_256 176 208 240
  (interval_append cellTest_256 176 192 208
  (interval_append cellTest_256 176 184 192
  cellTest_256_block_22
  cellTest_256_block_23)
  (interval_append cellTest_256 192 200 208
  cellTest_256_block_24
  cellTest_256_block_25))
  (interval_append cellTest_256 208 224 240
  (interval_append cellTest_256 208 216 224
  cellTest_256_block_26
  cellTest_256_block_27)
  (interval_append cellTest_256 224 232 240
  cellTest_256_block_28
  cellTest_256_block_29)))))"### args

elab "cert_cellTest_complete_3 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem cellTest_⟪0⟫_complete : Interval cellTest_⟪0⟫ 0 ⟪1⟫ :=
  (interval_append cellTest_⟪0⟫ 0 40 ⟪1⟫
  (interval_append cellTest_⟪0⟫ 0 16 40
  (interval_append cellTest_⟪0⟫ 0 8 16
  cellTest_⟪0⟫_block_0
  cellTest_⟪0⟫_block_1)
  (interval_append cellTest_⟪0⟫ 16 24 40
  cellTest_⟪0⟫_block_2
  (interval_append cellTest_⟪0⟫ 24 32 40
  cellTest_⟪0⟫_block_3
  cellTest_⟪0⟫_block_4)))
  (interval_append cellTest_⟪0⟫ 40 56 ⟪1⟫
  (interval_append cellTest_⟪0⟫ 40 48 56
  cellTest_⟪0⟫_block_5
  cellTest_⟪0⟫_block_6)
  (interval_append cellTest_⟪0⟫ 56 64 ⟪1⟫
  cellTest_⟪0⟫_block_7
  (interval_append cellTest_⟪0⟫ 64 72 ⟪1⟫
  cellTest_⟪0⟫_block_8
  cellTest_⟪0⟫_block_9))))"### args

elab "cert_kindSupport_checked " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem kindSupport⟪0⟫_⟪1⟫_checked :
    (kindSupport⟪0⟫_⟪1⟫.all (fun c => decide ((rawCells c).kind = ⟪0⟫))) = true := by decide +kernel"### args

elab "cert_kindSupport_checked_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem kindSupport⟪0⟫_⟪1⟫_checked :
    (kindSupport⟪0⟫_⟪1⟫.all (fun c => decide ((rawCells c).kind = ⟪0⟫))) = true := by decide +kernel"### args

elab "cert_kindSupport_decode " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem kindSupport⟪0⟫_⟪1⟫_decode :
    PackedRawNatGrowth.readList ⟪2⟫ ⟪3⟫ kindSupport⟪0⟫_rest_⟪1⟫ =
      (kindSupport⟪0⟫_⟪1⟫, kindSupport⟪0⟫_rest_⟪4⟫) := by decide +kernel"### args

elab "cert_kindSupport_mask " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem kindSupport⟪0⟫_⟪1⟫_mask : RawNatGrowthCheck.mask kindSupport⟪0⟫_⟪1⟫ = (certNat% ⟪2⟫) := by decide +kernel"### args

elab "cert_kindTest " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def kindTest_0 (i : Nat) := kindTest (i+0)"### args

elab "cert_kindTestInterval " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem kindTestInterval0 : Interval kindTest 0 5 := by
  intro i hlo hhi
  have h := kindTest_0_complete (i-0) (Nat.zero_le _) (by omega)
  simpa only [kindTest_0, Nat.sub_add_cancel hlo] using h"### args

elab "cert_kindTest_block " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem kindTest_0_block_⟪0⟫ : Interval kindTest_0 ⟪0⟫ ⟪1⟫ :=
  interval_of_check kindTest_0 ⟪0⟫ 1 (by decide +kernel)"### args

elab "cert_kindTest_complete " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem kindTest_0_complete : Interval kindTest_0 0 5 :=
  (interval_append kindTest_0 0 2 5
  (interval_append kindTest_0 0 1 2
  kindTest_0_block_0
  kindTest_0_block_1)
  (interval_append kindTest_0 2 3 5
  kindTest_0_block_2
  (interval_append kindTest_0 3 4 5
  kindTest_0_block_3
  kindTest_0_block_4)))"### args

elab "cert_ridgeSupport_checked " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem ridgeSupport⟪0⟫_⟪1⟫_checked :
    (ridgeSupport⟪0⟫_⟪1⟫.all (fun c => hasNat (rawCells c).ridgeMasks ⟪0⟫)) = true := by decide +kernel"### args

elab "cert_ridgeSupport_checked_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem ridgeSupport⟪0⟫_⟪1⟫_checked :
    (ridgeSupport⟪0⟫_⟪1⟫.all (fun c => hasNat (rawCells c).ridgeMasks ⟪0⟫)) = true := by decide +kernel"### args

elab "cert_ridgeSupport_decode " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem ridgeSupport⟪0⟫_⟪1⟫_decode :
    PackedRawNatGrowth.readList ⟪2⟫ ⟪3⟫ ridgeSupport⟪0⟫_rest_⟪1⟫ =
      (ridgeSupport⟪0⟫_⟪1⟫, ridgeSupport⟪0⟫_rest_⟪4⟫) := by decide +kernel"### args

elab "cert_ridgeSupport_mask " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem ridgeSupport⟪0⟫_⟪1⟫_mask : RawNatGrowthCheck.mask ridgeSupport⟪0⟫_⟪1⟫ = (certNat% ⟪2⟫) := by decide +kernel"### args

elab "cert_ridgeTest " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def ridgeTest_⟪0⟫ (i : Nat) := ridgeTest (i+⟪0⟫)"### args

elab "cert_ridgeTestInterval " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem ridgeTestInterval⟪0⟫ : Interval ridgeTest ⟪0⟫ ⟪1⟫ := by
  intro i hlo hhi
  have h := ridgeTest_⟪0⟫_complete (i-⟪0⟫) (Nat.zero_le _) (by omega)
  simpa only [ridgeTest_⟪0⟫, Nat.sub_add_cancel hlo] using h"### args

elab "cert_ridgeTest_block " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem ridgeTest_⟪0⟫_block_⟪1⟫ : Interval ridgeTest_⟪0⟫ ⟪2⟫ ⟪3⟫ :=
  interval_of_check ridgeTest_⟪0⟫ ⟪2⟫ 8 (by decide +kernel)"### args

elab "cert_ridgeTest_complete " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem ridgeTest_⟪0⟫_complete : Interval ridgeTest_⟪0⟫ 0 128 :=
  (interval_append ridgeTest_⟪0⟫ 0 64 128
  (interval_append ridgeTest_⟪0⟫ 0 32 64
  (interval_append ridgeTest_⟪0⟫ 0 16 32
  (interval_append ridgeTest_⟪0⟫ 0 8 16
  ridgeTest_⟪0⟫_block_0
  ridgeTest_⟪0⟫_block_1)
  (interval_append ridgeTest_⟪0⟫ 16 24 32
  ridgeTest_⟪0⟫_block_2
  ridgeTest_⟪0⟫_block_3))
  (interval_append ridgeTest_⟪0⟫ 32 48 64
  (interval_append ridgeTest_⟪0⟫ 32 40 48
  ridgeTest_⟪0⟫_block_4
  ridgeTest_⟪0⟫_block_5)
  (interval_append ridgeTest_⟪0⟫ 48 56 64
  ridgeTest_⟪0⟫_block_6
  ridgeTest_⟪0⟫_block_7)))
  (interval_append ridgeTest_⟪0⟫ 64 96 128
  (interval_append ridgeTest_⟪0⟫ 64 80 96
  (interval_append ridgeTest_⟪0⟫ 64 72 80
  ridgeTest_⟪0⟫_block_8
  ridgeTest_⟪0⟫_block_9)
  (interval_append ridgeTest_⟪0⟫ 80 88 96
  ridgeTest_⟪0⟫_block_10
  ridgeTest_⟪0⟫_block_11))
  (interval_append ridgeTest_⟪0⟫ 96 112 128
  (interval_append ridgeTest_⟪0⟫ 96 104 112
  ridgeTest_⟪0⟫_block_12
  ridgeTest_⟪0⟫_block_13)
  (interval_append ridgeTest_⟪0⟫ 112 120 128
  ridgeTest_⟪0⟫_block_14
  ridgeTest_⟪0⟫_block_15))))"### args

elab "cert_wellFormedTest " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def wellFormedTest_⟪0⟫ (i : Nat) := wellFormedTest (i+⟪0⟫)"### args

elab "cert_wellFormedTestInterval " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem wellFormedTestInterval⟪0⟫ : Interval wellFormedTest ⟪0⟫ ⟪1⟫ := by
  intro i hlo hhi
  have h := wellFormedTest_⟪0⟫_complete (i-⟪0⟫) (Nat.zero_le _) (by omega)
  simpa only [wellFormedTest_⟪0⟫, Nat.sub_add_cancel hlo] using h"### args

elab "cert_wellFormedTest_block " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem wellFormedTest_⟪0⟫_block_⟪1⟫ : Interval wellFormedTest_⟪0⟫ ⟪2⟫ ⟪3⟫ :=
  interval_of_check wellFormedTest_⟪0⟫ ⟪2⟫ ⟪4⟫ (by decide +kernel)"### args

elab "cert_wellFormedTest_complete " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem wellFormedTest_⟪0⟫_complete : Interval wellFormedTest_⟪0⟫ 0 ⟪1⟫ :=
  (interval_append wellFormedTest_⟪0⟫ 0 128 ⟪1⟫
  (interval_append wellFormedTest_⟪0⟫ 0 64 128
  (interval_append wellFormedTest_⟪0⟫ 0 32 64
  (interval_append wellFormedTest_⟪0⟫ 0 16 32
  wellFormedTest_⟪0⟫_block_0
  wellFormedTest_⟪0⟫_block_1)
  (interval_append wellFormedTest_⟪0⟫ 32 48 64
  wellFormedTest_⟪0⟫_block_2
  wellFormedTest_⟪0⟫_block_3))
  (interval_append wellFormedTest_⟪0⟫ 64 96 128
  (interval_append wellFormedTest_⟪0⟫ 64 80 96
  wellFormedTest_⟪0⟫_block_4
  wellFormedTest_⟪0⟫_block_5)
  (interval_append wellFormedTest_⟪0⟫ 96 112 128
  wellFormedTest_⟪0⟫_block_6
  wellFormedTest_⟪0⟫_block_7)))
  (interval_append wellFormedTest_⟪0⟫ 128 192 ⟪1⟫
  (interval_append wellFormedTest_⟪0⟫ 128 160 192
  (interval_append wellFormedTest_⟪0⟫ 128 144 160
  wellFormedTest_⟪0⟫_block_8
  wellFormedTest_⟪0⟫_block_9)
  (interval_append wellFormedTest_⟪0⟫ 160 176 192
  wellFormedTest_⟪0⟫_block_10
  wellFormedTest_⟪0⟫_block_11))
  (interval_append wellFormedTest_⟪0⟫ 192 224 ⟪1⟫
  (interval_append wellFormedTest_⟪0⟫ 192 208 224
  wellFormedTest_⟪0⟫_block_12
  wellFormedTest_⟪0⟫_block_13)
  (interval_append wellFormedTest_⟪0⟫ 224 240 ⟪1⟫
  wellFormedTest_⟪0⟫_block_14
  wellFormedTest_⟪0⟫_block_15))))"### args

elab "cert_wellFormedTest_complete_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem wellFormedTest_256_complete : Interval wellFormedTest_256 0 240 :=
  (interval_append wellFormedTest_256 0 112 240
  (interval_append wellFormedTest_256 0 48 112
  (interval_append wellFormedTest_256 0 16 48
  wellFormedTest_256_block_0
  (interval_append wellFormedTest_256 16 32 48
  wellFormedTest_256_block_1
  wellFormedTest_256_block_2))
  (interval_append wellFormedTest_256 48 80 112
  (interval_append wellFormedTest_256 48 64 80
  wellFormedTest_256_block_3
  wellFormedTest_256_block_4)
  (interval_append wellFormedTest_256 80 96 112
  wellFormedTest_256_block_5
  wellFormedTest_256_block_6)))
  (interval_append wellFormedTest_256 112 176 240
  (interval_append wellFormedTest_256 112 144 176
  (interval_append wellFormedTest_256 112 128 144
  wellFormedTest_256_block_7
  wellFormedTest_256_block_8)
  (interval_append wellFormedTest_256 144 160 176
  wellFormedTest_256_block_9
  wellFormedTest_256_block_10))
  (interval_append wellFormedTest_256 176 208 240
  (interval_append wellFormedTest_256 176 192 208
  wellFormedTest_256_block_11
  wellFormedTest_256_block_12)
  (interval_append wellFormedTest_256 208 224 240
  wellFormedTest_256_block_13
  wellFormedTest_256_block_14))))"### args

