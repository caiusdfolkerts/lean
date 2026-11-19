module
public meta import NumericProofSchema
public meta section
open Lean Elab Command

elab "cert_group " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def group⟪0⟫ : Group where
  vertexCode := ⟪1⟫
  inverseVertexCode := ⟪2⟫
  lowTable := (certNat% ⟪3⟫)
  highTable := (certNat% ⟪4⟫)
  edgeTable := (certNat% ⟪5⟫)
  pairPred := ⟪6⟫
  pairs := { width := 32, code := (Nat.lor (Nat.lor (certNat% ⟪7⟫) (Nat.shiftLeft (certNat% ⟪8⟫) 4096)) (Nat.shiftLeft (Nat.lor (certNat% ⟪9⟫) (Nat.shiftLeft (certNat% ⟪10⟫) 4096)) 8192)) }"### args

elab "cert_group_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def group⟪0⟫ : Group where
  vertexCode := ⟪1⟫
  inverseVertexCode := ⟪2⟫
  lowTable := (certNat% ⟪3⟫)
  highTable := (certNat% ⟪4⟫)
  edgeTable := (certNat% ⟪5⟫)
  pairPred := ⟪6⟫
  pairs := { width := 32, code := (Nat.lor (certNat% ⟪7⟫) (Nat.shiftLeft (Nat.lor (certNat% ⟪8⟫) (Nat.shiftLeft (certNat% ⟪9⟫) 4096)) 4096)) }"### args

elab "cert_group_3 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def group⟪0⟫ : Group where
  vertexCode := ⟪1⟫
  inverseVertexCode := ⟪2⟫
  lowTable := (certNat% ⟪3⟫)
  highTable := (certNat% ⟪4⟫)
  edgeTable := (certNat% ⟪5⟫)
  pairPred := ⟪6⟫
  pairs := { width := 32, code := (certNat% ⟪7⟫) }"### args

elab "cert_group_4 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def group⟪0⟫ : Group where
  vertexCode := ⟪1⟫
  inverseVertexCode := ⟪2⟫
  lowTable := (certNat% ⟪3⟫)
  highTable := (certNat% ⟪4⟫)
  edgeTable := (certNat% ⟪5⟫)
  pairPred := ⟪6⟫
  pairs := { width := 32, code := (Nat.lor (certNat% ⟪7⟫) (Nat.shiftLeft ⟪8⟫ 4096)) }"### args

elab "cert_group_5 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def group⟪0⟫ : Group where
  vertexCode := ⟪1⟫
  inverseVertexCode := ⟪2⟫
  lowTable := (certNat% ⟪3⟫)
  highTable := (certNat% ⟪4⟫)
  edgeTable := (certNat% ⟪5⟫)
  pairPred := ⟪6⟫
  pairs := { width := 32, code := (Nat.lor (Nat.lor (certNat% ⟪8⟫) (Nat.shiftLeft (certNat% ⟪9⟫) 4096)) (Nat.shiftLeft (Nat.lor (certNat% ⟪7⟫) (Nat.shiftLeft (Nat.lor (certNat% ⟪10⟫) (Nat.shiftLeft (certNat% ⟪11⟫) 4096)) 4096)) 8192)) }"### args

elab "cert_group_6 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def group⟪0⟫ : Group where
  vertexCode := ⟪1⟫
  inverseVertexCode := ⟪2⟫
  lowTable := (certNat% ⟪3⟫)
  highTable := (certNat% ⟪4⟫)
  edgeTable := (certNat% ⟪5⟫)
  pairPred := ⟪6⟫
  pairs := { width := 32, code := (Nat.lor (Nat.lor (Nat.lor (certNat% ⟪7⟫) (Nat.shiftLeft (certNat% ⟪8⟫) 4096)) (Nat.shiftLeft (Nat.lor (certNat% ⟪9⟫) (Nat.shiftLeft (Nat.lor (certNat% ⟪10⟫) (Nat.shiftLeft (certNat% ⟪11⟫) 4096)) 4096)) 8192)) (Nat.shiftLeft (Nat.lor (Nat.lor (certNat% ⟪12⟫) (Nat.shiftLeft (certNat% ⟪13⟫) 4096)) (Nat.shiftLeft (Nat.lor (certNat% ⟪14⟫) (Nat.shiftLeft (Nat.lor (certNat% ⟪15⟫) (Nat.shiftLeft (certNat% ⟪16⟫) 4096)) 4096)) 8192)) 20480)) }"### args

elab "cert_group_7 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def group⟪0⟫ : Group where
  vertexCode := ⟪1⟫
  inverseVertexCode := ⟪2⟫
  lowTable := (certNat% ⟪3⟫)
  highTable := (certNat% ⟪4⟫)
  edgeTable := (certNat% ⟪5⟫)
  pairPred := ⟪6⟫
  pairs := { width := 32, code := (Nat.lor (certNat% ⟪7⟫) (Nat.shiftLeft (certNat% ⟪8⟫) 4096)) }"### args

elab "cert_group_facts " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem group⟪0⟫_facts : group⟪0⟫.Facts FacetUniverses.FullSix0.cells :=
  group⟪0⟫.facts_of_checks _ group⟪0⟫_header (interval_append _ 0 128 ⟪1⟫ group⟪0⟫_pairs_00000 group⟪0⟫_pairs_00128)"### args

elab "cert_group_facts_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem group⟪0⟫_facts : group⟪0⟫.Facts FacetUniverses.FullSix0.cells :=
  group⟪0⟫.facts_of_checks _ group⟪0⟫_header (interval_append _ 0 128 ⟪1⟫ group⟪0⟫_pairs_00000 (interval_append _ 128 256 ⟪1⟫ group⟪0⟫_pairs_00128 group⟪0⟫_pairs_00256))"### args

elab "cert_group_facts_3 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem group⟪0⟫_facts : group⟪0⟫.Facts FacetUniverses.FullSix0.cells :=
  group⟪0⟫.facts_of_checks _ group⟪0⟫_header (interval_append _ 0 640 ⟪1⟫ (interval_append _ 0 256 640 (interval_append _ 0 128 256 group⟪0⟫_pairs_00000 group⟪0⟫_pairs_00128) (interval_append _ 256 384 640 group⟪0⟫_pairs_00256 (interval_append _ 384 512 640 group⟪0⟫_pairs_00384 group⟪0⟫_pairs_00512))) (interval_append _ 640 896 ⟪1⟫ (interval_append _ 640 768 896 group⟪0⟫_pairs_00640 group⟪0⟫_pairs_00768) (interval_append _ 896 1024 ⟪1⟫ group⟪0⟫_pairs_00896 (interval_append _ 1024 1152 ⟪1⟫ group⟪0⟫_pairs_01024 group⟪0⟫_pairs_01152))))"### args

elab "cert_group_facts_4 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem group⟪0⟫_facts : group⟪0⟫.Facts FacetUniverses.FullSix0.cells :=
  group⟪0⟫.facts_of_checks _ group⟪0⟫_header (interval_append _ 0 256 ⟪1⟫ (interval_append _ 0 128 256 group⟪0⟫_pairs_00000 group⟪0⟫_pairs_00128) (interval_append _ 256 384 ⟪1⟫ group⟪0⟫_pairs_00256 group⟪0⟫_pairs_00384))"### args

elab "cert_group_facts_5 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem group⟪0⟫_facts : group⟪0⟫.Facts FacetUniverses.FullSix0.cells :=
  group⟪0⟫.facts_of_checks _ group⟪0⟫_header (interval_append _ 0 256 ⟪1⟫ (interval_append _ 0 128 256 group⟪0⟫_pairs_00000 group⟪0⟫_pairs_00128) (interval_append _ 256 384 ⟪1⟫ group⟪0⟫_pairs_00256 (interval_append _ 384 512 ⟪1⟫ group⟪0⟫_pairs_00384 group⟪0⟫_pairs_00512)))"### args

elab "cert_group_facts_6 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem group⟪0⟫_facts : group⟪0⟫.Facts FacetUniverses.FullSix0.cells :=
  group⟪0⟫.facts_of_checks _ group⟪0⟫_header group⟪0⟫_pairs_00000"### args

elab "cert_group_header " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem group⟪0⟫_header : group⟪0⟫.headerCheck = true := by
  decide +kernel"### args

elab "cert_group_pairs " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem group⟪0⟫_pairs_⟪1⟫ :
    Interval (group⟪0⟫.pairTest FacetUniverses.FullSix0.cells) ⟪2⟫ ⟪3⟫ :=
  interval_of_check _ ⟪2⟫ ⟪4⟫ (by decide +kernel)"### args

