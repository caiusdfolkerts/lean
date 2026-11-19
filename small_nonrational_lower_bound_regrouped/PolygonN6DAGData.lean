module
prelude
public meta import IntegerTables
public import PolygonGrowthData

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Papers.RationalityTen.PolygonGrowth.N6
open Papers.RationalityTen ConcreteGrowth

noncomputable def ridgeTable : ConcreteGrowth.Table Nat :=
  integerTable% 0 129

noncomputable def ridgeList (a : Fin 65) : List (Fin 36) :=
  (unpackList (ridgeTable.get a.val)).1.map (Fin.ofNat 36)

noncomputable def compatibilityBits : ConcreteGrowth.Table Nat :=
  integerTable% 129 129

noncomputable def compatible (a b : Fin 65) : Bool :=
  decide ((compatibilityBits.get a.val / 2^b.val) % 2 = 1)

noncomputable def kind (_ : Fin 65) : Nat := 0
noncomputable def quota (j : Nat) : Nat := if j = 0 then 8 else 0

noncomputable def candidateTable : ConcreteGrowth.Table Nat :=
  integerTable% 258 49

noncomputable def candidates (q : Fin 36) : List (Fin 65) :=
  (unpackList (candidateTable.get q.val)).1.map (Fin.ofNat 65)

noncomputable def terminalTable : ConcreteGrowth.Table Nat :=
  integerTable% 307 219

noncomputable def terminals (j : Fin 110) : List (Fin 65) :=
  (unpackList (terminalTable.get j.val)).1.map (Fin.ofNat 65)

noncomputable def rawNodeTable : ConcreteGrowth.Table Nat :=
  integerTable% 526 577

noncomputable def nodes (i : Fin 289) : WitnessGrowthDAG.Node 65 36 110 289 :=
  PolygonGrowth.decodeNode (unpackNode (rawNodeTable.get i.val))

noncomputable def rootTable : ConcreteGrowth.Table Nat :=
(.branch 1
 (.leaf 246)
 (.branch 2
 (.leaf 283)
 (.leaf 288)))

noncomputable def roots (i : Fin 3) : Fin 289 := Fin.ofNat 289 (rootTable.get i.val)
noncomputable def neighborTable : ConcreteGrowth.Table Nat :=
(.branch 1
 (.leaf 1)
 (.branch 2
 (.leaf 20)
 (.leaf 47)))

noncomputable def neighbors (i : Fin 3) : Fin 65 := Fin.ofNat 65 (neighborTable.get i.val)
noncomputable def targetTable : ConcreteGrowth.Table Nat :=
  integerTable% 1103 195

noncomputable def permutationTable : ConcreteGrowth.Table Nat :=
  integerTable% 1298 211

noncomputable def targetTemplate (i : Fin 110) : Nat := targetTable.get i.val
noncomputable def permutationCode (i : Fin 110) : Nat := permutationTable.get i.val

end Papers.RationalityTen.PolygonGrowth.N6
