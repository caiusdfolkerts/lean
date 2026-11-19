module
prelude
public meta import IntegerTables
public import PolygonGrowthData
public import PolygonN7Nodes000
public import PolygonN7Nodes001
public import PolygonN7Nodes002
public import PolygonN7Nodes003
public import PolygonN7Nodes004
public import PolygonN7Nodes005
public import PolygonN7Nodes006
public import PolygonN7Nodes007
public import PolygonN7Nodes008
public import PolygonN7Nodes009
public import PolygonN7Nodes010
public import PolygonN7Nodes011
public import PolygonN7Nodes012
public import PolygonN7Nodes013
public import PolygonN7Nodes014
public import PolygonN7Nodes015
public import PolygonN7Nodes016
public import PolygonN7Nodes017
public import PolygonN7Nodes018
public import PolygonN7Nodes019
public import PolygonN7Nodes020
public import PolygonN7Nodes021
public import PolygonN7Nodes022
public import PolygonN7Nodes023
public import PolygonN7Nodes024
public import PolygonN7Nodes025
public import PolygonN7Nodes026
public import PolygonN7Nodes027
public import PolygonN7Nodes028
public import PolygonN7Nodes029
public import PolygonN7Nodes030
public import PolygonN7Nodes031
public import PolygonN7Nodes032
public import PolygonN7Nodes033
public import PolygonN7Nodes034
public import PolygonN7Nodes035
public import PolygonN7Nodes036
public import PolygonN7Nodes037
public import PolygonN7Nodes038
public import PolygonN7Nodes039
public import PolygonN7Nodes040
public import PolygonN7Nodes041
public import PolygonN7Nodes042
public import PolygonN7Nodes043
public import PolygonN7Nodes044

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Papers.RationalityTen.PolygonGrowth.N7
open Papers.RationalityTen ConcreteGrowth

noncomputable def ridgeTable : ConcreteGrowth.Table Nat :=
  integerTable% 0 579

noncomputable def ridgeList (a : Fin 290) : List (Fin 49) :=
  (unpackList (ridgeTable.get a.val)).1.map (Fin.ofNat 49)

noncomputable def compatibilityBits : ConcreteGrowth.Table Nat :=
  integerTable% 579 579

noncomputable def compatible (a b : Fin 290) : Bool :=
  decide ((compatibilityBits.get a.val / 2^b.val) % 2 = 1)

noncomputable def kind (_ : Fin 290) : Nat := 0
noncomputable def quota (j : Nat) : Nat := if j = 0 then 10 else 0

noncomputable def candidateTable : ConcreteGrowth.Table Nat :=
  integerTable% 1158 69

noncomputable def candidates (q : Fin 49) : List (Fin 290) :=
  (unpackList (candidateTable.get q.val)).1.map (Fin.ofNat 290)

noncomputable def terminalTable : ConcreteGrowth.Table Nat :=
  integerTable% 1227 7591

noncomputable def terminals (j : Fin 3796) : List (Fin 290) :=
  (unpackList (terminalTable.get j.val)).1.map (Fin.ofNat 290)

noncomputable def rawNodeTable : ConcreteGrowth.Table Nat :=
(.branch 5632 (.branch 2816 (.branch 1280 (.branch 512 (.branch 256 rawNodePart000 rawNodePart001) (.branch 768 rawNodePart002 (.branch 1024 rawNodePart003 rawNodePart004))) (.branch 2048 (.branch 1536 rawNodePart005 (.branch 1792 rawNodePart006 rawNodePart007)) (.branch 2304 rawNodePart008 (.branch 2560 rawNodePart009 rawNodePart010)))) (.branch 4096 (.branch 3328 (.branch 3072 rawNodePart011 rawNodePart012) (.branch 3584 rawNodePart013 (.branch 3840 rawNodePart014 rawNodePart015))) (.branch 4864 (.branch 4352 rawNodePart016 (.branch 4608 rawNodePart017 rawNodePart018)) (.branch 5120 rawNodePart019 (.branch 5376 rawNodePart020 rawNodePart021))))) (.branch 8448 (.branch 6912 (.branch 6144 (.branch 5888 rawNodePart022 rawNodePart023) (.branch 6400 rawNodePart024 (.branch 6656 rawNodePart025 rawNodePart026))) (.branch 7680 (.branch 7168 rawNodePart027 (.branch 7424 rawNodePart028 rawNodePart029)) (.branch 7936 rawNodePart030 (.branch 8192 rawNodePart031 rawNodePart032)))) (.branch 9984 (.branch 9216 (.branch 8704 rawNodePart033 (.branch 8960 rawNodePart034 rawNodePart035)) (.branch 9472 rawNodePart036 (.branch 9728 rawNodePart037 rawNodePart038))) (.branch 10752 (.branch 10240 rawNodePart039 (.branch 10496 rawNodePart040 rawNodePart041)) (.branch 11008 rawNodePart042 (.branch 11264 rawNodePart043 rawNodePart044))))))

noncomputable def nodes (i : Fin 11426) : WitnessGrowthDAG.Node 290 49 3796 11426 :=
  PolygonGrowth.decodeNode (unpackNode (rawNodeTable.get i.val))

noncomputable def rootTable : ConcreteGrowth.Table Nat :=
(.branch 2
 (.branch 1
 (.leaf 10307)
 (.leaf 11347))
 (.branch 3
 (.leaf 11419)
 (.leaf 11425)))

noncomputable def roots (i : Fin 4) : Fin 11426 := Fin.ofNat 11426 (rootTable.get i.val)
noncomputable def neighborTable : ConcreteGrowth.Table Nat :=
(.branch 2
 (.branch 1
 (.leaf 1)
 (.leaf 35))
 (.branch 3
 (.leaf 110)
 (.leaf 218)))

noncomputable def neighbors (i : Fin 4) : Fin 290 := Fin.ofNat 290 (neighborTable.get i.val)
noncomputable def targetTable : ConcreteGrowth.Table Nat :=
  integerTable% 8818 7115

noncomputable def permutationTable : ConcreteGrowth.Table Nat :=
  integerTable% 15933 6963

noncomputable def targetTemplate (i : Fin 3796) : Nat := targetTable.get i.val
noncomputable def permutationCode (i : Fin 3796) : Nat := permutationTable.get i.val

end Papers.RationalityTen.PolygonGrowth.N7
