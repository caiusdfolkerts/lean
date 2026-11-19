module
prelude
public import PolygonGrowthData

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Papers.RationalityTen.PolygonGrowth.N5
open Papers.RationalityTen ConcreteGrowth

noncomputable def ridgeTable : ConcreteGrowth.Table Nat :=
(.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf 1970333426974723)
 (.leaf 2251812698652675))
 (.branch 3
 (.leaf 2533291970330627)
 (.leaf 3659187582271491)))
 (.branch 6
 (.branch 5
 (.leaf 3940666853949443)
 (.leaf 5348041737568259))
 (.branch 7
 (.leaf 3659209057435651)
 (.leaf 3940688329113603))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf 5348063212732419)
 (.leaf 5348084687896579))
 (.branch 11
 (.leaf 350490389217475100676)
 (.leaf 350490670688156844036)))
 (.branch 14
 (.branch 13
 (.leaf 350491796592358719492)
 (.leaf 350492078063040462852))
 (.branch 15
 (.leaf 350491796613833883652)
 (.leaf 350492078084515627012)))))

noncomputable def ridgeList (a : Fin 16) : List (Fin 25) :=
  (unpackList (ridgeTable.get a.val)).1.map (Fin.ofNat 25)

noncomputable def compatibilityBits : ConcreteGrowth.Table Nat :=
(.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf 65534)
 (.leaf 41981))
 (.branch 3
 (.leaf 21499)
 (.leaf 19447)))
 (.branch 6
 (.branch 5
 (.leaf 34799)
 (.leaf 50143))
 (.branch 7
 (.leaf 6079)
 (.leaf 11135))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf 13055)
 (.leaf 3583))
 (.branch 11
 (.leaf 593)
 (.leaf 649)))
 (.branch 14
 (.branch 13
 (.leaf 325)
 (.leaf 387))
 (.branch 15
 (.leaf 45)
 (.leaf 51)))))

noncomputable def compatible (a b : Fin 16) : Bool :=
  decide ((compatibilityBits.get a.val / 2^b.val) % 2 = 1)

noncomputable def kind (_ : Fin 16) : Nat := 0
noncomputable def quota (j : Nat) : Nat := if j = 0 then 6 else 0

noncomputable def candidateTable : ConcreteGrowth.Table Nat :=
(.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf 0)
 (.branch 2
 (.leaf 13298368483764612265672709)
 (.leaf 15716257017044976577544197)))
 (.branch 4
 (.leaf 15716238570582377844768773)
 (.branch 5
 (.leaf 14507294304223679255543813)
 (.leaf 0))))
 (.branch 9
 (.branch 7
 (.leaf 0)
 (.branch 8
 (.leaf 18134145550606820161093637)
 (.leaf 18134071763912000299663365)))
 (.branch 10
 (.leaf 16925164391041449129541637)
 (.leaf 0))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf 0)
 (.branch 14
 (.leaf 16925182838066993520902149)
 (.leaf 18134127104425700700192773)))
 (.leaf 0))
 (.branch 21
 (.branch 19
 (.leaf 0)
 (.branch 20
 (.leaf 334515941998597050173725560162912009319677961)
 (.leaf 0)))
 (.leaf 0))))

noncomputable def candidates (q : Fin 25) : List (Fin 16) :=
  (unpackList (candidateTable.get q.val)).1.map (Fin.ofNat 16)

noncomputable def terminalTable : ConcreteGrowth.Table Nat :=
(.branch 3
 (.branch 1
 (.leaf 110681308871482408964)
 (.branch 2
 (.leaf 713063134164064008320485163014)
 (.leaf 713060716275531572389693358086)))
 (.branch 5
 (.branch 4
 (.leaf 633833762687086849425324113926)
 (.leaf 18133979529065710370160645))
 (.branch 6
 (.leaf 15716183230913098079535109)
 (.leaf 12089424218531822173159429))))

noncomputable def terminals (j : Fin 7) : List (Fin 16) :=
  (unpackList (terminalTable.get j.val)).1.map (Fin.ofNat 16)

noncomputable def rawNodeTable : ConcreteGrowth.Table Nat :=
(.branch 10
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf 110681308871482408964)
 (.leaf 340282367634001597627438615752253374470))
 (.branch 3
 (.leaf 39403208778632921898654475460424929900469135626535085434301595365710459620803586849048756799398295980933277470949381)
 (.branch 4
 (.leaf 1803699053658994671435131477699303003304690489094669733878988691364326575486059792419127488306042692507271168004)
 (.leaf 27522263392013468497240195724484820446926099075667538314684248432291711128069616539765256153257746930597891))))
 (.branch 7
 (.branch 6
 (.leaf 680564734554937643202280787253229780998)
 (.leaf 39403208778632921898654475462414222846108269827146281138209674214459465252185161402539668880858283631085569085276165))
 (.branch 8
 (.leaf 1020847101396649153077210671720628748294)
 (.branch 9
 (.leaf 275815245966173791636288936925562593026944086185946973592020680694737674291029995588839323977630310838778278749143045)
 (.leaf 20769187452273290043187695687041029)))))
 (.branch 15
 (.branch 12
 (.branch 11
 (.leaf 5411078808788530430045468550273364035355607529342116201918021359890307769141238808436078045335371505224927674372)
 (.leaf 36696257851701780471841636376062588652117999263067730063805312843405959735260288706297627474560783761801219))
 (.branch 13
 (.leaf 25961484308390321373565579725635589)
 (.branch 14
 (.leaf 4208606658419399896793959608887469622939957122768849388983056819995579414176037742771475036295179875050789535748)
 (.leaf 119262208031616328961673031537726218971161865944511750204723544728423497750808140364019932718802283270242307))))
 (.branch 17
 (.branch 16
 (.leaf 1959785193777426348294079581559712061851194830110918868735105692145333060301621198252484382257148067842)
 (.leaf 31153781163298389989714800148480005))
 (.branch 18
 (.leaf 2404925954709118339349834504800492849461101490563262537845619688159050966116282371636846768353046577877203550212)
 (.branch 19
 (.leaf 91740224639735568600070044849085936765590053227121846593411124927820466299720096549693880070030909232906243)
 (.leaf 1399844736258907929743681909466335981110236299750274608692602475468860545388655479734669643657089384450))))))

noncomputable def nodes (i : Fin 20) : WitnessGrowthDAG.Node 16 25 7 20 :=
  PolygonGrowth.decodeNode (unpackNode (rawNodeTable.get i.val))

noncomputable def rootTable : ConcreteGrowth.Table Nat :=
(.branch 1
 (.leaf 15)
 (.leaf 19))

noncomputable def roots (i : Fin 2) : Fin 20 := Fin.ofNat 20 (rootTable.get i.val)
noncomputable def neighborTable : ConcreteGrowth.Table Nat :=
(.branch 1
 (.leaf 1)
 (.leaf 10))

noncomputable def neighbors (i : Fin 2) : Fin 16 := Fin.ofNat 16 (neighborTable.get i.val)
noncomputable def targetTable : ConcreteGrowth.Table Nat :=
(.branch 3
 (.branch 1
 (.leaf 2)
 (.leaf 0))
 (.branch 5
 (.branch 4
 (.leaf 0)
 (.leaf 1))
 (.leaf 1)))

noncomputable def permutationTable : ConcreteGrowth.Table Nat :=
(.branch 3
 (.branch 1
 (.leaf 2930)
 (.branch 2
 (.leaf 2902)
 (.leaf 2910)))
 (.branch 5
 (.branch 4
 (.leaf 2430)
 (.leaf 2402))
 (.branch 6
 (.leaf 2410)
 (.leaf 2930))))

noncomputable def targetTemplate (i : Fin 7) : Nat := targetTable.get i.val
noncomputable def permutationCode (i : Fin 7) : Nat := permutationTable.get i.val

end Papers.RationalityTen.PolygonGrowth.N5
