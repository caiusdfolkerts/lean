module
prelude
public import FastTenGraphEdges
public import FiniteChecks

@[expose] public section

/-!
# The complete 120 triangles on ten vertices

The two checked inverse identities give an exact bijection with strictly
increasing triples of vertex labels. Both the vertex mask and the 45-bit
pair mask retain their ordinary combinatorial meaning.
-/

namespace Papers.RationalityTen.TenGraphTriangles
open FiniteChecks
set_option maxRecDepth 100000
set_option maxHeartbeats 0

structure Triple where
  a : Fin 10
  b : Fin 10
  c : Fin 10
  deriving DecidableEq

noncomputable def tripleCode : Nat := 18119725189021980437990312627097022058803696836191362193964707928945730932167291477089523177040631440949768521953323286008318380691873926065334689768079833187773146704166417335723369730167042659510648771356174689135231803076870032593316536291548072291091455697379776782332806816053330405302847848013784361267610499728406898133449701776523814935146999959399678351432532385707719766028977072595221322014590736493347453835749931772609040
noncomputable def indexCode : Nat := 461543897956736267831967784996172647502455980191741226235484362017786491888369790727968222052571360828060483939823151547627029075252168775427756924533518099688933572151798880712511693190544699484285774209909016651081820202994904665996531358037377208264948146221126297564401312114903693567441288945084154144832734510212787638569685746452823153856664470542643907462102964191376521385773449630261113227223605629555171120611889257314375708765098177682553773774235336793595716972439695553762063856768112292450410145683799301150657865777024624407353644938676256166026315947974721743252094794054348849448819922841299542483874273389281983826112375514742126463753286796250416981554069123245857811910006312181428478448145217556806299852207938277657926344944003160559769156814606802799474335900089954868599286484995463663806605271218906675766604173130013471465152155272101102462819237615281729380717745531280162519362009902172978018507255272018057015147846623823492851836432868243396352270296059702226408872829094552105717595817426809214520986513199411057614693783504569395738342067935824677777886644882823845731077611352868096977123111383706872989256386743069532992089287847993288451434677492811204502768665091030143354623756199838260866855567751988363205022832829023172890910386295624080700103163926990311834991631902007594207583938705846665361634630854947430275597612722484543900213944115912334052861632245366657659909875264879939943692698961119460387539728516571948683693522522877158010393546955695077854181943571912709393648659391223191482894486931259541414254735465765047443857419219310283398857838897769910309282696095410880455877685214558451525008964547056973769605120

noncomputable def triples (i : Fin 120) : Triple :=
  let code := tripleCode >>> (12 * i.val)
  ⟨Fin.ofNat 10 (Nat.land code 15),
    Fin.ofNat 10 (Nat.land (code >>> 4) 15),
    Fin.ofNat 10 (Nat.land (code >>> 8) 15)⟩

noncomputable def indexOf (t : Triple) : Fin 120 :=
  Fin.ofNat 120 (Nat.land
    (indexCode >>> (7 * (100 * t.a.val + 10 * t.b.val + t.c.val))) 127)

noncomputable def orderedTest (i : Nat) : Bool :=
  let j := Fin.ofNat 120 i
  let t := triples j
  decide (t.a.val < t.b.val ∧ t.b.val < t.c.val) &&
    decide (indexOf t = j)

noncomputable def coverTest (i : Nat) : Bool :=
  let a := Fin.ofNat 10 (i / 100)
  let b := Fin.ofNat 10 (i / 10)
  let c := Fin.ofNat 10 i
  if a.val < b.val ∧ b.val < c.val then
    decide (triples (indexOf ⟨a,b,c⟩) = ⟨a,b,c⟩)
  else true
theorem orderedTest_block_0 : Interval orderedTest 0 16 :=
  interval_of_check orderedTest 0 16 (by decide +kernel)

theorem orderedTest_block_16 : Interval orderedTest 16 32 :=
  interval_of_check orderedTest 16 16 (by decide +kernel)

theorem orderedTest_block_32 : Interval orderedTest 32 48 :=
  interval_of_check orderedTest 32 16 (by decide +kernel)

theorem orderedTest_block_48 : Interval orderedTest 48 64 :=
  interval_of_check orderedTest 48 16 (by decide +kernel)

theorem orderedTest_block_64 : Interval orderedTest 64 80 :=
  interval_of_check orderedTest 64 16 (by decide +kernel)

theorem orderedTest_block_80 : Interval orderedTest 80 96 :=
  interval_of_check orderedTest 80 16 (by decide +kernel)

theorem orderedTest_block_96 : Interval orderedTest 96 112 :=
  interval_of_check orderedTest 96 16 (by decide +kernel)

theorem orderedTest_block_112 : Interval orderedTest 112 120 :=
  interval_of_check orderedTest 112 8 (by decide +kernel)

theorem orderedTest_complete : Interval orderedTest 0 120 :=
  (interval_append orderedTest 0 64 120 (interval_append orderedTest 0 32 64 (interval_append orderedTest 0 16 32 orderedTest_block_0 orderedTest_block_16) (interval_append orderedTest 32 48 64 orderedTest_block_32 orderedTest_block_48)) (interval_append orderedTest 64 96 120 (interval_append orderedTest 64 80 96 orderedTest_block_64 orderedTest_block_80) (interval_append orderedTest 96 112 120 orderedTest_block_96 orderedTest_block_112)))

theorem coverTest_block_0 : Interval coverTest 0 32 :=
  interval_of_check coverTest 0 32 (by decide +kernel)

theorem coverTest_block_32 : Interval coverTest 32 64 :=
  interval_of_check coverTest 32 32 (by decide +kernel)

theorem coverTest_block_64 : Interval coverTest 64 96 :=
  interval_of_check coverTest 64 32 (by decide +kernel)

theorem coverTest_block_96 : Interval coverTest 96 128 :=
  interval_of_check coverTest 96 32 (by decide +kernel)

theorem coverTest_block_128 : Interval coverTest 128 160 :=
  interval_of_check coverTest 128 32 (by decide +kernel)

theorem coverTest_block_160 : Interval coverTest 160 192 :=
  interval_of_check coverTest 160 32 (by decide +kernel)

theorem coverTest_block_192 : Interval coverTest 192 224 :=
  interval_of_check coverTest 192 32 (by decide +kernel)

theorem coverTest_block_224 : Interval coverTest 224 256 :=
  interval_of_check coverTest 224 32 (by decide +kernel)

theorem coverTest_block_256 : Interval coverTest 256 288 :=
  interval_of_check coverTest 256 32 (by decide +kernel)

theorem coverTest_block_288 : Interval coverTest 288 320 :=
  interval_of_check coverTest 288 32 (by decide +kernel)

theorem coverTest_block_320 : Interval coverTest 320 352 :=
  interval_of_check coverTest 320 32 (by decide +kernel)

theorem coverTest_block_352 : Interval coverTest 352 384 :=
  interval_of_check coverTest 352 32 (by decide +kernel)

theorem coverTest_block_384 : Interval coverTest 384 416 :=
  interval_of_check coverTest 384 32 (by decide +kernel)

theorem coverTest_block_416 : Interval coverTest 416 448 :=
  interval_of_check coverTest 416 32 (by decide +kernel)

theorem coverTest_block_448 : Interval coverTest 448 480 :=
  interval_of_check coverTest 448 32 (by decide +kernel)

theorem coverTest_block_480 : Interval coverTest 480 512 :=
  interval_of_check coverTest 480 32 (by decide +kernel)

theorem coverTest_block_512 : Interval coverTest 512 544 :=
  interval_of_check coverTest 512 32 (by decide +kernel)

theorem coverTest_block_544 : Interval coverTest 544 576 :=
  interval_of_check coverTest 544 32 (by decide +kernel)

theorem coverTest_block_576 : Interval coverTest 576 608 :=
  interval_of_check coverTest 576 32 (by decide +kernel)

theorem coverTest_block_608 : Interval coverTest 608 640 :=
  interval_of_check coverTest 608 32 (by decide +kernel)

theorem coverTest_block_640 : Interval coverTest 640 672 :=
  interval_of_check coverTest 640 32 (by decide +kernel)

theorem coverTest_block_672 : Interval coverTest 672 704 :=
  interval_of_check coverTest 672 32 (by decide +kernel)

theorem coverTest_block_704 : Interval coverTest 704 736 :=
  interval_of_check coverTest 704 32 (by decide +kernel)

theorem coverTest_block_736 : Interval coverTest 736 768 :=
  interval_of_check coverTest 736 32 (by decide +kernel)

theorem coverTest_block_768 : Interval coverTest 768 800 :=
  interval_of_check coverTest 768 32 (by decide +kernel)

theorem coverTest_block_800 : Interval coverTest 800 832 :=
  interval_of_check coverTest 800 32 (by decide +kernel)

theorem coverTest_block_832 : Interval coverTest 832 864 :=
  interval_of_check coverTest 832 32 (by decide +kernel)

theorem coverTest_block_864 : Interval coverTest 864 896 :=
  interval_of_check coverTest 864 32 (by decide +kernel)

theorem coverTest_block_896 : Interval coverTest 896 928 :=
  interval_of_check coverTest 896 32 (by decide +kernel)

theorem coverTest_block_928 : Interval coverTest 928 960 :=
  interval_of_check coverTest 928 32 (by decide +kernel)

theorem coverTest_block_960 : Interval coverTest 960 992 :=
  interval_of_check coverTest 960 32 (by decide +kernel)

theorem coverTest_block_992 : Interval coverTest 992 1000 :=
  interval_of_check coverTest 992 8 (by decide +kernel)

theorem coverTest_complete : Interval coverTest 0 1000 :=
  (interval_append coverTest 0 512 1000 (interval_append coverTest 0 256 512 (interval_append coverTest 0 128 256 (interval_append coverTest 0 64 128 (interval_append coverTest 0 32 64 coverTest_block_0 coverTest_block_32) (interval_append coverTest 64 96 128 coverTest_block_64 coverTest_block_96)) (interval_append coverTest 128 192 256 (interval_append coverTest 128 160 192 coverTest_block_128 coverTest_block_160) (interval_append coverTest 192 224 256 coverTest_block_192 coverTest_block_224))) (interval_append coverTest 256 384 512 (interval_append coverTest 256 320 384 (interval_append coverTest 256 288 320 coverTest_block_256 coverTest_block_288) (interval_append coverTest 320 352 384 coverTest_block_320 coverTest_block_352)) (interval_append coverTest 384 448 512 (interval_append coverTest 384 416 448 coverTest_block_384 coverTest_block_416) (interval_append coverTest 448 480 512 coverTest_block_448 coverTest_block_480)))) (interval_append coverTest 512 768 1000 (interval_append coverTest 512 640 768 (interval_append coverTest 512 576 640 (interval_append coverTest 512 544 576 coverTest_block_512 coverTest_block_544) (interval_append coverTest 576 608 640 coverTest_block_576 coverTest_block_608)) (interval_append coverTest 640 704 768 (interval_append coverTest 640 672 704 coverTest_block_640 coverTest_block_672) (interval_append coverTest 704 736 768 coverTest_block_704 coverTest_block_736))) (interval_append coverTest 768 896 1000 (interval_append coverTest 768 832 896 (interval_append coverTest 768 800 832 coverTest_block_768 coverTest_block_800) (interval_append coverTest 832 864 896 coverTest_block_832 coverTest_block_864)) (interval_append coverTest 896 960 1000 (interval_append coverTest 896 928 960 coverTest_block_896 coverTest_block_928) (interval_append coverTest 960 992 1000 coverTest_block_960 coverTest_block_992)))))


theorem ordered_and_index (i : Fin 120) :
    (triples i).a.val < (triples i).b.val ∧
      (triples i).b.val < (triples i).c.val ∧ indexOf (triples i) = i := by
  have h := orderedTest_complete i.val (Nat.zero_le _) i.isLt
  have hh : ((triples i).a.val < (triples i).b.val ∧
      (triples i).b.val < (triples i).c.val) ∧ indexOf (triples i) = i := by
    simpa only [orderedTest, Fin.ofNat_val_eq_self, Bool.and_eq_true_iff,
      decide_eq_true_eq] using h
  exact ⟨hh.1.1, hh.1.2, hh.2⟩

theorem ordered (i : Fin 120) :
    (triples i).a.val < (triples i).b.val ∧
      (triples i).b.val < (triples i).c.val :=
  ⟨(ordered_and_index i).1, (ordered_and_index i).2.1⟩

theorem index_triples (i : Fin 120) : indexOf (triples i) = i :=
  (ordered_and_index i).2.2

theorem triples_index (t : Triple)
    (hab : t.a.val < t.b.val) (hbc : t.b.val < t.c.val) :
    triples (indexOf t) = t := by
  let code := 100 * t.a.val + 10 * t.b.val + t.c.val
  have hcode : code < 1000 := by
    have := t.a.isLt
    have := t.b.isLt
    have := t.c.isLt
    omega
  have ha : Fin.ofNat 10 (code / 100) = t.a := by
    apply Fin.ext
    change code / 100 % 10 = t.a.val
    have := t.a.isLt
    have := t.b.isLt
    have := t.c.isLt
    omega
  have hb : Fin.ofNat 10 (code / 10) = t.b := by
    apply Fin.ext
    change code / 10 % 10 = t.b.val
    have := t.a.isLt
    have := t.b.isLt
    have := t.c.isLt
    omega
  have hc : Fin.ofNat 10 code = t.c := by
    apply Fin.ext
    change code % 10 = t.c.val
    have := t.c.isLt
    omega
  have h := coverTest_complete code (Nat.zero_le _) hcode
  simpa only [coverTest, ha, hb, hc, hab, hbc, and_self, ite_true,
    decide_eq_true_eq] using h

theorem triples_injective (i j : Fin 120) (h : triples i = triples j) : i = j := by
  have hh := congrArg indexOf h
  simpa only [index_triples] using hh

noncomputable def vertices (i : Fin 120) : Nat :=
  let t := triples i
  Nat.lor (Nat.lor (1 <<< t.a.val) (1 <<< t.b.val)) (1 <<< t.c.val)

noncomputable def pairs (i : Fin 120) : Nat :=
  let t := triples i
  Nat.lor (Nat.lor (1 <<< (FastTenGraphEdges.encode t.a t.b).val)
    (1 <<< (FastTenGraphEdges.encode t.a t.c).val))
    (1 <<< (FastTenGraphEdges.encode t.b t.c).val)

theorem vertices_eq (i : Fin 120) :
    vertices i = Nat.lor (Nat.lor (1 <<< (triples i).a.val)
      (1 <<< (triples i).b.val)) (1 <<< (triples i).c.val) := rfl

theorem pairs_eq (i : Fin 120) :
    pairs i = Nat.lor (Nat.lor
      (1 <<< (TenGraphEdges.encode (triples i).a (triples i).b).val)
      (1 <<< (TenGraphEdges.encode (triples i).a (triples i).c).val))
      (1 <<< (TenGraphEdges.encode (triples i).b (triples i).c).val) := by
  simp only [pairs, FastTenGraphEdges.encode_eq]

noncomputable def count (complement : Nat) : Nat :=
  ((List.finRange 120).filter fun i =>
    decide (Nat.land complement (pairs i) = 0)).length

#print axioms triples_index
#print axioms triples_injective
#print axioms pairs_eq

end Papers.RationalityTen.TenGraphTriangles
