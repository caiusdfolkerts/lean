module
prelude
public import RootedSmallGeneratorWordsFastCheck0
public import RootedSmallGeneratorWordsFastCheck1
public import RootedSmallGeneratorWordsFastCheck2
public import RootedSmallGeneratorWordsFastCheck3
public import RootedSmallGeneratorWordsFastCheck4
public import RootedSmallGeneratorWordsFastCheck5
public import RootedSmallGeneratorWordsFastCheck6

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedSmallGeneratorWords
open Papers.RationalityTen ConcreteGrowth FiniteChecks

theorem bit_checked (g : Fin 7) : Interval (fun i => bitTest g.val i) 0 3436 := by
  have h : ∀ a : Fin 7, Interval (fun i => bitTest a.val i) 0 3436 :=
    (Fin.cases generatorBitTest0_complete (Fin.cases generatorBitTest1_complete (Fin.cases generatorBitTest2_complete (Fin.cases generatorBitTest3_complete (Fin.cases generatorBitTest4_complete (Fin.cases generatorBitTest5_complete (Fin.cases generatorBitTest6_complete (fun i => Fin.elim0 i))))))))
  exact h g

theorem cell_checked (g : Fin 7) (i : Fin 3436) : cellTest g.val i.val = true := by
  rw [← bitTest_eq]
  exact bit_checked g i.val (Nat.zero_le _) i.isLt

#print axioms cell_checked

end Papers.RationalityTen.RootedSmallGeneratorWords
