module

public import Papers.GraphicalZonotopes.SmallBooleanCertificates
public import Papers.GraphicalZonotopes.BooleanPair

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
namespace SmallBoolean
open Finset FiniteTight

def partGraph {n : ℕ} (part : Fin n → Fin 4) : SimpleGraph (Fin n) where
  Adj u v := part u≠part v
  symm := ⟨fun _ _ h => Ne.symm h⟩
  loopless := ⟨fun _ h => h rfl⟩

instance {n : ℕ} (part : Fin n → Fin 4) : DecidableRel (partGraph part).Adj :=
  fun u v => inferInstanceAs (Decidable (part u≠part v))

namespace K4

def part : Fin 4 → Fin 4 := ![0,1,2,3]

def graph : SimpleGraph (Fin 4) := partGraph part

instance : DecidableRel graph.Adj :=
  fun u v => inferInstanceAs (Decidable (part u≠part v))

theorem pair_differences : ∀ u v : Fin 4,u≠v → ∀ S : Finset (Fin 4),
    u∉S → v∉S → integerDelta integerFunction u v S+
      integerDelta K4Complement.integerFunction u v S=if graph.Adj u v then 1 else 0 := by decide

theorem left_occurs : ∀ u v : Fin 4,graph.Adj u v → ∃ S : Finset (Fin 4),
    u∉S ∧ v∉S ∧ integerDelta integerFunction u v S=1 := by decide

theorem right_occurs : ∀ u v : Fin 4,graph.Adj u v → ∃ S : Finset (Fin 4),
    u∉S ∧ v∉S ∧ integerDelta K4Complement.integerFunction u v S=1 := by decide

def pairData : BooleanPairData graph where
  left := realFunction integerFunction
  right := realFunction K4Complement.integerFunction
  left_extreme := extreme
  right_extreme := K4Complement.extreme
  left_integer := realFunction_integerValued _
  right_integer := realFunction_integerValued _
  pair_sum := pair_sum_of_integer_differences graph integerFunction K4Complement.integerFunction
    empty_zero singleton_zero K4Complement.empty_zero K4Complement.singleton_zero pair_differences
  left_boolean := by
    intro u v huv S hu hv
    rw [delta_realFunction]
    rcases boolean_differences u v huv S hu hv with h | h
    · exact Or.inl (by rw [h]; norm_num)
    · exact Or.inr (by rw [h]; norm_num)
  right_boolean := by
    intro u v huv S hu hv
    rw [delta_realFunction]
    rcases K4Complement.boolean_differences u v huv S hu hv with h | h
    · exact Or.inl (by rw [h]; norm_num)
    · exact Or.inr (by rw [h]; norm_num)
  left_direction := by
    intro u v huv
    obtain ⟨S,hu,hv,hd⟩ := left_occurs u v huv
    refine ⟨S,hu,hv,?_⟩
    rw [delta_realFunction,hd]
    norm_num
  right_direction := by
    intro u v huv
    obtain ⟨S,hu,hv,hd⟩ := right_occurs u v huv
    refine ⟨S,hu,hv,?_⟩
    rw [delta_realFunction,hd]
    norm_num

end K4

namespace K1112

def part : Fin 5 → Fin 4 := ![0,1,2,3,3]

def graph : SimpleGraph (Fin 5) := partGraph part

instance : DecidableRel graph.Adj :=
  fun u v => inferInstanceAs (Decidable (part u≠part v))

theorem pair_differences : ∀ u v : Fin 5,u≠v → ∀ S : Finset (Fin 5),
    u∉S → v∉S → integerDelta integerFunction u v S+
      integerDelta K1112Complement.integerFunction u v S=if graph.Adj u v then 1 else 0 := by decide

theorem left_occurs : ∀ u v : Fin 5,graph.Adj u v → ∃ S : Finset (Fin 5),
    u∉S ∧ v∉S ∧ integerDelta integerFunction u v S=1 := by decide

theorem right_occurs : ∀ u v : Fin 5,graph.Adj u v → ∃ S : Finset (Fin 5),
    u∉S ∧ v∉S ∧ integerDelta K1112Complement.integerFunction u v S=1 := by decide

def pairData : BooleanPairData graph where
  left := realFunction integerFunction
  right := realFunction K1112Complement.integerFunction
  left_extreme := extreme
  right_extreme := K1112Complement.extreme
  left_integer := realFunction_integerValued _
  right_integer := realFunction_integerValued _
  pair_sum := pair_sum_of_integer_differences graph integerFunction K1112Complement.integerFunction
    empty_zero singleton_zero K1112Complement.empty_zero K1112Complement.singleton_zero pair_differences
  left_boolean := by
    intro u v huv S hu hv
    rw [delta_realFunction]
    rcases boolean_differences u v huv S hu hv with h | h
    · exact Or.inl (by rw [h]; norm_num)
    · exact Or.inr (by rw [h]; norm_num)
  right_boolean := by
    intro u v huv S hu hv
    rw [delta_realFunction]
    rcases K1112Complement.boolean_differences u v huv S hu hv with h | h
    · exact Or.inl (by rw [h]; norm_num)
    · exact Or.inr (by rw [h]; norm_num)
  left_direction := by
    intro u v huv
    obtain ⟨S,hu,hv,hd⟩ := left_occurs u v huv
    refine ⟨S,hu,hv,?_⟩
    rw [delta_realFunction,hd]
    norm_num
  right_direction := by
    intro u v huv
    obtain ⟨S,hu,hv,hd⟩ := right_occurs u v huv
    refine ⟨S,hu,hv,?_⟩
    rw [delta_realFunction,hd]
    norm_num

end K1112

namespace K1122

def part : Fin 6 → Fin 4 := ![0,1,2,2,3,3]

def graph : SimpleGraph (Fin 6) := partGraph part

instance : DecidableRel graph.Adj :=
  fun u v => inferInstanceAs (Decidable (part u≠part v))

theorem pair_differences : ∀ u v : Fin 6,u≠v → ∀ S : Finset (Fin 6),
    u∉S → v∉S → integerDelta integerFunction u v S+
      integerDelta K1122Complement.integerFunction u v S=if graph.Adj u v then 1 else 0 := by decide

theorem left_occurs : ∀ u v : Fin 6,graph.Adj u v → ∃ S : Finset (Fin 6),
    u∉S ∧ v∉S ∧ integerDelta integerFunction u v S=1 := by decide

theorem right_occurs : ∀ u v : Fin 6,graph.Adj u v → ∃ S : Finset (Fin 6),
    u∉S ∧ v∉S ∧ integerDelta K1122Complement.integerFunction u v S=1 := by decide

def pairData : BooleanPairData graph where
  left := realFunction integerFunction
  right := realFunction K1122Complement.integerFunction
  left_extreme := extreme
  right_extreme := K1122Complement.extreme
  left_integer := realFunction_integerValued _
  right_integer := realFunction_integerValued _
  pair_sum := pair_sum_of_integer_differences graph integerFunction K1122Complement.integerFunction
    empty_zero singleton_zero K1122Complement.empty_zero K1122Complement.singleton_zero pair_differences
  left_boolean := by
    intro u v huv S hu hv
    rw [delta_realFunction]
    rcases boolean_differences u v huv S hu hv with h | h
    · exact Or.inl (by rw [h]; norm_num)
    · exact Or.inr (by rw [h]; norm_num)
  right_boolean := by
    intro u v huv S hu hv
    rw [delta_realFunction]
    rcases K1122Complement.boolean_differences u v huv S hu hv with h | h
    · exact Or.inl (by rw [h]; norm_num)
    · exact Or.inr (by rw [h]; norm_num)
  left_direction := by
    intro u v huv
    obtain ⟨S,hu,hv,hd⟩ := left_occurs u v huv
    refine ⟨S,hu,hv,?_⟩
    rw [delta_realFunction,hd]
    norm_num
  right_direction := by
    intro u v huv
    obtain ⟨S,hu,hv,hd⟩ := right_occurs u v huv
    refine ⟨S,hu,hv,?_⟩
    rw [delta_realFunction,hd]
    norm_num

end K1122

end SmallBoolean
end GraphicalZonotopes
