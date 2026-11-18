module

public import Papers.GraphicalZonotopes.ThreeTreeColumns
public import Papers.GraphicalZonotopes.EdgeCoordinates
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
namespace ThreeTreeStates
open Finset
open RootedResponse
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

structure ComplementPair (C E : Finset V) where
  first : ↥C
  second : ↥C
  ne : first≠second
  erase_eq : (C.erase first.1).erase second.1=E

theorem complementPair_nonempty {C E : Finset V} (hC : C.card=4) (hE : E.card=2)
    (hEC : E⊆C) : Nonempty (ComplementPair C E) := by
  have hc : (C\E).card=2 := by rw [card_sdiff_of_subset hEC,hC,hE]
  obtain ⟨a,b,hab,he⟩ := card_eq_two.mp hc
  have ha : a∈C\E := by rw [he]; simp
  have hb : b∈C\E := by rw [he]; simp
  refine ⟨⟨⟨a,(mem_sdiff.mp ha).1⟩,⟨b,(mem_sdiff.mp hb).1⟩,
    (fun h => hab (congrArg Subtype.val h)),?_⟩⟩
  ext x
  constructor
  · intro hx
    obtain ⟨hxb,hx'⟩ := mem_erase.mp hx
    obtain ⟨hxa,hxC⟩ := mem_erase.mp hx'
    by_contra hxE
    have hm : x∈C\E := mem_sdiff.mpr ⟨hxC,hxE⟩
    rw [he,mem_insert,mem_singleton] at hm
    exact hm.elim hxa hxb
  · intro hxE
    refine mem_erase.mpr ⟨?_,mem_erase.mpr ⟨?_,hEC hxE⟩⟩
    · intro hxb
      exact (mem_sdiff.mp hb).2 (by simpa only [hxb] using hxE)
    · intro hxa
      exact (mem_sdiff.mp ha).2 (by simpa only [hxa] using hxE)

def complementPair (G : SimpleGraph V) (C : ↥(tetrahedra G)) (E : Finset V)
    (hE : E.card=2) (hEC : E⊆C.1) : ComplementPair C.1 E :=
  Classical.choice (complementPair_nonempty (mem_filter.mp C.2).2.1 hE hEC)

theorem ComplementPair.pair_eq_complement {C E : Finset V} (p : ComplementPair C E) :
    ({p.first.1,p.second.1} : Finset V)=C\E := by
  conv_rhs => rw [← p.erase_eq]
  ext x
  by_cases hxa : x=p.first.1 <;> by_cases hxb : x=p.second.1 <;>
    simp [hxa,hxb,p.first.2,p.second.2]

theorem ComplementPair.unordered_eq {C E : Finset V} (p q : ComplementPair C E) :
    s(p.first.1,p.second.1)=s(q.first.1,q.second.1) := by
  apply sym2_toFinset_injective
  simp only [Sym2.toFinset_mk_eq,p.pair_eq_complement,q.pair_eq_complement]

def ComplementPair.maximum {C E : Finset V} (p : ComplementPair C E)
    (row : ↥C → ↥C → Bool) : ℤ :=
  max (RootedResponse.integerBit (row p.first p.second)) (RootedResponse.integerBit (row p.second p.first))

theorem ComplementPair.maximum_eq {C E : Finset V} (p q : ComplementPair C E)
    (row : ↥C → ↥C → Bool) : p.maximum row=q.maximum row := by
  rcases Sym2.eq_iff.mp (p.unordered_eq q) with h | h
  · obtain ⟨ha,hb⟩ := h
    have ha' : p.first=q.first := Subtype.ext ha
    have hb' : p.second=q.second := Subtype.ext hb
    simp only [ComplementPair.maximum,ha',hb']
  · obtain ⟨ha,hb⟩ := h
    have ha' : p.first=q.second := Subtype.ext ha
    have hb' : p.second=q.first := Subtype.ext hb
    simp only [ComplementPair.maximum,ha',hb',max_comm]

theorem ComplementPair.maximum_zero_or_one {C E : Finset V}
    (p : ComplementPair C E) (row : ↥C → ↥C → Bool) :
    p.maximum row=0 ∨ p.maximum row=1 := by
  unfold ComplementPair.maximum
  cases row p.first p.second <;> cases row p.second p.first <;> norm_num [RootedResponse.integerBit]

abbrev IncidentPairClique (G : SimpleGraph V) (E : Finset V) :=
  {C : ↥(tetrahedra G) // E⊆C.1}

def pairWeight (G : SimpleGraph V) (s : CompatibleRows G) (E : Finset V)
    (hE : E.card=2) : ℤ :=
  ∑ C : IncidentPairClique G E,
    (complementPair G C.1 E hE C.2).maximum (s.clique C.1).row

theorem pairWeight_nonneg (G : SimpleGraph V) (s : CompatibleRows G)
    (E : Finset V) (hE : E.card=2) : 0≤pairWeight G s E hE := by
  apply sum_nonneg
  intro C hC
  rcases (complementPair G C.1 E hE C.2).maximum_zero_or_one (s.clique C.1).row with h | h <;>
    simp [h]

theorem pairWeight_le_incident (G : SimpleGraph V) (s : CompatibleRows G)
    (E : Finset V) (hE : E.card=2) :
    pairWeight G s E hE≤(Fintype.card (IncidentPairClique G E) : ℤ) := by
  calc
    pairWeight G s E hE≤∑ _ : IncidentPairClique G E,(1:ℤ) := by
      apply sum_le_sum
      intro C hC
      rcases (complementPair G C.1 E hE C.2).maximum_zero_or_one (s.clique C.1).row with h | h <;>
        simp [h]
    _=(Fintype.card (IncidentPairClique G E) : ℤ) := by simp

end ThreeTreeStates
end GraphicalZonotopes
