module

public import PaperVerification.WeightedBarTor
public import Mathlib.LinearAlgebra.Dual.Basis

/-!
# The actual word bases on the diagonal and immediately below it

Positive original degrees force a tensor of length n and degree n to
have only degree-one factors. A tensor of length n-1 and degree n has
exactly one degree-two factor. The equivalences below are proved from
those degree equations, including degree zero, and apply to the actual
coefficient complex of ordinary augmentation Tor.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace PaperVerification.DiagonalBarWords

open WeightedBar

universe u
variable {I : Type u} (δ : I → ℕ) (hpos : ∀ i,0<δ i)

abbrev DegreeOne := {i : I // δ i=1}
abbrev DegreeTwo := {i : I // δ i=2}

def embedWord (L : List (DegreeOne δ)) : List I := L.map Subtype.val

@[simp] theorem embedWord_nil : embedWord δ []=[] := rfl
@[simp] theorem embedWord_cons (i : DegreeOne δ) (L : List (DegreeOne δ)) :
    embedWord δ (i::L)=i.val::embedWord δ L := rfl
@[simp] theorem embedWord_length (L : List (DegreeOne δ)) :
    (embedWord δ L).length=L.length := List.length_map _

theorem embedWord_injective : Function.Injective (embedWord δ) := by
  intro L T h
  exact (List.map_inj_right Subtype.val_injective).mp h

@[simp] theorem totalDegree_embedWord (L : List (DegreeOne δ)) :
    totalDegree δ (embedWord δ L)=L.length := by
  induction L with
  | nil => rfl
  | cons i L ih =>
      rw [embedWord_cons,totalDegree_cons,i.property,ih,List.length_cons,Nat.add_comm]

include hpos in
theorem degree_one_of_diagonal (L : List I) (hL : totalDegree δ L=L.length) :
    ∀ i∈L,δ i=1 := by
  induction L with
  | nil => simp only [List.not_mem_nil,false_implies,implies_true]
  | cons a L ih =>
      have ha := hpos a
      have hbound := length_le_totalDegree δ hpos L
      have hd : δ a+totalDegree δ L=L.length+1 := hL
      have ha1 : δ a=1 := by omega
      have ht : totalDegree δ L=L.length := by omega
      intro i hi
      rcases List.mem_cons.mp hi with rfl|hi
      · exact ha1
      · exact ih ht i hi

theorem exists_pure_lift (L : List I) (hL : ∀ i∈L,δ i=1) :
    ∃ T : List (DegreeOne δ),embedWord δ T=L := by
  induction L with
  | nil => exact ⟨[],rfl⟩
  | cons a L ih =>
      obtain ⟨T,hT⟩ := ih (fun i hi ↦ hL i (List.mem_cons_of_mem a hi))
      exact ⟨⟨a,hL a (List.mem_cons_self)⟩::T,by rw [embedWord_cons,hT]⟩

def PureWord (n : ℕ) := {L : List (DegreeOne δ) // L.length=n}

def pureToIndex (n : ℕ) (L : PureWord δ n) : Index δ n n :=
  ⟨embedWord δ L.val,by rw [embedWord_length,totalDegree_embedWord];exact ⟨L.property,L.property⟩⟩

theorem pureToIndex_injective (n : ℕ) : Function.Injective (pureToIndex δ n) := by
  intro L T h
  apply Subtype.ext
  exact embedWord_injective δ (congrArg Subtype.val h)

include hpos in
theorem pureToIndex_surjective (n : ℕ) : Function.Surjective (pureToIndex δ n) := by
  intro L
  obtain ⟨T,hT⟩ := exists_pure_lift δ L.val
    (degree_one_of_diagonal δ hpos L.val (L.property.2.trans L.property.1.symm))
  have ht : T.length=n := by rw [←embedWord_length δ T,hT];exact L.property.1
  exact ⟨⟨T,ht⟩,Subtype.ext hT⟩

def pureIndexEquiv (n : ℕ) : PureWord δ n ≃ Index δ n n :=
  Equiv.ofBijective (pureToIndex δ n)
    ⟨pureToIndex_injective δ n,pureToIndex_surjective δ hpos n⟩

instance pureWordFinite [Finite I] (n : ℕ) : Finite (PureWord δ n) :=
  Finite.of_injective (pureToIndex δ n) (pureToIndex_injective δ n)

instance pureWordFintype [Fintype I] (n : ℕ) : Fintype (PureWord δ n) :=
  Fintype.ofFinite _

variable {K : Type u} [Field K]

def diagonalBasis (n : ℕ) : Module.Basis (PureWord δ n) K (piece (K := K) δ n n) :=
  (basis δ n n).reindex (pureIndexEquiv δ hpos n).symm

@[simp] theorem diagonalBasis_val (n : ℕ) (L : PureWord δ n) :
    (diagonalBasis (K := K) δ hpos n L).val=Finsupp.single (embedWord δ L.val) 1 := by
  rw [diagonalBasis,Module.Basis.reindex_apply]
  change ((Finsupp.supportedEquivFinsupp (M := K) (R := K)
    {T : List I | T.length=n ∧ totalDegree δ T=n}).symm
      (Finsupp.single (pureToIndex δ n L) 1)).val=Finsupp.single (embedWord δ L.val) 1
  exact Finsupp.supportedEquivFinsupp_symm_single _ _ _

@[simp] theorem diagonalBasis_repr (n : ℕ) (z : piece (K := K) δ n n)
    (L : PureWord δ n) :
    (diagonalBasis δ hpos n).repr z L=z.val (embedWord δ L.val) := by
  rw [diagonalBasis,Module.Basis.repr_reindex_apply]
  rfl

include hpos in
/-- Every word one step below the diagonal has precisely one factor of
actual degree two and otherwise actual degree-one factors. -/
theorem defect_one_decomposition (L : List I)
    (hL : totalDegree δ L=L.length+1) :
    ∃ P : List (DegreeOne δ),∃ a : DegreeTwo δ,∃ Q : List (DegreeOne δ),
      L=embedWord δ P++a.val::embedWord δ Q := by
  induction L with
  | nil => simp only [totalDegree_nil,List.length_nil] at hL;omega
  | cons a L ih =>
      have ha := hpos a
      have hbound := length_le_totalDegree δ hpos L
      have hd : δ a+totalDegree δ L=(L.length+1)+1 := hL
      by_cases ha2 : δ a=2
      · have ht : totalDegree δ L=L.length := by omega
        obtain ⟨Q,hQ⟩ := exists_pure_lift δ L (degree_one_of_diagonal δ hpos L ht)
        exact ⟨[],⟨a,ha2⟩,Q,by simp only [embedWord_nil,List.nil_append,hQ]⟩
      · have ha1 : δ a=1 := by omega
        have ht : totalDegree δ L=L.length+1 := by omega
        obtain ⟨P,b,Q,h⟩ := ih ht
        refine ⟨⟨a,ha1⟩::P,b,Q,?_⟩
        rw [embedWord_cons,List.cons_append,←h]

end PaperVerification.DiagonalBarWords
