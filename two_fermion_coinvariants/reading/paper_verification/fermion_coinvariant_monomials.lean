module

public import PaperVerification.FermionCoinvariantReynolds
public import PaperVerification.FermionCoinvariantLocalBlocks
public import PaperVerification.FermionSuperMonomialBasics
public import PaperVerification.FermionCreatorTriangularity
public import TauCeti.LinearAlgebra.ExteriorAlgebra.Contraction
public import Mathlib.Data.Finsupp.Order
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.Ring.Int.Units

/-!
# Original supermonomials, occupied indices and local factorization

All support and cyclic-weight data belong to the
actual polynomial/exterior basis. Products use the genuine exterior shuffle
sign, including the zero case. The local factorization uses an actual unit
and erases exactly one occupied coordinate, so its induction measure strictly
decreases without discarding exterior signs or polynomial exponents.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators TensorProduct

namespace PaperVerification.Fermion.Coinvariants

variable {R : Type*} [CommRing R] {n : ℕ}

/-- The original index of either labelled odd generator. -/
def oddSite : OddIndex n → Fin n := Sum.elim id id

def oddLocalWeight (p q : ℕ) (i : Fin n) : OddIndex n → ℕ
  | .inl j => if j=i then p else 0
  | .inr j => if j=i then q else 0

/-- The character exponent at one original index. -/
def localDegree (p q : ℕ) (z : SuperMonomialIndex n) (i : Fin n) : ℕ :=
  z.1 i+∑ j∈z.2,oddLocalWeight p q i j

/-- A position is occupied by an even positive power or by either odd label. -/
def occupied (z : SuperMonomialIndex n) : Finset (Fin n) :=
  z.1.support ∪ z.2.image oddSite

@[simp] theorem mem_occupied (z : SuperMonomialIndex n) (i : Fin n) :
    i∈occupied z ↔ z.1 i≠0 ∨ Sum.inl i∈z.2 ∨ Sum.inr i∈z.2 := by
  simp only [occupied,Finset.mem_union,Finsupp.mem_support_iff,Finset.mem_image]
  constructor
  · rintro (h|⟨j,hj,he⟩)
    · exact Or.inl h
    · cases j with
      | inl j =>
          have hji : j=i := he
          subst j
          exact Or.inr (Or.inl hj)
      | inr j =>
          have hji : j=i := he
          subst j
          exact Or.inr (Or.inr hj)
  · rintro (h|h|h)
    · exact Or.inl h
    · exact Or.inr ⟨.inl i,h,rfl⟩
    · exact Or.inr ⟨.inr i,h,rfl⟩

/-- The actual four possible local exterior subsets. -/
def blockOddSet (a : MomentKind) (i : Fin n) : Finset (OddIndex n) :=
  match a with
  | .polynomial => ∅
  | .theta => {.inl i}
  | .xi => {.inr i}
  | .mixed => {.inl i,.inr i}

def localKind (T : Finset (OddIndex n)) (i : Fin n) : MomentKind :=
  if Sum.inl i∈T then (if Sum.inr i∈T then .mixed else .theta)
  else if Sum.inr i∈T then .xi else .polynomial

def localIndex (d : ℕ) (a : MomentKind) (i : Fin n) : SuperMonomialIndex n :=
  (Finsupp.single i d,blockOddSet a i)

def eraseIndex (z : SuperMonomialIndex n) (i : Fin n) : SuperMonomialIndex n :=
  (z.1.erase i,z.2.filter (fun j ↦ oddSite j≠i))

def joinIndex (z t : SuperMonomialIndex n) : SuperMonomialIndex n :=
  (z.1+t.1,z.2∪t.2)

@[simp] theorem occupied_join (z t : SuperMonomialIndex n) :
    occupied (joinIndex z t)=occupied z∪occupied t := by
  ext i
  simp only [mem_occupied,joinIndex,Finsupp.add_apply,Finset.mem_union]
  have hzero : z.1 i+t.1 i≠0 ↔ z.1 i≠0 ∨ t.1 i≠0 := by omega
  rw [hzero]
  tauto

@[simp] theorem occupied_eraseIndex (z : SuperMonomialIndex n) (i : Fin n) :
    occupied (eraseIndex z i)=(occupied z).erase i := by
  ext j
  simp only [mem_occupied,eraseIndex,Finsupp.erase_apply,Finset.mem_filter,
    oddSite,Finset.mem_erase]
  by_cases h : j=i
  · subst j; simp
  · simp [h,Ne.symm h]

theorem localKind_set (T : Finset (OddIndex n)) (i : Fin n) :
    blockOddSet (localKind T i) i=T.filter (fun j ↦ oddSite j=i) := by
  ext j
  cases j with
  | inl j =>
      by_cases hji : j=i
      · subst j
        by_cases ht : Sum.inl i∈T <;> by_cases hz : Sum.inr i∈T <;>
          simp [localKind,blockOddSet,ht,hz,oddSite]
      · by_cases ht : Sum.inl i∈T <;> by_cases hz : Sum.inr i∈T <;>
          simp [localKind,blockOddSet,ht,hz,oddSite,hji,Ne.symm hji]
  | inr j =>
      by_cases hji : j=i
      · subst j
        by_cases ht : Sum.inl i∈T <;> by_cases hz : Sum.inr i∈T <;>
          simp [localKind,blockOddSet,ht,hz,oddSite]
      · by_cases ht : Sum.inl i∈T <;> by_cases hz : Sum.inr i∈T <;>
          simp [localKind,blockOddSet,ht,hz,oddSite,hji,Ne.symm hji]

theorem localIndex_disjoint_erase (z : SuperMonomialIndex n) (i : Fin n) :
    Disjoint (localIndex (z.1 i) (localKind z.2 i) i).2 (eraseIndex z i).2 := by
  rw [localIndex,localKind_set]
  exact Finset.disjoint_filter_filter_not _ _ _

@[simp] theorem join_local_erase (z : SuperMonomialIndex n) (i : Fin n) :
    joinIndex (localIndex (z.1 i) (localKind z.2 i) i) (eraseIndex z i)=z := by
  apply Prod.ext
  · ext j
    by_cases h : j=i
    · subst j; simp [joinIndex,localIndex,eraseIndex]
    · simp [joinIndex,localIndex,eraseIndex,Finsupp.single_apply,h,Ne.symm h]
  · simp only [joinIndex,localIndex,eraseIndex,localKind_set]
    exact Finset.filter_union_filter_not_eq _ _

theorem occupied_localIndex_subset (d : ℕ) (a : MomentKind) (i : Fin n) :
    occupied (localIndex d a i)⊆{i} := by
  intro j hj
  rw [mem_occupied] at hj
  by_contra hji
  have hne : j≠i := by simpa using hji
  rcases hj with h|h|h
  · simpa [localIndex,Finsupp.single_apply,hne,Ne.symm hne] using h
  · cases a <;> simpa [localIndex,blockOddSet,hne,Ne.symm hne] using h
  · cases a <;> simpa [localIndex,blockOddSet,hne,Ne.symm hne] using h

theorem localKind_positive {z : SuperMonomialIndex n} {i : Fin n}
    (hi : i∈occupied z) : 0<z.1 i ∨ localKind z.2 i≠.polynomial := by
  rcases mem_occupied z i |>.mp hi with h|h|h
  · exact Or.inl (Nat.pos_of_ne_zero h)
  · exact Or.inr (by by_cases ht : Sum.inr i∈z.2 <;> simp [localKind,h,ht])
  · exact Or.inr (by by_cases ht : Sum.inl i∈z.2 <;> simp [localKind,ht,h])

theorem localDegree_join (p q : ℕ) (z t : SuperMonomialIndex n)
    (h : Disjoint z.2 t.2) (i : Fin n) :
    localDegree p q (joinIndex z t) i=localDegree p q z i+localDegree p q t i := by
  simp only [localDegree,joinIndex,Finsupp.add_apply,Finset.sum_union h]
  omega

@[simp] theorem localDegree_localIndex (p q d : ℕ) (a : MomentKind) (i j : Fin n) :
    localDegree p q (localIndex d a i) j=
      if i=j then d+oddWeight p q a else 0 := by
  by_cases h : i=j
  · subst j
    cases a <;> simp [localDegree,localIndex,blockOddSet,oddLocalWeight,oddWeight]
  · cases a <;>
      simp [localDegree,localIndex,blockOddSet,oddLocalWeight,oddWeight,h,Ne.symm h]

theorem localDegree_eraseIndex (p q : ℕ) (z : SuperMonomialIndex n) (i j : Fin n) :
    localDegree p q (eraseIndex z i) j=if j=i then 0 else localDegree p q z j := by
  by_cases hji : j=i
  · subst j
    simp only [localDegree,eraseIndex,Finsupp.erase_same,zero_add,if_pos rfl]
    apply Finset.sum_eq_zero
    intro k hk
    have h := (Finset.mem_filter.mp hk).2
    cases k <;> simp_all [oddLocalWeight,oddSite]
  · rw [if_neg hji]
    unfold localDegree eraseIndex
    rw [Finsupp.erase_ne hji]
    congr 1
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro k hk hnot
    have he : oddSite k=i := by simpa only [Finset.mem_filter,hk,true_and,not_not] using hnot
    cases k <;> simp_all [oddLocalWeight,oddSite,Ne.symm hji]

theorem localDegree_at_eq (p q : ℕ) (z : SuperMonomialIndex n) (i : Fin n) :
    localDegree p q z i=z.1 i+oddWeight p q (localKind z.2 i) := by
  have h := localDegree_join p q
    (localIndex (z.1 i) (localKind z.2 i) i) (eraseIndex z i)
    (localIndex_disjoint_erase z i) i
  rw [join_local_erase,localDegree_localIndex,localDegree_eraseIndex,
    if_pos rfl,if_pos rfl,add_zero] at h
  exact h

section ActualProducts

local instance coinvariantMonomialOrder : LinearOrder (OddIndex n) :=
  LinearOrder.lift' Exterior.modeRank Exterior.modeRank_injective

/-- Disjoint original exterior labels produce precisely a shuffle-sign unit. -/
theorem basis_mul_unit (z t : SuperMonomialIndex n) (h : Disjoint z.2 t.2) :
    ∃ ε : Rˣ,superMonomialBasis (K := R) z*superMonomialBasis t=
      (ε : R) • superMonomialBasis (joinIndex z t) := by
  let S : Set.powersetCard (OddIndex n) z.2.card := ⟨z.2,rfl⟩
  let T : Set.powersetCard (OddIndex n) t.2.card := ⟨t.2,rfl⟩
  let sign : ℤˣ := (Set.powersetCard.permOfDisjoint (s := S) (t := T) h).sign
  let ε : Rˣ := Units.map (Int.castRingHom R).toMonoidHom sign
  refine ⟨ε,?_⟩
  rw [superMonomialBasis_apply,superMonomialBasis_apply,
    Algebra.TensorProduct.tmul_mul_tmul,MvPolynomial.monomial_mul_monomial,one_mul,
    ExteriorAlgebra.basis_mul_of_disjoint (Pi.basisFun R (OddIndex n)) S T h,
    Set.powersetCard.coe_disjUnion,Finset.disjUnion_eq_union]
  change MvPolynomial.monomial (z.1+t.1) 1 ⊗ₜ[R]
    (sign • (Pi.basisFun R (OddIndex n)).ExteriorAlgebra (z.2∪t.2))=_
  have hε : (ε : R)=((sign : ℤ) : R) := rfl
  rw [hε,superMonomialBasis_apply]
  let p : PolynomialRing R n := MvPolynomial.monomial (z.1+t.1) 1
  let w : ExteriorAlgebra R (OddModule R n) :=
    (Pi.basisFun R (OddIndex n)).ExteriorAlgebra (z.2∪t.2)
  have hcast : sign • w=((sign : ℤ) : R) • w := by
    rw [Units.smul_def]
    exact (Int.cast_smul_eq_zsmul R (sign : ℤ) w).symm
  change p ⊗ₜ[R] (sign • w)=((sign : ℤ) : R) • (p ⊗ₜ[R] w)
  exact (congrArg (fun y : ExteriorAlgebra R (OddModule R n) ↦ p ⊗ₜ[R] y) hcast).trans
    (TensorProduct.tmul_smul ((sign : ℤ) : R) p w)

/-- Repeated original exterior labels give zero, not a new basis word. -/
theorem basis_mul_zero (z t : SuperMonomialIndex n) (h : ¬Disjoint z.2 t.2) :
    superMonomialBasis (K := R) z*superMonomialBasis t=0 := by
  rw [superMonomialBasis_apply,superMonomialBasis_apply,
    Algebra.TensorProduct.tmul_mul_tmul,
    ExteriorAlgebra.basis_mul_of_not_disjoint (Pi.basisFun R (OddIndex n))
      (⟨z.2,rfl⟩ : Set.powersetCard (OddIndex n) z.2.card)
      (⟨t.2,rfl⟩ : Set.powersetCard (OddIndex n) t.2.card) h,
    TensorProduct.tmul_zero]

private theorem basis_empty :
    (Pi.basisFun R (OddIndex n)).ExteriorAlgebra (∅ : Finset (OddIndex n))=1 := by
  rw [Module.Basis.exteriorAlgebra_eq_prod_map_sort]
  simp

private theorem basis_inl (i : Fin n) :
    (Pi.basisFun R (OddIndex n)) (.inl i)=Pi.single (.inl i) 1 := by
  funext j
  cases j <;> simp [Pi.basisFun_apply,Pi.single_apply]

private theorem basis_inr (i : Fin n) :
    (Pi.basisFun R (OddIndex n)) (.inr i)=Pi.single (.inr i) 1 := by
  funext j
  cases j <;> simp [Pi.basisFun_apply,Pi.single_apply]

/-- The local algebra factor is exactly the original supermonomial basis vector. -/
theorem localBlock_eq_basis (d : ℕ) (a : MomentKind) (i : Fin n) :
    localBlock (R := R) d a i=superMonomialBasis (localIndex d a i) := by
  rw [superMonomialBasis_apply]
  have he : even (R := R) i^d=
      Algebra.TensorProduct.includeLeft (R := R) (S := R)
        (MvPolynomial.monomial (Finsupp.single i d) (1:R)) := by
    rw [←MvPolynomial.X_pow_eq_monomial,map_pow]
    rfl
  rw [localBlock,he]
  cases a with
  | polynomial =>
      simp only [oddPart,localIndex,blockOddSet,basis_empty,mul_one,
        Algebra.TensorProduct.includeLeft_apply]
  | theta =>
      rw [show (localIndex d .theta i).2={Sum.inl i} from rfl,
        TauCeti.ExteriorAlgebra.basis_singleton,basis_inl]
      simp only [oddPart,theta,localIndex,Algebra.TensorProduct.includeLeft_apply,
        Algebra.TensorProduct.includeRight_apply,Algebra.TensorProduct.tmul_mul_tmul,mul_one,one_mul]
  | xi =>
      rw [show (localIndex d .xi i).2={Sum.inr i} from rfl,
        TauCeti.ExteriorAlgebra.basis_singleton,basis_inr]
      simp only [oddPart,xi,localIndex,Algebra.TensorProduct.includeLeft_apply,
        Algebra.TensorProduct.includeRight_apply,Algebra.TensorProduct.tmul_mul_tmul,mul_one,one_mul]
  | mixed =>
      have hi : @LT.lt (OddIndex n) coinvariantMonomialOrder.toLT (Sum.inl i) (Sum.inr i) := by
        change Exterior.modeRank (.inl i)<Exterior.modeRank (.inr i)
        simp only [Exterior.modeRank]
        omega
      have hpair : (Pi.basisFun R (OddIndex n)).ExteriorAlgebra
          (localIndex d .mixed i).2=
          ExteriorAlgebra.ι R ((Pi.basisFun R (OddIndex n)) (.inl i))*
            ExteriorAlgebra.ι R ((Pi.basisFun R (OddIndex n)) (.inr i)) := by
        convert TauCeti.ExteriorAlgebra.basis_pair (Pi.basisFun R (OddIndex n)) hi using 1 <;>
          congr 1 <;> ext j <;> simp [localIndex,blockOddSet]
      rw [hpair,basis_inl,basis_inr]
      simp only [oddPart,theta,xi,localIndex,Algebra.TensorProduct.includeLeft_apply,
        Algebra.TensorProduct.includeRight_apply,Algebra.TensorProduct.tmul_mul_tmul,
        mul_one,one_mul,mul_assoc]

/-- Removing one occupied coordinate gives a unit-valued, exact factorization. -/
theorem local_factorization (z : SuperMonomialIndex n) (i : Fin n) :
    ∃ ε : Rˣ,localBlock (R := R) (z.1 i) (localKind z.2 i) i*
      superMonomialBasis (eraseIndex z i)=(ε:R) • superMonomialBasis z := by
  rw [localBlock_eq_basis]
  obtain ⟨ε,hε⟩ := basis_mul_unit (R := R)
    (localIndex (z.1 i) (localKind z.2 i) i) (eraseIndex z i)
    (localIndex_disjoint_erase z i)
  exact ⟨ε,by simpa only [join_local_erase] using hε⟩

end ActualProducts
end PaperVerification.Fermion.Coinvariants
