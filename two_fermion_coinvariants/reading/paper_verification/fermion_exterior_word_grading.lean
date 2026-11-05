module

public import PaperVerification.FermionBasisGrading
public import PaperVerification.FermionDiagonalExterior
public import TauCeti.LinearAlgebra.ExteriorAlgebra.Contraction

/-!
# The natural grading of actual exterior basis words

Extracted without mathematical changes from
FermionExteriorMultigrading so the color action needs no local-coordinate
or moment-normalization imports.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators

namespace PaperVerification.Fermion

section Exterior

variable {A ι Γ : Type*} [CommRing A] [Fintype ι] [LinearOrder ι]
  [AddCommMonoid Γ] [DecidableEq Γ]

def exteriorWordDegree (w : ι → Γ) (T : Finset ι) : Γ := ∑ i∈T,w i

def exteriorWeightedPart (w : ι → Γ) (g : Γ) :
    Submodule A (ExteriorAlgebra A (ι → A)) :=
  basisDegreePart (Pi.basisFun A ι).ExteriorAlgebra (exteriorWordDegree w) g

theorem exteriorWeightedPart_basis (w : ι → Γ) (T : Finset ι) :
    (Pi.basisFun A ι).ExteriorAlgebra T∈exteriorWeightedPart w (exteriorWordDegree w T) :=
  Submodule.subset_span ⟨T,rfl,rfl⟩

theorem exteriorWeightedPart_one (w : ι → Γ) :
    (1 : ExteriorAlgebra A (ι → A))∈exteriorWeightedPart w 0 := by
  have he : (Pi.basisFun A ι).ExteriorAlgebra (∅ : Finset ι)=1 := by
    rw [Module.Basis.exteriorAlgebra_eq_prod_map_sort]
    simp
  simpa only [exteriorWordDegree,Finset.sum_empty,he] using
    exteriorWeightedPart_basis (A := A) w (∅ : Finset ι)

theorem exteriorWeightedPart_basis_mul (w : ι → Γ) (S T : Finset ι) :
    (Pi.basisFun A ι).ExteriorAlgebra S*(Pi.basisFun A ι).ExteriorAlgebra T∈
      exteriorWeightedPart w (exteriorWordDegree w S+exteriorWordDegree w T) := by
  by_cases h : Disjoint S T
  · let S' : Set.powersetCard ι S.card := ⟨S,rfl⟩
    let T' : Set.powersetCard ι T.card := ⟨T,rfl⟩
    let a : A := ((Set.powersetCard.permOfDisjoint (s := S') (t := T') h).sign : ℤ)
    have hp :
        (Pi.basisFun A ι).ExteriorAlgebra S*(Pi.basisFun A ι).ExteriorAlgebra T=
          a • (Pi.basisFun A ι).ExteriorAlgebra (S.disjUnion T h) := by
      simpa only [a,Units.smul_def,Int.cast_smul_eq_zsmul,Set.powersetCard.coe_disjUnion] using
        ExteriorAlgebra.basis_mul_of_disjoint (Pi.basisFun A ι) S' T' h
    rw [hp]
    apply Submodule.smul_mem
    have hd : exteriorWordDegree w (S.disjUnion T h)=
        exteriorWordDegree w S+exteriorWordDegree w T := Finset.sum_disjUnion h
    rw [←hd]
    exact exteriorWeightedPart_basis w _
  · rw [ExteriorAlgebra.basis_mul_of_not_disjoint (Pi.basisFun A ι)
      (⟨S,rfl⟩ : Set.powersetCard ι S.card)
      (⟨T,rfl⟩ : Set.powersetCard ι T.card) h]
    exact Submodule.zero_mem _

def exteriorWeightedGrading (w : ι → Γ) :
    GradedAlgebra (exteriorWeightedPart (A := A) w) :=
  basisDegreeGradedAlgebra (Pi.basisFun A ι).ExteriorAlgebra (exteriorWordDegree w)
    (exteriorWeightedPart_one w) (exteriorWeightedPart_basis_mul w)

theorem exteriorGenerator_weighted_mem (w : ι → Γ) (i : ι) :
    exteriorGenerator (A := A) i∈exteriorWeightedPart w (w i) := by
  have he : (Pi.basisFun A ι).ExteriorAlgebra {i}=exteriorGenerator (A := A) i := by
    rw [TauCeti.ExteriorAlgebra.basis_singleton]
    rfl
  simpa only [exteriorWordDegree,Finset.sum_singleton,he] using
    exteriorWeightedPart_basis (A := A) w {i}

end Exterior

end PaperVerification.Fermion
