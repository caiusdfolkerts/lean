module

public import PaperVerification.DimensionFiveGradedBasis
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# A finite homogeneous augmented basis with prescribed degree-one vectors

The degree-zero vector is literally one. The degree-one basis is supplied
as a basis of the actual degree-one subspace and is retained exactly. All
higher vectors are chosen inside their actual homogeneous subspaces. The
full algebra's finite dimensionality proves the resulting positive index
finite; no cutoff, Hilbert formula, or Koszul assertion is assumed.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace PaperVerification.HomogeneousAugmentedBasis

universe u
variable {K A ν : Type u} [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A]
  (G : TauCeti.InternalGrading K A ℕ)

abbrev DegreeIndex : ℕ → Type u
  | 0 => ULift.{u} (Fin 1)
  | 1 => ν
  | d+2 => ULift.{u} (Fin (Module.finrank K (G.piece (d+2))))

abbrev PositiveIndex := ν ⊕ (Σ d : ℕ,ULift.{u} (Fin (Module.finrank K (G.piece (d+2)))))

def positiveDegree : PositiveIndex (ν := ν) G → ℕ
  | .inl _ => 1
  | .inr ⟨d,_⟩ => d+2

theorem positiveDegree_pos (i : PositiveIndex (ν := ν) G) : 0<positiveDegree G i := by
  rcases i with i | ⟨d,i⟩ <;> simp only [positiveDegree] <;> omega

def indexEquiv : (Σ d,DegreeIndex (ν := ν) G d) ≃ Option (PositiveIndex (ν := ν) G) where
  toFun
    | ⟨0,_⟩ => none
    | ⟨1,i⟩ => some (.inl i)
    | ⟨d+2,i⟩ => some (.inr ⟨d,i⟩)
  invFun
    | none => ⟨0,⟨0⟩⟩
    | some (.inl i) => ⟨1,i⟩
    | some (.inr ⟨d,i⟩) => ⟨d+2,i⟩
  left_inv := by
    rintro ⟨d,i⟩
    rcases d with _ | _ | d
    · have hi : i=(⟨0⟩ : ULift.{u} (Fin 1)) := Subsingleton.elim _ _
      subst i
      rfl
    · rfl
    · rfl
  right_inv := by
    rintro (_ | i | ⟨d,i⟩) <;> rfl

variable (ε : A →ₐ[K] K) (hzero : G.piece 0=(1 : Submodule K A))
  (b₁ : Module.Basis ν K (G.piece 1))

def degreeBasis : (d : ℕ) → Module.Basis (DegreeIndex (ν := ν) G d) K (G.piece d)
  | 0 => (Module.Basis.singleton (ULift.{u} (Fin 1)) K).map
      (DimensionFiveGradedBasis.scalarPieceEquiv G ε hzero)
  | 1 => b₁
  | d+2 => (Module.finBasis K (G.piece (d+2))).reindex Equiv.ulift.symm

def basis : Module.Basis (Option (PositiveIndex (ν := ν) G)) K A :=
  (G.isInternal.collectedBasis (degreeBasis G ε hzero b₁)).reindex (indexEquiv G)

/-- Finite dimensionality, rather than an assumed finite degree cutoff,
proves that the actual collected basis has finitely many positive vectors. -/
def positiveFintype : Fintype (PositiveIndex (ν := ν) G) := by
  haveI : Finite (Option (PositiveIndex (ν := ν) G)) :=
    Module.Finite.finite_basis (basis G ε hzero b₁)
  haveI : Finite (PositiveIndex (ν := ν) G) :=
    Finite.of_injective (some : PositiveIndex (ν := ν) G → Option (PositiveIndex (ν := ν) G))
      (Option.some_injective _)
  exact Fintype.ofFinite _

theorem basis_none : basis G ε hzero b₁ none=1 := by
  rw [basis,Module.Basis.reindex_apply,DirectSum.IsInternal.collectedBasis_coe]
  change ((degreeBasis G ε hzero b₁ 0) (⟨0⟩ : ULift.{u} (Fin 1)) : A)=1
  simp only [degreeBasis,Module.Basis.map_apply,Module.Basis.singleton_apply,
    DimensionFiveGradedBasis.scalarPieceEquiv_val,map_one]

/-- The supplied degree-one vectors are retained literally. -/
theorem basis_one (i : ν) : basis G ε hzero b₁ (some (.inl i))=(b₁ i : A) := by
  rw [basis,Module.Basis.reindex_apply,DirectSum.IsInternal.collectedBasis_coe]
  rfl

theorem basis_positive_mem (i : PositiveIndex (ν := ν) G) :
    basis G ε hzero b₁ (some i)∈G.piece (positiveDegree G i) := by
  rw [basis,Module.Basis.reindex_apply]
  rcases i with i | ⟨d,i⟩
  · change (G.isInternal.collectedBasis (degreeBasis G ε hzero b₁)) ⟨1,i⟩∈G.piece 1
    exact G.isInternal.collectedBasis_mem (degreeBasis G ε hzero b₁) ⟨1,i⟩
  · change (G.isInternal.collectedBasis (degreeBasis G ε hzero b₁)) ⟨d+2,i⟩∈G.piece (d+2)
    exact G.isInternal.collectedBasis_mem (degreeBasis G ε hzero b₁) ⟨d+2,i⟩

theorem basis_repr_of_mem_ne {d : ℕ} {x : A} (hx : x∈G.piece d)
    (i : PositiveIndex (ν := ν) G) (hi : d≠positiveDegree G i) :
    (basis G ε hzero b₁).repr x (some i)=0 := by
  rw [basis,Module.Basis.repr_reindex_apply]
  rcases i with i | ⟨q,i⟩ <;>
    exact G.isInternal.collectedBasis_repr_of_mem_ne (degreeBasis G ε hzero b₁) hi hx

/-- Exactly the originally prescribed vectors have internal degree one. -/
def degreeOneIndexEquiv : ν ≃ {i : PositiveIndex (ν := ν) G // positiveDegree G i=1} where
  toFun i := ⟨.inl i,rfl⟩
  invFun
    | ⟨.inl i,_⟩ => i
    | ⟨.inr ⟨d,_⟩,h⟩ => False.elim (by change d+2=1 at h; omega)
  left_inv _ := rfl
  right_inv := by
    rintro ⟨i | ⟨d,i⟩,h⟩
    · rfl
    · change d+2=1 at h
      omega

variable (hε : ∀ d,0<d → ∀ x,x∈G.piece d → ε x=0)
  (hmul : ∀ d e (x y : A),x∈G.piece d → y∈G.piece e → x*y∈G.piece (d+e))

include hε in
theorem basis_positive_augmentation (i : PositiveIndex (ν := ν) G) :
    ε (basis G ε hzero b₁ (some i))=0 :=
  hε _ (positiveDegree_pos G i) _ (basis_positive_mem G ε hzero b₁ i)

include hmul in
theorem product_homogeneous (a b c : PositiveIndex (ν := ν) G)
    (h : AugmentedAlgebraBasis.productCoefficients (basis G ε hzero b₁) a b c≠0) :
    positiveDegree G c=positiveDegree G a+positiveDegree G b := by
  by_contra hc
  apply h
  change (basis G ε hzero b₁).repr
    (basis G ε hzero b₁ (some a)*basis G ε hzero b₁ (some b)) (some c)=0
  exact basis_repr_of_mem_ne G ε hzero b₁
    (hmul _ _ _ _ (basis_positive_mem G ε hzero b₁ a)
      (basis_positive_mem G ε hzero b₁ b)) c (Ne.symm hc)

end PaperVerification.HomogeneousAugmentedBasis
