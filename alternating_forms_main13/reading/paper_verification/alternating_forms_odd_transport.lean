module

public import PaperVerification.AlternatingFormsExteriorTransport
public import PaperVerification.AlternatingFormsOddPencilRelations

/-!
# Naturality of the displayed odd pencil

The two matching quadrics commute with every linear map.  A chosen basis
therefore identifies their degree quotients with the standard-coordinate
quotient through the actual exterior algebra functor.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.AlternatingForms

variable {K M N : Type*} [Field K]
  [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]

theorem exteriorPower_map_exteriorPair (l : M →ₗ[K] N) (u v : M) :
    exteriorPower.map 2 l (exteriorPair u v) = exteriorPair (l u) (l v) := by
  apply Subtype.ext
  simp only [exteriorPower.coe_map, exteriorPair_coe, map_mul,
    ExteriorAlgebra.map_apply_ι]

theorem matchingQuadratic_map {ι : Type*} [Fintype ι] [DecidableEq ι]
    (l : M →ₗ[K] N) (u v : ι → M) :
    exteriorPower.map 2 l (matchingQuadratic u v) =
      matchingQuadratic (l ∘ u) (l ∘ v) := by
  simp only [matchingQuadratic, map_sum, exteriorPower_map_exteriorPair,
    Function.comp_apply]

theorem oddPathFirstQuadratic_map {k : ℕ} (l : M →ₗ[K] N)
    (z : Fin (2*k+1) → M) :
    exteriorPower.map 2 l (oddPathFirstQuadratic (K := K) z) =
      oddPathFirstQuadratic (K := K) (l ∘ z) := by
  rw [oddPathFirstQuadratic, matchingQuadratic_map]
  rfl

theorem oddPathSecondQuadratic_map {k : ℕ} (l : M →ₗ[K] N)
    (z : Fin (2*k+1) → M) :
    exteriorPower.map 2 l (oddPathSecondQuadratic (K := K) z) =
      oddPathSecondQuadratic (K := K) (l ∘ z) := by
  rw [oddPathSecondQuadratic, matchingQuadratic_map]
  rfl

def standardBasisEquiv {n : ℕ} (b : Module.Basis (Fin n) K M) :
    (Fin n → K) ≃ₗ[K] M :=
  (Pi.basisFun K (Fin n)).equiv b (Equiv.refl (Fin n))

@[simp] theorem standardBasisEquiv_basisFun {n : ℕ}
    (b : Module.Basis (Fin n) K M) (i : Fin n) :
    standardBasisEquiv b (Pi.basisFun K (Fin n) i) = b i := by
  simp only [standardBasisEquiv, Module.Basis.equiv_apply, Equiv.refl_apply]

theorem oddPathFirstQuadratic_standardBasisEquiv {k : ℕ}
    (b : Module.Basis (Fin (2*k+1)) K M) :
    exteriorPower.map 2 (standardBasisEquiv b).toLinearMap
      (oddPathFirstQuadratic (K := K) (Pi.basisFun K (Fin (2*k+1)))) =
      oddPathFirstQuadratic (K := K) b := by
  rw [oddPathFirstQuadratic_map]
  congr 1
  funext i
  exact standardBasisEquiv_basisFun b i

theorem oddPathSecondQuadratic_standardBasisEquiv {k : ℕ}
    (b : Module.Basis (Fin (2*k+1)) K M) :
    exteriorPower.map 2 (standardBasisEquiv b).toLinearMap
      (oddPathSecondQuadratic (K := K) (Pi.basisFun K (Fin (2*k+1)))) =
      oddPathSecondQuadratic (K := K) b := by
  rw [oddPathSecondQuadratic_map]
  congr 1
  funext i
  exact standardBasisEquiv_basisFun b i

def oddExteriorBasisChangeEquiv {k : ℕ}
    (b : Module.Basis (Fin (2*k+1)) K M) (s : ℕ) :
    ExteriorQuotientDegree
      (oddPathFirstQuadratic (K := K) (Pi.basisFun K (Fin (2*k+1))))
      (oddPathSecondQuadratic (K := K) (Pi.basisFun K (Fin (2*k+1)))) s ≃ₗ[K]
    ExteriorQuotientDegree (oddPathFirstQuadratic (K := K) b) (oddPathSecondQuadratic (K := K) b) s :=
  exteriorQuotientDegreePencilEquiv (standardBasisEquiv b) _ _ _ _
    (by rw [oddPathFirstQuadratic_standardBasisEquiv,
      oddPathSecondQuadratic_standardBasisEquiv]) s

@[simp] theorem oddExteriorBasisChangeEquiv_mk {k : ℕ}
    (b : Module.Basis (Fin (2*k+1)) K M) (s : ℕ)
    (x : ⋀[K]^s (Fin (2*k+1) → K)) :
    oddExteriorBasisChangeEquiv b s (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk
        (exteriorPower.map s (standardBasisEquiv b).toLinearMap x) := by
  rw [oddExteriorBasisChangeEquiv, exteriorQuotientDegreePencilEquiv_mk]

end PaperVerification.AlternatingForms
