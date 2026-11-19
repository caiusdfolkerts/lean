module

public import Recovery.Unimodular.FlagKoszul.IndependentTor

/-!
# Ordinary bar boundaries and Tor along an actual algebra equivalence

The target basis is the image of the original basis and its multiplication
coefficients are proved equal. Consequently the actual reduced bar operators
are equal on the original coefficient word space. The internal degree is kept
unchanged. The final statements use genuine ordinary derived augmentation Tor.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section

namespace Unimodular.FlagKoszul.AlgebraTransport

open PaperVerification.AugmentedAlgebraBasis PaperVerification.ReducedBarBasis

section Data
variable {K A B I : Type*} [Field K] [Ring A] [Algebra K A] [Ring B] [Algebra K B]

abbrev basis (e : A ≃ₐ[K] B) (D : Module.Basis (Option I) K A) :
    Module.Basis (Option I) K B := D.map e.toLinearEquiv

def augmentation (e : A ≃ₐ[K] B) (ε : A →ₐ[K] K) : B →ₐ[K] K := ε.comp e.symm.toAlgHom

@[simp] theorem basis_apply (e : A ≃ₐ[K] B) (D : Module.Basis (Option I) K A)
    (i : Option I) : basis e D i = e (D i) := rfl

@[simp] theorem basis_repr (e : A ≃ₐ[K] B) (D : Module.Basis (Option I) K A)
    (b : B) (i : Option I) : (basis e D).repr b i = D.repr (e.symm b) i := rfl

@[simp] theorem augmentation_apply (e : A ≃ₐ[K] B) (ε : A →ₐ[K] K) (b : B) :
    augmentation e ε b = ε (e.symm b) := rfl

theorem unit_transport (e : A ≃ₐ[K] B) (D : Module.Basis (Option I) K A)
    (hunit : D none = 1) : basis e D none = 1 := by rw [basis_apply, hunit, map_one]

theorem augmentation_transport (e : A ≃ₐ[K] B) (ε : A →ₐ[K] K)
    (D : Module.Basis (Option I) K A) (hε : ∀ i, ε (D (some i)) = 0) :
    ∀ i, augmentation e ε (basis e D (some i)) = 0 := by
  intro i
  rw [augmentation_apply, basis_apply, AlgEquiv.symm_apply_apply]
  exact hε i

/-- The actual structure coefficients are unchanged by the algebra isomorphism. -/
theorem productCoefficients_transport (e : A ≃ₐ[K] B)
    (D : Module.Basis (Option I) K A) (i j : I) :
    productCoefficients (basis e D) i j = productCoefficients D i j := by
  ext l
  change D.repr (e.symm (e (D (some i)) * e (D (some j)))) (some l) =
    D.repr (D (some i) * D (some j)) (some l)
  rw [← map_mul, AlgEquiv.symm_apply_apply]

theorem mergeBasis_transport (e : A ≃ₐ[K] B) (D : Module.Basis (Option I) K A)
    (i : I) (L : List I) : mergeBasis (basis e D) i L = mergeBasis D i L := by
  cases L with
  | nil => rfl
  | cons j L => simp only [mergeBasis, productCoefficients_transport]

theorem merge_transport (e : A ≃ₐ[K] B) (D : Module.Basis (Option I) K A)
    (i : I) : merge (basis e D) i = merge D i := by
  apply Finsupp.lhom_ext
  intro L c
  simp only [merge_single, mergeBasis_transport]

theorem differentialBasis_transport (e : A ≃ₐ[K] B)
    (D : Module.Basis (Option I) K A) (L : List I) :
    differentialBasis (basis e D) L = differentialBasis D L := by
  induction L with
  | nil => rfl
  | cons i L ih => simp only [differentialBasis, merge_transport, ih]

/-- This is an equality of the literal reduced-bar linear maps. -/
theorem differential_transport (e : A ≃ₐ[K] B) (D : Module.Basis (Option I) K A) :
    differential (basis e D) = differential D := by
  apply Finsupp.lhom_ext
  intro L c
  simp only [differential_single, differentialBasis_transport]

theorem productDegree_transport (e : A ≃ₐ[K] B) (D : Module.Basis (Option I) K A)
    (δ : I → ℕ)
    (hδ : ∀ i j l, productCoefficients D i j l ≠ 0 → δ l = δ i + δ j) :
    ∀ i j l, productCoefficients (basis e D) i j l ≠ 0 → δ l = δ i + δ j := by
  intro i j l h
  rw [productCoefficients_transport] at h
  exact hδ i j l h

/-- Every constructed homogeneous boundary is preserved, without replacing
or identifying any actual algebra elements by fiat. -/
theorem boundaries_transport (e : A ≃ₐ[K] B) (D : Module.Basis (Option I) K A)
    (δ : I → ℕ)
    (hbound : ∀ r N, r < N → ∀ z : List I →₀ K,
      z ∈ BarReindex.homogeneousPiece δ r N → differential D z = 0 →
      ∃ y ∈ BarReindex.homogeneousPiece δ (r + 1) N, -differential D y = z) :
    ∀ r N, r < N → ∀ z : List I →₀ K,
      z ∈ BarReindex.homogeneousPiece δ r N → differential (basis e D) z = 0 →
      ∃ y ∈ BarReindex.homogeneousPiece δ (r + 1) N,
        -differential (basis e D) y = z := by
  simpa only [differential_transport] using hbound

end Data

section OrdinaryTor
universe u v
variable {K A B J : Type u} {I : Type v} [Field K]
  [Ring A] [Algebra K A] [Ring B] [Algebra K B]

/-- Transport to a genuinely isomorphic algebra and any equivalent basis
index in the ordinary module category's universe. -/
theorem hasDiagonalTor_reindex (e : A ≃ₐ[K] B) (index : I ≃ J)
    (ε : A →ₐ[K] K) (D : Module.Basis (Option I) K A)
    (hunit : D none = 1) (hε : ∀ i, ε (D (some i)) = 0) (δ : I → ℕ)
    (hδ : ∀ i j l, productCoefficients D i j l ≠ 0 → δ l = δ i + δ j)
    (hpos : ∀ i, 0 < δ i)
    (hbound : ∀ r N, r < N → ∀ z : List I →₀ K,
      z ∈ BarReindex.homogeneousPiece δ r N → differential D z = 0 →
      ∃ y ∈ BarReindex.homogeneousPiece δ (r + 1) N, -differential D y = z) :
    PaperVerification.WeightedBar.HasDiagonalTor (augmentation e ε)
      (BarReindex.basis index (basis e D))
      (BarReindex.unit_transport index (basis e D) (unit_transport e D hunit))
      (BarReindex.augmentation_transport index (augmentation e ε) (basis e D)
        (augmentation_transport e ε D hε))
      (δ ∘ index.symm)
      (BarReindex.productDegree_transport index (basis e D) δ (productDegree_transport e D δ hδ)) :=
  BarReindex.hasDiagonalTor_reindex index (augmentation e ε) (basis e D)
    (unit_transport e D hunit) (augmentation_transport e ε D hε) δ
    (productDegree_transport e D δ hδ) hpos (boundaries_transport e D δ hbound)

end OrdinaryTor

section ArbitraryField
universe u
variable {K A B : Type u} {I : Type} [Field K]
  [Ring A] [Algebra K A] [Ring B] [Algebra K B]

/-- The practical geometric-index endpoint, over any coefficient field. -/
theorem hasDiagonalTor_ulift (e : A ≃ₐ[K] B) (ε : A →ₐ[K] K)
    (D : Module.Basis (Option I) K A) (hunit : D none = 1)
    (hε : ∀ i, ε (D (some i)) = 0) (δ : I → ℕ)
    (hδ : ∀ i j l, productCoefficients D i j l ≠ 0 → δ l = δ i + δ j)
    (hpos : ∀ i, 0 < δ i)
    (hbound : ∀ r N, r < N → ∀ z : List I →₀ K,
      z ∈ BarReindex.homogeneousPiece δ r N → differential D z = 0 →
      ∃ y ∈ BarReindex.homogeneousPiece δ (r + 1) N, -differential D y = z) :
    PaperVerification.WeightedBar.HasDiagonalTor (augmentation e ε)
      (BarReindex.basis (Equiv.ulift.symm : I ≃ ULift.{u} I) (basis e D))
      (BarReindex.unit_transport Equiv.ulift.symm (basis e D) (unit_transport e D hunit))
      (BarReindex.augmentation_transport Equiv.ulift.symm (augmentation e ε) (basis e D)
        (augmentation_transport e ε D hε))
      (δ ∘ Equiv.ulift)
      (BarReindex.productDegree_transport Equiv.ulift.symm (basis e D) δ
        (productDegree_transport e D δ hδ)) :=
  hasDiagonalTor_reindex e Equiv.ulift.symm ε D hunit hε δ hδ hpos hbound

end ArbitraryField

#print axioms productCoefficients_transport
#print axioms differential_transport
#print axioms boundaries_transport
#print axioms hasDiagonalTor_reindex
#print axioms hasDiagonalTor_ulift

end Unimodular.FlagKoszul.AlgebraTransport

#check Unimodular.FlagKoszul.AlgebraTransport.hasDiagonalTor_ulift
