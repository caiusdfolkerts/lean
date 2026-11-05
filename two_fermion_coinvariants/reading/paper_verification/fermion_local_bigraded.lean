module

public import PaperVerification.FermionExteriorGradedMaps

/-!
# Exterior-bigraded local normalization

Both sides carry the image components of their original ordered exterior
basis words. The proof checks the canonical quotient representatives and
uses the genuine diagonal unit change, which scales theta and xi separately.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace PaperVerification.Fermion

section OddNormalization

variable {F A ι κ : Type*} [Field F] [CommRing A] [Algebra F A]
  [Fintype ι] [Fintype κ] [LinearOrder (ι⊕ι)]

variable (G : Polynomial F) (hG : G≠0)
  (center : κ → F) (hc : Function.Injective center)
  (cluster : ι → κ) (node z beta a b : ι → A) (r u v : ι → ℕ)
  (hz : ∀ i,z i^r i=node i-algebraMap F A (center (cluster i)))
  (N : κ → ℕ)
  (hN : ∀ i,(node i-algebraMap F A (center (cluster i)))^(N (cluster i))=0)
  (unitA unitB : ι → Aˣ)
  (ha : ∀ i,a i=z i^u i*(unitA i : A))
  (hb : ∀ i,b i=z i^v i*(unitB i : A))
  (hAB : ∀ i,(unitA i : A)*(unitB i : A)=
    Polynomial.aeval (node i) (rootCofactor G (center (cluster i))))

theorem oddNormalization_bigraded_iff (degree : ℕ×ℕ)
    (x : SeparatedOddQuotient node beta a b) :
    oddNormalizationEquiv G hG center hc cluster node z beta a b r u v
        hz N hN unitA unitB ha hb hAB x∈
      clusterOddBigradedPart cluster z beta r u v degree ↔
      x∈separatedOddBigradedPart node beta a b degree := by
  let e := oddNormalizationEquiv G hG center hc cluster node z beta a b r u v
    hz N hN unitA unitB ha hb hAB
  let d := pairedOddUnitEquiv unitA unitB
  constructor
  · intro hx
    obtain ⟨y,hy,hey⟩ := hx
    refine ⟨d y,exteriorDiagonalUnitEquiv_weighted_mem oddBidegree
      (Sum.elim unitB unitA) hy,?_⟩
    apply e.injective
    change e ((separatedOddIdeal node beta a b).ringCon.mkₐ A (d y))=e x
    rw [oddNormalizationEquiv_mk,AlgEquiv.symm_apply_apply]
    exact hey
  · intro hx
    obtain ⟨y,hy,rfl⟩ := hx
    refine ⟨d.symm y,exteriorDiagonalUnitEquiv_symm_weighted_mem oddBidegree
      (Sum.elim unitB unitA) hy,?_⟩
    exact (oddNormalizationEquiv_mk G hG center hc cluster node z beta a b r u v
      hz N hN unitA unitB ha hb hAB y).symm

end OddNormalization

section Coefficients

variable {F A B ι κ : Type*} [CommRing F] [CommRing A] [CommRing B]
  [Algebra F A] [Algebra F B] [Fintype ι] [Fintype κ] [LinearOrder (ι⊕ι)]

theorem clusterOddCoefficientEquiv_bigraded_iff (e : A ≃ₐ[F] B)
    (cluster : ι → κ) (z beta : ι → A) (r u v : ι → ℕ) (degree : ℕ×ℕ)
    (x : ClusterOddQuotient cluster z beta r u v) :
    clusterOddCoefficientEquiv e cluster z beta r u v x∈
      clusterOddBigradedPart cluster (fun i ↦ e (z i)) (fun i ↦ e (beta i)) r u v degree ↔
      x∈clusterOddBigradedPart cluster z beta r u v degree := by
  let f := clusterOddCoefficientEquiv e cluster z beta r u v
  let d := finiteExteriorCoefficientEquiv (ι := ι⊕ι) e
  constructor
  · intro hx
    obtain ⟨y,hy,hey⟩ := hx
    refine ⟨d.symm y,?_,?_⟩
    · rw [finiteExteriorCoefficientEquiv_symm]
      exact exteriorWeighted_coefficient_map_mem oddBidegree e.symm hy
    · apply f.injective
      change (clusterOddIdeal cluster (fun i ↦ e (z i)) (fun i ↦ e (beta i)) r u v).ringCon.mkₐ B
        (d (d.symm y))=f x
      rw [AlgEquiv.apply_symm_apply]
      exact hey
  · intro hx
    obtain ⟨y,hy,rfl⟩ := hx
    exact ⟨d y,exteriorWeighted_coefficient_map_mem oddBidegree e hy,rfl⟩

end Coefficients

end PaperVerification.Fermion

