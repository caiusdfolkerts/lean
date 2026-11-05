module

public import PaperVerification.HomogeneousKoszulRepresentation

/-!
# Equivariant comparison at two regular homogeneous fibers

The two endpoints may have different residue fields. The finite coefficient
and alternating Koszul matrices, their actions, and the literal quotient
presentations are all constructed. Exactness follows from regularity at the
chosen endpoint. If both endpoints are regular, applying the actual Reynolds
rank comparison in both directions identifies every intertwining dimension.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open MvPolynomial Representation
open PaperVerification.EquivariantHomMatrices

namespace PaperVerification.PowerOperators

variable {R K K₀ : Type*} [CommRing R] [IsDomain R] [Field K] [Field K₀] {n : ℕ}

theorem map_family_invariant (G : Subgroup (Equiv.Perm (Fin n)))
    (f : Fin n → MvPolynomial (Fin n) R)
    (hinv : ∀ g : G, ∀ i, MvPolynomial.rename (g : Equiv.Perm (Fin n)) (f i) = f i)
    (φ : R →+* K) (g : G) (i : Fin n) :
    MvPolynomial.rename (g : Equiv.Perm (Fin n)) (MvPolynomial.map φ (f i)) =
      MvPolynomial.map φ (f i) := by
  rw [← MvPolynomial.map_rename,hinv]

theorem ordinary_intertwiner_dimension_ge_exact_fiber
    (G : Subgroup (Equiv.Perm (Fin n))) [Fintype G]
    [Invertible (Fintype.card G : R)] [Invertible (Fintype.card G : K)]
    [Invertible (Fintype.card G : K₀)]
    (f : Fin n → MvPolynomial (Fin n) R) (m d : ℕ)
    (hf : ∀ i, (f i).IsHomogeneous (m+i.val))
    (hinv : ∀ g : G, ∀ i, MvPolynomial.rename (g : Equiv.Perm (Fin n)) (f i) = f i)
    (φ : R →+* K) (φ₀ : R →+* K₀)
    (hregular₀ : RingTheory.Sequence.IsWeaklyRegular (MvPolynomial (Fin n) K₀)
      (List.ofFn fun i : Fin n => MvPolynomial.map φ₀ (f i)))
    {l : Type*} [Fintype l] (τ : Representation R G (l → R)) :
    Module.finrank K₀ (IntertwiningMap (mapRepresentation φ₀ τ)
      (ordinaryQuotientDegreeRepresentation G (fun i => MvPolynomial.map φ₀ (f i))
        (map_family_invariant G f hinv φ₀) d)) ≤
    Module.finrank K (IntertwiningMap (mapRepresentation φ τ)
      (ordinaryQuotientDegreeRepresentation G (fun i => MvPolynomial.map φ (f i))
        (map_family_invariant G f hinv φ) d)) := by
  let fK := fun i => MvPolynomial.map φ (f i)
  let f₀ := fun i => MvPolynomial.map φ₀ (f i)
  let π := ordinaryQuotientDegreeRepresentation G fK (map_family_invariant G f hinv φ) d
  let π₀ := ordinaryQuotientDegreeRepresentation G f₀ (map_family_invariant G f hinv φ₀) d
  let q : IntertwiningMap (mapRepresentation φ (shiftedDegreeAction (R := R) G 0 d)) π :=
    { toLinearMap := ordinaryDegreeQuotientMap fK d
      isIntertwining' g := by
        rw [map_shiftedDegreeAction]
        exact (ordinaryDegreeQuotientIntertwiner G fK (map_family_invariant G f hinv φ) d).isIntertwining' g }
  let q₀ : IntertwiningMap (mapRepresentation φ₀ (shiftedDegreeAction (R := R) G 0 d)) π₀ :=
    { toLinearMap := ordinaryDegreeQuotientMap f₀ d
      isIntertwining' g := by
        rw [map_shiftedDegreeAction]
        exact (ordinaryDegreeQuotientIntertwiner G f₀ (map_family_invariant G f hinv φ₀) d).isIntertwining' g }
  have hexact : LinearMap.range ((ordinarySecondMatrix f m d).map φ₀).mulVecLin =
      LinearMap.ker ((ordinaryFirstMatrix f m d).map φ₀).mulVecLin := by
    rw [map_ordinarySecondMatrix,map_ordinaryFirstMatrix]
    exact ordinaryMatrices_exact _ m d (fun i => (hf i).map φ₀) hregular₀
  have hker : LinearMap.range ((ordinaryFirstMatrix f m d).map φ).mulVecLin =
      LinearMap.ker q.toLinearMap := by
    rw [map_ordinaryFirstMatrix]
    exact ordinaryDegreeQuotientMap_kernel fK m d (fun i => (hf i).map φ)
  have hker₀ : LinearMap.range ((ordinaryFirstMatrix f m d).map φ₀).mulVecLin =
      LinearMap.ker q₀.toLinearMap := by
    rw [map_ordinaryFirstMatrix]
    exact ordinaryDegreeQuotientMap_kernel f₀ m d (fun i => (hf i).map φ₀)
  exact intertwiner_cokernel_dimension_ge_exact_fiber
    τ (syzygyDegreeAction (R := R) G m d) (tailDegreeAction (R := R) G m d)
    (shiftedDegreeAction (R := R) G 0 d)
    (ordinaryFirstMatrix f m d) (ordinarySecondMatrix f m d)
    (ordinaryMatrices_complex f m d hf)
    (ordinaryFirstMatrix_intertwines G f m d hf hinv)
    (ordinarySecondMatrix_intertwines G f m d hf hinv)
    φ φ₀ hexact π π₀ q q₀ (ordinaryDegreeQuotientMap_surjective fK d)
    (ordinaryDegreeQuotientMap_surjective f₀ d) hker hker₀

/-- Two regular fibers of an invariant homogeneous family have equal actual
intertwining dimensions, even when the residue fields differ. -/
theorem ordinary_intertwiner_dimension_eq_at_regular_fibers
    (G : Subgroup (Equiv.Perm (Fin n))) [Fintype G]
    [Invertible (Fintype.card G : R)] [Invertible (Fintype.card G : K)]
    [Invertible (Fintype.card G : K₀)]
    (f : Fin n → MvPolynomial (Fin n) R) (m d : ℕ)
    (hf : ∀ i, (f i).IsHomogeneous (m+i.val))
    (hinv : ∀ g : G, ∀ i, MvPolynomial.rename (g : Equiv.Perm (Fin n)) (f i) = f i)
    (φ : R →+* K) (φ₀ : R →+* K₀)
    (hregular : RingTheory.Sequence.IsWeaklyRegular (MvPolynomial (Fin n) K)
      (List.ofFn fun i : Fin n => MvPolynomial.map φ (f i)))
    (hregular₀ : RingTheory.Sequence.IsWeaklyRegular (MvPolynomial (Fin n) K₀)
      (List.ofFn fun i : Fin n => MvPolynomial.map φ₀ (f i)))
    {l : Type*} [Fintype l] (τ : Representation R G (l → R)) :
    Module.finrank K₀ (IntertwiningMap (mapRepresentation φ₀ τ)
      (ordinaryQuotientDegreeRepresentation G (fun i => MvPolynomial.map φ₀ (f i))
        (map_family_invariant G f hinv φ₀) d)) =
    Module.finrank K (IntertwiningMap (mapRepresentation φ τ)
      (ordinaryQuotientDegreeRepresentation G (fun i => MvPolynomial.map φ (f i))
        (map_family_invariant G f hinv φ) d)) := by
  exact le_antisymm
    (ordinary_intertwiner_dimension_ge_exact_fiber G f m d hf hinv φ φ₀ hregular₀ τ)
    (ordinary_intertwiner_dimension_ge_exact_fiber G f m d hf hinv φ₀ φ hregular τ)

end PaperVerification.PowerOperators
