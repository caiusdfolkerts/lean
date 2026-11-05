module

public import PaperVerification.ToricOrbitChartQuotient
public import PaperVerification.ToricQuotientFaceCoordinates
public import PaperVerification.ToricChartLocalization

@[expose] public section

/-!
# The orbit chart is the actual chart of the quotient star

Vanishing on a smooth cone gives the saturated character lattice dual to
the quotient of the normal lattice. The coordinate maps are integral, and
the pairing identity identifies the two actual nonnegative semigroups.
Consequently the orbit quotient is a surjective map of the literal chart
algebras, rather than an assumed description of an orbit closure.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open PaperVerification.ToricCharacters
open AddMonoidAlgebra AlgebraicGeometry CategoryTheory
open scoped BigOperators Classical

variable {n : ℕ}

theorem integerPairing_basis_eq_dualCoordinate
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (i : Fin n) (m : Lattice n) :
    integerPairing (b i) m = (integralDualBasis b).repr m i := by
  simp only [integerPairing,integralDualBasis_repr,mul_comm]

theorem embed_faceTangentLattice
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (z : Lattice (n-I.card)) :
    embed n (faceTangentLattice b I z) =
      faceTangentReal b I (embed (n-I.card) z) := by
  simp only [faceTangentLattice,faceTangentReal,selectedBasisMap_apply,
    map_sum,embed_int_smul,integralBasisReal_apply]
  rfl

theorem integerPairing_faceTangentLattice
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (u : Lattice n) (z : Lattice (n-I.card)) :
    integerPairing u (faceTangentLattice b I z) =
      integerPairing (coneQuotientLattice b I u) z := by
  have h := faceTangentReal_pairing b I (embed n u) (embed (n-I.card) z)
  rw [← embed_faceTangentLattice,coneQuotient_compatible,
    SmoothCompleteFan.normalRay_pairing_lattice,
    SmoothCompleteFan.normalRay_pairing_lattice] at h
  exact_mod_cast h

def faceCharacterProjection
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n)) :
    Lattice n →ₗ[ℤ] Lattice (n-I.card) where
  toFun m j := (integralDualBasis b).repr m (complementaryEmbedding I j)
  map_add' m p := by ext j; simp
  map_smul' a m := by
    ext j
    exact congrArg (fun z : Fin n →₀ ℤ => z (complementaryEmbedding I j))
      ((integralDualBasis b).repr.map_smul a m)

@[simp] theorem faceCharacterProjection_tangent
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (z : Lattice (n-I.card)) :
    faceCharacterProjection b I (faceTangentLattice b I z) = z := by
  ext j
  exact selectedBasisMap_coordinate (integralDualBasis b) (complementaryEmbedding I) z j

theorem faceTangentLattice_annihilates
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (z : Lattice (n-I.card)) (u : Lattice n) (hu : u∈I.image b) :
    integerPairing u (faceTangentLattice b I z)=0 := by
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hu
  rw [integerPairing_basis_eq_dualCoordinate]
  apply selectedBasisMap_coordinate_eq_zero
  simpa only [mem_range_complementaryEmbedding_iff,not_not] using hi

theorem faceTangentLattice_projection
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (m : Lattice n) (hm : ∀ u∈I.image b,integerPairing u m=0) :
    faceTangentLattice b I (faceCharacterProjection b I m)=m := by
  apply selectedBasisMap_repr_restrict
  intro i hi
  have hiI : i∈I := by
    simpa only [mem_range_complementaryEmbedding_iff,not_not] using hi
  rw [← integerPairing_basis_eq_dualCoordinate]
  exact hm (b i) (Finset.mem_image.mpr ⟨i,hiI,rfl⟩)

def orbitQuotientCone
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (s : Finset (Lattice n)) : Finset (Lattice (n-I.card)) :=
  (s \ I.image b).image (coneQuotientLattice b I)

theorem faceCharacterProjection_mem_quotientDualCone
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (s : Finset (Lattice n))
    (m : orbitCharacterFace s (I.image b)) :
    faceCharacterProjection b I m.val.val ∈ dualConeMonoid (orbitQuotientCone b I s) := by
  intro v hv
  obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hv
  rw [← integerPairing_faceTangentLattice,
    faceTangentLattice_projection b I m.val.val m.property]
  exact m.val.property u (Finset.mem_sdiff.mp hu).1

theorem faceTangentLattice_mem_dualCone
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (s : Finset (Lattice n)) (z : dualConeMonoid (orbitQuotientCone b I s)) :
    faceTangentLattice b I z.val ∈ dualConeMonoid s := by
  intro u hu
  by_cases huI : u∈I.image b
  · rw [faceTangentLattice_annihilates b I z.val u huI]
  · rw [integerPairing_faceTangentLattice]
    exact z.property _ (Finset.mem_image.mpr
      ⟨u,Finset.mem_sdiff.mpr ⟨hu,huI⟩,rfl⟩)

/-- The actual saturated semigroup equivalence. It uses no fan
classification, geometry, or positivity hypothesis beyond the semigroups. -/
def orbitQuotientSemigroupEquiv
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (s : Finset (Lattice n)) :
    orbitCharacterFace s (I.image b) ≃+ dualConeMonoid (orbitQuotientCone b I s) where
  toFun m := ⟨faceCharacterProjection b I m.val.val,
    faceCharacterProjection_mem_quotientDualCone b I s m⟩
  invFun z := ⟨⟨faceTangentLattice b I z.val,faceTangentLattice_mem_dualCone b I s z⟩,
    faceTangentLattice_annihilates b I z.val⟩
  left_inv m := by
    apply Subtype.ext
    apply Subtype.ext
    exact faceTangentLattice_projection b I m.val.val m.property
  right_inv z := Subtype.ext (faceCharacterProjection_tangent b I z.val)
  map_add' m p := Subtype.ext ((faceCharacterProjection b I).map_add m.val.val p.val.val)

variable (k : Type*) [CommRing k]

def orbitQuotientAlgebraMap
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (s : Finset (Lattice n)) (hIs : I.image b⊆s) :
    monoidChartAlgebra k (dualConeMonoid s) →ₐ[k]
      monoidChartAlgebra k (dualConeMonoid (orbitQuotientCone b I s)) :=
  (monoidChartAlgebraEquiv k _).toAlgHom.comp
    ((AddMonoidAlgebra.domCongr k k (orbitQuotientSemigroupEquiv b I s)).toAlgHom.comp
      ((additiveFaceRetraction k (orbitCharacterFace s (I.image b))
        (orbitCharacterFace_isAdditiveFace s (I.image b) hIs)).comp
          (monoidChartAlgebraEquiv k (dualConeMonoid s)).symm.toAlgHom))

theorem orbitQuotientAlgebraMap_surjective
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (s : Finset (Lattice n)) (hIs : I.image b⊆s) :
    Function.Surjective (orbitQuotientAlgebraMap k b I s hIs) :=
  (monoidChartAlgebraEquiv k _).surjective.comp
    ((AddMonoidAlgebra.domCongr k k (orbitQuotientSemigroupEquiv b I s)).surjective.comp
      ((additiveFaceRetraction_surjective k (orbitCharacterFace s (I.image b))
        (orbitCharacterFace_isAdditiveFace s (I.image b) hIs)).comp
          (monoidChartAlgebraEquiv k (dualConeMonoid s)).symm.surjective))

theorem orbitQuotientChartMap_isClosedImmersion
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (s : Finset (Lattice n)) (hIs : I.image b⊆s) :
    IsClosedImmersion (Spec.map (CommRingCat.ofHom
      (orbitQuotientAlgebraMap k b I s hIs).toRingHom)) :=
  IsClosedImmersion.spec_of_surjective _ (orbitQuotientAlgebraMap_surjective k b I s hIs)

end PaperVerification.ToricGeometry

#print axioms PaperVerification.ToricGeometry.orbitQuotientSemigroupEquiv
#print axioms PaperVerification.ToricGeometry.orbitQuotientChartMap_isClosedImmersion
