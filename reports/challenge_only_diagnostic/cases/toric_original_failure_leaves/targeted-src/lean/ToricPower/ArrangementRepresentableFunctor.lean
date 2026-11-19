module

public import ToricPower.ArrangementRepresentableMaps
public import ToricPower.ArrangementCostalkCochainRepresentation

/-!
# The representable costalk comparison on actual morphisms

The chain map of a weighted incidence restricts coefficients along genuine
incidence composition. Its scalar dual extends coefficients along the same
injective index map. These are equalities of the actual cellular maps, not
new actions imposed on the previously computed homology groups.

The construction retains every integral weight. Only an individual open
costalk has finitely many cells, as proved independently from its geometry.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Topology Set
open scoped Classical

namespace ToricPower

variable (𝕜 : Type) [Field 𝕜]

/-- The transpose of restriction along an injective basis map is the
literal extension by zero along that map. -/
theorem finiteFreeScalarDualEquiv_comapDomain
    {I J : Type} [Finite I] [Finite J] (f : I → J) (injective : Function.Injective f)
    (φ : ModuleCat.of 𝕜 (I →₀ 𝕜) ⟶ ModuleCat.of 𝕜 𝕜) :
    finiteFreeScalarDualEquiv 𝕜 J
        (ModuleCat.ofHom (Finsupp.lcomapDomain (R := 𝕜) (M := 𝕜) f injective) ≫ φ) =
      Finsupp.mapDomain f (finiteFreeScalarDualEquiv 𝕜 I φ) := by
  ext j
  change φ (Finsupp.comapDomain f (Finsupp.single j 1) injective.injOn) = _
  by_cases inside : j ∈ Set.range f
  · obtain ⟨i, rfl⟩ := inside
    rw [Finsupp.comapDomain_single, Finsupp.mapDomain_apply_of_injective injective]
    rfl
  · rw [Finsupp.comapDomain_single_of_notMem_range inside, map_zero,
      Finsupp.mapDomain_of_notMem_range _ _ inside]

namespace IntegralArrangement

variable {n s : ℕ} (matrix : Fin s → Fin n → ℤ) (S : Set (Fin s))
  {c d : WeightedIncidenceObject matrix} (f : c ⟶ d)
  (R : Type) [Ring R]

local instance representableFunctorPeriodicCW : CWComplex (arrangementCarrier matrix) :=
  periodicArrangementCWComplex matrix

/-- The independently specified linear map restricts the source
coefficient function to actual composite incidences. -/
def representableCostalkRestrictionLinear (q : ℕ) :
    (RepresentableCostalkIndex matrix c.1 S c.2 q →₀ R) →ₗ[R]
      (RepresentableCostalkIndex matrix d.1 S d.2 q →₀ R) :=
  Finsupp.lcomapDomain (representableCostalkPrecompose matrix S f q)
    (representableCostalkPrecompose_injective matrix S f q)

@[simp]
theorem representableCostalkRestrictionLinear_apply (q : ℕ)
    (v : RepresentableCostalkIndex matrix c.1 S c.2 q →₀ R)
    (j : RepresentableCostalkIndex matrix d.1 S d.2 q) :
    representableCostalkRestrictionLinear matrix S f R q v j =
      v (representableCostalkPrecompose matrix S f q j) := rfl

/-- The actual map on skeletal relative homology is restriction of
the genuine characteristic-disk coefficients. -/
theorem weightedCostalkChainGroupMap_representable_coordinates (q : ℕ) :
    (representableCostalkBasis matrix d.1 S d.2 R q).repr.toLinearMap.comp
        (TauCeti.cellularChainGroupMap
          (relativeCWCarrier (weightedCostalkComplement matrix (Sum.inl '' S) c))
          (relativeCWCarrier (weightedCostalkComplement matrix (Sum.inl '' S) d))
          (relativeCWMap_cellular
            (weightedCostalkComplement matrix (Sum.inl '' S) c)
            (weightedCostalkComplement matrix (Sum.inl '' S) d)
            (arrangementTranslation matrix f.val.val)
            (arrangementTranslation_cellular matrix f.val.val)
            (weightedCostalk_base matrix (Sum.inl '' S) f))
          (ModuleCat.of R R) q).hom =
      (representableCostalkRestrictionLinear matrix S f R q).comp
        (representableCostalkBasis matrix c.1 S c.2 R q).repr.toLinearMap := by
  apply (representableCostalkBasis matrix c.1 S c.2 R q).ext
  intro i
  ext j
  change (representableCostalkBasis matrix d.1 S d.2 R q).repr
      (TauCeti.cellularChainGroupMap _ _ _ (ModuleCat.of R R) q
        (representableCostalkBasis matrix c.1 S c.2 R q i)) j =
    representableCostalkRestrictionLinear matrix S f R q
      ((representableCostalkBasis matrix c.1 S c.2 R q).repr
        (representableCostalkBasis matrix c.1 S c.2 R q i)) j
  refine (weightedCostalkChainGroupMap_representable_coefficient
    matrix S f R q i j).trans ?_
  rw [Module.Basis.repr_self, representableCostalkRestrictionLinear_apply]
  simp only [Finsupp.single_apply, eq_comm]

/-- The same coefficient equality on the actual chain complexes retains
the canonical transports from the skeletal homology construction. -/
theorem weightedCostalkChainMap_representable_coordinates (q : ℕ)
    (v : (weightedCostalkComplex matrix (Sum.inl '' S) (ModuleCat.of R R) c).X q) :
    representableCostalkChainCoordinates matrix d.1 S d.2 R q
        ((weightedCostalkChainMap matrix (Sum.inl '' S) (ModuleCat.of R R) f).f q v) =
      representableCostalkRestrictionLinear matrix S f R q
        (representableCostalkChainCoordinates matrix c.1 S c.2 R q v) := by
  let C := relativeCWCarrier (weightedCostalkComplement matrix (Sum.inl '' S) c)
  let D := relativeCWCarrier (weightedCostalkComplement matrix (Sum.inl '' S) d)
  let hf := relativeCWMap_cellular
    (weightedCostalkComplement matrix (Sum.inl '' S) c)
    (weightedCostalkComplement matrix (Sum.inl '' S) d)
    (arrangementTranslation matrix f.val.val)
    (arrangementTranslation_cellular matrix f.val.val)
    (weightedCostalk_base matrix (Sum.inl '' S) f)
  have square :
      (weightedCostalkChainMap matrix (Sum.inl '' S) (ModuleCat.of R R) f).f q ≫
          eqToHom (TauCeti.cellularChainComplex_X D (ModuleCat.of R R) q) =
        eqToHom (TauCeti.cellularChainComplex_X C (ModuleCat.of R R) q) ≫
          TauCeti.cellularChainGroupMap C D hf (ModuleCat.of R R) q := by
    change (TauCeti.cellularChainComplexMap C D hf (ModuleCat.of R R)).f q ≫ _ = _
    rw [TauCeti.cellularChainComplexMap_f]
    simp
  have first := congrArg (representableCostalkBasis matrix d.1 S d.2 R q).repr
    (ConcreteCategory.congr_hom square v)
  have second := DFunLike.congr_fun
    (weightedCostalkChainGroupMap_representable_coordinates matrix S f R q)
    (eqToHom (TauCeti.cellularChainComplex_X C (ModuleCat.of R R) q) v)
  exact first.trans second

/-- Conjugation by the actual characteristic-basis isomorphisms gives
the genuine map between the displayed finite matrix complexes. -/
def representableCostalkChainMap :
    representableCostalkChainComplex matrix c.1 S c.2 R ⟶
      representableCostalkChainComplex matrix d.1 S d.2 R :=
  (representableCostalkChainIso matrix c.1 S c.2 R).inv ≫
    weightedCostalkChainMap matrix (Sum.inl '' S) (ModuleCat.of R R) f ≫
      (representableCostalkChainIso matrix d.1 S d.2 R).hom

/-- Every component of the actual finite-matrix chain map is the
independently specified restriction along literal incidence composition. -/
theorem representableCostalkChainMap_f (q : ℕ) :
    (representableCostalkChainMap matrix S f R).f q =
      ModuleCat.ofHom (representableCostalkRestrictionLinear matrix S f R q) := by
  apply ModuleCat.hom_ext
  ext v
  change representableCostalkChainCoordinates matrix d.1 S d.2 R q
      ((weightedCostalkChainMap matrix (Sum.inl '' S) (ModuleCat.of R R) f).f q
        ((representableCostalkChainCoordinates matrix c.1 S c.2 R q).symm v)) = _
  rw [weightedCostalkChainMap_representable_coordinates, LinearEquiv.apply_symm_apply]
  rfl

/-- The representable matrices form an actual functor on the full
weighted incidence category, with every character retained. -/
def representableCostalkChainFunctor :
    WeightedIncidenceObject matrix ⥤ ChainComplex (ModuleCat.{0} R) ℕ where
  obj c := representableCostalkChainComplex matrix c.1 S c.2 R
  map f := representableCostalkChainMap matrix S f R
  map_id c := by
    simp only [representableCostalkChainMap, weightedCostalkChainMap_id]
    let e := representableCostalkChainIso matrix c.1 S c.2 R
    exact (congrArg (fun t => e.inv ≫ t) (Category.id_comp e.hom)).trans e.inv_hom_id
  map_comp f g := by
    simp only [representableCostalkChainMap, weightedCostalkChainMap_comp,
      Category.assoc, Iso.hom_inv_id_assoc]

/-- The objectwise geometric comparison is natural for the actual
incidence maps before passing to homology. -/
def representableCostalkChainNatIso :
    weightedCostalkChainFunctor matrix (Sum.inl '' S) (ModuleCat.of R R) ≅
      representableCostalkChainFunctor matrix S R :=
  NatIso.ofComponents (fun c => representableCostalkChainIso matrix c.1 S c.2 R)
    (by
      intro c d f
      simp only [representableCostalkChainFunctor, weightedCostalkChainFunctor,
        representableCostalkChainMap, Iso.hom_inv_id_assoc])

/-- The scalar-dual chain map is the actual representable cochain map. -/
def representableCostalkCochainMap :
    representableCostalkCochainComplex 𝕜 matrix d.1 S d.2 ⟶
      representableCostalkCochainComplex 𝕜 matrix c.1 S c.2 :=
  scalarDualMap 𝕜 (representableCostalkChainMap matrix S f 𝕜)

/-- The cochain comparison is literal extension by zero along actual
incidence composition in every degree and at every full character. -/
theorem representableCostalkCochainMap_coordinates (q : ℕ)
    (φ : (representableCostalkCochainComplex 𝕜 matrix d.1 S d.2).X q) :
    representableCostalkCochainCoordinates 𝕜 matrix c.1 S c.2 q
        ((representableCostalkCochainMap 𝕜 matrix S f).f q φ) =
      Finsupp.mapDomain (representableCostalkPrecompose matrix S f q)
        (representableCostalkCochainCoordinates 𝕜 matrix d.1 S d.2 q φ) := by
  change finiteFreeScalarDualEquiv 𝕜 _
    ((representableCostalkChainMap matrix S f 𝕜).f q ≫ φ) = _
  rw [representableCostalkChainMap_f]
  exact finiteFreeScalarDualEquiv_comapDomain 𝕜
    (representableCostalkPrecompose matrix S f q)
    (representableCostalkPrecompose_injective matrix S f q) φ

end IntegralArrangement
end ToricPower
