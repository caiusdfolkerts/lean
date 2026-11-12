module

public import ToricPower.RestrictedFanIncidence
public import ToricPower.CechWitnessReindex
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Category.Grp.Abelian

/-! # Character-complex comparison for a subspace and its ray span

Both sides use all characters of their actual saturated lattices and the
literal ray incidence on their actual finite affine chart covers. They are
compared with a common incidence complex through genuine complex
isomorphisms, including every differential.
-/

@[expose] public noncomputable section
open CategoryTheory TauCeti.Toric
open scoped Classical

namespace ToricPower
open NegativeSupportCech

variable (𝕜 : Type) [Field 𝕜]
variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V}

def retainedProfileComplex (fan : Fan i) (W : Submodule ℝ V)
    (b : fan.Ray → ℤ) (p : retainedFanRays fan W → ℤ) :=
  relativeComplex 𝕜 (retainedRayIncidence fan W) (fun ρ => b ρ.val + p ρ < 0)

def restrictedWeightComplex (fan : Fan i) (W : Submodule ℝ V)
    (hW : IsRationalSubspace i W) (b : fan.Ray → ℤ)
    (m : latticeTrace i W →+ ℤ) :=
  relativeComplex 𝕜
    (fun (ρ : (restrictedFan fan W hW).Ray) j => ρ.toCone ≤ linearRayCoreFiniteCharts fan W hW j)
    (fun ρ => restrictedFanRayCoefficients fan W hW b ρ +
      m (fanRayPrimitiveGenerator (restrictedFan fan W hW) ρ) < 0)

def rayCoreWeightComplex (fan : Fan i) (W : Submodule ℝ V)
    (hW : IsRationalSubspace i W) (b : fan.Ray → ℤ)
    (m : latticeTrace i (linearRayCore fan W) →+ ℤ) :=
  relativeComplex 𝕜
    (fun (ρ : (rayCoreFan fan W).Ray) j => ρ.toCone ≤ rayCoreFanFiniteCharts fan W hW j)
    (fun ρ => restrictedFanRayCoefficients fan (linearRayCore fan W)
        (fanRaySpan_rational fan (fanRaysIn fan W)) b ρ +
      m (fanRayPrimitiveGenerator (rayCoreFan fan W) ρ) < 0)

/-- The larger lattice changes only the list of feasible common profiles. -/
def restrictedWeightProfileIso (fan : Fan i) (W : Submodule ℝ V)
    (hW : IsRationalSubspace i W) (b : fan.Ray → ℤ)
    (m : latticeTrace i W →+ ℤ) :
    restrictedWeightComplex 𝕜 fan W hW b m ≅
      retainedProfileComplex 𝕜 fan W b
        (fun ρ => m (retainedRayPrimitiveInSubspace fan W ρ)) :=
  relativeComplexIsoOfForbiddenIff 𝕜 _ _ _ _ (by
    intro degree tuple
    constructor
    · rintro ⟨ρ, bad, incident⟩
      refine ⟨restrictedFanRayEquiv fan W hW ρ, ?_, ?_⟩
      · change b (restrictedFanRayEquiv fan W hW ρ).val +
          m (fanRayPrimitiveGenerator (restrictedFan fan W hW) ρ) < 0 at bad
        simpa only [restricted_ray_value] using bad
      · intro j
        exact (restricted_ray_incidence fan W hW ρ (tuple j)).mp (incident j)
    · rintro ⟨ρ, bad, incident⟩
      let ray := (restrictedFanRayEquiv fan W hW).symm ρ
      refine ⟨ray, ?_, ?_⟩
      · change b (restrictedFanRayEquiv fan W hW ray).val +
          m (fanRayPrimitiveGenerator (restrictedFan fan W hW) ray) < 0
        rw [restricted_ray_value]
        simpa only [ray, Equiv.apply_symm_apply] using bad
      · intro j
        apply (restricted_ray_incidence fan W hW ray (tuple j)).mpr
        simpa only [ray, Equiv.apply_symm_apply] using incident j)

/-- The smaller lattice gives the same common complex for the same profile. -/
def rayCoreWeightProfileIso (fan : Fan i) (W : Submodule ℝ V)
    (hW : IsRationalSubspace i W) (b : fan.Ray → ℤ)
    (m : latticeTrace i (linearRayCore fan W) →+ ℤ) :
    rayCoreWeightComplex 𝕜 fan W hW b m ≅
      retainedProfileComplex 𝕜 fan W b
        (fun ρ => m (retainedRayPrimitiveInCore fan W ρ)) :=
  relativeComplexIsoOfForbiddenIff 𝕜 _ _ _ _ (by
    intro degree tuple
    constructor
    · rintro ⟨ρ, bad, incident⟩
      refine ⟨rayCoreFanRayEquiv fan W ρ, ?_, ?_⟩
      · change b (rayCoreFanRayEquiv fan W ρ).val +
          m (fanRayPrimitiveGenerator (rayCoreFan fan W) ρ) < 0 at bad
        simpa only [rayCore_ray_value] using bad
      · intro j
        exact (rayCore_ray_incidence fan W hW ρ (tuple j)).mp (incident j)
    · rintro ⟨ρ, bad, incident⟩
      let ray := (rayCoreFanRayEquiv fan W).symm ρ
      refine ⟨ray, ?_, ?_⟩
      · change b (rayCoreFanRayEquiv fan W ray).val +
          m (fanRayPrimitiveGenerator (rayCoreFan fan W) ray) < 0
        rw [rayCore_ray_value]
        simpa only [ray, Equiv.apply_symm_apply] using bad
      · intro j
        apply (rayCore_ray_incidence fan W hW ray (tuple j)).mpr
        simpa only [ray, Equiv.apply_symm_apply] using incident j)

/-- Exact all-character, all-degree nonvanishing equivalence. -/
theorem restrictedWeightHomology_nonzero_iff_rayCore (fan : Fan i)
    (W : Submodule ℝ V) (hW : IsRationalSubspace i W) (b : fan.Ray → ℤ) :
    (∃ m : latticeTrace i W →+ ℤ, ∃ q : ℕ,
      Nontrivial ((restrictedWeightComplex 𝕜 fan W hW b m).homology q)) ↔
    (∃ m : latticeTrace i (linearRayCore fan W) →+ ℤ, ∃ q : ℕ,
      Nontrivial ((rayCoreWeightComplex 𝕜 fan W hW b m).homology q)) := by
  have hlarge : (∃ m : latticeTrace i W →+ ℤ, ∃ q : ℕ,
      Nontrivial ((restrictedWeightComplex 𝕜 fan W hW b m).homology q)) ↔
      (∃ m : latticeTrace i W →+ ℤ, ∃ q : ℕ,
      Nontrivial ((retainedProfileComplex 𝕜 fan W b
        (fun ρ => m (retainedRayPrimitiveInSubspace fan W ρ))).homology q)) := by
    apply exists_congr
    intro m
    apply exists_congr
    intro q
    let e := (HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.up ℕ) q).mapIso
      (restrictedWeightProfileIso 𝕜 fan W hW b m)
    exact e.addCommGroupIsoToAddEquiv.toEquiv.nontrivial_congr
  have hsmall : (∃ m : latticeTrace i (linearRayCore fan W) →+ ℤ, ∃ q : ℕ,
      Nontrivial ((rayCoreWeightComplex 𝕜 fan W hW b m).homology q)) ↔
      (∃ m : latticeTrace i (linearRayCore fan W) →+ ℤ, ∃ q : ℕ,
      Nontrivial ((retainedProfileComplex 𝕜 fan W b
        (fun ρ => m (retainedRayPrimitiveInCore fan W ρ))).homology q)) := by
    apply exists_congr
    intro m
    apply exists_congr
    intro q
    let e := (HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.up ℕ) q).mapIso
      (rayCoreWeightProfileIso 𝕜 fan W hW b m)
    exact e.addCommGroupIsoToAddEquiv.toEquiv.nontrivial_congr
  refine hlarge.trans (Iff.trans ?_ hsmall.symm)
  exact latticeTrace_exists_characterProfile_iff fan.lattice (linearRayCore_le fan W)
    (fun ρ : retainedFanRays fan W => fanRayPrimitiveGenerator fan ρ.val)
    (fun ρ => (retainedRayPrimitiveInCore fan W ρ).property)
    (fun p => ∃ q : ℕ, Nontrivial ((retainedProfileComplex 𝕜 fan W b p).homology q))

end ToricPower
