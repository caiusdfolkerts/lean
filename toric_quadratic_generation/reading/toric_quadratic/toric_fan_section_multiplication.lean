module

public import PaperVerification.ToricFanCartierArithmetic

@[expose] public section

/-!
# Actual section multiplication is the character multiplication map

Both sides are maps between the actual base-field tensor products. The
identity is proved after embedding in the scheme's genuine function
field, where multiplication is literal multiplication. Its surjectivity
is consequently equivalent to the complete lattice-point sum assertion.
-/

noncomputable section

universe u

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open AlgebraicGeometry CategoryTheory
open PaperVerification.ToricCharacters PaperVerification.ToricSchemes
open scoped Classical Pointwise TensorProduct BaseSections

variable {n : ℕ} («Σ» : SmoothCompleteFan n) (k : Type u) [Field k]

theorem fanSectionMultiplication_coordinates (hpure : «Σ».IsPure) (a b : Lattice n→ℤ) :
    («Σ».fanCartierSumSectionCoordinates k hpure a b).toLinearMap.comp
      ((«Σ».fanCartierData k hpure a).sectionMultiplicationOver k
        («Σ».fanCartierData k hpure b)) =
      (characterMultiplication k («Σ».fanIntegralExponents a) («Σ».fanIntegralExponents b)
        («Σ».fanIntegralExponents (a+b)) («Σ».fanIntegralExponents_add_subset a b)).comp
          (TensorProduct.map
            («Σ».fanCartierSectionCoordinates k hpure a).toLinearMap
            («Σ».fanCartierSectionCoordinates k hpure b).toLinearMap) := by
  apply TensorProduct.ext'
  intro s t
  apply Subtype.ext
  apply «Σ».torusRationalMap_injective k
  change «Σ».torusRationalMap k
      («Σ».fanCartierSumSectionCoordinates k hpure a b
        ((«Σ».fanCartierData k hpure a).sectionMultiplicationOver k
          («Σ».fanCartierData k hpure b) (s ⊗ₜ[k] t))).val =
    «Σ».torusRationalMap k
      ((«Σ».fanCartierSectionCoordinates k hpure a s).val *
        («Σ».fanCartierSectionCoordinates k hpure b t).val)
  rw [«Σ».fanCartierSumSectionCoordinates_value,
    CartierData.sectionMultiplicationOver_value_tmul,map_mul,
    «Σ».fanCartierSectionCoordinates_value,«Σ».fanCartierSectionCoordinates_value]

theorem fanSectionMultiplication_surjective_iff_characters (hpure : «Σ».IsPure)
    (a b : Lattice n→ℤ) :
    Function.Surjective ((«Σ».fanCartierData k hpure a).sectionMultiplicationOver k
      («Σ».fanCartierData k hpure b)) ↔
    Function.Surjective
      (characterMultiplication k («Σ».fanIntegralExponents a) («Σ».fanIntegralExponents b)
        («Σ».fanIntegralExponents (a+b)) («Σ».fanIntegralExponents_add_subset a b)) := by
  let ea := «Σ».fanCartierSectionCoordinates k hpure a
  let eb := «Σ».fanCartierSectionCoordinates k hpure b
  let ec := «Σ».fanCartierSumSectionCoordinates k hpure a b
  let et := TensorProduct.congr ea eb
  let μ := («Σ».fanCartierData k hpure a).sectionMultiplicationOver k
    («Σ».fanCartierData k hpure b)
  let ν := characterMultiplication k («Σ».fanIntegralExponents a) («Σ».fanIntegralExponents b)
    («Σ».fanIntegralExponents (a+b)) («Σ».fanIntegralExponents_add_subset a b)
  have hcomp (x) : ec (μ x)=ν (et x) :=
    congrArg (fun f=>f x) («Σ».fanSectionMultiplication_coordinates k hpure a b)
  constructor
  · intro hμ y
    obtain ⟨s,hs⟩ := ec.surjective y
    obtain ⟨x,hx⟩ := hμ s
    exact ⟨et x,(hcomp x).symm.trans (by rw [hx,hs])⟩
  · intro hν s
    obtain ⟨y,hy⟩ := hν (ec s)
    obtain ⟨x,hx⟩ := et.surjective y
    refine ⟨x,ec.injective ?_⟩
    rw [hcomp x,hx,hy]

/-- The exact scheme-section dictionary required for multiplication:
surjectivity of the actual global-section tensor map is equivalent to
decomposition of every integral point in the whole sum-support polytope. -/
theorem fanSectionMultiplication_surjective_iff (hpure : «Σ».IsPure) (a b : Lattice n→ℤ) :
    Function.Surjective ((«Σ».fanCartierData k hpure a).sectionMultiplicationOver k
      («Σ».fanCartierData k hpure b)) ↔
      «Σ».fanIntegralExponents (a+b) =
        «Σ».fanIntegralExponents a + «Σ».fanIntegralExponents b := by
  rw [«Σ».fanSectionMultiplication_surjective_iff_characters k hpure a b,
    characterMultiplication_surjective_iff]

end PaperVerification.ToricGeometry.SmoothCompleteFan

#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.fanSectionMultiplication_coordinates
#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.fanSectionMultiplication_surjective_iff
