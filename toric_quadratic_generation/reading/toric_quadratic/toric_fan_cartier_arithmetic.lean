module

public import PaperVerification.ToricFanSectionCoordinates
public import PaperVerification.ToricCartierAmpleDescent

@[expose] public section

/-! # Addition of integral coefficients and actual Cartier sheaf products -/

noncomputable section

universe u

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open AlgebraicGeometry CategoryTheory
open PaperVerification.ToricCharacters PaperVerification.ToricSchemes
open scoped Classical Pointwise

variable {n : ℕ} («Σ» : SmoothCompleteFan n) (k : Type u) [Field k]

theorem cartierLatticePoint_add_coefficients (a b : Lattice n→ℤ) (s : «Σ».fullCones) :
    «Σ».cartierLatticePoint (a+b) s=«Σ».cartierLatticePoint a s+«Σ».cartierLatticePoint b s := by
  symm
  apply «Σ».eq_cartierLatticePoint_of_pairings
  intro v hv
  rw [integerPairing_add,«Σ».cartierLatticePoint_pairing a s v hv,
    «Σ».cartierLatticePoint_pairing b s v hv]
  simp only [Pi.add_apply]
  omega

theorem fanIntegralExponents_add_subset (a b : Lattice n→ℤ) :
    «Σ».fanIntegralExponents a+«Σ».fanIntegralExponents b ⊆ «Σ».fanIntegralExponents (a+b) := by
  rintro m ⟨p,hp,q,hq,rfl⟩ v hv
  have hpv := hp v hv
  have hqv := hq v hv
  change -((a v+b v : ℤ):ℝ) ≤
    (dotProductEquiv ℝ (Fin n) (embed n v)) (embed n (p+q))
  rw [map_add,LinearMap.map_add,Int.cast_add]
  linarith

theorem fanCartierCocycle_mul_ratios (hpure : «Σ».IsPure) (a b : Lattice n→ℤ) :
    ((«Σ».fanCartierCocycle k hpure a).mul («Σ».fanCartierCocycle k hpure b)).GeneratorRatioRegular
      («Σ».fanCartierCocycle k hpure (a+b)) ∧
    («Σ».fanCartierCocycle k hpure (a+b)).GeneratorRatioRegular
      ((«Σ».fanCartierCocycle k hpure a).mul («Σ».fanCartierCocycle k hpure b)) := by
  constructor
  · intro i j x hxi hxj
    have ha := («Σ».fanCartierCocycle k hpure a).transition i.1 j x hxi.1 hxj
    have hb := («Σ».fanCartierCocycle k hpure b).transition i.2 j x hxi.2 hxj
    have h := (regularAtSubring («Σ».fanScheme k) x).mul_mem ha hb
    simpa only [RationalCartierCocycle.mul,fanCartierCocycle,Units.val_mul,
      «Σ».cartierLatticePoint_add_coefficients,«Σ».rationalCharacter_add k,
      div_mul_div_comm] using h
  · intro i j x hxi hxj
    have ha := («Σ».fanCartierCocycle k hpure a).transition i j.1 x hxi hxj.1
    have hb := («Σ».fanCartierCocycle k hpure b).transition i j.2 x hxi hxj.2
    have h := (regularAtSubring («Σ».fanScheme k) x).mul_mem ha hb
    simpa only [RationalCartierCocycle.mul,fanCartierCocycle,Units.val_mul,
      «Σ».cartierLatticePoint_add_coefficients,«Σ».rationalCharacter_add k,
      div_mul_div_comm] using h

/-- The true product Cartier sheaf is the sheaf of the sum of integral
support coefficients, with the same actual rational-function embedding. -/
theorem fanCartierData_add_equivalent (hpure : «Σ».IsPure) (a b : Lattice n→ℤ) :
    ((«Σ».fanCartierData k hpure a).add («Σ».fanCartierData k hpure b)).Equivalent
      («Σ».fanCartierData k hpure (a+b)) := by
  let C := «Σ».fanCartierCocycle k hpure a
  let D := «Σ».fanCartierCocycle k hpure b
  have h := (C.mul D).equivalent_of_generatorRatios
    («Σ».fanCartierCocycle k hpure (a+b))
    («Σ».fanCartierCocycle_mul_ratios k hpure a b).1
    («Σ».fanCartierCocycle_mul_ratios k hpure a b).2
  exact (C.toCartierData.add D.toCartierData).equivalent_trans
    (C.mul D).toCartierData («Σ».fanCartierData k hpure (a+b))
    (C.toCartierData_add_equivalent D) h

open scoped BaseSections

theorem fanCartierSum_globalSectionValue_range (hpure : «Σ».IsPure) (a b : Lattice n→ℤ) :
    (((«Σ».fanCartierData k hpure a).add («Σ».fanCartierData k hpure b)).globalSectionValue k).range =
      («Σ».fanCharacterValue k (a+b)).range := by
  let F := («Σ».fanCartierData k hpure a).add («Σ».fanCartierData k hpure b)
  have h := F.equivalent_sectionValueRange («Σ».fanCartierData k hpure (a+b))
    («Σ».fanCartierData_add_equivalent k hpure a b) ⊤
  have he : (F.globalSectionValue k).range =
      ((«Σ».fanCartierData k hpure (a+b)).globalSectionValue k).range := by
    apply SetLike.coe_injective
    change Set.range (F.sectionValue ⊤) =
      Set.range ((«Σ».fanCartierData k hpure (a+b)).sectionValue ⊤)
    exact congrArg (fun P : Submodule Γ(«Σ».fanScheme k, ⊤) («Σ».fanScheme k).functionField =>
      (P : Set («Σ».fanScheme k).functionField)) h
  exact he.trans («Σ».fanCartier_globalSectionValue_range k hpure (a+b))

/-- Character coordinates on the actual product sheaf, without replacing
its tensor/product construction by a formal support-set definition. -/
def fanCartierSumSectionCoordinates (hpure : «Σ».IsPure) (a b : Lattice n→ℤ) :
    Γ(((«Σ».fanCartierData k hpure a).add («Σ».fanCartierData k hpure b)).sheaf,⊤) ≃ₗ[k]
      characterModule k («Σ».fanIntegralExponents (a+b)) :=
  (LinearEquiv.ofInjective
    (((«Σ».fanCartierData k hpure a).add («Σ».fanCartierData k hpure b)).globalSectionValue k)
    (((«Σ».fanCartierData k hpure a).add («Σ».fanCartierData k hpure b)).globalSectionValue_injective k)).trans
    ((LinearEquiv.ofEq _ _ («Σ».fanCartierSum_globalSectionValue_range k hpure a b)).trans
      (LinearEquiv.ofInjective («Σ».fanCharacterValue k (a+b))
        («Σ».fanCharacterValue_injective k (a+b))).symm)

theorem fanCartierSumSectionCoordinates_value (hpure : «Σ».IsPure) (a b : Lattice n→ℤ)
    (s : Γ(((«Σ».fanCartierData k hpure a).add («Σ».fanCartierData k hpure b)).sheaf,⊤)) :
    «Σ».torusRationalMap k («Σ».fanCartierSumSectionCoordinates k hpure a b s).val =
      ((«Σ».fanCartierData k hpure a).add («Σ».fanCartierData k hpure b)).globalSectionValue k s := by
  change «Σ».fanCharacterValue k (a+b) («Σ».fanCartierSumSectionCoordinates k hpure a b s)=_
  simp only [fanCartierSumSectionCoordinates,LinearEquiv.trans_apply,
    LinearEquiv.ofInjective_symm_apply,LinearEquiv.coe_ofEq_apply,
    LinearEquiv.ofInjective_apply]

end PaperVerification.ToricGeometry.SmoothCompleteFan

#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.fanCartierData_add_equivalent
#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.fanCartierSumSectionCoordinates
