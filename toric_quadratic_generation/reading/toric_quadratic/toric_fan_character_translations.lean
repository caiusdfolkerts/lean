module

public import PaperVerification.ToricFanCartierArithmetic
public import PaperVerification.ToricCartierScaleCocycle

@[expose] public section

/-!
# Character translations of actual fan Cartier sheaves

Changing ray coefficients by the pairing with one integral character
translates every genuine local Cartier point by that character. The
resulting actual sheaf isomorphism is multiplication by the rational
character. Thus the customary lattice translations are proved principal
translations of the actual invertible sheaves.
-/

noncomputable section

universe u

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open AlgebraicGeometry CategoryTheory
open PaperVerification.ToricCharacters PaperVerification.ToricSchemes
open scoped Classical

variable {n : ℕ} («Σ» : SmoothCompleteFan n) (k : Type u) [Field k]
    (hpure : «Σ».IsPure)

theorem cartierLatticePoint_characterTranslation
    (a b : Lattice n → ℤ) (m : Lattice n)
    (h : ∀ v ∈ «Σ».rays,b v=a v-integerPairing v m) (s : «Σ».fullCones) :
    «Σ».cartierLatticePoint b s=«Σ».cartierLatticePoint a s+m := by
  symm
  apply «Σ».eq_cartierLatticePoint_of_pairings
  intro v hv
  rw [integerPairing_add,«Σ».cartierLatticePoint_pairing a s v hv,
    h v («Σ».ray_mem_of_mem_cone («Σ».fullCones_mem s) hv)]
  omega

/-- The character translate is a principal change of the actual
fractional presentation, with an actual isomorphism of its sheaf. -/
theorem fanCartierData_characterTranslation
    (a b : Lattice n → ℤ) (m : Lattice n)
    (h : ∀ v ∈ «Σ».rays,b v=a v-integerPairing v m) :
    («Σ».fanCartierData k hpure a).LinearlyEquivalent
      («Σ».fanCartierData k hpure b) := by
  let C := «Σ».fanCartierCocycle k hpure a
  let E := «Σ».fanCartierCocycle k hpure b
  let q := «Σ».rationalCharacter k m
  have he (i : C.index) : (C.scale q).generator i=E.generator i := by
    change «Σ».rationalCharacter k m *
        «Σ».rationalCharacter k («Σ».cartierLatticePoint a i.down) =
      «Σ».rationalCharacter k («Σ».cartierLatticePoint b i.down)
    rw [«Σ».cartierLatticePoint_characterTranslation a b m h,
      «Σ».rationalCharacter_add k]
    exact mul_comm _ _
  have hCE : (C.scale q).toCartierData.Equivalent E.toCartierData := by
    apply (C.scale q).equivalent_of_generatorRatios E
    · intro i j x hi hj
      rw [he i]
      exact E.transition i j x hi hj
    · intro i j x hi hj
      rw [he j]
      exact E.transition i j x hi hj
  exact ⟨C.scaleSheafIso q ≪≫ hCE.choose⟩

/-- The corresponding polytope is the literal integral translation of
the original halfspace intersection, even without positivity. -/
theorem fanPolytope_characterTranslation
    (a b : Lattice n → ℤ) (m : Lattice n)
    (h : ∀ v ∈ «Σ».rays,b v=a v-integerPairing v m) :
    «Σ».fanPolytope (fun v => (b v : ℝ)) =
      (fun x : Ambient n => x+embed n m) '' «Σ».fanPolytope (fun v => (a v : ℝ)) := by
  ext x
  constructor
  · intro hx
    refine ⟨x-embed n m,?_,sub_add_cancel _ _⟩
    intro v hv
    have hvx := hx v hv
    change -(b v : ℝ) ≤ _ at hvx
    rw [h v hv,Int.cast_sub] at hvx
    rw [map_sub,normalRay_pairing_lattice]
    change -((a v : ℝ)-(integerPairing v m : ℝ)) ≤ _ at hvx
    change -(a v : ℝ) ≤ _
    change -(a v : ℝ) ≤ _-(integerPairing v m : ℝ)
    linarith
  · rintro ⟨y,hy,rfl⟩ v hv
    have hvy := hy v hv
    change -(b v : ℝ) ≤ _
    rw [h v hv,Int.cast_sub,map_add,normalRay_pairing_lattice]
    change -((a v : ℝ)-(integerPairing v m : ℝ)) ≤ _+(integerPairing v m : ℝ)
    linarith

end PaperVerification.ToricGeometry.SmoothCompleteFan

#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.fanCartierData_characterTranslation
