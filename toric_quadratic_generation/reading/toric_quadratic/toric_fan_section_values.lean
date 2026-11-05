module

public import PaperVerification.ToricFanCartierCocycle
public import PaperVerification.ToricCartierCharacterModules
public import PaperVerification.ToricCartierBaseSections

@[expose] public section

/-!
# Actual global Cartier sections and Laurent characters

This file connects the actual invertible sheaf on the glued scheme with
the already computed algebraic intersection of character modules. The
bridge is proved using regularity in the actual local rings, the actual
affine chart section isomorphisms, and injectivity in the function field.
It does not take a global-section dictionary as a hypothesis.
-/

noncomputable section

universe u

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open PaperVerification.ToricCharacters PaperVerification.ToricSchemes
open scoped Classical

variable {n : ℕ} («Σ» : SmoothCompleteFan n) (k : Type u) [Field k]

/-- A rational function is in the actual chart coordinate ring precisely
when it is regular at every point of the chart image. -/
theorem mem_chartRationalMap_range_iff (s : «Σ».ConeIndex)
    (r : («Σ».fanScheme k).functionField) :
    r ∈ Set.range («Σ».chartRationalMap k s) ↔
      ∀ x ∈ («Σ».fanChartMap k s).opensRange,
        r ∈ regularAtSubring («Σ».fanScheme k) x := by
  letI := «Σ».coneChart_isIntegral k s
  let j := «Σ».fanChartMap k s
  letI : Nonempty (j ''ᵁ (⊤ : (coneChart k s.val).Opens)) :=
    openImmersion_image_nonempty j ⊤
  constructor
  · rintro ⟨f,rfl⟩ x ⟨y,rfl⟩
    exact «Σ».chartRationalMap_mem_regularAt k s f y
  · intro hr
    obtain ⟨a,ha⟩ := exists_regularSection_of_stalkwise («Σ».fanScheme k)
      (j ''ᵁ ⊤) r (by
        simpa only [j.image_top_eq_opensRange] using hr)
    let R := CommRingCat.of (monoidChartAlgebra k (dualConeMonoid s.val))
    let b := (Scheme.ΓSpecIso R).hom ((j.appIso ⊤).hom a)
    refine ⟨b,?_⟩
    change openImmersionGlobalToFunctionField j ((Scheme.ΓSpecIso R).inv b)=r
    rw [show (Scheme.ΓSpecIso R).inv b=(j.appIso ⊤).hom a by
      exact (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv.left_inv _]
    rw [openImmersionRegularToFunctionField_eq_germ_image]
    simpa using ha

/-- Literal equality of regular character membership and dual-cone
membership. The assertion concerns the actual chart ring in K(X). -/
theorem rationalCharacter_mem_chartRange_iff (s : «Σ».ConeIndex) (m : Lattice n) :
    («Σ».rationalCharacter k m : («Σ».fanScheme k).functionField) ∈
      Set.range («Σ».chartRationalMap k s) ↔ m∈dualConeMonoid s.val := by
  constructor
  · rintro ⟨f,hf⟩
    have he : (f : AddMonoidAlgebra k (Lattice n))=AddMonoidAlgebra.single m 1 := by
      apply «Σ».torusRationalMap_injective k
      rw [← «Σ».chartRationalMap_eq_torusRationalMap k s f]
      exact hf
    have hmem := (mem_monoidChartAlgebra k (dualConeMonoid s.val) f.val).mp f.property
    exact hmem (by rw [he]; simp)
  · intro hm
    exact ⟨chartCharacter k (dualConeMonoid s.val) m hm,
      «Σ».chartRationalMap_character k s m hm⟩

/-- The principal Cartier condition on each chart is exactly the actual
global-section condition in the constructed fractional sheaf. -/
theorem mem_fanCartier_globalRange_iff (hpure : «Σ».IsPure) (a : Lattice n→ℤ)
    (r : («Σ».fanScheme k).functionField) :
    r ∈ Set.range ((«Σ».fanCartierData k hpure a).sectionValue ⊤) ↔
      ∀ s : «Σ».fullCones,
        r/(«Σ».rationalCharacter k («Σ».cartierLatticePoint a s) :
          («Σ».fanScheme k).functionField) ∈
          Set.range («Σ».chartRationalMap k («Σ».fullConeIndex s)) := by
  let C := «Σ».fanCartierCocycle k hpure a
  constructor
  · rintro ⟨t,rfl⟩ s
    apply («Σ».mem_chartRationalMap_range_iff k («Σ».fullConeIndex s) _).mpr
    intro x hx
    exact t.property (ULift.up s) ⟨x,trivial⟩ hx
  · intro hr
    let t : Γ(rationalFunctions («Σ».fanScheme k),⊤) :=
      (rationalValue («Σ».fanScheme k) ⊤).symm r
    have ht : C.IsSection ⊤ t := by
      intro i x hx
      have hs := («Σ».mem_chartRationalMap_range_iff k («Σ».fullConeIndex i.down) _).mp
        (hr i.down) x.val hx
      simpa only [C,fanCartierCocycle,rationalValueAt_eq,t,AddEquiv.apply_symm_apply]
        using hs
    refine ⟨⟨t,ht⟩,?_⟩
    change rationalValue («Σ».fanScheme k) ⊤ t=r
    exact (rationalValue («Σ».fanScheme k) ⊤).apply_symm_apply r

/-- On a single chart the rational principal-module condition is exactly
membership in the literal Laurent character module. -/
theorem torusRationalMap_mem_principal_chart_iff
    (a : Lattice n→ℤ) (s : «Σ».fullCones)
    (f : AddMonoidAlgebra k (Lattice n)) :
    «Σ».torusRationalMap k f /
      («Σ».rationalCharacter k («Σ».cartierLatticePoint a s) :
        («Σ».fanScheme k).functionField) ∈
        Set.range («Σ».chartRationalMap k («Σ».fullConeIndex s)) ↔
      f ∈ «Σ».cartierChartCharacterModule k a s := by
  let m := «Σ».cartierLatticePoint a s
  constructor
  · rintro ⟨g,hg⟩
    have hf : (characterTranslation k m) (g : AddMonoidAlgebra k (Lattice n))=f := by
      apply «Σ».torusRationalMap_injective k
      change «Σ».torusRationalMap k (AddMonoidAlgebra.single m 1 * g.val) = _
      rw [map_mul,← «Σ».rationalCharacter_value k m,
        ← «Σ».chartRationalMap_eq_torusRationalMap k («Σ».fullConeIndex s) g,hg]
      exact mul_div_cancel₀ _ (Units.ne_zero («Σ».rationalCharacter k m))
    exact ⟨g.val,g.property,hf⟩
  · rintro ⟨g,hg,hf⟩
    let g' : monoidChartAlgebra k (dualConeMonoid s.val) := ⟨g,hg⟩
    refine ⟨g',?_⟩
    apply (eq_div_iff (Units.ne_zero («Σ».rationalCharacter k m))).mpr
    rw [«Σ».chartRationalMap_eq_torusRationalMap k («Σ».fullConeIndex s) g']
    change «Σ».torusRationalMap k g *
      «Σ».torusRationalMap k (AddMonoidAlgebra.single m 1) = «Σ».torusRationalMap k f
    rw [← map_mul]
    apply congrArg («Σ».torusRationalMap k)
    change AddMonoidAlgebra.single m (1 : k) * g = f at hf
    exact (mul_comm g (AddMonoidAlgebra.single m 1)).trans hf

/-- Actual global sections whose rational value is a Laurent polynomial
are precisely those supported on the integral support-polytope points. -/
theorem torusRationalMap_mem_fanCartier_globalRange_iff
    (hpure : «Σ».IsPure) (a : Lattice n→ℤ)
    (f : AddMonoidAlgebra k (Lattice n)) :
    «Σ».torusRationalMap k f ∈ Set.range ((«Σ».fanCartierData k hpure a).sectionValue ⊤) ↔
      f∈characterModule k («Σ».fanIntegralExponents a) := by
  rw [«Σ».mem_fanCartier_globalRange_iff k hpure a]
  simp only [«Σ».torusRationalMap_mem_principal_chart_iff]
  rw [← «Σ».iInf_cartierChartCharacterModule k hpure a]
  exact (Submodule.mem_iInf _).symm

/-- Every actual global section has a Laurent-polynomial rational value;
this follows from any one of the nonempty full charts. -/
theorem fanCartier_globalRange_subset_torusRange (hpure : «Σ».IsPure)
    (a : Lattice n→ℤ) :
    Set.range ((«Σ».fanCartierData k hpure a).sectionValue ⊤) ⊆
      Set.range («Σ».torusRationalMap k) := by
  intro r hr
  obtain ⟨s,hs⟩ := «Σ».fullChartOpen_cover k hpure (genericPoint («Σ».fanScheme k))
  obtain ⟨g,hg⟩ := («Σ».mem_fanCartier_globalRange_iff k hpure a r).mp hr s
  let m := «Σ».cartierLatticePoint a s
  refine ⟨AddMonoidAlgebra.single m 1 * g.val,?_⟩
  rw [map_mul,← «Σ».rationalCharacter_value k m,
    ← «Σ».chartRationalMap_eq_torusRationalMap k («Σ».fullConeIndex s) g,hg]
  exact mul_div_cancel₀ _ (Units.ne_zero («Σ».rationalCharacter k m))

/-- Complete actual global-section dictionary, as equality of the literal
images in the scheme's genuine function field. -/
theorem fanCartier_globalRange (hpure : «Σ».IsPure) (a : Lattice n→ℤ) :
    Set.range ((«Σ».fanCartierData k hpure a).sectionValue ⊤) =
      «Σ».torusRationalMap k '' (characterModule k («Σ».fanIntegralExponents a) :
        Set (AddMonoidAlgebra k (Lattice n))) := by
  ext r
  constructor
  · intro hr
    obtain ⟨f,hf⟩ := «Σ».fanCartier_globalRange_subset_torusRange k hpure a hr
    refine ⟨f,?_,hf⟩
    apply («Σ».torusRationalMap_mem_fanCartier_globalRange_iff k hpure a f).mp
    simpa only [hf] using hr
  · rintro ⟨f,hf,rfl⟩
    exact («Σ».torusRationalMap_mem_fanCartier_globalRange_iff k hpure a f).mpr hf

end PaperVerification.ToricGeometry.SmoothCompleteFan

#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.mem_fanCartier_globalRange_iff
#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.fanCartier_globalRange
