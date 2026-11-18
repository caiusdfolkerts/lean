module

public import ToricPower.VectorDerivedDetection

/-!
# A scalar summand in any nonzero complex of vector spaces

One nonzero homology class supplies a split copy of the scalar field
in a suitable shift. The construction is valid for arbitrary unbounded
complexes and arbitrary-dimensional vector spaces. It permits the
local detection proof to use split maps rather than an unproved tensor
and derived-Hom interchange.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace ToricPower

universe u w
variable (k : Type u) [Field k]

/-- A nonzero vector space contains the scalar field as an actual
retract, without any finite-dimensional assumption. -/
theorem nonzero_vector_has_scalar_retract (M : ModuleCat.{u} k)
    (nonzero : ¬ IsZero M) : Nonempty (Retract (ModuleCat.of k k) M) := by
  have scalarNonzero : ¬ IsZero (ModuleCat.of k k) := by
    intro h
    letI := ModuleCat.isZero_iff_subsingleton.mp h
    exact zero_ne_one (Subsingleton.elim (0 : k) 1)
  obtain ⟨f,hf⟩ := exists_nonzero_vector_map M (ModuleCat.of k k) nonzero scalarNonzero
  have value : ∃ x : M, f x ≠ 0 := by
    by_contra! zero
    apply hf
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    exact zero
  obtain ⟨x,hx⟩ := value
  haveI : Epi f := (ModuleCat.epi_iff_surjective f).mpr (by
    intro y
    refine ⟨(y / f x) • x,?_⟩
    change f.hom ((y / f x) • x) = y
    rw [map_smul,smul_eq_mul,div_mul_cancel₀ _ hx])
  letI : Projective (ModuleCat.of k k) :=
    ModuleCat.projective_of_free (Module.Basis.ofVectorSpace k k)
  let inclusion := Projective.factorThru (𝟙 (ModuleCat.of k k)) f
  exact ⟨⟨inclusion,f,by simp only [inclusion,Projective.factorThru_comp]⟩⟩

variable [HasDerivedCategory.{w} (ModuleCat.{u} k)]

/-- Some shift of every nonzero derived vector space has the genuine
degree-zero scalar object as a retract. -/
theorem nonzero_derived_vector_has_scalar_retract
    (E : DerivedCategory (ModuleCat.{u} k)) (nonzero : ¬ IsZero E) :
    ∃ n : ℤ, Nonempty (Retract
      ((DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).obj (ModuleCat.of k k)) (E⟦n⟧)) := by
  let K := DerivedCategory.Q.objPreimage E
  let e := DerivedCategory.Q.objObjPreimageIso E
  have hK : ¬ IsZero (DerivedCategory.Q.obj K) := fun h => nonzero (e.isZero_iff.mp h)
  obtain ⟨n,hn⟩ := exists_nonzero_homology_of_nonzero_Q K hK
  obtain ⟨scalar⟩ := nonzero_vector_has_scalar_retract k (K.homology n) hn
  letI : Projective (K.homology n) :=
    ModuleCat.projective_of_free (Module.Basis.ofVectorSpace k (K.homology n))
  letI : Injective (K.homology n) := vectorInjective _
  let r : Retract
      ((DerivedCategory.singleFunctor (ModuleCat.{u} k) n).obj (ModuleCat.of k k)) E :=
    (scalar.map (DerivedCategory.singleFunctor (ModuleCat.{u} k) n)).trans
      ((derivedHomologyRetract K n).trans (Retract.ofIso e))
  let shift := ((DerivedCategory.singleFunctors (ModuleCat.{u} k)).shiftIso
    n 0 n (by omega)).app (ModuleCat.of k k)
  exact ⟨n,⟨(Retract.ofIso shift.symm).trans (r.map (shiftFunctor _ n))⟩⟩

end ToricPower

end
