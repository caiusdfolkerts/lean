import Characterizations.Localization
import Mathlib.Algebra.MvPolynomial.Rename

/-! Exact retained-variable data for localization descent. -/

noncomputable section

namespace Characterizations.Resolution

open Classical Finset CommAlg.Polymatroid

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {U W : Finset V}

def retainedInclusion (hUW : U ⊆ W) : U → W := fun i => ⟨i.val, hUW i.property⟩

theorem retainedInclusion_injective (hUW : U ⊆ W) :
    Function.Injective (retainedInclusion hUW) := by
  intro i j h
  exact Subtype.ext (congrArg (fun x : W => x.val) h)

theorem extendExponent_mapDomain_retained (hUW : U ⊆ W) (a : Exponent U) :
    extendExponent W (a.mapDomain (retainedInclusion hUW)) = extendExponent U a := by
  simp only [extendExponent, Finsupp.extendDomain_eq_embDomain_subtype,
    Finsupp.embDomain_eq_mapDomain, ← Finsupp.mapDomain_comp]
  rfl

/-- Equality of the ambient localized families is precisely extension of the
smaller retained-variable family by zero in the newly retained variables. -/
theorem localFamily_eq_image_of_localize_eq (B : Family V) (hUW : U ⊆ W)
    (he : localize B W = localize B U) :
    localFamily B W = (localFamily B U).image
      (fun a => a.mapDomain (retainedInclusion hUW)) := by
  apply Finset.image_injective (show Function.Injective (extendExponent W) from
    (extendExponentEmbedding W).injective)
  calc
    (localFamily B W).image (extendExponent W) = localize B W :=
      (localize_eq_extend_localFamily B W).symm
    _ = localize B U := he
    _ = ((localFamily B U).image (fun a => a.mapDomain (retainedInclusion hUW))).image
        (extendExponent W) := by
      rw [localize_eq_extend_localFamily, Finset.image_image]
      simp only [Function.comp_def, extendExponent_mapDomain_retained]

theorem localFamily_zero_of_localize_eq (B : Family V) (hUW : U ⊆ W)
    (he : localize B W = localize B U) (j : W) (hj : j.val ∉ U)
    (a : Exponent W) (ha : a ∈ localFamily B W) : a j = 0 := by
  rw [localFamily_eq_image_of_localize_eq B hUW he] at ha
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
  apply Finsupp.mapDomain_of_notMem_range
  rintro ⟨i, hi⟩
  exact hj (congrArg Subtype.val hi ▸ i.property)

variable {k : Type*} [CommSemiring k]

/-- Setting all newly retained variables to zero gives exactly the ideal in
the smaller retained-variable polynomial ring. -/
theorem killCompl_localFamily_ideal (B : Family V) (hUW : U ⊆ W)
    (he : localize B W = localize B U) :
    Ideal.map (MvPolynomial.killCompl (retainedInclusion_injective hUW)).toRingHom
      (monomialIdeal k (localFamily B W)) = monomialIdeal k (localFamily B U) := by
  have hmon (a : Exponent U) :
      MvPolynomial.killCompl (retainedInclusion_injective hUW)
        (MvPolynomial.monomial (a.mapDomain (retainedInclusion hUW)) (1 : k)) =
          MvPolynomial.monomial a 1 := by
    rw [← MvPolynomial.rename_monomial]
    exact MvPolynomial.killCompl_rename_app _ _
  rw [localFamily_eq_image_of_localize_eq B hUW he]
  simp only [monomialIdeal, Ideal.map_span, Finset.coe_image, Set.image_image]
  apply congrArg Ideal.span
  ext p
  simp only [Set.mem_image, Function.comp_apply, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe, hmon]

end Characterizations.Resolution
