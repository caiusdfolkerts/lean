module

public import PaperVerification.SegreTwistingSections

/-!
# Naturality of the Laurent description of twisting-sheaf sections

The map on coordinate intersections is the literal inclusion of Laurent
monomials. Its total-degree restriction commutes with the actual sheaf
restriction map. Consequently the coefficient calculation is compatible
with every face of the Čech complex, not merely with its separate terms.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

namespace PaperVerification.Segre.CoordinateLocalization

open scoped BigOperators

variable {I K : Type*} [Fintype I] [DecidableEq I] [CommRing K]

/-- Enlarging the inverted coordinate set preserves each literal exponent. -/
def exponentInclusion {S T : Finset I} (h : S ⊆ T) : allowedExponents S →+ allowedExponents T where
  toFun a := ⟨a.val,fun i hi => a.property i (fun hs => hi (h hs))⟩
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] theorem exponentInclusion_val {S T : Finset I} (h : S ⊆ T) (a : allowedExponents S) :
    (exponentInclusion h a).val=a.val := rfl

theorem exponentInclusion_injective {S T : Finset I} (h : S ⊆ T) :
    Function.Injective (exponentInclusion h) := by
  intro a b hab
  exact Subtype.ext (congrArg (fun x : allowedExponents T => x.val) hab)

/-- The actual inclusion of coordinate Laurent algebras. -/
def localRestriction {S T : Finset I} (h : S ⊆ T) :
    LocalLaurent K I S →ₐ[K] LocalLaurent K I T :=
  AddMonoidAlgebra.mapDomainAlgHom K K (exponentInclusion h)

@[simp] theorem localRestriction_polynomial {S T : Finset I} (h : S ⊆ T)
    (p : MvPolynomial I K) :
    localRestriction h (localizationMap S p)=localizationMap T p := by
  apply AddMonoidAlgebra.coeff_injective
  change Finsupp.mapDomain (exponentInclusion h)
    (Finsupp.mapDomain (naturalExponentMap S) p.coeff)=
      Finsupp.mapDomain (naturalExponentMap T) p.coeff
  rw [← Finsupp.mapDomain_comp]
  rfl

@[simp] theorem localRestriction_coeff {S T : Finset I} (h : S ⊆ T)
    (z : LocalLaurent K I S) (a : allowedExponents S) :
    (localRestriction h z).coeff (exponentInclusion h a)=z.coeff a :=
  Finsupp.mapDomain_apply_of_injective (exponentInclusion_injective h) z.coeff a

theorem localRestriction_mem_degree {S T : Finset I} (h : S ⊆ T) {t : ℤ}
    {z : LocalLaurent K I S} (hz : z ∈ localDegree S t) :
    localRestriction h z ∈ localDegree T t := by
  intro a ha
  have hc : Finsupp.mapDomain (exponentInclusion h) z.coeff a≠0 :=
    Finsupp.mem_support_iff.mp ha
  obtain ⟨b,rfl⟩ := Finsupp.mem_range_of_mapDomain_ne_zero hc
  rw [Finsupp.mapDomain_apply_of_injective (exponentInclusion_injective h)] at hc
  exact hz b (Finsupp.mem_support_iff.mpr hc)

/-- Restriction on each whole homogeneous component. -/
def degreeRestriction {S T : Finset I} (h : S ⊆ T) (t : ℤ) :
    localDegree (K := K) S t →ₗ[K] localDegree (K := K) T t :=
  (localRestriction (K := K) h).toLinearMap.restrict
    (fun _ hz => localRestriction_mem_degree (K := K) h hz)

@[simp] theorem degreeRestriction_val {S T : Finset I} (h : S ⊆ T) (t : ℤ)
    (z : localDegree (K := K) S t) :
    (degreeRestriction h t z).val=localRestriction h z.val := rfl

end PaperVerification.Segre.CoordinateLocalization

namespace PaperVerification.Segre.TwistingSections

open CoordinateLocalization AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped BigOperators

variable {I K : Type*} [Fintype I] [DecidableEq I] [CommRing K]

local notation "P" => MvPolynomial I K
local notation "𝒜" => MvPolynomial.homogeneousSubmodule I K

theorem chartIntersection_antitone {S T : Finset I} (h : S ⊆ T) :
    chartIntersection (K := K) T ≤ chartIntersection S :=
  Proj.basicOpen_mono 𝒜 _ _
    (Finset.prod_dvd_prod_of_subset S T (fun i => (MvPolynomial.X i : P)) h)

/-- The localization map at a point is unchanged by enlarging the denominator set. -/
theorem toPoint_localRestriction {S T : Finset I} (h : S ⊆ T)
    (x : chartIntersection (K := K) T) (z : LocalLaurent K I S) :
    toPoint T x (localRestriction h z)=
      toPoint S ⟨x.val,chartIntersection_antitone h x.property⟩ z := by
  have he : (toPoint T x).comp (localRestriction h).toRingHom=
      toPoint S ⟨x.val,chartIntersection_antitone h x.property⟩ := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (denominator (K := K) S))
    apply RingHom.ext
    intro p
    change toPoint T x (localRestriction h (localizationMap S p)) =
      toPoint S ⟨x.val,chartIntersection_antitone h x.property⟩ (localizationMap S p)
    simp only [localRestriction_polynomial,toPoint_polynomial]
  exact congrArg (fun f => f z) he

/-- The full section comparison respects every actual restriction map. -/
theorem sectionsEquiv_restriction {S T : Finset I} (h : S ⊆ T)
    (hS : S.Nonempty) (hT : T.Nonempty) (t : ℤ) (z : localDegree (K := K) S t) :
    (Proj.twistingSheaf 𝒜 t).presheaf.map (homOfLE (chartIntersection_antitone h)).op
        (sectionsEquiv S hS t z) =
      sectionsEquiv T hT t (degreeRestriction h t z) := by
  apply Proj.twistingSheaf.ext
  intro x
  exact (toPoint_localRestriction h x z.val).symm

end PaperVerification.Segre.TwistingSections
