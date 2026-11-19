module

public import Recovery.Unimodular.GraphicSectionRing.ToricDictionary.Part09
public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.Algebra.Order.Group.PiLex
public import Mathlib.Data.Finset.Max
public import Mathlib.CategoryTheory.Monoidal.Mod
public import Mathlib.AlgebraicGeometry.Cover.Directed
public import Mathlib.AlgebraicGeometry.Cover.Over
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

@[expose] public section
set_option autoImplicit false

section
-- BEGIN PaperVerification.ToricFanCharacters



/-!
# Actual rational characters on the glued fan scheme

The zero-cone chart is identified with the literal group algebra. All
chart rings map into the scheme's actual generic stalk, compatibly with
the actual face inclusions. Thus the characters used for Cartier
generators are genuine nonzero rational functions on the glued scheme.
-/

noncomputable section

universe u

namespace PaperVerification.ToricGeometry

open AlgebraicGeometry CategoryTheory
open PaperVerification.ToricCharacters PaperVerification.ToricSchemes
open scoped Classical

variable (k : Type u) (n : ℕ)

section Ring

variable [CommRing k]

def zeroConeChartAlgEquiv :
    monoidChartAlgebra k (dualConeMonoid (∅ : Finset (Lattice n))) ≃ₐ[k]
      AddMonoidAlgebra k (Lattice n) :=
  AlgEquiv.ofBijective (Subalgebra.val _) ⟨Subtype.val_injective, by
    intro f
    refine ⟨⟨f, (mem_monoidChartAlgebra k _ f).mpr ?_⟩, rfl⟩
    intro m hm u hu
    exact (Finset.notMem_empty u hu).elim⟩

@[simp] theorem zeroConeChartAlgEquiv_apply
    (f : monoidChartAlgebra k (dualConeMonoid (∅ : Finset (Lattice n)))) :
    zeroConeChartAlgEquiv k n f = (f : AddMonoidAlgebra k (Lattice n)) := rfl

def splitTorus : Scheme.{u} := Spec (CommRingCat.of (AddMonoidAlgebra k (Lattice n)))

def zeroConeChartIso : coneChart k (∅ : Finset (Lattice n)) ≅ splitTorus k n :=
  Scheme.Spec.mapIso (zeroConeChartAlgEquiv k n).toRingEquiv.toCommRingCatIso.symm.op

end Ring

namespace SmoothCompleteFan

variable {n} («Σ» : SmoothCompleteFan n)

section Ring

variable [CommRing k]

def splitTorusOpenMap : splitTorus k n ⟶ «Σ».fanScheme k :=
  (zeroConeChartIso k n).inv ≫ «Σ».torusOpenMap k

instance splitTorusOpenMap_isOpenImmersion : IsOpenImmersion («Σ».splitTorusOpenMap k) := by
  unfold splitTorusOpenMap
  infer_instance

end Ring

section Field

variable [Field k]

theorem splitTorusOpenMap_denseRange : DenseRange («Σ».splitTorusOpenMap k) := by
  have hrange : Set.range («Σ».splitTorusOpenMap k) = Set.range («Σ».torusOpenMap k) := by
    have hcomp : («Σ».splitTorusOpenMap k : splitTorus k n → «Σ».fanScheme k) =
        («Σ».torusOpenMap k) ∘ (zeroConeChartIso k n).inv := by
      funext x
      exact Scheme.Hom.comp_apply _ _ x
    have hsurj : Function.Surjective
        ((zeroConeChartIso k n).inv : splitTorus k n → coneChart k (∅ : Finset (Lattice n))) :=
      (zeroConeChartIso k n).inv.homeomorph.surjective
    rw [hcomp, Set.range_comp,
      Set.range_eq_univ.mpr hsurj,
      Set.image_univ]
  change Dense (Set.range («Σ».splitTorusOpenMap k))
  rw [hrange]
  exact «Σ».torusOpenMap_denseRange k

/-- The coordinate ring of an actual affine chart embeds in the actual
function field of the glued scheme, through its regular-section germ. -/
def chartRationalMap (s : «Σ».ConeIndex) :
    monoidChartAlgebra k (dualConeMonoid s.val) →+* («Σ».fanScheme k).functionField := by
  letI := «Σ».coneChart_isIntegral k s
  exact (openImmersionGlobalToFunctionField («Σ».fanChartMap k s)).comp
    (Scheme.ΓSpecIso (CommRingCat.of (monoidChartAlgebra k (dualConeMonoid s.val)))).inv.hom

theorem chartRationalMap_injective (s : «Σ».ConeIndex) :
    Function.Injective («Σ».chartRationalMap k s) := by
  letI := «Σ».coneChart_isIntegral k s
  exact (openImmersionGlobalToFunctionField_injective («Σ».fanChartMap k s)).comp
    (Scheme.ΓSpecIso (CommRingCat.of
      (monoidChartAlgebra k (dualConeMonoid s.val)))).symm.commRingCatIsoToRingEquiv.injective

/-- Rational evaluation commutes with the literal algebra inclusion, not
merely with a chosen abstract identification of chart rings. -/
theorem chartRationalMap_restrict {s t : «Σ».ConeIndex} (hst : s.val ⊆ t.val)
    (f : monoidChartAlgebra k (dualConeMonoid t.val)) :
    «Σ».chartRationalMap k s (monoidChartInclusion k (dualConeMonoid_antitone hst) f) =
      «Σ».chartRationalMap k t f := by
  letI := «Σ».coneChart_isIntegral k s
  letI := «Σ».coneChart_isIntegral k t
  letI := «Σ».coneChartFaceMap_isOpenImmersion k t.val s.val t.property hst
  let Rs := CommRingCat.of (monoidChartAlgebra k (dualConeMonoid s.val))
  let Rt := CommRingCat.of (monoidChartAlgebra k (dualConeMonoid t.val))
  have hsec : (Scheme.ΓSpecIso Rs).inv
      (monoidChartInclusion k (dualConeMonoid_antitone hst) f) =
      (coneChartFaceMap k hst).appTop ((Scheme.ΓSpecIso Rt).inv f) :=
    congrArg (fun g => g f) (Scheme.ΓSpecIso_inv_naturality
      (CommRingCat.ofHom (monoidChartInclusion k (dualConeMonoid_antitone hst)).toRingHom))
  change openImmersionGlobalToFunctionField («Σ».fanChartMap k s)
      ((Scheme.ΓSpecIso Rs).inv
        (monoidChartInclusion k (dualConeMonoid_antitone hst) f)) =
    openImmersionGlobalToFunctionField («Σ».fanChartMap k t) ((Scheme.ΓSpecIso Rt).inv f)
  rw [hsec]
  let a : Γ(coneChart k t.val, ⊤) := (Scheme.ΓSpecIso Rt).inv f
  change openImmersionGlobalToFunctionField («Σ».fanChartMap k s)
      ((coneChartFaceMap k hst).appTop a) =
    openImmersionGlobalToFunctionField («Σ».fanChartMap k t) a
  have h := openImmersionGlobalToFunctionField_restrict
    (coneChartFaceMap k hst) («Σ».fanChartMap k t) a
  simpa only [«Σ».fanChartMap_naturality k hst] using h

def torusRationalMap : AddMonoidAlgebra k (Lattice n) →+* («Σ».fanScheme k).functionField :=
  («Σ».chartRationalMap k «Σ».zeroConeIndex).comp (zeroConeChartAlgEquiv k n).symm.toRingHom

theorem torusRationalMap_injective : Function.Injective («Σ».torusRationalMap k) :=
  («Σ».chartRationalMap_injective k «Σ».zeroConeIndex).comp
    (zeroConeChartAlgEquiv k n).symm.injective

theorem chartRationalMap_eq_torusRationalMap (s : «Σ».ConeIndex)
    (f : monoidChartAlgebra k (dualConeMonoid s.val)) :
    «Σ».chartRationalMap k s f = «Σ».torusRationalMap k (f : AddMonoidAlgebra k (Lattice n)) := by
  rw [← «Σ».chartRationalMap_restrict k (s := «Σ».zeroConeIndex) (Finset.empty_subset s.val) f]
  change «Σ».chartRationalMap k «Σ».zeroConeIndex _ =
    «Σ».chartRationalMap k «Σ».zeroConeIndex ((zeroConeChartAlgEquiv k n).symm _)
  congr 1
  apply (zeroConeChartAlgEquiv k n).injective
  rw [AlgEquiv.apply_symm_apply]
  rfl

def rationalCharacterHom : Multiplicative (Lattice n) →* ((«Σ».fanScheme k).functionField)ˣ where
  toFun m := Units.mk0 («Σ».torusRationalMap k (AddMonoidAlgebra.single m.toAdd 1)) (by
    intro hz
    have hh : (AddMonoidAlgebra.single m.toAdd (1 : k)) = 0 :=
      «Σ».torusRationalMap_injective k (by simpa only [map_zero] using hz)
    simpa using hh)
  map_one' := by
    apply Units.ext
    change «Σ».torusRationalMap k (AddMonoidAlgebra.single 0 1) = 1
    exact («Σ».torusRationalMap k).map_one
  map_mul' m p := by
    apply Units.ext
    change «Σ».torusRationalMap k (AddMonoidAlgebra.single (m.toAdd + p.toAdd) 1) =
      «Σ».torusRationalMap k (AddMonoidAlgebra.single m.toAdd 1) *
        «Σ».torusRationalMap k (AddMonoidAlgebra.single p.toAdd 1)
    rw [← map_mul]
    simp

def rationalCharacter (m : Lattice n) : ((«Σ».fanScheme k).functionField)ˣ :=
  «Σ».rationalCharacterHom k (Multiplicative.ofAdd m)

@[simp] theorem rationalCharacter_value (m : Lattice n) :
    («Σ».rationalCharacter k m : («Σ».fanScheme k).functionField) =
      «Σ».torusRationalMap k (AddMonoidAlgebra.single m 1) := rfl

@[simp] theorem rationalCharacter_zero : «Σ».rationalCharacter k 0 = 1 :=
  («Σ».rationalCharacterHom k).map_one

@[simp] theorem rationalCharacter_add (m p : Lattice n) :
    «Σ».rationalCharacter k (m + p) = «Σ».rationalCharacter k m * «Σ».rationalCharacter k p :=
  («Σ».rationalCharacterHom k).map_mul (Multiplicative.ofAdd m) (Multiplicative.ofAdd p)

@[simp] theorem rationalCharacter_sub (m p : Lattice n) :
    «Σ».rationalCharacter k (m - p) = «Σ».rationalCharacter k m / «Σ».rationalCharacter k p :=
  («Σ».rationalCharacterHom k).map_div (Multiplicative.ofAdd m) (Multiplicative.ofAdd p)

theorem chartRationalMap_character (s : «Σ».ConeIndex) (m : Lattice n)
    (hm : m ∈ dualConeMonoid s.val) :
    «Σ».chartRationalMap k s (chartCharacter k (dualConeMonoid s.val) m hm) =
      («Σ».rationalCharacter k m : («Σ».fanScheme k).functionField) :=
  «Σ».chartRationalMap_eq_torusRationalMap k s _

end Field

end SmoothCompleteFan

end PaperVerification.ToricGeometry
end
-- END PaperVerification.ToricFanCharacters
end

section
-- BEGIN PaperVerification.ToricFanCartierCocycle



/-!
# Actual Cartier sheaves from integral fan support coefficients

For every integral coefficient function the full smooth charts give
genuine rational character generators. Their ratios are units on the
actual scheme overlaps. These data construct an invertible fractional
sheaf using the proved rational Cartier cocycle construction.
-/

noncomputable section

universe u

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open AlgebraicGeometry CategoryTheory
open PaperVerification.ToricCharacters PaperVerification.ToricSchemes
open scoped Classical

variable {n : ℕ} («Σ» : SmoothCompleteFan n) (k : Type u) [Field k]

def fullConeIndex (s : «Σ».fullCones) : «Σ».ConeIndex := ⟨s.val, «Σ».fullCones_mem s⟩

def fullChartOpen (s : «Σ».fullCones) : («Σ».fanScheme k).Opens :=
  («Σ».fanChartMap k («Σ».fullConeIndex s)).opensRange

theorem fullChartOpen_cover (hpure : «Σ».IsPure) (x : «Σ».fanScheme k) :
    ∃ s : «Σ».fullCones, x ∈ «Σ».fullChartOpen k s := by
  obtain ⟨t, y, hy⟩ := «Σ».fanChartMap_jointly_surjective k x
  obtain ⟨s, hs, hts, hcard⟩ := hpure t.val t.property
  let s' : «Σ».fullCones := ⟨s, Finset.mem_filter.mpr ⟨hs, hcard⟩⟩
  have hts' : t.val ⊆ («Σ».fullConeIndex s').val := hts
  refine ⟨s', coneChartFaceMap k hts' y, ?_⟩
  exact (congrArg (fun f : coneChart k t.val ⟶ «Σ».fanScheme k => f y)
    («Σ».fanChartMap_naturality k hts')).trans hy

theorem chartRationalMap_mem_regularAt (s : «Σ».ConeIndex)
    (f : monoidChartAlgebra k (dualConeMonoid s.val)) (x : coneChart k s.val) :
    «Σ».chartRationalMap k s f ∈ regularAtSubring («Σ».fanScheme k) («Σ».fanChartMap k s x) := by
  letI := «Σ».coneChart_isIntegral k s
  exact openImmersionGlobalToFunctionField_mem_regularAt («Σ».fanChartMap k s)
    ((Scheme.ΓSpecIso (CommRingCat.of
      (monoidChartAlgebra k (dualConeMonoid s.val)))).inv f) x

/-- The actual rational transition function is regular at each point of
the actual overlap. Interchanging s and t proves its inverse regular. -/
theorem cartier_rational_transition_regular (a : Lattice n → ℤ)
    (s t : «Σ».fullCones) (x : «Σ».fanScheme k)
    (hxs : x ∈ «Σ».fullChartOpen k s) (hxt : x ∈ «Σ».fullChartOpen k t) :
    ((«Σ».rationalCharacter k («Σ».cartierLatticePoint a s) : («Σ».fanScheme k).functionField) /
      («Σ».rationalCharacter k («Σ».cartierLatticePoint a t) : («Σ».fanScheme k).functionField)) ∈
        regularAtSubring («Σ».fanScheme k) x := by
  obtain ⟨ys, hys⟩ := hxs
  obtain ⟨yt, hyt⟩ := hxt
  obtain ⟨z, hzs, hzt⟩ := («Σ».fanChartMap_eq_iff k
    («Σ».fullConeIndex s) («Σ».fullConeIndex t) ys yt).mp (hys.trans hyt.symm)
  let l : «Σ».ConeIndex :=
    ⟨s.val ∩ t.val, «Σ».downward s.val («Σ».fullCones_mem s) _ Finset.inter_subset_left⟩
  have hlx : «Σ».fanChartMap k l z = x := by
    rw [← «Σ».fanChartMap_naturality k
      (show l.val ⊆ («Σ».fullConeIndex s).val from Finset.inter_subset_left)]
    change «Σ».fanChartMap k («Σ».fullConeIndex s)
      (coneChartFaceMap k Finset.inter_subset_left z) = x
    rw [hzs, hys]
  let m := «Σ».cartierLatticePoint a s - «Σ».cartierLatticePoint a t
  have hm : m ∈ dualConeMonoid l.val :=
    («Σ».cartier_difference_mem_overlap a s t).1
  have hregular := «Σ».chartRationalMap_mem_regularAt k l
    (chartCharacter k (dualConeMonoid l.val) m hm) z
  rw [«Σ».chartRationalMap_character k l m hm, hlx] at hregular
  simpa only [m, «Σ».rationalCharacter_sub k, Units.val_div_eq_div_val] using hregular

/-- The rational cocycle is built from ordinary integral ray coefficients;
local freeness and the actual sheaf condition are proved downstream. -/
def fanCartierCocycle (hpure : «Σ».IsPure) (a : Lattice n → ℤ) :
    RationalCartierCocycle («Σ».fanScheme k) where
  index := ULift.{u} «Σ».fullCones
  openSet i := «Σ».fullChartOpen k i.down
  covers x := by
    obtain ⟨s, hs⟩ := «Σ».fullChartOpen_cover k hpure x
    exact ⟨⟨s⟩, hs⟩
  generator i := «Σ».rationalCharacter k («Σ».cartierLatticePoint a i.down)
  transition i j x hxi hxj :=
    «Σ».cartier_rational_transition_regular k a i.down j.down x hxi hxj

/-- The genuine invertible fractional sheaf associated to the integral
Cartier data on the fan. -/
def fanCartierData (hpure : «Σ».IsPure) (a : Lattice n → ℤ) :
    CartierData («Σ».fanScheme k) :=
  («Σ».fanCartierCocycle k hpure a).toCartierData

end PaperVerification.ToricGeometry.SmoothCompleteFan
end
-- END PaperVerification.ToricFanCartierCocycle
end

section
-- BEGIN PaperVerification.ToricCartierBaseSections



/-!
# Actual base-field section multiplication

The scalar map comes from the given structural morphism X→Spec k, followed
by the actual structure-sheaf restriction. Consequently the multiplication
map here is the tensor map over the base field, without assuming Γ(X,O_X)=k.
The rational-value square is proved on pure tensors and hence on the whole
tensor product.
-/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped TensorProduct

namespace PaperVerification.ToricSchemes

namespace BaseSections

variable (k : Type u) [CommRing k] (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k))]

/-- The scalar map is induced by the actual structural morphism. -/
def scalarMap (U : X.Opens) : k →+* Γ(X,U) :=
  (X.presheaf.map (homOfLE le_top).op).hom.comp
    (((X ↘ Spec (CommRingCat.of k)).appTop).hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom)

scoped instance sectionsAlgebra (U : X.Opens) : Algebra k Γ(X,U) :=
  (scalarMap k X U).toAlgebra

scoped instance sectionsModule (M : X.Modules) (U : X.Opens) : Module k Γ(M,U) :=
  Module.compHom Γ(M,U) (scalarMap k X U)

scoped instance sectionsScalarTower (M : X.Modules) (U : X.Opens) :
    IsScalarTower k Γ(X,U) Γ(M,U) :=
  IsScalarTower.of_compHom k Γ(X,U) Γ(M,U)

variable [IsIntegral X]

scoped instance functionFieldAlgebra : Algebra k X.functionField :=
  ((X.germToFunctionField ⊤).hom.comp (scalarMap k X ⊤)).toAlgebra

scoped instance functionFieldScalarTower : IsScalarTower k Γ(X,⊤) X.functionField :=
  IsScalarTower.of_algebraMap_eq' rfl

end BaseSections

open scoped BaseSections

namespace CartierData

variable (k : Type u) [CommRing k] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of k))] (D E : CartierData X)

/-- Actual rational values of global sections as a base-linear map. -/
def globalSectionValue : Γ(D.sheaf,⊤) →ₗ[k] X.functionField :=
  (D.sectionValue ⊤).restrictScalars k

theorem globalSectionValue_injective : Function.Injective (D.globalSectionValue k) :=
  D.sectionValue_injective ⊤

/-- Multiplication of actual sections as a bilinear map over the base. -/
def sectionProductOver :
    Γ(D.sheaf,⊤) →ₗ[k] Γ(E.sheaf,⊤) →ₗ[k] Γ((D.add E).sheaf,⊤) :=
  (D.sectionProduct E ⊤).restrictScalars₁₂ k k

/-- The section multiplication map in the manuscript, with its tensor
product over the actual base field (indeed over any commutative base ring). -/
def sectionMultiplicationOver :
    Γ(D.sheaf,⊤) ⊗[k] Γ(E.sheaf,⊤) →ₗ[k] Γ((D.add E).sheaf,⊤) :=
  TensorProduct.lift (D.sectionProductOver k E)

@[simp] theorem sectionMultiplicationOver_value_tmul
    (s : Γ(D.sheaf,⊤)) (t : Γ(E.sheaf,⊤)) :
    (D.add E).globalSectionValue k (D.sectionMultiplicationOver k E (s ⊗ₜ[k] t)) =
      D.globalSectionValue k s * E.globalSectionValue k t :=
  D.sectionProduct_value E ⊤ s t

/-- The actual section tensor map becomes literal multiplication in K(X)
under the actual injective rational-value maps. -/
theorem globalSectionValue_comp_sectionMultiplicationOver :
    ((D.add E).globalSectionValue k).comp (D.sectionMultiplicationOver k E) =
      (LinearMap.mul' k X.functionField).comp
        (TensorProduct.map (D.globalSectionValue k) (E.globalSectionValue k)) := by
  apply TensorProduct.ext'
  intro s t
  exact D.sectionMultiplicationOver_value_tmul k E s t

/-- Surjectivity may be checked in the actual function field because the
target section map is proved injective. -/
theorem sectionMultiplicationOver_surjective_iff_range :
    Function.Surjective (D.sectionMultiplicationOver k E) ↔
      ((LinearMap.mul' k X.functionField).comp
        (TensorProduct.map (D.globalSectionValue k) (E.globalSectionValue k))).range =
      ((D.add E).globalSectionValue k).range := by
  rw [← D.globalSectionValue_comp_sectionMultiplicationOver k E]
  constructor
  · intro hs
    ext r
    constructor
    · rintro ⟨s,rfl⟩
      exact ⟨D.sectionMultiplicationOver k E s,rfl⟩
    · rintro ⟨t,rfl⟩
      obtain ⟨s,rfl⟩ := hs t
      exact ⟨s,rfl⟩
  · intro hr t
    have ht : (D.add E).globalSectionValue k t ∈
        (((D.add E).globalSectionValue k).comp
          (D.sectionMultiplicationOver k E)).range := by
      rw [hr]
      exact ⟨t,rfl⟩
    obtain ⟨s,hs⟩ := ht
    exact ⟨s,(D.add E).globalSectionValue_injective k hs⟩

end CartierData

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.CartierData.globalSectionValue_comp_sectionMultiplicationOver
#print axioms PaperVerification.ToricSchemes.CartierData.sectionMultiplicationOver_surjective_iff_range
end
-- END PaperVerification.ToricCartierBaseSections
end

section
-- BEGIN PaperVerification.ToricFanSectionValues



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
end
-- END PaperVerification.ToricFanSectionValues
end

section
-- BEGIN PaperVerification.ToricChartPicard



/-! # Triviality of the actual Picard group on every smooth fan chart -/

noncomputable section

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open PaperVerification.ToricCharacters PaperVerification.ToricSchemes
open AlgebraicGeometry CategoryTheory

variable {n : ℕ} («Σ» : SmoothCompleteFan n) (k : Type*) [Field k]

theorem chartPic_subsingleton (s : Finset (Lattice n)) (hs : s ∈ «Σ».cones) :
    Subsingleton (CommRing.Pic (monoidChartAlgebra k (dualConeMonoid s))) := by
  letI := «Σ».chartRing_isDomain k s hs
  letI := «Σ».chartRing_uniqueFactorization k s hs
  infer_instance

/-- Every actual invertible sheaf on a smooth cone chart is trivial.
The assertion is for the genuine structure sheaf, not a character module. -/
def chartInvertibleSheafIso (s : Finset (Lattice n)) (hs : s ∈ «Σ».cones)
    (M : (Spec (CommRingCat.of (monoidChartAlgebra k (dualConeMonoid s)))).Modules)
    (hM : IsInvertibleModule M) :
    M ≅ SheafOfModules.unit
      (Spec (CommRingCat.of (monoidChartAlgebra k (dualConeMonoid s)))).ringCatSheaf := by
  letI := «Σ».chartPic_subsingleton k s hs
  exact affineInvertibleSheafIso M hM

end PaperVerification.ToricGeometry.SmoothCompleteFan

#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.chartInvertibleSheafIso
end
-- END PaperVerification.ToricChartPicard
end

section
-- BEGIN PaperVerification.ToricFanCartierFrames



/-!
# Arbitrary Cartier frames on the actual fan scheme

An arbitrary invertible fractional sheaf is normalized on the dense torus.
Triviality of the genuine Picard group of each affine smooth chart supplies
an actual frame. Its rational generator is proved to be an actual unit of
the Laurent algebra, because both it and its inverse are regular on the
torus. No invariant-divisor presentation is assumed.
-/

noncomputable section

universe u

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open PaperVerification.ToricCharacters PaperVerification.ToricSchemes
open scoped Classical

variable {n : ℕ} («Σ» : SmoothCompleteFan n) (k : Type u) [Field k]

local instance splitTorus_integral : IsIntegral (ToricGeometry.splitTorus k n) := by
  letI := torusCoordinateRing_isDomain k n
  change IsIntegral (Spec (CommRingCat.of (torusCoordinateRing k n)))
  infer_instance

local instance splitTorusOpenMap_schemes_isOpenImmersion : IsOpenImmersion
    (show ToricSchemes.splitTorus k (Fin n → ℤ) ⟶ «Σ».fanScheme k from
      «Σ».splitTorusOpenMap k) :=
  «Σ».splitTorusOpenMap_isOpenImmersion k

set_option backward.isDefEq.respectTransparency.types false in
/-- Compatibility of the literal Laurent-ring inclusion with the actual
open torus's regular-function map into the genuine function field. -/
theorem torusRationalMap_eq_openImmersion (f : AddMonoidAlgebra k (Lattice n)) :
    «Σ».torusRationalMap k f =
      openImmersionGlobalToFunctionField («Σ».splitTorusOpenMap k)
        ((Scheme.ΓSpecIso (CommRingCat.of (AddMonoidAlgebra k (Lattice n)))).inv f) := by
  letI : IsIntegral (coneChart k (∅ : Finset (Lattice n))) :=
    «Σ».coneChart_isIntegral k «Σ».zeroConeIndex
  let R := CommRingCat.of (monoidChartAlgebra k (dualConeMonoid (∅ : Finset (Lattice n))))
  let S := CommRingCat.of (AddMonoidAlgebra k (Lattice n))
  let e := zeroConeChartAlgEquiv k n
  let g := (zeroConeChartIso k n).inv
  let a : Γ(coneChart k (∅ : Finset (Lattice n)),⊤) :=
    (Scheme.ΓSpecIso R).inv (e.symm f)
  have hsec : g.appTop a =
      (Scheme.ΓSpecIso S).inv f := by
    change @Eq (Γ(Spec S,⊤)) (g.appTop a) ((Scheme.ΓSpecIso S).inv f)
    have h := congrArg (fun h=>h (e.symm f))
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom e.toRingHom))
    change (Scheme.ΓSpecIso S).inv (e (e.symm f)) =
      g.appTop a at h
    exact h.symm.trans (congrArg (Scheme.ΓSpecIso S).inv (e.apply_symm_apply f))
  change openImmersionGlobalToFunctionField («Σ».torusOpenMap k) a =
    openImmersionGlobalToFunctionField (g ≫ «Σ».torusOpenMap k)
      ((Scheme.ΓSpecIso S).inv f)
  calc
    _ = openImmersionGlobalToFunctionField (g ≫ «Σ».torusOpenMap k) (g.appTop a) :=
      (openImmersionGlobalToFunctionField_restrict g («Σ».torusOpenMap k) a).symm
    _ = _ := congrArg (openImmersionGlobalToFunctionField (g ≫ «Σ».torusOpenMap k)) hsec

theorem torusOpen_le_chartOpen (s : «Σ».ConeIndex) :
    («Σ».splitTorusOpenMap k).opensRange ≤ («Σ».fanChartMap k s).opensRange := by
  rintro x ⟨y,rfl⟩
  refine ⟨coneChartFaceMap k (Finset.empty_subset s.val)
    ((zeroConeChartIso k n).inv y),?_⟩
  change (coneChartFaceMap k (Finset.empty_subset s.val) ≫ «Σ».fanChartMap k s)
      ((zeroConeChartIso k n).inv y) = _
  rw [«Σ».torusOpenMap_chart]
  rfl

/-- The actual normalized Cartier presentation for an arbitrary divisor. -/
def normalizedCartier (D : CartierData («Σ».fanScheme k)) : CartierData («Σ».fanScheme k) :=
  torusNormalizedCartier k n («Σ».fanScheme k) («Σ».splitTorusOpenMap k) D

theorem normalizedCartier_linearlyEquivalent (D : CartierData («Σ».fanScheme k)) :
    («Σ».normalizedCartier k D).LinearlyEquivalent D :=
  torusNormalizedCartier_linearlyEquivalent k n («Σ».fanScheme k)
    («Σ».splitTorusOpenMap k) D

theorem normalizedCartier_isAmple_iff (D : CartierData («Σ».fanScheme k)) :
    («Σ».normalizedCartier k D).IsAmple ↔ D.IsAmple :=
  torusNormalizedCartier_isAmple_iff k n («Σ».fanScheme k)
    («Σ».splitTorusOpenMap k) D

set_option backward.isDefEq.respectTransparency.types false in
/-- Normalization makes the actual fractional section image equal to the
ordinary ring of regular functions on the torus image. -/
theorem normalizedCartier_torus_range (D : CartierData («Σ».fanScheme k)) :
    let W := («Σ».splitTorusOpenMap k) ''ᵁ (⊤ : (ToricGeometry.splitTorus k n).Opens)
    letI : Nonempty W := openImmersion_image_nonempty («Σ».splitTorusOpenMap k) ⊤
    ((«Σ».normalizedCartier k D).sectionValueRange W : Set («Σ».fanScheme k).functionField) =
      Set.range ((«Σ».fanScheme k).germToFunctionField W) := by
  let j := «Σ».splitTorusOpenMap k
  letI : IsOpenImmersion j := «Σ».splitTorusOpenMap_isOpenImmersion k
  letI : IsOpenImmersion
      (show ToricSchemes.splitTorus k (Fin n → ℤ) ⟶ «Σ».fanScheme k from j) :=
    «Σ».splitTorusOpenMap_isOpenImmersion k
  letI : Nonempty (⊤ : (ToricSchemes.splitTorus k (Fin n → ℤ)).Opens) := by
    change Nonempty (⊤ : (ToricGeometry.splitTorus k n).Opens)
    infer_instance
  let W := j ''ᵁ (⊤ : (ToricGeometry.splitTorus k n).Opens)
  letI : Nonempty W := openImmersion_image_nonempty j ⊤
  change Set.range ((«Σ».normalizedCartier k D).sectionValue W) = _
  rw [← («Σ».normalizedCartier k D).alongSectionValue_range j ⊤]
  trans Set.range (openImmersionRegularToFunctionField j ⊤)
  · exact torusNormalizedCartier_range k n («Σ».fanScheme k) j D ⊤
  ext r
  constructor
  · rintro ⟨a,rfl⟩
    exact ⟨(j.appIso ⊤).inv a,
      (openImmersionRegularToFunctionField_eq_germ_image j ⊤ a).symm⟩
  · rintro ⟨a,rfl⟩
    refine ⟨(j.appIso ⊤).hom a,?_⟩
    rw [openImmersionRegularToFunctionField_eq_germ_image]
    simp
    rfl

/-- The frame is an actual sheaf isomorphism produced by affine Picard
triviality, applied to the arbitrary normalized Cartier sheaf. -/
def normalizedChartFrame (D : CartierData («Σ».fanScheme k)) (s : «Σ».ConeIndex) :
    («Σ».normalizedCartier k D).sheaf.restrict («Σ».fanChartMap k s) ≅
      SheafOfModules.unit (coneChart k s.val).ringCatSheaf := by
  letI : IsOpenImmersion
      (show Spec (CommRingCat.of (monoidChartAlgebra k (dualConeMonoid s.val))) ⟶
        «Σ».fanScheme k from «Σ».fanChartMap k s) :=
    «Σ».fanChartMap_isOpenImmersion k s
  exact «Σ».chartInvertibleSheafIso k s.val s.property
    ((«Σ».normalizedCartier k D).sheaf.restrict («Σ».fanChartMap k s))
    (isInvertibleModule_restrict («Σ».fanChartMap k s) («Σ».normalizedCartier k D).locallyFree)

def normalizedChartGenerator (D : CartierData («Σ».fanScheme k)) (s : «Σ».ConeIndex) :
    («Σ».fanScheme k).functionField := by
  letI := «Σ».coneChart_isIntegral k s
  exact («Σ».normalizedCartier k D).chartFrameRationalGenerator
    («Σ».fanChartMap k s) («Σ».normalizedChartFrame k D s)

theorem normalizedChartGenerator_ne_zero (D : CartierData («Σ».fanScheme k))
    (s : «Σ».ConeIndex) : «Σ».normalizedChartGenerator k D s ≠ 0 := by
  letI := «Σ».coneChart_isIntegral k s
  exact («Σ».normalizedCartier k D).chartFrameRationalGenerator_ne_zero
    («Σ».fanChartMap k s) («Σ».normalizedChartFrame k D s)

/-- Every chosen genuine chart generator is a genuine Laurent unit.
In particular this is stronger than being a nonzero rational function. -/
theorem exists_normalizedChartLaurentUnit (D : CartierData («Σ».fanScheme k))
    (s : «Σ».ConeIndex) :
    ∃ v : (AddMonoidAlgebra k (Lattice n))ˣ,
      «Σ».torusRationalMap k (v : AddMonoidAlgebra k (Lattice n)) =
        «Σ».normalizedChartGenerator k D s := by
  letI := «Σ».coneChart_isIntegral k s
  let j := «Σ».splitTorusOpenMap k
  let W := j ''ᵁ (⊤ : (ToricGeometry.splitTorus k n).Opens)
  letI : Nonempty W := openImmersion_image_nonempty j ⊤
  have hW : W≤(«Σ».fanChartMap k s).opensRange := by
    rw [show W=j ''ᵁ ⊤ from rfl,j.image_top_eq_opensRange]
    exact «Σ».torusOpen_le_chartOpen k s
  obtain ⟨a,ha⟩ := («Σ».normalizedCartier k D).chartFrameGenerator_isUnit_of_range
    («Σ».fanChartMap k s) («Σ».normalizedChartFrame k D s) W hW
    («Σ».normalizedCartier_torus_range k D)
  let S := CommRingCat.of (AddMonoidAlgebra k (Lattice n))
  let φ : Γ(«Σ».fanScheme k,W) →+* AddMonoidAlgebra k (Lattice n) :=
    (Scheme.ΓSpecIso S).hom.hom.comp (j.appIso ⊤).hom.hom
  refine ⟨Units.map φ a,?_⟩
  rw [Units.coe_map,«Σ».torusRationalMap_eq_openImmersion]
  change openImmersionGlobalToFunctionField j
    ((Scheme.ΓSpecIso S).inv (φ a))=«Σ».normalizedChartGenerator k D s
  rw [show (Scheme.ΓSpecIso S).inv (φ a)=(j.appIso ⊤).hom a by
    change (Scheme.ΓSpecIso S).inv ((Scheme.ΓSpecIso S).hom ((j.appIso ⊤).hom a)) = _
    exact (Scheme.ΓSpecIso S).hom_inv_id_apply _]
  rw [openImmersionRegularToFunctionField_eq_germ_image]
  simpa only [normalizedChartGenerator,Iso.hom_inv_id_apply] using ha

end PaperVerification.ToricGeometry.SmoothCompleteFan

#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.normalizedCartier_linearlyEquivalent
#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.exists_normalizedChartLaurentUnit
end
-- END PaperVerification.ToricFanCartierFrames
end

section
-- BEGIN PaperVerification.ToricFanRegularCharacters



/-! # Regular constants and the overlap equations of actual Cartier frames -/

noncomputable section

universe u

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open AlgebraicGeometry CategoryTheory
open PaperVerification.ToricCharacters PaperVerification.ToricSchemes
open scoped Classical

variable {n : ℕ} («Σ» : SmoothCompleteFan n) (k : Type u) [Field k]

def rationalScalar : k →+* («Σ».fanScheme k).functionField :=
  («Σ».torusRationalMap k).comp (algebraMap k (AddMonoidAlgebra k (Lattice n)))

def rationalScalarUnit (c : kˣ) : («Σ».fanScheme k).functionFieldˣ :=
  Units.map («Σ».rationalScalar k) c

theorem rationalScalar_mem_regularAt (c : k) (x : «Σ».fanScheme k) :
    «Σ».rationalScalar k c ∈ regularAtSubring («Σ».fanScheme k) x := by
  obtain ⟨s,y,rfl⟩ := «Σ».fanChartMap_jointly_surjective k x
  have h := «Σ».chartRationalMap_mem_regularAt k s
    (algebraMap k (monoidChartAlgebra k (dualConeMonoid s.val)) c) y
  rw [«Σ».chartRationalMap_eq_torusRationalMap k s] at h
  exact h

theorem torusRationalMap_single (m : Lattice n) (c : k) :
    «Σ».torusRationalMap k (AddMonoidAlgebra.single m c) =
      «Σ».rationalScalar k c *
        («Σ».rationalCharacter k m : («Σ».fanScheme k).functionField) := by
  change «Σ».torusRationalMap k (AddMonoidAlgebra.single m c) =
    «Σ».torusRationalMap k (algebraMap k (AddMonoidAlgebra k (Lattice n)) c) *
      «Σ».torusRationalMap k (AddMonoidAlgebra.single m 1)
  rw [← map_mul]
  congr 1
  simp

theorem characterDifference_regular_of_frameFactors
    (D : CartierData («Σ».fanScheme k)) (s t : «Σ».ConeIndex)
    (es : D.sheaf.restrict («Σ».fanChartMap k s) ≅
      SheafOfModules.unit (coneChart k s.val).ringCatSheaf)
    (et : D.sheaf.restrict («Σ».fanChartMap k t) ≅
      SheafOfModules.unit (coneChart k t.val).ringCatSheaf)
    (cs ct : kˣ) (ms mt : Lattice n)
    (hs : letI := «Σ».coneChart_isIntegral k s
      D.chartFrameRationalGenerator («Σ».fanChartMap k s) es =
        («Σ».rationalScalarUnit k cs : («Σ».fanScheme k).functionField) *
          («Σ».rationalCharacter k ms : («Σ».fanScheme k).functionField))
    (ht : letI := «Σ».coneChart_isIntegral k t
      D.chartFrameRationalGenerator («Σ».fanChartMap k t) et =
        («Σ».rationalScalarUnit k ct : («Σ».fanScheme k).functionField) *
          («Σ».rationalCharacter k mt : («Σ».fanScheme k).functionField))
    (x : «Σ».fanScheme k)
    (hxs : x∈(«Σ».fanChartMap k s).opensRange)
    (hxt : x∈(«Σ».fanChartMap k t).opensRange) :
    («Σ».rationalCharacter k (ms-mt) : («Σ».fanScheme k).functionField) ∈
      regularAtSubring («Σ».fanScheme k) x := by
  letI := «Σ».coneChart_isIntegral k s
  letI := «Σ».coneChart_isIntegral k t
  have hratio := D.chartFrameRatio_regularAt («Σ».fanChartMap k s)
    («Σ».fanChartMap k t) es et x hxs hxt
  have hconst := «Σ».rationalScalar_mem_regularAt k ((ct / cs : kˣ) : k) x
  have h := (regularAtSubring («Σ».fanScheme k) x).mul_mem hratio hconst
  rw [hs,ht] at h
  have he :
      ((«Σ».rationalScalarUnit k cs : («Σ».fanScheme k).functionField) *
        («Σ».rationalCharacter k ms : («Σ».fanScheme k).functionField) /
        ((«Σ».rationalScalarUnit k ct : («Σ».fanScheme k).functionField) *
          («Σ».rationalCharacter k mt : («Σ».fanScheme k).functionField))) *
          «Σ».rationalScalar k ((ct/cs : kˣ) : k) =
      («Σ».rationalCharacter k (ms-mt) : («Σ».fanScheme k).functionField) := by
    have hcs : «Σ».rationalScalar k (cs:k) ≠ 0 :=
      Units.ne_zero («Σ».rationalScalarUnit k cs)
    have hct : «Σ».rationalScalar k (ct:k) ≠ 0 :=
      Units.ne_zero («Σ».rationalScalarUnit k ct)
    simp only [«Σ».rationalCharacter_sub k ms mt,Units.val_div_eq_div_val]
    change ((«Σ».rationalScalar k (cs:k) *
        («Σ».rationalCharacter k ms : («Σ».fanScheme k).functionField)) /
        («Σ».rationalScalar k (ct:k) *
          («Σ».rationalCharacter k mt : («Σ».fanScheme k).functionField))) *
        «Σ».rationalScalar k ((ct:k)/(cs:k)) =
      («Σ».rationalCharacter k ms : («Σ».fanScheme k).functionField) /
        («Σ».rationalCharacter k mt : («Σ».fanScheme k).functionField)
    rw [map_div₀]
    field_simp [hcs,hct,Units.ne_zero] <;> ring
  simpa only [he] using h

/-- On every common ray, actual chart frames normalized by scalar units
have equal integral character pairings. This is obtained from regularity
of both transition directions on the genuine overlap chart. -/
theorem frameCharacter_pairing_eq
    (D : CartierData («Σ».fanScheme k)) (s t : «Σ».ConeIndex)
    (es : D.sheaf.restrict («Σ».fanChartMap k s) ≅
      SheafOfModules.unit (coneChart k s.val).ringCatSheaf)
    (et : D.sheaf.restrict («Σ».fanChartMap k t) ≅
      SheafOfModules.unit (coneChart k t.val).ringCatSheaf)
    (cs ct : kˣ) (ms mt : Lattice n)
    (hs : letI := «Σ».coneChart_isIntegral k s
      D.chartFrameRationalGenerator («Σ».fanChartMap k s) es =
        («Σ».rationalScalarUnit k cs : («Σ».fanScheme k).functionField) *
          («Σ».rationalCharacter k ms : («Σ».fanScheme k).functionField))
    (ht : letI := «Σ».coneChart_isIntegral k t
      D.chartFrameRationalGenerator («Σ».fanChartMap k t) et =
        («Σ».rationalScalarUnit k ct : («Σ».fanScheme k).functionField) *
          («Σ».rationalCharacter k mt : («Σ».fanScheme k).functionField))
    (v : Lattice n) (hvs : v∈s.val) (hvt : v∈t.val) :
    integerPairing v ms=integerPairing v mt := by
  let q : «Σ».ConeIndex := ⟨s.val∩t.val,«Σ».downward s.val s.property _ Finset.inter_subset_left⟩
  have hregular (x : «Σ».fanScheme k) (hx : x∈(«Σ».fanChartMap k q).opensRange) :
      («Σ».rationalCharacter k (ms-mt) : («Σ».fanScheme k).functionField) ∈
        regularAtSubring («Σ».fanScheme k) x := by
    obtain ⟨z,rfl⟩ := hx
    apply «Σ».characterDifference_regular_of_frameFactors k D s t es et cs ct ms mt hs ht
    · refine ⟨coneChartFaceMap k Finset.inter_subset_left z,?_⟩
      exact congrArg (fun f=>f z) («Σ».fanChartMap_naturality k Finset.inter_subset_left)
    · refine ⟨coneChartFaceMap k Finset.inter_subset_right z,?_⟩
      exact congrArg (fun f=>f z) («Σ».fanChartMap_naturality k Finset.inter_subset_right)
  have h₁ : ms-mt ∈ dualConeMonoid q.val :=
    («Σ».rationalCharacter_mem_chartRange_iff k q (ms-mt)).mp
      ((«Σ».mem_chartRationalMap_range_iff k q _).mpr hregular)
  have hregular' (x : «Σ».fanScheme k) (hx : x∈(«Σ».fanChartMap k q).opensRange) :
      («Σ».rationalCharacter k (mt-ms) : («Σ».fanScheme k).functionField) ∈
        regularAtSubring («Σ».fanScheme k) x := by
    obtain ⟨z,rfl⟩ := hx
    apply «Σ».characterDifference_regular_of_frameFactors k D t s et es ct cs mt ms ht hs
    · refine ⟨coneChartFaceMap k Finset.inter_subset_right z,?_⟩
      exact congrArg (fun f=>f z) («Σ».fanChartMap_naturality k Finset.inter_subset_right)
    · refine ⟨coneChartFaceMap k Finset.inter_subset_left z,?_⟩
      exact congrArg (fun f=>f z) («Σ».fanChartMap_naturality k Finset.inter_subset_left)
  have h₂ : mt-ms ∈ dualConeMonoid q.val :=
    («Σ».rationalCharacter_mem_chartRange_iff k q (mt-ms)).mp
      ((«Σ».mem_chartRationalMap_range_iff k q _).mpr hregular')
  have hv : v∈q.val := Finset.mem_inter.mpr ⟨hvs,hvt⟩
  have ha := h₁ v hv
  have hb := h₂ v hv
  rw [integerPairing_sub] at ha hb
  omega

end PaperVerification.ToricGeometry.SmoothCompleteFan

#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.frameCharacter_pairing_eq
end
-- END PaperVerification.ToricFanRegularCharacters
end

section
-- BEGIN PaperVerification.ToricFanIntegralCoefficients



/-! # Recovering integral support coefficients from compatible chart characters -/

noncomputable section

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open scoped Classical BigOperators

variable {n : ℕ} («Σ» : SmoothCompleteFan n) (hpure : «Σ».IsPure)

include hpure in
theorem exists_fullCone_of_ray (u : «Σ».rays) :
    ∃ s : «Σ».fullCones,u.val∈s.val := by
  obtain ⟨t,ht,hut⟩ := («Σ».mem_rays_iff u.val).mp u.property
  obtain ⟨s,hs,hts,hcard⟩ := hpure t ht
  exact ⟨⟨s,Finset.mem_filter.mpr ⟨hs,hcard⟩⟩,hts hut⟩

def rayFullCone (u : «Σ».rays) : «Σ».fullCones :=
  («Σ».exists_fullCone_of_ray hpure u).choose

theorem mem_rayFullCone (u : «Σ».rays) : u.val∈(«Σ».rayFullCone hpure u).val :=
  («Σ».exists_fullCone_of_ray hpure u).choose_spec

/-- Only actual rays carry coefficients; the extension away from the
finite ray set is fixed to zero and has no geometric effect. -/
def coefficientsOfCharacters (m : «Σ».fullCones→Lattice n) (u : Lattice n) : ℤ :=
  if hu : u∈«Σ».rays then -integerPairing u (m («Σ».rayFullCone hpure ⟨u,hu⟩)) else 0

theorem coefficientsOfCharacters_pairing (m : «Σ».fullCones→Lattice n)
    (hcompat : ∀ s t (u : Lattice n),u∈s.val → u∈t.val →
      integerPairing u (m s)=integerPairing u (m t))
    (s : «Σ».fullCones) (u : Lattice n) (hu : u∈s.val) :
    integerPairing u (m s) = -«Σ».coefficientsOfCharacters hpure m u := by
  have hray : u∈«Σ».rays := «Σ».ray_mem_of_mem_cone («Σ».fullCones_mem s) hu
  rw [coefficientsOfCharacters,dif_pos hray,neg_neg]
  exact hcompat s («Σ».rayFullCone hpure ⟨u,hray⟩) u hu
    («Σ».mem_rayFullCone hpure ⟨u,hray⟩)

/-- A full smooth cone determines the lattice character uniquely from
its actual pairings with the primitive ray basis. -/
theorem eq_cartierLatticePoint_of_pairings (a : Lattice n→ℤ)
    (s : «Σ».fullCones) (m : Lattice n)
    (hm : ∀ u∈s.val,integerPairing u m = -a u) :
    m=«Σ».cartierLatticePoint a s := by
  apply (integralDualBasis («Σ».fullConeBasis s)).repr.injective
  ext i
  have hi : «Σ».fullConeBasis s i∈s.val := by
    rw [«Σ».fullConeBasis_ray_set]
    exact Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩
  have h := (hm _ hi).trans («Σ».cartierLatticePoint_pairing a s _ hi).symm
  simpa only [integerPairing,integralDualBasis_repr,mul_comm] using h

/-- Compatibility on common rays reconstructs one honest integral
coefficient function whose ordinary Cartier points are the given characters. -/
theorem characters_eq_cartierLatticePoint (m : «Σ».fullCones→Lattice n)
    (hcompat : ∀ s t (u : Lattice n),u∈s.val → u∈t.val →
      integerPairing u (m s)=integerPairing u (m t)) (s : «Σ».fullCones) :
    m s=«Σ».cartierLatticePoint («Σ».coefficientsOfCharacters hpure m) s :=
  «Σ».eq_cartierLatticePoint_of_pairings _ s (m s)
    («Σ».coefficientsOfCharacters_pairing hpure m hcompat s)

end PaperVerification.ToricGeometry.SmoothCompleteFan

#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.characters_eq_cartierLatticePoint
end
-- END PaperVerification.ToricFanIntegralCoefficients
end

section
-- BEGIN PaperVerification.ToricLaurentUnits



/-!
# Units of the actual Laurent character ring

Maximum and minimum exponents of a product cannot cancel in a linearly
ordered character group. If the product is one, the two support widths
must both be zero. The finite-rank lattice receives its lexicographic
order only for this proof; the resulting classification is intrinsic.
-/

noncomputable section

namespace PaperVerification.ToricCharacters

open AddMonoidAlgebra

section Ordered

variable {k A : Type*} [Field k] [AddCommGroup A] [LinearOrder A]
    [IsOrderedAddMonoid A]

private theorem uniqueAdd_max (s t : Finset A) (hs : s.Nonempty) (ht : t.Nonempty) :
    UniqueAdd s t (s.max' hs) (t.max' ht) := by
  intro a b ha hb hab
  have ha' := Finset.le_max' s a ha
  have hb' := Finset.le_max' t b hb
  rcases lt_or_eq_of_le ha' with hlt | heq
  · exact ((ne_of_lt (add_lt_add_of_lt_of_le hlt hb')) hab).elim
  · exact ⟨heq, add_left_cancel ((congrArg (fun z => z+b) heq.symm).trans hab)⟩

private theorem uniqueAdd_min (s t : Finset A) (hs : s.Nonempty) (ht : t.Nonempty) :
    UniqueAdd s t (s.min' hs) (t.min' ht) := by
  intro a b ha hb hab
  have ha' := Finset.min'_le s a ha
  have hb' := Finset.min'_le t b hb
  rcases lt_or_eq_of_le ha' with hlt | heq
  · exact ((ne_of_lt (add_lt_add_of_lt_of_le hlt hb')) hab.symm).elim
  · exact ⟨heq.symm, add_left_cancel ((congrArg (fun z => z+b) heq).trans hab)⟩

/-- A unit of a group algebra of a linearly ordered abelian group is a
single character with a nonzero scalar coefficient. -/
theorem orderedCharacter_unit_single (u : (AddMonoidAlgebra k A)ˣ) :
    ∃ (c : kˣ) (m : A), (u : AddMonoidAlgebra k A) = single m (c : k) := by
  classical
  let f : AddMonoidAlgebra k A := u
  let g : AddMonoidAlgebra k A := ↑(u⁻¹)
  have hf : f ≠ 0 := Units.ne_zero u
  have hg : g ≠ 0 := Units.ne_zero (u⁻¹)
  have hs : f.coeff.support.Nonempty := by
    apply Finsupp.support_nonempty_iff.mpr
    intro h
    exact hf (AddMonoidAlgebra.coeff_eq_zero.mp h)
  have ht : g.coeff.support.Nonempty := by
    apply Finsupp.support_nonempty_iff.mpr
    intro h
    exact hg (AddMonoidAlgebra.coeff_eq_zero.mp h)
  have hprod : f * g = 1 := u.val_inv
  let amax := f.coeff.support.max' hs
  let amin := f.coeff.support.min' hs
  let bmax := g.coeff.support.max' ht
  let bmin := g.coeff.support.min' ht
  have hmax : amax + bmax = 0 := by
    have hcoeff : (f*g).coeff (amax+bmax) ≠ 0 := by
      rw [coeff_mul_add_of_uniqueAdd (uniqueAdd_max _ _ hs ht)]
      exact mul_ne_zero
        (Finsupp.mem_support_iff.mp (Finset.max'_mem _ hs))
        (Finsupp.mem_support_iff.mp (Finset.max'_mem _ ht))
    by_contra hne
    rw [hprod] at hcoeff
    simpa [AddMonoidAlgebra.one_def, hne] using hcoeff
  have hmin : amin + bmin = 0 := by
    have hcoeff : (f*g).coeff (amin+bmin) ≠ 0 := by
      rw [coeff_mul_add_of_uniqueAdd (uniqueAdd_min _ _ hs ht)]
      exact mul_ne_zero
        (Finsupp.mem_support_iff.mp (Finset.min'_mem _ hs))
        (Finsupp.mem_support_iff.mp (Finset.min'_mem _ ht))
    by_contra hne
    rw [hprod] at hcoeff
    simpa [AddMonoidAlgebra.one_def, hne] using hcoeff
  have hb : bmin ≤ bmax := Finset.min'_le _ _ (Finset.max'_mem _ ht)
  have hwidth : amax ≤ amin := (add_le_add_iff_right bmax).mp <| calc
    amax+bmax = amin+bmin := hmax.trans hmin.symm
    _ ≤ amin+bmax := add_le_add_right hb amin
  have hsupport : ∀ a ∈ f.coeff.support, a = amin := by
    intro a ha
    exact le_antisymm ((Finset.le_max' _ _ ha).trans hwidth) (Finset.min'_le _ _ ha)
  have hc : f.coeff amin ≠ 0 := Finsupp.mem_support_iff.mp (Finset.min'_mem _ hs)
  refine ⟨Units.mk0 (f.coeff amin) hc, amin, ?_⟩
  change f = single amin (f.coeff amin)
  apply AddMonoidAlgebra.ext
  ext a
  by_cases ha : a = amin
  · subst a
    simp
  · have hnot : a ∉ f.coeff.support := fun h => ha (hsupport a h)
    simp [Finsupp.notMem_support_iff.mp hnot, ha, Ne.symm ha]

end Ordered

variable (k : Type*) [Field k] (n : ℕ)

/-- The actual units of k[Z^n] are exactly nonzero constants times
individual lattice characters, in every rank including zero. -/
theorem laurent_unit_single (u : (AddMonoidAlgebra k (Fin n → ℤ))ˣ) :
    ∃ (c : kˣ) (m : Fin n → ℤ),
      (u : AddMonoidAlgebra k (Fin n → ℤ)) = single m (c : k) := by
  let e : (Fin n → ℤ) ≃+ Lex (Fin n → ℤ) :=
    { toFun := toLex, invFun := ofLex, left_inv := fun _ => rfl,
      right_inv := fun _ => rfl, map_add' := fun _ _ => rfl }
  let E := AddMonoidAlgebra.domCongr k k e
  obtain ⟨c,m,hm⟩ := orderedCharacter_unit_single (Units.map E.toMonoidHom u)
  refine ⟨c,ofLex m,?_⟩
  apply E.injective
  change E (u : AddMonoidAlgebra k (Fin n → ℤ)) =
    E (single (ofLex m) (c:k))
  change E (u : AddMonoidAlgebra k (Fin n → ℤ)) = single m (c:k) at hm
  have he : e (ofLex m) = m := by
    change toLex (ofLex m) = m
    exact toLex_ofLex m
  simpa only [E,AddMonoidAlgebra.domCongr_single,he] using hm

/-- Conversely every displayed scalar-character monomial is a unit. -/
theorem isUnit_single_character (c : kˣ) (m : Fin n → ℤ) :
    IsUnit (single m (c : k) : AddMonoidAlgebra k (Fin n → ℤ)) := by
  refine ⟨⟨single m (c:k), single (-m) ((c⁻¹:kˣ):k), ?_, ?_⟩, rfl⟩ <;>
    simp [AddMonoidAlgebra.single_mul_single, AddMonoidAlgebra.one_def]

theorem laurent_isUnit_iff (f : AddMonoidAlgebra k (Fin n → ℤ)) :
    IsUnit f ↔ ∃ (c : kˣ) (m : Fin n → ℤ), f = single m (c:k) := by
  constructor
  · rintro ⟨u,rfl⟩
    exact laurent_unit_single k n u
  · rintro ⟨c,m,rfl⟩
    exact isUnit_single_character k n c m

end PaperVerification.ToricCharacters

#print axioms PaperVerification.ToricCharacters.laurent_unit_single
end
-- END PaperVerification.ToricLaurentUnits
end

section
-- BEGIN PaperVerification.ToricCartierRangeEquality



/-! # Local equality of actual fractional sheaves detects Cartier equality -/

noncomputable section

universe u v

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

namespace PaperVerification.ToricSchemes.CartierData

variable {X : Scheme.{u}} [IsIntegral X] (D E : CartierData X)

set_option backward.isDefEq.respectTransparency false in
theorem localCocycle_generatorRatios_of_ranges
    (h : ∀ (U : X.Opens) [Nonempty U],
      (D.sectionValueRange U : Set X.functionField) = E.sectionValueRange U) :
    D.localCocycle.GeneratorRatioRegular E.localCocycle := by
  intro i j x hxi hxj
  let U := invertibleOpen D.locallyFree i
  let W := invertibleOpen E.locallyFree j
  let V := U⊓W
  letI : Nonempty U := ⟨⟨i,mem_invertibleOpen D.locallyFree i⟩⟩
  letI : Nonempty W := ⟨⟨j,mem_invertibleOpen E.locallyFree j⟩⟩
  letI : Nonempty V := ⟨⟨x,hxi,hxj⟩⟩
  have hq : D.frameRationalGenerator (invertibleFrame D.locallyFree i)∈E.sectionValueRange V := by
    change D.frameRationalGenerator (invertibleFrame D.locallyFree i) ∈
      (E.sectionValueRange V : Set X.functionField)
    rw [← h V]
    exact ⟨D.frameGenerator (invertibleFrame D.locallyFree i) V inf_le_left,
      D.sectionValue_frameGenerator _ inf_le_left⟩
  obtain ⟨a,ha⟩ := (E.mem_sectionValueRange_iff
    (invertibleFrame E.locallyFree j) (V:=V) inf_le_right _).mp hq
  have hav : X.germToFunctionField V a =
      D.frameRationalGenerator (invertibleFrame D.locallyFree i) /
        E.frameRationalGenerator (invertibleFrame E.locallyFree j) :=
    (eq_div_iff (E.frameRationalGenerator_ne_zero _)).mpr ha
  change D.frameRationalGenerator (invertibleFrame D.locallyFree i) /
    E.frameRationalGenerator (invertibleFrame E.locallyFree j) ∈ regularAtSubring X x
  rw [← hav]
  exact regular_germ_mem_regularAt X V a x ⟨hxi,hxj⟩

/-- Equality of all actual fractional section images gives an actual
sheaf isomorphism preserving the rational embedding. -/
theorem equivalent_of_sectionValueRanges
    (h : ∀ (U : X.Opens) [Nonempty U],
      (D.sectionValueRange U : Set X.functionField) = E.sectionValueRange U) :
    D.Equivalent E := by
  have hCE := D.localCocycle.equivalent_of_generatorRatios E.localCocycle
    (D.localCocycle_generatorRatios_of_ranges E h)
    (E.localCocycle_generatorRatios_of_ranges D (fun U _=>(h U).symm))
  exact D.equivalent_trans E.localCocycle.toCartierData E
    (D.equivalent_trans D.localCocycle.toCartierData E.localCocycle.toCartierData
      D.equivalent_localCocycle hCE)
    (E.equivalent_symm E.localCocycle.toCartierData E.equivalent_localCocycle)

theorem sectionValueRanges_eq_of_cover {ι : Type v} (W : ι→X.Opens)
    (hcover : ∀ x : X,∃ i,x∈W i)
    (hlocal : ∀ i (V : X.Opens) [Nonempty V], V≤W i →
      (D.sectionValueRange V : Set X.functionField)=E.sectionValueRange V)
    (U : X.Opens) [Nonempty U] :
    (D.sectionValueRange U : Set X.functionField)=E.sectionValueRange U := by
  have hincl (D E : CartierData X)
      (hlocal : ∀ i (V : X.Opens) [Nonempty V], V≤W i →
        (D.sectionValueRange V : Set X.functionField)=E.sectionValueRange V) :
      (D.sectionValueRange U : Set X.functionField)⊆E.sectionValueRange U := by
    rintro r ⟨s,rfl⟩
    apply E.exists_section_of_locally_in_range U (D.sectionValue U s)
    intro x
    obtain ⟨i,hxi⟩ := hcover x.val
    let V := U⊓W i
    letI : Nonempty V := ⟨⟨x.val,x.property,hxi⟩⟩
    have hr : D.sectionValue U s∈E.sectionValueRange V := by
      change D.sectionValue U s ∈ (E.sectionValueRange V : Set X.functionField)
      rw [← hlocal i V inf_le_right]
      exact ⟨D.sheaf.presheaf.map (homOfLE inf_le_left).op s,D.sectionValue_restrict _ s⟩
    obtain ⟨t,ht⟩ := hr
    exact ⟨V,inf_le_left,⟨x.property,hxi⟩,t,fun _=>ht⟩
  exact Set.Subset.antisymm (hincl D E hlocal)
    (hincl E D (fun i V _ hV=>(hlocal i V hV).symm))

/-- It suffices to compare the genuine fractional modules locally on an
actual open cover. No abstract divisor-dictionary premise is needed. -/
theorem equivalent_of_local_ranges {ι : Type v} (W : ι→X.Opens)
    (hcover : ∀ x : X,∃ i,x∈W i)
    (hlocal : ∀ i (V : X.Opens) [Nonempty V], V≤W i →
      (D.sectionValueRange V : Set X.functionField)=E.sectionValueRange V) :
    D.Equivalent E :=
  D.equivalent_of_sectionValueRanges E
    (fun U _=>D.sectionValueRanges_eq_of_cover E W hcover hlocal U)

end PaperVerification.ToricSchemes.CartierData

namespace PaperVerification.ToricSchemes.RationalCartierCocycle

variable {X : Scheme.{u}} [IsIntegral X] (C : RationalCartierCocycle X)

/-- The actual section image on a framed open is precisely its principal
fractional module, expressed by division by the genuine generator. -/
theorem mem_sectionValueRange_iff (i : C.index) (V : X.Opens) [Nonempty V]
    (hVi : V≤C.openSet i) (r : X.functionField) :
    r∈C.toCartierData.sectionValueRange V ↔
      r/(C.generator i : X.functionField)∈(X.germToFunctionField V).hom.range := by
  constructor
  · rintro ⟨s,rfl⟩
    exact (C.mem_submodule_iff_local i V hVi s.val).mp s.property
  · intro hr
    let t := (rationalValue X V).symm r
    have ht : t∈C.presheafSubmodule.obj (op V) := by
      apply (C.mem_submodule_iff_local i V hVi t).mpr
      simpa only [t,AddEquiv.apply_symm_apply] using hr
    exact ⟨⟨t,ht⟩,(rationalValue X V).apply_symm_apply r⟩

/-- Equality of the constructed actual Cartier sheaves recovers regular
ratios between the original, possibly differently indexed cocycles. -/
theorem generatorRatios_of_equivalent (D : RationalCartierCocycle X)
    (h : C.toCartierData.Equivalent D.toCartierData) : C.GeneratorRatioRegular D := by
  intro i j x hxi hxj
  let V := C.openSet i⊓D.openSet j
  letI : Nonempty V := ⟨⟨x,hxi,hxj⟩⟩
  have hmem : (C.generator i : X.functionField)∈C.toCartierData.sectionValueRange V := by
    apply (C.mem_sectionValueRange_iff i V inf_le_left _).mpr
    exact ⟨1,by simp⟩
  rw [C.toCartierData.equivalent_sectionValueRange D.toCartierData h V] at hmem
  obtain ⟨a,ha⟩ := (D.mem_sectionValueRange_iff j V inf_le_right _).mp hmem
  rw [← ha]
  exact regular_germ_mem_regularAt X V a x ⟨hxi,hxj⟩

/-- Arithmetic via chosen fractional-sheaf frames agrees with arithmetic
via any genuine original Cartier cocycle presentations. -/
theorem toCartierData_add_equivalent (D : RationalCartierCocycle X) :
    (C.toCartierData.add D.toCartierData).Equivalent (C.mul D).toCartierData := by
  let C' := C.toCartierData.localCocycle
  let D' := D.toCartierData.localCocycle
  have hC : C'.toCartierData.Equivalent C.toCartierData :=
    C.toCartierData.equivalent_symm C'.toCartierData C.toCartierData.equivalent_localCocycle
  have hD : D'.toCartierData.Equivalent D.toCartierData :=
    D.toCartierData.equivalent_symm D'.toCartierData D.toCartierData.equivalent_localCocycle
  exact (C'.mul D').equivalent_of_generatorRatios (C.mul D)
    (GeneratorRatioRegular.mul C' C D' D
      (C'.generatorRatios_of_equivalent C hC) (D'.generatorRatios_of_equivalent D hD))
    (GeneratorRatioRegular.mul C C' D D'
      (C.generatorRatios_of_equivalent C' C.toCartierData.equivalent_localCocycle)
      (D.generatorRatios_of_equivalent D' D.toCartierData.equivalent_localCocycle))

end PaperVerification.ToricSchemes.RationalCartierCocycle

#print axioms PaperVerification.ToricSchemes.CartierData.equivalent_of_local_ranges
end
-- END PaperVerification.ToricCartierRangeEquality
end

section
-- BEGIN PaperVerification.ToricArbitraryCartierFan



/-!
# Arbitrary Cartier data on a smooth fan scheme

Every actual invertible fractional sheaf on the actual glued fan scheme
has a linearly equivalent integral invariant presentation. The proof
normalizes on the dense torus, trivializes each actual affine chart by
its proved Picard vanishing, classifies the resulting Laurent units,
and reconstructs integral ray coefficients from the genuine overlaps.
The final equality preserves the actual rational embeddings after the
explicit principal translation used for torus normalization.
-/

noncomputable section

universe u

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open PaperVerification.ToricCharacters PaperVerification.ToricSchemes
open scoped Classical

variable {n : ℕ} («Σ» : SmoothCompleteFan n) (k : Type u) [Field k]

theorem exists_normalizedChartFactor (D : CartierData («Σ».fanScheme k))
    (s : «Σ».ConeIndex) :
    ∃ c : kˣ, ∃ m : Lattice n,
      «Σ».normalizedChartGenerator k D s =
        («Σ».rationalScalarUnit k c : («Σ».fanScheme k).functionField) *
          («Σ».rationalCharacter k m : («Σ».fanScheme k).functionField) := by
  obtain ⟨v,hv⟩ := «Σ».exists_normalizedChartLaurentUnit k D s
  obtain ⟨c,m,hv'⟩ := laurent_unit_single k n v
  refine ⟨c,m,?_⟩
  rw [← hv,hv',«Σ».torusRationalMap_single]
  rfl

def normalizedChartScalar (D : CartierData («Σ».fanScheme k)) (s : «Σ».ConeIndex) : kˣ :=
  («Σ».exists_normalizedChartFactor k D s).choose

def normalizedChartExponent (D : CartierData («Σ».fanScheme k)) (s : «Σ».ConeIndex) : Lattice n :=
  («Σ».exists_normalizedChartFactor k D s).choose_spec.choose

theorem normalizedChartGenerator_factor (D : CartierData («Σ».fanScheme k))
    (s : «Σ».ConeIndex) :
    «Σ».normalizedChartGenerator k D s =
      («Σ».rationalScalarUnit k («Σ».normalizedChartScalar k D s) :
        («Σ».fanScheme k).functionField) *
      («Σ».rationalCharacter k («Σ».normalizedChartExponent k D s) :
        («Σ».fanScheme k).functionField) :=
  («Σ».exists_normalizedChartFactor k D s).choose_spec.choose_spec

theorem normalizedChartExponent_pairing (D : CartierData («Σ».fanScheme k))
    (s t : «Σ».ConeIndex) (v : Lattice n) (hvs : v∈s.val) (hvt : v∈t.val) :
    integerPairing v («Σ».normalizedChartExponent k D s) =
      integerPairing v («Σ».normalizedChartExponent k D t) := by
  exact «Σ».frameCharacter_pairing_eq k («Σ».normalizedCartier k D) s t
    («Σ».normalizedChartFrame k D s) («Σ».normalizedChartFrame k D t)
    («Σ».normalizedChartScalar k D s) («Σ».normalizedChartScalar k D t)
    («Σ».normalizedChartExponent k D s) («Σ».normalizedChartExponent k D t)
    («Σ».normalizedChartGenerator_factor k D s) («Σ».normalizedChartGenerator_factor k D t)
    v hvs hvt

/-- Integral coefficients recovered from an arbitrary actual Cartier
divisor. They are not included as part of its definition. -/
def cartierCoefficients (hpure : «Σ».IsPure) (D : CartierData («Σ».fanScheme k)) :
    Lattice n→ℤ :=
  «Σ».coefficientsOfCharacters hpure
    (fun s=>«Σ».normalizedChartExponent k D («Σ».fullConeIndex s))

theorem normalizedChartExponent_eq_cartierPoint (hpure : «Σ».IsPure)
    (D : CartierData («Σ».fanScheme k)) (s : «Σ».fullCones) :
    «Σ».normalizedChartExponent k D («Σ».fullConeIndex s) =
      «Σ».cartierLatticePoint («Σ».cartierCoefficients k hpure D) s := by
  change «Σ».normalizedChartExponent k D («Σ».fullConeIndex s) =
    «Σ».cartierLatticePoint («Σ».coefficientsOfCharacters hpure
      (fun t => «Σ».normalizedChartExponent k D («Σ».fullConeIndex t))) s
  apply «Σ».characters_eq_cartierLatticePoint hpure
    (fun t => «Σ».normalizedChartExponent k D («Σ».fullConeIndex t))
  intro s t v hvs hvt
  exact «Σ».normalizedChartExponent_pairing k D («Σ».fullConeIndex s) («Σ».fullConeIndex t)
    v hvs hvt

/-- Scalar units do not change the actual principal fractional module on
a chart. This statement uses actual regular sections on every subopen. -/
theorem mem_normalizedCartier_range_iff (D : CartierData («Σ».fanScheme k))
    (s : «Σ».ConeIndex) (V : («Σ».fanScheme k).Opens) [Nonempty V]
    (hV : V≤(«Σ».fanChartMap k s).opensRange) (r : («Σ».fanScheme k).functionField) :
    r∈(«Σ».normalizedCartier k D).sectionValueRange V ↔
      r/(«Σ».rationalCharacter k («Σ».normalizedChartExponent k D s) :
        («Σ».fanScheme k).functionField) ∈
          ((«Σ».fanScheme k).germToFunctionField V).hom.range := by
  letI := «Σ».coneChart_isIntegral k s
  let N := «Σ».normalizedCartier k D
  let e := «Σ».normalizedChartFrame k D s
  let q := «Σ».normalizedChartGenerator k D s
  let c := «Σ».normalizedChartScalar k D s
  let m := «Σ».normalizedChartExponent k D s
  have hq : q=(«Σ».rationalScalarUnit k c : («Σ».fanScheme k).functionField) *
      («Σ».rationalCharacter k m : («Σ».fanScheme k).functionField) :=
    «Σ».normalizedChartGenerator_factor k D s
  constructor
  · intro hr
    obtain ⟨a,ha⟩ := (N.mem_sectionValueRange_iff_chartFrame
      («Σ».fanChartMap k s) e V hV r).mp hr
    apply (mem_regular_range_iff_stalkwise («Σ».fanScheme k) V _).mpr
    intro x hx
    have h := (regularAtSubring («Σ».fanScheme k) x).mul_mem
      (regular_germ_mem_regularAt («Σ».fanScheme k) V a x hx)
      («Σ».rationalScalar_mem_regularAt k (c:k) x)
    have he : («Σ».fanScheme k).germToFunctionField V a * «Σ».rationalScalar k (c:k) =
        r/(«Σ».rationalCharacter k m : («Σ».fanScheme k).functionField) := by
      apply (eq_div_iff (Units.ne_zero («Σ».rationalCharacter k m))).mpr
      rw [mul_assoc]
      exact (congrArg ((«Σ».fanScheme k).germToFunctionField V a * ·) hq.symm).trans ha
    simpa only [he] using h
  · intro hr
    have hr' := (mem_regular_range_iff_stalkwise («Σ».fanScheme k) V _).mp hr
    have hregular : ∀ x∈V,r/q∈regularAtSubring («Σ».fanScheme k) x := by
      intro x hx
      have h := (regularAtSubring («Σ».fanScheme k) x).mul_mem (hr' x hx)
        («Σ».rationalScalar_mem_regularAt k ((c⁻¹:kˣ):k) x)
      change (r/(«Σ».rationalCharacter k m : («Σ».fanScheme k).functionField)) *
        «Σ».rationalScalar k ((c⁻¹:kˣ):k) ∈ regularAtSubring («Σ».fanScheme k) x at h
      have he : (r/(«Σ».rationalCharacter k m : («Σ».fanScheme k).functionField)) *
          «Σ».rationalScalar k ((c⁻¹:kˣ):k) = r/q := by
        have hc : «Σ».rationalScalar k (c:k)≠0 := Units.ne_zero («Σ».rationalScalarUnit k c)
        rw [hq]
        simp only [rationalScalarUnit,Units.coe_map,Units.val_inv_eq_inv_val,map_inv₀]
        field_simp [hc,Units.ne_zero]
        rfl
      simpa only [he] using h
    obtain ⟨a,ha⟩ := exists_regularSection_of_stalkwise («Σ».fanScheme k) V (r/q) hregular
    apply (N.mem_sectionValueRange_iff_chartFrame («Σ».fanChartMap k s) e V hV r).mpr
    refine ⟨a,?_⟩
    rw [ha]
    exact div_mul_cancel₀ r («Σ».normalizedChartGenerator_ne_zero k D s)

/-- Equality of actual Cartier-divisor presentations after the explicit
principal normalization on the dense torus. No invariant presentation is
assumed for the input divisor. -/
theorem normalizedCartier_equivalent_fanCartier (hpure : «Σ».IsPure)
    (D : CartierData («Σ».fanScheme k)) :
    («Σ».normalizedCartier k D).Equivalent
      («Σ».fanCartierData k hpure («Σ».cartierCoefficients k hpure D)) := by
  apply («Σ».normalizedCartier k D).equivalent_of_local_ranges
    («Σ».fanCartierData k hpure («Σ».cartierCoefficients k hpure D))
    («Σ».fullChartOpen k) («Σ».fullChartOpen_cover k hpure)
  intro s V _ hV
  ext r
  change r ∈ («Σ».normalizedCartier k D).sectionValueRange V ↔
    r ∈ («Σ».fanCartierData k hpure («Σ».cartierCoefficients k hpure D)).sectionValueRange V
  rw [«Σ».mem_normalizedCartier_range_iff k D («Σ».fullConeIndex s) V hV r]
  rw [«Σ».normalizedChartExponent_eq_cartierPoint k hpure D s]
  exact ((«Σ».fanCartierCocycle k hpure («Σ».cartierCoefficients k hpure D)).mem_sectionValueRange_iff (ULift.up s) V hV r).symm

/-- Every arbitrary Cartier sheaf on the actual smooth fan scheme is
linearly equivalent to a proved integral invariant presentation. -/
theorem cartierData_linearlyEquivalent_fanCartier (hpure : «Σ».IsPure)
    (D : CartierData («Σ».fanScheme k)) :
    D.LinearlyEquivalent
      («Σ».fanCartierData k hpure («Σ».cartierCoefficients k hpure D)) := by
  exact D.linearlyEquivalent_trans («Σ».normalizedCartier k D) _
    ((«Σ».normalizedCartier k D).linearlyEquivalent_symm D
      («Σ».normalizedCartier_linearlyEquivalent k D))
    ⟨(«Σ».normalizedCartier_equivalent_fanCartier k hpure D).choose⟩

/-- The actual section-space dictionary for an arbitrary Cartier divisor,
after the explicitly recorded principal translation. -/
theorem normalizedCartier_globalRange (hpure : «Σ».IsPure)
    (D : CartierData («Σ».fanScheme k)) :
    Set.range ((«Σ».normalizedCartier k D).sectionValue ⊤) =
      «Σ».torusRationalMap k ''
        (characterModule k («Σ».fanIntegralExponents («Σ».cartierCoefficients k hpure D)) :
          Set (AddMonoidAlgebra k (Lattice n))) := by
  have hr := («Σ».normalizedCartier k D).equivalent_sectionValueRange
    («Σ».fanCartierData k hpure («Σ».cartierCoefficients k hpure D))
    («Σ».normalizedCartier_equivalent_fanCartier k hpure D) ⊤
  change (↑((«Σ».normalizedCartier k D).sectionValueRange ⊤) :
    Set («Σ».fanScheme k).functionField)=_
  rw [hr]
  exact «Σ».fanCartier_globalRange k hpure _

end PaperVerification.ToricGeometry.SmoothCompleteFan

#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.normalizedCartier_equivalent_fanCartier
#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.cartierData_linearlyEquivalent_fanCartier
#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.normalizedCartier_globalRange
end
-- END PaperVerification.ToricArbitraryCartierFan
end

section
-- BEGIN PaperVerification.ToricActionGluing



/-!
# Gluing genuine group actions over a directed open cover

The construction uses the actual base change of an open cover along the
second projection. Consequently its descent and action laws are equalities
of scheme morphisms, over arbitrary base schemes and all residue fields.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open MonoidalCategory MonObj

variable {S X : Scheme.{u}} [X.Over S]
    (C : X.OpenCover) [Category C.I₀] [C.LocallyDirected] [C.Over S]

instance directedCoverTrans_isOver {i j : C.I₀} (h : i ⟶ j) :
    (C.trans h).IsOver S where
  comp_over := by
    rw [← comp_over (C.f j) S, ← Category.assoc, C.trans_map, comp_over]

/-- The pullback of a chart along the second projection is its actual
product with the first factor. -/
def tensorPullbackChartIso (A : Over S) (i : C.I₀) :
    (C.pullback₁ (pullback.snd A.hom (X ↘ S))).X i ≅
      (A ⊗ (C.X i).asOver S).left :=
  pullbackLeftPullbackSndIso A.hom (X ↘ S) (C.f i) ≪≫
    pullback.congrHom rfl (comp_over (C.f i) S)

@[reassoc (attr := simp)] theorem tensorPullbackChartIso_hom_fst
    (A : Over S) (i : C.I₀) :
    (tensorPullbackChartIso C A i).hom ≫ pullback.fst A.hom (C.X i ↘ S) =
      pullback.fst (pullback.snd A.hom (X ↘ S)) (C.f i) ≫
        pullback.fst A.hom (X ↘ S) := by
  change (pullbackLeftPullbackSndIso A.hom (X ↘ S) (C.f i) ≪≫
    pullback.congrHom rfl (comp_over (C.f i) S)).hom ≫ _ = _
  simp

@[reassoc (attr := simp)] theorem tensorPullbackChartIso_hom_snd
    (A : Over S) (i : C.I₀) :
    (tensorPullbackChartIso C A i).hom ≫ pullback.snd A.hom (C.X i ↘ S) =
      pullback.snd (pullback.snd A.hom (X ↘ S)) (C.f i) := by
  change (pullbackLeftPullbackSndIso A.hom (X ↘ S) (C.f i) ≪≫
    pullback.congrHom rfl (comp_over (C.f i) S)).hom ≫ _ = _
  simp

@[reassoc (attr := simp)] theorem tensorPullbackChartIso_hom_map
    (A : Over S) (i : C.I₀) :
    (tensorPullbackChartIso C A i).hom ≫ (A ◁ (C.f i).asOver S).left =
      (C.pullback₁ (pullback.snd A.hom (X ↘ S))).f i := by
  change (tensorPullbackChartIso C A i).hom ≫ (A ◁ (C.f i).asOver S).left =
    pullback.fst (pullback.snd A.hom (X ↘ S)) (C.f i)
  apply pullback.hom_ext
  all_goals dsimp only [Scheme.asOver, OverClass.asOver]
  · simp only [Category.assoc, Over.whiskerLeft_left_fst]
    dsimp only [Over.mk]
    exact tensorPullbackChartIso_hom_fst C A i
  · simp only [Category.assoc, Over.whiskerLeft_left_snd, OverClass.asOverHom_left]
    dsimp only [Over.mk]
    exact (tensorPullbackChartIso_hom_snd_assoc C A i (C.f i)).trans
      (pullback.condition (f := pullback.snd A.hom (X ↘ S)) (g := C.f i)).symm

@[reassoc (attr := simp)] theorem tensorPullbackChartIso_inv_map
    (A : Over S) (i : C.I₀) :
    (tensorPullbackChartIso C A i).inv ≫
        (C.pullback₁ (pullback.snd A.hom (X ↘ S))).f i =
      (A ◁ (C.f i).asOver S).left := by
  calc
    (tensorPullbackChartIso C A i).inv ≫
        (C.pullback₁ (pullback.snd A.hom (X ↘ S))).f i =
      (tensorPullbackChartIso C A i).inv ≫
        (tensorPullbackChartIso C A i).hom ≫ (A ◁ (C.f i).asOver S).left :=
          congrArg (fun f => (tensorPullbackChartIso C A i).inv ≫ f)
            (tensorPullbackChartIso_hom_map C A i).symm
    _ = _ := Iso.inv_hom_id_assoc _ _

@[reassoc (attr := simp)] theorem tensorPullbackChartIso_naturality
    (A : Over S) {i j : C.I₀} (h : i ⟶ j) :
    Scheme.Cover.trans (C.pullback₁ (pullback.snd A.hom (X ↘ S))) h ≫
        (tensorPullbackChartIso C A j).hom =
      (tensorPullbackChartIso C A i).hom ≫
        (A ◁ (C.trans h).asOver S).left := by
  apply pullback.hom_ext
  all_goals dsimp only [Scheme.asOver, OverClass.asOver]
  · change Scheme.Cover.trans (C.pullback₁ (pullback.snd A.hom (X ↘ S))) h ≫
        (tensorPullbackChartIso C A j).hom ≫ pullback.fst A.hom (C.X j ↘ S) = _
    simp only [tensorPullbackChartIso_hom_fst, Category.assoc,
      Over.whiskerLeft_left_fst]
    change pullback.map _ _ _ _ (𝟙 _) (C.trans h) (𝟙 _) (by simp) (by simp) ≫
      pullback.fst _ _ ≫ pullback.fst _ _ = _
    simp
  · change Scheme.Cover.trans (C.pullback₁ (pullback.snd A.hom (X ↘ S))) h ≫
        (tensorPullbackChartIso C A j).hom ≫ pullback.snd A.hom (C.X j ↘ S) = _
    simp only [tensorPullbackChartIso_hom_snd, Category.assoc,
      Over.whiskerLeft_left_snd, OverClass.asOverHom_left,
      tensorPullbackChartIso_hom_snd_assoc]
    change pullback.map _ _ _ _ (𝟙 _) (C.trans h) (𝟙 _) (by simp) (by simp) ≫ pullback.snd _ _ = _
    simp

/-- Tensoring a genuine open cover is jointly epimorphic. The proof uses
scheme-theoretic base change, not an assertion about pairs of points. -/
theorem tensorCover_hom_ext (A Y : Over S)
    (f g : A ⊗ X.asOver S ⟶ Y)
    (h : ∀ i, A ◁ (C.f i).asOver S ≫ f = A ◁ (C.f i).asOver S ≫ g) :
    f = g := by
  apply Over.OverMorphism.ext
  apply Scheme.Cover.hom_ext (C.pullback₁ (pullback.snd A.hom (X ↘ S)))
  intro i
  rw [← tensorPullbackChartIso_hom_map C A i]
  simpa only [Over.comp_left, Category.assoc] using
    congrArg (fun z => (tensorPullbackChartIso C A i).hom ≫ z.left) (h i)

section Actions

variable (G : Over S) [MonObj G]
    [∀ i, ModObj G ((C.X i).asOver S)]
    (htrans : ∀ {i j : C.I₀} (h : i ⟶ j),
      IsModHom G ((C.trans h).asOver S))

/-- Compatible chart actions descend to an actual scheme morphism. -/
def gluedAction : G ⊗ X.asOver S ⟶ X.asOver S := by
  letI : Category (C.pullback₁ (pullback.snd G.hom (X ↘ S))).I₀ :=
    inferInstanceAs (Category C.I₀)
  letI : Scheme.Cover.LocallyDirected
      (C.pullback₁ (pullback.snd G.hom (X ↘ S))) :=
    Scheme.Cover.locallyDirectedPullbackCover C (pullback.snd G.hom (X ↘ S))
  exact Scheme.OpenCover.glueMorphismsOverOfLocallyDirected
    (X := G ⊗ X.asOver S) (Y := X.asOver S)
    (C.pullback₁ (pullback.snd G.hom (X ↘ S)))
    (fun (i : C.I₀) => (tensorPullbackChartIso C G i).hom ≫
      (γ[G,(C.X i).asOver S]).left ≫ C.f i)
    (by
      intro i j h
      letI := htrans h
      rw [← Category.assoc, tensorPullbackChartIso_naturality C, Category.assoc]
      have heq : (γ[G,(C.X i).asOver S]).left ≫ C.trans h =
          (G ◁ (C.trans h).asOver S).left ≫ (γ[G,(C.X j).asOver S]).left := by
        simpa only [Over.comp_left, OverClass.asOverHom_left,
          selfLeftAction_actionObj, selfLeftAction_actionHomRight,
          OverClass.asOver_left] using
          congrArg (fun z => z.left)
            (IsModHom.smul_hom (A := G) (f := (C.trans h).asOver S))
      simpa only [Category.assoc, C.trans_map] using
        congrArg (fun f => (tensorPullbackChartIso C G i).hom ≫ f ≫ C.f j) heq.symm)
    (by
      intro i
      change (tensorPullbackChartIso C G i).hom ≫
        (γ[G,(C.X i).asOver S]).left ≫ C.f i ≫ (X ↘ S) = _
      rw [comp_over]
      change (tensorPullbackChartIso C G i).hom ≫
        (γ[G,(C.X i).asOver S]).left ≫ ((C.X i).asOver S).hom = _
      rw [Over.w]
      change (tensorPullbackChartIso C G i).hom ≫
        pullback.fst G.hom (C.X i ↘ S) ≫ G.hom = _
      simp only [tensorPullbackChartIso_hom_fst_assoc]
      rfl)

/-- The descended morphism restricts to the original action on every
actual affine chart. -/
@[reassoc (attr := simp)] theorem gluedAction_restrict (i : C.I₀) :
    G ◁ (C.f i).asOver S ≫ gluedAction C G htrans =
      γ[G,(C.X i).asOver S] ≫ (C.f i).asOver S := by
  letI : Category (C.pullback₁ (pullback.snd G.hom (X ↘ S))).I₀ :=
    inferInstanceAs (Category C.I₀)
  letI : Scheme.Cover.LocallyDirected
      (C.pullback₁ (pullback.snd G.hom (X ↘ S))) :=
    Scheme.Cover.locallyDirectedPullbackCover C (pullback.snd G.hom (X ↘ S))
  apply Over.OverMorphism.ext
  apply (cancel_epi (tensorPullbackChartIso C G i).hom).mp
  simp only [Over.comp_left, Category.assoc]
  rw [tensorPullbackChartIso_hom_map_assoc]
  simp only [gluedAction, OverClass.asOverHom_left]
  erw [Scheme.OpenCover.map_glueMorphismsOverOfLocallyDirected_left]
  intro i j h
  letI := htrans h
  rw [← Category.assoc, tensorPullbackChartIso_naturality C, Category.assoc]
  have heq : (γ[G,(C.X i).asOver S]).left ≫ C.trans h =
      (G ◁ (C.trans h).asOver S).left ≫ (γ[G,(C.X j).asOver S]).left := by
    simpa only [Over.comp_left, OverClass.asOverHom_left,
      selfLeftAction_actionObj, selfLeftAction_actionHomRight,
      OverClass.asOver_left] using
      congrArg (fun z => z.left)
        (IsModHom.smul_hom (A := G) (f := (C.trans h).asOver S))
  simpa only [Category.assoc, C.trans_map] using
    congrArg (fun f => (tensorPullbackChartIso C G i).hom ≫ f ≫ C.f j) heq.symm

/-- Unit and multiplication laws descend from the actual chart laws. -/
def gluedModObj : ModObj G (X.asOver S) where
  smul := gluedAction C G htrans
  one_smul := by
    change (η[G] ▷ X.asOver S) ≫ gluedAction C G htrans =
      (λ_ (X.asOver S)).hom
    apply tensorCover_hom_ext C (𝟙_ (Over S)) (X.asOver S)
    intro i
    rw [whisker_exchange_assoc, gluedAction_restrict C,
      ← Category.assoc, ModObj.one_smul_self, leftUnitor_naturality]
  mul_smul := by
    change (μ[G] ▷ X.asOver S) ≫ gluedAction C G htrans =
      (α_ G G (X.asOver S)).hom ≫
        (G ◁ gluedAction C G htrans) ≫ gluedAction C G htrans
    apply tensorCover_hom_ext C (G ⊗ G) (X.asOver S)
    intro i
    rw [whisker_exchange_assoc, gluedAction_restrict C,
      ← Category.assoc, ModObj.mul_smul_self, Category.assoc]
    rw [associator_naturality_right_assoc]
    rw [← whiskerLeft_comp_assoc, gluedAction_restrict C, whiskerLeft_comp]
    simp only [Category.assoc]
    rw [gluedAction_restrict C]

/-- Every chart inclusion is equivariant for the descended action. -/
theorem gluedModObj_chart (i : C.I₀) :
    letI := gluedModObj C G htrans
    IsModHom G ((C.f i).asOver S) := by
  letI := gluedModObj C G htrans
  refine ⟨?_⟩
  change γ[G,(C.X i).asOver S] ≫ (C.f i).asOver S =
    (G ◁ (C.f i).asOver S) ≫ gluedAction C G htrans
  exact (gluedAction_restrict C G htrans i).symm

end Actions

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.gluedModObj
end
-- END PaperVerification.ToricActionGluing
end

#eval "TORIC_DICTIONARY_PART_10_EOF"
