module

public import Lean.Elab.BuiltinEvalCommand
public meta import Lean.Elab.BuiltinEvalCommand
public import Lean.Util.CollectAxioms
public meta import Lean.Util.CollectAxioms
public import Lean.Util.FoldConsts
public meta import Lean.Util.FoldConsts
public import Mathlib.Algebra.Order.Group.PiLex
public import Mathlib.AlgebraicGeometry.Cover.Directed
public import Mathlib.AlgebraicGeometry.Cover.Over
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Mathlib.CategoryTheory.Monoidal.Mod
public import Mathlib.Data.Finset.Max
public import paper_verification.toric010
public import paper_verification.toric022

@[expose] public section


-- BEGIN ORIGINAL PaperVerification.ToricFanCharacters
section Source_ToricFanCharacters

-- original header: module

-- original header: public import PaperVerification.ToricFanSchemeIntegral
-- original header: public import PaperVerification.ToricFunctionFieldBridge

-- original header: @[expose] public section

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
end Source_ToricFanCharacters
-- END ORIGINAL PaperVerification.ToricFanCharacters


-- BEGIN ORIGINAL PaperVerification.ToricFanCartierCocycle
section Source_ToricFanCartierCocycle

-- original header: module

-- original header: public import PaperVerification.ToricFanCharacters
-- original header: public import PaperVerification.ToricCartierCocycle

-- original header: @[expose] public section

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
end Source_ToricFanCartierCocycle
-- END ORIGINAL PaperVerification.ToricFanCartierCocycle


-- BEGIN ORIGINAL PaperVerification.ToricFanSectionValues
section Source_ToricFanSectionValues

-- original header: module

-- original header: public import PaperVerification.ToricFanCartierCocycle
-- original header: public import PaperVerification.ToricCartierCharacterModules
-- original header: public import PaperVerification.ToricCartierBaseSections

-- original header: @[expose] public section

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
end Source_ToricFanSectionValues
-- END ORIGINAL PaperVerification.ToricFanSectionValues


-- BEGIN ORIGINAL PaperVerification.ToricFanCartierFrames
section Source_ToricFanCartierFrames

-- original header: module

-- original header: public import PaperVerification.ToricCartierChartValues
-- original header: public import PaperVerification.ToricFanSectionValues
-- original header: public import PaperVerification.ToricChartPicard

-- original header: @[expose] public section

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
end Source_ToricFanCartierFrames
-- END ORIGINAL PaperVerification.ToricFanCartierFrames


-- BEGIN ORIGINAL PaperVerification.ToricFanRegularCharacters
section Source_ToricFanRegularCharacters

-- original header: module

-- original header: public import PaperVerification.ToricFanCartierFrames

-- original header: @[expose] public section

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
end Source_ToricFanRegularCharacters
-- END ORIGINAL PaperVerification.ToricFanRegularCharacters


-- BEGIN ORIGINAL PaperVerification.ToricLaurentUnits
section Source_ToricLaurentUnits

-- original header: module

-- original header: public import PaperVerification.ToricLaurentPicard
-- original header: public import Mathlib.Algebra.Order.Group.PiLex
-- original header: public import Mathlib.Data.Finset.Max

-- original header: @[expose] public section

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
end Source_ToricLaurentUnits
-- END ORIGINAL PaperVerification.ToricLaurentUnits


-- BEGIN ORIGINAL PaperVerification.ToricArbitraryCartierFan
section Source_ToricArbitraryCartierFan

-- original header: module

-- original header: public import PaperVerification.ToricFanRegularCharacters
-- original header: public import PaperVerification.ToricFanIntegralCoefficients
-- original header: public import PaperVerification.ToricLaurentUnits
-- original header: public import PaperVerification.ToricCartierRangeEquality

-- original header: @[expose] public section

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
end Source_ToricArbitraryCartierFan
-- END ORIGINAL PaperVerification.ToricArbitraryCartierFan


-- BEGIN ORIGINAL PaperVerification.ToricCartierAmpleDescent
section Source_ToricCartierAmpleDescent

-- original header: module

-- original header: public import PaperVerification.ToricArbitraryCartierFan

-- original header: @[expose] public section

/-!
# Intrinsic ampleness is independent of Cartier presentation

The proof transports the actual positive-power sections and proves equality
of their genuine nonvanishing open subsets. Thus the intrinsic affine-open
criterion is preserved by the established equality of fractional sheaves.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace PaperVerification.ToricSchemes.RationalCartierCocycle

variable {X : Scheme.{u}} [IsIntegral X] (C D : RationalCartierCocycle X)

theorem mem_nonvanishingOpen_iff_rational (i : C.index) (s : Γ(C.sheaf,⊤))
    (x : X) (hxi : x∈C.openSet i) :
    x∈C.nonvanishingOpen s ↔
      C.toCartierData.sectionValue ⊤ s≠0 ∧
        (C.generator i : X.functionField)/C.toCartierData.sectionValue ⊤ s ∈
          regularAtSubring X x := by
  rw [C.mem_nonvanishingOpen_iff i s x hxi,
    ← X.mem_basicOpen (C.localCoefficient i s) x hxi,
    C.mem_localNonvanishing_iff i s x hxi]

/-- The actual section iso preserving fractional values preserves the
ordinary nonvanishing open, including at zeros of the section. -/
theorem nonvanishingOpen_sameGenerator
    (hCD : C.GeneratorRatioRegular D) (hDC : D.GeneratorRatioRegular C)
    (s : Γ(C.sheaf,⊤)) :
    D.nonvanishingOpen (C.sameGeneratorSheafLinearEquiv D hCD hDC ⊤ s) =
      C.nonvanishingOpen s := by
  ext x
  change x∈D.nonvanishingOpen (C.sameGeneratorSheafLinearEquiv D hCD hDC ⊤ s) ↔
    x∈C.nonvanishingOpen s
  obtain ⟨i,hxi⟩ := C.covers x
  obtain ⟨j,hxj⟩ := D.covers x
  rw [D.mem_nonvanishingOpen_iff_rational j _ x hxj,
    C.mem_nonvanishingOpen_iff_rational i s x hxi]
  have hv : D.toCartierData.sectionValue ⊤
      (C.sameGeneratorSheafLinearEquiv D hCD hDC ⊤ s) =
        C.toCartierData.sectionValue ⊤ s := rfl
  rw [hv]
  constructor
  · rintro ⟨hr,h⟩
    refine ⟨hr,?_⟩
    have hh := (regularAtSubring X x).mul_mem (hCD i j x hxi hxj) h
    have he : ((C.generator i : X.functionField)/(D.generator j : X.functionField)) *
        ((D.generator j : X.functionField)/C.toCartierData.sectionValue ⊤ s) =
        (C.generator i : X.functionField)/C.toCartierData.sectionValue ⊤ s := by
      field_simp [Units.ne_zero,hr]
    simpa only [he] using hh
  · rintro ⟨hr,h⟩
    refine ⟨hr,?_⟩
    have hh := (regularAtSubring X x).mul_mem (hDC j i x hxj hxi) h
    have he : ((D.generator j : X.functionField)/(C.generator i : X.functionField)) *
        ((C.generator i : X.functionField)/C.toCartierData.sectionValue ⊤ s) =
        (D.generator j : X.functionField)/C.toCartierData.sectionValue ⊤ s := by
      field_simp [Units.ne_zero,hr]
    simpa only [he] using hh

theorem isAmple_of_generatorRatios
    (hCD : C.GeneratorRatioRegular D) (hDC : D.GeneratorRatioRegular C)
    (hC : C.IsAmple) : D.IsAmple := by
  refine ⟨hC.1,?_⟩
  intro x
  obtain ⟨n,hn,s,hx,ha⟩ := hC.2 x
  let hpowCD := GeneratorRatioRegular.pow C D hCD n
  let hpowDC := GeneratorRatioRegular.pow D C hDC n
  let t := (C.pow n).sameGeneratorSheafLinearEquiv (D.pow n) hpowCD hpowDC ⊤ s
  have hopen : (D.pow n).nonvanishingOpen t=(C.pow n).nonvanishingOpen s :=
    (C.pow n).nonvanishingOpen_sameGenerator (D.pow n) hpowCD hpowDC s
  exact ⟨n,hn,t,by simpa only [hopen] using hx,by simpa only [hopen] using ha⟩

theorem isAmple_iff_of_generatorRatios
    (hCD : C.GeneratorRatioRegular D) (hDC : D.GeneratorRatioRegular C) :
    C.IsAmple ↔ D.IsAmple :=
  ⟨C.isAmple_of_generatorRatios D hCD hDC,D.isAmple_of_generatorRatios C hDC hCD⟩

end PaperVerification.ToricSchemes.RationalCartierCocycle

namespace PaperVerification.ToricSchemes.CartierData

variable {X : Scheme.{u}} [IsIntegral X] (D E : CartierData X)

theorem isAmple_iff_of_equivalent (h : D.Equivalent E) : D.IsAmple ↔ E.IsAmple :=
  D.localCocycle.isAmple_iff_of_generatorRatios E.localCocycle
    (D.localCocycle_generatorRatios E h)
    (E.localCocycle_generatorRatios D (D.equivalent_symm E h))

end PaperVerification.ToricSchemes.CartierData

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open PaperVerification.ToricSchemes

variable {n : ℕ} («Σ» : SmoothCompleteFan n) (k : Type u) [Field k]

/-- The recovered integral invariant divisor preserves the original
intrinsic ampleness condition on the actual scheme. -/
theorem fanCartier_isAmple_iff (hpure : «Σ».IsPure)
    (D : CartierData («Σ».fanScheme k)) :
    («Σ».fanCartierData k hpure («Σ».cartierCoefficients k hpure D)).IsAmple ↔ D.IsAmple := by
  rw [← («Σ».normalizedCartier k D).isAmple_iff_of_equivalent _
    («Σ».normalizedCartier_equivalent_fanCartier k hpure D)]
  exact «Σ».normalizedCartier_isAmple_iff k D

end PaperVerification.ToricGeometry.SmoothCompleteFan

#print axioms PaperVerification.ToricSchemes.CartierData.isAmple_iff_of_equivalent
#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.fanCartier_isAmple_iff
end
end Source_ToricCartierAmpleDescent
-- END ORIGINAL PaperVerification.ToricCartierAmpleDescent


-- BEGIN ORIGINAL PaperVerification.ToricActionGluing
section Source_ToricActionGluing

-- original header: module

-- original header: public import Mathlib.CategoryTheory.Monoidal.Mod
-- original header: public import Mathlib.AlgebraicGeometry.Cover.Directed
-- original header: public import Mathlib.AlgebraicGeometry.Cover.Over
-- original header: public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

-- original header: @[expose] public section

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
end Source_ToricActionGluing
-- END ORIGINAL PaperVerification.ToricActionGluing


-- BEGIN ORIGINAL PaperVerification.ToricChartActions
section Source_ToricChartActions

-- original header: module

-- original header: public import PaperVerification.ToricTorusAction
-- original header: public import PaperVerification.ToricChartOpenImmersions

-- original header: @[expose] public section

/-!
# Equivariance of the actual affine chart inclusions

The chart subalgebra and its semigroup algebra are identified by the
proved range equivalence. The action is transported across that actual
affine scheme isomorphism. Face maps are equivariant because they arise
from semigroup homomorphisms commuting with inclusion in the character
lattice. All actions and equations are in schemes over Spec(k).
-/

noncomputable section

universe u v

open CategoryTheory MonoidalCategory MonObj

namespace PaperVerification.ToricSchemes

section Categorical

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
    {T A B : C} [MonObj T] [MonObj A] [MonObj B]

/-- A commuting triangle of monoid maps is equivariant for the
restrictions of the actual regular monoid actions. -/
theorem restrictedRegular_isModHom (iA : T ⟶ A) (iB : T ⟶ B) (f : A ⟶ B)
    [IsMonHom iA] [IsMonHom iB] [IsMonHom f] (h : iA ≫ f = iB) :
    letI : ModObj A A := ModObj.regular A
    letI : ModObj B B := ModObj.regular B
    letI : ModObj T A := Mod.scalarRestriction iA A
    letI : ModObj T B := Mod.scalarRestriction iB B
    IsModHom T f := by
  letI : ModObj A A := ModObj.regular A
  letI : ModObj B B := ModObj.regular B
  letI : ModObj T A := Mod.scalarRestriction iA A
  letI : ModObj T B := Mod.scalarRestriction iB B
  refine ⟨?_⟩
  change (iA ▷ A ≫ μ[A]) ≫ f = T ◁ f ≫ (iB ▷ B ≫ μ[B])
  calc
    (iA ▷ A ≫ μ[A]) ≫ f = (iA ⊗ₘ 𝟙 A) ≫ (f ⊗ₘ f) ≫ μ[B] := by
      rw [Category.assoc, IsMonHom.mul_hom, tensorHom_id]
    _ = (iB ⊗ₘ f) ≫ μ[B] := by
      rw [← Category.assoc, tensorHom_comp_tensorHom, h, Category.id_comp]
    _ = _ := by rw [tensorHom_def', Category.assoc]

end Categorical

open AlgebraicGeometry Opposite
open PaperVerification.ToricCharacters

variable (k : Type (max u v)) [CommRing k] {M : Type v} [AddCommGroup M]

def semigroupFaceMapOver {S T : AddSubmonoid M} (hST : S≤T) :
    semigroupChartOver k T ⟶ semigroupChartOver k S :=
  (algSpec (CommRingCat.of k)).map
    (CommAlgCat.ofHom (AddMonoidAlgebra.mapDomainBialgHom k
      (AddSubmonoid.inclusion hST)).toAlgHom).op

instance semigroupFaceMapOver_isMonHom {S T : AddSubmonoid M} (hST : S≤T) :
    IsMonHom (semigroupFaceMapOver k hST) := by
  change IsMonHom (((bialgSpec (CommRingCat.of k)).map
    (CommBialgCat.ofHom (AddMonoidAlgebra.mapDomainBialgHom k
      (AddSubmonoid.inclusion hST))).op).hom)
  infer_instance

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem torusToSemigroupChartOver_faceMap {S T : AddSubmonoid M} (hST : S≤T) :
    torusToSemigroupChartOver k T ≫ semigroupFaceMapOver k hST =
      torusToSemigroupChartOver k S := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom
      (AddMonoidAlgebra.mapDomainBialgHom k T.subtype).toAlgHom.toRingHom) ≫
      Spec.map (CommRingCat.ofHom
        (AddMonoidAlgebra.mapDomainBialgHom k
          (AddSubmonoid.inclusion hST)).toAlgHom.toRingHom) =
    Spec.map (CommRingCat.ofHom
      (AddMonoidAlgebra.mapDomainBialgHom k S.subtype).toAlgHom.toRingHom)
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro f
  change AddMonoidAlgebra.mapDomainBialgHom k T.subtype
      (AddMonoidAlgebra.mapDomainBialgHom k (AddSubmonoid.inclusion hST) f) =
    AddMonoidAlgebra.mapDomainBialgHom k S.subtype f
  rw [AddMonoidAlgebra.mapDomainBialgHom_mapDomainBialgHom]
  rfl

instance semigroupFaceMapOver_isModHom {S T : AddSubmonoid M} (hST : S≤T) :
    IsModHom (splitTorusOver k M) (semigroupFaceMapOver k hST) :=
  restrictedRegular_isModHom (torusToSemigroupChartOver k T)
    (torusToSemigroupChartOver k S) (semigroupFaceMapOver k hST)
    (torusToSemigroupChartOver_faceMap k hST)

instance monoidChartScheme_isOver (S : AddSubmonoid M) :
    (monoidChartScheme k S).Over (Spec (CommRingCat.of k)) := by
  dsimp only [monoidChartScheme]
  infer_instance

abbrev monoidChartSchemeOver (S : AddSubmonoid M) : Over (Spec (CommRingCat.of k)) :=
  (monoidChartScheme k S).asOver (Spec (CommRingCat.of k))

/-- The actual chart subalgebra spectrum is isomorphic over k to the
semigroup spectrum. Contravariance gives this displayed direction. -/
def monoidChartSchemeOverIso (S : AddSubmonoid M) :
    monoidChartSchemeOver k S ≅ semigroupChartOver k S :=
  (algSpec (CommRingCat.of k)).mapIso
    (CommAlgCat.isoMk (monoidChartAlgebraEquiv k S)).op

instance monoidChartScheme_torusAction (S : AddSubmonoid M) :
    ModObj (splitTorusOver k M) (monoidChartSchemeOver k S) := by
  letI : IsMonHom (Iso.refl (splitTorusOver k M)).hom := by
    change IsMonHom (𝟙 (splitTorusOver k M))
    infer_instance
  exact ModObj.ofIso (Iso.refl (splitTorusOver k M)) (monoidChartSchemeOverIso k S).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
instance monoidChartSchemeOverIso_isModHom (S : AddSubmonoid M) :
    IsModHom (splitTorusOver k M) (monoidChartSchemeOverIso k S).hom where
  smul_hom := by
    change ((𝟙 _ ⊗ₘ (monoidChartSchemeOverIso k S).hom) ≫
      γ[splitTorusOver k M,semigroupChartOver k S] ≫
        (monoidChartSchemeOverIso k S).inv) ≫
      (monoidChartSchemeOverIso k S).hom = _
    simp

instance monoidChartSpecMap_isOver {S T : AddSubmonoid M} (hST : S≤T) :
    (monoidChartSpecMap k hST).IsOver (Spec (CommRingCat.of k)) := by
  constructor
  change Spec.map (CommRingCat.ofHom (monoidChartInclusion k hST).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k (monoidChartAlgebra k S))) =
    Spec.map (CommRingCat.ofHom (algebraMap k (monoidChartAlgebra k T)))
  rw [← Spec.map_comp]
  congr 1

abbrev monoidChartSpecMapOver {S T : AddSubmonoid M} (hST : S≤T) :
    monoidChartSchemeOver k T ⟶ monoidChartSchemeOver k S :=
  (monoidChartSpecMap k hST).asOver (Spec (CommRingCat.of k))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem monoidChartSpecMapOver_conjugate {S T : AddSubmonoid M} (hST : S≤T) :
    monoidChartSpecMapOver k hST =
      (monoidChartSchemeOverIso k T).hom ≫ semigroupFaceMapOver k hST ≫
        (monoidChartSchemeOverIso k S).inv := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom (monoidChartInclusion k hST).toRingHom) =
    Spec.map (CommRingCat.ofHom (monoidChartAlgebraEquiv k T).toRingHom) ≫
      Spec.map (CommRingCat.ofHom
        (AddMonoidAlgebra.mapDomainBialgHom k
          (AddSubmonoid.inclusion hST)).toAlgHom.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (monoidChartAlgebraEquiv k S).symm.toRingHom)
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro f
  change monoidChartInclusion k hST f =
    monoidChartAlgebraEquiv k T
      (AddMonoidAlgebra.mapDomainBialgHom k (AddSubmonoid.inclusion hST)
        ((monoidChartAlgebraEquiv k S).symm f))
  apply Subtype.ext
  obtain ⟨g,rfl⟩ := (monoidChartAlgebraEquiv k S).surjective f
  rw [AlgEquiv.symm_apply_apply]
  change AddMonoidAlgebra.mapDomainBialgHom k S.subtype g =
    AddMonoidAlgebra.mapDomainBialgHom k T.subtype
      (AddMonoidAlgebra.mapDomainBialgHom k (AddSubmonoid.inclusion hST) g)
  rw [AddMonoidAlgebra.mapDomainBialgHom_mapDomainBialgHom]
  rfl

/-- Literal face inclusions of actual chart spectra are equivariant. -/
instance monoidChartSpecMapOver_isModHom {S T : AddSubmonoid M} (hST : S≤T) :
    IsModHom (splitTorusOver k M) (monoidChartSpecMapOver k hST) := by
  rw [monoidChartSpecMapOver_conjugate]
  infer_instance

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.monoidChartSpecMapOver_isModHom
end
end Source_ToricChartActions
-- END ORIGINAL PaperVerification.ToricChartActions


-- BEGIN ORIGINAL PaperVerification.ToricFanAction
section Source_ToricFanAction

-- original header: module

-- original header: public import PaperVerification.ToricActionGluing
-- original header: public import PaperVerification.ToricChartActions
-- original header: public import PaperVerification.ToricFanCharacters

-- original header: @[expose] public section

/-!
# The actual split-torus action on the glued fan scheme

Every chart action is the spectrum of the character coaction. Its face
inclusions are equivariant, and the actual directed affine open cover
glues these maps into a group-scheme action. The embedded dense torus
inherits its genuine multiplication map.
-/

noncomputable section

universe u

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open MonoidalCategory MonObj
open PaperVerification.ToricCharacters PaperVerification.ToricSchemes

theorem action_extends_mul_comp {C : Type*} [Category C] [MonoidalCategory C]
    (G A B : C) [MonObj G] [ModObj G A] [ModObj G B]
    (f : G ⟶ A) (g : A ⟶ B) [IsModHom G g]
    (hf : μ[G] ≫ f = G ◁ f ≫ γ[G,A]) :
    μ[G] ≫ (f ≫ g) = G ◁ (f ≫ g) ≫ γ[G,B] := by
  have hg : γ[G,A] ≫ g = G ◁ g ≫ γ[G,B] :=
    IsModHom.smul_hom (A := G) (f := g)
  calc
    μ[G] ≫ (f ≫ g) = (μ[G] ≫ f) ≫ g := (Category.assoc _ _ _).symm
    _ = (G ◁ f ≫ γ[G,A]) ≫ g := congrArg (fun h => h ≫ g) hf
    _ = G ◁ f ≫ (γ[G,A] ≫ g) := Category.assoc _ _ _
    _ = G ◁ f ≫ (G ◁ g ≫ γ[G,B]) := congrArg (fun h => G ◁ f ≫ h) hg
    _ = (G ◁ f ≫ G ◁ g) ≫ γ[G,B] := (Category.assoc _ _ _).symm
    _ = G ◁ (f ≫ g) ≫ γ[G,B] :=
      congrArg (fun h => h ≫ γ[G,B]) (whiskerLeft_comp G f g).symm

variable {n : ℕ} («Σ» : SmoothCompleteFan n) (k : Type u) [CommRing k]

instance coneChart_isOver (s : Finset (Lattice n)) :
    (coneChart k s).Over (Spec (CommRingCat.of k)) := by
  change (monoidChartScheme k (dualConeMonoid s)).Over _
  infer_instance

instance coneChartFaceMap_isOver {s t : Finset (Lattice n)} (hts : t ⊆ s) :
    (coneChartFaceMap k hts).IsOver (Spec (CommRingCat.of k)) := by
  change (monoidChartSpecMap k (dualConeMonoid_antitone hts)).IsOver _
  infer_instance

/-- The actual structure morphism to the field spectrum is glued from
its specified algebra structures on every semigroup chart. -/
def fanSchemeBaseCocone : Cocone («Σ».coneDiagram k) where
  pt := Spec (CommRingCat.of k)
  «ι» := {
    app := fun s => coneChart k s.val ↘ Spec (CommRingCat.of k)
    naturality := by
      intro s t h
      change coneChartFaceMap k (leOfHom h) ≫
        (coneChart k t.val ↘ Spec (CommRingCat.of k)) =
          (coneChart k s.val ↘ Spec (CommRingCat.of k)) ≫ 𝟙 _
      simpa only [Category.comp_id] using
        (comp_over (coneChartFaceMap k (leOfHom h)) (Spec (CommRingCat.of k))) }

def fanSchemeStructureMap : «Σ».fanScheme k ⟶ Spec (CommRingCat.of k) :=
  colimit.desc («Σ».coneDiagram k) («Σ».fanSchemeBaseCocone k)

instance fanScheme_isOver : («Σ».fanScheme k).Over (Spec (CommRingCat.of k)) where
  hom := «Σ».fanSchemeStructureMap k

instance fanChartMap_isOver (s : «Σ».ConeIndex) :
    («Σ».fanChartMap k s).IsOver (Spec (CommRingCat.of k)) where
  comp_over := by
    change colimit.ι («Σ».coneDiagram k) s ≫
      colimit.desc («Σ».coneDiagram k) («Σ».fanSchemeBaseCocone k) = _
    exact colimit.ι_desc («Σ».fanSchemeBaseCocone k) s

instance fanSchemeOpenCover_preorder : Preorder («Σ».fanSchemeOpenCover k).I₀ :=
  inferInstanceAs (Preorder «Σ».ConeIndex)

instance fanSchemeOpenCover_category : Category («Σ».fanSchemeOpenCover k).I₀ :=
  inferInstanceAs (Category «Σ».ConeIndex)

instance fanSchemeOpenCover_isOver :
    («Σ».fanSchemeOpenCover k).Over (Spec (CommRingCat.of k)) where
  over s := coneChart_isOver k s.val
  isOver_map s := «Σ».fanChartMap_isOver k s

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The common-face pullback supplies actual local directedness of the
chosen affine cover, including its residue-field-compatible point lifting. -/
instance fanSchemeOpenCover_locallyDirected : («Σ».fanSchemeOpenCover k).LocallyDirected where
  trans {s t} h := coneChartFaceMap k (leOfHom h)
  trans_id s := coneChartFaceMap_self k s.val
  trans_comp hst htu := (coneChartFaceMap_comp k (leOfHom htu) (leOfHom hst)).symm
  w h := «Σ».fanChartMap_naturality k (leOfHom h)
  directed {s t} x := by
    let l : «Σ».ConeIndex :=
      ⟨t.val ∩ s.val, «Σ».downward t.val t.property _ Finset.inter_subset_left⟩
    let H := «Σ».fanChart_inter_isPullback k t s
    refine ⟨l,homOfLE Finset.inter_subset_right,homOfLE Finset.inter_subset_left,
      H.isoPullback.inv x,?_⟩
    have heq : pullback.lift
        (coneChartFaceMap k (Finset.inter_subset_right : t.val∩s.val ⊆ s.val))
        (coneChartFaceMap k (Finset.inter_subset_left : t.val∩s.val ⊆ t.val))
        ((«Σ».fanChartMap_naturality k (s := l) (t := s)
          Finset.inter_subset_right).trans
            («Σ».fanChartMap_naturality k (s := l) (t := t)
              Finset.inter_subset_left).symm) =
        H.isoPullback.hom := by
      apply pullback.hom_ext <;> simp
    change (pullback.lift
      (coneChartFaceMap k (Finset.inter_subset_right : t.val∩s.val ⊆ s.val))
      (coneChartFaceMap k (Finset.inter_subset_left : t.val∩s.val ⊆ t.val)) _)
        (H.isoPullback.inv x) = x
    have hpoint := congrArg
      (fun f : coneChart k (t.val∩s.val) ⟶
        pullback («Σ».fanChartMap k s) («Σ».fanChartMap k t) =>
          f (H.isoPullback.inv x)) heq
    have hcancel := congrArg
      (fun f : pullback («Σ».fanChartMap k s) («Σ».fanChartMap k t) ⟶
        pullback («Σ».fanChartMap k s) («Σ».fanChartMap k t) => f x)
      H.isoPullback.inv_hom_id
    change H.isoPullback.hom (H.isoPullback.inv x) = x at hcancel
    exact hpoint.trans hcancel
  property_trans {s t} h :=
    «Σ».coneChartFaceMap_isOpenImmersion k t.val s.val t.property (leOfHom h)

abbrev fanSchemeOver : Over (Spec (CommRingCat.of k)) :=
  («Σ».fanScheme k).asOver (Spec (CommRingCat.of k))

instance coneChart_torusAction (s : Finset (Lattice n)) :
    ModObj (ToricSchemes.splitTorusOver k (Lattice n))
      ((coneChart k s).asOver (Spec (CommRingCat.of k))) := by
  change ModObj (ToricSchemes.splitTorusOver k (Lattice n))
    (monoidChartSchemeOver k (dualConeMonoid s))
  infer_instance

instance coneChartFaceMap_isModHom {s t : Finset (Lattice n)} (hts : t ⊆ s) :
    IsModHom (ToricSchemes.splitTorusOver k (Lattice n))
      ((coneChartFaceMap k hts).asOver (Spec (CommRingCat.of k))) := by
  change IsModHom (ToricSchemes.splitTorusOver k (Lattice n))
    (monoidChartSpecMapOver k (dualConeMonoid_antitone hts))
  infer_instance

/-- Genuine action of the split group scheme on the actual glued scheme. -/
instance fanScheme_torusAction :
    ModObj (ToricSchemes.splitTorusOver k (Lattice n)) («Σ».fanSchemeOver k) := by
  letI : ∀ i : («Σ».fanSchemeOpenCover k).I₀,
      ModObj (ToricSchemes.splitTorusOver k (Lattice n))
        (((«Σ».fanSchemeOpenCover k).X i).asOver (Spec (CommRingCat.of k))) :=
    fun i => coneChart_torusAction k i.val
  exact gluedModObj («Σ».fanSchemeOpenCover k)
    (ToricSchemes.splitTorusOver k (Lattice n)) (fun {i j} h => by
      change IsModHom (ToricSchemes.splitTorusOver k (Lattice n))
        ((coneChartFaceMap k (leOfHom h)).asOver (Spec (CommRingCat.of k)))
      exact coneChartFaceMap_isModHom k (leOfHom h))

instance fanChartMap_isModHom (s : «Σ».ConeIndex) :
    IsModHom (ToricSchemes.splitTorusOver k (Lattice n))
      ((«Σ».fanChartMap k s).asOver (Spec (CommRingCat.of k))) := by
  letI : ∀ i : («Σ».fanSchemeOpenCover k).I₀,
      ModObj (ToricSchemes.splitTorusOver k (Lattice n))
        (((«Σ».fanSchemeOpenCover k).X i).asOver (Spec (CommRingCat.of k))) :=
    fun i => coneChart_torusAction k i.val
  exact gluedModObj_chart («Σ».fanSchemeOpenCover k)
    (ToricSchemes.splitTorusOver k (Lattice n)) (fun {i j} h => by
      change IsModHom (ToricSchemes.splitTorusOver k (Lattice n))
        ((coneChartFaceMap k (leOfHom h)).asOver (Spec (CommRingCat.of k)))
      exact coneChartFaceMap_isModHom k (leOfHom h)) s

/-- Actual torus-to-chart morphism, with its specified algebra map. -/
def torusChartMapOver («Σ» : SmoothCompleteFan n) (s : Finset (Lattice n)) :
    ToricSchemes.splitTorusOver k (Lattice n) ⟶
      (coneChart k s).asOver (Spec (CommRingCat.of k)) :=
  torusToSemigroupChartOver k (dualConeMonoid s) ≫
    (monoidChartSchemeOverIso k (dualConeMonoid s)).inv

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc] theorem torusChartMapOver_action (s : Finset (Lattice n)) :
    μ[ToricSchemes.splitTorusOver k (Lattice n)] ≫ «Σ».torusChartMapOver k s =
      ToricSchemes.splitTorusOver k (Lattice n) ◁ «Σ».torusChartMapOver k s ≫
        γ[ToricSchemes.splitTorusOver k (Lattice n),
          (coneChart k s).asOver (Spec (CommRingCat.of k))] := by
  change μ[ToricSchemes.splitTorusOver k (Lattice n)] ≫
      (torusToSemigroupChartOver k (dualConeMonoid s) ≫
        (monoidChartSchemeOverIso k (dualConeMonoid s)).inv) =
    ToricSchemes.splitTorusOver k (Lattice n) ◁
      (torusToSemigroupChartOver k (dualConeMonoid s) ≫
        (monoidChartSchemeOverIso k (dualConeMonoid s)).inv) ≫
      γ[ToricSchemes.splitTorusOver k (Lattice n),
        monoidChartSchemeOver k (dualConeMonoid s)]
  apply action_extends_mul_comp
  simpa only [id_tensorHom] using
    (semigroupChart_action_extends_torus k (dualConeMonoid s)).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem torusChartMapOver_zero :
    («Σ».torusChartMapOver k (∅ : Finset (Lattice n))).left =
      (zeroConeChartIso k n).inv := by
  change Spec.map (CommRingCat.ofHom (monoidChartMap k (dualConeMonoid ∅)).toRingHom) ≫
      Spec.map (CommRingCat.ofHom
        (monoidChartAlgebraEquiv k (dualConeMonoid ∅)).symm.toRingHom) =
    Spec.map (CommRingCat.ofHom (zeroConeChartAlgEquiv k n).toRingHom)
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro f
  exact congrArg Subtype.val
    ((monoidChartAlgebraEquiv k (dualConeMonoid (∅ : Finset (Lattice n)))).apply_symm_apply f)

instance geometricSplitTorus_isOver :
    (PaperVerification.ToricGeometry.splitTorus k n).Over (Spec (CommRingCat.of k)) := by
  change (ToricSchemes.splitTorus k (Lattice n)).Over _
  infer_instance

instance torusOpenMap_isOver :
    («Σ».torusOpenMap k).IsOver (Spec (CommRingCat.of k)) := by
  change («Σ».fanChartMap k «Σ».zeroConeIndex).IsOver _
  exact «Σ».fanChartMap_isOver k «Σ».zeroConeIndex

instance splitTorusOpenMap_isOver :
    («Σ».splitTorusOpenMap k).IsOver (Spec (CommRingCat.of k)) := by
  constructor
  change ((zeroConeChartIso k n).inv ≫ «Σ».torusOpenMap k) ≫
      («Σ».fanScheme k ↘ Spec (CommRingCat.of k)) = _
  rw [Category.assoc,comp_over]
  exact (congrArg (fun f => f ≫ (coneChart k (∅ : Finset (Lattice n)) ↘
    Spec (CommRingCat.of k))) («Σ».torusChartMapOver_zero k).symm).trans
      (Over.w («Σ».torusChartMapOver k ∅))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The global action restricts to the actual torus multiplication.
This equality is over Spec(k), not just on k-rational points. -/
theorem fanScheme_action_extends_torus :
    μ[ToricSchemes.splitTorusOver k (Lattice n)] ≫
        («Σ».splitTorusOpenMap k).asOver (Spec (CommRingCat.of k)) =
      ToricSchemes.splitTorusOver k (Lattice n) ◁
        («Σ».splitTorusOpenMap k).asOver (Spec (CommRingCat.of k)) ≫
          γ[ToricSchemes.splitTorusOver k (Lattice n),«Σ».fanSchemeOver k] := by
  have hmap : («Σ».splitTorusOpenMap k).asOver (Spec (CommRingCat.of k)) =
      «Σ».torusChartMapOver k ∅ ≫
        («Σ».fanChartMap k «Σ».zeroConeIndex).asOver (Spec (CommRingCat.of k)) := by
    apply Over.OverMorphism.ext
    change (zeroConeChartIso k n).inv ≫ «Σ».torusOpenMap k =
      («Σ».torusChartMapOver k ∅).left ≫ «Σ».fanChartMap k «Σ».zeroConeIndex
    rw [«Σ».torusChartMapOver_zero]
    rfl
  erw [hmap]
  exact action_extends_mul_comp
    (ToricSchemes.splitTorusOver k (Lattice n))
    ((coneChart k ∅).asOver (Spec (CommRingCat.of k))) («Σ».fanSchemeOver k)
    («Σ».torusChartMapOver k ∅)
    ((«Σ».fanChartMap k «Σ».zeroConeIndex).asOver (Spec (CommRingCat.of k)))
    («Σ».torusChartMapOver_action k ∅)

end PaperVerification.ToricGeometry.SmoothCompleteFan

#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.fanScheme_torusAction
#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.fanScheme_action_extends_torus
end
end Source_ToricFanAction
-- END ORIGINAL PaperVerification.ToricFanAction


-- BEGIN ORIGINAL PaperVerification.ToricFanSectionCoordinates
section Source_ToricFanSectionCoordinates

-- original header: module

-- original header: public import PaperVerification.ToricArbitraryCartierFan
-- original header: public import PaperVerification.ToricFanAction
-- original header: public import PaperVerification.ToricBaseSectionNaturality

-- original header: @[expose] public section

/-!
# The actual base-linear character coordinates of global sections

The scalar maps are induced by the actual structural morphism to Spec(k).
The resulting isomorphism therefore concerns the ordinary vector space
of genuine global sections over the base field, with its true rational
value map.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Opposite



namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open PaperVerification.ToricCharacters PaperVerification.ToricSchemes
open scoped BaseSections Classical

variable {n : ℕ} («Σ» : SmoothCompleteFan n) (k : Type u) [Field k]

local instance fanSectionCoordinates_splitTorus_integral : IsIntegral (ToricGeometry.splitTorus k n) := by
  letI := torusCoordinateRing_isDomain k n
  change IsIntegral (Spec (CommRingCat.of (torusCoordinateRing k n)))
  infer_instance

/-- Constants in the character algebra agree with constants from the
actual structural morphism of the glued scheme. -/
theorem rationalScalar_eq_algebraMap (c : k) :
    «Σ».rationalScalar k c=algebraMap k («Σ».fanScheme k).functionField c := by
  let j := «Σ».splitTorusOpenMap k
  let A := AddMonoidAlgebra k (Lattice n)
  have hconst : j.appTop (BaseSections.scalarMap k («Σ».fanScheme k) ⊤ c) =
      (Scheme.ΓSpecIso (CommRingCat.of A)).inv (algebraMap k A c) := by
    calc
      j.appTop (BaseSections.scalarMap k («Σ».fanScheme k) ⊤ c) =
          BaseSections.scalarMap k (ToricGeometry.splitTorus k n) ⊤ c :=
        BaseSections.scalarMap_top_natural k j c
      _ = _ := by
        change BaseSections.scalarMap k (Spec (CommRingCat.of A)) ⊤ c = _
        exact BaseSections.scalarMap_affine_top k A c
  change «Σ».torusRationalMap k (algebraMap k A c) =
    («Σ».fanScheme k).germToFunctionField ⊤ (BaseSections.scalarMap k («Σ».fanScheme k) ⊤ c)
  rw [«Σ».torusRationalMap_eq_openImmersion]
  letI : Nonempty (j ⁻¹ᵁ (⊤ : («Σ».fanScheme k).Opens)) :=
    openImmersion_preimage_nonempty j ⊤
  apply (openImmersionFunctionFieldEquiv j).injective
  change (openImmersionFunctionFieldEquiv j)
    ((openImmersionFunctionFieldEquiv j).symm
      ((ToricGeometry.splitTorus k n).germToFunctionField ⊤
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv (algebraMap k A c)))) = _
  rw [RingEquiv.apply_symm_apply]
  exact (congrArg (fun a : Γ(ToricGeometry.splitTorus k n, ⊤) =>
    (ToricGeometry.splitTorus k n).germToFunctionField ⊤ a) hconst.symm).trans
    (openImmersionFunctionFieldEquiv_germ j ⊤
      (BaseSections.scalarMap k («Σ».fanScheme k) ⊤ c)).symm

/-- The actual Laurent embedding is an algebra map over the true base. -/
def torusRationalAlgHom : AddMonoidAlgebra k (Lattice n) →ₐ[k]
    («Σ».fanScheme k).functionField where
  __ := «Σ».torusRationalMap k
  commutes' := «Σ».rationalScalar_eq_algebraMap k

theorem torusRationalAlgHom_injective : Function.Injective («Σ».torusRationalAlgHom k) :=
  «Σ».torusRationalMap_injective k

/-- Base-linear Laurent evaluation on the allowed exponent submodule. -/
def fanCharacterValue (a : Lattice n→ℤ) :
    characterModule k («Σ».fanIntegralExponents a) →ₗ[k] («Σ».fanScheme k).functionField :=
  («Σ».torusRationalAlgHom k).toLinearMap.comp
    (characterModule k («Σ».fanIntegralExponents a)).subtype

theorem fanCharacterValue_injective (a : Lattice n→ℤ) :
    Function.Injective («Σ».fanCharacterValue k a) :=
  («Σ».torusRationalMap_injective k).comp Subtype.val_injective

theorem fanCartier_globalSectionValue_range (hpure : «Σ».IsPure) (a : Lattice n→ℤ) :
    ((«Σ».fanCartierData k hpure a).globalSectionValue k).range =
      («Σ».fanCharacterValue k a).range := by
  apply SetLike.coe_injective
  change Set.range ((«Σ».fanCartierData k hpure a).sectionValue ⊤) = _
  rw [«Σ».fanCartier_globalRange]
  ext r
  constructor
  · rintro ⟨f,hf,rfl⟩
    exact ⟨⟨f,hf⟩,rfl⟩
  · rintro ⟨f,rfl⟩
    exact ⟨f.val,f.property,rfl⟩

/-- The actual global-section vector space is canonically identified by
its rational values with the literal finite-support character module. -/
def fanCartierSectionCoordinates (hpure : «Σ».IsPure) (a : Lattice n→ℤ) :
    Γ((«Σ».fanCartierData k hpure a).sheaf,⊤) ≃ₗ[k]
      characterModule k («Σ».fanIntegralExponents a) :=
  (LinearEquiv.ofInjective ((«Σ».fanCartierData k hpure a).globalSectionValue k)
    ((«Σ».fanCartierData k hpure a).globalSectionValue_injective k)).trans
    ((LinearEquiv.ofEq _ _ («Σ».fanCartier_globalSectionValue_range k hpure a)).trans
      (LinearEquiv.ofInjective («Σ».fanCharacterValue k a)
        («Σ».fanCharacterValue_injective k a)).symm)

theorem fanCartierSectionCoordinates_value (hpure : «Σ».IsPure) (a : Lattice n→ℤ)
    (s : Γ((«Σ».fanCartierData k hpure a).sheaf,⊤)) :
    «Σ».torusRationalMap k ((«Σ».fanCartierSectionCoordinates k hpure a s).val) =
      («Σ».fanCartierData k hpure a).globalSectionValue k s := by
  change «Σ».fanCharacterValue k a («Σ».fanCartierSectionCoordinates k hpure a s)=_
  simp only [fanCartierSectionCoordinates,LinearEquiv.trans_apply,
    LinearEquiv.ofInjective_symm_apply,LinearEquiv.coe_ofEq_apply,
    LinearEquiv.ofInjective_apply]

end PaperVerification.ToricGeometry.SmoothCompleteFan

#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.rationalScalar_eq_algebraMap
#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.fanCartierSectionCoordinates
#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.fanCartierSectionCoordinates_value
end
end Source_ToricFanSectionCoordinates
-- END ORIGINAL PaperVerification.ToricFanSectionCoordinates


-- BEGIN ORIGINAL PaperVerification.ToricFanCartierArithmetic
section Source_ToricFanCartierArithmetic

-- original header: module

-- original header: public import PaperVerification.ToricFanSectionCoordinates
-- original header: public import PaperVerification.ToricCartierAmpleDescent

-- original header: @[expose] public section

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
end
end Source_ToricFanCartierArithmetic
-- END ORIGINAL PaperVerification.ToricFanCartierArithmetic


-- BEGIN ORIGINAL PaperVerification.ToricFanSectionMultiplication
section Source_ToricFanSectionMultiplication

-- original header: module

-- original header: public import PaperVerification.ToricFanCartierArithmetic

-- original header: @[expose] public section

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
end
end Source_ToricFanSectionMultiplication
-- END ORIGINAL PaperVerification.ToricFanSectionMultiplication


