module

public import PaperVerification.ToricFanSchemeIntegral
public import PaperVerification.ToricFunctionFieldBridge

@[expose] public section

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
