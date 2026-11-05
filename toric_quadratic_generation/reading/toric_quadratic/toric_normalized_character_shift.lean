module

public import PaperVerification.ToricIntrinsicSectionCharacters
public import PaperVerification.ToricCartierChartValues
public import PaperVerification.ToricLaurentUnits
public import PaperVerification.ToricCartierSchemeIso
public import PaperVerification.ToricDominantAffineCoordinates

@[expose] public section

/-!
# The actual character shift caused by a second torus normalization

The exponent set is read from the Laurent values of genuine global
sections. A Cartier presentation whose local frames are units on the
torus has a Laurent-unit normalization factor. Its scalar and its
integral character exponent are retained explicitly. Consequently a
second normalization translates the exponent set by an actual lattice
vector; it does not silently identify two differently framed polytopes.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open PaperVerification.ToricCharacters
open scoped PaperVerification.ToricSchemes.BaseSections

namespace PaperVerification.ToricSchemes

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]

namespace CartierData

/-- Unit frames characterize the ordinary fractional regular-function
module on every open contained in the specified open. -/
theorem sectionValueRange_eq_regular_of_unitFrames (E : CartierData X)
    {V : X.Opens} (hE : E.localCocycle.HasUnitFramesOn V)
    (U : X.Opens) [Nonempty U] (hU : U≤V) :
    (E.sectionValueRange U : Set X.functionField)=
      Set.range (X.germToFunctionField U) := by
  ext z
  change z ∈ E.sectionValueRange U ↔ z ∈ (X.germToFunctionField U).hom.range
  rw [E.mem_sectionValueRange_iff_localStalks,
    mem_regular_range_iff_stalkwise]
  constructor
  · intro h x hx
    obtain ⟨i,hi⟩ := E.localCocycle.covers x
    have hz := (regularAtSubring X x).mul_mem (h i x hx hi)
      (hE i x (hU hx) hi).1
    simpa only [div_mul_cancel₀ _ (E.localCocycle.generator i).ne_zero] using hz
  · intro h i x hx hi
    simpa only [div_eq_mul_inv] using
      (regularAtSubring X x).mul_mem (h x hx) (hE i x (hU hx) hi).2

theorem hasUnitFramesOn_dominantPullback (E : CartierData X)
    {V : X.Opens} (hE : E.localCocycle.HasUnitFramesOn V)
    (f : Y ⟶ X) [IsDominant f] :
    (E.dominantPullback f).localCocycle.HasUnitFramesOn (f ⁻¹ᵁ V) :=
  (E.localCocycle.hasUnitFramesOn_pullback V hE f).of_equivalent
    (E.dominantPullback f).localCocycle
    (E.dominantPullback f).equivalent_localCocycle

end CartierData

variable (k : Type u) [Field k] (n : ℕ)
    (X : Scheme.{u}) [IsIntegral X] [X.Over (Spec (CommRingCat.of k))]
    (j : splitTorus k (Fin n→ℤ) ⟶ X) [IsOpenImmersion j]
    [j.IsOver (Spec (CommRingCat.of k))]

local instance : IsDomain (torusCoordinateRing k n) :=
  torusCoordinateRing_isDomain k n

/-- The exponents of literal characters contained in the actual Laurent
image of the global-section space of a Cartier presentation. -/
def torusSectionExponents (E : CartierData X) : Set (Fin n→ℤ) :=
  characterExponents k (torusSectionCharacters k n X j E)

/-- An intrinsic exponent set: it is defined before choosing any fan,
projective embedding, affine invariant cover, or polytope description. -/
def intrinsicSectionExponents (D : CartierData X) : Set (Fin n→ℤ) :=
  characterExponents k (normalizedGlobalCharacters k n X j D)

theorem intrinsicSectionExponents_eq (D : CartierData X) :
    intrinsicSectionExponents k n X j D=
      torusSectionExponents k n X j (torusNormalizedCartier k n X j D) := by
  rw [intrinsicSectionExponents,normalizedGlobalCharacters_eq_torusSectionCharacters]
  rfl

/-- A genuine global torus frame of an already torus-trivial divisor
has an actual Laurent-unit rational value. -/
theorem torusCartierGenerator_laurentUnit (E : CartierData X)
    (hE : E.localCocycle.HasUnitFramesOn j.opensRange) :
    ∃ v : (AddMonoidAlgebra k (Fin n→ℤ))ˣ,
      openTorusRationalAlgHom k n X j (v : AddMonoidAlgebra k (Fin n→ℤ))=
        (torusCartierGenerator k n X j E : X.functionField) := by
  let W := j ''ᵁ (⊤ : (splitTorus k (Fin n→ℤ)).Opens)
  letI : Nonempty W := openImmersion_image_nonempty j ⊤
  have hW : W≤j.opensRange := by
    rw [show W=j ''ᵁ ⊤ from rfl,Scheme.Hom.image_top_eq_opensRange]
  obtain ⟨a,ha⟩ := E.chartFrameGenerator_isUnit_of_range j
    (torusCartierFrame k n X j E) W hW
    (E.sectionValueRange_eq_regular_of_unitFrames hE W hW)
  let A := CommRingCat.of (torusCoordinateRing k n)
  let φ : Γ(X,W) →+* AddMonoidAlgebra k (Fin n→ℤ) :=
    (Scheme.ΓSpecIso A).hom.hom.comp (j.appIso ⊤).hom.hom
  refine ⟨Units.map φ a,?_⟩
  rw [Units.coe_map,openTorusRationalAlgHom_value]
  change openImmersionGlobalToFunctionField j
    ((Scheme.ΓSpecIso A).inv (φ a))=_
  rw [show (Scheme.ΓSpecIso A).inv (φ a)=(j.appIso ⊤).hom a by
      exact (Scheme.ΓSpecIso A).commRingCatIsoToRingEquiv.left_inv _,
    openImmersionRegularToFunctionField_eq_germ_image]
  simpa only [torusCartierGenerator,Units.val_mk0,Iso.hom_inv_id_apply] using ha

/-- Both the scalar and the integral character shift are obtained from
the genuine torus frame. No character-frame hypothesis is assumed. -/
theorem torusCartierGenerator_scalar_character (E : CartierData X)
    (hE : E.localCocycle.HasUnitFramesOn j.opensRange) :
    ∃ c : kˣ, ∃ m : Fin n→ℤ,
      (torusCartierGenerator k n X j E : X.functionField)=
        openTorusRationalAlgHom k n X j (AddMonoidAlgebra.single m (c:k)) := by
  obtain ⟨v,hv⟩ := torusCartierGenerator_laurentUnit k n X j E hE
  obtain ⟨c,m,hm⟩ := laurent_unit_single k n v
  exact ⟨c,m,hv.symm.trans (congrArg (openTorusRationalAlgHom k n X j) hm)⟩

theorem mem_normalizedGlobalRange_iff (E : CartierData X) (z : X.functionField) :
    z∈((torusNormalizedCartier k n X j E).globalSectionValue k).range ↔
      (torusCartierGenerator k n X j E : X.functionField)*z∈
        (E.globalSectionValue k).range := by
  let q := torusCartierGenerator k n X j E
  constructor
  · rintro ⟨s,rfl⟩
    refine ⟨s,?_⟩
    change E.sectionValue ⊤ s=(q:X.functionField)*
      (E.scale q⁻¹).sectionValue ⊤ s
    simpa only [Units.val_inv_eq_inv_val,← mul_assoc,
      mul_inv_cancel₀ q.ne_zero,one_mul] using
      congrArg (fun r : X.functionField => (q : X.functionField) * r)
        (E.scale_sectionValue q⁻¹ ⊤ s).symm
  · rintro ⟨s,hs⟩
    refine ⟨s,?_⟩
    change (E.scale q⁻¹).sectionValue ⊤ s=z
    change E.sectionValue ⊤ s = (q : X.functionField) * z at hs
    calc
      _ = ((q⁻¹ : X.functionFieldˣ) : X.functionField) * E.sectionValue ⊤ s :=
        E.scale_sectionValue q⁻¹ ⊤ s
      _ = z := by
        rw [Units.val_inv_eq_inv_val,hs,← mul_assoc,
          inv_mul_cancel₀ q.ne_zero,one_mul]

/-- Exact membership after normalization, retaining the full integral
translation and cancelling only the proved nonzero scalar. -/
theorem torusSectionExponents_normalize_iff (E : CartierData X)
    (c : kˣ) (v : Fin n→ℤ)
    (hq : (torusCartierGenerator k n X j E : X.functionField)=
      openTorusRationalAlgHom k n X j (AddMonoidAlgebra.single v (c:k)))
    (m : Fin n→ℤ) :
    m∈torusSectionExponents k n X j E ↔
      m-v∈intrinsicSectionExponents k n X j E := by
  rw [intrinsicSectionExponents_eq]
  change openTorusRationalAlgHom k n X j (AddMonoidAlgebra.single m (1:k))∈
      (E.globalSectionValue k).range ↔
    openTorusRationalAlgHom k n X j (AddMonoidAlgebra.single (m-v) (1:k))∈
      ((torusNormalizedCartier k n X j E).globalSectionValue k).range
  rw [mem_normalizedGlobalRange_iff,hq,← map_mul,
    AddMonoidAlgebra.single_mul_single,mul_one,
    show v+(m-v)=m by abel]
  have hs : AddMonoidAlgebra.single m (c:k)=
      (c:k) • AddMonoidAlgebra.single m (1:k) := by
    simp only [AddMonoidAlgebra.smul_single,smul_eq_mul,mul_one]
  rw [hs,map_smul]
  exact ((E.globalSectionValue k).range.smul_mem_iff c.ne_zero).symm

theorem torusSectionExponents_eq_translate (E : CartierData X)
    (c : kˣ) (v : Fin n→ℤ)
    (hq : (torusCartierGenerator k n X j E : X.functionField)=
      openTorusRationalAlgHom k n X j (AddMonoidAlgebra.single v (c:k))) :
    torusSectionExponents k n X j E=
      (fun m=>v+m) '' intrinsicSectionExponents k n X j E := by
  ext m
  constructor
  · intro hm
    exact ⟨m-v,(torusSectionExponents_normalize_iff k n X j E c v hq m).mp hm,
      by abel⟩
  · rintro ⟨w,hw,rfl⟩
    apply (torusSectionExponents_normalize_iff k n X j E c v hq (v+w)).mpr
    simpa only [add_sub_cancel_left] using hw

end PaperVerification.ToricSchemes
