module

public import PaperVerification.ToricCartierProducts
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

@[expose] public section

/-!
# Intrinsic nonvanishing and ampleness of actual Cartier sheaves

The nonvanishing open is computed from actual regular coordinates in local
frames. Its membership is independent of the frame, and is exactly the
condition that the local coefficient is outside the maximal ideal of the
actual local ring. Ampleness uses the standard affine nonvanishing-open
definition (EGA II, Definition 4.5.3; Stacks Project, tag 01PS).

No fan, polytope, support-function inequality, or section-space formula is
part of this definition. Powers use powers of actual local Cartier equations;
the tensor-sheaf identification is developed separately.
-/

noncomputable section

universe u

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

namespace PaperVerification.ToricSchemes

variable {X : Scheme.{u}} [IsIntegral X]

/-- The usual unit condition in an actual local ring, expressed through its
injective embedding in the actual function field. -/
theorem isUnit_stalk_iff (x : X) (a : X.presheaf.stalk x) :
    IsUnit a ↔
      algebraMap (X.presheaf.stalk x) X.functionField a ≠ 0 ∧
      (algebraMap (X.presheaf.stalk x) X.functionField a)⁻¹ ∈ regularAtSubring X x := by
  constructor
  · rintro ⟨u,rfl⟩
    have hne : algebraMap (X.presheaf.stalk x) X.functionField (u : X.presheaf.stalk x)≠0 :=
      ((u.isUnit).map (algebraMap (X.presheaf.stalk x) X.functionField)).ne_zero
    refine ⟨hne,⟨(u⁻¹ : (X.presheaf.stalk x)ˣ),?_⟩⟩
    apply mul_left_cancel₀ hne
    rw [← map_mul,u.mul_inv,map_one,mul_inv_cancel₀ hne]
  · rintro ⟨hne,b,hb⟩
    have hab : a*b=1 := by
      apply IsFractionRing.injective (X.presheaf.stalk x) X.functionField
      rw [map_mul,hb,map_one,mul_inv_cancel₀ hne]
    exact ⟨⟨a,b,hab,by simpa only [mul_comm] using hab⟩,rfl⟩

namespace RationalCartierCocycle

variable (C D : RationalCartierCocycle X)

/-- Natural powers of the actual local rational generators. -/
def pow (n : ℕ) : RationalCartierCocycle X where
  index := C.index
  openSet := C.openSet
  covers := C.covers
  generator i := C.generator i ^ n
  transition i j x hi hj := by
    simpa only [Units.val_pow_eq_pow_val,div_pow] using
      (regularAtSubring X x).pow_mem (C.transition i j x hi hj) n

@[simp] theorem pow_openSet (n : ℕ) (i : C.index) :
    (C.pow n).openSet i=C.openSet i := rfl

@[simp] theorem pow_generator (n : ℕ) (i : C.index) :
    ((C.pow n).generator i : X.functionField)=(C.generator i : X.functionField)^n := rfl

/-- The actual regular coefficient of a global section in a local frame. -/
def localCoefficient (i : C.index) (s : Γ(C.sheaf,⊤)) : Γ(X,C.openSet i) :=
  C.localCoordinates i (C.openSet i) le_rfl
    (C.sheaf.presheaf.map (homOfLE le_top).op s)

theorem localCoefficient_value (i : C.index) [Nonempty (C.openSet i)]
    (s : Γ(C.sheaf,⊤)) :
    X.germToFunctionField (C.openSet i) (C.localCoefficient i s) =
      C.toCartierData.sectionValue ⊤ s / (C.generator i : X.functionField) := by
  rw [localCoefficient,C.localCoordinates_value]
  change rationalValue X (C.openSet i)
      ((rationalFunctions X).presheaf.map (homOfLE le_top).op s.val) /
        (C.generator i : X.functionField) =
    rationalValue X ⊤ s.val / (C.generator i : X.functionField)
  exact congrArg (fun z : X.functionField => z / (C.generator i : X.functionField))
    (rationalValue_restrict X (homOfLE (show C.openSet i≤⊤ from le_top)) s.val)

/-- The usual nonvanishing locus of a section, as an actual open set. -/
def nonvanishingOpen (s : Γ(C.sheaf,⊤)) : X.Opens :=
  ⨆ i,X.basicOpen (C.localCoefficient i s)

/-- In any chosen local frame, nonvanishing is the actual local unit test. -/
theorem mem_localNonvanishing_iff (i : C.index) (s : Γ(C.sheaf,⊤))
    (x : X) (hxi : x∈C.openSet i) :
    x∈X.basicOpen (C.localCoefficient i s) ↔
      C.toCartierData.sectionValue ⊤ s ≠ 0 ∧
      (C.generator i : X.functionField)/C.toCartierData.sectionValue ⊤ s ∈
        regularAtSubring X x := by
  letI : Nonempty (C.openSet i) := ⟨⟨x,hxi⟩⟩
  rw [X.mem_basicOpen _ x hxi,isUnit_stalk_iff,
    X.algebraMap_germ_eq_germToFunctionField hxi,C.localCoefficient_value]
  rw [div_ne_zero_iff,inv_div]
  constructor
  · rintro ⟨⟨h,-⟩,hr⟩
    exact ⟨h,hr⟩
  · rintro ⟨h,hr⟩
    exact ⟨⟨h,(C.generator i).ne_zero⟩,hr⟩

/-- The local nonvanishing condition agrees on overlaps. -/
theorem localNonvanishing_iff (i j : C.index) (s : Γ(C.sheaf,⊤))
    (x : X) (hxi : x∈C.openSet i) (hxj : x∈C.openSet j) :
    x∈X.basicOpen (C.localCoefficient i s) ↔
      x∈X.basicOpen (C.localCoefficient j s) := by
  rw [C.mem_localNonvanishing_iff i s x hxi,
    C.mem_localNonvanishing_iff j s x hxj]
  constructor
  · rintro ⟨hr,h⟩
    refine ⟨hr,?_⟩
    have hratio := C.transition j i x hxj hxi
    have he : ((C.generator j : X.functionField)/(C.generator i : X.functionField))*
        ((C.generator i : X.functionField)/C.toCartierData.sectionValue ⊤ s) =
        (C.generator j : X.functionField)/C.toCartierData.sectionValue ⊤ s := by
      field_simp [Units.ne_zero,hr]
    simpa only [he] using (regularAtSubring X x).mul_mem hratio h
  · rintro ⟨hr,h⟩
    refine ⟨hr,?_⟩
    have hratio := C.transition i j x hxi hxj
    have he : ((C.generator i : X.functionField)/(C.generator j : X.functionField))*
        ((C.generator j : X.functionField)/C.toCartierData.sectionValue ⊤ s) =
        (C.generator i : X.functionField)/C.toCartierData.sectionValue ⊤ s := by
      field_simp [Units.ne_zero,hr]
    simpa only [he] using (regularAtSubring X x).mul_mem hratio h

/-- A frame-independent membership test for the actual nonvanishing open. -/
theorem mem_nonvanishingOpen_iff (i : C.index) (s : Γ(C.sheaf,⊤))
    (x : X) (hxi : x∈C.openSet i) :
    x∈C.nonvanishingOpen s ↔
      IsUnit (X.presheaf.germ (C.openSet i) x hxi (C.localCoefficient i s)) := by
  rw [← X.mem_basicOpen _ x hxi]
  constructor
  · intro hx
    obtain ⟨j,hj⟩ := Opens.mem_iSup.mp hx
    exact (C.localNonvanishing_iff j i s x (X.basicOpen_le _ hj) hxi).mp hj
  · intro hx
    exact Opens.mem_iSup.mpr ⟨i,hx⟩

/-- In the actual local rank-one coordinate, the section is nonvanishing
exactly when it is outside the maximal ideal. This is the ordinary fibre
criterion, without interpreting nonvanishing as a formal support inequality. -/
theorem mem_nonvanishingOpen_iff_not_mem_maximalIdeal
    (i : C.index) (s : Γ(C.sheaf,⊤)) (x : X) (hxi : x∈C.openSet i) :
    x∈C.nonvanishingOpen s ↔
      X.presheaf.germ (C.openSet i) x hxi (C.localCoefficient i s) ∉
        IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
  rw [C.mem_nonvanishingOpen_iff i s x hxi,IsLocalRing.mem_maximalIdeal,
    mem_nonunits_iff,not_not]

/-- A power of an actual rational section is an actual section of the
corresponding power of its Cartier sheaf. -/
def sectionPow (n : ℕ) (s : Γ(C.sheaf,⊤)) : Γ((C.pow n).sheaf,⊤) := by
  let t : Γ(rationalFunctions X,⊤) :=
    (show Γ(Spec X.functionField,genericPointMap X ⁻¹ᵁ (⊤ : X.Opens)) from s.val)^n
  refine ⟨t,?_⟩
  intro i x hx
  have hs : rationalValue X ⊤ s.val / (C.generator i : X.functionField) ∈
      regularAtSubring X x.val := s.property i x hx
  have h := (regularAtSubring X x.val).pow_mem hs n
  have ht : rationalValue X ⊤ t = (rationalValue X ⊤ s.val)^n :=
    map_pow (rationalSectionValueIso X ⊤).hom.hom
      (show Γ(Spec X.functionField,genericPointMap X ⁻¹ᵁ (⊤ : X.Opens)) from s.val) n
  change rationalValue X ⊤ t / (C.generator i : X.functionField)^n ∈ regularAtSubring X x.val
  rw [ht]
  simpa only [div_pow] using h

@[simp] theorem sectionPow_value (n : ℕ) (s : Γ(C.sheaf,⊤)) :
    (C.pow n).toCartierData.sectionValue ⊤ (C.sectionPow n s) =
      (C.toCartierData.sectionValue ⊤ s)^n :=
  map_pow (rationalSectionValueIso X ⊤).hom.hom
    (show Γ(Spec X.functionField,genericPointMap X ⁻¹ᵁ (⊤ : X.Opens)) from s.val) n

theorem localCoefficient_sectionPow (n : ℕ) (i : C.index)
    (s : Γ(C.sheaf,⊤)) :
    (C.pow n).localCoefficient i (C.sectionPow n s) = (C.localCoefficient i s)^n := by
  classical
  by_cases hU : Nonempty (C.openSet i)
  · letI := hU
    letI : Nonempty ((C.pow n).openSet i) := by
      change Nonempty (C.openSet i)
      exact hU
    apply X.germToFunctionField_injective (C.openSet i)
    calc
      _ = (C.pow n).toCartierData.sectionValue ⊤ (C.sectionPow n s) /
          (C.generator i : X.functionField)^n :=
        (C.pow n).localCoefficient_value i (C.sectionPow n s)
      _ = (C.toCartierData.sectionValue ⊤ s)^n / (C.generator i : X.functionField)^n :=
        congrArg (fun z : X.functionField => z / (C.generator i : X.functionField)^n)
          (C.sectionPow_value n s)
      _ = (C.toCartierData.sectionValue ⊤ s / (C.generator i : X.functionField))^n :=
        (div_pow _ _ n).symm
      _ = (X.germToFunctionField (C.openSet i) (C.localCoefficient i s))^n :=
        congrArg (fun z : X.functionField => z^n) (C.localCoefficient_value i s).symm
      _ = _ := (map_pow (X.germToFunctionField (C.openSet i)).hom _ n).symm
  · have hbot : C.openSet i=⊥ := by
      apply le_antisymm ?_ bot_le
      intro x hx
      exact (hU ⟨⟨x,hx⟩⟩).elim
    letI := regularSections_subsingleton_of_empty X (C.openSet i) hbot
    change (_ : Γ(X,C.openSet i)) = _
    exact Subsingleton.elim _ _

/-- Raising a section to a positive power preserves its actual nonvanishing
open, exactly as for regular functions. -/
theorem nonvanishingOpen_sectionPow (n : ℕ) (hn : 0<n) (s : Γ(C.sheaf,⊤)) :
    (C.pow n).nonvanishingOpen (C.sectionPow n s)=C.nonvanishingOpen s := by
  change (⨆ i : C.index,X.basicOpen ((C.pow n).localCoefficient i (C.sectionPow n s))) =
    ⨆ i : C.index,X.basicOpen (C.localCoefficient i s)
  apply iSup_congr
  intro i
  exact (congrArg (fun t : Γ(X,C.openSet i) => X.basicOpen t)
    (C.localCoefficient_sectionPow n i s)).trans (X.basicOpen_pow _ hn)

/-- The standard intrinsic definition of an ample Cartier sheaf. Compactness
here is quasi-compactness of the underlying spectral topological space. -/
def IsAmple : Prop :=
  CompactSpace X ∧ ∀ x : X,∃ n : ℕ,0<n ∧
    ∃ s : Γ((C.pow n).sheaf,⊤),
      x∈(C.pow n).nonvanishingOpen s ∧ IsAffineOpen ((C.pow n).nonvanishingOpen s)

/-- Ampleness supplies a finite affine cover by genuine nonvanishing opens
of positive tensor powers. -/
theorem IsAmple.exists_finite_cover (hC : C.IsAmple) :
    ∃ (ι : Type u) (_ : Fintype ι) (n : ι→ℕ)
      (s : ∀ i,Γ((C.pow (n i)).sheaf,⊤)),
      (∀ i,0<n i) ∧
      (∀ i,IsAffineOpen ((C.pow (n i)).nonvanishingOpen (s i))) ∧
      (⨆ i,(C.pow (n i)).nonvanishingOpen (s i))=⊤ := by
  classical
  letI := hC.1
  choose n hn s hs ha using hC.2
  have hcover : IsOpenCover (fun x:X=>(C.pow (n x)).nonvanishingOpen (s x)) := by
    apply le_antisymm le_top
    intro x hx
    exact Opens.mem_iSup.mpr ⟨x,hs x⟩
  obtain ⟨t,ht⟩ := hcover.exists_finite_of_compactSpace
  exact ⟨t,inferInstance,fun i=>n i.val,fun i=>s i.val,
    fun i=>hn i.val,fun i=>ha i.val,ht⟩

end RationalCartierCocycle

namespace CartierData

variable (D : CartierData X)

/-- Multiplication of a Cartier divisor by a natural number. -/
def nsmul (n : ℕ) : CartierData X := (D.localCocycle.pow n).toCartierData

/-- Intrinsic ampleness, without any fan or polytope hypothesis. -/
def IsAmple : Prop := D.localCocycle.IsAmple

end CartierData

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.RationalCartierCocycle.mem_nonvanishingOpen_iff_not_mem_maximalIdeal
#print axioms PaperVerification.ToricSchemes.RationalCartierCocycle.nonvanishingOpen_sectionPow
#print axioms PaperVerification.ToricSchemes.RationalCartierCocycle.IsAmple.exists_finite_cover
