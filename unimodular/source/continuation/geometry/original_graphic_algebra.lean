module

public import Continuation.Geometry.OriginalGraphicCoordinates
public import Recovery.Unimodular.GraphicSectionRing.EhrhartAlgebra

/-!
# Literal toric ideals and Ehrhart algebras on an abstract integral lattice

The toric map has target k[ℕ × N] and sends the original variable x to (1,x).
The Ehrhart algebra has exactly the original geometric exponent carrier.
Coordinates prove closure and provide explicit degree-preserving equivalences;
they are not substituted into the definitions of the original variables or
the original toric kernel.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open TauCeti.Toric
open scoped BigOperators Pointwise

universe u v w

namespace Unimodular.GraphicSectionRing.OriginalLattice

section Toric

variable {N : Type u} [AddCommGroup N] {σ : Type v}

/-- The ordinary homogeneous monomial map in the original exponent lattice. -/
def toricMap (p : σ → N) (K : Type w) [CommSemiring K] :
    MvPolynomial σ K →ₐ[K] AddMonoidAlgebra K (ℕ × N) :=
  MvPolynomial.aeval (fun x => AddMonoidAlgebra.single (1, p x) 1)

@[simp] theorem toricMap_X (p : σ → N) (K : Type w) [CommSemiring K] (x : σ) :
    toricMap p K (MvPolynomial.X x) = AddMonoidAlgebra.single (1, p x) 1 := by
  simp only [toricMap, MvPolynomial.aeval_X]

/-- The kernel is defined before any coordinates or normal-form theorem. -/
def toricIdeal (p : σ → N) (K : Type w) [CommSemiring K] :
    Ideal (MvPolynomial σ K) :=
  RingHom.ker (toricMap p K).toRingHom

/-- Degree is unchanged by the integral map on exponents. -/
def degreeMap {M : Type*} [AddCommGroup M] (f : N →+ M) :
    (ℕ × N) →+ (ℕ × M) where
  toFun z := (z.1, f z.2)
  map_zero' := by simp
  map_add' x y := by simp [map_add]

theorem degreeMap_injective {M : Type*} [AddCommGroup M] {f : N →+ M}
    (hf : Function.Injective f) : Function.Injective (degreeMap f) := by
  intro x y h
  change (x.1, f x.2) = (y.1, f y.2) at h
  apply Prod.ext
  · exact congrArg (fun z : ℕ × M => z.1) h
  · exact hf (congrArg (fun z : ℕ × M => z.2) h)

/-- Actual compatibility of monomial maps, on the unchanged original labels. -/
theorem toricMap_coordinates {d : ℕ} (p : σ → N) (e : N →+ Lattice d)
    (K : Type w) [CommSemiring K] :
    GraphicSectionRing.toricMap (e ∘ p) K =
      (AddMonoidAlgebra.mapDomainAlgHom K K (degreeMap e)).comp (toricMap p K) := by
  apply MvPolynomial.algHom_ext
  intro x
  simp only [AlgHom.comp_apply, GraphicSectionRing.toricMap_X, toricMap_X,
    Function.comp_apply, AddMonoidAlgebra.mapDomainAlgHom_apply,
    AddMonoidAlgebra.mapDomain_single]
  rfl

/-- Injective lattice coordinates preserve the original ideal literally,
inside the polynomial ring on the same original variables. -/
theorem toricIdeal_coordinates {d : ℕ} (p : σ → N) (e : N →+ Lattice d)
    (he : Function.Injective e) (K : Type w) [CommSemiring K] :
    GraphicSectionRing.toricIdeal (e ∘ p) K = toricIdeal p K := by
  have hinj : Function.Injective
      (AddMonoidAlgebra.mapDomainAlgHom K K (degreeMap e)) :=
    AddMonoidAlgebra.mapDomain_injective (degreeMap_injective he)
  ext f
  change GraphicSectionRing.toricMap (e ∘ p) K f = 0 ↔ toricMap p K f = 0
  rw [toricMap_coordinates, AlgHom.comp_apply]
  constructor
  · intro h
    apply hinj
    simpa only [map_zero] using h
  · intro h
    rw [h, map_zero]

end Toric

variable {N : Type u} [AddCommGroup N]
    {V : Type v} [AddCommGroup V] [Module ℝ V]
    {d : ℕ} {ι : N →+ V}

/-- The ordinary geometric Ehrhart exponent condition, independent of a
coordinate presentation. Degree zero consists only of the zero exponent. -/
def EhrhartPoint (ι : N →+ V) (P : Set V) (z : ℕ × N) : Prop :=
  z = 0 ∨ (0 < z.1 ∧ ι z.2 ∈ (z.1 : ℝ) • P)

/-- The integral coordinate change on actual homogeneous exponents. -/
def exponentEquiv (e : N ≃ₗ[ℤ] Lattice d) : (ℕ × N) ≃+ (ℕ × Lattice d) where
  toFun z := (z.1, e z.2)
  invFun z := (z.1, e.symm z.2)
  left_inv z := Prod.ext rfl (e.symm_apply_apply z.2)
  right_inv z := Prod.ext rfl (e.apply_symm_apply z.2)
  map_add' x y := Prod.ext rfl (e.map_add x.2 y.2)

variable (hi : IsIntegralLattice ι) (e : N ≃ₗ[ℤ] Lattice d)
    (C : Set (Constraint d)) (P : Set V)
    (hP : P = coordinateBody hi e C)

include hP in
/-- The literal original dilation condition is equivalent to the actual
scaled-inequality monoid. This is proved in both directions, including zero. -/
theorem ehrhartPoint_iff (z : ℕ × N) :
    EhrhartPoint ι P z ↔ exponentEquiv e z ∈ sectionSemigroup C := by
  constructor
  · rintro (rfl | ⟨hk, hz⟩)
    · simpa only [map_zero] using (sectionSemigroup C).zero_mem
    · change (z.1 = 0 → e z.2 = 0) ∧
        ∀ c ∈ C, difference (e z.2) c.left c.right ≤ (z.1 : ℤ) * c.bound
      refine ⟨fun hzero => False.elim ((ne_of_gt hk) hzero), ?_⟩
      exact (mem_dilate_iff_scaled_inequalities hk C (e z.2)).mp
        ((lattice_mem_dilate hi e C z.1 z.2).mp (by simpa only [hP] using hz))
  · intro hz
    change (z.1 = 0 → e z.2 = 0) ∧
      (∀ c ∈ C, difference (e z.2) c.left c.right ≤ (z.1 : ℤ) * c.bound) at hz
    by_cases hk : z.1 = 0
    · refine Or.inl (Prod.ext hk (e.injective ?_))
      simpa only [Prod.snd_zero, map_zero] using hz.1 hk
    · refine Or.inr ⟨Nat.pos_of_ne_zero hk, ?_⟩
      rw [hP]
      apply (lattice_mem_dilate hi e C z.1 z.2).mpr
      exact (mem_dilate_iff_scaled_inequalities (Nat.pos_of_ne_zero hk) C (e z.2)).mpr hz.2

/-- Its carrier is the ordinary original Ehrhart exponent set. The graphic
presentation is used solely to prove its closure under addition. -/
def ehrhartSemigroup : AddSubmonoid (ℕ × N) where
  carrier := {z | EhrhartPoint ι P z}
  zero_mem' := Or.inl rfl
  add_mem' := by
    intro x y hx hy
    apply (ehrhartPoint_iff hi e C P hP (x + y)).mpr
    have h := (sectionSemigroup C).add_mem
      ((ehrhartPoint_iff hi e C P hP x).mp hx)
      ((ehrhartPoint_iff hi e C P hP y).mp hy)
    simpa only [map_add] using h

@[simp] theorem mem_ehrhartSemigroup (z : ℕ × N) :
    z ∈ ehrhartSemigroup hi e C P hP ↔ EhrhartPoint ι P z := Iff.rfl

/-- A different graphic coordinate presentation gives the same original
submonoid, rather than merely a newly named isomorphic replacement. -/
theorem ehrhartSemigroup_independent {d' : ℕ}
    (e' : N ≃ₗ[ℤ] Lattice d') (C' : Set (Constraint d'))
    (hP' : P = coordinateBody hi e' C') :
    ehrhartSemigroup hi e C P hP = ehrhartSemigroup hi e' C' P hP' := by
  ext z
  rfl

def semigroupEquiv : ehrhartSemigroup hi e C P hP ≃+ sectionSemigroup C where
  toFun z := ⟨exponentEquiv e z.val, (ehrhartPoint_iff hi e C P hP z.val).mp z.property⟩
  invFun z := ⟨(exponentEquiv e).symm z.val, (ehrhartPoint_iff hi e C P hP _).mpr (by
    rw [AddEquiv.apply_symm_apply]
    exact z.property)⟩
  left_inv z := Subtype.ext ((exponentEquiv e).symm_apply_apply z.val)
  right_inv z := Subtype.ext ((exponentEquiv e).apply_symm_apply z.val)
  map_add' x y := Subtype.ext ((exponentEquiv e).map_add x.val y.val)

@[simp] theorem semigroupEquiv_val (z : ehrhartSemigroup hi e C P hP) :
    (semigroupEquiv hi e C P hP z).val = (z.val.1, e z.val.2) := rfl

def sectionEhrhartIndex : sectionSemigroup C ≃+ ehrhartSemigroup hi e C P hP :=
  (semigroupEquiv hi e C P hP).symm

@[simp] theorem sectionEhrhartIndex_val (z : sectionSemigroup C) :
    (sectionEhrhartIndex hi e C P hP z).val = (z.val.1, e.symm z.val.2) := rfl

/-- The actual monoid algebra on the original geometric exponent carrier. -/
abbrev EhrhartAlgebra (K : Type w) [CommSemiring K] :=
  AddMonoidAlgebra K (ehrhartSemigroup hi e C P hP)

def sectionEhrhartEquiv (K : Type w) [CommSemiring K] :
    SectionAlgebra C K ≃ₐ[K] EhrhartAlgebra hi e C P hP K :=
  AddMonoidAlgebra.domCongr K K (sectionEhrhartIndex hi e C P hP)

@[simp] theorem sectionEhrhartEquiv_single (K : Type w) [CommSemiring K]
    (z : sectionSemigroup C) (a : K) :
    sectionEhrhartEquiv hi e C P hP K (AddMonoidAlgebra.single z a) =
      AddMonoidAlgebra.single (sectionEhrhartIndex hi e C P hP z) a :=
  AddMonoidAlgebra.domCongr_single _ _ _

/-- An explicit bridge to the existing standard-coordinate Ehrhart algebra.
The common section algebra is used only to construct this genuine isomorphism. -/
def coordinateEhrhartEquiv (K : Type w) [CommSemiring K] :
    EhrhartAlgebra hi e C P hP K ≃ₐ[K]
      GraphicSectionRing.EhrhartAlgebra
        (RealCoordinates.coordinateBody (LinearEquiv.refl ℤ (Lattice d)) C)
        (LinearEquiv.refl ℤ (Lattice d)) C rfl K :=
  (sectionEhrhartEquiv hi e C P hP K).symm.trans
    (GraphicSectionRing.sectionEhrhartEquiv
      (RealCoordinates.coordinateBody (LinearEquiv.refl ℤ (Lattice d)) C)
      (LinearEquiv.refl ℤ (Lattice d)) C rfl K)


/-- The bridge to the existing Ehrhart algebra is explicit on every
original monomial; its exponent is the degree together with e(x). -/
@[simp] theorem coordinateEhrhartEquiv_single (K : Type w) [CommSemiring K]
    (z : ehrhartSemigroup hi e C P hP) (a : K) :
    coordinateEhrhartEquiv hi e C P hP K (AddMonoidAlgebra.single z a) =
      AddMonoidAlgebra.single
        (GraphicSectionRing.sectionEhrhartIndex
          (RealCoordinates.coordinateBody (LinearEquiv.refl ℤ (Lattice d)) C)
          (LinearEquiv.refl ℤ (Lattice d)) C rfl (semigroupEquiv hi e C P hP z)) a := by
  change GraphicSectionRing.sectionEhrhartEquiv
    (RealCoordinates.coordinateBody (LinearEquiv.refl ℤ (Lattice d)) C)
    (LinearEquiv.refl ℤ (Lattice d)) C rfl K
    ((sectionEhrhartEquiv hi e C P hP K).symm (AddMonoidAlgebra.single z a)) = _
  rw [sectionEhrhartEquiv, AddMonoidAlgebra.domCongr_symm,
    AddMonoidAlgebra.domCongr_single, GraphicSectionRing.sectionEhrhartEquiv_single]
  rfl

def ehrhartDegreeOne (x : LatticePoint ι P) : ehrhartSemigroup hi e C P hP :=
  ⟨(1, x.val), Or.inr ⟨Nat.zero_lt_succ 0, by
    simpa only [Nat.cast_one, one_smul] using x.property⟩⟩

@[simp] theorem sectionEhrhartIndex_degreeOne (x : LatticePoint ι P) :
    sectionEhrhartIndex hi e C P hP (degreeOnePoint (pointEquiv hi e C P hP x)) =
      ehrhartDegreeOne hi e C P hP x := by
  apply Subtype.ext
  exact Prod.ext rfl (e.symm_apply_apply x.val)

section Ring

variable (K : Type w) [CommRing K]

/-- The ordinary polynomial map on original lattice-point variables. -/
def ehrhartPolynomialMap :
    MvPolynomial (LatticePoint ι P) K →ₐ[K] EhrhartAlgebra hi e C P hP K :=
  MvPolynomial.aeval (fun x => AddMonoidAlgebra.single (ehrhartDegreeOne hi e C P hP x) 1)

@[simp] theorem ehrhartPolynomialMap_X (x : LatticePoint ι P) :
    ehrhartPolynomialMap hi e C P hP K (MvPolynomial.X x) =
      AddMonoidAlgebra.single (ehrhartDegreeOne hi e C P hP x) 1 := by
  simp only [ehrhartPolynomialMap, MvPolynomial.aeval_X]

/-- The actual polynomial maps commute with both the point and algebra
equivalences. No kernel or generation statement is an input. -/
theorem sectionEhrhart_comp_map :
    (sectionEhrhartEquiv hi e C P hP K).toAlgHom.comp
      ((sectionMap C K).comp (MvPolynomial.renameEquiv K (pointEquiv hi e C P hP)).toAlgHom) =
      ehrhartPolynomialMap hi e C P hP K := by
  apply MvPolynomial.algHom_ext
  intro x
  change sectionEhrhartEquiv hi e C P hP K
    (sectionMap C K ((MvPolynomial.renameEquiv K (pointEquiv hi e C P hP))
      (MvPolynomial.X x))) = ehrhartPolynomialMap hi e C P hP K (MvPolynomial.X x)
  rw [MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X, sectionMap_X,
    sectionEhrhartEquiv_single, sectionEhrhartIndex_degreeOne, ehrhartPolynomialMap_X]

theorem ehrhartPolynomialMap_surjective :
    Function.Surjective (ehrhartPolynomialMap hi e C P hP K) := by
  rw [← sectionEhrhart_comp_map hi e C P hP K]
  exact (sectionEhrhartEquiv hi e C P hP K).surjective.comp
    ((sectionMap_surjective C K).comp
      (MvPolynomial.renameEquiv K (pointEquiv hi e C P hP)).surjective)

def ehrhartAmbientMap :
    EhrhartAlgebra hi e C P hP K →ₐ[K] AddMonoidAlgebra K (ℕ × N) :=
  AddMonoidAlgebra.mapDomainAlgHom K K (ehrhartSemigroup hi e C P hP).subtype

theorem ehrhartAmbientMap_injective :
    Function.Injective (ehrhartAmbientMap hi e C P hP K) :=
  AddMonoidAlgebra.mapDomain_injective Subtype.val_injective

theorem ehrhartAmbientMap_comp :
    (ehrhartAmbientMap hi e C P hP K).comp (ehrhartPolynomialMap hi e C P hP K) =
      toricMap (Subtype.val : LatticePoint ι P → N) K := by
  apply MvPolynomial.algHom_ext
  intro x
  simp only [AlgHom.comp_apply, ehrhartPolynomialMap_X, toricMap_X,
    ehrhartAmbientMap, AddMonoidAlgebra.mapDomainAlgHom_apply,
    AddMonoidAlgebra.mapDomain_single]
  rfl

/-- Exact equality with the independently defined original lattice-point
toric ideal inside the original polynomial ring. -/
theorem ehrhartPolynomialMap_ker :
    RingHom.ker (ehrhartPolynomialMap hi e C P hP K).toRingHom =
      toricIdeal (Subtype.val : LatticePoint ι P → N) K := by
  ext f
  change ehrhartPolynomialMap hi e C P hP K f = 0 ↔ toricMap Subtype.val K f = 0
  constructor
  · intro h
    have hc := DFunLike.congr_fun (ehrhartAmbientMap_comp hi e C P hP K) f
    rw [AlgHom.comp_apply, h, map_zero] at hc
    exact hc.symm
  · intro h
    apply ehrhartAmbientMap_injective hi e C P hP K
    rw [map_zero]
    change ((ehrhartAmbientMap hi e C P hP K).comp (ehrhartPolynomialMap hi e C P hP K)) f = 0
    rw [ehrhartAmbientMap_comp, h]

def ehrhartQuotientEquiv :
    (MvPolynomial (LatticePoint ι P) K ⧸ toricIdeal (Subtype.val : LatticePoint ι P → N) K) ≃ₐ[K]
      EhrhartAlgebra hi e C P hP K := by
  rw [← ehrhartPolynomialMap_ker hi e C P hP K]
  exact Ideal.quotientKerAlgEquivOfSurjective (ehrhartPolynomialMap_surjective hi e C P hP K)

end Ring

/-- The intrinsic degree is the first coordinate of the original exponent. -/
def ehrhartInternalDegree : ehrhartSemigroup hi e C P hP →+ ℕ where
  toFun z := z.val.1
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] theorem ehrhartInternalDegree_transport (z : sectionSemigroup C) :
    ehrhartInternalDegree hi e C P hP (sectionEhrhartIndex hi e C P hP z) =
      internalDegree C z := rfl

/-- The comparison with the existing ordinary Ehrhart algebra preserves
the literal homogeneous degree of each original exponent. -/
theorem coordinateEhrhartEquiv_degree (z : ehrhartSemigroup hi e C P hP) :
    GraphicSectionRing.ehrhartInternalDegree
      (RealCoordinates.coordinateBody (LinearEquiv.refl ℤ (Lattice d)) C)
      (LinearEquiv.refl ℤ (Lattice d)) C rfl
      (GraphicSectionRing.sectionEhrhartIndex
        (RealCoordinates.coordinateBody (LinearEquiv.refl ℤ (Lattice d)) C)
        (LinearEquiv.refl ℤ (Lattice d)) C rfl (semigroupEquiv hi e C P hP z)) =
      ehrhartInternalDegree hi e C P hP z := rfl


#print axioms toricIdeal_coordinates
#print axioms ehrhartPoint_iff
#print axioms ehrhartSemigroup_independent
#print axioms coordinateEhrhartEquiv
#print axioms sectionEhrhart_comp_map
#print axioms ehrhartPolynomialMap_surjective
#print axioms ehrhartPolynomialMap_ker
#print axioms ehrhartQuotientEquiv

end Unimodular.GraphicSectionRing.OriginalLattice
