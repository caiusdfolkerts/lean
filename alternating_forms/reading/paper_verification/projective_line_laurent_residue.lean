module

public import PaperVerification.SegreCechVanishing
public import Mathlib.LinearAlgebra.Finsupp.Supported
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.Tactic.FinCases

/-!
# The residue description of the projective-line Čech quotient

This file computes the full degree-one quotient of the Laurent tuple
complex. The residue is the coefficient on the ordered intersection
`(0, 1)` for precisely the exponent vectors with both coordinates negative.
All other coefficients are removed by the existing explicit contraction.
The inverse sends a residue to the alternating edge cocycle. The maps are
linear over an arbitrary commutative coefficient ring.

The comparison with actual twisting-sheaf cohomology is kept separate.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PaperVerification.ProjectiveLineLaurentResidue

open Segre.CechMonomials
open scoped BigOperators

variable {R : Type*} [CommRing R]

/-- Evaluation of the first tuple differential. -/
theorem differential_one_apply (f : RawCochain (Fin 2) R 1)
    (a : Fin 2 → Fin 2) :
    differential 1 f a = f (fun _ ↦ a 1) - f (fun _ ↦ a 0) := by
  have h₀ : a ∘ (0 : Fin 2).succAbove = fun _ : Fin 1 ↦ a 1 := by
    funext i
    fin_cases i
    rfl
  have h₁ : a ∘ (1 : Fin 2).succAbove = fun _ : Fin 1 ↦ a 0 := by
    funext i
    fin_cases i
    rfl
  rw [differential_apply, Fin.sum_univ_two, h₀, h₁]
  simp [sub_eq_add_neg]

/-- A value at vertex `1`, with value zero at vertex `0`. -/
def vertex : R →ₗ[R] RawCochain (Fin 2) R 1 where
  toFun c a := if a 0 = 1 then c else 0
  map_add' c d := by
    funext a
    by_cases h : a 0 = 1 <;> simp [h]
  map_smul' c d := by
    funext a
    by_cases h : a 0 = 1 <;> simp [h]

/-- The alternating edge cocycle with coefficient `c` on `(0, 1)`. -/
def edge : R →ₗ[R] RawCochain (Fin 2) R 2 :=
  (differential 1).comp vertex

theorem edge_apply (c : R) (a : Fin 2 → Fin 2) :
    edge c a = (if a 1 = 1 then c else 0) - (if a 0 = 1 then c else 0) :=
  differential_one_apply (vertex c) a

@[simp] theorem edge_id (c : R) : edge c id = c := by
  simp [edge_apply]

theorem edge_cocycle (c : R) : differential 2 (edge c) = 0 :=
  differential_squared 1 (vertex c)

theorem edge_supported (c : R) :
    edge c ∈ supportedCochains (Set.univ : Set (Fin 2)) 2 := by
  intro a ha
  have he : a 0 = a 1 := by
    by_contra hn
    apply ha
    intro i _
    have h₀ := (a 0).isLt
    have h₁ := (a 1).isLt
    have hi := i.isLt
    have hne : (a 0).val ≠ (a 1).val := fun h ↦ hn (Fin.ext h)
    by_cases h : (a 0).val = i.val
    · exact ⟨0, Fin.ext h⟩
    · exact ⟨1, Fin.ext (by omega)⟩
  rw [edge_apply, he, sub_self]

/-- An all-negative supported cocycle is determined by its value on `(0, 1)`. -/
theorem supported_cocycle_eq_zero (f : RawCochain (Fin 2) R 2)
    (hf : f ∈ supportedCochains (Set.univ : Set (Fin 2)) 2)
    (hc : differential 2 f = 0) (hres : f id = 0) : f = 0 := by
  have h₀ : f (fun _ ↦ 0) = 0 := by
    apply hf
    intro h
    obtain ⟨i, hi⟩ := h (Set.mem_univ (1 : Fin 2))
    exact Fin.zero_ne_one hi
  have hh := contraction_identity (0 : Fin 2) 1 f
  rw [hc, map_zero, zero_add] at hh
  have hv : contraction (0 : Fin 2) 1 f = 0 := by
    funext a
    change f (Fin.cons (0 : Fin 2) a) = 0
    by_cases ha : a 0 = 0
    · have he : Fin.cons (0 : Fin 2) a = (fun _ ↦ (0 : Fin 2)) := by
        funext i
        fin_cases i <;> simp [ha]
      rw [he]
      exact h₀
    · have ha' : a 0 = 1 := Fin.eq_one_of_ne_zero _ ha
      have he : Fin.cons (0 : Fin 2) a = id := by
        funext i
        fin_cases i <;> simp [ha']
      rw [he]
      exact hres
  rw [hv, map_zero] at hh
  exact hh.symm

/-- Both negative exponents, with exactly the prescribed integer degree. -/
def negativeExponents (t : ℤ) : Set (DegreeExponent (Fin 2) t) :=
  {a | ∀ i, a.val i < 0}

/-- The Laurent support submodule carries its ordinary inherited additive group. -/
instance laurentCochains_addCommGroup (t : ℤ) (q : ℕ) :
    AddCommGroup (laurentCochains (I := Fin 2) (K := R) t q) := by
  letI : AddCommGroup (FiniteCochain (Fin 2) R t q) := inferInstance
  exact (laurentCochains (I := Fin 2) (K := R) t q).addCommGroup

/-- The full Laurent tuple differential, restricted to the denominator condition. -/
def tupleDifferential (t : ℤ) (q : ℕ) :
    laurentCochains (I := Fin 2) (K := R) t q →ₗ[R]
      laurentCochains (I := Fin 2) (K := R) t (q + 1) :=
  (laurentDifferential (I := Fin 2) (K := R) t q).restrict
    (fun _ h ↦ laurentDifferential_mem h)

@[simp] theorem tupleDifferential_val (t : ℤ) (q : ℕ)
    (f : laurentCochains (I := Fin 2) (K := R) t q) :
    (tupleDifferential t q f).val =
      laurentDifferential (I := Fin 2) (K := R) t q f.val := rfl

theorem tupleDifferential_squared (t : ℤ) (q : ℕ)
    (f : laurentCochains (I := Fin 2) (K := R) t q) :
    tupleDifferential t (q + 1) (tupleDifferential t q f) = 0 :=
  Subtype.ext (laurentDifferential_squared t q f.val)

/-- The actual kernel of the degree-one tuple differential. -/
abbrev Cycles (R : Type*) [CommRing R] (t : ℤ) :=
  LinearMap.ker (tupleDifferential (R := R) t 2)

/-- The cycle submodule has the inherited additive group used by its quotient. -/
instance cycles_addCommGroup (t : ℤ) : AddCommGroup (Cycles R t) :=
  (Cycles R t).addCommGroup

/-- The actual degree-zero boundaries, with their canonical inclusion into cycles. -/
def toCycles (t : ℤ) :
    laurentCochains (I := Fin 2) (K := R) t 1 →ₗ[R] Cycles R t :=
  (tupleDifferential t 1).codRestrict (Cycles R t)
    (fun f ↦ tupleDifferential_squared t 1 f)

/-- Retain the ordered-intersection coefficient on every all-negative monomial. -/
def residue (t : ℤ) : Cycles R t →ₗ[R] (negativeExponents t →₀ R) :=
  (Finsupp.lsubtypeDomain (negativeExponents t)).comp
    ((mapAtIndex (fun _ ↦ (LinearMap.proj id : RawCochain (Fin 2) R 2 →ₗ[R] R))).comp
      ((laurentCochains (I := Fin 2) (K := R) t 2).subtype.comp
        (Cycles R t).subtype))

@[simp] theorem residue_apply (t : ℤ) (f : Cycles R t) (a : negativeExponents t) :
    residue t f a = f.val.val a.val id := rfl

theorem residue_boundary (t : ℤ)
    (f : laurentCochains (I := Fin 2) (K := R) t 1) :
    residue t (toCycles t f) = 0 := by
  ext a
  change differential 1 (f.val a.val) id = 0
  have ha : negativeSupport a.val.val = Set.univ := by
    ext i
    simp [negativeSupport, a.property i]
  have hz : f.val a.val = 0 :=
    supported_univ_eq_zero 1 (by simp) _ (by simpa [ha] using f.property a.val)
  rw [hz, map_zero]
  rfl

/-- Zero residue is precisely the obstruction-free case of the Laurent contraction. -/
theorem exists_boundary_of_residue_zero (t : ℤ) (f : Cycles R t)
    (hres : residue t f = 0) : ∃ g, toCycles t g = f := by
  classical
  let g : laurentCochains (I := Fin 2) (K := R) t 1 :=
    ⟨laurentContraction (I := Fin 2) (K := R) t 1 f.val.val,
      laurentContraction_mem f.val.property⟩
  refine ⟨g, Subtype.ext (Subtype.ext ?_)⟩
  ext a : 1
  change differential 1 (coefficientContraction a.val 1 (f.val.val a)) = f.val.val a
  have hc : differential 2 (f.val.val a) = 0 := by
    have h := congrArg
      (fun z : laurentCochains (I := Fin 2) (K := R) t 3 ↦ z.val a) f.property
    exact h
  unfold coefficientContraction
  split_ifs with h
  · have hi := contraction_identity (Classical.choose h) 1 (f.val.val a)
    simpa only [hc, map_zero, zero_add] using hi
  · have ha : a ∈ negativeExponents t := fun i ↦
      lt_of_not_ge (fun hi ↦ h ⟨i, hi⟩)
    have hz : f.val.val a = 0 := by
      have hsupport : f.val.val a ∈ supportedCochains (Set.univ : Set (Fin 2)) 2 := by
        simpa only [negativeSupport_eq_univ_of_no_nonnegative a.val h] using f.val.property a
      exact supported_cocycle_eq_zero _ hsupport hc
        (congrArg (fun z ↦ z ⟨a, ha⟩) hres)
    rw [LinearMap.zero_apply, map_zero, hz]

theorem range_toCycles_eq_ker_residue (t : ℤ) :
    LinearMap.range (toCycles (R := R) t) = LinearMap.ker (residue t) := by
  ext f
  constructor
  · rintro ⟨g, rfl⟩
    exact residue_boundary t g
  · exact exists_boundary_of_residue_zero t f

/-- Include an arbitrary finite family of all-negative monomials as alternating edge cocycles. -/
def residueLift (t : ℤ) (p : negativeExponents t →₀ R) : Cycles R t := by
  classical
  let v := (Finsupp.supportedEquivFinsupp (R := R) (negativeExponents t)).symm p
  let f : FiniteCochain (Fin 2) R t 2 := mapAtIndex (fun _ ↦ edge) v.val
  have hf : f ∈ laurentCochains (I := Fin 2) (K := R) t 2 := by
    intro a
    change edge (v.val a) ∈ supportedCochains (negativeSupport a.val) 2
    by_cases ha : a ∈ negativeExponents t
    · have hs : negativeSupport a.val = Set.univ := by
        ext i
        simp [negativeSupport, ha i]
      rw [hs]
      exact edge_supported _
    · have hz := (Finsupp.mem_supported' R _).mp v.property a ha
      rw [hz, map_zero]
      exact (supportedCochains _ _).zero_mem
  refine ⟨⟨f, hf⟩, ?_⟩
  apply Subtype.ext
  ext a : 1
  exact edge_cocycle (v.val a)

@[simp] theorem residue_residueLift (t : ℤ) (p : negativeExponents t →₀ R) :
    residue t (residueLift t p) = p := by
  classical
  ext a
  change edge (((Finsupp.supportedEquivFinsupp (R := R) (negativeExponents t)).symm p).val
    a.val) id = p a
  rw [edge_id]
  simp [Finsupp.supportedEquivFinsupp_symm_apply_coe, Finsupp.extendDomain_apply]

/-- The entire degree-one Laurent Čech quotient is the module of negative Laurent residues. -/
def homologyResidueEquiv (t : ℤ) :
    (Cycles R t ⧸ LinearMap.range (toCycles (R := R) t)) ≃ₗ[R]
      (negativeExponents t →₀ R) :=
  (Submodule.quotEquivOfEq _ _ (range_toCycles_eq_ker_residue (R := R) t)).trans
    ((residue (R := R) t).quotKerEquivOfSurjective
      (fun p ↦ ⟨residueLift t p, residue_residueLift t p⟩))

/-- The isomorphism is the literal residue of a representative cocycle. -/
@[simp] theorem homologyResidueEquiv_mk (t : ℤ) (f : Cycles R t) :
    homologyResidueEquiv (R := R) t (Submodule.Quotient.mk f) = residue t f := by
  simp [homologyResidueEquiv]

end PaperVerification.ProjectiveLineLaurentResidue
