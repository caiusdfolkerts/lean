module

public import PaperVerification.FermionPrefix
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.LinearAlgebra.ExteriorPower.Basic

/-!
# Transport from the actual suffix coefficient to the smaller exterior algebra

The smaller module is the free coordinate module on the selected prefix. Its
inclusion and coordinate restriction are explicitly split. The induced exterior
maps are inverse on the prefix span, preserve exterior degree, and transport the
odd and mixed annihilator equations without any faithfulness assumption.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PaperVerification.Fermion.Exterior

open scoped BigOperators

variable {R V J : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    [LinearOrder J] [Fintype J]

local notation "E" => ExteriorAlgebra R V

variable (b : Module.Basis J R V) (P : Finset J)

/-- Inclusion of the actual free coordinate module on the prefix. -/
def prefixInclusion : (P → R) →ₗ[R] V :=
  (Pi.basisFun R P).constr R fun i ↦ b i.val

/-- Coordinate restriction to the selected prefix. -/
def prefixRestriction : V →ₗ[R] (P → R) :=
  LinearMap.pi fun i ↦ b.coord i.val

@[simp] theorem prefixInclusion_basis (i : P) :
    prefixInclusion b P (Pi.basisFun R P i) = b i.val :=
  (Pi.basisFun R P).constr_basis R _ i

@[simp] theorem prefixRestriction_apply (w : V) (i : P) :
    prefixRestriction b P w i = b.coord i.val w := rfl

 theorem prefixRestriction_basis (i : P) :
    prefixRestriction b P (b i.val) = Pi.basisFun R P i := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [prefixRestriction_apply, Module.Basis.coord_apply, Pi.basisFun_apply]
  · have hval : j.val ≠ i.val := fun h ↦ hji (Subtype.ext h)
    simp [prefixRestriction_apply, Module.Basis.coord_apply, Pi.basisFun_apply,
      Finsupp.single_apply, Pi.single_apply, hji, (Ne.symm hji), hval, (Ne.symm hval)]

 theorem prefixRestriction_comp_inclusion :
    (prefixRestriction b P).comp (prefixInclusion b P) = LinearMap.id := by
  apply (Pi.basisFun R P).ext
  intro i
  simp only [LinearMap.comp_apply, prefixInclusion_basis, prefixRestriction_basis,
    LinearMap.id_apply]

 theorem exterior_prefixInclusion_injective :
    Function.Injective (ExteriorAlgebra.map (prefixInclusion b P)) :=
  ExteriorAlgebra.map_injective ⟨prefixRestriction b P, prefixRestriction_comp_inclusion b P⟩

 theorem prefixInclusion_restriction_basis {i : J} (hi : i ∈ P) :
    prefixInclusion b P (prefixRestriction b P (b i)) = b i := by
  have h := prefixRestriction_basis b P (⟨i, hi⟩ : P)
  rw [h, prefixInclusion_basis]

 theorem exterior_prefixInclusion_restriction_basis (T : Finset J) (hT : T ⊆ P) :
    ExteriorAlgebra.map (prefixInclusion b P)
      (ExteriorAlgebra.map (prefixRestriction b P) (b.ExteriorAlgebra T)) =
      b.ExteriorAlgebra T := by
  simp only [Module.Basis.exteriorAlgebra_eq_prod_map_sort]
  simp only [map_list_prod, List.map_map, Function.comp_apply,
    ExteriorAlgebra.map_apply_ι]
  congr 1
  apply List.map_congr_left
  intro i hi
  simp only [Function.comp_apply, ExteriorAlgebra.map_apply_ι]
  rw [prefixInclusion_restriction_basis b P (hT (by simpa using hi))]

/-- The split exterior inclusion reconstructs every prefix-supported element. -/
theorem exterior_prefixInclusion_restriction {w : E}
    (hw : w ∈ prefixExteriorSpan b P) :
    ExteriorAlgebra.map (prefixInclusion b P)
      (ExteriorAlgebra.map (prefixRestriction b P) w) = w := by
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨T, hT, rfl⟩ := hx
    exact exterior_prefixInclusion_restriction_basis b P T hT
  | zero => simp
  | add x y hx hy ihx ihy => simp only [map_add, ihx, ihy]
  | smul a x hx ih => simp only [map_smul, ih]

/-- Exact extraction followed by coordinate restriction remains nonzero. -/
theorem exterior_prefixRestriction_ne_zero {w : E}
    (hw : w ∈ prefixExteriorSpan b P) (hne : w ≠ 0) :
    ExteriorAlgebra.map (prefixRestriction b P) w ≠ 0 := by
  intro hz
  apply hne
  rw [← exterior_prefixInclusion_restriction b P hw, hz, map_zero]

/-- Coordinate restriction preserves the genuine homogeneous exterior degree. -/
theorem exterior_prefixRestriction_mem {k : ℕ} {w : E} (hw : w ∈ ⋀[R]^k V) :
    ExteriorAlgebra.map (prefixRestriction b P) w ∈ ⋀[R]^k (P → R) := by
  have h := (exteriorPower.map k (prefixRestriction b P) ⟨w, hw⟩).property
  simpa only [exteriorPower.coe_map] using h

/-- Every global odd equation transports to its literal restriction on the
smaller prefix module. -/
theorem prefix_annihilation_zero (l : Module.Dual R V) {w : E}
    (hw : w ∈ prefixExteriorSpan b P) (hl : annihilation l w = 0) :
    annihilation (l.comp (prefixInclusion b P))
      (ExteriorAlgebra.map (prefixRestriction b P) w) = 0 := by
  apply exterior_prefixInclusion_injective b P
  rw [map_zero]
  have h := ExteriorAlgebra.contractLeft_map (prefixInclusion b P) l
    (ExteriorAlgebra.map (prefixRestriction b P) w)
  rw [exterior_prefixInclusion_restriction b P hw] at h
  exact h.symm.trans hl

/-- A whole mixed-current equation transports simultaneously. Terms supported
outside the prefix become zero through their pulled-back coordinate functionals;
no individual mixed summand is assumed to annihilate the vector. -/
theorem prefix_mixed_current_zero {A : Type*} [Fintype A]
    (c : A → R) (l m : A → Module.Dual R V) {w : E}
    (hw : w ∈ prefixExteriorSpan b P)
    (hcurrent : (∑ i, c i • annihilation (l i) (annihilation (m i) w)) = 0) :
    (∑ i, c i • annihilation ((l i).comp (prefixInclusion b P))
      (annihilation ((m i).comp (prefixInclusion b P))
        (ExteriorAlgebra.map (prefixRestriction b P) w))) = 0 := by
  apply exterior_prefixInclusion_injective b P
  rw [map_zero, map_sum]
  simp only [map_smul]
  have hmap (i : A) :
      ExteriorAlgebra.map (prefixInclusion b P)
        (annihilation ((l i).comp (prefixInclusion b P))
          (annihilation ((m i).comp (prefixInclusion b P))
            (ExteriorAlgebra.map (prefixRestriction b P) w))) =
      annihilation (l i) (annihilation (m i) w) := by
    change ExteriorAlgebra.map (prefixInclusion b P)
      (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R (P → R)))
        ((l i).comp (prefixInclusion b P))
        (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R (P → R)))
          ((m i).comp (prefixInclusion b P))
          (ExteriorAlgebra.map (prefixRestriction b P) w))) = _
    rw [← ExteriorAlgebra.contractLeft_map, ← ExteriorAlgebra.contractLeft_map,
      exterior_prefixInclusion_restriction b P hw]
    rfl
  simpa only [hmap] using hcurrent

end PaperVerification.Fermion.Exterior
