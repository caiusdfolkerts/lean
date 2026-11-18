module

public import Unimodular.Extensions
public import Recovery.Unimodular.ProductVectorMatroid
public import Recovery.Unimodular.ProductComponents

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open Set
open scoped BigOperators Matroid

namespace Unimodular.ComponentLattice

variable {n : ℕ}

/-- The actual ordinary vector matroid on the original nonidentified labels. -/
def represented (U : Set (Lattice n)) : Matroid U :=
  VectorMatroid.ofFamily (K := ℝ) (fun u : U => embed u.val)

abbrev Components (U : Set (Lattice n)) := MatroidComponents.Component (represented U)

/-- A component's original integral vectors; this definition contains no basis choice. -/
def part (U : Set (Lattice n)) (c : Components U) : Set (Lattice n) :=
  Subtype.val '' MatroidComponents.fiber (represented U) c

def latticeSpan (U : Set (Lattice n)) (c : Components U) : Submodule ℤ (Lattice n) :=
  Submodule.span ℤ (part U c)

def realSpan (U : Set (Lattice n)) (c : Components U) : Submodule ℝ (Ambient n) :=
  Submodule.span ℝ ((fun u : U => embed u.val) ''
    MatroidComponents.fiber (represented U) c)

def basisLabel {U : Set (Lattice n)} (b : Module.Basis (Fin n) ℤ (Lattice n))
    (hb : ∀ i, b i ∈ U) (i : Fin n) : U := ⟨b i, hb i⟩

def basisComponent {U : Set (Lattice n)} (b : Module.Basis (Fin n) ℤ (Lattice n))
    (hb : ∀ i, b i ∈ U) (i : Fin n) : Components U :=
  MatroidComponents.component (represented U) (basisLabel b hb i)

theorem basisLabel_injective {U : Set (Lattice n)}
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (hb : ∀ i, b i ∈ U) :
    Function.Injective (basisLabel b hb) := by
  intro i j hij
  exact b.injective (congrArg Subtype.val hij)

/-- An integral basis contained in the configuration is a basis of its actual
ordinary real vector matroid. -/
theorem basis_isBase {U : Set (Lattice n)}
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (hb : ∀ i, b i ∈ U) :
    (represented U).IsBase (Set.range (basisLabel b hb)) := by
  have hli : LinearIndepOn ℝ (fun u : U => embed u.val)
      (Set.range (basisLabel b hb)) := by
    rw [linearIndepOn_range_iff (basisLabel_injective b hb)]
    exact embed_basis_linearIndependent b
  have htop : Submodule.span ℝ ((fun u : U => embed u.val) ''
      Set.range (basisLabel b hb)) = ⊤ := by
    apply top_unique
    intro x _
    rw [← sum_basis_realCoordinates b x]
    exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨basisLabel b hb i, ⟨i, rfl⟩, rfl⟩))
  apply Matroid.Indep.isBase_of_forall_insert
    ((VectorMatroid.ofFamily_indep _ _).mpr hli)
  intro u hu hi
  have h := (linearIndepOn_insert hu.2).mp
    ((VectorMatroid.ofFamily_indep _ _).mp hi)
  exact h.2 (by rw [htop]; trivial)

/-- A component's intrinsic real span is exactly the span of the part of any
configuration basis lying in that component. -/
theorem realSpan_eq_basis_span {U : Set (Lattice n)}
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (hb : ∀ i, b i ∈ U)
    (c : Components U) :
    realSpan U c = Submodule.span ℝ ((fun i => embed (b i)) ''
      {i | basisComponent b hb i = c}) := by
  have hbase := MatroidComponents.isBasis_inter_fiber (represented U) rfl
    (basis_isBase b hb) c
  have hs := VectorMatroid.isBasis_span_eq (fun u : U => embed u.val) hbase
  have himage : (fun u : U => embed u.val) ''
      (Set.range (basisLabel b hb) ∩ MatroidComponents.fiber (represented U) c) =
      (fun i => embed (b i)) '' {i | basisComponent b hb i = c} := by
    ext x
    constructor
    · rintro ⟨u, ⟨⟨i, rfl⟩, hi⟩, rfl⟩
      exact ⟨i, hi, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨basisLabel b hb i, ⟨⟨i, rfl⟩, hi⟩, rfl⟩
  rw [himage] at hs
  exact hs.symm

theorem coordinates_zero_outside_span (b : Module.Basis (Fin n) ℤ (Lattice n))
    {s : Set (Fin n)} {x : Ambient n}
    (hx : x ∈ Submodule.span ℝ ((fun i => embed (b i)) '' s))
    {j : Fin n} (hj : j ∉ s) : realCoordinates b x j = 0 := by
  let q : Ambient n →ₗ[ℝ] ℝ := (LinearMap.proj j).comp (realCoordinates b)
  have hs : Submodule.span ℝ ((fun i => embed (b i)) '' s) ≤ LinearMap.ker q := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, hi, rfl⟩
    have hij : i ≠ j := by rintro rfl; exact hj hi
    change realCoordinates b (embed (b i)) j = 0
    rw [realCoordinates_basis]
    simp [Pi.single_apply, hij, Ne.symm hij]
  exact hs hx

/-- Integral basis blocks are saturated in their literal real spans. -/
theorem embed_mem_basis_span_iff (b : Module.Basis (Fin n) ℤ (Lattice n))
    (s : Set (Fin n)) (x : Lattice n) :
    embed x ∈ Submodule.span ℝ ((fun i => embed (b i)) '' s) ↔
      x ∈ Submodule.span ℤ (b '' s) := by
  classical
  constructor
  · intro hx
    apply b.mem_span_image.mpr
    intro j hj
    by_contra hjs
    have hz := coordinates_zero_outside_span b hx hjs
    rw [realCoordinates_embed] at hz
    exact (Finsupp.mem_support_iff.mp hj) (Int.cast_eq_zero.mp hz)
  · intro hx
    have hs := b.repr_support_subset_of_mem_span s hx
    rw [← sum_basis_realCoordinates b (embed x)]
    apply Submodule.sum_mem
    intro i _
    by_cases hi : i ∈ s
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)
    · have hz : b.repr x i = 0 := by
        by_contra hn
        exact hi (hs (Finsupp.mem_support_iff.mpr hn))
      rw [realCoordinates_embed, hz, Int.cast_zero, zero_smul]
      exact Submodule.zero_mem _

/-- The integer span of each original component is a coordinate direct
summand in every integral configuration basis. -/
theorem latticeSpan_eq_basis_span {U : Set (Lattice n)}
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (hb : ∀ i, b i ∈ U)
    (c : Components U) :
    latticeSpan U c = Submodule.span ℤ (b '' {i | basisComponent b hb i = c}) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨u, hu, rfl⟩
    apply (embed_mem_basis_span_iff b _ u.val).mp
    rw [← realSpan_eq_basis_span b hb c]
    exact Submodule.subset_span ⟨u, hu, rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, hi, rfl⟩
    exact Submodule.subset_span ⟨basisLabel b hb i, hi, rfl⟩

/-- Saturation is stated in the original lattice and actual real embedding,
without an assumed adapted basis or a quotient-lattice surrogate. -/
theorem saturated_component {U : Set (Lattice n)}
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (hb : ∀ i, b i ∈ U)
    (c : Components U) (x : Lattice n) :
    x ∈ latticeSpan U c ↔ embed x ∈ realSpan U c := by
  rw [latticeSpan_eq_basis_span b hb c, realSpan_eq_basis_span b hb c]
  exact (embed_mem_basis_span_iff b _ x).symm

/-- Full-rank unimodularity supplies the basis used above, rather than making
the existence of an adapted integral decomposition an extra hypothesis. -/
theorem uniform_components_saturated (U : Set (Lattice n))
    (hU : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n)) (fun u : U => u.val))
    (hspan : Submodule.span ℝ (embed '' U) = ⊤) :
    ∀ c : Components U, ∀ x : Lattice n,
      x ∈ latticeSpan U c ↔ embed x ∈ realSpan U c := by
  obtain ⟨b, hb, _⟩ := LatticeHull.exists_lattice_basis_extension U hU hspan
    (fun i : Fin 0 => (Fin.elim0 i : U)) (linearIndependent_empty_type)
  exact saturated_component b hb

end Unimodular.ComponentLattice

#print axioms Unimodular.ComponentLattice.basis_isBase
#print axioms Unimodular.ComponentLattice.realSpan_eq_basis_span
#print axioms Unimodular.ComponentLattice.latticeSpan_eq_basis_span
#print axioms Unimodular.ComponentLattice.saturated_component
#print axioms Unimodular.ComponentLattice.uniform_components_saturated
#check "UNIMODULAR_COMPONENT_LATTICE_EOF_V1"
