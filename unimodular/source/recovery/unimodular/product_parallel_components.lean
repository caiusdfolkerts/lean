module
public import Recovery.Unimodular.ProductComponents
public import Mathlib.Combinatorics.Matroid.Map
public import Mathlib.Combinatorics.Matroid.Loop
@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set
namespace Unimodular.MatroidComponents

variable {A B : Type*} (N : Matroid B) (f : A → B)

/-- An injectively lifted set is a circuit precisely when its image is a
circuit.  This is for ordinary matroid comap, with all labels retained. -/
theorem comap_isCircuit_iff_of_injOn {C : Set A} (hinj : Set.InjOn f C) :
    (N.comap f).IsCircuit C ↔ N.IsCircuit (f '' C) := by
  constructor
  · intro hC
    apply Matroid.isCircuit_iff.mpr
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro hi
      exact hC.not_indep (Matroid.comap_indep_iff.mpr ⟨hi, hinj⟩)
    · rintro _ ⟨a, ha, rfl⟩
      exact hC.subset_ground ha
    · intro D hD hDC
      have him : f '' (C ∩ f ⁻¹' D) = D := by
        rw [Set.image_inter_preimage, Set.inter_eq_right.mpr hDC]
      have hp : ¬ (N.comap f).Indep (C ∩ f ⁻¹' D) := by
        intro hi
        have hz := (Matroid.comap_indep_iff.mp hi).1
        rw [him] at hz
        exact hD.not_indep hz
      have heq := hC.eq_of_not_indep_subset hp Set.inter_subset_left
      rw [heq] at him
      exact him.symm
  · intro hC
    apply Matroid.isCircuit_iff.mpr
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro hi
      exact hC.not_indep (Matroid.comap_indep_iff.mp hi).1
    · intro a ha
      exact hC.subset_ground ⟨a, ha, rfl⟩
    · intro D hD hDC
      have hnot : ¬ N.Indep (f '' D) := by
        intro hi
        exact hD.not_indep (Matroid.comap_indep_iff.mpr ⟨hi, hinj.mono hDC⟩)
      have heq := hC.eq_of_not_indep_subset hnot (Set.image_mono hDC)
      apply Set.Subset.antisymm hDC
      intro c hc
      have him : f c ∈ f '' D := by rw [heq]; exact ⟨c, hc, rfl⟩
      obtain ⟨d, hd, hdc⟩ := him
      exact (hinj (hDC hd) hc hdc) ▸ hd

/-- A circuit in a comap either maps injectively to a circuit, or is a pair
of parallel copies.  In either case all its image labels have one component. -/
theorem comap_circuit_component_constant {C : Set A}
    (hC : (N.comap f).IsCircuit C) {a b : A} (ha : a ∈ C) (hb : b ∈ C) :
    component N (f a) = component N (f b) := by
  classical
  by_cases hinj : Set.InjOn f C
  · exact component_eq_of_circuit N
      ((comap_isCircuit_iff_of_injOn N f hinj).mp hC)
      ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
  · simp only [Set.InjOn, not_forall, not_imp] at hinj
    obtain ⟨x, hx, y, hy, hxy, hne⟩ := hinj
    have hp : ¬ (N.comap f).Indep ({x, y} : Set A) := by
      intro hi
      exact hne ((Matroid.comap_indep_iff.mp hi).2 (by simp) (by simp) hxy)
    have hpair : ({x, y} : Set A) = C := hC.eq_of_not_indep_subset hp (by
      intro z hz
      rcases hz with rfl | hz
      · exact hx
      · exact (Set.mem_singleton_iff.mp hz) ▸ hy)
    have hconst : ∀ z ∈ C, f z = f x := by
      intro z hz
      rw [← hpair] at hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · rfl
      · exact hxy.symm
    exact congrArg (component N) ((hconst a ha).trans (hconst b hb).symm)

/-- The canonical map on circuit-chain components induced by comap. -/
def comapComponentMap : Component (N.comap f) → Component N :=
  Quotient.lift (fun a => component N (f a)) (fun a b hab =>
    constant_on_component (N.comap f) (fun a => component N (f a))
      (fun _ hC _ ha _ hb => comap_circuit_component_constant N f hC ha hb)
      (Quotient.sound hab))

@[simp] theorem comapComponentMap_component (a : A) :
    comapComponentMap N f (component (N.comap f) a) = component N (f a) := rfl

/-- Distinct copies of a nonloop lie in the same component.  This is the
point where looplessness is mathematically necessary. -/
theorem comap_component_eq_of_image_eq {a b : A} (ha : N.IsNonloop (f a))
    (hab : f a = f b) : component (N.comap f) a = component (N.comap f) b := by
  by_cases heq : a = b
  · subst b
    rfl
  have hnon : (N.comap f).IsNonloop a := Matroid.comap_isNonloop_iff.mpr ha
  have hclosure : (N.comap f).closure {a} = (N.comap f).closure {b} := by
    simp only [Matroid.comap_closure_eq, Set.image_singleton, hab]
  have hcir := (hnon.closure_eq_closure_iff_isCircuit_of_ne heq).mp hclosure
  exact component_eq_of_circuit (N.comap f) hcir (by simp) (by simp)

/-- A section lifts each circuit injectively to a genuine circuit. -/
theorem section_image_isCircuit (g : B → A) (hg : Function.RightInverse g f)
    {C : Set B} (hC : N.IsCircuit C) : (N.comap f).IsCircuit (g '' C) := by
  have hi : Set.InjOn f (g '' C) := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ heq
    have he : a = b := by simpa only [hg a, hg b] using heq
    exact congrArg g he
  apply (comap_isCircuit_iff_of_injOn N f hi).mpr
  have he : f '' (g '' C) = C := by
    ext b
    constructor
    · rintro ⟨_, ⟨c, hc, rfl⟩, rfl⟩
      simpa only [hg c] using hc
    · intro hb
      exact ⟨g b, ⟨b, hb, rfl⟩, hg b⟩
  rwa [he]

/-- The map on components induced by an actual set-theoretic section. -/
def sectionComponentMap (g : B → A) (hg : Function.RightInverse g f) :
    Component N → Component (N.comap f) :=
  Quotient.lift (fun b => component (N.comap f) (g b)) (fun a b hab =>
    constant_on_component N (fun b => component (N.comap f) (g b))
      (fun _ hC _ ha _ hb => component_eq_of_circuit (N.comap f)
        (section_image_isCircuit N f g hg hC) ⟨_, ha, rfl⟩ ⟨_, hb, rfl⟩)
      (Quotient.sound hab))

@[simp] theorem sectionComponentMap_component (g : B → A)
    (hg : Function.RightInverse g f) (b : B) :
    sectionComponentMap N f g hg (component N b) = component (N.comap f) (g b) := rfl

/-- Surjective parallel replication preserves the exact canonical connected
component partition of every full-ground loopless matroid.  No representation,
rank, finiteness, or simplicity hypothesis is imposed. -/
def comapComponentEquiv [N.Loopless] (hE : N.E = Set.univ)
    (hf : Function.Surjective f) : Component (N.comap f) ≃ Component N := by
  let g := Function.surjInv hf
  have hg : Function.RightInverse g f := Function.rightInverse_surjInv hf
  refine ⟨comapComponentMap N f, sectionComponentMap N f g hg, ?_, ?_⟩
  · intro c
    obtain ⟨a, rfl⟩ := component_surjective (N.comap f) c
    change component (N.comap f) (g (f a)) = component (N.comap f) a
    apply comap_component_eq_of_image_eq N f
    · apply Matroid.isNonloop_of_loopless
      rw [hE]
      trivial
    · exact hg (f a)
  · intro c
    obtain ⟨b, rfl⟩ := component_surjective N c
    change component N (f (g b)) = component N b
    rw [hg b]

@[simp] theorem comapComponentEquiv_component [N.Loopless] (hE : N.E = Set.univ)
    (hf : Function.Surjective f) (a : A) :
    comapComponentEquiv N f hE hf (component (N.comap f) a) = component N (f a) := rfl

/-- Equality of ray components is exactly equality of their line components
when the ray-to-line map is a surjective parallel replication. -/
theorem comap_component_eq_iff [N.Loopless] (hE : N.E = Set.univ)
    (hf : Function.Surjective f) (a b : A) :
    component (N.comap f) a = component (N.comap f) b ↔
      component N (f a) = component N (f b) := by
  exact (comapComponentEquiv N f hE hf).injective.eq_iff.symm

end Unimodular.MatroidComponents
#print axioms Unimodular.MatroidComponents.comap_isCircuit_iff_of_injOn
#print axioms Unimodular.MatroidComponents.comap_component_eq_of_image_eq
#print axioms Unimodular.MatroidComponents.comapComponentEquiv
#print axioms Unimodular.MatroidComponents.comap_component_eq_iff
#check Unimodular.MatroidComponents.comap_component_eq_iff
