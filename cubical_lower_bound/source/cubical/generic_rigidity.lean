import cubical.rigidity_linear
import cubical.generic_exactness
import Mathlib.Topology.Algebra.Module.Cardinality
import Mathlib.Topology.Baire.Lemmas

/-!
# Generic placements for rigidity and independence

A graph is generically rigid when it has an infinitesimally rigid placement.
We justify this terminology by proving that such placements form an open
dense set. The proof uses exactness of the actual motion complex, rather
than a dimension bound that might fail to characterize rigid motions at
degenerate placements.
-/

open Module Filter
open scoped InnerProductSpace Topology

namespace Cubical

/-- A property attained somewhere and having only finitely many failures
along each affine line through a good point holds densely. -/
theorem dense_of_finite_bad_along_affine_path
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (P : X → Prop) (hP : ∃ x, P x)
    (hline : ∀ a b : X, ∀ t₀ : ℝ, P (a + t₀ • b) →
      {t : ℝ | ¬ P (a + t • b)}.Finite) : Dense {x | P x} := by
  rw [dense_iff_inter_open]
  rintro U hU ⟨a, ha⟩
  obtain ⟨q, hq⟩ := hP
  have hgood : P (a + (1 : ℝ) • (q - a)) := by simpa using hq
  have hbad := hline a (q - a) 1 hgood
  have hdense := hbad.countable.dense_compl ℝ
  let line : ℝ → X := fun t => a + t • (q - a)
  have hcont : Continuous line := continuous_const.add (continuous_id.smul continuous_const)
  have hopen : IsOpen (line ⁻¹' U) := hU.preimage hcont
  have hne : (line ⁻¹' U).Nonempty := ⟨0, by simpa [line] using ha⟩
  obtain ⟨t, htU, htgood⟩ := hdense.inter_open_nonempty _ hopen hne
  exact ⟨line t, htU, by simpa [line] using htgood⟩

/-- Finite intersections of open dense sets are dense. -/
theorem dense_iInter_finite {X I : Type*} [TopologicalSpace X] [Finite I]
    (s : I → Set X) (ho : ∀ i, IsOpen (s i)) (hd : ∀ i, Dense (s i)) :
    Dense (⋂ i, s i) := by
  rw [← Set.sInter_range]
  exact (Set.finite_range s).dense_sInter (by simpa using ho) (by simpa using hd)

end Cubical

namespace Cubical.Rigidity

variable {V E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Existence of an infinitesimally rigid Euclidean placement. The open
density theorem below shows this is the usual generic rigidity property. -/
def GenericallyRigid (G : SimpleGraph V) (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] : Prop := ∃ p : V → E, IsRigid G p

section Finite

variable [Fintype V] [FiniteDimensional ℝ E]

/-- Infinitesimal rigidity can fail only finitely often along an affine
path that contains one rigid placement. -/
theorem IsRigid.finite_setOf_not_along_affine_path {G : SimpleGraph V}
    (p q : V → E) (t₀ : ℝ)
    (hrigid : IsRigid G (fun v => p v + t₀ • q v)) :
    {t : ℝ | ¬ IsRigid G (fun v => p v + t • q v)}.Finite := by
  classical
  let f : ℝ → EuclideanMotionParameters E →ₗ[ℝ] (V → E) :=
    fun t => trivialMotionMap (fun v => p v + t • q v)
  let g : ℝ → (V → E) →ₗ[ℝ] (DirectedEdge G → ℝ) :=
    fun t => motionMap G (fun v => p v + t • q v)
  have hf : ∀ a, ∃ x y : V → E, ∀ t, f t a = x + t • y := by
    intro a
    refine ⟨fun v => a.1 + a.2.val (p v), fun v => a.2.val (q v), ?_⟩
    intro t
    funext v
    simp only [f, trivialMotionMap, LinearMap.coe_mk, AddHom.coe_mk,
      map_add, map_smul, Pi.add_apply, Pi.smul_apply]
    abel
  have hg : ∀ u, ∃ x y : DirectedEdge G → ℝ, ∀ t, g t u = x + t • y := by
    intro u
    refine ⟨motionMap G p u, motionMap G q u, ?_⟩
    intro t
    funext e
    simp only [g, motionMap, LinearMap.coe_mk, AddHom.coe_mk,
      Pi.add_apply, Pi.smul_apply]
    have hs : p e.val.1 + t • q e.val.1 - (p e.val.2 + t • q e.val.2) =
        (p e.val.1 - p e.val.2) + t • (q e.val.1 - q e.val.2) := by module
    rw [hs, inner_add_left, real_inner_smul_left]
    rfl
  have hbad := Exactness.finite_setOf_range_ne_ker f g t₀ hf hg
    (fun t => motionMap_comp_trivialMotionMap G _) 
    ((isRigid_iff_range_eq_ker G _).mp hrigid)
  convert hbad using 1
  ext t
  exact not_congr (isRigid_iff_range_eq_ker G _)

/-- Rigid placements form an open set. -/
theorem isOpen_setOf_isRigid (G : SimpleGraph V) :
    IsOpen {p : V → E | IsRigid G p} := by
  apply isOpen_iff_mem_nhds.mpr
  intro p hp
  exact hp.eventually (fun q => q) p (fun v => (continuous_apply v).continuousAt)

/-- A generically rigid graph has a dense set of rigid placements. -/
theorem GenericallyRigid.dense {G : SimpleGraph V} (hG : GenericallyRigid G E) :
    Dense {p : V → E | IsRigid G p} := by
  apply Cubical.dense_of_finite_bad_along_affine_path _ hG
  intro p q t₀ h
  exact h.finite_setOf_not_along_affine_path p q t₀

omit [Fintype V] in
/-- Restricting an ambient placement to an embedded finite vertex set
preserves the open nature of rigidity. -/
theorem isOpen_setOf_isRigid_precomp {W : Type*} [Fintype W]
    (G : SimpleGraph W) (i : W ↪ V) :
    IsOpen {p : V → E | IsRigid G (p ∘ i)} := by
  have hc : Continuous (fun p : V → E => p ∘ i) :=
    continuous_pi fun w => continuous_apply (i w)
  exact (isOpen_setOf_isRigid (E := E) G).preimage hc

/-- Rigid placements on any embedded finite vertex set occur densely
among ambient placements. -/
theorem GenericallyRigid.dense_precomp {W : Type*} [Fintype W]
    {G : SimpleGraph W} (hG : GenericallyRigid G E) (i : W ↪ V) :
    Dense {p : V → E | IsRigid G (p ∘ i)} := by
  apply Cubical.dense_of_finite_bad_along_affine_path
  · obtain ⟨q, hq⟩ := hG
    refine ⟨Function.extend i q 0, ?_⟩
    simpa only [Function.extend_comp i.injective] using hq
  · intro p q t₀ h
    exact h.finite_setOf_not_along_affine_path (p ∘ i) (q ∘ i) t₀

omit [Fintype V] [FiniteDimensional ℝ E] in
/-- Independence of an embedded finite tuple is open in the placement. -/
theorem isOpen_setOf_linearIndependent_precomp {C : Type*} [Fintype C]
    (c : C ↪ V) :
    IsOpen {p : V → E | LinearIndependent ℝ (p ∘ c)} := by
  have hc : Continuous (fun p : V → E => p ∘ c) :=
    continuous_pi fun i => continuous_apply (c i)
  exact (isOpen_setOfPred_linearIndependent (𝕜 := ℝ) (E := E) (ι := C)).preimage hc

/-- Every tuple whose size is at most the ambient dimension is linearly
independent at a dense set of ambient placements. -/
theorem dense_setOf_linearIndependent_precomp {C : Type*} [Fintype C]
    (c : C ↪ V) (hcard : Fintype.card C ≤ finrank ℝ E) :
    Dense {p : V → E | LinearIndependent ℝ (p ∘ c)} := by
  classical
  apply Cubical.dense_of_finite_bad_along_affine_path
  · obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le
      (β := Fin (finrank ℝ E)) (by simpa using hcard)
    let q : C → E := fun i => Module.finBasis ℝ E (e i)
    have hq : LinearIndependent ℝ q :=
      (Module.finBasis ℝ E).linearIndependent.comp e e.injective
    refine ⟨Function.extend c q 0, ?_⟩
    simpa only [Function.extend_comp c.injective] using hq
  · intro p q t₀ h
    exact h.finite_setOf_not_along_affine_path

/-- A simultaneous placement for finitely many generically rigid graphs
on embedded vertex subsets and finitely many independent vertex tuples. -/
theorem exists_simultaneous_rigid_and_independent
    {I J : Type*} [Finite I] [Finite J]
    {W : I → Type*} [∀ i, Fintype (W i)]
    {C : J → Type*} [∀ j, Fintype (C j)]
    (G : ∀ i, SimpleGraph (W i)) (inc : ∀ i, W i ↪ V)
    (hG : ∀ i, GenericallyRigid (G i) E)
    (tuple : ∀ j, C j ↪ V)
    (hcard : ∀ j, Fintype.card (C j) ≤ finrank ℝ E) :
    ∃ p : V → E, (∀ i, IsRigid (G i) (p ∘ inc i)) ∧
      (∀ j, LinearIndependent ℝ (p ∘ tuple j)) := by
  have hR : Dense {p : V → E | ∀ i, IsRigid (G i) (p ∘ inc i)} := by
    simpa only [Set.mem_iInter, Set.mem_ofPred_eq, Set.ofPred_forall] using
      Cubical.dense_iInter_finite (fun i => {p : V → E | IsRigid (G i) (p ∘ inc i)})
        (fun i => isOpen_setOf_isRigid_precomp (G i) (inc i))
        (fun i => (hG i).dense_precomp (inc i))
  have hI : Dense {p : V → E | ∀ j, LinearIndependent ℝ (p ∘ tuple j)} := by
    simpa only [Set.mem_iInter, Set.mem_ofPred_eq, Set.ofPred_forall] using
      Cubical.dense_iInter_finite (fun j => {p : V → E | LinearIndependent ℝ (p ∘ tuple j)})
        (fun j => isOpen_setOf_linearIndependent_precomp (tuple j))
        (fun j => dense_setOf_linearIndependent_precomp (tuple j) (hcard j))
  have ho : IsOpen {p : V → E | ∀ j, LinearIndependent ℝ (p ∘ tuple j)} := by
    simp only [Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun j => isOpen_setOf_linearIndependent_precomp (tuple j)
  exact (hR.inter_of_isOpen_right hI ho).nonempty

/-- Every set of at most `dim E` vertices is sent to linearly independent
vectors. This is a convenient stronger form of the affine general
position needed for pinning and splitting. -/
def InGeneralLinearPosition (p : V → E) : Prop :=
  ∀ s : Finset V, s.card ≤ finrank ℝ E →
    LinearIndependent ℝ (fun v : s => p v)

omit [Fintype V] [FiniteDimensional ℝ E] in
/-- General linear position applies to any injectively indexed tuple of
at most the ambient dimension. -/
theorem InGeneralLinearPosition.linearIndependent {p : V → E}
    (hp : InGeneralLinearPosition p) {C : Type*} [Fintype C]
    (c : C → V) (hc : Function.Injective c)
    (hcard : Fintype.card C ≤ finrank ℝ E) :
    LinearIndependent ℝ (p ∘ c) := by
  classical
  let s : Finset V := Finset.univ.image c
  have hs : s.card ≤ finrank ℝ E := by
    simpa [s, Finset.card_image_of_injective _ hc] using hcard
  let j : C → s := fun i => ⟨c i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
  have hj : Function.Injective j := by
    intro a b hab
    exact hc (congrArg Subtype.val hab)
  exact (hp s hs).comp j hj

omit [Fintype V] [FiniteDimensional ℝ E] in
/-- Differences from one point in a small injective tuple are independent
in general linear position. -/
theorem InGeneralLinearPosition.differences {p : V → E}
    (hp : InGeneralLinearPosition p) {C : Type*} [Fintype C]
    (root : V) (c : C → V) (hc : Function.Injective c)
    (hne : ∀ i, c i ≠ root)
    (hcard : Fintype.card C + 1 ≤ finrank ℝ E) :
    LinearIndependent ℝ (fun i => p root - p (c i)) := by
  classical
  let q : Option C → V := fun i => i.elim root c
  have hq : Function.Injective q := by
    intro a b hab
    cases a with
    | none =>
      cases b with
      | none => rfl
      | some b => exact False.elim (hne b hab.symm)
    | some a =>
      cases b with
      | none => exact False.elim (hne a hab)
      | some b => exact congrArg some (hc hab)
  have hind := (hp.linearIndependent q hq (by simpa using hcard)).affineIndependent
  have hdiff := (affineIndependent_iff_linearIndependent_vsub ℝ (p ∘ q) none).mp hind
  let j : C → {i : Option C // i ≠ none} := fun i => ⟨some i, Option.some_ne_none i⟩
  have hj : Function.Injective j := by
    intro a b hab
    exact Option.some.inj (congrArg Subtype.val hab)
  have hneg := (hdiff.comp j hj).neg
  change LinearIndependent ℝ (fun i => -(p (c i) - p root)) at hneg
  simpa only [neg_sub] using hneg

/-- Finitely many generically rigid subgraphs admit one shared placement
in general linear position. -/
theorem exists_simultaneous_rigid_in_general_position
    {I : Type*} [Finite I] {W : I → Type*} [∀ i, Fintype (W i)]
    (G : ∀ i, SimpleGraph (W i)) (inc : ∀ i, W i ↪ V)
    (hG : ∀ i, GenericallyRigid (G i) E) :
    ∃ p : V → E, (∀ i, IsRigid (G i) (p ∘ inc i)) ∧ InGeneralLinearPosition p := by
  classical
  let J := {s : Finset V // s.card ≤ finrank ℝ E}
  let tuple : ∀ s : J, s.val ↪ V := fun s => ⟨Subtype.val, Subtype.val_injective⟩
  obtain ⟨p, hpG, hpI⟩ := exists_simultaneous_rigid_and_independent G inc hG tuple
    (fun s => by simpa using s.property)
  exact ⟨p, hpG, fun s hs => hpI ⟨s, hs⟩⟩

/-- A generically rigid graph has a rigid placement in general position. -/
theorem GenericallyRigid.exists_in_general_position {G : SimpleGraph V}
    (hG : GenericallyRigid G E) :
    ∃ p : V → E, IsRigid G p ∧ InGeneralLinearPosition p := by
  obtain ⟨p, hp, hpos⟩ := exists_simultaneous_rigid_in_general_position
    (fun _ : Unit => G) (fun _ => Function.Embedding.refl V) (fun _ => hG)
  exact ⟨p, hp (), hpos⟩

end Finite

end Cubical.Rigidity
