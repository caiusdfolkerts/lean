module

public import Continuation.Runtime.RationalClosure
public import Continuation.Runtime.MatroidMinorOperations
public import Continuation.Runtime.R10Verification
public import Continuation.R10.PortQuotients
public import Continuation.R10.FieldPortNormalization
public import Continuation.SeriesParallel.All
public import Recovery.Unimodular.PriorExtensions.SignedSumsFaithful
public import Lean

@[expose] public section

set_option debug.skipKernelTC false
set_option maxHeartbeats 0

/-!
# Ordinary R₁₀ minor locality and graphic/cographic nonconstructibility

The source bodies below are retained in their original order and with their
original local scopes. The manifest records every source hash. This aggregate
shares the already checked rational, R₁₀ structure, graph, and port modules;
it does not import separate copies of their declarations.
-/

/-! Injective relabelling and duality primitives are imported from their
unique `Continuation.Runtime.MatroidMinorOperations` owner. -/

/-! ## Exact source module: R10SumLocality -/
section



set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0

/-!
# An R₁₀ minor of a binary sum comes from one factor

The proof starts with Mathlib's ordinary minor relation. It contracts the actual
contracted vectors, bounds the intersection of the two quotient side spaces by
the port dimension, and moves a small surviving side to genuine port columns
of the other factor. The argument handles empty, single and triangle binary
ports uniformly and places no size bound on either factor.
-/

noncomputable section
open Set Submodule
open scoped Matroid

namespace Unimodular.SignedSums.MinorPorts

variable {K P A B L R : Type*} [Field K]
  [AddCommGroup P] [Module K P]
  [AddCommGroup A] [Module K A]
  [AddCommGroup B] [Module K B]

theorem joined_span_split (u : L → P × A) (v : R → P × B) (D : Set (L ⊕ R)) :
    span K (joinedFamily (R := K) u v '' D) =
      (span K (u '' (Sum.inl ⁻¹' D))).map (sumLeft (R := K)) ⊔
      (span K (v '' (Sum.inr ⁻¹' D))).map (sumRight (R := K)) := by
  have hD : D = Sum.inl '' (Sum.inl ⁻¹' D) ∪ Sum.inr '' (Sum.inr ⁻¹' D) := by
    ext x
    cases x <;> simp
  conv_lhs => rw [hD]
  rw [Set.image_union, span_union, Submodule.map_span, Submodule.map_span,
    Set.image_image, Set.image_image, Set.image_image, Set.image_image]
  rfl

end Unimodular.SignedSums.MinorPorts

namespace Unimodular.R10Maximality

open Unimodular.RepresentationBridge
open Unimodular.SignedSums Unimodular.SignedSums.MinorPorts

variable {K P A B T L R : Type*} [Field K]
  [AddCommGroup P] [Module K P] [Module.Finite K P]
  [AddCommGroup A] [Module K A]
  [AddCommGroup B] [Module K B]

/-- Actual R₁₀ minors cannot cross a complete port of dimension at most two. -/
theorem r10_minor_of_joined_local
    (u : L → P × A) (v : R → P × B) (ports : T → P)
    (hports : CompletePorts ports) (hdim : Module.finrank K P ≤ 2)
    (f : Fin 10 ↪ L ⊕ R)
    (hminor : r10Matroid.mapEmbedding f ≤m
      VectorMatroid.ofFamily (K := K) (joinedFamily (R := K) u v)) :
    (∃ g : Fin 10 ↪ T ⊕ L,
      r10Matroid.mapEmbedding g ≤m VectorMatroid.ofFamily (K := K)
        (Sum.elim (fun t ↦ (ports t, (0 : A))) u)) ∨
    (∃ g : Fin 10 ↪ T ⊕ R,
      r10Matroid.mapEmbedding g ≤m VectorMatroid.ofFamily (K := K)
        (Sum.elim (fun t ↦ (ports t, (0 : B))) v)) := by
  classical
  let joined := joinedFamily (R := K) u v
  obtain ⟨D, _, hM⟩ := exists_quotient_representation_of_minor r10Matroid
    (by simp [r10Matroid]) joined f hminor
  let q := (span K (joined '' D)).mkQ
  let Q := (P × (A × B)) ⧸ span K (joined '' D)
  let w : Fin 10 → Q := q ∘ joined ∘ f
  change r10Matroid = VectorMatroid.ofFamily (K := K) w at hM
  let CL : Submodule K (P × (A × B)) :=
    (span K (u '' (Sum.inl ⁻¹' D))).map (sumLeft (R := K))
  let CR : Submodule K (P × (A × B)) :=
    (span K (v '' (Sum.inr ⁻¹' D))).map (sumRight (R := K))
  have hCL : CL ≤ LinearMap.range (sumLeft (R := K)) := LinearMap.map_le_range
  have hCR : CR ≤ LinearMap.range (sumRight (R := K)) := LinearMap.map_le_range
  have hker : LinearMap.ker q = CL ⊔ CR := by
    rw [Submodule.ker_mkQ]
    exact joined_span_split u v D
  let SL := (LinearMap.range (sumLeft (R := K) (P := P) (A := A) (B := B))).map q
  let SR := (LinearMap.range (sumRight (R := K) (P := P) (A := A) (B := B))).map q
  let s : Finset (Fin 10) := Finset.univ.filter (fun i ↦ ∃ l, f i = Sum.inl l)
  have hleft (i : Fin 10) (hi : i ∈ s) : w i ∈ SL := by
    obtain ⟨l, hl⟩ : ∃ l, f i = Sum.inl l := by simpa [s] using hi
    apply Submodule.mem_map.mpr
    refine ⟨sumLeft (R := K) (u l), ⟨u l, rfl⟩, ?_⟩
    change q (sumLeft (R := K) (u l)) = q (joinedFamily (R := K) u v (f i))
    rw [hl]
    rfl
  have hright (i : Fin 10) (hi : i ∈ sᶜ) : w i ∈ SR := by
    have hn : ¬∃ l, f i = Sum.inl l := by simpa [s] using hi
    cases hf : f i with
    | inl l => exact False.elim (hn ⟨l, hf⟩)
    | inr r =>
      apply Submodule.mem_map.mpr
      refine ⟨sumRight (R := K) (v r), ⟨v r, rfl⟩, ?_⟩
      change q (sumRight (R := K) (v r)) = q (joinedFamily (R := K) u v (f i))
      rw [hf]
      rfl
  have hspanL : span K (w '' (s : Set (Fin 10))) ≤ SL := by
    apply span_le.mpr
    rintro _ ⟨i, hi, rfl⟩
    exact hleft i hi
  have hspanR : span K (w '' (sᶜ : Finset (Fin 10)) : Set _) ≤ SR := by
    apply span_le.mpr
    rintro _ ⟨i, hi, rfl⟩
    exact hright i hi
  have hportEq : SL ⊓ SR =
      (LinearMap.range (portInclusion (K := K) (P := P) (A := A) (B := B))).map q :=
    quotient_side_intersection q CL CR hCL hCR hker
  letI : Module.Finite K (SL ⊓ SR : Submodule K Q) := by
    rw [hportEq]
    infer_instance
  have hbound : Module.finrank K
      (span K (w '' (s : Set (Fin 10))) ⊓
        span K (w '' (sᶜ : Finset (Fin 10)) : Set _) : Submodule K Q) ≤ 2 :=
    (Submodule.finrank_mono (inf_le_inf hspanL hspanR)).trans
      ((quotient_side_intersection_dimension q CL CR hCL hCR hker).trans hdim)
  rcases small_side_of_intersection_dimension w hM s hbound with hs | hs
  · have hall : span K (Set.range w) ≤ SR := by
      rw [← complement_spans_of_small w hM s (by omega)]
      exact hspanR
    obtain ⟨g, hg⟩ := lift_minor_to_right u v ports hports q CL
      (Sum.inr ⁻¹' D) hCL hker w f (representation_injective w hM)
      (representation_nonzero w hM) (fun _ ↦ rfl)
      (fun i _ _ ↦ hall (subset_span ⟨i, rfl⟩))
    exact Or.inr ⟨g, by rwa [← hM] at hg⟩
  · have heq := complement_spans_of_small w hM sᶜ (by omega)
    simp only [compl_compl] at heq
    have hall : span K (Set.range w) ≤ SL := by rw [← heq]; exact hspanL
    obtain ⟨g, hg⟩ := lift_minor_to_left u v ports hports q CR
      (Sum.inl ⁻¹' D) hCR hker w f (representation_injective w hM)
      (representation_nonzero w hM) (fun _ ↦ rfl)
      (fun i _ _ ↦ hall (subset_span ⟨i, rfl⟩))
    exact Or.inl ⟨g, by rwa [← hM] at hg⟩

/-- The ordinary binary two-sum specialization, with arbitrary side sizes. -/
theorem r10_minor_single_sum {A B L R : Type*}
    [AddCommGroup A] [Module Binary.F A] [AddCommGroup B] [Module Binary.F B]
    (u : L → (Fin 1 → Binary.F) × A) (v : R → (Fin 1 → Binary.F) × B)
    (f : Fin 10 ↪ L ⊕ R)
    (hminor : r10Matroid.mapEmbedding f ≤m VectorMatroid.ofFamily (K := Binary.F)
      (joinedFamily (R := Binary.F) u v)) :
    (∃ g : Fin 10 ↪ Fin 1 ⊕ L, r10Matroid.mapEmbedding g ≤m
      VectorMatroid.ofFamily (K := Binary.F) (Binary.sideFamily Binary.singlePort u)) ∨
    (∃ g : Fin 10 ↪ Fin 1 ⊕ R, r10Matroid.mapEmbedding g ≤m
      VectorMatroid.ofFamily (K := Binary.F) (Binary.sideFamily Binary.singlePort v)) :=
  r10_minor_of_joined_local u v Binary.singlePort singlePort_complete
    (by simp) f hminor

/-- The ordinary binary three-sum specialization, with arbitrary side sizes. -/
theorem r10_minor_triangle_sum {A B L R : Type*}
    [AddCommGroup A] [Module Binary.F A] [AddCommGroup B] [Module Binary.F B]
    (u : L → (Fin 2 → Binary.F) × A) (v : R → (Fin 2 → Binary.F) × B)
    (f : Fin 10 ↪ L ⊕ R)
    (hminor : r10Matroid.mapEmbedding f ≤m VectorMatroid.ofFamily (K := Binary.F)
      (joinedFamily (R := Binary.F) u v)) :
    (∃ g : Fin 10 ↪ Fin 3 ⊕ L, r10Matroid.mapEmbedding g ≤m
      VectorMatroid.ofFamily (K := Binary.F) (Binary.sideFamily Binary.trianglePort u)) ∨
    (∃ g : Fin 10 ↪ Fin 3 ⊕ R, r10Matroid.mapEmbedding g ≤m
      VectorMatroid.ofFamily (K := Binary.F) (Binary.sideFamily Binary.trianglePort v)) :=
  r10_minor_of_joined_local u v Binary.trianglePort trianglePort_complete
    (by simp) f hminor

end Unimodular.R10Maximality
end
end

/-! ## Exact source module: R10Exclusion -/
section



set_option backward.isDefEq.respectTransparency false

/-! # Closure of the R₁₀-minor exclusion property -/

noncomputable section
open Set
open scoped Matroid

namespace Unimodular.R10Maximality
open Unimodular.RepresentationBridge
open Unimodular.SignedSums Unimodular.SignedSums.MinorPorts

/-- No injective relabelling of the ordinary R₁₀ matroid is a minor. -/
def ExcludesR10 {E : Type*} (M : Matroid E) : Prop :=
  ∀ f : Fin 10 ↪ E, ¬r10Matroid.mapEmbedding f ≤m M

theorem ExcludesR10.of_minor {E : Type*} {M N : Matroid E}
    (hM : ExcludesR10 M) (hN : N ≤m M) : ExcludesR10 N :=
  fun f hf ↦ hM f (hf.trans hN)

theorem ExcludesR10.mapEquiv {E F : Type*} {M : Matroid E}
    (hM : ExcludesR10 M) (e : E ≃ F) : ExcludesR10 (M.mapEquiv e) := by
  intro f hf
  have hback := isMinor_mapEmbedding hf e.symm.toEmbedding
  change (r10Matroid.mapEmbedding f).mapEquiv e.symm ≤m
    (M.mapEquiv e).mapEquiv e.symm at hback
  rw [mapEquiv_symm_cancel] at hback
  change (r10Matroid.mapEmbedding f).mapEmbedding e.symm.toEmbedding ≤m M at hback
  rw [mapEmbedding_comp] at hback
  exact hM _ hback

theorem ExcludesR10.dual {E : Type*} {M : Matroid E}
    (hM : ExcludesR10 M) : ExcludesR10 M✶ := by
  intro f hf
  have hd := Unimodular.RepresentationBridge.isMinor_dual hf
  rw [Matroid.dual_dual, mapEmbedding_dual, r10_selfdual] at hd
  change (r10Matroid.mapEmbedding swapReflect.toEmbedding).mapEmbedding f ≤m M at hd
  rw [mapEmbedding_comp] at hd
  exact hM _ hd

theorem ExcludesR10.joined {K P A B T L R : Type*} [Field K]
    [AddCommGroup P] [Module K P] [Module.Finite K P]
    [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B]
    (u : L → P × A) (v : R → P × B) (ports : T → P)
    (hports : CompletePorts ports) (hdim : Module.finrank K P ≤ 2)
    (hu : ExcludesR10 (VectorMatroid.ofFamily (K := K)
      (Sum.elim (fun t ↦ (ports t, (0 : A))) u)))
    (hv : ExcludesR10 (VectorMatroid.ofFamily (K := K)
      (Sum.elim (fun t ↦ (ports t, (0 : B))) v))) :
    ExcludesR10 (VectorMatroid.ofFamily (K := K) (joinedFamily (R := K) u v)) := by
  intro f hf
  rcases r10_minor_of_joined_local u v ports hports hdim f hf with ⟨g, hg⟩ | ⟨g, hg⟩
  · exact hu g hg
  · exact hv g hg

/-- The intrinsic ordinary-matroid sum and the displayed binary quotient are
equal, rather than merely assigned the same name. -/
theorem ordinaryPortSum_eq_joined {P A B T L R : Type*}
    [AddCommGroup P] [Module Binary.F P]
    [AddCommGroup A] [Module Binary.F A] [AddCommGroup B] [Module Binary.F B]
    [Fintype T] [Fintype L] [Fintype R]
    (u : L → P × A) (v : R → P × B) (ports : T → P)
    (hports : CompletePorts ports)
    {M : Matroid (L ⊕ R)} {M₁ : Matroid (T ⊕ L)} {M₂ : Matroid (T ⊕ R)}
    (hM : IsOrdinaryPortSum M M₁ M₂)
    (h₁ : M₁ = VectorMatroid.ofFamily (K := Binary.F) (Binary.sideFamily ports u))
    (h₂ : M₂ = VectorMatroid.ofFamily (K := Binary.F) (Binary.sideFamily ports v)) :
    M = VectorMatroid.ofFamily (K := Binary.F) (joinedFamily (R := Binary.F) u v) := by
  have hspan : Submodule.span Binary.F (Set.range ports) = ⊤ := by
    apply top_unique
    intro p _
    rcases hports p with rfl | ⟨t, rfl⟩
    · exact Submodule.zero_mem _
    · exact Submodule.subset_span ⟨t, rfl⟩
  exact hM.unique (ordinaryPortSum_of_isPortSum
    (Binary.joined_matroid_isPortSum ports hspan u v) h₁ h₂)

theorem ExcludesR10.ordinaryPortSum {P A B T L R : Type*}
    [AddCommGroup P] [Module Binary.F P] [Module.Finite Binary.F P]
    [AddCommGroup A] [Module Binary.F A] [AddCommGroup B] [Module Binary.F B]
    [Fintype T] [Fintype L] [Fintype R]
    (u : L → P × A) (v : R → P × B) (ports : T → P)
    (hports : CompletePorts ports) (hdim : Module.finrank Binary.F P ≤ 2)
    {M : Matroid (L ⊕ R)} {M₁ : Matroid (T ⊕ L)} {M₂ : Matroid (T ⊕ R)}
    (hM : IsOrdinaryPortSum M M₁ M₂)
    (h₁ : M₁ = VectorMatroid.ofFamily (K := Binary.F) (Binary.sideFamily ports u))
    (h₂ : M₂ = VectorMatroid.ofFamily (K := Binary.F) (Binary.sideFamily ports v))
    (hfree₁ : ExcludesR10 M₁) (hfree₂ : ExcludesR10 M₂) : ExcludesR10 M := by
  rw [ordinaryPortSum_eq_joined u v ports hports hM h₁ h₂]
  apply ExcludesR10.joined u v ports hports hdim
  · simpa only [h₁, Binary.sideFamily] using hfree₁
  · simpa only [h₂, Binary.sideFamily] using hfree₂

end Unimodular.R10Maximality
end
end

/-! ## Exact source module: R10OrdinarySums -/
section



set_option backward.isDefEq.respectTransparency false

/-!
# R₁₀ locality for the intrinsic ordinary binary sum rule

The input representations are arbitrary. The singleton and triangle port
hypotheses are ordinary matroid predicates, and the output is specified by
its intrinsic matched-circuit rule. Product coordinates are constructed in the
proof, so they are absent from the hypotheses and conclusions.
-/

noncomputable section
open scoped Matroid

namespace Unimodular.R10Maximality
open Unimodular.SignedSums Unimodular.SignedSums.MinorPorts

variable {V W L R : Type*} [AddCommGroup V] [Module Binary.F V]
  [AddCommGroup W] [Module Binary.F W] [Fintype L] [Fintype R]

theorem r10_minor_ordinary_one_sum
    (u : Fin 0 ⊕ L → V) (v : Fin 0 ⊕ R → W)
    {M : Matroid (L ⊕ R)}
    (hM : IsOrdinaryPortSum M (VectorMatroid.ofFamily (K := Binary.F) u)
      (VectorMatroid.ofFamily (K := Binary.F) v))
    (f : Fin 10 ↪ L ⊕ R) (hf : r10Matroid.mapEmbedding f ≤m M) :
    (∃ g : Fin 10 ↪ Fin 0 ⊕ L, r10Matroid.mapEmbedding g ≤m
      VectorMatroid.ofFamily (K := Binary.F) u) ∨
    (∃ g : Fin 10 ↪ Fin 0 ⊕ R, r10Matroid.mapEmbedding g ≤m
      VectorMatroid.ofFamily (K := Binary.F) v) := by
  obtain ⟨N₁, u₁, h₁⟩ := Binary.empty_port_normal_form u
  obtain ⟨N₂, u₂, h₂⟩ := Binary.empty_port_normal_form v
  have houtput := ordinaryPortSum_eq_joined u₁ u₂
    (Fin.elim0 : Fin 0 → Fin 0 → Binary.F) emptyPort_complete hM h₁ h₂
  rw [houtput] at hf
  simpa only [h₁, h₂, Binary.sideFamily] using
    r10_minor_of_joined_local u₁ u₂
      (Fin.elim0 : Fin 0 → Fin 0 → Binary.F) emptyPort_complete (by simp) f hf

theorem r10_minor_ordinary_two_sum
    (u : Fin 1 ⊕ L → V) (v : Fin 1 ⊕ R → W)
    (hu : (VectorMatroid.ofFamily (K := Binary.F) u).Indep
      (Set.range (Sum.inl : Fin 1 → Fin 1 ⊕ L)))
    (hv : (VectorMatroid.ofFamily (K := Binary.F) v).Indep
      (Set.range (Sum.inl : Fin 1 → Fin 1 ⊕ R)))
    {M : Matroid (L ⊕ R)}
    (hM : IsOrdinaryPortSum M (VectorMatroid.ofFamily (K := Binary.F) u)
      (VectorMatroid.ofFamily (K := Binary.F) v))
    (f : Fin 10 ↪ L ⊕ R) (hf : r10Matroid.mapEmbedding f ≤m M) :
    (∃ g : Fin 10 ↪ Fin 1 ⊕ L, r10Matroid.mapEmbedding g ≤m
      VectorMatroid.ofFamily (K := Binary.F) u) ∨
    (∃ g : Fin 10 ↪ Fin 1 ⊕ R, r10Matroid.mapEmbedding g ≤m
      VectorMatroid.ofFamily (K := Binary.F) v) := by
  obtain ⟨N₁, u₁, h₁⟩ := Binary.single_port_normal_form u hu
  obtain ⟨N₂, u₂, h₂⟩ := Binary.single_port_normal_form v hv
  have houtput := ordinaryPortSum_eq_joined u₁ u₂ Binary.singlePort
    singlePort_complete hM h₁ h₂
  rw [houtput] at hf
  simpa only [h₁, h₂] using r10_minor_single_sum u₁ u₂ f hf

theorem r10_minor_ordinary_three_sum
    (u : Fin 3 ⊕ L → V) (v : Fin 3 ⊕ R → W)
    (hu : (VectorMatroid.ofFamily (K := Binary.F) u).IsCircuit
      (Set.range (Sum.inl : Fin 3 → Fin 3 ⊕ L)))
    (hv : (VectorMatroid.ofFamily (K := Binary.F) v).IsCircuit
      (Set.range (Sum.inl : Fin 3 → Fin 3 ⊕ R)))
    {M : Matroid (L ⊕ R)}
    (hM : IsOrdinaryPortSum M (VectorMatroid.ofFamily (K := Binary.F) u)
      (VectorMatroid.ofFamily (K := Binary.F) v))
    (f : Fin 10 ↪ L ⊕ R) (hf : r10Matroid.mapEmbedding f ≤m M) :
    (∃ g : Fin 10 ↪ Fin 3 ⊕ L, r10Matroid.mapEmbedding g ≤m
      VectorMatroid.ofFamily (K := Binary.F) u) ∨
    (∃ g : Fin 10 ↪ Fin 3 ⊕ R, r10Matroid.mapEmbedding g ≤m
      VectorMatroid.ofFamily (K := Binary.F) v) := by
  obtain ⟨N₁, u₁, h₁⟩ := Binary.triangle_port_normal_form u hu
  obtain ⟨N₂, u₂, h₂⟩ := Binary.triangle_port_normal_form v hv
  have houtput := ordinaryPortSum_eq_joined u₁ u₂ Binary.trianglePort
    trianglePort_complete hM h₁ h₂
  rw [houtput] at hf
  simpa only [h₁, h₂] using r10_minor_triangle_sum u₁ u₂ f hf

theorem ExcludesR10.ordinary_two_sum
    (u : Fin 1 ⊕ L → V) (v : Fin 1 ⊕ R → W)
    (hu : (VectorMatroid.ofFamily (K := Binary.F) u).Indep
      (Set.range (Sum.inl : Fin 1 → Fin 1 ⊕ L)))
    (hv : (VectorMatroid.ofFamily (K := Binary.F) v).Indep
      (Set.range (Sum.inl : Fin 1 → Fin 1 ⊕ R)))
    {M : Matroid (L ⊕ R)}
    (hM : IsOrdinaryPortSum M (VectorMatroid.ofFamily (K := Binary.F) u)
      (VectorMatroid.ofFamily (K := Binary.F) v))
    (hfree₁ : ExcludesR10 (VectorMatroid.ofFamily (K := Binary.F) u))
    (hfree₂ : ExcludesR10 (VectorMatroid.ofFamily (K := Binary.F) v)) : ExcludesR10 M := by
  intro f hf
  rcases r10_minor_ordinary_two_sum u v hu hv hM f hf with ⟨g, hg⟩ | ⟨g, hg⟩
  · exact hfree₁ g hg
  · exact hfree₂ g hg

theorem ExcludesR10.ordinary_one_sum
    (u : Fin 0 ⊕ L → V) (v : Fin 0 ⊕ R → W)
    {M : Matroid (L ⊕ R)}
    (hM : IsOrdinaryPortSum M (VectorMatroid.ofFamily (K := Binary.F) u)
      (VectorMatroid.ofFamily (K := Binary.F) v))
    (hfree₁ : ExcludesR10 (VectorMatroid.ofFamily (K := Binary.F) u))
    (hfree₂ : ExcludesR10 (VectorMatroid.ofFamily (K := Binary.F) v)) : ExcludesR10 M := by
  intro f hf
  rcases r10_minor_ordinary_one_sum u v hM f hf with ⟨g, hg⟩ | ⟨g, hg⟩
  · exact hfree₁ g hg
  · exact hfree₂ g hg

theorem ExcludesR10.ordinary_three_sum
    (u : Fin 3 ⊕ L → V) (v : Fin 3 ⊕ R → W)
    (hu : (VectorMatroid.ofFamily (K := Binary.F) u).IsCircuit
      (Set.range (Sum.inl : Fin 3 → Fin 3 ⊕ L)))
    (hv : (VectorMatroid.ofFamily (K := Binary.F) v).IsCircuit
      (Set.range (Sum.inl : Fin 3 → Fin 3 ⊕ R)))
    {M : Matroid (L ⊕ R)}
    (hM : IsOrdinaryPortSum M (VectorMatroid.ofFamily (K := Binary.F) u)
      (VectorMatroid.ofFamily (K := Binary.F) v))
    (hfree₁ : ExcludesR10 (VectorMatroid.ofFamily (K := Binary.F) u))
    (hfree₂ : ExcludesR10 (VectorMatroid.ofFamily (K := Binary.F) v)) : ExcludesR10 M := by
  intro f hf
  rcases r10_minor_ordinary_three_sum u v hu hv hM f hf with ⟨g, hg⟩ | ⟨g, hg⟩
  · exact hfree₁ g hg
  · exact hfree₂ g hg

end Unimodular.R10Maximality
end
end

/-! ## Exact source module: R10GraphObstruction -/
section



set_option backward.isDefEq.respectTransparency false

/-! # R₁₀ is neither a graph cycle matroid nor its dual -/

open scoped Matroid

namespace Unimodular.R10Maximality
open Unimodular.SeriesParallel

theorem incidence_cycle_eq_of_ground_univ {V : Type*} [DecidableEq V]
    (G : IncidenceGraph V (Fin 10)) (hE : G.edges = Set.univ) :
    G.cycleMatroid = VectorMatroid.ofFamily (K := ℝ)
      (incidenceFamily G.source G.target) := by
  have hu : G.column = incidenceFamily G.source G.target := by
    funext j v
    by_cases hs : v = G.source j <;> by_cases ht : v = G.target j <;>
      simp [IncidenceGraph.column, IncidenceGraph.vertex, incidenceFamily, Pi.single_apply,
        hs, ht]
  change VectorMatroid.onSet (K := ℝ) G.column G.edges = _
  rw [hE, hu]
  rfl

theorem r10_ne_cycleMatroid {V : Type*} [DecidableEq V]
    (G : IncidenceGraph V (Fin 10)) : r10Matroid ≠ G.cycleMatroid := by
  intro hM
  have hE : G.edges = Set.univ := by
    have hx := congrArg Matroid.E hM
    simpa [r10Matroid, IncidenceGraph.cycleMatroid] using hx.symm
  rw [incidence_cycle_eq_of_ground_univ G hE] at hM
  exact no_graphic_family G.source G.target hM

theorem r10_ne_dual_cycleMatroid {V : Type*} [DecidableEq V]
    (G : IncidenceGraph V (Fin 10)) : r10Matroid ≠ G.cycleMatroid✶ := by
  intro hM
  have hE : G.edges = Set.univ := by
    have hx := congrArg Matroid.E hM
    simpa [r10Matroid, IncidenceGraph.cycleMatroid] using hx.symm
  rw [incidence_cycle_eq_of_ground_univ G hE] at hM
  exact no_cographic_family G.source G.target hM

end Unimodular.R10Maximality
end

/-! ## Exact source module: R10GraphicMinor -/
section



/-!
# Graphic and cographic matroids exclude an R₁₀ minor

Every finite contraction/deletion of a graph cycle matroid is realized by
literal graph operations. This connects the ordinary-matroid R₁₀ obstruction
to larger configurations with an embedded R₁₀ minor.
-/

set_option backward.isDefEq.respectTransparency false
open Set
open scoped Matroid

namespace Unimodular.R10Maximality
open Unimodular.SeriesParallel

theorem exists_cycleMatroid_contract_singleton {V E : Type*}
    (G : IncidenceGraph V E) (e : E) :
    ∃ H : IncidenceGraph V E, H.cycleMatroid = G.cycleMatroid ／ {e} := by
  classical
  by_cases he : e ∈ G.edges
  · by_cases hne : G.source e ≠ G.target e
    · exact ⟨G.contract e, G.cycleMatroid_contract e he hne⟩
    · have heq := not_not.mp hne
      have hl : G.cycleMatroid.IsLoop e := by
        rw [← Matroid.singleton_not_indep he]
        simp [IncidenceGraph.cycleMatroid, VectorMatroid.onSet_indep,
          linearIndepOn_singleton_iff, IncidenceGraph.column, heq]
      refine ⟨G.delete {e}, ?_⟩
      rw [IncidenceGraph.cycleMatroid_delete]
      exact (Matroid.contract_eq_delete_of_subset_loops
        (Set.singleton_subset_iff.mpr hl)).symm
  · have hd : Disjoint ({e} : Set E) G.cycleMatroid.E :=
      Set.disjoint_singleton_left.mpr he
    exact ⟨G, (Matroid.contract_eq_self_iff.mpr hd).symm⟩

theorem exists_cycleMatroid_contract_finset {V E : Type*}
    (G : IncidenceGraph V E) (C : Finset E) :
    ∃ H : IncidenceGraph V E, H.cycleMatroid = G.cycleMatroid ／ (C : Set E) := by
  classical
  induction C using Finset.induction_on with
  | empty => exact ⟨G, by simp⟩
  | @insert e C he ih =>
      obtain ⟨H, hH⟩ := ih
      obtain ⟨J, hJ⟩ := exists_cycleMatroid_contract_singleton H e
      refine ⟨J, ?_⟩
      rw [hJ, hH, Matroid.contract_contract]
      congr 1
      simp [Finset.coe_insert, Set.union_comm]

theorem exists_cycleMatroid_of_minor {V E : Type*} [Fintype E]
    (G : IncidenceGraph V E) {N : Matroid E} (hN : N ≤m G.cycleMatroid) :
    ∃ H : IncidenceGraph V E, H.cycleMatroid = N := by
  classical
  obtain ⟨C, D, rfl⟩ := hN
  obtain ⟨H, hH⟩ := exists_cycleMatroid_contract_finset G C.toFinset
  refine ⟨H.delete D, ?_⟩
  rw [IncidenceGraph.cycleMatroid_delete, hH]
  simp

theorem of_mapEmbedding_eq_cycleMatroid {V E : Type*} [DecidableEq V]
    (M : Matroid (Fin 10)) (hME : M.E = Set.univ) (f : Fin 10 ↪ E)
    (G : IncidenceGraph V E) (hM : M.mapEmbedding f = G.cycleMatroid) :
    M = VectorMatroid.ofFamily (K := ℝ)
      (incidenceFamily (G.source ∘ f) (G.target ∘ f)) := by
  have hE : G.edges = Set.range f := by
    have hx := congrArg Matroid.E hM
    simpa [IncidenceGraph.cycleMatroid, hME] using hx.symm
  have hh := VectorMatroid.ofFamily_mapEmbedding_eq_onSet
    (K := ℝ) (G.column ∘ f) G.column f (fun _ ↦ rfl)
  rw [← hE] at hh
  change (VectorMatroid.ofFamily (K := ℝ) (G.column ∘ f)).mapEmbedding f =
    G.cycleMatroid at hh
  have heq := hM.trans hh.symm
  have hfamily : G.column ∘ f = incidenceFamily (G.source ∘ f) (G.target ∘ f) := by
    funext j v
    by_cases hs : v = G.source (f j) <;> by_cases ht : v = G.target (f j) <;>
      simp [IncidenceGraph.column, IncidenceGraph.vertex, incidenceFamily, Pi.single_apply,
        hs, ht]
  rw [hfamily] at heq
  apply Matroid.ext_indep (by simpa using hME)
  intro I hI
  have hi := Eq.to_iff (congrArg (fun N : Matroid E ↦ N.Indep (f '' I)) heq)
  simpa [Matroid.mapEmbedding_indep_iff, Set.preimage_image_eq I f.injective] using hi

theorem r10_not_minor_cycleMatroid {V E : Type*} [Fintype E]
    (G : IncidenceGraph V E) (f : Fin 10 ↪ E) :
    ¬r10Matroid.mapEmbedding f ≤m G.cycleMatroid := by
  classical
  intro h
  obtain ⟨H, hH⟩ := exists_cycleMatroid_of_minor G h
  have hm := of_mapEmbedding_eq_cycleMatroid r10Matroid (by simp [r10Matroid]) f H hH.symm
  exact no_graphic_family (H.source ∘ f) (H.target ∘ f) hm

theorem isMinor_dual {E : Type*} {N M : Matroid E} (h : N ≤m M) : N✶ ≤m M✶ := by
  obtain ⟨C, D, _, _, hCD, rfl⟩ := h.exists_eq_contract_delete_disjoint
  refine ⟨D, C, ?_⟩
  rw [Matroid.dual_delete, Matroid.dual_contract,
    ← Matroid.contract_delete_comm _ hCD.symm]

theorem r10_not_minor_dual_cycleMatroid {V E : Type*} [Fintype E]
    (G : IncidenceGraph V E) (f : Fin 10 ↪ E) :
    ¬r10Matroid.mapEmbedding f ≤m G.cycleMatroid✶ := by
  classical
  intro h
  have hd : (r10Matroid.mapEmbedding f)✶ ≤m G.cycleMatroid := by
    simpa using isMinor_dual h
  obtain ⟨H, hH⟩ := exists_cycleMatroid_of_minor G hd
  have hmap : r10Matroid✶.mapEmbedding f = H.cycleMatroid := by
    simpa [Matroid.mapEmbedding, Matroid.map_dual] using hH.symm
  have hm := of_mapEmbedding_eq_cycleMatroid r10Matroid✶
    (by simp [r10Matroid]) f H hmap
  have hm' := congrArg Matroid.dual hm
  apply no_cographic_family (H.source ∘ f) (H.target ∘ f)
  simpa using hm'

end Unimodular.R10Maximality
end

/-! ## Exact source module: FiniteRepresentability -/
section



set_option backward.isDefEq.respectTransparency false

/-! # Finite field representations and their closure operations -/

noncomputable section
open Set Submodule
open scoped Matroid BigOperators

namespace Unimodular.RepresentationBridge

open Unimodular.SignedSums Unimodular.SignedSums.MinorPorts
open Unimodular.R10Maximality

theorem HasFiniteRepresentation.ordinary_one_sum {L R : Type*}
    [Fintype L] [Fintype R] {M : Matroid (L ⊕ R)}
    {M₁ : Matroid (Fin 0 ⊕ L)} {M₂ : Matroid (Fin 0 ⊕ R)}
    (h₁ : HasFiniteRepresentation Binary.F M₁)
    (h₂ : HasFiniteRepresentation Binary.F M₂)
    (hM : IsOrdinaryPortSum M M₁ M₂) : HasFiniteRepresentation Binary.F M := by
  obtain ⟨n, u, rfl⟩ := h₁
  obtain ⟨m, v, rfl⟩ := h₂
  obtain ⟨N₁, u₁, hu⟩ := Binary.empty_port_normal_form u
  obtain ⟨N₂, u₂, hv⟩ := Binary.empty_port_normal_form v
  rw [ordinaryPortSum_eq_joined u₁ u₂
    (Fin.elim0 : Fin 0 → Fin 0 → Binary.F) emptyPort_complete hM hu hv]
  exact hasFiniteRepresentation_ofFamily _

theorem HasFiniteRepresentation.ordinary_two_sum {L R : Type*}
    [Fintype L] [Fintype R] {M : Matroid (L ⊕ R)}
    {M₁ : Matroid (Fin 1 ⊕ L)} {M₂ : Matroid (Fin 1 ⊕ R)}
    (h₁ : HasFiniteRepresentation Binary.F M₁)
    (h₂ : HasFiniteRepresentation Binary.F M₂)
    (hport₁ : M₁.Indep (Set.range (Sum.inl : Fin 1 → Fin 1 ⊕ L)))
    (hport₂ : M₂.Indep (Set.range (Sum.inl : Fin 1 → Fin 1 ⊕ R)))
    (hM : IsOrdinaryPortSum M M₁ M₂) : HasFiniteRepresentation Binary.F M := by
  obtain ⟨n, u, rfl⟩ := h₁
  obtain ⟨m, v, rfl⟩ := h₂
  obtain ⟨N₁, u₁, hu⟩ := Binary.single_port_normal_form u hport₁
  obtain ⟨N₂, u₂, hv⟩ := Binary.single_port_normal_form v hport₂
  rw [ordinaryPortSum_eq_joined u₁ u₂ Binary.singlePort singlePort_complete hM hu hv]
  exact hasFiniteRepresentation_ofFamily _

theorem HasFiniteRepresentation.ordinary_three_sum {L R : Type*}
    [Fintype L] [Fintype R] {M : Matroid (L ⊕ R)}
    {M₁ : Matroid (Fin 3 ⊕ L)} {M₂ : Matroid (Fin 3 ⊕ R)}
    (h₁ : HasFiniteRepresentation Binary.F M₁)
    (h₂ : HasFiniteRepresentation Binary.F M₂)
    (hport₁ : M₁.IsCircuit (Set.range (Sum.inl : Fin 3 → Fin 3 ⊕ L)))
    (hport₂ : M₂.IsCircuit (Set.range (Sum.inl : Fin 3 → Fin 3 ⊕ R)))
    (hM : IsOrdinaryPortSum M M₁ M₂) : HasFiniteRepresentation Binary.F M := by
  obtain ⟨n, u, rfl⟩ := h₁
  obtain ⟨m, v, rfl⟩ := h₂
  obtain ⟨N₁, u₁, hu⟩ := Binary.triangle_port_normal_form u hport₁
  obtain ⟨N₂, u₂, hv⟩ := Binary.triangle_port_normal_form v hport₂
  rw [ordinaryPortSum_eq_joined u₁ u₂ Binary.trianglePort trianglePort_complete hM hu hv]
  exact hasFiniteRepresentation_ofFamily _

open Unimodular.SeriesParallel

theorem incidence_integer_totallyUnimodular {V E : Type*} [DecidableEq V]
    (a b : E → V) : Matrix.IsTotallyUnimodular
      (fun (i : V) (j : E) ↦
        (Pi.single (a j) (1 : ℤ) : V → ℤ) i -
          (Pi.single (b j) (1 : ℤ) : V → ℤ) i) := by
  let A : Matrix V E ℤ := fun i j ↦
    (Pi.single (a j) (1 : ℤ) : V → ℤ) i -
      (Pi.single (b j) (1 : ℤ) : V → ℤ) i
  change A.IsTotallyUnimodular
  intro n f g hf _
  have hcol (j : E) : Graphic.IncidenceColumn (fun i ↦ A i j) := by
    simpa [A, Graphic.endpoint, Pi.single_apply, eq_comm] using
      Graphic.endpoint_difference_column (some (a j)) (some (b j))
  have h := Graphic.all_minors_abs_le_one A hcol f hf g
  have hb := abs_le.mp h
  rcases (show (A.submatrix f g).det = 0 ∨
      (A.submatrix f g).det = 1 ∨ (A.submatrix f g).det = -1 by omega) with h0 | h1 | hm
  · exact ⟨0, by simp [h0]⟩
  · exact ⟨1, by simp [h1]⟩
  · exact ⟨-1, by simp [hm]⟩

theorem graph_hasFiniteRepresentation {V E K : Type*} [Fintype V] [Fintype E]
    [Field K] (G : IncidenceGraph V E) (hE : G.edges = Set.univ) :
    HasFiniteRepresentation K G.cycleMatroid := by
  classical
  let A : Matrix V E ℤ := fun i j ↦
    (Pi.single (G.source j) (1 : ℤ) : V → ℤ) i -
      (Pi.single (G.target j) (1 : ℤ) : V → ℤ) i
  have hTU : A.IsTotallyUnimodular :=
    incidence_integer_totallyUnimodular G.source G.target
  have hg : G.cycleMatroid =
      VectorMatroid.ofFamily (K := ℝ) (fun j i ↦ (A i j : ℝ)) := by
    unfold IncidenceGraph.cycleMatroid VectorMatroid.ofFamily
    rw [hE]
    congr 1
    funext j i
    simp [A, IncidenceGraph.column, IncidenceGraph.vertex, Pi.single_apply]
  rw [hg, tu_matroid_field_invariant (F := K) A hTU]
  exact hasFiniteRepresentation_ofFamily _

end Unimodular.RepresentationBridge
end
end

/-! ## Exact source module: GraphicCographicConstruction -/
section



set_option backward.isDefEq.respectTransparency false

/-!
# The intrinsic graphic/cographic construction class

The generators are finite graph cycle matroids and their ordinary duals.
Relabelling, duality and the intrinsic ordinary 1-, 2- and 3-sum rules are the
constructors. Binary representability is proved by induction; it is not an
extra hypothesis in the definition. The singleton/triangle port conditions
are stated using the ordinary input matroids. We allow more port sums than
Seymour's usual nondegenerate size/cocircuit conventions, so exclusion from
this class also excludes every such conventional construction.
-/

noncomputable section
open scoped Matroid

namespace Unimodular.R10Maximality

open Unimodular.SeriesParallel Unimodular.SignedSums
open Unimodular.RepresentationBridge

universe u

/-- The closure under the stated, intrinsic operations. The definition makes
no reference to R₁₀, its minors, or a prechosen binary realization. -/
inductive GraphicCographicConstructible : {E : Type u} → Matroid E → Prop
  | graphic {E V : Type u} [Fintype E] [Fintype V]
      (G : IncidenceGraph V E) (hE : G.edges = Set.univ) :
      GraphicCographicConstructible G.cycleMatroid
  | cographic {E V : Type u} [Fintype E] [Fintype V]
      (G : IncidenceGraph V E) (hE : G.edges = Set.univ) :
      GraphicCographicConstructible G.cycleMatroid✶
  | relabel {E F : Type u} {M : Matroid E}
      (hM : GraphicCographicConstructible M) (e : E ≃ F) :
      GraphicCographicConstructible (M.mapEquiv e)
  | dual {E : Type u} [Fintype E] {M : Matroid E}
      (hM : GraphicCographicConstructible M) : GraphicCographicConstructible M✶
  | one_sum {L R : Type u} [Fintype L] [Fintype R]
      {M₁ : Matroid (Fin 0 ⊕ L)} {M₂ : Matroid (Fin 0 ⊕ R)} {M : Matroid (L ⊕ R)}
      (h₁ : GraphicCographicConstructible M₁) (h₂ : GraphicCographicConstructible M₂)
      (hM : IsOrdinaryPortSum M M₁ M₂) : GraphicCographicConstructible M
  | two_sum {L R : Type u} [Fintype L] [Fintype R]
      {M₁ : Matroid (Fin 1 ⊕ L)} {M₂ : Matroid (Fin 1 ⊕ R)} {M : Matroid (L ⊕ R)}
      (h₁ : GraphicCographicConstructible M₁) (h₂ : GraphicCographicConstructible M₂)
      (hp₁ : M₁.Indep (Set.range (Sum.inl : Fin 1 → Fin 1 ⊕ L)))
      (hp₂ : M₂.Indep (Set.range (Sum.inl : Fin 1 → Fin 1 ⊕ R)))
      (hM : IsOrdinaryPortSum M M₁ M₂) : GraphicCographicConstructible M
  | three_sum {L R : Type u} [Fintype L] [Fintype R]
      {M₁ : Matroid (Fin 3 ⊕ L)} {M₂ : Matroid (Fin 3 ⊕ R)} {M : Matroid (L ⊕ R)}
      (h₁ : GraphicCographicConstructible M₁) (h₂ : GraphicCographicConstructible M₂)
      (hp₁ : M₁.IsCircuit (Set.range (Sum.inl : Fin 3 → Fin 3 ⊕ L)))
      (hp₂ : M₂.IsCircuit (Set.range (Sum.inl : Fin 3 → Fin 3 ⊕ R)))
      (hM : IsOrdinaryPortSum M M₁ M₂) : GraphicCographicConstructible M

theorem GraphicCographicConstructible.binary_and_excludesR10 {E : Type u}
    {M : Matroid E} (hM : GraphicCographicConstructible M) :
    HasFiniteRepresentation Binary.F M ∧ ExcludesR10 M := by
  induction hM with
  | graphic G hE =>
      exact ⟨graph_hasFiniteRepresentation G hE, r10_not_minor_cycleMatroid G⟩
  | cographic G hE =>
      exact ⟨(graph_hasFiniteRepresentation (K := Binary.F) G hE).dual,
        r10_not_minor_dual_cycleMatroid G⟩
  | relabel h e ih => exact ⟨ih.1.mapEquiv e, ih.2.mapEquiv e⟩
  | dual h ih => exact ⟨ih.1.dual, ih.2.dual⟩
  | one_sum h₁ h₂ hM ih₁ ih₂ =>
      refine ⟨ih₁.1.ordinary_one_sum ih₂.1 hM, ?_⟩
      obtain ⟨n, u, hu⟩ := ih₁.1
      obtain ⟨m, v, hv⟩ := ih₂.1
      exact ExcludesR10.ordinary_one_sum u v (by simpa only [← hu, ← hv] using hM)
        (by simpa only [← hu] using ih₁.2) (by simpa only [← hv] using ih₂.2)
  | two_sum h₁ h₂ hp₁ hp₂ hM ih₁ ih₂ =>
      refine ⟨ih₁.1.ordinary_two_sum ih₂.1 hp₁ hp₂ hM, ?_⟩
      obtain ⟨n, u, hu⟩ := ih₁.1
      obtain ⟨m, v, hv⟩ := ih₂.1
      exact ExcludesR10.ordinary_two_sum u v
        (by simpa only [← hu] using hp₁) (by simpa only [← hv] using hp₂)
        (by simpa only [← hu, ← hv] using hM)
        (by simpa only [← hu] using ih₁.2) (by simpa only [← hv] using ih₂.2)
  | three_sum h₁ h₂ hp₁ hp₂ hM ih₁ ih₂ =>
      refine ⟨ih₁.1.ordinary_three_sum ih₂.1 hp₁ hp₂ hM, ?_⟩
      obtain ⟨n, u, hu⟩ := ih₁.1
      obtain ⟨m, v, hv⟩ := ih₂.1
      exact ExcludesR10.ordinary_three_sum u v
        (by simpa only [← hu] using hp₁) (by simpa only [← hv] using hp₂)
        (by simpa only [← hu, ← hv] using hM)
        (by simpa only [← hu] using ih₁.2) (by simpa only [← hv] using ih₂.2)

theorem GraphicCographicConstructible.excludesR10 {E : Type u} {M : Matroid E}
    (hM : GraphicCographicConstructible M) : ExcludesR10 M :=
  hM.binary_and_excludesR10.2

/-- The obstruction applies to every actual matroid with an embedded R₁₀ minor. -/
theorem not_graphicCographicConstructible_of_r10_minor {E : Type u} {M : Matroid E}
    (f : Fin 10 ↪ E) (hf : r10Matroid.mapEmbedding f ≤m M) :
    ¬GraphicCographicConstructible M :=
  fun hM ↦ hM.excludesR10 f hf

end Unimodular.R10Maximality
end
end

run_cmd do
  let roots : Array Lean.Name := #[
    ``Unimodular.R10Maximality.r10_minor_of_joined_local,
    ``Unimodular.R10Maximality.r10_minor_ordinary_three_sum,
    ``Unimodular.RepresentationBridge.graph_hasFiniteRepresentation,
    ``Unimodular.R10Maximality.GraphicCographicConstructible.binary_and_excludesR10,
    ``Unimodular.R10Maximality.not_graphicCographicConstructible_of_r10_minor]
  let allowed : Array Lean.Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in roots do
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Unapproved transitive axiom {ax} in {name}"
    Lean.logInfo m!"R10_CLOSURE_CHECKED {name}: {axioms}"

#print axioms Unimodular.R10Maximality.r10_minor_of_joined_local
#print axioms Unimodular.R10Maximality.r10_minor_ordinary_three_sum
#print axioms Unimodular.RepresentationBridge.graph_hasFiniteRepresentation
#print axioms Unimodular.R10Maximality.GraphicCographicConstructible.binary_and_excludesR10
#print axioms Unimodular.R10Maximality.not_graphicCographicConstructible_of_r10_minor
