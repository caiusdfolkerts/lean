module
public import consolidated.rigidity_combined03_part1
import all consolidated.rigidity_combined03_part1
set_option Elab.async false
section BundleSource0038
/- Source: Papers/RigidityLocalStressSum.lean -/





@[expose] public section

/-!
# The actual direct sum of local body stresses

Each local space consists of ordinary graph stresses supported on the
complete graph of one maximal body.  The copied-star theorem proves
both injectivity of their finite sum and its compatibility with every
induced vertex set.  No dimension count substitutes for this support
identity.

These local stress spaces supply the denominator in Proposition 6.2.
-/

noncomputable section
namespace Papers.Rigidity.BodyLoads

open BarJoint SupportedCode
open scoped Classical BigOperators

variable {V : Type} [Fintype V]

abbrev Body (G : SimpleGraph V) := {S : Finset V // IsBody G S}

/-- The actual edges having both endpoints in the displayed vertex set. -/
def vertexEdgeSet (G : SimpleGraph V) (T : Finset V) : Set (Edge G) :=
  {e | ∀ v, v ∈ e.val → v ∈ T}

def localStressSpace (G : SimpleGraph V) (p : Placement V 3) (C : Body G) :
    Submodule ℝ (Edge G → ℝ) :=
  supportedOn (StressSpace G p) (vertexEdgeSet G C.val)

def localStressSum (G : SimpleGraph V) (p : Placement V 3) :
    (∀ C : Body G, localStressSpace G p C) →ₗ[ℝ] (Edge G → ℝ) :=
  ∑ C : Body G, (localStressSpace G p C).subtype.comp (LinearMap.proj C)

@[simp] theorem localStressSum_apply
    (G : SimpleGraph V) (p : Placement V 3)
    (a : ∀ C : Body G, localStressSpace G p C) :
    localStressSum G p a = ∑ C : Body G, (a C).val := by
  simp [localStressSum]

theorem localStressSum_mem
    (G : SimpleGraph V) (p : Placement V 3)
    (a : ∀ C : Body G, localStressSpace G p C) :
    localStressSum G p a ∈ StressSpace G p := by
  rw [localStressSum_apply]
  exact Submodule.sum_mem _ (fun C _ => (a C).property.1)

theorem local_star_nonzero_endpoints
    (G : SimpleGraph V) (p : Placement V 3) (C : Body G)
    (a : localStressSpace G p C) (v w : V)
    (ha : starCoordinates G v a.val w ≠ 0) :
    v ∈ C.val ∧ w ∈ C.val ∧ w ≠ v := by
  by_cases hvw : G.Adj v w
  · rw [starCoordinates_of_adj G v w a.val hvw] at ha
    have he : (⟨s(v,w), hvw⟩ : Edge G) ∈ vertexEdgeSet G C.val := by
      by_contra hne
      exact ha (a.property.2 _ hne)
    exact ⟨he v (Sym2.mem_mk_left v w), he w (Sym2.mem_mk_right v w), hvw.ne.symm⟩
  · exact False.elim (ha (starCoordinates_of_not_adj G v w a.val hvw))

theorem local_star_zero_of_not_mem
    (G : SimpleGraph V) (p : Placement V 3) (C : Body G)
    (a : localStressSpace G p C) (v : V) (hv : v ∉ C.val) (w : V) :
    starCoordinates G v a.val w = 0 := by
  by_contra hn
  exact hv (local_star_nonzero_endpoints G p C a v w hn).1

/-- At an omitted vertex, support of the aggregate makes all actual
copied body-star coefficients vanish separately. -/
theorem omitted_vertex_local_stars_zero
    (M : MinimalCounterexample V) (p : Placement V 3)
    (hp : GeneralPosition.InGeneralPosition p) (T : Finset V)
    (a : ∀ C : Body M.graph, localStressSpace M.graph p C)
    (ha : ∀ e, e ∉ vertexEdgeSet M.graph T → localStressSum M.graph p a e = 0)
    (v : V) (hv : v ∉ T) :
    ∀ C : Body M.graph, ∀ w, starCoordinates M.graph v (a C).val w = 0 := by
  let I := {C : Body M.graph // v ∈ C.val}
  let b : I → V → ℝ := fun i => starCoordinates M.graph v (a i.val).val
  have hfull (w : V) :
      (∑ C : Body M.graph, starCoordinates M.graph v (a C).val w) = 0 := by
    have hmap := congrFun (map_sum (starCoordinates M.graph v)
      (fun C : Body M.graph => (a C).val) Finset.univ) w
    rw [← localStressSum_apply] at hmap
    simp only [Finset.sum_apply] at hmap
    rw [← hmap]
    by_cases h : M.graph.Adj v w
    · rw [starCoordinates_of_adj _ _ _ _ h]
      apply ha
      intro he
      exact hv (he v (Sym2.mem_mk_left v w))
    · exact starCoordinates_of_not_adj _ _ _ _ h
  have hcancel (w : V) : ∑ i : I, b i w = 0 := by
    have hsplit := Fintype.sum_subtype_add_sum_subtype
      (fun C : Body M.graph => v ∈ C.val)
      (fun C => starCoordinates M.graph v (a C).val w)
    have hout : (∑ C : {C : Body M.graph // v ∉ C.val},
        starCoordinates M.graph v (a C.val).val w) = 0 := by
      apply Finset.sum_eq_zero
      intro C _
      exact local_star_zero_of_not_mem M.graph p C.val (a C.val) v C.property w
    rw [hout, add_zero, hfull] at hsplit
    exact hsplit
  have hsupport (i : I) (w : V) (hi : b i w ≠ 0) : w ∈ i.val.val.erase v := by
    have hw := local_star_nonzero_endpoints M.graph p i.val (a i.val) v w hi
    exact Finset.mem_erase.mpr ⟨hw.2.2, hw.2.1⟩
  have hz := copied_star_coefficients_eq_zero M p hp v (fun i : I => i.val.val)
    (Subtype.val_injective.comp Subtype.val_injective)
    (fun i => i.val.property) (fun i => i.property) b hsupport hcancel
    (fun i => stress_starCoordinates_balance M.graph p (a i.val).val
      (a i.val).property.1 v)
  intro C w
  by_cases hC : v ∈ C.val
  · exact hz ⟨C, hC⟩ w
  · exact local_star_zero_of_not_mem M.graph p C (a C) v hC w

/-- The literal induced-prefix support equality for the finite sum of
local stresses.  This is the support assertion in Proposition 6.2. -/
theorem localStressSum_supported_iff
    (M : MinimalCounterexample V) (p : Placement V 3)
    (hp : GeneralPosition.InGeneralPosition p) (T : Finset V)
    (a : ∀ C : Body M.graph, localStressSpace M.graph p C) :
    (∀ e, e ∉ vertexEdgeSet M.graph T → localStressSum M.graph p a e = 0) ↔
      ∀ C e, e ∉ vertexEdgeSet M.graph T → (a C).val e = 0 := by
  constructor
  · intro ha C e he
    change ¬∀ v, v ∈ e.val → v ∈ T at he
    push_neg at he
    obtain ⟨v, hve, hv⟩ := he
    have hz := omitted_vertex_local_stars_zero M p hp T a ha v hv C
      (incidentOther M.graph v ⟨e, hve⟩)
    simpa only [starCoordinates_incidentOther] using hz
  · intro ha e he
    rw [localStressSum_apply, Finset.sum_apply]
    exact Finset.sum_eq_zero (fun C _ => ha C e he)

/-- Ordinary stresses on the distinct maximal bodies have a genuine
direct sum inside the ambient graph stress space. -/
theorem localStressSum_injective
    (M : MinimalCounterexample V) (p : Placement V 3)
    (hp : GeneralPosition.InGeneralPosition p) :
    Function.Injective (localStressSum M.graph p) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm
  · intro a ha
    have hz : localStressSum M.graph p a = 0 := LinearMap.mem_ker.mp ha
    have hlocal := (localStressSum_supported_iff M p hp ∅ a).mp
      (fun e _ => congrFun hz e)
    change a = 0
    funext C
    apply Subtype.ext
    funext e
    apply hlocal C e
    intro he
    exact Finset.notMem_empty e.val.out.1
      (he e.val.out.1 (Sym2.out_fst_mem e.val))
  · exact bot_le

end Papers.Rigidity.BodyLoads

end
end
end BundleSource0038

section BundleSource0039
/- Source: Papers/RigidityCompleteFragmentMotions.lean -/




@[expose] public section

/-!
# Complete fragments of every cardinality

The body-load exact sequences use fragments with zero, one, or two
vertices.  This file proves that their actual complete-graph motion
kernels still consist of restrictions of Euclidean twists.  In the
two-point case the angular velocity is constructed by the ordinary
vector triple-product identity; no six-dimensional-motion assumption
is made at small cardinalities.

The construction includes complete fragments of every finite size.
-/

noncomputable section
namespace Papers.Rigidity

open BarJoint Matrix
open scoped Classical Matrix BigOperators

variable {V : Type} [Fintype V]

theorem exists_twist_fitting_two_points
    (p q u v : Vec3) (hpq : p ≠ q)
    (hbar : (q - p) ⬝ᵥ (v - u) = 0) :
    ∃ X : Twist, evaluateTwist p X = u ∧ evaluateTwist q X = v := by
  let d := q - p
  let e := v - u
  have hd : d ≠ 0 := sub_ne_zero.mpr (Ne.symm hpq)
  have hdd : d ⬝ᵥ d ≠ 0 := by
    intro hz
    exact hd (dotProduct_self_eq_zero.mp hz)
  have hed : e ⬝ᵥ d = 0 := by
    rw [dotProduct_comm]
    exact hbar
  let ω := (d ⬝ᵥ d)⁻¹ • (d ⨯₃ e)
  have hω : ω ⨯₃ d = e := by
    dsimp only [ω]
    rw [map_smul, LinearMap.smul_apply, cross_cross_eq_smul_sub_smul,
      hed, zero_smul, sub_zero, smul_smul, inv_mul_cancel₀ hdd, one_smul]
  refine ⟨(ω, u - ω ⨯₃ p), ?_, ?_⟩
  · simp only [evaluateTwist_apply, sub_add_cancel]
  · rw [evaluateTwist_apply]
    have hcross : ω ⨯₃ q - ω ⨯₃ p = e := by
      rw [← map_sub]
      exact hω
    ext i
    have hi := congrFun hcross i
    change u i - (ω ⨯₃ p) i + (ω ⨯₃ q) i = v i
    change (ω ⨯₃ q) i - (ω ⨯₃ p) i = v i - u i at hi
    linarith

theorem GeneralPosition.InGeneralPosition.injective
    (p : Placement V 3) (hp : GeneralPosition.InGeneralPosition p) :
    Function.Injective p := by
  intro v w hpvw
  by_contra hvw
  let f : Fin 2 ↪ V := ⟨![v, w], Matrix.injective_pair_iff_ne.mpr hvw⟩
  have hlin := hp (1 : Fin 4) f
  have hn := hlin.ne_zero (0 : Fin 1)
  apply hn
  change p w - p v = 0
  rw [hpvw, sub_self]

/-- Every infinitesimal motion of a complete fragment is an actual
Euclidean twist restriction, including the empty and tiny fragments. -/
theorem exists_twist_of_completeMotion_all
    (p u : Placement V 3) (hp : GeneralPosition.InGeneralPosition p)
    (hu : IsInfinitesimalMotion (SimpleGraph.completeGraph V) p u) :
    ∃ X : Twist, ∀ v, u v = evaluateTwist (p v) X := by
  by_cases hlarge : 3 ≤ Fintype.card V
  · obtain ⟨f : Fin 3 ↪ V⟩ := Function.Embedding.nonempty_of_card_le
      (α := Fin 3) (β := V) (by simpa using hlarge)
    exact exists_twist_of_completeMotion p u hp f hu
  · have hsmall : Fintype.card V ≤ 2 := by omega
    by_cases htwo : Fintype.card V = 2
    · have hc : (Finset.univ : Finset V).card = 2 := by simpa using htwo
      obtain ⟨v, w, hvw, hVW⟩ := Finset.card_eq_two.mp hc
      have hpvw : p v ≠ p w := (GeneralPosition.InGeneralPosition.injective p hp).ne hvw
      have hbar : (p w - p v) ⬝ᵥ (u w - u v) = 0 :=
        (isInfinitesimalMotion_iff (SimpleGraph.completeGraph V) p u).mp hu
          w v (Ne.symm hvw)
      obtain ⟨X, hXv, hXw⟩ := exists_twist_fitting_two_points (p v) (p w) (u v) (u w)
        hpvw hbar
      refine ⟨X, ?_⟩
      intro x
      have hx : x = v ∨ x = w := by
        simpa only [hVW, Finset.mem_insert, Finset.mem_singleton] using
          (Finset.mem_univ x : x ∈ (Finset.univ : Finset V))
      rcases hx with rfl | rfl
      · exact hXv.symm
      · exact hXw.symm
    · by_cases hone : Fintype.card V = 1
      · have hc : (Finset.univ : Finset V).card = 1 := by simpa using hone
        obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hc
        refine ⟨(0, u v), ?_⟩
        intro w
        have hw : w = v := by simpa only [hv, Finset.mem_singleton] using Finset.mem_univ w
        subst w
        simp [evaluateTwist_apply]
      · have hz : Fintype.card V = 0 := by omega
        letI : IsEmpty V := Fintype.card_eq_zero_iff.mp hz
        exact ⟨0, fun v => isEmptyElim v⟩

theorem complete_kernel_eq_twist_range_all
    (p : Placement V 3) (hp : GeneralPosition.InGeneralPosition p) :
    (rigidityOperator (SimpleGraph.completeGraph V) p).ker =
      (globalTwistOperator p).range := by
  apply le_antisymm
  · intro u hu
    obtain ⟨X, hX⟩ := exists_twist_of_completeMotion_all p u hp hu
    exact ⟨X, funext fun v => (hX v).symm⟩
  · rintro u ⟨X, rfl⟩
    exact globalTwist_isMotion (SimpleGraph.completeGraph V) p X

end Papers.Rigidity

end
end
end BundleSource0039

section BundleSource0040
/- Source: Papers/RigidityFragmentLoads.lean -/






@[expose] public section

/-!
# Literal balanced loads and complete-fragment resolution

Loads are ordinary vectors on the actual vertices.  Their force and
moment equations are proved equivalent to annihilating Euclidean twist
restrictions.  Duality then resolves every balanced load by bar
coefficients on the complete fragment, at every fragment size.

The definition of balanced loads does not encode representability as
an assumption.
-/

noncomputable section
namespace Papers.Rigidity.BodyLoads

open BarJoint Matrix
open scoped Classical BigOperators Matrix

variable {V : Type} [Fintype V]

/-- The ordinary Euclidean virtual-work pairing, with no quotient or
equilibrium condition imposed on either argument. -/
def loadWorkEquiv : Velocity V 3 ≃ₗ[ℝ] Module.Dual ℝ (Velocity V 3) :=
  let e := (LinearEquiv.curry ℝ ℝ V (Fin 3)).symm
  (e.trans (dotProductEquiv ℝ (V × Fin 3))).trans e.dualMap

@[simp] theorem loadWorkEquiv_apply (F u : Velocity V 3) :
    loadWorkEquiv F u = ∑ v, F v ⬝ᵥ u v := by
  change (∑ x : V × Fin 3, F x.1 x.2 * u x.1 x.2) = ∑ v, F v ⬝ᵥ u v
  rw [Fintype.sum_prod_type]
  rfl

theorem loadWorkEquiv_comm (F u : Velocity V 3) :
    loadWorkEquiv F u = loadWorkEquiv u F := by
  rw [loadWorkEquiv_apply, loadWorkEquiv_apply]
  exact Finset.sum_congr rfl (fun v _ => dotProduct_comm _ _)

theorem stressOperator_single
    (G : SimpleGraph V) (p u : Placement V 3) (e : Edge G) :
    stressOperator G p (Pi.single e 1) u = unorderedFunctional p e.val u := by
  change (Pi.single e (1 : ℝ) : Edge G → ℝ) ⬝ᵥ
    (fun f : Edge G => unorderedFunctional p f.val u) = _
  exact single_one_dotProduct e _

/-- Actual forces exerted by an unordered-edge coefficient vector. -/
def forceOperator (G : SimpleGraph V) (p : Placement V 3) :
    (Edge G → ℝ) →ₗ[ℝ] Velocity V 3 :=
  loadWorkEquiv.symm.toLinearMap.comp (stressOperator G p)

@[simp] theorem loadWork_forceOperator
    (G : SimpleGraph V) (p : Placement V 3) (a : Edge G → ℝ) :
    loadWorkEquiv (forceOperator G p a) = stressOperator G p a := by
  exact loadWorkEquiv.apply_symm_apply _

theorem forceOperator_eq_zero_iff
    (G : SimpleGraph V) (p : Placement V 3) (a : Edge G → ℝ) :
    forceOperator G p a = 0 ↔ a ∈ StressSpace G p := by
  rw [StressSpace, LinearMap.mem_ker]
  constructor
  · intro ha
    rw [← loadWork_forceOperator, ha, map_zero]
  · intro ha
    apply loadWorkEquiv.injective
    rw [loadWork_forceOperator, ha, map_zero]

theorem forceOperator_vertex
    (G : SimpleGraph V) (p : Placement V 3) (a : Edge G → ℝ) (v : V) :
    forceOperator G p a v =
      ∑ e : IncidentEdge G v, a e.val • (p v - p (incidentOther G v e)) := by
  have hwork (z : Vec3) :
      forceOperator G p a v ⬝ᵥ z =
        (∑ e : IncidentEdge G v, a e.val • (p v - p (incidentOther G v e))) ⬝ᵥ z := by
    have h := congrArg (fun f : Module.Dual ℝ (Velocity V 3) => f (Pi.single v z))
      (loadWork_forceOperator G p a)
    simp only [loadWorkEquiv_apply] at h
    have hleft : (∑ w, forceOperator G p a w ⬝ᵥ (Pi.single v z : Velocity V 3) w) =
        forceOperator G p a v ⬝ᵥ z := by
      rw [Finset.sum_eq_single v]
      · simp
      · intro w _ hw
        simp [Pi.single_apply, hw, Ne.symm hw]
      · simp
    rw [hleft] at h
    have hsplit := Fintype.sum_subtype_add_sum_subtype
      (fun e : Edge G => v ∈ e.val)
      (fun e : Edge G => a e * unorderedFunctional p e.val (Pi.single v z))
    have hout : (∑ e : {e : Edge G // v ∉ e.val},
        a e.val * unorderedFunctional p e.val.val (Pi.single v z)) = 0 := by
      apply Finset.sum_eq_zero
      intro e _
      rw [unorderedFunctional_impulse_of_not_incident G p v z e.val e.property, mul_zero]
    rw [hout, add_zero] at hsplit
    have hstress : stressOperator G p a (Pi.single v z) =
        ∑ e : Edge G, a e * unorderedFunctional p e.val (Pi.single v z) := by
      simp only [stressOperator_apply, unorderedFunctional_out]
    rw [hstress, ← hsplit] at h
    rw [h, sum_dotProduct]
    apply Finset.sum_congr rfl
    intro e _
    simp only [smul_dotProduct, smul_eq_mul,
      unorderedFunctional_impulse_of_incident G p v z]
  ext i
  simpa using hwork (Pi.single i 1)

theorem work_on_globalTwist (p F : Placement V 3) (X : Twist) :
    loadWorkEquiv F (globalTwistOperator p X) =
      (∑ v, F v) ⬝ᵥ X.2 + (∑ v, p v ⨯₃ F v) ⬝ᵥ X.1 := by
  rw [loadWorkEquiv_apply]
  simp only [globalTwistOperator_apply, evaluateTwist_apply, dotProduct_add,
    Finset.sum_add_distrib]
  rw [← sum_dotProduct]
  congr 1
  calc
    (∑ v, F v ⬝ᵥ X.1 ⨯₃ p v) = ∑ v, X.1 ⬝ᵥ p v ⨯₃ F v := by
      apply Finset.sum_congr rfl
      intro v _
      exact triple_product_permutation _ _ _
    _ = X.1 ⬝ᵥ (∑ v, p v ⨯₃ F v) := (dotProduct_sum _ _ _).symm
    _ = (∑ v, p v ⨯₃ F v) ⬝ᵥ X.1 := dotProduct_comm _ _

/-- A load is balanced precisely when its total force and total moment
are zero.  The annihilator presentation only supplies its linear space. -/
def balancedLoads (p : Placement V 3) : Submodule ℝ (Velocity V 3) :=
  (globalTwistOperator p).range.dualAnnihilator.comap loadWorkEquiv.toLinearMap

theorem mem_balancedLoads_iff (p F : Placement V 3) :
    F ∈ balancedLoads p ↔ (∑ v, F v = 0) ∧ (∑ v, p v ⨯₃ F v = 0) := by
  have hmem : F ∈ balancedLoads p ↔
      ∀ X : Twist, loadWorkEquiv F (globalTwistOperator p X) = 0 := by
    simp only [balancedLoads, Submodule.mem_comap, Submodule.mem_dualAnnihilator,
      LinearMap.mem_range, forall_exists_index]
    constructor
    · intro h X
      exact h _ X rfl
    · intro h u X hX
      subst u
      exact h X
  rw [hmem]
  constructor
  · intro h
    constructor
    · ext i
      have hi := h (0, Pi.single i 1)
      simpa only [work_on_globalTwist, dotProduct_zero, add_zero, dotProduct_single,
        mul_one, Pi.zero_apply] using hi
    · ext i
      have hi := h (Pi.single i 1, 0)
      simpa only [work_on_globalTwist, dotProduct_zero, zero_add, dotProduct_single,
        mul_one, Pi.zero_apply] using hi
  · rintro ⟨hF, hM⟩ X
    rw [work_on_globalTwist, hF, hM, zero_dotProduct, zero_dotProduct, add_zero]

theorem stressOperator_range_eq_annihilator (G : SimpleGraph V) (p : Placement V 3) :
    (stressOperator G p).range =
      (undirectedRigidityOperator G p).ker.dualAnnihilator := by
  rw [stressOperator, LinearMap.range_comp_of_range_eq_top _
    (dotProductEquiv ℝ (Edge G)).range,
    LinearMap.range_dualMap_eq_dualAnnihilator_ker]

/-- Every literal balanced load is resolved by ordinary bar coefficients
on the complete fragment.  Empty, singleton and two-point fragments are
included by the preceding complete-kernel theorem. -/
theorem balanced_iff_complete_bar_load
    (p : Placement V 3) (hp : GeneralPosition.InGeneralPosition p)
    (F : Placement V 3) :
    F ∈ balancedLoads p ↔
      ∃ a : Edge (SimpleGraph.completeGraph V) → ℝ,
        forceOperator (SimpleGraph.completeGraph V) p a = F := by
  change loadWorkEquiv F ∈ (globalTwistOperator p).range.dualAnnihilator ↔ _
  rw [← complete_kernel_eq_twist_range_all p hp,
    ← ker_undirectedRigidityOperator,
    ← stressOperator_range_eq_annihilator]
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a, loadWorkEquiv.injective ?_⟩
    rw [loadWork_forceOperator, ha]
  · rintro ⟨a, rfl⟩
    exact ⟨a, (loadWork_forceOperator _ _ _).symm⟩

/-- A complete graph on the displayed subset, with the other ambient
vertices isolated.  This keeps all prefix spaces in common coordinates. -/
def cliqueOn (S : Finset V) : SimpleGraph V where
  Adj v w := v ≠ w ∧ v ∈ S ∧ w ∈ S
  symm := by
    constructor
    rintro v w ⟨hvw, hv, hw⟩
    exact ⟨Ne.symm hvw, hw, hv⟩
  loopless := by constructor; intro v; simp

theorem cliqueOn_le {G : SimpleGraph V} (S : Finset V)
    (hS : G.IsClique (S : Set V)) : cliqueOn S ≤ G := by
  intro v w h
  exact hS h.2.1 h.2.2 h.1

def balancedLoadsOn (p : Placement V 3) (S : Finset V) :
    Submodule ℝ (Velocity V 3) where
  carrier := {F | F ∈ balancedLoads p ∧ ∀ v, v ∉ S → F v = 0}
  zero_mem' := ⟨(balancedLoads p).zero_mem, by simp⟩
  add_mem' := by
    rintro F H ⟨hF, hFS⟩ ⟨hH, hHS⟩
    exact ⟨(balancedLoads p).add_mem hF hH, fun v hv => by simp [hFS v hv, hHS v hv]⟩
  smul_mem' := by
    rintro c F ⟨hF, hFS⟩
    exact ⟨(balancedLoads p).smul_mem c hF, fun v hv => by simp [hFS v hv]⟩

theorem balanced_load_annihilates_twist
    (p F : Placement V 3) (hF : F ∈ balancedLoads p) (X : Twist) :
    loadWorkEquiv F (globalTwistOperator p X) = 0 := by
  change loadWorkEquiv F ∈ (globalTwistOperator p).range.dualAnnihilator at hF
  exact (Submodule.mem_dualAnnihilator (loadWorkEquiv F)).mp hF _ ⟨X, rfl⟩

theorem forceOperator_balanced
    (G : SimpleGraph V) (p : Placement V 3) (a : Edge G → ℝ) :
    forceOperator G p a ∈ balancedLoads p := by
  have htwist : (globalTwistOperator p).range ≤ (undirectedRigidityOperator G p).ker := by
    rw [ker_undirectedRigidityOperator]
    rintro u ⟨X, rfl⟩
    exact globalTwist_isMotion G p X
  have hstress : stressOperator G p a ∈
      (undirectedRigidityOperator G p).ker.dualAnnihilator := by
    rw [← stressOperator_range_eq_annihilator]
    exact ⟨a, rfl⟩
  change loadWorkEquiv (forceOperator G p a) ∈
    (globalTwistOperator p).range.dualAnnihilator
  rw [loadWork_forceOperator]
  exact Submodule.dualAnnihilator_anti htwist hstress

theorem clique_force_zero_outside
    (p : Placement V 3) (S : Finset V) (a : Edge (cliqueOn S) → ℝ)
    (v : V) (hv : v ∉ S) : forceOperator (cliqueOn S) p a v = 0 := by
  letI : IsEmpty (IncidentEdge (cliqueOn S) v) :=
    ⟨fun e => hv (incidentOther_adj (cliqueOn S) v e).2.1⟩
  rw [forceOperator_vertex]
  simp

/-- Complete-fragment surjectivity in fixed ambient coordinates.  The
right side is the actual force/moment space with literal support in S. -/
theorem range_clique_forceOperator
    (p : Placement V 3) (hp : GeneralPosition.InGeneralPosition p) (S : Finset V) :
    (forceOperator (cliqueOn S) p).range = balancedLoadsOn p S := by
  apply le_antisymm
  · rintro F ⟨a, rfl⟩
    exact ⟨forceOperator_balanced _ p a, clique_force_zero_outside p S a⟩
  · intro F hF
    have hwork : loadWorkEquiv F ∈ (undirectedRigidityOperator (cliqueOn S) p).ker.dualAnnihilator := by
      rw [Submodule.mem_dualAnnihilator]
      intro u hu
      rw [ker_undirectedRigidityOperator] at hu
      let e : S ↪ V := Function.Embedding.subtype _
      have hpS := GeneralPosition.InGeneralPosition.comp_embedding p hp e
      have huS : IsInfinitesimalMotion (SimpleGraph.completeGraph S) (p ∘ e) (u ∘ e) := by
        rw [isInfinitesimalMotion_iff]
        intro v w hvw
        exact (isInfinitesimalMotion_iff (cliqueOn S) p u).mp hu v.val w.val
          ⟨fun h => hvw (Subtype.ext h), v.property, w.property⟩
      obtain ⟨X, hX⟩ := exists_twist_of_completeMotion_all (p ∘ e) (u ∘ e) hpS huS
      have heq : loadWorkEquiv F u = loadWorkEquiv F (globalTwistOperator p X) := by
        rw [loadWorkEquiv_apply, loadWorkEquiv_apply]
        apply Finset.sum_congr rfl
        intro v _
        by_cases hv : v ∈ S
        · rw [show u v = evaluateTwist (p v) X from hX ⟨v, hv⟩]
          rfl
        · rw [hF.2 v hv, zero_dotProduct, zero_dotProduct]
      rw [heq]
      exact balanced_load_annihilates_twist p F hF.1 X
    rw [← stressOperator_range_eq_annihilator] at hwork
    obtain ⟨a, ha⟩ := hwork
    refine ⟨a, loadWorkEquiv.injective ?_⟩
    rw [loadWork_forceOperator, ha]

theorem forceOperator_rank (G : SimpleGraph V) (p : Placement V 3) :
    Module.finrank ℝ (forceOperator G p).range = rigidityRank G p := by
  have hker : (forceOperator G p).ker = StressSpace G p := by
    ext a
    exact forceOperator_eq_zero_iff G p a
  have hF := (forceOperator G p).finrank_range_add_finrank_ker
  have hS := (stressOperator G p).finrank_range_add_finrank_ker
  rw [hker] at hF
  rw [stressOperator_rank] at hS
  change rigidityRank G p + Module.finrank ℝ (StressSpace G p) = _ at hS
  omega

theorem balancedLoadsOn_finrank
    (p : Placement V 3) (hp : GeneralPosition.InGeneralPosition p) (S : Finset V) :
    Module.finrank ℝ (balancedLoadsOn p S) = rigidityRank (cliqueOn S) p := by
  rw [← range_clique_forceOperator p hp S, forceOperator_rank]

end Papers.Rigidity.BodyLoads

end
end
end BundleSource0040

section BundleSource0041
/- Source: Papers/RigidityBodyLoadRank.lean -/





@[expose] public section

/-!
# Actual compatible body loads and the full prefix rank formula

Each member of the body-load family is an ordinary balanced vector load
supported on its complete fragment.  Compatibility is cancellation at
each actual vertex.  The dual test map has exactly the induced graph's
ordinary motion kernel.  Rank-nullity therefore yields Proposition 6.2's
rank identity for every induced vertex set, including empty and tiny
fragments.  The family is not defined in terms of the desired rank.

The rank calculation uses the actual force-balance maps of Proposition 6.2.
-/

noncomputable section
namespace Papers.Rigidity.BodyLoads

open BarJoint Matrix
open scoped Classical BigOperators

variable {V : Type} [Fintype V]

def maskedGraph (G : SimpleGraph V) (T : Finset V) : SimpleGraph V where
  Adj v w := G.Adj v w ∧ v ∈ T ∧ w ∈ T
  symm := by constructor; rintro v w ⟨h, hv, hw⟩; exact ⟨h.symm, hw, hv⟩
  loopless := by constructor; intro v; rintro ⟨h, _⟩; exact G.loopless.irrefl v h

theorem maskedGraph_eq_liftInduce (G : SimpleGraph V) (T : Finset V) :
    maskedGraph G T = liftGraph T (G.induce (T : Set V)) := by
  ext v w
  simp only [maskedGraph, liftGraph, SimpleGraph.induce_adj]
  constructor
  · rintro ⟨h, hv, hw⟩
    exact ⟨hv, hw, h⟩
  · rintro ⟨hv, hw, h⟩
    exact ⟨h, hv, hw⟩

theorem cliqueOn_eq_liftComplete (T : Finset V) :
    cliqueOn T = liftGraph T (SimpleGraph.completeGraph T) := by
  ext v w
  constructor
  · rintro ⟨hne, hv, hw⟩
    exact ⟨hv, hw, fun h => hne (congrArg Subtype.val h)⟩
  · rintro ⟨hv, hw, hne⟩
    exact ⟨fun h => hne (Subtype.ext h), hv, hw⟩

abbrev BodyBalancedFamily (G : SimpleGraph V) (p : Placement V 3) (T : Finset V) :=
  ∀ C : Body G, balancedLoadsOn p (C.val ∩ T)

/-- Add all load copies at their actual vertex coordinates. -/
def totalBodyLoad (G : SimpleGraph V) (p : Placement V 3) (T : Finset V) :
    BodyBalancedFamily G p T →ₗ[ℝ] Velocity V 3 :=
  ∑ C : Body G, (balancedLoadsOn p (C.val ∩ T)).subtype.comp (LinearMap.proj C)

@[simp] theorem totalBodyLoad_apply
    (G : SimpleGraph V) (p : Placement V 3) (T : Finset V)
    (F : BodyBalancedFamily G p T) :
    totalBodyLoad G p T F = ∑ C : Body G, (F C).val := by
  simp [totalBodyLoad]

@[simp] theorem totalBodyLoad_single
    (G : SimpleGraph V) (p : Placement V 3) (T : Finset V)
    (C : Body G) (F : balancedLoadsOn p (C.val ∩ T)) :
    totalBodyLoad G p T (Pi.single C F) = F.val := by
  rw [totalBodyLoad_apply, Finset.sum_eq_single C]
  · simp
  · intro D _ hDC
    simp [Pi.single_eq_of_ne hDC]
  · simp

/-- The literal compatible load space of Section 6 at the prefix T. -/
def compatibleBodyLoads (G : SimpleGraph V) (p : Placement V 3) (T : Finset V) :
    Submodule ℝ (BodyBalancedFamily G p T) :=
  (totalBodyLoad G p T).ker

theorem mem_compatibleBodyLoads_iff
    (G : SimpleGraph V) (p : Placement V 3) (T : Finset V)
    (F : BodyBalancedFamily G p T) :
    F ∈ compatibleBodyLoads G p T ↔ ∀ v, ∑ C : Body G, (F C).val v = 0 := by
  simp only [compatibleBodyLoads, LinearMap.mem_ker, totalBodyLoad_apply,
    funext_iff, Finset.sum_apply, Pi.zero_apply]

/-- The constraints tested against actual balanced body loads. -/
def bodyLoadTest (G : SimpleGraph V) (p : Placement V 3) (T : Finset V) :
    Velocity V 3 →ₗ[ℝ] Module.Dual ℝ (BodyBalancedFamily G p T) :=
  (totalBodyLoad G p T).dualMap.comp loadWorkEquiv.toLinearMap

theorem fragment_le_masked (G : SimpleGraph V) (T : Finset V) (C : Body G) :
    cliqueOn (C.val ∩ T) ≤ maskedGraph G T := by
  intro v w h
  exact ⟨C.property.2.1 (Finset.mem_inter.mp h.2.1).1
    (Finset.mem_inter.mp h.2.2).1 h.1,
    (Finset.mem_inter.mp h.2.1).2, (Finset.mem_inter.mp h.2.2).2⟩

/-- This is the ordinary graph-motion kernel, proved by testing actual
single-bar loads in bodies containing the edge. -/
theorem ker_bodyLoadTest
    (G : SimpleGraph V) (hG : K4Covered G) (p : Placement V 3)
    (hp : GeneralPosition.InGeneralPosition p) (T : Finset V) :
    (bodyLoadTest G p T).ker = (rigidityOperator (maskedGraph G T) p).ker := by
  ext u
  constructor
  · intro hu
    rw [← IsInfinitesimalMotion, isInfinitesimalMotion_iff]
    intro v w h
    obtain ⟨S, hS, hv, hw⟩ := hG.edge_in_body h.1
    let C : Body G := ⟨S, hS⟩
    have hadj : (cliqueOn (C.val ∩ T)).Adj v w :=
      ⟨h.1.ne, Finset.mem_inter.mpr ⟨hv, h.2.1⟩,
        Finset.mem_inter.mpr ⟨hw, h.2.2⟩⟩
    let e : Edge (cliqueOn (C.val ∩ T)) := ⟨s(v,w), hadj⟩
    let a : Edge (cliqueOn (C.val ∩ T)) → ℝ := Pi.single e 1
    have hF : forceOperator (cliqueOn (C.val ∩ T)) p a ∈
        balancedLoadsOn p (C.val ∩ T) := by
      rw [← range_clique_forceOperator p hp (C.val ∩ T)]
      exact ⟨a, rfl⟩
    let F : balancedLoadsOn p (C.val ∩ T) := ⟨_, hF⟩
    have hz := congrArg (fun f : Module.Dual ℝ (BodyBalancedFamily G p T) =>
      f (Pi.single C F)) (LinearMap.mem_ker.mp hu)
    change loadWorkEquiv u (totalBodyLoad G p T (Pi.single C F)) = 0 at hz
    rw [totalBodyLoad_single, loadWorkEquiv_comm] at hz
    change loadWorkEquiv (forceOperator (cliqueOn (C.val ∩ T)) p a) u = 0 at hz
    rw [loadWork_forceOperator, stressOperator_single] at hz
    exact hz
  · intro hu
    rw [LinearMap.mem_ker]
    apply LinearMap.ext
    intro F
    change loadWorkEquiv u (totalBodyLoad G p T F) = 0
    rw [totalBodyLoad_apply, map_sum]
    apply Finset.sum_eq_zero
    intro C _
    rw [loadWorkEquiv_comm]
    have huC : u ∈ (undirectedRigidityOperator (cliqueOn (C.val ∩ T)) p).ker := by
      rw [ker_undirectedRigidityOperator]
      rw [← IsInfinitesimalMotion, isInfinitesimalMotion_iff]
      intro v w h
      exact (isInfinitesimalMotion_iff (maskedGraph G T) p u).mp hu v w
        (fragment_le_masked G T C h)
    obtain ⟨a, ha⟩ : (F C).val ∈ (forceOperator (cliqueOn (C.val ∩ T)) p).range :=
      (range_clique_forceOperator p hp (C.val ∩ T)).ge (F C).property
    rw [← ha, loadWork_forceOperator]
    have hstress : stressOperator (cliqueOn (C.val ∩ T)) p a ∈
        (undirectedRigidityOperator (cliqueOn (C.val ∩ T)) p).ker.dualAnnihilator := by
      rw [← stressOperator_range_eq_annihilator]
      exact ⟨a, rfl⟩
    exact (Submodule.mem_dualAnnihilator
      (stressOperator (cliqueOn (C.val ∩ T)) p a)).mp hstress u huC

theorem totalBodyLoad_rank
    (G : SimpleGraph V) (hG : K4Covered G) (p : Placement V 3)
    (hp : GeneralPosition.InGeneralPosition p) (T : Finset V) :
    Module.finrank ℝ (totalBodyLoad G p T).range = rigidityRank (maskedGraph G T) p := by
  have htest : Module.finrank ℝ (bodyLoadTest G p T).range =
      Module.finrank ℝ (totalBodyLoad G p T).range := by
    rw [bodyLoadTest, LinearMap.range_comp_of_range_eq_top _ loadWorkEquiv.range,
      LinearMap.finrank_range_dualMap_eq_finrank_range]
  have h₁ := (bodyLoadTest G p T).finrank_range_add_finrank_ker
  have h₂ := (rigidityOperator (maskedGraph G T) p).finrank_range_add_finrank_ker
  rw [htest, ker_bodyLoadTest G hG p hp T] at h₁
  unfold rigidityRank
  omega

/-- Proposition 6.2's rank formula, as an exact addition identity. -/
theorem body_load_rank_identity
    (G : SimpleGraph V) (hG : K4Covered G) (p : Placement V 3)
    (hp : GeneralPosition.InGeneralPosition p) (T : Finset V) :
    rigidityRank (maskedGraph G T) p +
        Module.finrank ℝ (compatibleBodyLoads G p T) =
      ∑ C : Body G, rigidityRank (cliqueOn (C.val ∩ T)) p := by
  have h := (totalBodyLoad G p T).finrank_range_add_finrank_ker
  rw [totalBodyLoad_rank G hG p hp T] at h
  change rigidityRank (maskedGraph G T) p +
    Module.finrank ℝ (compatibleBodyLoads G p T) =
    Module.finrank ℝ (BodyBalancedFamily G p T) at h
  rw [Module.finrank_pi_fintype] at h
  simpa only [balancedLoadsOn_finrank p hp] using h

/-- The same identity on the literal induced subtype graph and complete
fragment graphs, with their actual generic ranks. -/
theorem generic_body_load_rank_identity
    (G : SimpleGraph V) (hG : K4Covered G) (p : Placement V 3)
    (hgen : IsGenericPlacement p) (hp : GeneralPosition.InGeneralPosition p) (T : Finset V) :
    genericRigidityRank (G.induce (T : Set V)) 3 +
        Module.finrank ℝ (compatibleBodyLoads G p T) =
      ∑ C : Body G, genericRigidityRank (SimpleGraph.completeGraph ↥(C.val ∩ T)) 3 := by
  have h := body_load_rank_identity G hG p hp T
  change ∀ H : SimpleGraph V, rigidityRank H p = genericRigidityRank H 3 at hgen
  simp only [hgen] at h
  rw [maskedGraph_eq_liftInduce, genericRigidityRank_liftGraph] at h
  simpa only [cliqueOn_eq_liftComplete, genericRigidityRank_liftGraph] using h

end Papers.Rigidity.BodyLoads

end
end
end BundleSource0041

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombined03/block_0041/Consolidated/RigidityCombined03.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombined03/checkpoint_0041.json"

section BundleSource0042
/- Source: Papers/RigidityUniformOrders.lean -/










@[expose] public section

/-!
# Restricting an actual uniform vertex order

An outcome records the position of every label.  Restriction sorts the
positions of a specified embedded set of labels.  Its uniform law is
proved by extending permutations of these labels to the whole vertex
set and double-counting a finite sum.  Thus later star estimates need
no independent assumption about the relative order of a neighborhood.
-/

namespace Papers.Rigidity.UniformOrders

noncomputable section

open scoped Classical BigOperators

variable {V I : Type*} [Fintype V] [Fintype I]

/-- The position of every label in a total ordering. -/
abbrev Outcome (V : Type*) [Fintype V] := V ≃ Fin (Fintype.card V)

instance outcome_nonempty (V : Type*) [Fintype V] : Nonempty (Outcome V) :=
  ⟨Fintype.equivFin V⟩

/-- Sort exactly the positions occupied by the selected labels. -/
def restrict (e : I ↪ V) (σ : Outcome V) : Outcome I := by
  letI : LinearOrder I := LinearOrder.lift' (fun i => σ (e i))
    (σ.injective.comp e.injective)
  exact (Fintype.orderIsoFinOfCardEq I rfl).symm.toEquiv

theorem restrict_lt_iff (e : I ↪ V) (σ : Outcome V) (i j : I) :
    restrict e σ i < restrict e σ j ↔ σ (e i) < σ (e j) := by
  letI : LinearOrder I := LinearOrder.lift' (fun i => σ (e i))
    (σ.injective.comp e.injective)
  exact (Fintype.orderIsoFinOfCardEq I rfl).symm.lt_iff_lt

theorem outcome_eq_of_lt_iff (σ τ : Outcome I)
    (h : ∀ i j, σ i < σ j ↔ τ i < τ j) : σ = τ := by
  have hm : StrictMono (fun k => τ (σ.symm k)) := by
    intro a b hab
    exact (h (σ.symm a) (σ.symm b)).mp (by simpa using hab)
  apply Equiv.ext
  intro i
  have hi := congrFun hm.eq_id (σ i)
  simpa using hi.symm

/-- Relabeling only the selected vertices permutes their induced order
by precisely the same relabeling. -/
theorem restrict_relabel (e : I ↪ V) (σ : Outcome V) (τ : Equiv.Perm I) :
    restrict e ((τ.viaEmbedding e).trans σ) = τ.trans (restrict e σ) := by
  apply outcome_eq_of_lt_iff
  intro i j
  simp only [restrict_lt_iff, Equiv.trans_apply,
    Equiv.Perm.viaEmbedding_apply]

def relabelEquiv (e : I ↪ V) (τ : Equiv.Perm I) : Outcome V ≃ Outcome V where
  toFun σ := (τ.viaEmbedding e).trans σ
  invFun σ := (τ.viaEmbedding e).symm.trans σ
  left_inv σ := by ext i; simp
  right_inv σ := by ext i; simp

def permOutcomeEquiv (ρ : Outcome I) : Equiv.Perm I ≃ Outcome I where
  toFun τ := τ.trans ρ
  invFun ω := ω.trans ρ.symm
  left_inv τ := by ext i; simp
  right_inv ω := by ext i; simp

def mean (f : Outcome V → ℝ) : ℝ :=
  (∑ σ : Outcome V, f σ) / Fintype.card (Outcome V)

/-- The exact pushforward law of a uniformly chosen total order under
restriction to any embedded finite set of labels. -/
theorem mean_restrict (e : I ↪ V) (f : Outcome I → ℝ) :
    mean (fun σ : Outcome V => f (restrict e σ)) = mean f := by
  have hglobal (τ : Equiv.Perm I) :
      (∑ σ : Outcome V, f (τ.trans (restrict e σ))) =
        ∑ σ : Outcome V, f (restrict e σ) := by
    simpa only [relabelEquiv, Equiv.coe_fn_mk, restrict_relabel] using
      (Equiv.sum_comp (relabelEquiv e τ) (fun σ => f (restrict e σ)))
  have hlocal (σ : Outcome V) :
      (∑ τ : Equiv.Perm I, f (τ.trans (restrict e σ))) =
        ∑ ρ : Outcome I, f ρ :=
    Equiv.sum_comp (permOutcomeEquiv (restrict e σ)) f
  have hdouble :
      (Fintype.card (Equiv.Perm I) : ℝ) *
          (∑ σ : Outcome V, f (restrict e σ)) =
        (Fintype.card (Outcome V) : ℝ) * (∑ ρ : Outcome I, f ρ) := by
    calc
      _ = ∑ τ : Equiv.Perm I, ∑ σ : Outcome V,
          f (τ.trans (restrict e σ)) := by
            simp only [hglobal, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = ∑ σ : Outcome V, ∑ τ : Equiv.Perm I,
          f (τ.trans (restrict e σ)) := Finset.sum_comm
      _ = _ := by
        simp only [hlocal, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hcard : Fintype.card (Equiv.Perm I) = Fintype.card (Outcome I) :=
    Fintype.card_congr (permOutcomeEquiv (Fintype.equivFin I))
  rw [hcard] at hdouble
  have hV : (Fintype.card (Outcome V) : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Fintype.card_pos_iff.mpr inferInstance))
  have hI : (Fintype.card (Outcome I) : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Fintype.card_pos_iff.mpr inferInstance))
  unfold mean
  apply (div_eq_div_iff hV hI).mpr
  simpa only [mul_comm] using hdouble

theorem mean_congr (f g : Outcome V → ℝ) (h : ∀ σ, f σ = g σ) :
    mean f = mean g := by
  unfold mean
  congr 1
  exact Finset.sum_congr rfl (fun σ _ => h σ)

theorem mean_mono (f g : Outcome V → ℝ) (h : ∀ σ, f σ ≤ g σ) :
    mean f ≤ mean g := by
  unfold mean
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun σ _ => h σ))
    (Nat.cast_nonneg _)

theorem mean_add (f g : Outcome V → ℝ) :
    mean (fun σ => f σ + g σ) = mean f + mean g := by
  simp only [mean, Finset.sum_add_distrib, add_div]

theorem mean_sub (f g : Outcome V → ℝ) :
    mean (fun σ => f σ - g σ) = mean f - mean g := by
  simp only [mean, Finset.sum_sub_distrib, sub_div]

theorem mean_const (a : ℝ) : mean (fun _ : Outcome V => a) = a := by
  have hV : (Fintype.card (Outcome V) : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Fintype.card_pos_iff.mpr inferInstance))
  simp only [mean, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact mul_div_cancel_left₀ a hV

end
end Papers.Rigidity.UniformOrders

end
end BundleSource0042

section BundleSource0043
/- Source: Papers/RigidityStressPrefix.lean -/





@[expose] public section

/-!
# Induced graph prefixes and their actual stress stars

Both prefix spaces are subspaces of the original unordered-edge
coefficient space, supported precisely on the induced graph before or
after the specified vertex enters.  The new-star kernel is the old
space, so its dimension increase is bounded by the supported part of
the actual global star image.
-/

namespace Papers.Rigidity.BarJoint

noncomputable section

open SupportedCode UniformOrders
open scoped Classical

variable {V : Type} [Fintype V]

def edgesBefore (G : SimpleGraph V) (σ : Outcome V) (v : V) : Set (Edge G) :=
  {e | ∀ w, w ∈ e.val → σ w < σ v}

def edgesThrough (G : SimpleGraph V) (σ : Outcome V) (v : V) : Set (Edge G) :=
  {e | ∀ w, w ∈ e.val → σ w ≤ σ v}

def incidentEdgeEmbedding (G : SimpleGraph V) (v : V) : IncidentEdge G v ↪ Edge G :=
  ⟨Subtype.val, Subtype.val_injective⟩

theorem edgesBefore_subset_edgesThrough (G : SimpleGraph V) (σ : Outcome V) (v : V) :
    edgesBefore G σ v ⊆ edgesThrough G σ v := by
  intro e he w hw
  exact (he w hw).le

theorem incident_not_edgesBefore (G : SimpleGraph V) (σ : Outcome V) (v : V)
    (e : IncidentEdge G v) : e.val ∉ edgesBefore G σ v := by
  intro he
  exact (lt_irrefl (σ v)) (he v e.property)

theorem new_edge_incident (G : SimpleGraph V) (σ : Outcome V) (v : V)
    (e : Edge G) (he : e ∈ edgesThrough G σ v) (hold : e ∉ edgesBefore G σ v) :
    e ∈ Set.range (incidentEdgeEmbedding G v) := by
  change ¬ ∀ w, w ∈ e.val → σ w < σ v at hold
  push_neg at hold
  obtain ⟨w, hw, hnot⟩ := hold
  have hwv : w = v := σ.injective (le_antisymm (he w hw) hnot)
  exact ⟨⟨e, hwv ▸ hw⟩, rfl⟩

theorem incident_edgesThrough_iff (G : SimpleGraph V) (σ : Outcome V) (v : V)
    (e : IncidentEdge G v) :
    e.val ∈ edgesThrough G σ v ↔ σ (incidentOther G v e) < σ v := by
  constructor
  · intro he
    have hle := he (incidentOther G v e) (Sym2.other_mem e.property)
    exact lt_of_le_of_ne hle (fun h => incidentOther_ne G v e (σ.injective h))
  · intro he w hw
    rw [← Sym2.other_spec e.property] at hw
    rcases Sym2.mem_iff.mp hw with h | h
    · subst w
      exact le_rfl
    · subst w
      exact he.le

/-- The old and new actual induced-prefix stress subspaces. -/
def stressBefore (G : SimpleGraph V) (W : Submodule ℝ (Edge G → ℝ))
    (σ : Outcome V) (v : V) : Submodule ℝ (Edge G → ℝ) :=
  supportedOn W (edgesBefore G σ v)

def stressThrough (G : SimpleGraph V) (W : Submodule ℝ (Edge G → ℝ))
    (σ : Outcome V) (v : V) : Submodule ℝ (Edge G → ℝ) :=
  supportedOn W (edgesThrough G σ v)

def precedingStarCode (G : SimpleGraph V) (W : Submodule ℝ (Edge G → ℝ))
    (σ : Outcome V) (v : V) : Submodule ℝ (IncidentEdge G v → ℝ) :=
  supportedOn (stressStarCode G v W)
    {e | σ (incidentOther G v e) < σ v}

/-- An actual induced-prefix dimension increase injects into the global
star image supported on the preceding neighbors.  This applies equally
to proper subspaces of the full stress space. -/
theorem stressPrefix_finrank_le (G : SimpleGraph V)
    (W : Submodule ℝ (Edge G → ℝ)) (σ : Outcome V) (v : V) :
    Module.finrank ℝ (stressThrough G W σ v) ≤
      Module.finrank ℝ (stressBefore G W σ v) +
        Module.finrank ℝ (precedingStarCode G W σ v) := by
  have h := supportedPrefix_finrank_le W (edgesBefore G σ v) (edgesThrough G σ v)
    (incidentEdgeEmbedding G v) (edgesBefore_subset_edgesThrough G σ v)
    (incident_not_edgesBefore G σ v) (new_edge_incident G σ v)
  have hsets : (incidentEdgeEmbedding G v) ⁻¹' edgesThrough G σ v =
      {e | σ (incidentOther G v e) < σ v} := by
    ext e
    exact incident_edgesThrough_iff G σ v e
  rw [hsets] at h
  exact h

theorem stressPrefix_dimension_increase_le (G : SimpleGraph V)
    (W : Submodule ℝ (Edge G → ℝ)) (σ : Outcome V) (v : V) :
    (Module.finrank ℝ (stressThrough G W σ v) : ℤ) -
        Module.finrank ℝ (stressBefore G W σ v) ≤
      Module.finrank ℝ (precedingStarCode G W σ v) := by
  have h := stressPrefix_finrank_le G W σ v
  omega

end
end Papers.Rigidity.BarJoint

end
end BundleSource0043

section BundleSource0044
/- Source: Papers/RigiditySupportedOrder.lean -/









@[expose] public section

/-!
# Uniform finite orders with a marker

An outcome is a literal permutation of the coordinates and one distinct
marker.  Its probability is the reciprocal of the factorial of the
number of labels.  We first use the coordinates following the marker;
reversing the permutation gives exactly the preceding-coordinate model.
The recursion conditions on the first label and shortens the actual
code whenever this label is a coordinate.
-/

namespace Papers.Rigidity.SupportedCode

noncomputable section

open scoped Classical BigOperators

variable {K : Type*} [Field K]

def remainingCode {n : ℕ} (W : Submodule K (Fin n → K))
    (σ : Equiv.Perm (Fin (n + 1))) : Submodule K (Fin n → K) where
  carrier := {w | w ∈ W ∧ ∀ i : Fin n,
    σ.symm i.castSucc < σ.symm (Fin.last n) → w i = 0}
  zero_mem' := ⟨W.zero_mem, by simp⟩
  add_mem' := by
    rintro u v ⟨hu, hu'⟩ ⟨hv, hv'⟩
    exact ⟨W.add_mem hu hv, fun i hi => by simp [hu' i hi, hv' i hi]⟩
  smul_mem' := by
    rintro a w ⟨hw, hw'⟩
    exact ⟨W.smul_mem a hw, fun i hi => by simp [hw' i hi]⟩

@[simp] theorem mem_remainingCode {n : ℕ} (W : Submodule K (Fin n → K))
    (σ : Equiv.Perm (Fin (n + 1))) (w : Fin n → K) :
    w ∈ remainingCode W σ ↔ w ∈ W ∧ ∀ i : Fin n,
      σ.symm i.castSucc < σ.symm (Fin.last n) → w i = 0 := Iff.rfl

theorem remainingCode_le {n : ℕ} (W : Submodule K (Fin n → K))
    (σ : Equiv.Perm (Fin (n + 1))) : remainingCode W σ ≤ W := fun _ h => h.1

/-- Literal expectation under the uniform finite ordering law. -/
def orderMean {n : ℕ} (W : Submodule K (Fin n → K)) : ℝ :=
  (∑ σ : Equiv.Perm (Fin (n + 1)), (Module.finrank K (remainingCode W σ) : ℝ)) /
    (n + 1).factorial

/-- The literal subspace supported on coordinates preceding the marker. -/
def precedingCode {n : ℕ} (W : Submodule K (Fin n → K))
    (σ : Equiv.Perm (Fin (n + 1))) : Submodule K (Fin n → K) where
  carrier := {w | w ∈ W ∧ ∀ i : Fin n,
    σ.symm (Fin.last n) < σ.symm i.castSucc → w i = 0}
  zero_mem' := ⟨W.zero_mem, by simp⟩
  add_mem' := by
    rintro u v ⟨hu, hu'⟩ ⟨hv, hv'⟩
    exact ⟨W.add_mem hu hv, fun i hi => by simp [hu' i hi, hv' i hi]⟩
  smul_mem' := by
    rintro a w ⟨hw, hw'⟩
    exact ⟨W.smul_mem a hw, fun i hi => by simp [hw' i hi]⟩

def precedingMean {n : ℕ} (W : Submodule K (Fin n → K)) : ℝ :=
  (∑ σ : Equiv.Perm (Fin (n + 1)), (Module.finrank K (precedingCode W σ) : ℝ)) /
    (n + 1).factorial

private def reversePositions (n : ℕ) : Equiv.Perm (Fin n) where
  toFun := Fin.rev
  invFun := Fin.rev
  left_inv := Fin.rev_rev
  right_inv := Fin.rev_rev

/-- Reversal is a probability-preserving bijection of the finite order
space because all outcomes have the same factorial weight. -/
private def reverseOrder (n : ℕ) :
    Equiv.Perm (Fin n) ≃ Equiv.Perm (Fin n) where
  toFun σ := (reversePositions n).trans σ
  invFun σ := (reversePositions n).trans σ
  left_inv σ := by ext i; simp [reversePositions]
  right_inv σ := by ext i; simp [reversePositions]

private theorem remainingCode_reverse {n : ℕ} (W : Submodule K (Fin n → K))
    (σ : Equiv.Perm (Fin (n + 1))) :
    remainingCode W (reverseOrder (n + 1) σ) = precedingCode W σ := by
  ext w
  simp [remainingCode, precedingCode, reverseOrder, reversePositions, Fin.rev_lt_rev]

theorem orderMean_eq_precedingMean {n : ℕ} (W : Submodule K (Fin n → K)) :
    orderMean W = precedingMean W := by
  unfold orderMean precedingMean
  apply congrArg (fun x : ℝ => x / (n + 1).factorial)
  calc
    _ = ∑ σ : Equiv.Perm (Fin (n + 1)),
        (Module.finrank K (remainingCode W (reverseOrder (n + 1) σ)) : ℝ) :=
      (Equiv.sum_comp (reverseOrder (n + 1))
        (fun σ => (Module.finrank K (remainingCode W σ) : ℝ))).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro σ _
      rw [remainingCode_reverse]

private theorem first_marker {n : ℕ} (W : Submodule K (Fin (n + 1) → K))
    (σ : Equiv.Perm (Fin (n + 1))) :
    remainingCode W (Equiv.Perm.decomposeFin'Symm (Fin.last (n + 1)) σ) = W := by
  ext w
  simp [mem_remainingCode]

private theorem first_coordinate_position {n : ℕ} (i : Fin (n + 1))
    (σ : Equiv.Perm (Fin (n + 1))) (j : Fin n) :
    (Equiv.Perm.decomposeFin'Symm i.castSucc σ).symm (i.succAbove j).castSucc =
      (σ.symm j.castSucc).succ := by
  have h := Equiv.Perm.decomposeFin'Symm_symm_succAbove i.castSucc σ
    (σ.symm j.castSucc)
  simpa only [Equiv.apply_symm_apply, Fin.castSucc_succAbove_castSucc] using h

private theorem marker_position {n : ℕ} (i : Fin (n + 1))
    (σ : Equiv.Perm (Fin (n + 1))) :
    (Equiv.Perm.decomposeFin'Symm i.castSucc σ).symm (Fin.last (n + 1)) =
      (σ.symm (Fin.last n)).succ := by
  have h := Equiv.Perm.decomposeFin'Symm_symm_succAbove i.castSucc σ
    (σ.symm (Fin.last n))
  simpa only [Equiv.apply_symm_apply,
    Fin.succAbove_ne_last_last (Fin.castSucc_ne_last i)] using h

private theorem first_coordinate_inactive {n : ℕ}
    (W : Submodule K (Fin (n + 1) → K)) (i : Fin (n + 1))
    (σ : Equiv.Perm (Fin (n + 1))) :
    i ∉ activeCoordinates (remainingCode W (Equiv.Perm.decomposeFin'Symm i.castSucc σ)) := by
  rintro hi
  obtain ⟨w, hw, hwi⟩ := (mem_activeCoordinates _ i).mp hi
  apply hwi
  apply hw.2 i
  rw [Equiv.Perm.decomposeFin'Symm_symm_eq_zero, marker_position]
  exact Fin.succ_pos _

private theorem shorten_remainingCode {n : ℕ}
    (W : Submodule K (Fin (n + 1) → K)) (i : Fin (n + 1))
    (σ : Equiv.Perm (Fin (n + 1))) :
    shorten (remainingCode W (Equiv.Perm.decomposeFin'Symm i.castSucc σ)) i =
      remainingCode (shorten W i) σ := by
  ext w
  simp only [mem_shorten, mem_remainingCode]
  constructor
  · rintro ⟨hw, hz⟩
    refine ⟨hw, ?_⟩
    intro j hj
    have h := hz (i.succAbove j)
    rw [first_coordinate_position, marker_position] at h
    simpa only [insertZero_succAbove] using h (Fin.succ_lt_succ_iff.mpr hj)
  · rintro ⟨hw, hz⟩
    refine ⟨hw, ?_⟩
    intro j hj
    cases j using Fin.succAboveCases i with
    | x => simp
    | p j =>
      rw [first_coordinate_position, marker_position] at hj
      simpa only [insertZero_succAbove] using hz j (Fin.succ_lt_succ_iff.mp hj)

private theorem first_coordinate_finrank {n : ℕ}
    (W : Submodule K (Fin (n + 1) → K)) (i : Fin (n + 1))
    (σ : Equiv.Perm (Fin (n + 1))) :
    Module.finrank K (remainingCode W (Equiv.Perm.decomposeFin'Symm i.castSucc σ)) =
      Module.finrank K (remainingCode (shorten W i) σ) := by
  rw [← shorten_remainingCode]
  exact (finrank_shorten_of_inactive _ i (first_coordinate_inactive W i σ)).symm

/-- Conditioning on the first label gives the exact finite-order
recursion, with the marker term equal to the whole code dimension. -/
theorem orderMean_recursion {n : ℕ} (W : Submodule K (Fin (n + 1) → K)) :
    orderMean W =
      ((Module.finrank K W : ℝ) + ∑ i : Fin (n + 1), orderMean (shorten W i)) /
        (n + 2) := by
  have hsum :
      (∑ τ : Equiv.Perm (Fin (n + 2)), (Module.finrank K (remainingCode W τ) : ℝ)) =
      (n + 1).factorial * (Module.finrank K W : ℝ) +
        ∑ i : Fin (n + 1),
          ∑ σ : Equiv.Perm (Fin (n + 1)),
            (Module.finrank K (remainingCode (shorten W i) σ) : ℝ) := by
    rw [← Equiv.sum_comp (Equiv.Perm.decomposeFin' (n := n)).symm]
    rw [Fintype.sum_prod_type, Fin.sum_univ_castSucc]
    simp only [Equiv.Perm.decomposeFin'_symm]
    change
      (∑ i : Fin (n + 1), ∑ σ : Equiv.Perm (Fin (n + 1)),
        (Module.finrank K (remainingCode W
          (Equiv.Perm.decomposeFin'Symm i.castSucc σ)) : ℝ)) +
      (∑ σ : Equiv.Perm (Fin (n + 1)),
        (Module.finrank K (remainingCode W
          (Equiv.Perm.decomposeFin'Symm (Fin.last (n + 1)) σ)) : ℝ)) = _
    calc
      _ = (∑ i : Fin (n + 1), ∑ σ : Equiv.Perm (Fin (n + 1)),
          (Module.finrank K (remainingCode (shorten W i) σ) : ℝ)) +
          (n + 1).factorial * (Module.finrank K W : ℝ) := by
        apply congrArg₂ (fun x y : ℝ => x + y)
        · apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro σ _
          exact congrArg (fun r : ℕ => (r : ℝ)) (first_coordinate_finrank W i σ)
        · calc
            _ = ∑ σ : Equiv.Perm (Fin (n + 1)), (Module.finrank K W : ℝ) := by
              apply Finset.sum_congr rfl
              intro σ _
              rw [first_marker W σ]
            _ = _ := by
              simp only [Finset.sum_const, Finset.card_univ,
                Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
      _ = _ := add_comm _ _
  unfold orderMean
  rw [hsum, Nat.factorial_succ (n + 1)]
  have hfac : ((n + 1).factorial : ℝ) ≠ 0 := by positivity
  have hn : (n + 2 : ℝ) ≠ 0 := by positivity
  have hn' : (n + 1 + 1 : ℝ) ≠ 0 := by positivity
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  rw [← Finset.sum_div]
  field_simp [hfac, hn, hn']
  <;> ring

theorem orderMean_eq_zero_of_finrank_eq_zero {n : ℕ}
    (W : Submodule K (Fin n → K)) (hW : Module.finrank K W = 0) :
    orderMean W = 0 := by
  have hz (σ : Equiv.Perm (Fin (n + 1))) :
      Module.finrank K (remainingCode W σ) = 0 := by
    have h := Submodule.finrank_mono (remainingCode_le W σ)
    omega
  simp [orderMean, hz]

end

end Papers.Rigidity.SupportedCode

end
end BundleSource0044

section BundleSource0045
/- Source: Papers/RigiditySupportedBound.lean -/




@[expose] public section

/-!
# The supported-code inequality for every field and finite length

This is the full inequality needed for the random-order stress argument.
Its expectation is the uniform average of the actual supported subspace
dimensions over all coordinate-and-marker permutations.  The proof uses
no coding-theoretic axiom, probabilistic memorylessness assertion, or
additional hypothesis on the code.
-/

namespace Papers.Rigidity.SupportedCode

noncomputable section

open scoped Classical BigOperators

def bound (s r : ℕ) : ℝ := (r : ℝ) * (r + 1) / (2 * (r + s))

@[simp] theorem bound_zero (s : ℕ) : bound s 0 = 0 := by simp [bound]

theorem bound_succ_mono (s r : ℕ) (hs : 1 ≤ s) : bound s r ≤ bound s (r + 1) := by
  have hs' : (0 : ℝ) < s := by exact_mod_cast (show 0 < s by omega)
  have hden : (r : ℝ) + s ≠ 0 := by positivity
  have hden' : (r : ℝ) + 1 + s ≠ 0 := by positivity
  have hdiff : bound s (r + 1) - bound s r =
      ((r : ℝ) + 1) * (r + 2 * s) /
        (2 * (r + s) * (r + 1 + s)) := by
    unfold bound
    push_cast
    field_simp
    <;> ring
  apply sub_nonneg.mp
  rw [hdiff]
  positivity

private theorem bound_step (s r d g : ℕ) (hs : 1 ≤ s) (hr : 1 ≤ r)
    (hg : g ≤ d) (hsingle : r + s ≤ g + 1) :
    ((r : ℝ) + ((d - g : ℕ) : ℝ) * bound s r + (g : ℝ) * bound s (r - 1)) /
        (d + 1) ≤ bound s r := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show r ≠ 0 by omega)
  have hs' : (0 : ℝ) < s := by exact_mod_cast (show 0 < s by omega)
  have hden : (k : ℝ) + s ≠ 0 := by positivity
  have hden' : (k : ℝ) + 1 + s ≠ 0 := by positivity
  have hidentity : ((k : ℝ) + 1 + s) * bound s (k + 1) =
      (k + 1) + (k + s) * bound s k := by
    unfold bound
    push_cast
    field_simp
    <;> ring
  have hmono := bound_succ_mono s k hs
  have hg' : (k : ℝ) + s ≤ g := by exact_mod_cast (show k + s ≤ g by omega)
  have hmul := mul_nonneg (sub_nonneg.mpr hg') (sub_nonneg.mpr hmono)
  have hmain : (k : ℝ) + 1 + (g : ℝ) * bound s k ≤
      ((g : ℝ) + 1) * bound s (k + 1) := by
    nlinarith [hidentity]
  have hd : (0 : ℝ) < d + 1 := by positivity
  apply (div_le_iff₀ hd).mpr
  rw [Nat.cast_sub hg]
  norm_num only [Nat.succ_eq_add_one, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
  nlinarith [hmain]

/-- Lemma 2.1's supported-subspace upper bound, under the exact uniform
finite order law.  The length and support threshold are unrestricted,
and the coefficient field is arbitrary. -/
theorem orderMean_le_bound {K : Type*} [Field K] {n s : ℕ}
    (W : Submodule K (Fin n → K)) (hs : 1 ≤ s) (hmin : MinimumSupport W s) :
    orderMean W ≤ bound s (Module.finrank K W) := by
  induction n with
  | zero =>
    have hzero : Module.finrank K W = 0 := by
      have h := W.finrank_le
      simpa using h
    rw [orderMean_eq_zero_of_finrank_eq_zero W hzero, hzero, bound_zero]
  | succ n ih =>
    by_cases hrzero : Module.finrank K W = 0
    · rw [orderMean_eq_zero_of_finrank_eq_zero W hrzero, hrzero, bound_zero]
    · let r := Module.finrank K W
      let g := (activeCoordinates W).card
      have hr : 1 ≤ r := by omega
      have hg : g ≤ n + 1 := by
        exact (Finset.card_le_univ _).trans_eq (Fintype.card_fin _)
      have hW : W ≠ ⊥ := by intro hz; simp [hz] at hrzero
      have hsingle : r + s ≤ g + 1 := singleton_bound W s hs hmin hW
      have hterm (i : Fin (n + 1)) : orderMean (shorten W i) ≤
          if i ∈ activeCoordinates W then bound s (r - 1) else bound s r := by
        have h := ih (shorten W i) (minimumSupport_shorten W i hmin)
        by_cases hi : i ∈ activeCoordinates W
        · have hd := finrank_shorten_of_active W i hi
          have hd' : Module.finrank K (shorten W i) = r - 1 := by omega
          simpa [hi, hd'] using h
        · have hd := finrank_shorten_of_inactive W i hi
          simpa [hi, hd, r] using h
      have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hterm i)
      have hite :
          (∑ i : Fin (n + 1), if i ∈ activeCoordinates W then bound s (r - 1) else bound s r) =
            (g : ℝ) * bound s (r - 1) + ((n + 1 - g : ℕ) : ℝ) * bound s r := by
        rw [Finset.sum_ite]
        have hpos : (Finset.univ.filter fun i => i ∈ activeCoordinates W) =
            activeCoordinates W := by ext i; simp
        have hneg : (Finset.univ.filter fun i => i ∉ activeCoordinates W) =
            Finset.univ \ activeCoordinates W := by ext i; simp
        rw [hpos, hneg]
        simp only [Finset.sum_const, nsmul_eq_mul,
          Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
          Fintype.card_fin, g]
      rw [hite] at hsum
      rw [orderMean_recursion]
      calc
        ((Module.finrank K W : ℝ) + ∑ i : Fin (n + 1), orderMean (shorten W i)) /
            (n + 2) ≤
            ((r : ℝ) + (g : ℝ) * bound s (r - 1) +
              ((n + 1 - g : ℕ) : ℝ) * bound s r) / (n + 2) := by
                apply div_le_div_of_nonneg_right _ (by positivity)
                dsimp [r] at *
                linarith
        _ ≤ bound s r := by
          have h := bound_step s r (n + 1) g hs hr hg hsingle
          convert h using 1 <;> push_cast <;> ring

/-- The same bound in the paper's preceding-coordinate convention. -/
theorem precedingMean_le_bound {K : Type*} [Field K] {n s : ℕ}
    (W : Submodule K (Fin n → K)) (hs : 1 ≤ s) (hmin : MinimumSupport W s) :
    precedingMean W ≤ bound s (Module.finrank K W) := by
  rw [← orderMean_eq_precedingMean]
  exact orderMean_le_bound W hs hmin

end

end Papers.Rigidity.SupportedCode

end
end BundleSource0045

section BundleSource0046
/- Source: Papers/RigiditySupportedRelabel.lean -/





@[expose] public section

/-!
# Supported codes under actual vertex orders

Coordinate relabeling preserves support, dimension and each supported
subspace.  The preceding-code estimate is then transported from its
finite permutation model to the restriction of a genuinely uniform
order on an arbitrary finite ambient vertex set.
-/

namespace Papers.Rigidity.SupportedCode

noncomputable section

open UniformOrders
open scoped Classical BigOperators

variable {K I J : Type*} [Field K] [Fintype I] [Fintype J]

def reindexCode (W : Submodule K (I → K)) (e : J ≃ I) : Submodule K (J → K) :=
  W.map (LinearEquiv.funCongrLeft K K e).toLinearMap

theorem support_reindex (w : I → K) (e : J ≃ I) :
    support (fun j => w (e j)) = (support w).map e.symm.toEmbedding := by
  ext j
  simp only [mem_support, Finset.mem_map, Equiv.toEmbedding_apply]
  constructor
  · intro h
    exact ⟨e j, h, e.symm_apply_apply j⟩
  · rintro ⟨i, hi, rfl⟩
    simpa using hi

theorem minimumSupport_reindex (W : Submodule K (I → K)) (e : J ≃ I)
    {s : ℕ} (hW : MinimumSupport W s) : MinimumSupport (reindexCode W e) s := by
  rintro a ⟨w, hw, rfl⟩ hne
  have hwn : w ≠ 0 := by
    intro hz
    apply hne
    rw [hz, map_zero]
  have h := hW w hw hwn
  change s ≤ (support (fun j => w (e j))).card
  simpa only [support_reindex, Finset.card_map] using h

theorem finrank_reindex (W : Submodule K (I → K)) (e : J ≃ I) :
    Module.finrank K (reindexCode W e) = Module.finrank K W :=
  (LinearEquiv.funCongrLeft K K e).finrank_map_eq W

theorem reindex_supportedOn (W : Submodule K (I → K)) (e : J ≃ I) (A : Set I) :
    reindexCode (supportedOn W A) e = supportedOn (reindexCode W e) (e ⁻¹' A) := by
  ext a
  constructor
  · rintro ⟨w, ⟨hw, hs⟩, rfl⟩
    exact ⟨⟨w, hw, rfl⟩, fun j hj => hs (e j) hj⟩
  · rintro ⟨⟨w, hw, rfl⟩, hs⟩
    refine ⟨w, ⟨hw, ?_⟩, rfl⟩
    intro i hi
    have h := hs (e.symm i)
    simpa using h (by simpa using hi)

theorem finrank_supportedOn_reindex (W : Submodule K (I → K))
    (e : J ≃ I) (A : Set I) :
    Module.finrank K (supportedOn (reindexCode W e) (e ⁻¹' A)) =
      Module.finrank K (supportedOn W A) := by
  rw [← reindex_supportedOn]
  exact finrank_reindex _ _

theorem precedingCode_eq_supportedOn {n : ℕ}
    (W : Submodule K (Fin n → K)) (σ : Equiv.Perm (Fin (n + 1))) :
    precedingCode W σ = supportedOn W
      {i | σ.symm i.castSucc < σ.symm (Fin.last n)} := by
  ext w
  constructor
  · rintro ⟨hw, hs⟩
    refine ⟨hw, ?_⟩
    intro i hi
    apply hs i
    exact lt_of_le_of_ne (le_of_not_gt hi)
      (fun h => (Fin.castSucc_ne_last i) (σ.symm.injective h).symm)
  · rintro ⟨hw, hs⟩
    refine ⟨hw, ?_⟩
    intro i hi
    exact hs i (not_lt_of_gt hi)

end
end Papers.Rigidity.SupportedCode

namespace Papers.Rigidity.UniformOrders

noncomputable section

open scoped Classical BigOperators

def finOutcomeEquiv (n : ℕ) : Outcome (Fin n) ≃ Equiv.Perm (Fin n) where
  toFun ρ := (ρ.trans (finCongr (Fintype.card_fin n))).symm
  invFun σ := σ.symm.trans (finCongr (Fintype.card_fin n)).symm
  left_inv ρ := by ext i; simp
  right_inv σ := by ext i; simp

theorem mean_finOutcome (n : ℕ) (f : Equiv.Perm (Fin n) → ℝ) :
    mean (fun ρ : Outcome (Fin n) => f (finOutcomeEquiv n ρ)) =
      (∑ σ : Equiv.Perm (Fin n), f σ) / n.factorial := by
  have hcard : Fintype.card (Outcome (Fin n)) = n.factorial := by
    calc
      _ = Fintype.card (Equiv.Perm (Fin n)) := Fintype.card_congr (finOutcomeEquiv n)
      _ = n.factorial := by rw [Fintype.card_perm, Fintype.card_fin]
  unfold mean
  apply congrArg₂ (fun x y : ℝ => x / y)
  · apply Finset.sum_equiv (finOutcomeEquiv n)
    · intro ρ
      simp only [Finset.mem_univ]
    · intro ρ _
      rfl
  · simpa only [← Nat.card_eq_fintype_card] using
      congrArg (fun k : ℕ => (k : ℝ)) hcard

variable {V : Type*} [Fintype V]

def restrictPermutation {n : ℕ} (e : Fin n ↪ V) (σ : Outcome V) :
    Equiv.Perm (Fin n) := finOutcomeEquiv n (restrict e σ)

theorem restrictPermutation_lt_iff {n : ℕ} (e : Fin n ↪ V)
    (σ : Outcome V) (i j : Fin n) :
    (restrictPermutation e σ).symm i < (restrictPermutation e σ).symm j ↔
      σ (e i) < σ (e j) := by
  simpa only [restrictPermutation, finOutcomeEquiv, Equiv.coe_fn_mk, Equiv.symm_symm,
    Equiv.trans_apply, finCongr_apply, Fin.cast_lt_cast] using restrict_lt_iff e σ i j

theorem mean_restrictPermutation {n : ℕ} (e : Fin n ↪ V)
    (f : Equiv.Perm (Fin n) → ℝ) :
    mean (fun σ : Outcome V => f (restrictPermutation e σ)) =
      (∑ τ : Equiv.Perm (Fin n), f τ) / n.factorial := by
  unfold restrictPermutation
  exact (mean_restrict e (fun ρ => f (finOutcomeEquiv n ρ))).trans
    (mean_finOutcome n f)

/-- The supported-code bound for the labels of a fixed embedded
coordinate-and-marker set inside an actual global vertex permutation. -/
theorem mean_supported_preceding_le {K : Type*} [Field K] {n s : ℕ}
    (e : Fin (n + 1) ↪ V) (W : Submodule K (Fin n → K))
    (hs : 1 ≤ s) (hW : SupportedCode.MinimumSupport W s) :
    mean (fun σ : Outcome V =>
      (Module.finrank K (SupportedCode.supportedOn W
        {i | σ (e i.castSucc) < σ (e (Fin.last n))}) : ℝ)) ≤
      SupportedCode.bound s (Module.finrank K W) := by
  have hcode (σ : Outcome V) :
      SupportedCode.supportedOn W
        {i | σ (e i.castSucc) < σ (e (Fin.last n))} =
      SupportedCode.precedingCode W (restrictPermutation e σ) := by
    rw [SupportedCode.precedingCode_eq_supportedOn]
    congr 1
    ext i
    exact (restrictPermutation_lt_iff e σ i.castSucc (Fin.last n)).symm
  calc
    _ = mean (fun σ : Outcome V =>
        (Module.finrank K (SupportedCode.precedingCode W
          (restrictPermutation e σ)) : ℝ)) := by
      apply congrArg mean
      funext σ
      exact congrArg (fun S : Submodule K (Fin n → K) =>
        (Module.finrank K S : ℝ)) (hcode σ)
    _ = SupportedCode.precedingMean W :=
      mean_restrictPermutation e
        (fun τ => (Module.finrank K (SupportedCode.precedingCode W τ) : ℝ))
    _ ≤ SupportedCode.bound s (Module.finrank K W) :=
      SupportedCode.precedingMean_le_bound W hs hW

end
end Papers.Rigidity.UniformOrders

end
end BundleSource0046

section BundleSource0047
/- Source: Papers/RigidityStressExpectation.lean -/




@[expose] public section

/-!
# The supported-stress expectation in Corollary 2.2

The expectation here is taken over the actual uniformly chosen global
vertex order.  The proof combines the previously established local-order
pushforward law, force equilibrium at the given general-position
placement, and the actual prefix-kernel injection.
-/

namespace Papers.Rigidity.BarJoint

noncomputable section

open SupportedCode UniformOrders
open scoped Classical

variable {V : Type} [Fintype V]

def starEnumeration (G : SimpleGraph V) (v : V) :
    Fin (Fintype.card (IncidentEdge G v)) ≃ IncidentEdge G v :=
  (Fintype.equivFin (IncidentEdge G v)).symm

/-- The coordinates are the distinct neighboring vertices; the final
marker is the vertex whose insertion is being studied. -/
def starMarkerEmbedding (G : SimpleGraph V) (v : V) :
    Fin (Fintype.card (IncidentEdge G v) + 1) ↪ V where
  toFun := Fin.lastCases v (fun i => incidentOther G v (starEnumeration G v i))
  inj' := by
    intro i j hij
    cases i using Fin.lastCases with
    | last =>
      cases j using Fin.lastCases with
      | last => rfl
      | cast j =>
        simp only [Fin.lastCases_last, Fin.lastCases_castSucc] at hij
        exact False.elim (incidentOther_ne G v (starEnumeration G v j) hij.symm)
    | cast i =>
      cases j using Fin.lastCases with
      | last =>
        simp only [Fin.lastCases_last, Fin.lastCases_castSucc] at hij
        exact False.elim (incidentOther_ne G v (starEnumeration G v i) hij)
      | cast j =>
        simp only [Fin.lastCases_castSucc] at hij
        exact congrArg Fin.castSucc
          ((starEnumeration G v).injective (incidentOther_injective G v hij))

@[simp] theorem starMarkerEmbedding_coordinate (G : SimpleGraph V) (v : V)
    (i : Fin (Fintype.card (IncidentEdge G v))) :
    starMarkerEmbedding G v i.castSucc = incidentOther G v (starEnumeration G v i) := by
  simp [starMarkerEmbedding]

@[simp] theorem starMarkerEmbedding_marker (G : SimpleGraph V) (v : V) :
    starMarkerEmbedding G v (Fin.last (Fintype.card (IncidentEdge G v))) = v := by
  simp [starMarkerEmbedding]

/-- Expected supported dimension in the actual global star image, with
no independence law for local positions assumed in the hypotheses. -/
theorem mean_precedingStarCode_le
    (G : SimpleGraph V) (p : Placement V 3) (hp : GeneralPosition.InGeneralPosition p)
    (v : V) (W : Submodule ℝ (Edge G → ℝ)) (hW : W ≤ StressSpace G p) :
    mean (fun σ : Outcome V => (Module.finrank ℝ (precedingStarCode G W σ v) : ℝ)) ≤
      bound 4 (Module.finrank ℝ (stressStarCode G v W)) := by
  let e := starEnumeration G v
  let C := reindexCode (stressStarCode G v W) e
  have hC : MinimumSupport C 4 :=
    minimumSupport_reindex _ e (stressStarCode_minimumSupport_four G p hp v W hW)
  have hmean := mean_supported_preceding_le (starMarkerEmbedding G v) C (by decide) hC
  have hdim (σ : Outcome V) :
      Module.finrank ℝ (supportedOn C
        {i | σ (starMarkerEmbedding G v i.castSucc) <
          σ (starMarkerEmbedding G v (Fin.last (Fintype.card (IncidentEdge G v))))}) =
      Module.finrank ℝ (precedingStarCode G W σ v) := by
    have hset :
        {i | σ (starMarkerEmbedding G v i.castSucc) <
          σ (starMarkerEmbedding G v (Fin.last (Fintype.card (IncidentEdge G v))))} =
        e ⁻¹' {a | σ (incidentOther G v a) < σ v} := by
      ext i
      change σ (starMarkerEmbedding G v i.castSucc) <
          σ (starMarkerEmbedding G v (Fin.last (Fintype.card (IncidentEdge G v)))) ↔
        σ (incidentOther G v (e i)) < σ v
      rw [starMarkerEmbedding_coordinate G v i, starMarkerEmbedding_marker G v]
    calc
      _ = Module.finrank ℝ (supportedOn C
          (e ⁻¹' {a | σ (incidentOther G v a) < σ v})) :=
        congrArg (fun S : Set (Fin (Fintype.card (IncidentEdge G v))) =>
          Module.finrank ℝ (supportedOn C S)) hset
      _ = _ := finrank_supportedOn_reindex (stressStarCode G v W) e
        {a | σ (incidentOther G v a) < σ v}
  have hCd : Module.finrank ℝ C = Module.finrank ℝ (stressStarCode G v W) :=
    finrank_reindex _ e
  calc
    _ = mean (fun σ : Outcome V =>
        (Module.finrank ℝ (supportedOn C
          {i | σ (starMarkerEmbedding G v i.castSucc) <
            σ (starMarkerEmbedding G v
              (Fin.last (Fintype.card (IncidentEdge G v))))}) : ℝ)) := by
      apply congrArg mean
      funext σ
      exact congrArg (fun k : ℕ => (k : ℝ)) (hdim σ).symm
    _ ≤ bound 4 (Module.finrank ℝ C) := hmean
    _ = bound 4 (Module.finrank ℝ (stressStarCode G v W)) :=
      congrArg (bound 4) hCd

/-- The actual expected induced-prefix increase of a fixed stress
subspace.  The integer-valued dimensions are embedded in `ℝ` before
subtraction, so this definition involves no truncated natural subtraction. -/
def stressDimensionContribution (G : SimpleGraph V)
    (W : Submodule ℝ (Edge G → ℝ)) (v : V) : ℝ :=
  mean fun σ : Outcome V =>
    (Module.finrank ℝ (stressThrough G W σ v) : ℝ) -
      Module.finrank ℝ (stressBefore G W σ v)

/-- The full subspace assertion of Corollary 2.2, for every finite graph,
every general-position placement, and every actual stress subspace. -/
theorem corollary_two_two_subspace
    (G : SimpleGraph V) (p : Placement V 3) (hp : GeneralPosition.InGeneralPosition p)
    (v : V) (W : Submodule ℝ (Edge G → ℝ)) (hW : W ≤ StressSpace G p) :
    stressDimensionContribution G W v ≤
      bound 4 (Module.finrank ℝ (stressStarCode G v W)) := by
  apply le_trans (mean_mono _ _ ?_) (mean_precedingStarCode_le G p hp v W hW)
  intro σ
  have h := stressPrefix_finrank_le G W σ v
  have hreal :
      (Module.finrank ℝ (stressThrough G W σ v) : ℝ) ≤
        (Module.finrank ℝ (stressBefore G W σ v) : ℝ) +
          Module.finrank ℝ (precedingStarCode G W σ v) := by exact_mod_cast h
  linarith

end
end Papers.Rigidity.BarJoint

end
end BundleSource0047

section BundleSource0048
/- Source: Papers/RigidityRankContributions.lean -/






@[expose] public section

/-!
# Actual vertex-order rigidity-rank contributions

The graph at each stage is the induced prefix with the remaining labels
isolated.  Rank contributions are literal uniform averages of successive
generic ranks.  Their sum is the rank of the original graph.  The
expected number of newly inserted edges is proved by swapping the two
endpoint labels in the uniform order space.
-/

namespace Papers.Rigidity.UniformOrders

noncomputable section

open scoped Classical BigOperators

variable {V I : Type*} [Fintype V] [Fintype I]

theorem mean_sum (f : I → Outcome V → ℝ) :
    mean (fun σ => ∑ i, f i σ) = ∑ i, mean (f i) := by
  unfold mean
  rw [Finset.sum_comm, Finset.sum_div]

theorem mean_indicator_precedes (v w : V) (hne : v ≠ w) :
    mean (fun σ : Outcome V => if σ v < σ w then (1 : ℝ) else 0) = 1 / 2 := by
  let F : Outcome V → ℝ := fun σ => if σ v < σ w then 1 else 0
  let H : Outcome V → ℝ := fun σ => if σ w < σ v then 1 else 0
  let swap : Outcome V ≃ Outcome V :=
    { toFun := fun σ => (Equiv.swap v w).trans σ
      invFun := fun σ => (Equiv.swap v w).trans σ
      left_inv := by intro σ; ext a; simp
      right_inv := by intro σ; ext a; simp }
  have hsum : (∑ σ : Outcome V, F σ) = ∑ σ : Outcome V, H σ := by
    have h := Equiv.sum_comp swap F
    simpa [F, H, swap] using h.symm
  have hmean : mean F = mean H := by unfold mean; rw [hsum]
  have hone (σ : Outcome V) : F σ + H σ = 1 := by
    have hneq : σ v ≠ σ w := σ.injective.ne hne
    rcases lt_or_gt_of_ne hneq with hlt | hgt
    · simp [F, H, hlt, not_lt_of_gt hlt]
    · simp [F, H, hgt, not_lt_of_gt hgt]
  have htotal : mean F + mean H = 1 := by
    rw [← mean_add, mean_congr _ _ hone, mean_const]
  change mean F = 1 / 2
  linarith

end
end Papers.Rigidity.UniformOrders

namespace Papers.Rigidity.BarJoint

noncomputable section

open SupportedCode UniformOrders
open scoped Classical BigOperators

variable {V : Type} [Fintype V]

/-- The actual graph induced by the first `k` labels; all remaining
labels are isolated and contribute no bar row. -/
def prefixGraph (G : SimpleGraph V) (σ : Outcome V) (k : ℕ) : SimpleGraph V where
  Adj v w := G.Adj v w ∧ (σ v).val < k ∧ (σ w).val < k
  symm := by constructor; rintro v w ⟨h, hv, hw⟩; exact ⟨h.symm, hw, hv⟩
  loopless := by constructor; intro v; rintro ⟨h, _⟩; exact G.loopless.irrefl v h

theorem prefixGraph_le (G : SimpleGraph V) (σ : Outcome V) (k : ℕ) :
    prefixGraph G σ k ≤ G := fun _ _ h => h.1

@[simp] theorem prefixGraph_zero (G : SimpleGraph V) (σ : Outcome V) :
    prefixGraph G σ 0 = ⊥ := by ext v w; simp [prefixGraph]

@[simp] theorem prefixGraph_card (G : SimpleGraph V) (σ : Outcome V) :
    prefixGraph G σ (Fintype.card V) = G := by
  ext v w
  simp only [prefixGraph, and_iff_left_iff_imp]
  exact fun _ => ⟨(σ v).isLt, (σ w).isLt⟩

theorem subgraphEdgeSet_prefixGraph (G : SimpleGraph V) (σ : Outcome V) (k : ℕ) :
    subgraphEdgeSet G (prefixGraph G σ k) =
      {e : Edge G | ∀ w, w ∈ e.val → (σ w).val < k} := by
  ext e
  rcases e with ⟨e, he⟩
  induction e using Sym2.inductionOn with
  | _ a b =>
      change (G.Adj a b ∧ (σ a).val < k ∧ (σ b).val < k) ↔ _
      have hab : G.Adj a b := he
      simp [Sym2.mem_iff, hab]

theorem subgraphEdgeSet_prefix_before (G : SimpleGraph V) (σ : Outcome V) (v : V) :
    subgraphEdgeSet G (prefixGraph G σ (σ v).val) = edgesBefore G σ v := by
  rw [subgraphEdgeSet_prefixGraph]
  rfl

theorem subgraphEdgeSet_prefix_through (G : SimpleGraph V) (σ : Outcome V) (v : V) :
    subgraphEdgeSet G (prefixGraph G σ ((σ v).val + 1)) = edgesThrough G σ v := by
  rw [subgraphEdgeSet_prefixGraph]
  ext e
  simp only [Set.mem_setOf_eq, edgesThrough, Nat.lt_add_one_iff, Fin.le_def]

/-- A rank contribution is the expected change in actual generic
rigidity rank at the moment the named vertex enters. -/
def rankContribution (G : SimpleGraph V) (v : V) : ℝ :=
  mean fun σ : Outcome V =>
    (genericRigidityRank (prefixGraph G σ ((σ v).val + 1)) 3 : ℝ) -
      genericRigidityRank (prefixGraph G σ (σ v).val) 3

/-- No rank is lost in the bookkeeping: the contributions add to the
full graph rank, for every finite graph including the empty graph. -/
theorem sum_rankContribution (G : SimpleGraph V) :
    (∑ v : V, rankContribution G v) = (genericRigidityRank G 3 : ℝ) := by
  have htel (σ : Outcome V) :
      (∑ v : V, ((genericRigidityRank (prefixGraph G σ ((σ v).val + 1)) 3 : ℝ) -
        genericRigidityRank (prefixGraph G σ (σ v).val) 3)) =
      (genericRigidityRank G 3 : ℝ) := by
    let f : ℕ → ℝ := fun k => genericRigidityRank (prefixGraph G σ k) 3
    have heq := Equiv.sum_comp σ (fun k : Fin (Fintype.card V) => f (k.val + 1) - f k.val)
    rw [heq, Fin.sum_univ_eq_sum_range
      (fun k => f (k + 1) - f k) (Fintype.card V), Finset.sum_range_sub f]
    simp [f, genericRigidityRank_bot]
  simp only [rankContribution]
  rw [← mean_sum]
  rw [mean_congr _ _ htel, mean_const]

def precedingIncidentCount (G : SimpleGraph V) (σ : Outcome V) (v : V) : ℕ :=
  (Finset.univ.filter (fun e : IncidentEdge G v => σ (incidentOther G v e) < σ v)).card

/-- The expected number of preceding incident edges is half the literal
number of incident edges.  This follows from the actual global order,
with no probabilistic assumption about neighboring labels. -/
theorem mean_precedingIncidentCount (G : SimpleGraph V) (v : V) :
    mean (fun σ : Outcome V => (precedingIncidentCount G σ v : ℝ)) =
      (Fintype.card (IncidentEdge G v) : ℝ) / 2 := by
  have hcount (σ : Outcome V) : (precedingIncidentCount G σ v : ℝ) =
      ∑ e : IncidentEdge G v, if σ (incidentOther G v e) < σ v then (1 : ℝ) else 0 := by
    simp [precedingIncidentCount, Finset.sum_boole]
  rw [mean_congr _ _ hcount, mean_sum]
  simp_rw [mean_indicator_precedes _ _ (incidentOther_ne G v _)]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

/-- The two supported spaces appearing in the prefix injection have
exactly the ordinary induced-subgraph stress dimensions. -/
theorem prefix_rank_stress_identities (G : SimpleGraph V) (p : Placement V 3)
    (σ : Outcome V) (v : V) :
    rigidityRank (prefixGraph G σ (σ v).val) p +
        Module.finrank ℝ (stressBefore G (StressSpace G p) σ v) =
      Fintype.card (Edge (prefixGraph G σ (σ v).val)) ∧
    rigidityRank (prefixGraph G σ ((σ v).val + 1)) p +
        Module.finrank ℝ (stressThrough G (StressSpace G p) σ v) =
      Fintype.card (Edge (prefixGraph G σ ((σ v).val + 1))) := by
  constructor
  · exact (congrArg (fun S : Set (Edge G) =>
        rigidityRank (prefixGraph G σ (σ v).val) p +
          Module.finrank ℝ (SupportedCode.supportedOn (StressSpace G p) S))
        (subgraphEdgeSet_prefix_before G σ v)).symm.trans
      (rigidityRank_add_supportedStress_dimension (prefixGraph_le G σ (σ v).val) p)
  · exact (congrArg (fun S : Set (Edge G) =>
        rigidityRank (prefixGraph G σ ((σ v).val + 1)) p +
          Module.finrank ℝ (SupportedCode.supportedOn (StressSpace G p) S))
        (subgraphEdgeSet_prefix_through G σ v)).symm.trans
      (rigidityRank_add_supportedStress_dimension
        (prefixGraph_le G σ ((σ v).val + 1)) p)

end
end Papers.Rigidity.BarJoint

end
end BundleSource0048

section BundleSource0049
/- Source: Papers/RigidityRankContributionBound.lean -/




@[expose] public section

/-!
# The actual rank-contribution bound from stress support

The change in the number of prefix edges is identified with the actual
preceding incident edges.  Together with the exact rank/stress identities,
this gives the rank-contribution bound in terms of the dimension of the
full star image.  No generic-rank increment is defined by the desired
inequality.
-/

namespace Papers.Rigidity.BarJoint

noncomputable section

open SupportedCode UniformOrders
open scoped Classical BigOperators

variable {V : Type} [Fintype V]

def incidentEdgeEquivIncidenceSet (G : SimpleGraph V) (v : V) :
    IncidentEdge G v ≃ G.incidenceSet v where
  toFun e := ⟨e.val.val, e.val.property, e.property⟩
  invFun e := ⟨⟨e.val, e.property.1⟩, e.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_incidentEdge_eq_degree (G : SimpleGraph V) (v : V) :
    Fintype.card (IncidentEdge G v) = G.degree v := by
  rw [Fintype.card_congr (incidentEdgeEquivIncidenceSet G v),
    G.card_incidenceSet_eq_degree]

def newPrefixEdgeEquiv (G : SimpleGraph V) (σ : Outcome V) (v : V) :
    ↥(edgesThrough G σ v \ edgesBefore G σ v) ≃
      {e : IncidentEdge G v // σ (incidentOther G v e) < σ v} where
  toFun e := by
    have hv : v ∈ e.val.val := by
      obtain ⟨f, hf⟩ := new_edge_incident G σ v e.val e.property.1 e.property.2
      change f.val = e.val at hf
      exact hf ▸ f.property
    let f : IncidentEdge G v := ⟨e.val, hv⟩
    exact ⟨f, (incident_edgesThrough_iff G σ v f).mp e.property.1⟩
  invFun e := ⟨e.val.val,
    (incident_edgesThrough_iff G σ v e.val).mpr e.property,
    incident_not_edgesBefore G σ v e.val⟩
  left_inv e := rfl
  right_inv e := rfl

/-- Every edge appearing at this step is an actual star edge to a
preceding neighbor, and every such edge appears at this step. -/
theorem card_prefixEdges_step (G : SimpleGraph V) (σ : Outcome V) (v : V) :
    Fintype.card (Edge (prefixGraph G σ ((σ v).val + 1))) =
      Fintype.card (Edge (prefixGraph G σ (σ v).val)) + precedingIncidentCount G σ v := by
  have hbefore := Fintype.card_congr
    (subgraphEdgeEquiv (prefixGraph_le G σ (σ v).val))
  rw [subgraphEdgeSet_prefix_before] at hbefore
  have hthrough := Fintype.card_congr
    (subgraphEdgeEquiv (prefixGraph_le G σ ((σ v).val + 1)))
  rw [subgraphEdgeSet_prefix_through] at hthrough
  have hsplit := Fintype.card_congr
    (Equiv.Set.sumDiffSubset (edgesBefore_subset_edgesThrough G σ v))
  rw [Fintype.card_sum] at hsplit
  have hnew := Fintype.card_congr (newPrefixEdgeEquiv G σ v)
  have hnew' : Fintype.card ↥(edgesThrough G σ v \ edgesBefore G σ v) =
      precedingIncidentCount G σ v := by
    exact hnew.trans (Fintype.card_subtype
      (fun e : IncidentEdge G v => σ (incidentOther G v e) < σ v))
  omega

/-- Exact decomposition of a rank contribution into the expected new
edges and the expected dimension of the actual new stresses. -/
theorem rankContribution_eq_degree_half_sub_stress
    (G : SimpleGraph V) (p : Placement V 3) (hp : IsGenericPlacement p) (v : V) :
    rankContribution G v = (G.degree v : ℝ) / 2 -
      stressDimensionContribution G (StressSpace G p) v := by
  have hpoint (σ : Outcome V) :
      ((genericRigidityRank (prefixGraph G σ ((σ v).val + 1)) 3 : ℝ) -
        genericRigidityRank (prefixGraph G σ (σ v).val) 3) =
      (precedingIncidentCount G σ v : ℝ) -
        ((Module.finrank ℝ (stressThrough G (StressSpace G p) σ v) : ℝ) -
          Module.finrank ℝ (stressBefore G (StressSpace G p) σ v)) := by
    obtain ⟨hbefore, hthrough⟩ := prefix_rank_stress_identities G p σ v
    have hcard := card_prefixEdges_step G σ v
    rw [hp] at hbefore hthrough
    have hbefore' := congrArg (fun n : ℕ => (n : ℝ)) hbefore
    have hthrough' := congrArg (fun n : ℕ => (n : ℝ)) hthrough
    have hcard' := congrArg (fun n : ℕ => (n : ℝ)) hcard
    push_cast at hbefore' hthrough' hcard'
    linarith
  unfold rankContribution
  rw [mean_congr _ _ hpoint, mean_sub, mean_precedingIncidentCount,
    card_incidentEdge_eq_degree]
  rfl

/-- Corollary 2.2's numerical bound, first stated with the literal full
star-image dimension.  Its identification with `degree - deletionRankDrop`
is a separate exact-sequence calculation. -/
theorem rankContribution_ge_degree_half_sub_bound_star
    (G : SimpleGraph V) (p : Placement V 3) (hp : IsGenericPlacement p)
    (hgeom : GeneralPosition.InGeneralPosition p) (v : V) :
    (G.degree v : ℝ) / 2 - bound 4 (Module.finrank ℝ (stressStarCode G v (StressSpace G p))) ≤
      rankContribution G v := by
  rw [rankContribution_eq_degree_half_sub_stress G p hp v]
  exact sub_le_sub_left
    (corollary_two_two_subspace G p hgeom v (StressSpace G p) le_rfl) _

end
end Papers.Rigidity.BarJoint

end
end BundleSource0049

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/Consolidated_RigidityCombined03/block_0049/Consolidated/RigidityCombined03.olean" record ".lake/reports/audit/checkpoints/Consolidated_RigidityCombined03/checkpoint_0049.json"
