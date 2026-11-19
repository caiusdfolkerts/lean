module
prelude
public import FacetSatCoverage
public import PackedGraphInputs

@[expose] public section

/-!
# Reusing the existing graph metadata for SAT coverage

The SAT projection keeps the original candidate indices, cells, proper-face
cache and ridge matrix.  Only its compact vertex and kind columns are new.
Their pointwise equality check is sufficient to transport every original
graph target to the local boundary used by the SAT certificate.  In
particular, this adapter does not repeat either global candidate coverage
or the already checked ridge-incidence matrix calculation.
-/

namespace Papers.RationalityTen.FacetSat.RawProjection

open ConcreteGrowth GrowthDAG SparseGrowthDAG GrowthPruning
open PackedGraphCertificate

def data (R : RawData) (vertices kinds : Fields) : FacetSat.Data where
  count := R.n
  embedding := R.embedding
  vertices := vertices
  faces := R.faceMasks
  kinds := kinds
  cellCodes := R.cells
  ridgeMatrix := R.candidateMatrix

def check (R : RawData) (vertices kinds : Fields) : Bool :=
  (List.finRange R.n).all fun c =>
    decide (vertices.get c.val = (R.data.cells c).vertices) &&
      decide (kinds.get c.val = (R.data.cells c).kind)

theorem vertices_eq (R : RawData) (vertices kinds : Fields)
    (hcheck : check R vertices kinds = true) (c : Fin R.n) :
    vertices.get c.val = (R.data.cells c).vertices :=
  of_decide_eq_true (Bool.and_eq_true_iff.mp
    (List.all_eq_true.mp hcheck c (List.mem_finRange c))).1

theorem kind_eq (R : RawData) (vertices kinds : Fields)
    (hcheck : check R vertices kinds = true) (c : Fin R.n) :
    (data R vertices kinds).toData.kind c = R.data.kind c :=
  of_decide_eq_true (Bool.and_eq_true_iff.mp
    (List.all_eq_true.mp hcheck c (List.mem_finRange c))).2

theorem ridge_matrix (R : RawData) (vertices kinds : Fields)
    (h : MatrixGraphProblem.Checked R.data) :
    (data R vertices kinds).ridgeMatrix =
      PackedIncidenceMatrix.code (ridgeList (data R vertices kinds).cells) :=
  h.candidateMatrix

/-- The candidate kinds are checked once for the entire certificate. -/
def kindKeysCheck {n : Nat} (kind : Fin n → Nat) (keys : List Nat) : Bool :=
  (List.finRange n).all fun c => decide (kind c ∈ keys)

/-- Count a leaf once per distinct kind, rather than once per candidate. -/
def leafCountsCheck {n : Nat} (kind : Fin n → Nat) (quota : Nat → Nat)
    (keys : List Nat) (leaf : List (Fin n)) : Bool :=
  decide leaf.Nodup && keys.all fun key => decide (kindCount kind leaf key = quota key)

theorem leafCheck_of_counts {n : Nat} (kind : Fin n → Nat) (quota : Nat → Nat)
    (keys : List Nat) (leaf : List (Fin n))
    (hkeys : kindKeysCheck kind keys = true)
    (hcounts : leafCountsCheck kind quota keys leaf = true) :
    Boundary.leafCheck kind quota leaf = true := by
  obtain ⟨hnodup, hcounts⟩ := Bool.and_eq_true_iff.mp hcounts
  apply Bool.and_eq_true_iff.mpr
  refine ⟨hnodup, List.all_eq_true.mpr ?_⟩
  intro c hc
  have hk : kind c ∈ keys := of_decide_eq_true
    (List.all_eq_true.mp hkeys c (List.mem_finRange c))
  exact List.all_eq_true.mp hcounts (kind c) hk

/-- Completeness and distinctness of a kind list follow structurally from
filtering the finite candidate range; no quadratic membership check is needed. -/
theorem kindListCheck_enumerated {n : Nat} (kind : Fin n → Nat) (key : Nat) :
    Boundary.kindListCheck kind key
      ((List.finRange n).filter fun c => decide (kind c = key)) = true := by
  have hn : (List.finRange n).Nodup := by
    apply List.pairwise_iff_getElem.mpr
    intro i j hi hj hij heq
    rw [List.getElem_finRange, List.getElem_finRange] at heq
    exact Nat.ne_of_lt hij (congrArg Fin.val heq)
  apply Bool.and_eq_true_iff.mpr
  refine ⟨decide_eq_true (List.Pairwise.filter _ hn), List.all_eq_true.mpr ?_⟩
  intro c hc
  apply decide_eq_true
  simp only [List.mem_filter, List.mem_finRange, decide_eq_true_eq, true_and]

/-- The original target supplies all local clauses.  Extra graph incidence,
edge-cover and missing-edge conditions remain available to later refinements;
this necessary-condition projection does not assume them away. -/
theorem boundary_of_target (R : RawData)
    (valid : GraphGrowthInputs.Valid R.inputs)
    (checked : MatrixGraphProblem.Checked R.data)
    (vertices kinds : Fields) (hcheck : check R vertices kinds = true)
    (B : List (Fin R.n))
    (H : GraphGrowthConstraints.Target (R.inputs.problem valid) B) :
    Boundary (data R vertices kinds).toData.kind
      (data R vertices kinds).toData.relation
      (data R vertices kinds).ridges R.data.quota B := by
  refine ⟨H.nodup, ?_, ?_, ?_, ?_⟩
  · intro a ha b hb hab
    have hcompat := H.boundary.pairwise a b ha hb hab
    have hface := FaceOnlyCompatibility.necessary
      (R.data.cells a) (R.data.cells b)
      (R.data.faceMasks a) (R.data.faceMasks b)
      (checked.cellFacts a).2.1 (checked.cellFacts b).2.1 hcompat
    change FaceOnlyCompatibility.proper (R.faceMasks.get a.val)
        (Nat.land (vertices.get a.val) (vertices.get b.val)) &&
      FaceOnlyCompatibility.proper (R.faceMasks.get b.val)
        (Nat.land (vertices.get a.val) (vertices.get b.val)) = true
    rw [vertices_eq R vertices kinds hcheck a,
      vertices_eq R vertices kinds hcheck b]
    exact hface
  · intro j
    have hk : (data R vertices kinds).toData.kind = R.data.kind :=
      funext (kind_eq R vertices kinds hcheck)
    rw [hk]
    by_cases hj : j < R.k
    · exact H.exactQuota ⟨j, hj⟩
    · have hempty : (B.filter fun c => decide (R.data.kind c = j)) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro c hc
        have hlt := valid.kind_lt c
        have hne : R.data.kind c ≠ j := by
          intro heq
          exact hj (heq ▸ hlt)
        intro heq
        exact hne (of_decide_eq_true heq)
      change kindCount R.data.kind B j = if j < R.k then R.quota.get j else 0
      rw [ite_eq_right hj, kindCount, hempty]
      rfl
  · intro q a ha haq
    have hinc : Incident (fun c => has ((R.inputs.problem valid).ridgeList c))
        (family B) q a := ⟨(has_true B a).mpr ha, haq⟩
    obtain ⟨b, hb, hba⟩ := H.boundary.mates q a hinc
    exact ⟨b, (has_true B b).mp hb.1, hb.2, hba⟩
  · intro q a b c ha hb hc haq hbq hcq
    exact H.boundary.no_three q a b c
      ⟨(has_true B a).mpr ha, haq⟩
      ⟨(has_true B b).mpr hb, hbq⟩
      ⟨(has_true B c).mpr hc, hcq⟩

/-- A refutation with leaf blockers gives direct catalogue coverage of the
original graph target, with no growth-node replay. -/
theorem coverage (R : RawData)
    (valid : GraphGrowthInputs.Valid R.inputs)
    (checked : MatrixGraphProblem.Checked R.data)
    (vertices kinds : Fields) (hcheck : check R vertices kinds = true)
    {l : Nat} (leaves : Fin l → List (Fin R.n))
    (hunsat : ∀ B, Boundary (data R vertices kinds).toData.kind
      (data R vertices kinds).toData.relation
      (data R vertices kinds).ridges R.data.quota B →
      (∀ j, ¬Same (family (leaves j)) (family B)) → False)
    (B : List (Fin R.n))
    (H : GraphGrowthConstraints.Target (R.inputs.problem valid) B) :
    ∃ j, Same (family (leaves j)) (family B) :=
  coverage_of_unsat _ _ _ _ leaves hunsat B
    (boundary_of_target R valid checked vertices kinds hcheck B H)

#print axioms boundary_of_target
#print axioms coverage

end Papers.RationalityTen.FacetSat.RawProjection
