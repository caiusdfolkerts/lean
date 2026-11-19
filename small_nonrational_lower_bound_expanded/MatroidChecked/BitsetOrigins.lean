module
public import MatroidChecked.BitsetSemanticChecks

@[expose] public section
noncomputable section

/-!
# Exact bit-set checking of excluded-model clauses

An excluded-model clause lists one literal for each new basis coordinate.
Checking this by repeated list membership builds unnecessarily large reduction
traces.  The finite lists below are compared by the bit sets of their literal
codes.  The comparison is proved equivalent to inclusion for arbitrary lists,
so no bound, ordering, uniqueness, or completeness premise is hidden in the
computational representation.
-/

namespace Papers.RationalityTen.MatroidChecked.BitsetOrigins

open BasisExtensionCNF FastSemanticChecks BitsetSemanticChecks

theorem familyCode_and_eq_iff (L M : List ℕ) :
    familyCode L &&& familyCode M = familyCode L ↔ ∀ i ∈ L, i ∈ M := by
  constructor
  · intro h i hi
    have hb := congrArg (fun n : ℕ => n.testBit i) h
    rw [Nat.testBit_and, (familyCode_testBit L i).2 hi] at hb
    apply (familyCode_testBit M i).1
    simpa only [Bool.true_and] using hb
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and]
    cases hl : (familyCode L).testBit i with
    | false => simp
    | true =>
      have hm := (familyCode_testBit M i).2 (h i ((familyCode_testBit L i).1 hl))
      simp [hm]

def literalCode : Sat.Literal → ℕ
  | .pos i => 2 * i
  | .neg i => 2 * i + 1

theorem literalCode_injective : Function.Injective literalCode := by
  intro a b h
  cases a with
  | pos i =>
    cases b with
    | pos j =>
      have hij : i = j := by simp only [literalCode] at h; omega
      exact congrArg Sat.Literal.pos hij
    | neg j => simp only [literalCode] at h; omega
  | neg i =>
    cases b with
    | pos j => simp only [literalCode] at h; omega
    | neg j =>
      have hij : i = j := by simp only [literalCode] at h; omega
      exact congrArg Sat.Literal.neg hij

def clauseCode (c : List Sat.Literal) : ℕ :=
  familyCode (c.map literalCode)

theorem clauseCode_and_eq_iff (c d : List Sat.Literal) :
    clauseCode c &&& clauseCode d = clauseCode c ↔ ∀ z ∈ c, z ∈ d := by
  rw [clauseCode, clauseCode, familyCode_and_eq_iff]
  constructor
  · intro h z hz
    obtain ⟨w, hw, hcode⟩ := List.mem_map.mp (h (literalCode z) (List.mem_map.mpr ⟨z,hz,rfl⟩))
    exact literalCode_injective hcode ▸ hw
  · intro h i hi
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hi
    exact List.mem_map.mpr ⟨z,h z hz,rfl⟩

def excludedClause {k t : ℕ} (newIndex : Fin t → Fin k) (model : ℕ) :
    List Sat.Literal :=
  (List.finRange t).map fun j =>
    if model.testBit j.val then .neg (newIndex j).val else .pos (newIndex j).val

theorem excludedClause_subset_iff {k t : ℕ} (newIndex : Fin t → Fin k)
    (model : ℕ) (c : List Sat.Literal) :
    (∀ z ∈ excludedClause newIndex model, z ∈ c) ↔
      ∀ j : Fin t,
        (if model.testBit j.val then Sat.Literal.neg (newIndex j).val
          else Sat.Literal.pos (newIndex j).val) ∈ c := by
  simp only [excludedClause, List.mem_map, List.mem_finRange, true_and,
    forall_exists_index, forall_apply_eq_imp_iff]

def BitsetOrigin {k t l : ℕ} (U : Fin k → Finset (Fin 8)) (e : Fin 8)
    (old : Finset (Finset (Fin 8))) (newIndex : Fin t → Fin k)
    (models : Fin l → ℕ) : Origin k l → List Sat.Literal → Prop
  | .excluded w, c =>
      clauseCode (excludedClause newIndex (models w)) &&& clauseCode c =
        clauseCode (excludedClause newIndex (models w))
  | .exchange a b x, c => FastOrigin U e old newIndex models (.exchange a b x) c
  | .fixed i, c => FastOrigin U e old newIndex models (.fixed i) c
  | .newPoint, c => FastOrigin U e old newIndex models .newPoint c

instance {k t l : ℕ} (U : Fin k → Finset (Fin 8)) (e : Fin 8)
    (old : Finset (Finset (Fin 8))) (newIndex : Fin t → Fin k)
    (models : Fin l → ℕ) (o : Origin k l) (c : List Sat.Literal) :
    Decidable (BitsetOrigin U e old newIndex models o c) := by
  cases o <;> unfold BitsetOrigin <;> infer_instance

theorem bitsetOrigin_iff {k t l : ℕ} (U : Fin k → Finset (Fin 8)) (e : Fin 8)
    (old : Finset (Finset (Fin 8))) (newIndex : Fin t → Fin k)
    (models : Fin l → ℕ) (o : Origin k l) (c : List Sat.Literal) :
    BitsetOrigin U e old newIndex models o c ↔ FastOrigin U e old newIndex models o c := by
  cases o with
  | fixed i => rfl
  | exchange a b x => rfl
  | newPoint => rfl
  | excluded w =>
    exact (clauseCode_and_eq_iff _ _).trans (excludedClause_subset_iff newIndex (models w) c)

theorem bitsetOrigin_sound {k t l : ℕ} (U : Fin k → Finset (Fin 8)) (e : Fin 8)
    (old : Finset (Finset (Fin 8))) (newIndex : Fin t → Fin k)
    (models : Fin l → ℕ) (o : Origin k l) (c : List Sat.Literal)
    (h : BitsetOrigin U e old newIndex models o c) :
    ValidOrigin U e old newIndex models o c :=
  fastOrigin_sound U e old newIndex models o c ((bitsetOrigin_iff U e old newIndex models o c).1 h)

theorem bitsetOrigins_sound {k t l : ℕ} (U : Fin k → Finset (Fin 8)) (e : Fin 8)
    (old : Finset (Finset (Fin 8))) (newIndex : Fin t → Fin k)
    (models : Fin l → ℕ) (cs : List (Origin k l × List Sat.Literal))
    (h : ∀ oc ∈ cs, BitsetOrigin U e old newIndex models oc.1 oc.2) :
    ∀ oc ∈ cs, ValidOrigin U e old newIndex models oc.1 oc.2 := by
  intro oc hoc
  exact bitsetOrigin_sound U e old newIndex models oc.1 oc.2 (h oc hoc)

end Papers.RationalityTen.MatroidChecked.BitsetOrigins
