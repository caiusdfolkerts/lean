module
public import Papers.FiniteProjectionData

@[expose] public section

/-!
# Decidable finite checks for projection certificates

These predicates search only finite sets of supplied face masks and
retained nodes. A proof obtained by `decide` is checked by the Lean kernel.
The soundness lemmas convert each successful check into geometric
certificate constructors; no native-decide axiom is used.


-/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection

variable {n c : ℕ}

/-- A normalized finite-set literal. Its distinctness is proved in the kernel. -/
def literalFinset {α : Type*} (xs : List α) (h : xs.Nodup) : Finset α := ⟨xs, h⟩

@[simp] theorem mem_literalFinset {α : Type*} (xs : List α) (h : xs.Nodup) (a : α) :
    a ∈ literalFinset xs h ↔ a ∈ xs := Iff.rfl

def PointRuleValid (B : Boundary n) (S : Finset (Fin n)) : Prop :=
  S.card ≤ 2 ∨
  (S.card ≤ 3 ∧ ∃ R : B.polygons, 0 ∉ R.val ∧ ∀ i : S, i.val.succ ∈ R.val) ∨
  (S.card ≤ 3 ∧ ∃ R : B.polygons, 0 ∈ R.val ∧ ∃ v : S,
    v.val.succ ∉ R.val ∧ ∀ i : S, i ≠ v → i.val.succ ∈ R.val)

def PlanePairValid {B : Boundary n} (p q : PlaneNode B) : Prop :=
  (p.val.1 = false ∧ q.val.1 = false ∧ p ≠ q) ∨
  (p.val.1 = true ∧ q.val.1 = false) ∨
  (p.val.1 = false ∧ q.val.1 = true) ∨
  ∃ F : B.facets, 0 ∉ F.val ∧
    F.val ∩ carrier p ∈ B.polygons ∧ F.val ∩ carrier q ∈ B.polygons ∧
    F.val ∩ carrier p ≠ F.val ∩ carrier q

def PlaneRuleValid (B : Boundary n) (S : Finset (PlaneNode B)) : Prop :=
  S.card ≤ 1 ∨
  (S.card ≤ 2 ∧ ∀ p q : S, p ≠ q → PlanePairValid p.val q.val) ∨
  (S.card ≤ 3 ∧ ∀ p : S, p.val.val.1 = false) ∨
  (S.card ≤ 3 ∧ ∃ F : B.facets, 0 ∉ F.val ∧
    (∀ p : S, F.val ∩ carrier p.val ∈ B.polygons) ∧
    Function.Injective (fun p : S => F.val ∩ carrier p.val)) ∨
  (∃ p q r : S, r.val.val.1 = false ∧ PlanePairValid p.val q.val ∧
    ∃ w : Fin n, incidence w p.val ∧ incidence w q.val ∧ ¬ incidence w r.val ∧
      S ⊆ {p.val, q.val, r.val})

instance (B : Boundary n) (S : Finset (Fin n)) : Decidable (PointRuleValid B S) := by
  unfold PointRuleValid
  infer_instance

instance {B : Boundary n} (p q : PlaneNode B) : Decidable (PlanePairValid p q) := by
  unfold PlanePairValid
  infer_instance

instance (B : Boundary n) (S : Finset (PlaneNode B)) : Decidable (PlaneRuleValid B S) := by
  haveI (p q : S) : Decidable (p ≠ q → PlanePairValid p.val q.val) := inferInstance
  haveI (F : B.facets) : Decidable
      (Function.Injective (fun p : S => F.val ∩ carrier p.val)) := by
    unfold Function.Injective
    infer_instance
  haveI (p q r : S) : Decidable
      (∃ w : Fin n, incidence w p.val ∧ incidence w q.val ∧ ¬incidence w r.val ∧
        S ⊆ {p.val, q.val, r.val}) := by
    unfold incidence
    infer_instance
  unfold PlaneRuleValid
  infer_instance

theorem pointRule_of_valid (B : Boundary n) (S : Finset (Fin n))
    (h : PointRuleValid B S) : PointRule B S := by
  rcases h with hc | ⟨hc, R, ha, hmem⟩ | ⟨hc, R, ha, v, hout, hin⟩
  · exact .atMostTwo hc
  · exact .avoidingPolygon hc R ha (fun i hi => hmem ⟨i, hi⟩)
  · exact .facialWitness hc R ha v.val v.property hout
      (fun i hi hiv => hin ⟨i, hi⟩ (fun heq => hiv (congrArg Subtype.val heq)))

theorem planePairRule_of_valid {B : Boundary n} (p q : PlaneNode B)
    (h : PlanePairValid p q) : PlanePairRule p q := by
  rcases h with ⟨hp, hq, hne⟩ | ⟨hp, hq⟩ | ⟨hp, hq⟩ | ⟨F, ha, hp, hq, hne⟩
  · exact .ordinary p q hp hq hne
  · exact .extraOrdinary p q hp hq
  · exact .ordinaryExtra p q hp hq
  · exact .commonFacet p q F ha ⟨F.val ∩ carrier p, hp⟩ ⟨F.val ∩ carrier q, hq⟩
      rfl rfl (fun heq => hne (congrArg Subtype.val heq))

theorem planeRule_of_valid (B : Boundary n) (S : Finset (PlaneNode B))
    (h : PlaneRuleValid B S) : PlaneRule B S := by
  rcases h with hc | ⟨hc, hpairs⟩ | ⟨hc, hord⟩ | ⟨hc, F, ha, htrace, hinj⟩ |
    ⟨p, q, r, hr, hpq, w, hwp, hwq, hwr, hsub⟩
  · exact .atMostOne hc
  · apply PlaneRule.atMostTwo hc
    intro p hp q hq hpq
    exact planePairRule_of_valid p q
      (hpairs ⟨p, hp⟩ ⟨q, hq⟩ (fun heq => hpq (congrArg Subtype.val heq)))
  · exact .ordinary hc (fun p hp => hord ⟨p, hp⟩)
  · let R : S → B.polygons := fun p => ⟨F.val ∩ carrier p.val, htrace p⟩
    exact .commonFacet hc F ha R
      (fun p q heq => hinj (congrArg Subtype.val heq)) (fun _ => rfl)
  · exact .commonPoint p.val q.val r.val hr w (planePairRule_of_valid _ _ hpq)
      hwp hwq hwr hsub

def incidenceCertificateOfChecks (B : Boundary n) (priority : Node B → ℕ)
    (hinj : Function.Injective priority)
    (hplane : ∀ p, PointRuleValid B (retainedPoints priority p))
    (hpoint : ∀ i, PlaneRuleValid B (retainedPlanes priority i)) : IncidenceCertificate B where
  priority := priority
  injective := hinj
  plane_rule p := pointRule_of_valid B _ (hplane p)
  point_rule i := planeRule_of_valid B _ (hpoint i)

def FrameValid (B : Boundary n) {k : ℕ} (b : Fin k → Fin n) : Prop :=
  Function.Injective b ∧
  ((k ≤ 3 ∧ ∃ R : B.polygons, 0 ∉ R.val ∧ ∀ j, (b j).succ ∈ R.val) ∨
    (k ≤ 4 ∧ ∃ F : B.facets, 0 ∉ F.val ∧ (∀ j, (b j).succ ∈ F.val) ∧
      ∃ R : B.polygons, ∃ t : Fin k, (b t).succ ∉ R.val ∧
        ∀ j, j ≠ t → (b j).succ ∈ R.val))

instance (B : Boundary n) {k : ℕ} (b : Fin k → Fin n) : Decidable (FrameValid B b) := by
  unfold FrameValid
  infer_instance

theorem frameCertificate_of_valid (B : Boundary n) {k : ℕ} (b : Fin k → Fin n)
    (h : FrameValid B b) : FrameCertificate B b := by
  obtain ⟨hinj, hp | hf⟩ := h
  · obtain ⟨hk, R, ha, hmem⟩ := hp
    exact .polygon hk hinj R ha hmem
  · obtain ⟨hk, F, ha, hmem, R, t, hout, hin⟩ := hf
    exact .facial hk hinj R F ha hmem t hout hin

def heightCertificateOfChecks (B : Boundary n) (rows : Fin c → HeightRow B)
    (pivot : Fin c → Fin n)
    (hpivot : ∀ i, pivot i = (rows i).vertex ∨
      ∃ j : Fin (rows i).frameSize, pivot i = (rows i).frame j ∧
        FrameValid B (Function.update (rows i).frame j (rows i).vertex))
    (hlater : ∀ i j, i < j → pivot i ≠ (rows j).vertex ∧
      pivot i ∉ Set.range (rows j).frame) : HeightCertificate B c where
  rows := rows
  pivot := pivot
  pivot_certificate i := by
    rcases hpivot i with hi | ⟨j, hij, hframe⟩
    · exact Or.inl hi
    · exact Or.inr ⟨j, hij, frameCertificate_of_valid B _ hframe⟩
  later_absent := hlater

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection
