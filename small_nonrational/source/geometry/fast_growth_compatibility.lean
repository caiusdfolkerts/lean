module
prelude
public import FiniteChecks

@[expose] public section

/-!
# Checked face-membership caches

The cache must contain every listed edge and ridge. It may contain extra
members: those only enlarge the search. Thus a false cached compatibility test
is a sound rejection for the original literal cells. Singletons and the empty
face are tested directly, and shared-face edge equality is still computed from
the literal edge lists.
-/

namespace Papers.RationalityTen.ConcreteGrowth

def bitAt (bits index : Nat) : Bool := decide ((bits / 2^index) % 2 = 1)

def faceCacheCheck (cell : Cell) (bits : Nat) : Bool :=
  cell.edges.all (bitAt bits) && cell.ridgeMasks.all (bitAt bits)

def fastProper (bits mask : Nat) : Bool :=
  decide (Nat.land mask (mask - 1) = 0) || bitAt bits mask

theorem fastProper_of_proper (cell : Cell) (bits mask : Nat)
    (hcache : faceCacheCheck cell bits = true) (hproper : proper cell mask = true) :
    fastProper bits mask = true := by
  obtain ⟨hedges, hridges⟩ := Bool.and_eq_true_iff.mp hcache
  apply Bool.or_eq_true_iff.mpr
  obtain hsmall | hridge := Bool.or_eq_true_iff.mp hproper
  · obtain hsmall | hedge := Bool.or_eq_true_iff.mp hsmall
    · exact Or.inl hsmall
    · obtain ⟨e, he, heq⟩ := List.any_eq_true.mp hedge
      have heq' : e = mask := of_decide_eq_true heq
      exact Or.inr (heq' ▸ List.all_eq_true.mp hedges e he)
  · obtain ⟨q, hq, heq⟩ := List.any_eq_true.mp hridge
    have heq' : q = mask := of_decide_eq_true heq
    exact Or.inr (heq' ▸ List.all_eq_true.mp hridges q hq)

def fastCompatible (a b : Cell) (aFaces bFaces : Nat) : Bool :=
  let common := Nat.land a.vertices b.vertices
  (fastProper aFaces common && fastProper bFaces common) &&
    decide ((a.edges.filter fun e => decide (Nat.land e common = e)) =
            (b.edges.filter fun e => decide (Nat.land e common = e)))

theorem fastCompatible_of_compatible (a b : Cell) (aFaces bFaces : Nat)
    (ha : faceCacheCheck a aFaces = true) (hb : faceCacheCheck b bFaces = true)
    (hab : compatible a b = true) : fastCompatible a b aFaces bFaces = true := by
  obtain ⟨hproper, hedges⟩ := Bool.and_eq_true_iff.mp hab
  obtain ⟨hap, hbp⟩ := Bool.and_eq_true_iff.mp hproper
  exact Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr
    ⟨fastProper_of_proper a aFaces _ ha hap,
     fastProper_of_proper b bFaces _ hb hbp⟩, hedges⟩

#print axioms fastCompatible_of_compatible

end Papers.RationalityTen.ConcreteGrowth
