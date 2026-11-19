module
prelude

public import RawLeafCertificate
public import GrowthRenaming

@[expose] public section

/-!
# Reusing a complete growth forest at a smaller facet budget

Coverage is monotone in the upper quota. Leaf dispositions are not: a leaf
which fails the larger exact quota may meet the smaller one. Consequently a
transfer checks a new route for every larger-forest leaf. It either proves a
failure of the smaller quota or identifies exactly an ordered leaf whose
smaller-quota disposition has already been checked.
-/

namespace Papers.RationalityTen.QuotaLeafTransfer

open ConcreteGrowth RawLeafCertificate

inductive Route where
  | quota (kind : Nat)
  | reuse (index : Nat)
  deriving Inhabited

def certificate (oldCertificates : Nat → Certificate) : Route → Certificate
  | .quota kind => .quota kind
  | .reuse index => oldCertificates index

def routeCheck (quota : Nat → Nat) (cells : Nat → Cell)
    (oldLeaves : Nat → List Nat) (oldCount : Nat) (leaf : List Nat) : Route → Bool
  | .quota kind => RawClosedLeafData.quotaFailure (leaf.map cells) kind (quota kind)
  | .reuse index => decide (index < oldCount) && decide (leaf = oldLeaves index)

theorem routeCheck_sound (quota : Nat → Nat) (cells : Nat → Cell)
    (oldLeaves : Nat → List Nat) (oldCount : Nat)
    (oldCertificates : Nat → Certificate)
    (oldChecked : ∀ j, j < oldCount →
      RawLeafCertificate.check quota ((oldLeaves j).map cells) (oldCertificates j) = true)
    (leaf : List Nat) (route : Route)
    (h : routeCheck quota cells oldLeaves oldCount leaf route = true) :
    RawLeafCertificate.check quota (leaf.map cells) (certificate oldCertificates route) = true := by
  cases route with
  | quota kind => exact h
  | reuse index =>
    obtain ⟨hindex, hleaf⟩ := Bool.and_eq_true_iff.mp h
    have hindex' : index < oldCount := of_decide_eq_true hindex
    have hleaf' : leaf = oldLeaves index := of_decide_eq_true hleaf
    change RawLeafCertificate.check quota (leaf.map cells) (oldCertificates index) = true
    rw [hleaf']
    exact oldChecked index hindex'

theorem target_mono {n r : Nat} {ridges : Fin n → Fin r → Bool}
    {compatible : Fin n → Fin n → Bool} {kind : Fin n → Nat}
    {smallQuota largeQuota : Nat → Nat} {B : List (Fin n)}
    (h : GrowthRenaming.Target ridges compatible kind smallQuota B)
    (hquota : ∀ k, smallQuota k ≤ largeQuota k) :
    GrowthRenaming.Target ridges compatible kind largeQuota B :=
  { h with budget := fun k => Nat.le_trans (h.budget k) (hquota k) }

#print axioms routeCheck_sound
#print axioms target_mono

end Papers.RationalityTen.QuotaLeafTransfer
