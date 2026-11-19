module
prelude
public import RawFaceNormalizers

@[expose] public section

namespace Papers.RationalityTen.RawKindedFacePlacement

/-- The stronger placement check retains the prescribed facet kind as well
as all geometric faces. This supplies exact type quotas downstream. -/
def check {n : Nat} (size : Nat) (B : RawFacePlacement.Block)
    (template root : ConcreteGrowth.Cell) (cells : Fin n → ConcreteGrowth.Cell)
    (inner outer : Nat) (witness : Fin n) : Bool :=
  let placed := RawFacetEmbedding.mapCell size (RawFacePlacement.label size B inner outer) template
  (!RawFacePlacement.compatible placed root) ||
    (decide ((cells witness).kind = template.kind) &&
      RawFacetEmbedding.sameGeometry (cells witness) placed)

def intervalCheck {n : Nat} (size : Nat) (B : RawFacePlacement.Block)
    (template root : ConcreteGrowth.Cell) (cells : Fin n → ConcreteGrowth.Cell)
    (witness : Nat → Fin n) (code : Nat) : Bool :=
  let width := RawFacePlacement.count B.outside (size - B.shared)
  check size B template root cells (code / width) (code % width) (witness code)

theorem check_of_interval {m n : Nat} (raw : RawFacePlacement.Block)
    (template root : ConcreteGrowth.Cell) (cells : Fin n → ConcreteGrowth.Cell)
    (witness : Nat → Fin n)
    (h : FiniteChecks.Interval (intervalCheck m raw template root cells witness)
      0 (RawFacePlacement.count raw.shared raw.shared *
        RawFacePlacement.count raw.outside (m - raw.shared)))
    (inner outer : Nat) (hi : inner < RawFacePlacement.count raw.shared raw.shared)
    (ho : outer < RawFacePlacement.count raw.outside (m - raw.shared)) :
    check m raw template root cells inner outer
      (witness (outer + RawFacePlacement.count raw.outside (m - raw.shared) * inner)) = true := by
  let width := RawFacePlacement.count raw.outside (m - raw.shared)
  have hwidth : 0 < width := Nat.zero_lt_of_lt ho
  have hcode : outer + width * inner <
      RawFacePlacement.count raw.shared raw.shared * width := by
    calc
      _ < width + width * inner := Nat.add_lt_add_right ho _
      _ = (inner + 1) * width := by
        simp only [Nat.add_mul, Nat.one_mul, Nat.mul_comm, Nat.add_comm]
      _ ≤ _ := Nat.mul_le_mul_right width (Nat.succ_le_of_lt hi)
  have hc := h (outer + width * inner) (Nat.zero_le _) hcode
  simpa only [intervalCheck, width,
    Nat.add_mul_div_left _ _ hwidth, Nat.div_eq_of_lt ho, Nat.zero_add,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ho] using hc

end Papers.RationalityTen.RawKindedFacePlacement
