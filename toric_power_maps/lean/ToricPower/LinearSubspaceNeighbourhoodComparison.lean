module

public import ToricPower.LinearSubspaceNeighbourhood

/-!
# The neighbourhood restriction is the original linear restriction

Restricting the same-lattice neighbourhood fan to `W` gives exactly the
original saturated-trace fan. The composite fan morphism back to the
original fan agrees with the original inclusion after this proved source
equality. The final transport lemma applies to any proposition built from
the actual fan morphism, including cohomology of its actual pullback.

Using equality of the source fans avoids an unrelated comparison theorem
for sheaf cohomology on isomorphic schemes.
-/

@[expose] public noncomputable section

open TauCeti.Toric

namespace ToricPower

universe u

variable {N : Type u} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V}

/-- The two restricted fans have the same actual cones in the same
saturated lattice, hence are equal as fans. -/
theorem linearAmbient_restrictedFan_eq (fan : Fan i) (W : Submodule ℝ V)
    (rational : IsRationalSubspace i W) :
    restrictedFan (linearAmbientFan fan W) W rational = restrictedFan fan W rational := by
  apply Fan.ext
  ext σ
  rw [mem_restrictedFan_cones, mem_restrictedFan_cones]
  constructor
  · rintro ⟨τ, hτ, hτW, rfl⟩
    exact ⟨τ, hτ.1, hτW, rfl⟩
  · rintro ⟨τ, hτ, hτW, rfl⟩
    exact ⟨τ, ⟨hτ, hτW⟩, hτW, rfl⟩

section SourceTransport

variable {N' : Type u} {V' : Type*} [AddCommGroup N'] [AddCommGroup V']
  [Module ℝ V'] {i' : N' →+ V'}

/-- Transport of a fan morphism along equality of its source fan. -/
def fanHomTransportSource {source other : Fan i} {target : Fan i'}
    (same : source = other) (f : FanHom source target) : FanHom other target :=
  same ▸ f

@[simp]
theorem fanHomTransportSource_latticeMap {source other : Fan i} {target : Fan i'}
    (same : source = other) (f : FanHom source target) :
    (fanHomTransportSource same f).latticeMap = f.latticeMap := by
  subst other
  rfl

/-- Every proposition about the genuine map transports by the proved
source equality. No new categorical or cohomological assertion is assumed. -/
theorem fanHomTransportSource_predicate {source other : Fan i} {target : Fan i'}
    (same : source = other) (f : FanHom source target)
    (P : ∀ source : Fan i, FanHom source target → Prop) :
    P source f ↔ P other (fanHomTransportSource same f) := by
  subst other
  rfl

end SourceTransport

/-- The two-stage inclusion through the actual open neighbourhood. -/
def linearAmbientRestrictedComposite (fan : Fan i) (W : Submodule ℝ V)
    (rational : IsRationalSubspace i W) :
    FanHom (restrictedFan (linearAmbientFan fan W) W rational) fan :=
  (subfanFanHom (linearAmbientFan fan W) fan (fun _ h => h.1)).comp
    (restrictedFanInclusion (linearAmbientFan fan W) W rational)

/-- After the exact source identification, the composite is the original
linear inclusion, as an equality of fan morphisms. -/
theorem linearAmbientRestrictedComposite_transport (fan : Fan i) (W : Submodule ℝ V)
    (rational : IsRationalSubspace i W) :
    fanHomTransportSource (linearAmbient_restrictedFan_eq fan W rational)
        (linearAmbientRestrictedComposite fan W rational) =
      restrictedFanInclusion fan W rational := by
  apply FanHom.ext
  rw [fanHomTransportSource_latticeMap]
  change ((subfanFanHom (linearAmbientFan fan W) fan (fun _ h => h.1)).comp
    (restrictedFanInclusion (linearAmbientFan fan W) W rational)).latticeMap = _
  rw [FanHom.comp_latticeMap]
  rfl

/-- A map-dependent proposition for the neighbourhood composite is
exactly that proposition for the original restricted inclusion. In
particular this applies degree by degree to actual pullback cohomology. -/
theorem linearAmbientRestrictedComposite_predicate (fan : Fan i) (W : Submodule ℝ V)
    (rational : IsRationalSubspace i W)
    (P : ∀ source : Fan (latticeTraceMap i W), FanHom source fan → Prop) :
    P (restrictedFan (linearAmbientFan fan W) W rational)
        (linearAmbientRestrictedComposite fan W rational) ↔
      P (restrictedFan fan W rational) (restrictedFanInclusion fan W rational) := by
  rw [fanHomTransportSource_predicate
    (linearAmbient_restrictedFan_eq fan W rational)
    (linearAmbientRestrictedComposite fan W rational) P,
    linearAmbientRestrictedComposite_transport]

end ToricPower

end
