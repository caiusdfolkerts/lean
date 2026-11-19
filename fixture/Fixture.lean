module
public import Lean
@[expose] public section
namespace Fixture
/-- A polymorphic literal identity. -/
def identity {α : Sort u} (x : α) : α := x
/-- A literal type-valued family. -/
def carrier (n : Nat) : Type := Fin (n+1)
/-- A literal proposition-valued family. -/
def positive (n : Nat) : Prop := 0 < n
#print equations identity
#print equations carrier
#print equations positive
end Fixture
