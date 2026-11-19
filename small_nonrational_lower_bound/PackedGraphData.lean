module
prelude
public import PackedGeneralGraphNodes

@[expose] public section

/-! Transparent decoders for literal facet and incidence data.  The data
carry no mathematical assertions; the cache and graph checks establish their
required properties after decoding. -/

namespace Papers.RationalityTen.PackedGraphData

open PackedRawNatGrowth ConcreteGrowth

def list (width code : Nat) : List Nat :=
  (readList width (take 16 code) (drop 16 code)).1

def finiteList (n width code : Nat) [NeZero n] : List (Fin n) :=
  (list width code).map (Fin.ofNat n)

def cell (code : Nat) : Cell :=
  let kind := take 5 code
  let vertices := take 10 (drop 5 code)
  let edgeCount := take 5 (drop 15 code)
  let edgeCode := drop 20 code
  let ridgeHeader := drop (10 * edgeCount) edgeCode
  let ridgeCount := take 5 ridgeHeader
  let ridgeCode := drop 5 ridgeHeader
  ⟨kind, vertices, (readList 10 edgeCount edgeCode).1,
    (readList 10 ridgeCount ridgeCode).1⟩

/-- Optional short covering lists for the capacity rules. -/
def bounds (n width : Nat) [NeZero n] : Nat → Nat → FastGraphRuleCheck.Bounds n
  | 0, _ => []
  | count + 1, code =>
      if take 1 code = 0 then none :: bounds n width count (drop 1 code)
      else
        let size := take 5 (drop 1 code)
        let values := drop 6 code
        some (PackedGraphNodes.finiteList n width size values) ::
          bounds n width count (drop (6 + width * size) code)

end Papers.RationalityTen.PackedGraphData
