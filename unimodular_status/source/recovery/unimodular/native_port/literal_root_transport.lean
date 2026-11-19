module

public import Recovery.Unimodular.NativePort.A3Enumeration
public import TauCeti.Geometry.Toric.Algebraic.Regular
public import Recovery.Unimodular.PriorExtensions.FanEquivCompatibility
public import Unimodular.FanTransport
public import Unimodular.FanRayTransport
public import Unimodular.HellerRootLattice
public import Recovery.Unimodular.PriorExtensions.LiteralRootCoordinates

/-! Literal root transport is assembled from the canonical complete owners.
All original declarations, proof bodies and compatibility helpers are retained
once; the exact comparisons are recorded in the geometry ownership record. -/

#print axioms Unimodular.FanTransport.transport
#print axioms Unimodular.FanTransport.fansEquiv
#print axioms Unimodular.FanTransport.transport_complete_iff
#print axioms Unimodular.FanTransport.transport_regular_iff
#print axioms Unimodular.FanTransport.hasRays_of_equiv
#print axioms Unimodular.FanTransport.hasRays_equiv_iff

namespace Unimodular.LiteralRootCoordinates

#print axioms coordinateCompatibility
#print axioms rootEmbedding_isIntegralLattice
#print axioms range_literalRootFamily
#print axioms completeRootFansEquiv
#print axioms regularCompleteRootFansEquiv
#print axioms a3_literal_complete_fan_count
#print axioms a3_literal_regular_complete_fan_count

end Unimodular.LiteralRootCoordinates

#check "UNIMODULAR_LITERAL_ROOT_TRANSPORT_EOF_V3"
