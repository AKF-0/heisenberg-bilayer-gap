import Dressed.QuarticIntegerMembership64.Dictionary
import Dressed.QuarticIntegerBalancedKernel
import Dressed.QuarticIntegerZeroCases
import Dressed.QuarticIntegerSpatialListCertificate
import Dressed.QuarticIntegerRepresentativeTree
namespace BilayerDressed.QuarticIntegerSpatialRepresentatives64
open BilayerGap QuarticIntegerArrays QuarticIntegerDirect QuarticIntegerData
open QuarticIntegerLocalCases QuarticIntegerZeroCases QuarticIntegerBalancedKernel QuarticIntegerMembership64
open QuarticIntegerSpatialListCertificate QuarticIntegerRepresentativeTree
set_option maxHeartbeats 0
set_option maxRecDepth 200000
def validRep (rep : Rep) : Prop :=
  forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4)
    (repTuple 4 4 rep)=dictionary64.getD rep.label 0
end BilayerDressed.QuarticIntegerSpatialRepresentatives64
