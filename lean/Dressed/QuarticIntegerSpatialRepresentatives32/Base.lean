import Dressed.QuarticIntegerMembership32.Dictionary
import Dressed.QuarticIntegerBalancedKernel
import Dressed.QuarticIntegerZeroCases
import Dressed.QuarticIntegerSpatialListCertificate
import Dressed.QuarticIntegerRepresentativeTree
namespace BilayerDressed.QuarticIntegerSpatialRepresentatives32
open BilayerGap QuarticIntegerArrays QuarticIntegerDirect QuarticIntegerData
open QuarticIntegerLocalCases QuarticIntegerZeroCases QuarticIntegerBalancedKernel QuarticIntegerMembership32
open QuarticIntegerSpatialListCertificate QuarticIntegerRepresentativeTree
set_option maxHeartbeats 0
set_option maxRecDepth 200000
def validRep (rep : Rep) : Prop :=
  forward (cachedKernel 4 2 kernelData32) (Torus.xNext 4 2) (Torus.yNext 4 2)
    (repTuple 4 2 rep)=dictionary32.getD rep.label 0
end BilayerDressed.QuarticIntegerSpatialRepresentatives32
