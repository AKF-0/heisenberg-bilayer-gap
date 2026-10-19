import Dressed.QuarticIntegerData16
import Dressed.QuarticIntegerRowValidity

/-! Linear kernel checks cover the actual decoded row list, including zero rows. -/
namespace BilayerDressed.QuarticIntegerRows
open QuarticIntegerData QuarticRootedRowTable QuarticIntegerRowValidity
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem size16 : raw16.size=455 := by decide +kernel

theorem all16 : raw16.toList.all (fun r=>decide (Valid (area 2 2) r))=true := by
  decide +kernel

theorem chain16 : List.IsChain (fun r s=>code (area 2 2) r<code (area 2 2) s) raw16.toList := by
  decide +kernel

theorem valid16 : ∀ i : Fin 455,Valid (area 2 2) (row raw16 i) :=
  valid_of_all raw16 size16 all16

theorem codes16 : StrictMono (fun i : Fin 455=>code (area 2 2) (row raw16 i)) :=
  strictMono_of_isChain raw16 size16 chain16

theorem count16 : 455=(area 2 2-1).choose 3 := by decide +kernel

end BilayerDressed.QuarticIntegerRows
