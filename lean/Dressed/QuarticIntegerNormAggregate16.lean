import Dressed.QuarticIntegerNormBlocks16.Remaining
import Dressed.QuarticIntegerNormBlocks16.Batch000
import Dressed.QuarticIntegerNormCompatibility
namespace BilayerDressed.QuarticIntegerNormAggregate16
open QuarticIntegerData QuarticIntegerTable QuarticIntegerListAggregates QuarticIntegerNormBlocks16
set_option maxHeartbeats 0
set_option maxRecDepth 200000
def allIds : List QuarticRootedRowTable.Row := ((((ids_000 ++ (ids_001 ++ ids_002)) ++ ((ids_003 ++ ids_004) ++ (ids_005 ++ ids_006))) ++ ((ids_007 ++ (ids_008 ++ ids_009)) ++ ((ids_010 ++ ids_011) ++ (ids_012 ++ ids_013)))) ++ (((ids_014 ++ (ids_015 ++ ids_016)) ++ ((ids_017 ++ ids_018) ++ (ids_019 ++ ids_020))) ++ (((ids_021 ++ ids_022) ++ (ids_023 ++ ids_024)) ++ ((ids_025 ++ ids_026) ++ (ids_027 ++ ids_028)))))
theorem ids_eq : ids16.toList=allIds := by rfl
theorem ids_size : ids16.size=455 := by decide +kernel
/-- All455 signed rooted Gram rows, assembled solely from bounded checked folds. -/
theorem aggregate_checked : normCoefficients 455 dictionary16 ids16 4=normNumerators16 := by
  rw [normCoefficients_eq_gramList 455 4 dictionary16 ids16 ids_size,ids_eq]
  simp only [allIds,gramList_append,checked_000,checked_001,checked_002,checked_003,checked_004,checked_005,checked_006,checked_007,checked_008,checked_009,checked_010,checked_011,checked_012,checked_013,checked_014,checked_015,checked_016,checked_017,checked_018,checked_019,checked_020,checked_021,checked_022,checked_023,checked_024,checked_025,checked_026,checked_027,checked_028]
  decide +kernel
end BilayerDressed.QuarticIntegerNormAggregate16
