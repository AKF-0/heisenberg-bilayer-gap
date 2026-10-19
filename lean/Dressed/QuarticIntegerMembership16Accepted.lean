import Dressed.QuarticIntegerMembership16Accepted.Block000
import Dressed.QuarticIntegerMembership16Accepted.FastBatch000
import Dressed.QuarticIntegerMembership16Accepted.FastBatch001
import Dressed.QuarticIntegerMembership16Accepted.FastBatch002
import Dressed.QuarticIntegerMembership16Accepted.FastBatch003
import Dressed.QuarticIntegerRows16
namespace BilayerDressed.QuarticIntegerMembership16Accepted
open QuarticIntegerArrays QuarticIntegerData QuarticIntegerListCertificate QuarticIntegerTable
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem all_rows : List.Forall₂ (Matches 2 2 kernelData16 dictionary16) raw16.toList ids16.toList := by
  change List.Forall₂ (Matches 2 2 kernelData16 dictionary16) (((rows_000 ++ (rows_001 ++ rows_002)) ++ ((rows_003 ++ rows_004) ++ (rows_005 ++ rows_006))) ++ (((rows_007 ++ rows_008) ++ (rows_009 ++ rows_010)) ++ ((rows_011 ++ rows_012) ++ (rows_013 ++ rows_014)))) (((ids_000 ++ (ids_001 ++ ids_002)) ++ ((ids_003 ++ ids_004) ++ (ids_005 ++ ids_006))) ++ (((ids_007 ++ ids_008) ++ (ids_009 ++ ids_010)) ++ ((ids_011 ++ ids_012) ++ (ids_013 ++ ids_014))))
  exact (List.rel_append (List.rel_append (List.rel_append checked_000 (List.rel_append checked_001 checked_002)) (List.rel_append (List.rel_append checked_003 checked_004) (List.rel_append checked_005 checked_006))) (List.rel_append (List.rel_append (List.rel_append checked_007 checked_008) (List.rel_append checked_009 checked_010)) (List.rel_append (List.rel_append checked_011 checked_012) (List.rel_append checked_013 checked_014))))
/-- Every actual signed coefficient on every rooted support and matching. -/
theorem checked : Checked 2 2 455 kernelData16 raw16 dictionary16 ids16 :=
  checked_of_forall₂ 2 2 455 kernelData16 raw16 dictionary16 ids16 QuarticIntegerRows.size16 all_rows
end BilayerDressed.QuarticIntegerMembership16Accepted
