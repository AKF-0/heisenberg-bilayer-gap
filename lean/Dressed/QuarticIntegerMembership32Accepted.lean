import Dressed.QuarticIntegerSpatialMembership32.Batch000
import Dressed.QuarticIntegerSpatialMembership32.Batch001
import Dressed.QuarticIntegerSpatialMembership32.Batch002
import Dressed.QuarticIntegerSpatialMembership32.Batch003
import Dressed.QuarticIntegerSpatialMembership32.Batch004
import Dressed.QuarticIntegerSpatialMembership32.Batch005
import Dressed.QuarticIntegerComputationalData32
namespace BilayerDressed.QuarticIntegerMembership32Accepted
open QuarticIntegerArrays QuarticIntegerData QuarticIntegerListCertificate QuarticIntegerTable
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem all_rows : List.Forall₂ (Matches 4 2 kernelData32 dictionary32) QuarticIntegerComputationalData.raw32.toList QuarticIntegerComputationalData.ids32.toList := by
  change List.Forall₂ (Matches 4 2 kernelData32 dictionary32) QuarticIntegerComputationalData.rows32 QuarticIntegerComputationalData.labels32
  unfold QuarticIntegerComputationalData.rows32 QuarticIntegerComputationalData.labels32
  exact (List.rel_append (List.rel_append (List.rel_append (List.rel_append chunk_000 chunk_001) (List.rel_append chunk_002 chunk_003)) (List.rel_append (List.rel_append chunk_004 chunk_005) (List.rel_append chunk_006 (List.rel_append chunk_007 chunk_008)))) (List.rel_append (List.rel_append (List.rel_append chunk_009 chunk_010) (List.rel_append chunk_011 chunk_012)) (List.rel_append (List.rel_append chunk_013 chunk_014) (List.rel_append chunk_015 (List.rel_append chunk_016 chunk_017)))))
theorem checked : Checked 4 2 4495 kernelData32 QuarticIntegerComputationalData.raw32 dictionary32 QuarticIntegerComputationalData.ids32 :=
  checked_of_forall₂ 4 2 4495 kernelData32 QuarticIntegerComputationalData.raw32 dictionary32 QuarticIntegerComputationalData.ids32 QuarticIntegerComputationalData.raw32_size all_rows
end BilayerDressed.QuarticIntegerMembership32Accepted
