import Dressed.QuarticIntegerComputationalData32.Block000
import Dressed.QuarticIntegerComputationalData32.Block001
import Dressed.QuarticIntegerComputationalData32.Block002
import Dressed.QuarticIntegerComputationalData32.Block003
import Dressed.QuarticIntegerComputationalData32.Block004
import Dressed.QuarticIntegerComputationalData32.Block005
import Dressed.QuarticIntegerComputationalData32.Block006
import Dressed.QuarticIntegerComputationalData32.Block007
import Dressed.QuarticIntegerComputationalData32.Block008
import Dressed.QuarticIntegerComputationalData32.Block009
import Dressed.QuarticIntegerComputationalData32.Block010
import Dressed.QuarticIntegerComputationalData32.Block011
import Dressed.QuarticIntegerComputationalData32.Block012
import Dressed.QuarticIntegerComputationalData32.Block013
import Dressed.QuarticIntegerComputationalData32.Block014
import Dressed.QuarticIntegerComputationalData32.Block015
import Dressed.QuarticIntegerComputationalData32.Block016
import Dressed.QuarticIntegerComputationalData32.Block017
namespace BilayerDressed.QuarticIntegerComputationalData
open QuarticIntegerData QuarticRootedRowTable QuarticIntegerRowChunks
set_option maxRecDepth 200000
set_option maxHeartbeats 0
def rows32 : List Row := ((((rows32_000 ++ rows32_001) ++ (rows32_002 ++ rows32_003)) ++ ((rows32_004 ++ rows32_005) ++ (rows32_006 ++ (rows32_007 ++ rows32_008)))) ++ (((rows32_009 ++ rows32_010) ++ (rows32_011 ++ rows32_012)) ++ ((rows32_013 ++ rows32_014) ++ (rows32_015 ++ (rows32_016 ++ rows32_017)))))
def labels32 : List Row := ((((ids32_000 ++ ids32_001) ++ (ids32_002 ++ ids32_003)) ++ ((ids32_004 ++ ids32_005) ++ (ids32_006 ++ (ids32_007 ++ ids32_008)))) ++ (((ids32_009 ++ ids32_010) ++ (ids32_011 ++ ids32_012)) ++ ((ids32_013 ++ ids32_014) ++ (ids32_015 ++ (ids32_016 ++ ids32_017)))))
def raw32 : Array Row := ⟨rows32⟩
def ids32 : Array Row := ⟨labels32⟩
theorem rows32_checked : EndpointChunk 32 (row3 1 2 3) (row3 29 30 31) rows32 :=
  ((((rows32_000_checked.append rows32_001_checked (by decide +kernel)).append (rows32_002_checked.append rows32_003_checked (by decide +kernel)) (by decide +kernel)).append ((rows32_004_checked.append rows32_005_checked (by decide +kernel)).append (rows32_006_checked.append (rows32_007_checked.append rows32_008_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)).append (((rows32_009_checked.append rows32_010_checked (by decide +kernel)).append (rows32_011_checked.append rows32_012_checked (by decide +kernel)) (by decide +kernel)).append ((rows32_013_checked.append rows32_014_checked (by decide +kernel)).append (rows32_015_checked.append (rows32_016_checked.append rows32_017_checked (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))
theorem raw32_size : (raw32 : Array Row).size=4495 := by
  change rows32.length=4495
  norm_num only [rows32,List.length_append,rows32_000_length,rows32_001_length,rows32_002_length,rows32_003_length,rows32_004_length,rows32_005_length,rows32_006_length,rows32_007_length,rows32_008_length,rows32_009_length,rows32_010_length,rows32_011_length,rows32_012_length,rows32_013_length,rows32_014_length,rows32_015_length,rows32_016_length,rows32_017_length]
theorem ids32_size : (ids32 : Array Row).size=4495 := by
  change labels32.length=4495
  norm_num only [labels32,List.length_append,ids32_000_length,ids32_001_length,ids32_002_length,ids32_003_length,ids32_004_length,ids32_005_length,ids32_006_length,ids32_007_length,ids32_008_length,ids32_009_length,ids32_010_length,ids32_011_length,ids32_012_length,ids32_013_length,ids32_014_length,ids32_015_length,ids32_016_length,ids32_017_length]
theorem hypotheses32 : (∀ i : Fin 4495,Valid 32 (row raw32 i)) ∧ StrictMono (fun i : Fin 4495=>code 32 (row raw32 i)) :=
  hypotheses_of_endpointChunk raw32 raw32_size rows32 rfl _ _ rows32_checked
theorem count32 : 4495=(32-1).choose 3 := by decide +kernel
end BilayerDressed.QuarticIntegerComputationalData
