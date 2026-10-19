import Dressed.QuarticIntegerNormCases16
import Dressed.QuarticIntegerGramFold
namespace BilayerDressed.QuarticIntegerNormBlocks16
open QuarticIntegerData QuarticIntegerListAggregates QuarticIntegerNormCases16
set_option maxHeartbeats 0
set_option maxRecDepth 200000
def ids_000 : List QuarticRootedRowTable.Row := [(row3 6 42 6),(row3 7 41 39),(row3 5 5 5),(row3 39 41 7),(row3 36 8 36),(row3 37 9 10),(row3 38 40 38),(row3 10 9 37),(row3 12 35 12),(row3 7 41 39),(row3 5 5 5),(row3 39 41 7),(row3 36 8 36),(row3 5 5 5),(row3 7 39 41),(row3 36 36 8)]
def norm_000 : QuarticIntegerNorm.NormCoefficients := ![0,0,0,0,0,0,199715979264,483989127168,2239557009408,3858726125568,9762678767616,12838974259200,21056024739840,23558548881408,30253385515008,28726206332928,27534132314112,19753464029184,13114393165824,5592193929216,1914905676288]
theorem checked_000 : gramList dictionary16 ids_000=norm_000 := by
  unfold ids_000
  rw [gramList_cons,gram_2]
  rw [gramList_cons,gram_4]
  rw [gramList_cons,gram_0]
  rw [gramList_cons,gram_56]
  rw [gramList_cons,gram_49]
  rw [gramList_cons,gram_51]
  rw [gramList_cons,gram_54]
  rw [gramList_cons,gram_8]
  rw [gramList_cons,gram_13]
  rw [gramList_cons,gram_4]
  rw [gramList_cons,gram_0]
  rw [gramList_cons,gram_56]
  rw [gramList_cons,gram_49]
  rw [gramList_cons,gram_0]
  rw [gramList_cons,gram_3]
  rw [gramList_cons,gram_50]
  rw [gramList_nil]
  decide +kernel
def ids_001 : List QuarticRootedRowTable.Row := [(row3 39 7 41),(row3 38 38 40),(row3 37 10 9),(row3 12 12 35),(row3 10 37 9),(row3 5 5 5),(row3 7 39 41),(row3 36 36 8),(row3 39 7 41),(row3 6 6 42),(row3 36 36 8),(row3 39 7 41),(row3 39 7 41),(row3 36 36 8),(row3 12 12 35),(row3 10 37 9)]
def norm_001 : QuarticIntegerNorm.NormCoefficients := ![0,0,0,0,0,0,103079215104,290715598848,1614639267840,2953159114752,8150354755584,10741100838912,18502800900096,20875318394880,28199014367232,26992703373312,27035190362112,19664424099840,13992970518528,6234986778624,2549920645632]
theorem checked_001 : gramList dictionary16 ids_001=norm_001 := by
  unfold ids_001
  rw [gramList_cons,gram_55]
  rw [gramList_cons,gram_53]
  rw [gramList_cons,gram_52]
  rw [gramList_cons,gram_12]
  rw [gramList_cons,gram_9]
  rw [gramList_cons,gram_0]
  rw [gramList_cons,gram_3]
  rw [gramList_cons,gram_50]
  rw [gramList_cons,gram_55]
  rw [gramList_cons,gram_1]
  rw [gramList_cons,gram_50]
  rw [gramList_cons,gram_55]
  rw [gramList_cons,gram_55]
  rw [gramList_cons,gram_50]
  rw [gramList_cons,gram_12]
  rw [gramList_cons,gram_9]
  rw [gramList_nil]
  decide +kernel
def ids_002 : List QuarticRootedRowTable.Row := [(row3 5 5 5),(row3 7 39 41),(row3 37 10 9),(row3 38 38 40),(row3 39 41 7),(row3 36 8 36),(row3 36 8 36),(row3 39 41 7),(row3 10 9 37),(row3 12 35 12),(row3 7 41 39),(row3 5 5 5),(row3 38 40 38),(row3 37 9 10),(row3 11 34 32),(row3 14 33 28)]
def norm_002 : QuarticIntegerNorm.NormCoefficients := ![0,0,0,0,0,0,109521666048,235149459456,1243393032192,2288680697856,6859599642624,9410558558208,17659286519808,20461243072512,29191917797376,28699749974016,30197454077952,22696103239680,17223544700928,7821650202624,3188806482432]
theorem checked_002 : gramList dictionary16 ids_002=norm_002 := by
  unfold ids_002
  rw [gramList_cons,gram_0]
  rw [gramList_cons,gram_3]
  rw [gramList_cons,gram_52]
  rw [gramList_cons,gram_53]
  rw [gramList_cons,gram_56]
  rw [gramList_cons,gram_49]
  rw [gramList_cons,gram_49]
  rw [gramList_cons,gram_56]
  rw [gramList_cons,gram_8]
  rw [gramList_cons,gram_13]
  rw [gramList_cons,gram_4]
  rw [gramList_cons,gram_0]
  rw [gramList_cons,gram_54]
  rw [gramList_cons,gram_51]
  rw [gramList_cons,gram_11]
  rw [gramList_cons,gram_17]
  rw [gramList_nil]
  decide +kernel
def ids_003 : List QuarticRootedRowTable.Row := [(row3 15 13 13),(row3 27 31 30),(row3 24 16 18),(row3 37 9 10),(row3 38 38 40),(row3 15 13 13),(row3 14 33 28),(row3 15 13 13),(row3 14 28 33),(row3 24 18 16),(row3 27 30 31),(row3 38 40 38),(row3 37 10 9),(row3 14 28 33),(row3 15 13 13),(row3 11 32 34)]
def norm_003 : QuarticIntegerNorm.NormCoefficients := ![0,0,0,0,0,0,0,0,74088185856,185220464640,1116355952640,1804691570688,6996199735296,9865751691264,22677662466048,26055391641600,38909959864320,33479559782400,30045188554752,15774057787392,5618708737536]
theorem checked_003 : gramList dictionary16 ids_003=norm_003 := by
  unfold ids_003
  rw [gramList_cons,gram_18]
  rw [gramList_cons,gram_37]
  rw [gramList_cons,gram_31]
  rw [gramList_cons,gram_51]
  rw [gramList_cons,gram_53]
  rw [gramList_cons,gram_18]
  rw [gramList_cons,gram_17]
  rw [gramList_cons,gram_18]
  rw [gramList_cons,gram_16]
  rw [gramList_cons,gram_32]
  rw [gramList_cons,gram_36]
  rw [gramList_cons,gram_54]
  rw [gramList_cons,gram_52]
  rw [gramList_cons,gram_16]
  rw [gramList_cons,gram_18]
  rw [gramList_cons,gram_10]
  rw [gramList_nil]
  decide +kernel
end BilayerDressed.QuarticIntegerNormBlocks16
