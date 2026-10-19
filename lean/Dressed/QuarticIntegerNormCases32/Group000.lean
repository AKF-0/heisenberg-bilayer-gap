import Dressed.QuarticIntegerGramCases
import Dressed.QuarticIntegerGramPermutation
import Dressed.QuarticIntegerMembership32.Dictionary
import Dressed.QuarticIntegerNormSorted32.Group000
import Dressed.QuarticIntegerNormSorted32.Group001
import Dressed.QuarticIntegerNormSorted32.Group002
set_option Elab.async false
namespace BilayerDressed.QuarticIntegerNormCases32
open QuarticIntegerData QuarticIntegerMembership32 QuarticIntegerNormSorted32
open QuarticIntegerListAggregates QuarticIntegerNorm QuarticIntegerGramPermutation
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem gram_0 : gram (fun a=>dictionary32.getD ((row3 11 293 216) a) 0)=norm_004 := by
  rw [gram_eq_of_entries dictionary32 (row3 11 293 216) _ _ _ dictionary_11 dictionary_293 dictionary_216]
  exact (gram021 (![0,0,0,0,0,0,0,4800,0,0,0]) (![0,0,0,0,0,0,0,-4800,8400,4200,5250]) (![0,0,0,0,0,0,0,0,3600,1800,2250])).trans sorted_004
theorem gram_1 : gram (fun a=>dictionary32.getD ((row3 11 294 217) a) 0)=norm_005 := by
  rw [gram_eq_of_entries dictionary32 (row3 11 294 217) _ _ _ dictionary_11 dictionary_294 dictionary_217]
  exact (gram021 (![0,0,0,0,0,0,0,4800,0,0,0]) (![0,0,0,0,0,0,0,-4800,8400,4200,35250]) (![0,0,0,0,0,0,0,0,3600,1800,32250])).trans sorted_005
theorem gram_2 : gram (fun a=>dictionary32.getD ((row3 13 320 166) a) 0)=norm_009 := by
  rw [gram_eq_of_entries dictionary32 (row3 13 320 166) _ _ _ dictionary_13 dictionary_320 dictionary_166]
  exact (gram021 (![0,0,0,0,0,0,0,14400,0,0,0]) (![0,0,0,0,0,0,0,-14400,25200,12600,15750]) (![0,0,0,0,0,0,0,0,10800,5400,6750])).trans sorted_009
theorem gram_3 : gram (fun a=>dictionary32.getD ((row3 21 21 22) a) 0)=norm_013 := by
  rw [gram_eq_of_entries dictionary32 (row3 21 21 22) _ _ _ dictionary_21 dictionary_21 dictionary_22]
  exact sorted_013
theorem gram_4 : gram (fun a=>dictionary32.getD ((row3 21 22 21) a) 0)=norm_013 := by
  rw [gram_eq_of_entries dictionary32 (row3 21 22 21) _ _ _ dictionary_21 dictionary_22 dictionary_21]
  exact (gram021 (![0,0,0,-32768,-32768,-82944,-59904,-105088,-94720,-63936,-18816]) (![0,0,0,-32768,-32768,-82944,-59904,-105088,-94720,-63936,-18816]) (![0,0,0,-32768,-32768,-79872,-60416,-99072,-91648,-55872,-15072])).trans sorted_013
theorem gram_5 : gram (fun a=>dictionary32.getD ((row3 22 21 21) a) 0)=norm_013 := by
  rw [gram_eq_of_entries dictionary32 (row3 22 21 21) _ _ _ dictionary_22 dictionary_21 dictionary_21]
  exact (gram201 (![0,0,0,-32768,-32768,-82944,-59904,-105088,-94720,-63936,-18816]) (![0,0,0,-32768,-32768,-82944,-59904,-105088,-94720,-63936,-18816]) (![0,0,0,-32768,-32768,-79872,-60416,-99072,-91648,-55872,-15072])).trans sorted_013
theorem gram_6 : gram (fun a=>dictionary32.getD ((row3 23 24 24) a) 0)=norm_014 := by
  rw [gram_eq_of_entries dictionary32 (row3 23 24 24) _ _ _ dictionary_23 dictionary_24 dictionary_24]
  exact sorted_014
theorem gram_7 : gram (fun a=>dictionary32.getD ((row3 24 24 23) a) 0)=norm_014 := by
  rw [gram_eq_of_entries dictionary32 (row3 24 24 23) _ _ _ dictionary_24 dictionary_24 dictionary_23]
  exact (gram120 (![0,0,0,-32768,-32768,-71680,-56320,-84224,-68608,-42880,-12480]) (![0,0,0,-32768,-32768,-54272,-31232,-58560,-58880,-36176,-9576]) (![0,0,0,-32768,-32768,-54272,-31232,-58560,-58880,-36176,-9576])).trans sorted_014
theorem gram_8 : gram (fun a=>dictionary32.getD ((row3 26 507 26) a) 0)=norm_016 := by
  rw [gram_eq_of_entries dictionary32 (row3 26 507 26) _ _ _ dictionary_26 dictionary_507 dictionary_26]
  exact (gram021 (![0,0,0,-32768,16384,-8192,96256,97792,121600,59520,26400]) (![0,0,0,-32768,16384,-8192,96256,97792,121600,59520,26400]) (![0,0,0,65536,196608,229376,172032,91136,22528,12288,2560])).trans sorted_016
theorem gram_9 : gram (fun a=>dictionary32.getD ((row3 27 25 506) a) 0)=norm_015 := by
  rw [gram_eq_of_entries dictionary32 (row3 27 25 506) _ _ _ dictionary_27 dictionary_25 dictionary_506]
  exact (gram102 (![0,0,0,-32768,16384,-8192,73216,84992,88160,36720,11700]) (![0,0,0,-32768,16384,12288,85504,82304,77536,38576,11620]) (![0,0,0,65536,196608,208896,133120,59008,8704,3584,640])).trans sorted_015
theorem gram_10 : gram (fun a=>dictionary32.getD ((row3 28 501 473) a) 0)=norm_017 := by
  rw [gram_eq_of_entries dictionary32 (row3 28 501 473) _ _ _ dictionary_28 dictionary_501 dictionary_473]
  exact (gram021 (![0,0,0,-16384,4096,12288,37120,30400,27472,13032,4145]) (![0,0,0,0,4096,-16384,7424,18560,25680,11080,3925]) (![0,0,0,16384,49152,57344,40960,23232,10816,6336,1360])).trans sorted_017
theorem gram_11 : gram (fun a=>dictionary32.getD ((row3 29 502 487) a) 0)=norm_018 := by
  rw [gram_eq_of_entries dictionary32 (row3 29 502 487) _ _ _ dictionary_29 dictionary_502 dictionary_487]
  exact (gram021 (![0,0,0,-16384,16384,25600,60416,39296,50992,31992,14825]) (![0,0,0,0,16384,-26624,19968,35968,62640,29240,15445]) (![0,0,0,16384,65536,99328,86528,48640,27520,21120,4960])).trans sorted_018
theorem gram_12 : gram (fun a=>dictionary32.getD ((row3 31 497 504) a) 0)=norm_020 := by
  rw [gram_eq_of_entries dictionary32 (row3 31 497 504) _ _ _ dictionary_31 dictionary_497 dictionary_504]
  exact sorted_020
theorem gram_13 : gram (fun a=>dictionary32.getD ((row3 31 504 497) a) 0)=norm_020 := by
  rw [gram_eq_of_entries dictionary32 (row3 31 504 497) _ _ _ dictionary_31 dictionary_504 dictionary_497]
  exact (gram021 (![0,0,0,-16384,28672,48128,127744,72320,105504,74864,33440]) (![0,0,0,0,28672,-51200,51456,63232,151200,70320,40800]) (![0,0,0,16384,81920,146432,162304,105600,55040,48640,11840])).trans sorted_020
theorem gram_14 : gram (fun a=>dictionary32.getD ((row3 32 498 503) a) 0)=norm_021 := by
  rw [gram_eq_of_entries dictionary32 (row3 32 498 503) _ _ _ dictionary_32 dictionary_498 dictionary_503]
  exact sorted_021
theorem gram_15 : gram (fun a=>dictionary32.getD ((row3 32 503 498) a) 0)=norm_021 := by
  rw [gram_eq_of_entries dictionary32 (row3 32 503 498) _ _ _ dictionary_32 dictionary_503 dictionary_498]
  exact (gram021 (![0,0,0,-16384,28672,53248,114176,72128,73808,45288,14610]) (![0,0,0,0,28672,-20480,40448,52480,85904,36744,14490]) (![0,0,0,16384,81920,110592,94208,45376,14848,17408,4480])).trans sorted_021
theorem gram_16 : gram (fun a=>dictionary32.getD ((row3 33 483 483) a) 0)=norm_022 := by
  rw [gram_eq_of_entries dictionary32 (row3 33 483 483) _ _ _ dictionary_33 dictionary_483 dictionary_483]
  exact sorted_022
theorem gram_17 : gram (fun a=>dictionary32.getD ((row3 36 44 485) a) 0)=norm_025 := by
  rw [gram_eq_of_entries dictionary32 (row3 36 44 485) _ _ _ dictionary_36 dictionary_44 dictionary_485]
  exact sorted_025
theorem gram_18 : gram (fun a=>dictionary32.getD ((row3 37 486 45) a) 0)=norm_026 := by
  rw [gram_eq_of_entries dictionary32 (row3 37 486 45) _ _ _ dictionary_37 dictionary_486 dictionary_45]
  exact (gram021 (![0,0,0,0,-16384,-90112,-54272,-51200,-27392,-43040,-17840]) (![0,0,0,0,0,-34816,-17408,-43136,-36608,-49600,-19840]) (![0,0,0,0,16384,-30720,-30720,-62848,-45568,-22880,-6000])).trans sorted_026
theorem gram_19 : gram (fun a=>dictionary32.getD ((row3 38 489 51) a) 0)=norm_027 := by
  rw [gram_eq_of_entries dictionary32 (row3 38 489 51) _ _ _ dictionary_38 dictionary_489 dictionary_51]
  exact (gram021 (![0,0,0,0,-16384,-71680,-58368,-56000,-32384,-32080,-11480]) (![0,0,0,0,0,-25600,-14848,-44928,-40192,-43680,-16080]) (![0,0,0,0,16384,-17408,-20992,-58944,-47744,-23760,-6200])).trans sorted_027
theorem gram_20 : gram (fun a=>dictionary32.getD ((row3 40 56 476) a) 0)=norm_029 := by
  rw [gram_eq_of_entries dictionary32 (row3 40 56 476) _ _ _ dictionary_40 dictionary_56 dictionary_476]
  exact sorted_029
theorem gram_21 : gram (fun a=>dictionary32.getD ((row3 40 476 56) a) 0)=norm_029 := by
  rw [gram_eq_of_entries dictionary32 (row3 40 476 56) _ _ _ dictionary_40 dictionary_476 dictionary_56]
  exact (gram021 (![0,0,0,0,-8192,-51200,-36864,-45824,-22528,-21408,-7568]) (![0,0,0,0,0,-23552,-15872,-48512,-39936,-38688,-13968]) (![0,0,0,0,8192,-19456,-18944,-54656,-39936,-28800,-9600])).trans sorted_029
theorem gram_22 : gram (fun a=>dictionary32.getD ((row3 42 477 84) a) 0)=norm_031 := by
  rw [gram_eq_of_entries dictionary32 (row3 42 477 84) _ _ _ dictionary_42 dictionary_477 dictionary_84]
  exact (gram021 (![0,0,0,0,-8192,-30720,-26624,-28480,-19072,-10960,-2840]) (![0,0,0,0,0,-9216,-4608,-15616,-15488,-11920,-3640]) (![0,0,0,0,8192,-5120,-7680,-28224,-24064,-12160,-3200])).trans sorted_031
theorem gram_23 : gram (fun a=>dictionary32.getD ((row3 44 36 485) a) 0)=norm_025 := by
  rw [gram_eq_of_entries dictionary32 (row3 44 36 485) _ _ _ dictionary_44 dictionary_36 dictionary_485]
  exact (gram102 (![0,0,0,0,-16384,-102400,-68608,-55168,-20736,-35936,-14736]) (![0,0,0,0,0,-47104,-31744,-69504,-61952,-66496,-24736]) (![0,0,0,0,16384,-38912,-43008,-95232,-63232,-43040,-14000])).trans sorted_025
theorem gram_24 : gram (fun a=>dictionary32.getD ((row3 45 37 486) a) 0)=norm_026 := by
  rw [gram_eq_of_entries dictionary32 (row3 45 37 486) _ _ _ dictionary_45 dictionary_37 dictionary_486]
  exact (gram102 (![0,0,0,0,-16384,-90112,-54272,-51200,-27392,-43040,-17840]) (![0,0,0,0,0,-34816,-17408,-43136,-36608,-49600,-19840]) (![0,0,0,0,16384,-30720,-30720,-62848,-45568,-22880,-6000])).trans sorted_026
theorem gram_25 : gram (fun a=>dictionary32.getD ((row3 45 486 37) a) 0)=norm_026 := by
  rw [gram_eq_of_entries dictionary32 (row3 45 486 37) _ _ _ dictionary_45 dictionary_486 dictionary_37]
  exact (gram120 (![0,0,0,0,-16384,-90112,-54272,-51200,-27392,-43040,-17840]) (![0,0,0,0,0,-34816,-17408,-43136,-36608,-49600,-19840]) (![0,0,0,0,16384,-30720,-30720,-62848,-45568,-22880,-6000])).trans sorted_026
theorem gram_26 : gram (fun a=>dictionary32.getD ((row3 46 448 470) a) 0)=norm_033 := by
  rw [gram_eq_of_entries dictionary32 (row3 46 448 470) _ _ _ dictionary_46 dictionary_448 dictionary_470]
  exact sorted_033
theorem gram_27 : gram (fun a=>dictionary32.getD ((row3 46 470 448) a) 0)=norm_033 := by
  rw [gram_eq_of_entries dictionary32 (row3 46 470 448) _ _ _ dictionary_46 dictionary_470 dictionary_448]
  exact (gram021 (![0,0,0,0,0,-32768,69632,-512,196480,93120,60400]) (![0,0,0,0,0,0,131072,188928,103424,98304,24320]) (![0,0,0,0,0,32768,217088,131072,117120,96960,5040])).trans sorted_033
theorem gram_28 : gram (fun a=>dictionary32.getD ((row3 48 59 58) a) 0)=norm_035 := by
  rw [gram_eq_of_entries dictionary32 (row3 48 59 58) _ _ _ dictionary_48 dictionary_59 dictionary_58]
  exact (gram021 (![0,0,0,0,0,-30720,-15360,-17600,-3200,-3600,-1400]) (![0,0,0,0,0,-21504,-16896,-41088,-27648,-21120,-7200]) (![0,0,0,0,0,-21504,-16896,-27968,-19328,-9840,-2600])).trans sorted_035
theorem gram_29 : gram (fun a=>dictionary32.getD ((row3 49 468 191) a) 0)=norm_036 := by
  rw [gram_eq_of_entries dictionary32 (row3 49 468 191) _ _ _ dictionary_49 dictionary_468 dictionary_191]
  exact (gram021 (![0,0,0,0,0,-30720,6144,14976,36768,15888,7230]) (![0,0,0,0,0,0,0,-7680,12960,13200,6150]) (![0,0,0,0,0,30720,36864,26496,16128,12288,2880])).trans sorted_036
theorem gram_30 : gram (fun a=>dictionary32.getD ((row3 50 472 72) a) 0)=norm_037 := by
  rw [gram_eq_of_entries dictionary32 (row3 50 472 72) _ _ _ dictionary_50 dictionary_472 dictionary_72]
  exact (gram021 (![0,0,0,0,0,-30720,23808,18432,69456,37896,46590]) (![0,0,0,0,0,-15360,25344,15936,54288,37608,45510]) (![0,0,0,0,0,46080,87552,74688,52224,40704,9600])).trans sorted_037
theorem gram_31 : gram (fun a=>dictionary32.getD ((row3 51 38 489) a) 0)=norm_027 := by
  rw [gram_eq_of_entries dictionary32 (row3 51 38 489) _ _ _ dictionary_51 dictionary_38 dictionary_489]
  exact (gram102 (![0,0,0,0,-16384,-71680,-58368,-56000,-32384,-32080,-11480]) (![0,0,0,0,0,-25600,-14848,-44928,-40192,-43680,-16080]) (![0,0,0,0,16384,-17408,-20992,-58944,-47744,-23760,-6200])).trans sorted_027
theorem gram_32 : gram (fun a=>dictionary32.getD ((row3 51 489 38) a) 0)=norm_027 := by
  rw [gram_eq_of_entries dictionary32 (row3 51 489 38) _ _ _ dictionary_51 dictionary_489 dictionary_38]
  exact (gram120 (![0,0,0,0,-16384,-71680,-58368,-56000,-32384,-32080,-11480]) (![0,0,0,0,0,-25600,-14848,-44928,-40192,-43680,-16080]) (![0,0,0,0,16384,-17408,-20992,-58944,-47744,-23760,-6200])).trans sorted_027
theorem gram_33 : gram (fun a=>dictionary32.getD ((row3 52 52 66) a) 0)=norm_038 := by
  rw [gram_eq_of_entries dictionary32 (row3 52 52 66) _ _ _ dictionary_52 dictionary_52 dictionary_66]
  exact sorted_038
theorem gram_34 : gram (fun a=>dictionary32.getD ((row3 53 54 64) a) 0)=norm_039 := by
  rw [gram_eq_of_entries dictionary32 (row3 53 54 64) _ _ _ dictionary_53 dictionary_54 dictionary_64]
  exact sorted_039
theorem gram_35 : gram (fun a=>dictionary32.getD ((row3 53 64 54) a) 0)=norm_039 := by
  rw [gram_eq_of_entries dictionary32 (row3 53 64 54) _ _ _ dictionary_53 dictionary_64 dictionary_54]
  exact (gram021 (![0,0,0,0,0,-24576,-59392,-117888,-75776,-105136,-41816]) (![0,0,0,0,0,-24576,-44032,-97664,-60160,-118528,-50848]) (![0,0,0,0,0,-16384,21504,-83200,-105216,-100304,-36104])).trans sorted_039
theorem gram_36 : gram (fun a=>dictionary32.getD ((row3 54 64 53) a) 0)=norm_039 := by
  rw [gram_eq_of_entries dictionary32 (row3 54 64 53) _ _ _ dictionary_54 dictionary_64 dictionary_53]
  exact (gram120 (![0,0,0,0,0,-24576,-59392,-117888,-75776,-105136,-41816]) (![0,0,0,0,0,-24576,-44032,-97664,-60160,-118528,-50848]) (![0,0,0,0,0,-16384,21504,-83200,-105216,-100304,-36104])).trans sorted_039
theorem gram_37 : gram (fun a=>dictionary32.getD ((row3 55 55 60) a) 0)=norm_040 := by
  rw [gram_eq_of_entries dictionary32 (row3 55 55 60) _ _ _ dictionary_55 dictionary_55 dictionary_60]
  exact sorted_040
theorem gram_38 : gram (fun a=>dictionary32.getD ((row3 56 40 476) a) 0)=norm_029 := by
  rw [gram_eq_of_entries dictionary32 (row3 56 40 476) _ _ _ dictionary_56 dictionary_40 dictionary_476]
  exact (gram102 (![0,0,0,0,-8192,-51200,-36864,-45824,-22528,-21408,-7568]) (![0,0,0,0,0,-23552,-15872,-48512,-39936,-38688,-13968]) (![0,0,0,0,8192,-19456,-18944,-54656,-39936,-28800,-9600])).trans sorted_029
theorem gram_39 : gram (fun a=>dictionary32.getD ((row3 56 476 40) a) 0)=norm_029 := by
  rw [gram_eq_of_entries dictionary32 (row3 56 476 40) _ _ _ dictionary_56 dictionary_476 dictionary_40]
  exact (gram120 (![0,0,0,0,-8192,-51200,-36864,-45824,-22528,-21408,-7568]) (![0,0,0,0,0,-23552,-15872,-48512,-39936,-38688,-13968]) (![0,0,0,0,8192,-19456,-18944,-54656,-39936,-28800,-9600])).trans sorted_029
theorem gram_40 : gram (fun a=>dictionary32.getD ((row3 57 41 475) a) 0)=norm_030 := by
  rw [gram_eq_of_entries dictionary32 (row3 57 41 475) _ _ _ dictionary_57 dictionary_41 dictionary_475]
  exact (gram102 (![0,0,0,0,-8192,-51200,-34304,-27584,-10368,-6768,-1768]) (![0,0,0,0,0,-23552,-15872,-32192,-28416,-19808,-5968]) (![0,0,0,0,8192,-19456,-21504,-50176,-34176,-23760,-7800])).trans sorted_030
theorem gram_41 : gram (fun a=>dictionary32.getD ((row3 58 48 59) a) 0)=norm_035 := by
  rw [gram_eq_of_entries dictionary32 (row3 58 48 59) _ _ _ dictionary_58 dictionary_48 dictionary_59]
  exact (gram102 (![0,0,0,0,0,-30720,-15360,-17600,-3200,-3600,-1400]) (![0,0,0,0,0,-21504,-16896,-41088,-27648,-21120,-7200]) (![0,0,0,0,0,-21504,-16896,-27968,-19328,-9840,-2600])).trans sorted_035
theorem gram_42 : gram (fun a=>dictionary32.getD ((row3 58 59 48) a) 0)=norm_035 := by
  rw [gram_eq_of_entries dictionary32 (row3 58 59 48) _ _ _ dictionary_58 dictionary_59 dictionary_48]
  exact (gram120 (![0,0,0,0,0,-30720,-15360,-17600,-3200,-3600,-1400]) (![0,0,0,0,0,-21504,-16896,-41088,-27648,-21120,-7200]) (![0,0,0,0,0,-21504,-16896,-27968,-19328,-9840,-2600])).trans sorted_035
theorem gram_43 : gram (fun a=>dictionary32.getD ((row3 59 48 58) a) 0)=norm_035 := by
  rw [gram_eq_of_entries dictionary32 (row3 59 48 58) _ _ _ dictionary_59 dictionary_48 dictionary_58]
  exact (gram201 (![0,0,0,0,0,-30720,-15360,-17600,-3200,-3600,-1400]) (![0,0,0,0,0,-21504,-16896,-41088,-27648,-21120,-7200]) (![0,0,0,0,0,-21504,-16896,-27968,-19328,-9840,-2600])).trans sorted_035
theorem gram_44 : gram (fun a=>dictionary32.getD ((row3 60 55 55) a) 0)=norm_040 := by
  rw [gram_eq_of_entries dictionary32 (row3 60 55 55) _ _ _ dictionary_60 dictionary_55 dictionary_55]
  exact (gram201 (![0,0,0,0,0,-24576,-44032,-76224,-53120,-81568,-33248]) (![0,0,0,0,0,-24576,-44032,-76224,-53120,-81568,-33248]) (![0,0,0,0,0,-16384,6144,-64256,-75520,-62576,-21336])).trans sorted_040
theorem gram_45 : gram (fun a=>dictionary32.getD ((row3 61 463 417) a) 0)=norm_041 := by
  rw [gram_eq_of_entries dictionary32 (row3 61 463 417) _ _ _ dictionary_61 dictionary_463 dictionary_417]
  exact (gram021 (![0,0,0,0,0,-16384,7168,9152,42544,18584,8515]) (![0,0,0,0,0,0,22528,17472,10496,15616,4160]) (![0,0,0,0,0,16384,62464,34816,38640,27000,8175])).trans sorted_041
theorem gram_46 : gram (fun a=>dictionary32.getD ((row3 62 464 418) a) 0)=norm_042 := by
  rw [gram_eq_of_entries dictionary32 (row3 62 464 418) _ _ _ dictionary_62 dictionary_464 dictionary_418]
  exact (gram021 (![0,0,0,0,0,-16384,7168,9152,51184,24824,18475]) (![0,0,0,0,0,0,22528,17472,18176,23296,6080]) (![0,0,0,0,0,16384,62464,34816,47280,33240,18135])).trans sorted_042
theorem gram_47 : gram (fun a=>dictionary32.getD ((row3 63 465 435) a) 0)=norm_043 := by
  rw [gram_eq_of_entries dictionary32 (row3 63 465 435) _ _ _ dictionary_63 dictionary_465 dictionary_435]
  exact (gram021 (![0,0,0,0,0,-16384,20992,11648,107872,58352,67690]) (![0,0,0,0,0,0,44032,48768,61184,62464,15680]) (![0,0,0,0,0,16384,85504,50176,92640,66480,64770])).trans sorted_043
theorem gram_48 : gram (fun a=>dictionary32.getD ((row3 64 54 53) a) 0)=norm_039 := by
  rw [gram_eq_of_entries dictionary32 (row3 64 54 53) _ _ _ dictionary_64 dictionary_54 dictionary_53]
  exact (gram210 (![0,0,0,0,0,-24576,-59392,-117888,-75776,-105136,-41816]) (![0,0,0,0,0,-24576,-44032,-97664,-60160,-118528,-50848]) (![0,0,0,0,0,-16384,21504,-83200,-105216,-100304,-36104])).trans sorted_039
theorem gram_49 : gram (fun a=>dictionary32.getD ((row3 65 441 466) a) 0)=norm_044 := by
  rw [gram_eq_of_entries dictionary32 (row3 65 441 466) _ _ _ dictionary_65 dictionary_441 dictionary_466]
  exact sorted_044
theorem gram_50 : gram (fun a=>dictionary32.getD ((row3 65 466 441) a) 0)=norm_044 := by
  rw [gram_eq_of_entries dictionary32 (row3 65 466 441) _ _ _ dictionary_65 dictionary_466 dictionary_441]
  exact (gram021 (![0,0,0,0,0,-16384,34816,-256,150080,84000,89960]) (![0,0,0,0,0,0,65536,94464,97792,95232,23680]) (![0,0,0,0,0,16384,108544,65536,110400,85920,62280])).trans sorted_044
theorem gram_51 : gram (fun a=>dictionary32.getD ((row3 66 52 52) a) 0)=norm_038 := by
  rw [gram_eq_of_entries dictionary32 (row3 66 52 52) _ _ _ dictionary_66 dictionary_52 dictionary_52]
  exact (gram201 (![0,0,0,0,0,-24576,-59392,-129792,-56832,-116864,-50304]) (![0,0,0,0,0,-24576,-59392,-129792,-56832,-116864,-50304]) (![0,0,0,0,0,-16384,36864,-80896,-107520,-98176,-35136])).trans sorted_038
theorem gram_52 : gram (fun a=>dictionary32.getD ((row3 67 460 124) a) 0)=norm_045 := by
  rw [gram_eq_of_entries dictionary32 (row3 67 460 124) _ _ _ dictionary_67 dictionary_460 dictionary_124]
  exact (gram021 (![0,0,0,0,0,-15360,512,4928,16144,7144,3365]) (![0,0,0,0,0,0,-2560,-6400,4240,5800,2825]) (![0,0,0,0,0,15360,18432,13248,8064,6144,1440])).trans sorted_045
theorem gram_53 : gram (fun a=>dictionary32.getD ((row3 68 462 391) a) 0)=norm_046 := by
  rw [gram_eq_of_entries dictionary32 (row3 68 462 391) _ _ _ dictionary_68 dictionary_462 dictionary_391]
  exact (gram021 (![0,0,0,0,0,-15360,7424,8576,26768,11688,5230]) (![0,0,0,0,0,0,8960,1280,11600,11400,4150]) (![0,0,0,0,0,15360,29184,26496,16128,12288,2880])).trans sorted_046
theorem gram_54 : gram (fun a=>dictionary32.getD ((row3 69 467 102) a) 0)=norm_047 := by
  rw [gram_eq_of_entries dictionary32 (row3 69 467 102) _ _ _ dictionary_69 dictionary_467 dictionary_102]
  exact (gram021 (![0,0,0,0,0,-15360,8704,7296,30048,15728,9440]) (![0,0,0,0,0,-5120,9728,4032,19936,15536,8720]) (![0,0,0,0,0,20480,38912,33728,22784,17664,4160])).trans sorted_047
theorem gram_55 : gram (fun a=>dictionary32.getD ((row3 70 411 461) a) 0)=norm_048 := by
  rw [gram_eq_of_entries dictionary32 (row3 70 411 461) _ _ _ dictionary_70 dictionary_411 dictionary_461]
  exact sorted_048
theorem gram_56 : gram (fun a=>dictionary32.getD ((row3 70 461 411) a) 0)=norm_048 := by
  rw [gram_eq_of_entries dictionary32 (row3 70 461 411) _ _ _ dictionary_70 dictionary_461 dictionary_411]
  exact (gram021 (![0,0,0,0,0,-15360,17664,23616,43248,19608,12210]) (![0,0,0,0,0,0,19200,11520,28080,19320,11130]) (![0,0,0,0,0,15360,29184,21696,19968,16128,3840])).trans sorted_048
theorem gram_57 : gram (fun a=>dictionary32.getD ((row3 71 71 469) a) 0)=norm_049 := by
  rw [gram_eq_of_entries dictionary32 (row3 71 71 469) _ _ _ dictionary_71 dictionary_71 dictionary_469]
  exact sorted_049
theorem gram_58 : gram (fun a=>dictionary32.getD ((row3 71 469 71) a) 0)=norm_049 := by
  rw [gram_eq_of_entries dictionary32 (row3 71 469 71) _ _ _ dictionary_71 dictionary_469 dictionary_71]
  exact (gram021 (![0,0,0,0,0,-15360,21504,14976,60288,35328,38340]) (![0,0,0,0,0,-15360,21504,14976,60288,35328,38340]) (![0,0,0,0,0,30720,58368,52992,39936,32256,7680])).trans sorted_049
theorem gram_59 : gram (fun a=>dictionary32.getD ((row3 72 50 472) a) 0)=norm_037 := by
  rw [gram_eq_of_entries dictionary32 (row3 72 50 472) _ _ _ dictionary_72 dictionary_50 dictionary_472]
  exact (gram102 (![0,0,0,0,0,-30720,23808,18432,69456,37896,46590]) (![0,0,0,0,0,-15360,25344,15936,54288,37608,45510]) (![0,0,0,0,0,46080,87552,74688,52224,40704,9600])).trans sorted_037
theorem gram_60 : gram (fun a=>dictionary32.getD ((row3 72 472 50) a) 0)=norm_037 := by
  rw [gram_eq_of_entries dictionary32 (row3 72 472 50) _ _ _ dictionary_72 dictionary_472 dictionary_50]
  exact (gram120 (![0,0,0,0,0,-30720,23808,18432,69456,37896,46590]) (![0,0,0,0,0,-15360,25344,15936,54288,37608,45510]) (![0,0,0,0,0,46080,87552,74688,52224,40704,9600])).trans sorted_037
theorem gram_61 : gram (fun a=>dictionary32.getD ((row3 73 39 490) a) 0)=norm_028 := by
  rw [gram_eq_of_entries dictionary32 (row3 73 39 490) _ _ _ dictionary_73 dictionary_39 dictionary_490]
  exact (gram102 (![0,0,0,0,-16384,-59392,-38912,-33920,-19712,-14720,-4640]) (![0,0,0,0,0,-13312,-512,-17088,-19200,-16840,-5540]) (![0,0,0,0,16384,-9216,-13824,-39360,-30720,-15560,-4100])).trans sorted_028
theorem gram_62 : gram (fun a=>dictionary32.getD ((row3 74 75 92) a) 0)=norm_050 := by
  rw [gram_eq_of_entries dictionary32 (row3 74 75 92) _ _ _ dictionary_74 dictionary_75 dictionary_92]
  exact sorted_050
theorem gram_63 : gram (fun a=>dictionary32.getD ((row3 75 74 92) a) 0)=norm_050 := by
  rw [gram_eq_of_entries dictionary32 (row3 75 74 92) _ _ _ dictionary_75 dictionary_74 dictionary_92]
  exact (gram102 (![0,0,0,0,0,-12288,-29696,-88192,-56320,-89664,-36704]) (![0,0,0,0,0,-12288,-29696,-87936,-51456,-102592,-44352]) (![0,0,0,0,0,-8192,18432,-63744,-81664,-85120,-31520])).trans sorted_050
open QuarticIntegerData QuarticIntegerMembership32 QuarticIntegerNormSorted32
open QuarticIntegerListAggregates QuarticIntegerNorm QuarticIntegerGramPermutation
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem gram_64 : gram (fun a=>dictionary32.getD ((row3 76 77 93) a) 0)=norm_051 := by
  rw [gram_eq_of_entries dictionary32 (row3 76 77 93) _ _ _ dictionary_76 dictionary_77 dictionary_93]
  exact sorted_051
theorem gram_65 : gram (fun a=>dictionary32.getD ((row3 77 76 93) a) 0)=norm_051 := by
  rw [gram_eq_of_entries dictionary32 (row3 77 76 93) _ _ _ dictionary_77 dictionary_76 dictionary_93]
  exact (gram102 (![0,0,0,0,0,-12288,-29696,-52864,-14848,-41088,-18368]) (![0,0,0,0,0,-12288,-29696,-50304,-12288,-38848,-17568]) (![0,0,0,0,0,-8192,18432,-29184,-39424,-30400,-10400])).trans sorted_051
theorem gram_66 : gram (fun a=>dictionary32.getD ((row3 78 81 87) a) 0)=norm_052 := by
  rw [gram_eq_of_entries dictionary32 (row3 78 81 87) _ _ _ dictionary_78 dictionary_81 dictionary_87]
  exact sorted_052
theorem gram_67 : gram (fun a=>dictionary32.getD ((row3 78 87 81) a) 0)=norm_052 := by
  rw [gram_eq_of_entries dictionary32 (row3 78 87 81) _ _ _ dictionary_78 dictionary_87 dictionary_81]
  exact (gram021 (![0,0,0,0,0,-12288,-29696,-36480,-17152,-45680,-20440]) (![0,0,0,0,0,-12288,-19456,-18560,-4352,-38480,-18440]) (![0,0,0,0,0,-8192,8192,-21504,-26624,-13600,-3600])).trans sorted_052
theorem gram_68 : gram (fun a=>dictionary32.getD ((row3 79 80 85) a) 0)=norm_053 := by
  rw [gram_eq_of_entries dictionary32 (row3 79 80 85) _ _ _ dictionary_79 dictionary_80 dictionary_85]
  exact sorted_053
theorem gram_69 : gram (fun a=>dictionary32.getD ((row3 81 87 78) a) 0)=norm_052 := by
  rw [gram_eq_of_entries dictionary32 (row3 81 87 78) _ _ _ dictionary_81 dictionary_87 dictionary_78]
  exact (gram120 (![0,0,0,0,0,-12288,-29696,-36480,-17152,-45680,-20440]) (![0,0,0,0,0,-12288,-19456,-18560,-4352,-38480,-18440]) (![0,0,0,0,0,-8192,8192,-21504,-26624,-13600,-3600])).trans sorted_052
theorem gram_70 : gram (fun a=>dictionary32.getD ((row3 82 94 94) a) 0)=norm_054 := by
  rw [gram_eq_of_entries dictionary32 (row3 82 94 94) _ _ _ dictionary_82 dictionary_94 dictionary_94]
  exact sorted_054
theorem gram_71 : gram (fun a=>dictionary32.getD ((row3 83 96 95) a) 0)=norm_055 := by
  rw [gram_eq_of_entries dictionary32 (row3 83 96 95) _ _ _ dictionary_83 dictionary_96 dictionary_95]
  exact (gram021 (![0,0,0,0,0,-10240,-5120,-6720,-1920,-1680,-600]) (![0,0,0,0,0,-7168,-5632,-13696,-9216,-7040,-2400]) (![0,0,0,0,0,-7168,-5632,-10176,-7296,-3760,-1000])).trans sorted_055
theorem gram_72 : gram (fun a=>dictionary32.getD ((row3 84 42 477) a) 0)=norm_031 := by
  rw [gram_eq_of_entries dictionary32 (row3 84 42 477) _ _ _ dictionary_84 dictionary_42 dictionary_477]
  exact (gram102 (![0,0,0,0,-8192,-30720,-26624,-28480,-19072,-10960,-2840]) (![0,0,0,0,0,-9216,-4608,-15616,-15488,-11920,-3640]) (![0,0,0,0,8192,-5120,-7680,-28224,-24064,-12160,-3200])).trans sorted_031
theorem gram_73 : gram (fun a=>dictionary32.getD ((row3 84 477 42) a) 0)=norm_031 := by
  rw [gram_eq_of_entries dictionary32 (row3 84 477 42) _ _ _ dictionary_84 dictionary_477 dictionary_42]
  exact (gram120 (![0,0,0,0,-8192,-30720,-26624,-28480,-19072,-10960,-2840]) (![0,0,0,0,0,-9216,-4608,-15616,-15488,-11920,-3640]) (![0,0,0,0,8192,-5120,-7680,-28224,-24064,-12160,-3200])).trans sorted_031
theorem gram_74 : gram (fun a=>dictionary32.getD ((row3 85 80 79) a) 0)=norm_053 := by
  rw [gram_eq_of_entries dictionary32 (row3 85 80 79) _ _ _ dictionary_85 dictionary_80 dictionary_79]
  exact (gram210 (![0,0,0,0,0,-12288,-22016,-42304,-34688,-37568,-13808]) (![0,0,0,0,0,-12288,-19456,-36544,-27648,-43288,-17868]) (![0,0,0,0,0,-8192,512,-36992,-41856,-36296,-12596])).trans sorted_053
theorem gram_75 : gram (fun a=>dictionary32.getD ((row3 86 454 379) a) 0)=norm_056 := by
  rw [gram_eq_of_entries dictionary32 (row3 86 454 379) _ _ _ dictionary_86 dictionary_454 dictionary_379]
  exact (gram021 (![0,0,0,0,0,-8192,1280,4160,20064,8944,4365]) (![0,0,0,0,0,0,7680,3520,2560,5760,1600]) (![0,0,0,0,0,8192,27392,14848,20000,13200,4625])).trans sorted_056
theorem gram_76 : gram (fun a=>dictionary32.getD ((row3 87 81 78) a) 0)=norm_052 := by
  rw [gram_eq_of_entries dictionary32 (row3 87 81 78) _ _ _ dictionary_87 dictionary_81 dictionary_78]
  exact (gram210 (![0,0,0,0,0,-12288,-29696,-36480,-17152,-45680,-20440]) (![0,0,0,0,0,-12288,-19456,-18560,-4352,-38480,-18440]) (![0,0,0,0,0,-8192,8192,-21504,-26624,-13600,-3600])).trans sorted_052
theorem gram_77 : gram (fun a=>dictionary32.getD ((row3 88 455 410) a) 0)=norm_057 := by
  rw [gram_eq_of_entries dictionary32 (row3 88 455 410) _ _ _ dictionary_88 dictionary_455 dictionary_410]
  exact (gram021 (![0,0,0,0,0,-8192,8192,7808,35488,15888,7730]) (![0,0,0,0,0,0,18432,16768,10624,11904,3040]) (![0,0,0,0,0,8192,38912,22528,32160,21200,7450])).trans sorted_057
theorem gram_78 : gram (fun a=>dictionary32.getD ((row3 89 429 456) a) 0)=norm_058 := by
  rw [gram_eq_of_entries dictionary32 (row3 89 429 456) _ _ _ dictionary_89 dictionary_429 dictionary_456]
  exact sorted_058
theorem gram_79 : gram (fun a=>dictionary32.getD ((row3 89 456 429) a) 0)=norm_058 := by
  rw [gram_eq_of_entries dictionary32 (row3 89 456 429) _ _ _ dictionary_89 dictionary_456 dictionary_429]
  exact (gram021 (![0,0,0,0,0,-8192,17408,-128,53920,25680,18100]) (![0,0,0,0,0,0,32768,47232,25856,24576,6080]) (![0,0,0,0,0,8192,54272,32768,34080,26640,4260])).trans sorted_058
theorem gram_80 : gram (fun a=>dictionary32.getD ((row3 90 429 457) a) 0)=norm_059 := by
  rw [gram_eq_of_entries dictionary32 (row3 90 429 457) _ _ _ dictionary_90 dictionary_429 dictionary_457]
  exact sorted_059
theorem gram_81 : gram (fun a=>dictionary32.getD ((row3 91 430 458) a) 0)=norm_060 := by
  rw [gram_eq_of_entries dictionary32 (row3 91 430 458) _ _ _ dictionary_91 dictionary_430 dictionary_458]
  exact sorted_060
theorem gram_82 : gram (fun a=>dictionary32.getD ((row3 91 458 430) a) 0)=norm_060 := by
  rw [gram_eq_of_entries dictionary32 (row3 91 458 430) _ _ _ dictionary_91 dictionary_458 dictionary_430]
  exact (gram021 (![0,0,0,0,0,-8192,17408,-128,118720,72480,97300]) (![0,0,0,0,0,0,32768,47232,83456,82176,20480]) (![0,0,0,0,0,8192,54272,32768,98880,73440,83460])).trans sorted_060
theorem gram_83 : gram (fun a=>dictionary32.getD ((row3 92 74 75) a) 0)=norm_050 := by
  rw [gram_eq_of_entries dictionary32 (row3 92 74 75) _ _ _ dictionary_92 dictionary_74 dictionary_75]
  exact (gram201 (![0,0,0,0,0,-12288,-29696,-88192,-56320,-89664,-36704]) (![0,0,0,0,0,-12288,-29696,-87936,-51456,-102592,-44352]) (![0,0,0,0,0,-8192,18432,-63744,-81664,-85120,-31520])).trans sorted_050
theorem gram_84 : gram (fun a=>dictionary32.getD ((row3 92 75 74) a) 0)=norm_050 := by
  rw [gram_eq_of_entries dictionary32 (row3 92 75 74) _ _ _ dictionary_92 dictionary_75 dictionary_74]
  exact (gram210 (![0,0,0,0,0,-12288,-29696,-88192,-56320,-89664,-36704]) (![0,0,0,0,0,-12288,-29696,-87936,-51456,-102592,-44352]) (![0,0,0,0,0,-8192,18432,-63744,-81664,-85120,-31520])).trans sorted_050
theorem gram_85 : gram (fun a=>dictionary32.getD ((row3 93 76 77) a) 0)=norm_051 := by
  rw [gram_eq_of_entries dictionary32 (row3 93 76 77) _ _ _ dictionary_93 dictionary_76 dictionary_77]
  exact (gram201 (![0,0,0,0,0,-12288,-29696,-52864,-14848,-41088,-18368]) (![0,0,0,0,0,-12288,-29696,-50304,-12288,-38848,-17568]) (![0,0,0,0,0,-8192,18432,-29184,-39424,-30400,-10400])).trans sorted_051
theorem gram_86 : gram (fun a=>dictionary32.getD ((row3 93 77 76) a) 0)=norm_051 := by
  rw [gram_eq_of_entries dictionary32 (row3 93 77 76) _ _ _ dictionary_93 dictionary_77 dictionary_76]
  exact (gram210 (![0,0,0,0,0,-12288,-29696,-52864,-14848,-41088,-18368]) (![0,0,0,0,0,-12288,-29696,-50304,-12288,-38848,-17568]) (![0,0,0,0,0,-8192,18432,-29184,-39424,-30400,-10400])).trans sorted_051
theorem gram_87 : gram (fun a=>dictionary32.getD ((row3 94 82 94) a) 0)=norm_054 := by
  rw [gram_eq_of_entries dictionary32 (row3 94 82 94) _ _ _ dictionary_94 dictionary_82 dictionary_94]
  exact (gram102 (![0,0,0,0,0,-10240,-5120,-11520,-5120,-4480,-1600]) (![0,0,0,0,0,-7168,-5632,-14976,-10496,-8160,-2800]) (![0,0,0,0,0,-7168,-5632,-14976,-10496,-8160,-2800])).trans sorted_054
theorem gram_88 : gram (fun a=>dictionary32.getD ((row3 94 94 82) a) 0)=norm_054 := by
  rw [gram_eq_of_entries dictionary32 (row3 94 94 82) _ _ _ dictionary_94 dictionary_94 dictionary_82]
  exact (gram120 (![0,0,0,0,0,-10240,-5120,-11520,-5120,-4480,-1600]) (![0,0,0,0,0,-7168,-5632,-14976,-10496,-8160,-2800]) (![0,0,0,0,0,-7168,-5632,-14976,-10496,-8160,-2800])).trans sorted_054
theorem gram_89 : gram (fun a=>dictionary32.getD ((row3 95 83 96) a) 0)=norm_055 := by
  rw [gram_eq_of_entries dictionary32 (row3 95 83 96) _ _ _ dictionary_95 dictionary_83 dictionary_96]
  exact (gram102 (![0,0,0,0,0,-10240,-5120,-6720,-1920,-1680,-600]) (![0,0,0,0,0,-7168,-5632,-13696,-9216,-7040,-2400]) (![0,0,0,0,0,-7168,-5632,-10176,-7296,-3760,-1000])).trans sorted_055
theorem gram_90 : gram (fun a=>dictionary32.getD ((row3 95 96 83) a) 0)=norm_055 := by
  rw [gram_eq_of_entries dictionary32 (row3 95 96 83) _ _ _ dictionary_95 dictionary_96 dictionary_83]
  exact (gram120 (![0,0,0,0,0,-10240,-5120,-6720,-1920,-1680,-600]) (![0,0,0,0,0,-7168,-5632,-13696,-9216,-7040,-2400]) (![0,0,0,0,0,-7168,-5632,-10176,-7296,-3760,-1000])).trans sorted_055
theorem gram_91 : gram (fun a=>dictionary32.getD ((row3 96 83 95) a) 0)=norm_055 := by
  rw [gram_eq_of_entries dictionary32 (row3 96 83 95) _ _ _ dictionary_96 dictionary_83 dictionary_95]
  exact (gram201 (![0,0,0,0,0,-10240,-5120,-6720,-1920,-1680,-600]) (![0,0,0,0,0,-7168,-5632,-13696,-9216,-7040,-2400]) (![0,0,0,0,0,-7168,-5632,-10176,-7296,-3760,-1000])).trans sorted_055
theorem gram_92 : gram (fun a=>dictionary32.getD ((row3 97 97 105) a) 0)=norm_061 := by
  rw [gram_eq_of_entries dictionary32 (row3 97 97 105) _ _ _ dictionary_97 dictionary_97 dictionary_105]
  exact sorted_061
theorem gram_93 : gram (fun a=>dictionary32.getD ((row3 98 459 98) a) 0)=norm_062 := by
  rw [gram_eq_of_entries dictionary32 (row3 98 459 98) _ _ _ dictionary_98 dictionary_459 dictionary_98]
  exact (gram021 (![0,0,0,0,0,-5120,-1536,-1344,6048,4048,2230]) (![0,0,0,0,0,-5120,-1536,-1344,6048,4048,2230]) (![0,0,0,0,0,10240,12288,8832,5376,4096,960])).trans sorted_062
theorem gram_94 : gram (fun a=>dictionary32.getD ((row3 99 452 355) a) 0)=norm_063 := by
  rw [gram_eq_of_entries dictionary32 (row3 99 452 355) _ _ _ dictionary_99 dictionary_452 dictionary_355]
  exact (gram021 (![0,0,0,0,0,-5120,3328,3712,9936,4296,1910]) (![0,0,0,0,0,0,3840,1280,4880,4200,1550]) (![0,0,0,0,0,5120,9728,8832,5376,4096,960])).trans sorted_063
theorem gram_95 : gram (fun a=>dictionary32.getD ((row3 100 369 453) a) 0)=norm_064 := by
  rw [gram_eq_of_entries dictionary32 (row3 100 369 453) _ _ _ dictionary_100 dictionary_369 dictionary_453]
  exact sorted_064
theorem gram_96 : gram (fun a=>dictionary32.getD ((row3 100 453 369) a) 0)=norm_064 := by
  rw [gram_eq_of_entries dictionary32 (row3 100 453 369) _ _ _ dictionary_100 dictionary_453 dictionary_369]
  exact (gram021 (![0,0,0,0,0,-5120,5888,6272,17216,7936,5820]) (![0,0,0,0,0,0,6400,3840,10560,7040,4460]) (![0,0,0,0,0,5120,9728,8832,6656,5376,1280])).trans sorted_064
theorem gram_97 : gram (fun a=>dictionary32.getD ((row3 101 368 451) a) 0)=norm_065 := by
  rw [gram_eq_of_entries dictionary32 (row3 101 368 451) _ _ _ dictionary_101 dictionary_368 dictionary_451]
  exact sorted_065
theorem gram_98 : gram (fun a=>dictionary32.getD ((row3 101 451 368) a) 0)=norm_065 := by
  rw [gram_eq_of_entries dictionary32 (row3 101 451 368) _ _ _ dictionary_101 dictionary_451 dictionary_368]
  exact (gram021 (![0,0,0,0,0,-5120,5888,7872,14416,6536,4070]) (![0,0,0,0,0,0,6400,3840,9360,6440,3710]) (![0,0,0,0,0,5120,9728,7232,6656,5376,1280])).trans sorted_065
theorem gram_99 : gram (fun a=>dictionary32.getD ((row3 102 69 467) a) 0)=norm_047 := by
  rw [gram_eq_of_entries dictionary32 (row3 102 69 467) _ _ _ dictionary_102 dictionary_69 dictionary_467]
  exact (gram102 (![0,0,0,0,0,-15360,8704,7296,30048,15728,9440]) (![0,0,0,0,0,-5120,9728,4032,19936,15536,8720]) (![0,0,0,0,0,20480,38912,33728,22784,17664,4160])).trans sorted_047
theorem gram_100 : gram (fun a=>dictionary32.getD ((row3 102 467 69) a) 0)=norm_047 := by
  rw [gram_eq_of_entries dictionary32 (row3 102 467 69) _ _ _ dictionary_102 dictionary_467 dictionary_69]
  exact (gram120 (![0,0,0,0,0,-15360,8704,7296,30048,15728,9440]) (![0,0,0,0,0,-5120,9728,4032,19936,15536,8720]) (![0,0,0,0,0,20480,38912,33728,22784,17664,4160])).trans sorted_047
theorem gram_101 : gram (fun a=>dictionary32.getD ((row3 103 449 348) a) 0)=norm_066 := by
  rw [gram_eq_of_entries dictionary32 (row3 103 449 348) _ _ _ dictionary_103 dictionary_449 dictionary_348]
  exact (gram021 (![0,0,0,0,0,-4096,-512,1472,9968,4888,4115]) (![0,0,0,0,0,0,2048,-448,1216,3136,880]) (![0,0,0,0,0,4096,11776,6144,10480,6840,4335])).trans sorted_066
theorem gram_102 : gram (fun a=>dictionary32.getD ((row3 104 407 450) a) 0)=norm_067 := by
  rw [gram_eq_of_entries dictionary32 (row3 104 407 450) _ _ _ dictionary_104 dictionary_407 dictionary_450]
  exact sorted_067
theorem gram_103 : gram (fun a=>dictionary32.getD ((row3 104 450 407) a) 0)=norm_067 := by
  rw [gram_eq_of_entries dictionary32 (row3 104 450 407) _ _ _ dictionary_104 dictionary_450 dictionary_407]
  exact (gram021 (![0,0,0,0,0,-4096,8704,-64,29360,14040,10550]) (![0,0,0,0,0,0,16384,23616,12928,12288,3040]) (![0,0,0,0,0,4096,27136,16384,19440,14520,3630])).trans sorted_067
theorem gram_104 : gram (fun a=>dictionary32.getD ((row3 105 97 97) a) 0)=norm_061 := by
  rw [gram_eq_of_entries dictionary32 (row3 105 97 97) _ _ _ dictionary_105 dictionary_97 dictionary_97]
  exact (gram201 (![0,0,0,0,0,-6144,-14848,-26432,-7424,-16944,-7384]) (![0,0,0,0,0,-6144,-14848,-26432,-7424,-16944,-7384]) (![0,0,0,0,0,-4096,9216,-15872,-20992,-16320,-5600])).trans sorted_061
theorem gram_105 : gram (fun a=>dictionary32.getD ((row3 106 43 478) a) 0)=norm_032 := by
  rw [gram_eq_of_entries dictionary32 (row3 106 43 478) _ _ _ dictionary_106 dictionary_43 dictionary_478]
  exact (gram102 (![0,0,0,0,-8192,-24576,-16896,-16640,-11136,-6080,-1520]) (![0,0,0,0,0,-3072,2560,-5056,-7552,-5440,-1520]) (![0,0,0,0,8192,-1024,-4096,-17472,-14592,-7520,-2000])).trans sorted_032
theorem gram_106 : gram (fun a=>dictionary32.getD ((row3 109 127 401) a) 0)=norm_070 := by
  rw [gram_eq_of_entries dictionary32 (row3 109 127 401) _ _ _ dictionary_109 dictionary_127 dictionary_401]
  exact sorted_070
theorem gram_107 : gram (fun a=>dictionary32.getD ((row3 110 133 402) a) 0)=norm_071 := by
  rw [gram_eq_of_entries dictionary32 (row3 110 133 402) _ _ _ dictionary_110 dictionary_133 dictionary_402]
  exact sorted_071
theorem gram_108 : gram (fun a=>dictionary32.getD ((row3 111 403 145) a) 0)=norm_072 := by
  rw [gram_eq_of_entries dictionary32 (row3 111 403 145) _ _ _ dictionary_111 dictionary_403 dictionary_145]
  exact (gram021 (![0,0,0,0,0,0,-15360,-48000,-11520,-34080,-15600]) (![0,0,0,0,0,0,0,-26240,2560,-26160,-13400]) (![0,0,0,0,0,0,15360,-16640,-24320,-13680,-3800])).trans sorted_072
theorem gram_109 : gram (fun a=>dictionary32.getD ((row3 116 156 377) a) 0)=norm_077 := by
  rw [gram_eq_of_entries dictionary32 (row3 116 156 377) _ _ _ dictionary_116 dictionary_156 dictionary_377]
  exact sorted_077
theorem gram_110 : gram (fun a=>dictionary32.getD ((row3 118 173 364) a) 0)=norm_079 := by
  rw [gram_eq_of_entries dictionary32 (row3 118 173 364) _ _ _ dictionary_118 dictionary_173 dictionary_364]
  exact sorted_079
theorem gram_111 : gram (fun a=>dictionary32.getD ((row3 119 174 364) a) 0)=norm_080 := by
  rw [gram_eq_of_entries dictionary32 (row3 119 174 364) _ _ _ dictionary_119 dictionary_174 dictionary_364]
  exact sorted_080
theorem gram_112 : gram (fun a=>dictionary32.getD ((row3 120 365 183) a) 0)=norm_081 := by
  rw [gram_eq_of_entries dictionary32 (row3 120 365 183) _ _ _ dictionary_120 dictionary_365 dictionary_183]
  exact (gram021 (![0,0,0,0,0,0,-5120,-16000,-3840,-8160,-3600]) (![0,0,0,0,0,0,0,-9600,0,-6000,-3000]) (![0,0,0,0,0,0,5120,-6400,-8960,-5040,-1400])).trans sorted_081
theorem gram_113 : gram (fun a=>dictionary32.getD ((row3 124 460 67) a) 0)=norm_045 := by
  rw [gram_eq_of_entries dictionary32 (row3 124 460 67) _ _ _ dictionary_124 dictionary_460 dictionary_67]
  exact (gram120 (![0,0,0,0,0,-15360,512,4928,16144,7144,3365]) (![0,0,0,0,0,0,-2560,-6400,4240,5800,2825]) (![0,0,0,0,0,15360,18432,13248,8064,6144,1440])).trans sorted_045
theorem gram_114 : gram (fun a=>dictionary32.getD ((row3 126 107 427) a) 0)=norm_068 := by
  rw [gram_eq_of_entries dictionary32 (row3 126 107 427) _ _ _ dictionary_126 dictionary_107 dictionary_427]
  exact (gram102 (![0,0,0,0,0,0,-30720,-111360,-38400,-91200,-40800]) (![0,0,0,0,0,0,0,-71424,-16896,-76128,-35568]) (![0,0,0,0,0,0,30720,-52224,-70656,-70368,-25968])).trans sorted_068
theorem gram_115 : gram (fun a=>dictionary32.getD ((row3 126 427 107) a) 0)=norm_068 := by
  rw [gram_eq_of_entries dictionary32 (row3 126 427 107) _ _ _ dictionary_126 dictionary_427 dictionary_107]
  exact (gram120 (![0,0,0,0,0,0,-30720,-111360,-38400,-91200,-40800]) (![0,0,0,0,0,0,0,-71424,-16896,-76128,-35568]) (![0,0,0,0,0,0,30720,-52224,-70656,-70368,-25968])).trans sorted_068
theorem gram_116 : gram (fun a=>dictionary32.getD ((row3 127 109 401) a) 0)=norm_070 := by
  rw [gram_eq_of_entries dictionary32 (row3 127 109 401) _ _ _ dictionary_127 dictionary_109 dictionary_401]
  exact (gram102 (![0,0,0,0,0,0,-15360,-78720,-42240,-96960,-43200]) (![0,0,0,0,0,0,0,-64128,-41472,-84576,-36336]) (![0,0,0,0,0,0,15360,-54528,-68352,-86496,-33936])).trans sorted_070
theorem gram_117 : gram (fun a=>dictionary32.getD ((row3 128 130 130) a) 0)=norm_086 := by
  rw [gram_eq_of_entries dictionary32 (row3 128 130 130) _ _ _ dictionary_128 dictionary_130 dictionary_130]
  exact sorted_086
theorem gram_118 : gram (fun a=>dictionary32.getD ((row3 129 15 244) a) 0)=norm_012 := by
  rw [gram_eq_of_entries dictionary32 (row3 129 15 244) _ _ _ dictionary_129 dictionary_15 dictionary_244]
  exact (gram102 (![0,0,0,0,0,0,0,57600,0,0,0]) (![0,0,0,0,0,0,0,-57600,43200,21600,31500]) (![0,0,0,0,0,0,0,0,-14400,-7200,13500])).trans sorted_012
theorem gram_119 : gram (fun a=>dictionary32.getD ((row3 130 130 128) a) 0)=norm_086 := by
  rw [gram_eq_of_entries dictionary32 (row3 130 130 128) _ _ _ dictionary_130 dictionary_130 dictionary_128]
  exact (gram120 (![0,0,0,0,0,0,0,-58368,-64512,-128736,-55536]) (![0,0,0,0,0,0,0,-56832,-66048,-126624,-53904]) (![0,0,0,0,0,0,0,-56832,-66048,-126624,-53904])).trans sorted_086
theorem gram_120 : gram (fun a=>dictionary32.getD ((row3 131 132 147) a) 0)=norm_087 := by
  rw [gram_eq_of_entries dictionary32 (row3 131 132 147) _ _ _ dictionary_131 dictionary_132 dictionary_147]
  exact sorted_087
theorem gram_121 : gram (fun a=>dictionary32.getD ((row3 133 110 402) a) 0)=norm_071 := by
  rw [gram_eq_of_entries dictionary32 (row3 133 110 402) _ _ _ dictionary_133 dictionary_110 dictionary_402]
  exact (gram102 (![0,0,0,0,0,0,-15360,-48000,-11520,-41280,-19200]) (![0,0,0,0,0,0,0,-36480,-7680,-37920,-18000]) (![0,0,0,0,0,0,15360,-26880,-34560,-30240,-10800])).trans sorted_071
theorem gram_122 : gram (fun a=>dictionary32.getD ((row3 134 134 135) a) 0)=norm_088 := by
  rw [gram_eq_of_entries dictionary32 (row3 134 134 135) _ _ _ dictionary_134 dictionary_134 dictionary_135]
  exact sorted_088
theorem gram_123 : gram (fun a=>dictionary32.getD ((row3 135 134 134) a) 0)=norm_088 := by
  rw [gram_eq_of_entries dictionary32 (row3 135 134 134) _ _ _ dictionary_135 dictionary_134 dictionary_134]
  exact (gram201 (![0,0,0,0,0,0,0,-33792,-37888,-73744,-31624]) (![0,0,0,0,0,0,0,-33792,-37888,-73744,-31624]) (![0,0,0,0,0,0,0,-32768,-38912,-56336,-22536])).trans sorted_088
theorem gram_124 : gram (fun a=>dictionary32.getD ((row3 136 136 144) a) 0)=norm_089 := by
  rw [gram_eq_of_entries dictionary32 (row3 136 136 144) _ _ _ dictionary_136 dictionary_136 dictionary_144]
  exact sorted_089
theorem gram_125 : gram (fun a=>dictionary32.getD ((row3 137 138 143) a) 0)=norm_090 := by
  rw [gram_eq_of_entries dictionary32 (row3 137 138 143) _ _ _ dictionary_137 dictionary_138 dictionary_143]
  exact sorted_090
theorem gram_126 : gram (fun a=>dictionary32.getD ((row3 139 139 159) a) 0)=norm_091 := by
  rw [gram_eq_of_entries dictionary32 (row3 139 139 159) _ _ _ dictionary_139 dictionary_139 dictionary_159]
  exact sorted_091
theorem gram_127 : gram (fun a=>dictionary32.getD ((row3 139 159 139) a) 0)=norm_091 := by
  rw [gram_eq_of_entries dictionary32 (row3 139 159 139) _ _ _ dictionary_139 dictionary_159 dictionary_139]
  exact (gram021 (![0,0,0,0,0,0,0,-29184,-32256,-34368,-12768]) (![0,0,0,0,0,0,0,-29184,-32256,-34368,-12768]) (![0,0,0,0,0,0,0,-15360,-15360,-42240,-19200])).trans sorted_091
open QuarticIntegerData QuarticIntegerMembership32 QuarticIntegerNormSorted32
open QuarticIntegerListAggregates QuarticIntegerNorm QuarticIntegerGramPermutation
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem gram_128 : gram (fun a=>dictionary32.getD ((row3 140 162 140) a) 0)=norm_092 := by
  rw [gram_eq_of_entries dictionary32 (row3 140 162 140) _ _ _ dictionary_140 dictionary_162 dictionary_140]
  exact (gram021 (![0,0,0,0,0,0,0,-29184,-32256,-29568,-10368]) (![0,0,0,0,0,0,0,-29184,-32256,-29568,-10368]) (![0,0,0,0,0,0,0,-15360,-15360,-32640,-14400])).trans sorted_092
theorem gram_129 : gram (fun a=>dictionary32.getD ((row3 141 14 245) a) 0)=norm_010 := by
  rw [gram_eq_of_entries dictionary32 (row3 141 14 245) _ _ _ dictionary_141 dictionary_14 dictionary_245]
  exact (gram102 (![0,0,0,0,0,0,0,28800,0,0,0]) (![0,0,0,0,0,0,0,-28800,16800,8400,5250]) (![0,0,0,0,0,0,0,0,-12000,-6000,-3750])).trans sorted_010
theorem gram_130 : gram (fun a=>dictionary32.getD ((row3 142 14 333) a) 0)=norm_011 := by
  rw [gram_eq_of_entries dictionary32 (row3 142 14 333) _ _ _ dictionary_142 dictionary_14 dictionary_333]
  exact (gram102 (![0,0,0,0,0,0,0,28800,0,0,0]) (![0,0,0,0,0,0,0,-28800,50400,25200,31500]) (![0,0,0,0,0,0,0,0,21600,10800,13500])).trans sorted_011
theorem gram_131 : gram (fun a=>dictionary32.getD ((row3 142 333 14) a) 0)=norm_011 := by
  rw [gram_eq_of_entries dictionary32 (row3 142 333 14) _ _ _ dictionary_142 dictionary_333 dictionary_14]
  exact (gram120 (![0,0,0,0,0,0,0,28800,0,0,0]) (![0,0,0,0,0,0,0,-28800,50400,25200,31500]) (![0,0,0,0,0,0,0,0,21600,10800,13500])).trans sorted_011
theorem gram_132 : gram (fun a=>dictionary32.getD ((row3 143 138 137) a) 0)=norm_090 := by
  rw [gram_eq_of_entries dictionary32 (row3 143 138 137) _ _ _ dictionary_143 dictionary_138 dictionary_137]
  exact (gram210 (![0,0,0,0,0,0,0,-29184,-32256,-58368,-24768]) (![0,0,0,0,0,0,0,-29184,-32256,-53568,-22368]) (![0,0,0,0,0,0,0,-27648,-33792,-46656,-18336])).trans sorted_090
theorem gram_133 : gram (fun a=>dictionary32.getD ((row3 144 136 136) a) 0)=norm_089 := by
  rw [gram_eq_of_entries dictionary32 (row3 144 136 136) _ _ _ dictionary_144 dictionary_136 dictionary_136]
  exact (gram201 (![0,0,0,0,0,0,0,-29184,-32256,-63168,-27168]) (![0,0,0,0,0,0,0,-29184,-32256,-63168,-27168]) (![0,0,0,0,0,0,0,-27648,-33792,-41856,-15936])).trans sorted_089
theorem gram_134 : gram (fun a=>dictionary32.getD ((row3 145 111 403) a) 0)=norm_072 := by
  rw [gram_eq_of_entries dictionary32 (row3 145 111 403) _ _ _ dictionary_145 dictionary_111 dictionary_403]
  exact (gram102 (![0,0,0,0,0,0,-15360,-48000,-11520,-34080,-15600]) (![0,0,0,0,0,0,0,-26240,2560,-26160,-13400]) (![0,0,0,0,0,0,15360,-16640,-24320,-13680,-3800])).trans sorted_072
theorem gram_135 : gram (fun a=>dictionary32.getD ((row3 145 403 111) a) 0)=norm_072 := by
  rw [gram_eq_of_entries dictionary32 (row3 145 403 111) _ _ _ dictionary_145 dictionary_403 dictionary_111]
  exact (gram120 (![0,0,0,0,0,0,-15360,-48000,-11520,-34080,-15600]) (![0,0,0,0,0,0,0,-26240,2560,-26160,-13400]) (![0,0,0,0,0,0,15360,-16640,-24320,-13680,-3800])).trans sorted_072
theorem gram_136 : gram (fun a=>dictionary32.getD ((row3 147 132 131) a) 0)=norm_087 := by
  rw [gram_eq_of_entries dictionary32 (row3 147 132 131) _ _ _ dictionary_147 dictionary_132 dictionary_131]
  exact (gram210 (![0,0,0,0,0,0,0,-40320,-11520,-53280,-25200]) (![0,0,0,0,0,0,0,-40320,-11520,-29280,-13200]) (![0,0,0,0,0,0,0,-23040,-23040,-46560,-20400])).trans sorted_087
theorem gram_137 : gram (fun a=>dictionary32.getD ((row3 148 163 210) a) 0)=norm_093 := by
  rw [gram_eq_of_entries dictionary32 (row3 148 163 210) _ _ _ dictionary_148 dictionary_163 dictionary_210]
  exact sorted_093
theorem gram_138 : gram (fun a=>dictionary32.getD ((row3 149 149 179) a) 0)=norm_094 := by
  rw [gram_eq_of_entries dictionary32 (row3 149 149 179) _ _ _ dictionary_149 dictionary_149 dictionary_179]
  exact sorted_094
theorem gram_139 : gram (fun a=>dictionary32.getD ((row3 150 150 180) a) 0)=norm_095 := by
  rw [gram_eq_of_entries dictionary32 (row3 150 150 180) _ _ _ dictionary_150 dictionary_150 dictionary_180]
  exact sorted_095
theorem gram_140 : gram (fun a=>dictionary32.getD ((row3 151 152 155) a) 0)=norm_096 := by
  rw [gram_eq_of_entries dictionary32 (row3 151 152 155) _ _ _ dictionary_151 dictionary_152 dictionary_155]
  exact sorted_096
theorem gram_141 : gram (fun a=>dictionary32.getD ((row3 151 155 152) a) 0)=norm_096 := by
  rw [gram_eq_of_entries dictionary32 (row3 151 155 152) _ _ _ dictionary_151 dictionary_155 dictionary_152]
  exact (gram021 (![0,0,0,0,0,0,0,-19968,-20992,-39616,-17056]) (![0,0,0,0,0,0,0,-18944,-22016,-33408,-13568]) (![0,0,0,0,0,0,0,-18432,-22528,-29504,-11424])).trans sorted_096
theorem gram_142 : gram (fun a=>dictionary32.getD ((row3 152 155 151) a) 0)=norm_096 := by
  rw [gram_eq_of_entries dictionary32 (row3 152 155 151) _ _ _ dictionary_152 dictionary_155 dictionary_151]
  exact (gram120 (![0,0,0,0,0,0,0,-19968,-20992,-39616,-17056]) (![0,0,0,0,0,0,0,-18944,-22016,-33408,-13568]) (![0,0,0,0,0,0,0,-18432,-22528,-29504,-11424])).trans sorted_096
theorem gram_143 : gram (fun a=>dictionary32.getD ((row3 153 161 154) a) 0)=norm_097 := by
  rw [gram_eq_of_entries dictionary32 (row3 153 161 154) _ _ _ dictionary_153 dictionary_161 dictionary_154]
  exact (gram021 (![0,0,0,0,0,0,0,-18944,-22016,-30208,-11968]) (![0,0,0,0,0,0,0,-18944,-22016,-25408,-9568]) (![0,0,0,0,0,0,0,-15360,-15360,-37440,-16800])).trans sorted_097
theorem gram_144 : gram (fun a=>dictionary32.getD ((row3 154 153 161) a) 0)=norm_097 := by
  rw [gram_eq_of_entries dictionary32 (row3 154 153 161) _ _ _ dictionary_154 dictionary_153 dictionary_161]
  exact (gram102 (![0,0,0,0,0,0,0,-18944,-22016,-30208,-11968]) (![0,0,0,0,0,0,0,-18944,-22016,-25408,-9568]) (![0,0,0,0,0,0,0,-15360,-15360,-37440,-16800])).trans sorted_097
theorem gram_145 : gram (fun a=>dictionary32.getD ((row3 154 161 153) a) 0)=norm_097 := by
  rw [gram_eq_of_entries dictionary32 (row3 154 161 153) _ _ _ dictionary_154 dictionary_161 dictionary_153]
  exact (gram120 (![0,0,0,0,0,0,0,-18944,-22016,-30208,-11968]) (![0,0,0,0,0,0,0,-18944,-22016,-25408,-9568]) (![0,0,0,0,0,0,0,-15360,-15360,-37440,-16800])).trans sorted_097
theorem gram_146 : gram (fun a=>dictionary32.getD ((row3 155 152 151) a) 0)=norm_096 := by
  rw [gram_eq_of_entries dictionary32 (row3 155 152 151) _ _ _ dictionary_155 dictionary_152 dictionary_151]
  exact (gram210 (![0,0,0,0,0,0,0,-19968,-20992,-39616,-17056]) (![0,0,0,0,0,0,0,-18944,-22016,-33408,-13568]) (![0,0,0,0,0,0,0,-18432,-22528,-29504,-11424])).trans sorted_096
theorem gram_147 : gram (fun a=>dictionary32.getD ((row3 156 116 377) a) 0)=norm_077 := by
  rw [gram_eq_of_entries dictionary32 (row3 156 116 377) _ _ _ dictionary_156 dictionary_116 dictionary_377]
  exact (gram102 (![0,0,0,0,0,0,-7680,-24000,-5760,-15840,-7200]) (![0,0,0,0,0,0,0,-18240,-3840,-14160,-6600]) (![0,0,0,0,0,0,7680,-13440,-17280,-15120,-5400])).trans sorted_077
theorem gram_148 : gram (fun a=>dictionary32.getD ((row3 157 108 428) a) 0)=norm_069 := by
  rw [gram_eq_of_entries dictionary32 (row3 157 108 428) _ _ _ dictionary_157 dictionary_108 dictionary_428]
  exact (gram102 (![0,0,0,0,0,0,-30720,-55680,-11520,-29280,-13200]) (![0,0,0,0,0,0,0,-17280,11520,-16320,-9600]) (![0,0,0,0,0,0,30720,-15360,-30720,-17280,-4800])).trans sorted_069
theorem gram_149 : gram (fun a=>dictionary32.getD ((row3 158 168 167) a) 0)=norm_098 := by
  rw [gram_eq_of_entries dictionary32 (row3 158 168 167) _ _ _ dictionary_158 dictionary_168 dictionary_167]
  exact (gram021 (![0,0,0,0,0,0,0,-15360,-15360,-80640,-38400]) (![0,0,0,0,0,0,0,-13824,-16896,-78528,-36768]) (![0,0,0,0,0,0,0,-13824,-16896,-73728,-34368])).trans sorted_098
theorem gram_150 : gram (fun a=>dictionary32.getD ((row3 161 153 154) a) 0)=norm_097 := by
  rw [gram_eq_of_entries dictionary32 (row3 161 153 154) _ _ _ dictionary_161 dictionary_153 dictionary_154]
  exact (gram201 (![0,0,0,0,0,0,0,-18944,-22016,-30208,-11968]) (![0,0,0,0,0,0,0,-18944,-22016,-25408,-9568]) (![0,0,0,0,0,0,0,-15360,-15360,-37440,-16800])).trans sorted_097
theorem gram_151 : gram (fun a=>dictionary32.getD ((row3 163 148 210) a) 0)=norm_093 := by
  rw [gram_eq_of_entries dictionary32 (row3 163 148 210) _ _ _ dictionary_163 dictionary_148 dictionary_210]
  exact (gram102 (![0,0,0,0,0,0,0,-20480,-20480,-13120,-4000]) (![0,0,0,0,0,0,0,-15360,-15360,-8640,-2400]) (![0,0,0,0,0,0,0,-5120,-5120,-4480,-1600])).trans sorted_093
theorem gram_152 : gram (fun a=>dictionary32.getD ((row3 164 13 246) a) 0)=norm_007 := by
  rw [gram_eq_of_entries dictionary32 (row3 164 13 246) _ _ _ dictionary_164 dictionary_13 dictionary_246]
  exact (gram102 (![0,0,0,0,0,0,0,14400,0,0,0]) (![0,0,0,0,0,0,0,-14400,6000,3000,1875]) (![0,0,0,0,0,0,0,0,-8400,-4200,-2625])).trans sorted_007
theorem gram_153 : gram (fun a=>dictionary32.getD ((row3 165 13 247) a) 0)=norm_008 := by
  rw [gram_eq_of_entries dictionary32 (row3 165 13 247) _ _ _ dictionary_165 dictionary_13 dictionary_247]
  exact (gram102 (![0,0,0,0,0,0,0,14400,0,0,0]) (![0,0,0,0,0,0,0,-14400,6000,3000,4875]) (![0,0,0,0,0,0,0,0,-8400,-4200,375])).trans sorted_008
theorem gram_154 : gram (fun a=>dictionary32.getD ((row3 166 13 320) a) 0)=norm_009 := by
  rw [gram_eq_of_entries dictionary32 (row3 166 13 320) _ _ _ dictionary_166 dictionary_13 dictionary_320]
  exact (gram102 (![0,0,0,0,0,0,0,14400,0,0,0]) (![0,0,0,0,0,0,0,-14400,25200,12600,15750]) (![0,0,0,0,0,0,0,0,10800,5400,6750])).trans sorted_009
theorem gram_155 : gram (fun a=>dictionary32.getD ((row3 166 320 13) a) 0)=norm_009 := by
  rw [gram_eq_of_entries dictionary32 (row3 166 320 13) _ _ _ dictionary_166 dictionary_320 dictionary_13]
  exact (gram120 (![0,0,0,0,0,0,0,14400,0,0,0]) (![0,0,0,0,0,0,0,-14400,25200,12600,15750]) (![0,0,0,0,0,0,0,0,10800,5400,6750])).trans sorted_009
theorem gram_156 : gram (fun a=>dictionary32.getD ((row3 167 168 158) a) 0)=norm_098 := by
  rw [gram_eq_of_entries dictionary32 (row3 167 168 158) _ _ _ dictionary_167 dictionary_168 dictionary_158]
  exact (gram120 (![0,0,0,0,0,0,0,-15360,-15360,-80640,-38400]) (![0,0,0,0,0,0,0,-13824,-16896,-78528,-36768]) (![0,0,0,0,0,0,0,-13824,-16896,-73728,-34368])).trans sorted_098
theorem gram_157 : gram (fun a=>dictionary32.getD ((row3 169 160 169) a) 0)=norm_099 := by
  rw [gram_eq_of_entries dictionary32 (row3 169 160 169) _ _ _ dictionary_169 dictionary_160 dictionary_169]
  exact (gram102 (![0,0,0,0,0,0,0,-15360,-15360,-39840,-18000]) (![0,0,0,0,0,0,0,-13824,-16896,-61728,-28368]) (![0,0,0,0,0,0,0,-13824,-16896,-61728,-28368])).trans sorted_099
theorem gram_158 : gram (fun a=>dictionary32.getD ((row3 170 170 190) a) 0)=norm_100 := by
  rw [gram_eq_of_entries dictionary32 (row3 170 170 190) _ _ _ dictionary_170 dictionary_170 dictionary_190]
  exact sorted_100
theorem gram_159 : gram (fun a=>dictionary32.getD ((row3 171 122 350) a) 0)=norm_083 := by
  rw [gram_eq_of_entries dictionary32 (row3 171 122 350) _ _ _ dictionary_171 dictionary_122 dictionary_350]
  exact (gram102 (![0,0,0,0,0,0,-2560,-15680,-9600,-24000,-10800]) (![0,0,0,0,0,0,0,-12992,-9728,-16784,-6984]) (![0,0,0,0,0,0,2560,-11392,-14208,-19504,-7784])).trans sorted_083
theorem gram_160 : gram (fun a=>dictionary32.getD ((row3 172 175 178) a) 0)=norm_101 := by
  rw [gram_eq_of_entries dictionary32 (row3 172 175 178) _ _ _ dictionary_172 dictionary_175 dictionary_178]
  exact sorted_101
theorem gram_161 : gram (fun a=>dictionary32.getD ((row3 173 118 364) a) 0)=norm_079 := by
  rw [gram_eq_of_entries dictionary32 (row3 173 118 364) _ _ _ dictionary_173 dictionary_118 dictionary_364]
  exact (gram102 (![0,0,0,0,0,0,-5120,-16000,-3840,-39360,-19200]) (![0,0,0,0,0,0,0,-12160,-2560,-38240,-18800]) (![0,0,0,0,0,0,5120,-8960,-11520,-10080,-3600])).trans sorted_079
theorem gram_162 : gram (fun a=>dictionary32.getD ((row3 174 119 364) a) 0)=norm_080 := by
  rw [gram_eq_of_entries dictionary32 (row3 174 119 364) _ _ _ dictionary_174 dictionary_119 dictionary_364]
  exact (gram102 (![0,0,0,0,0,0,-5120,-16000,-3840,-10560,-4800]) (![0,0,0,0,0,0,0,-12160,-2560,-9440,-4400]) (![0,0,0,0,0,0,5120,-8960,-11520,-10080,-3600])).trans sorted_080
theorem gram_163 : gram (fun a=>dictionary32.getD ((row3 176 188 177) a) 0)=norm_102 := by
  rw [gram_eq_of_entries dictionary32 (row3 176 188 177) _ _ _ dictionary_176 dictionary_188 dictionary_177]
  exact (gram021 (![0,0,0,0,0,0,0,-12032,-13568,-15744,-5984]) (![0,0,0,0,0,0,0,-12032,-13568,-13344,-4784]) (![0,0,0,0,0,0,0,-7680,-7680,-18720,-8400])).trans sorted_102
theorem gram_164 : gram (fun a=>dictionary32.getD ((row3 177 188 176) a) 0)=norm_102 := by
  rw [gram_eq_of_entries dictionary32 (row3 177 188 176) _ _ _ dictionary_177 dictionary_188 dictionary_176]
  exact (gram120 (![0,0,0,0,0,0,0,-12032,-13568,-15744,-5984]) (![0,0,0,0,0,0,0,-12032,-13568,-13344,-4784]) (![0,0,0,0,0,0,0,-7680,-7680,-18720,-8400])).trans sorted_102
theorem gram_165 : gram (fun a=>dictionary32.getD ((row3 178 175 172) a) 0)=norm_101 := by
  rw [gram_eq_of_entries dictionary32 (row3 178 175 172) _ _ _ dictionary_178 dictionary_175 dictionary_172]
  exact (gram210 (![0,0,0,0,0,0,0,-12288,-13312,-25696,-11056]) (![0,0,0,0,0,0,0,-12032,-13568,-21344,-8784]) (![0,0,0,0,0,0,0,-11520,-14080,-19840,-7840])).trans sorted_101
theorem gram_166 : gram (fun a=>dictionary32.getD ((row3 179 149 149) a) 0)=norm_094 := by
  rw [gram_eq_of_entries dictionary32 (row3 179 149 149) _ _ _ dictionary_179 dictionary_149 dictionary_149]
  exact (gram201 (![0,0,0,0,0,0,0,-20160,-5760,-17040,-7800]) (![0,0,0,0,0,0,0,-20160,-5760,-17040,-7800]) (![0,0,0,0,0,0,0,-11520,-11520,-16080,-6600])).trans sorted_094
theorem gram_167 : gram (fun a=>dictionary32.getD ((row3 180 150 150) a) 0)=norm_095 := by
  rw [gram_eq_of_entries dictionary32 (row3 180 150 150) _ _ _ dictionary_180 dictionary_150 dictionary_150]
  exact (gram201 (![0,0,0,0,0,0,0,-20160,-5760,-15840,-7200]) (![0,0,0,0,0,0,0,-20160,-5760,-15840,-7200]) (![0,0,0,0,0,0,0,-11520,-11520,-10080,-3600])).trans sorted_095
theorem gram_168 : gram (fun a=>dictionary32.getD ((row3 181 210 210) a) 0)=norm_103 := by
  rw [gram_eq_of_entries dictionary32 (row3 181 210 210) _ _ _ dictionary_181 dictionary_210 dictionary_210]
  exact sorted_103
theorem gram_169 : gram (fun a=>dictionary32.getD ((row3 182 182 231) a) 0)=norm_104 := by
  rw [gram_eq_of_entries dictionary32 (row3 182 182 231) _ _ _ dictionary_182 dictionary_182 dictionary_231]
  exact sorted_104
theorem gram_170 : gram (fun a=>dictionary32.getD ((row3 182 231 182) a) 0)=norm_104 := by
  rw [gram_eq_of_entries dictionary32 (row3 182 231 182) _ _ _ dictionary_182 dictionary_231 dictionary_182]
  exact (gram021 (![0,0,0,0,0,0,0,-9984,-10496,-8608,-2928]) (![0,0,0,0,0,0,0,-9984,-10496,-8608,-2928]) (![0,0,0,0,0,0,0,-2560,-2560,-7040,-3200])).trans sorted_104
theorem gram_171 : gram (fun a=>dictionary32.getD ((row3 183 120 365) a) 0)=norm_081 := by
  rw [gram_eq_of_entries dictionary32 (row3 183 120 365) _ _ _ dictionary_183 dictionary_120 dictionary_365]
  exact (gram102 (![0,0,0,0,0,0,-5120,-16000,-3840,-8160,-3600]) (![0,0,0,0,0,0,0,-9600,0,-6000,-3000]) (![0,0,0,0,0,0,5120,-6400,-8960,-5040,-1400])).trans sorted_081
theorem gram_172 : gram (fun a=>dictionary32.getD ((row3 183 365 120) a) 0)=norm_081 := by
  rw [gram_eq_of_entries dictionary32 (row3 183 365 120) _ _ _ dictionary_183 dictionary_365 dictionary_120]
  exact (gram120 (![0,0,0,0,0,0,-5120,-16000,-3840,-8160,-3600]) (![0,0,0,0,0,0,0,-9600,0,-6000,-3000]) (![0,0,0,0,0,0,5120,-6400,-8960,-5040,-1400])).trans sorted_081
theorem gram_173 : gram (fun a=>dictionary32.getD ((row3 184 12 248) a) 0)=norm_006 := by
  rw [gram_eq_of_entries dictionary32 (row3 184 12 248) _ _ _ dictionary_184 dictionary_12 dictionary_248]
  exact (gram102 (![0,0,0,0,0,0,0,9600,0,0,0]) (![0,0,0,0,0,0,0,-9600,7200,3600,2250]) (![0,0,0,0,0,0,0,0,-2400,-1200,-750])).trans sorted_006
theorem gram_174 : gram (fun a=>dictionary32.getD ((row3 185 186 188) a) 0)=norm_105 := by
  rw [gram_eq_of_entries dictionary32 (row3 185 186 188) _ _ _ dictionary_185 dictionary_186 dictionary_188]
  exact sorted_105
theorem gram_175 : gram (fun a=>dictionary32.getD ((row3 185 188 186) a) 0)=norm_105 := by
  rw [gram_eq_of_entries dictionary32 (row3 185 188 186) _ _ _ dictionary_185 dictionary_188 dictionary_186]
  exact (gram021 (![0,0,0,0,0,0,0,-9472,-11008,-15104,-5984]) (![0,0,0,0,0,0,0,-9472,-11008,-12704,-4784]) (![0,0,0,0,0,0,0,-7680,-7680,-18720,-8400])).trans sorted_105
theorem gram_176 : gram (fun a=>dictionary32.getD ((row3 186 188 185) a) 0)=norm_105 := by
  rw [gram_eq_of_entries dictionary32 (row3 186 188 185) _ _ _ dictionary_186 dictionary_188 dictionary_185]
  exact (gram120 (![0,0,0,0,0,0,0,-9472,-11008,-15104,-5984]) (![0,0,0,0,0,0,0,-9472,-11008,-12704,-4784]) (![0,0,0,0,0,0,0,-7680,-7680,-18720,-8400])).trans sorted_105
theorem gram_177 : gram (fun a=>dictionary32.getD ((row3 187 192 192) a) 0)=norm_106 := by
  rw [gram_eq_of_entries dictionary32 (row3 187 192 192) _ _ _ dictionary_187 dictionary_192 dictionary_192]
  exact sorted_106
theorem gram_178 : gram (fun a=>dictionary32.getD ((row3 187 195 195) a) 0)=norm_107 := by
  rw [gram_eq_of_entries dictionary32 (row3 187 195 195) _ _ _ dictionary_187 dictionary_195 dictionary_195]
  exact sorted_107
theorem gram_179 : gram (fun a=>dictionary32.getD ((row3 188 186 185) a) 0)=norm_105 := by
  rw [gram_eq_of_entries dictionary32 (row3 188 186 185) _ _ _ dictionary_188 dictionary_186 dictionary_185]
  exact (gram210 (![0,0,0,0,0,0,0,-9472,-11008,-15104,-5984]) (![0,0,0,0,0,0,0,-9472,-11008,-12704,-4784]) (![0,0,0,0,0,0,0,-7680,-7680,-18720,-8400])).trans sorted_105
theorem gram_180 : gram (fun a=>dictionary32.getD ((row3 188 197 196) a) 0)=norm_109 := by
  rw [gram_eq_of_entries dictionary32 (row3 188 197 196) _ _ _ dictionary_188 dictionary_197 dictionary_196]
  exact (gram021 (![0,0,0,0,0,0,0,-7680,-7680,-18720,-8400]) (![0,0,0,0,0,0,0,-6912,-8448,-12864,-5184]) (![0,0,0,0,0,0,0,-6912,-8448,-10464,-3984])).trans sorted_109
theorem gram_181 : gram (fun a=>dictionary32.getD ((row3 190 170 170) a) 0)=norm_100 := by
  rw [gram_eq_of_entries dictionary32 (row3 190 170 170) _ _ _ dictionary_190 dictionary_170 dictionary_170]
  exact (gram201 (![0,0,0,0,0,0,0,-13440,-3840,-8160,-3600]) (![0,0,0,0,0,0,0,-13440,-3840,-8160,-3600]) (![0,0,0,0,0,0,0,-7680,-7680,-4320,-1200])).trans sorted_100
theorem gram_182 : gram (fun a=>dictionary32.getD ((row3 190 190 508) a) 0)=norm_111 := by
  rw [gram_eq_of_entries dictionary32 (row3 190 190 508) _ _ _ dictionary_190 dictionary_190 dictionary_508]
  exact sorted_111
theorem gram_183 : gram (fun a=>dictionary32.getD ((row3 191 468 49) a) 0)=norm_036 := by
  rw [gram_eq_of_entries dictionary32 (row3 191 468 49) _ _ _ dictionary_191 dictionary_468 dictionary_49]
  exact (gram120 (![0,0,0,0,0,-30720,6144,14976,36768,15888,7230]) (![0,0,0,0,0,0,0,-7680,12960,13200,6150]) (![0,0,0,0,0,30720,36864,26496,16128,12288,2880])).trans sorted_036
theorem gram_184 : gram (fun a=>dictionary32.getD ((row3 192 187 192) a) 0)=norm_106 := by
  rw [gram_eq_of_entries dictionary32 (row3 192 187 192) _ _ _ dictionary_192 dictionary_187 dictionary_192]
  exact (gram102 (![0,0,0,0,0,0,0,-7680,-7680,-21120,-9600]) (![0,0,0,0,0,0,0,-6912,-8448,-27264,-12384]) (![0,0,0,0,0,0,0,-6912,-8448,-27264,-12384])).trans sorted_106
theorem gram_185 : gram (fun a=>dictionary32.getD ((row3 192 192 187) a) 0)=norm_106 := by
  rw [gram_eq_of_entries dictionary32 (row3 192 192 187) _ _ _ dictionary_192 dictionary_192 dictionary_187]
  exact (gram120 (![0,0,0,0,0,0,0,-7680,-7680,-21120,-9600]) (![0,0,0,0,0,0,0,-6912,-8448,-27264,-12384]) (![0,0,0,0,0,0,0,-6912,-8448,-27264,-12384])).trans sorted_106
theorem gram_186 : gram (fun a=>dictionary32.getD ((row3 193 188 194) a) 0)=norm_108 := by
  rw [gram_eq_of_entries dictionary32 (row3 193 188 194) _ _ _ dictionary_193 dictionary_188 dictionary_194]
  exact (gram102 (![0,0,0,0,0,0,0,-7680,-7680,-18720,-8400]) (![0,0,0,0,0,0,0,-6912,-8448,-22464,-9984]) (![0,0,0,0,0,0,0,-6912,-8448,-20064,-8784])).trans sorted_108
theorem gram_187 : gram (fun a=>dictionary32.getD ((row3 194 188 193) a) 0)=norm_108 := by
  rw [gram_eq_of_entries dictionary32 (row3 194 188 193) _ _ _ dictionary_194 dictionary_188 dictionary_193]
  exact (gram201 (![0,0,0,0,0,0,0,-7680,-7680,-18720,-8400]) (![0,0,0,0,0,0,0,-6912,-8448,-22464,-9984]) (![0,0,0,0,0,0,0,-6912,-8448,-20064,-8784])).trans sorted_108
theorem gram_188 : gram (fun a=>dictionary32.getD ((row3 195 195 187) a) 0)=norm_107 := by
  rw [gram_eq_of_entries dictionary32 (row3 195 195 187) _ _ _ dictionary_195 dictionary_195 dictionary_187]
  exact (gram120 (![0,0,0,0,0,0,0,-7680,-7680,-21120,-9600]) (![0,0,0,0,0,0,0,-6912,-8448,-15264,-6384]) (![0,0,0,0,0,0,0,-6912,-8448,-15264,-6384])).trans sorted_107
theorem gram_189 : gram (fun a=>dictionary32.getD ((row3 196 197 188) a) 0)=norm_109 := by
  rw [gram_eq_of_entries dictionary32 (row3 196 197 188) _ _ _ dictionary_196 dictionary_197 dictionary_188]
  exact (gram120 (![0,0,0,0,0,0,0,-7680,-7680,-18720,-8400]) (![0,0,0,0,0,0,0,-6912,-8448,-12864,-5184]) (![0,0,0,0,0,0,0,-6912,-8448,-10464,-3984])).trans sorted_109
theorem gram_190 : gram (fun a=>dictionary32.getD ((row3 198 200 222) a) 0)=norm_112 := by
  rw [gram_eq_of_entries dictionary32 (row3 198 200 222) _ _ _ dictionary_198 dictionary_200 dictionary_222]
  exact sorted_112
theorem gram_191 : gram (fun a=>dictionary32.getD ((row3 199 202 224) a) 0)=norm_113 := by
  rw [gram_eq_of_entries dictionary32 (row3 199 202 224) _ _ _ dictionary_199 dictionary_202 dictionary_224]
  exact sorted_113
open QuarticIntegerData QuarticIntegerMembership32 QuarticIntegerNormSorted32
open QuarticIntegerListAggregates QuarticIntegerNorm QuarticIntegerGramPermutation
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem gram_192 : gram (fun a=>dictionary32.getD ((row3 200 198 222) a) 0)=norm_112 := by
  rw [gram_eq_of_entries dictionary32 (row3 200 198 222) _ _ _ dictionary_200 dictionary_198 dictionary_222]
  exact (gram102 (![0,0,0,0,0,0,0,-6720,-1920,-19680,-9600]) (![0,0,0,0,0,0,0,-6720,-1920,-6880,-3200]) (![0,0,0,0,0,0,0,-3840,-3840,-19360,-9200])).trans sorted_112
theorem gram_193 : gram (fun a=>dictionary32.getD ((row3 201 201 225) a) 0)=norm_114 := by
  rw [gram_eq_of_entries dictionary32 (row3 201 201 225) _ _ _ dictionary_201 dictionary_201 dictionary_225]
  exact sorted_114
theorem gram_194 : gram (fun a=>dictionary32.getD ((row3 203 123 351) a) 0)=norm_084 := by
  rw [gram_eq_of_entries dictionary32 (row3 203 123 351) _ _ _ dictionary_203 dictionary_123 dictionary_351]
  exact (gram102 (![0,0,0,0,0,0,-2560,-8000,-1920,-7680,-3600]) (![0,0,0,0,0,0,0,-6080,-1280,-7120,-3400]) (![0,0,0,0,0,0,2560,-4480,-5760,-5040,-1800])).trans sorted_084
theorem gram_195 : gram (fun a=>dictionary32.getD ((row3 204 112 404) a) 0)=norm_073 := by
  rw [gram_eq_of_entries dictionary32 (row3 204 112 404) _ _ _ dictionary_204 dictionary_112 dictionary_404]
  exact (gram102 (![0,0,0,0,0,0,-15360,-27840,-5760,-14640,-6600]) (![0,0,0,0,0,0,0,-6080,8320,-6720,-4400]) (![0,0,0,0,0,0,15360,-5120,-12800,-7200,-2000])).trans sorted_073
theorem gram_196 : gram (fun a=>dictionary32.getD ((row3 205 113 404) a) 0)=norm_074 := by
  rw [gram_eq_of_entries dictionary32 (row3 205 113 404) _ _ _ dictionary_205 dictionary_113 dictionary_404]
  exact (gram102 (![0,0,0,0,0,0,-15360,-27840,-5760,-12240,-5400]) (![0,0,0,0,0,0,0,-6080,8320,-4320,-3200]) (![0,0,0,0,0,0,15360,-5120,-12800,-7200,-2000])).trans sorted_074
theorem gram_197 : gram (fun a=>dictionary32.getD ((row3 206 258 211) a) 0)=norm_115 := by
  rw [gram_eq_of_entries dictionary32 (row3 206 258 211) _ _ _ dictionary_206 dictionary_258 dictionary_211]
  exact (gram021 (![0,0,0,0,0,0,0,-5120,-5120,-17280,-8000]) (![0,0,0,0,0,0,0,-5120,-5120,-2880,-800]) (![0,0,0,0,0,0,0,0,0,-14400,-7200])).trans sorted_115
theorem gram_198 : gram (fun a=>dictionary32.getD ((row3 207 211 262) a) 0)=norm_116 := by
  rw [gram_eq_of_entries dictionary32 (row3 207 211 262) _ _ _ dictionary_207 dictionary_211 dictionary_262]
  exact sorted_116
theorem gram_199 : gram (fun a=>dictionary32.getD ((row3 207 220 221) a) 0)=norm_117 := by
  rw [gram_eq_of_entries dictionary32 (row3 207 220 221) _ _ _ dictionary_207 dictionary_220 dictionary_221]
  exact sorted_117
theorem gram_200 : gram (fun a=>dictionary32.getD ((row3 207 262 211) a) 0)=norm_116 := by
  rw [gram_eq_of_entries dictionary32 (row3 207 262 211) _ _ _ dictionary_207 dictionary_262 dictionary_211]
  exact (gram021 (![0,0,0,0,0,0,0,-5120,-5120,-12480,-5600]) (![0,0,0,0,0,0,0,-5120,-5120,-2880,-800]) (![0,0,0,0,0,0,0,0,0,-9600,-4800])).trans sorted_116
theorem gram_201 : gram (fun a=>dictionary32.getD ((row3 208 221 221) a) 0)=norm_119 := by
  rw [gram_eq_of_entries dictionary32 (row3 208 221 221) _ _ _ dictionary_208 dictionary_221 dictionary_221]
  exact sorted_119
theorem gram_202 : gram (fun a=>dictionary32.getD ((row3 209 268 210) a) 0)=norm_120 := by
  rw [gram_eq_of_entries dictionary32 (row3 209 268 210) _ _ _ dictionary_209 dictionary_268 dictionary_210]
  exact (gram021 (![0,0,0,0,0,0,0,-5120,-5120,-9280,-4000]) (![0,0,0,0,0,0,0,-5120,-5120,-4480,-1600]) (![0,0,0,0,0,0,0,0,0,-4800,-2400])).trans sorted_120
theorem gram_203 : gram (fun a=>dictionary32.getD ((row3 210 148 163) a) 0)=norm_093 := by
  rw [gram_eq_of_entries dictionary32 (row3 210 148 163) _ _ _ dictionary_210 dictionary_148 dictionary_163]
  exact (gram201 (![0,0,0,0,0,0,0,-20480,-20480,-13120,-4000]) (![0,0,0,0,0,0,0,-15360,-15360,-8640,-2400]) (![0,0,0,0,0,0,0,-5120,-5120,-4480,-1600])).trans sorted_093
theorem gram_204 : gram (fun a=>dictionary32.getD ((row3 210 163 148) a) 0)=norm_093 := by
  rw [gram_eq_of_entries dictionary32 (row3 210 163 148) _ _ _ dictionary_210 dictionary_163 dictionary_148]
  exact (gram210 (![0,0,0,0,0,0,0,-20480,-20480,-13120,-4000]) (![0,0,0,0,0,0,0,-15360,-15360,-8640,-2400]) (![0,0,0,0,0,0,0,-5120,-5120,-4480,-1600])).trans sorted_093
theorem gram_205 : gram (fun a=>dictionary32.getD ((row3 210 181 210) a) 0)=norm_103 := by
  rw [gram_eq_of_entries dictionary32 (row3 210 181 210) _ _ _ dictionary_210 dictionary_181 dictionary_210]
  exact (gram102 (![0,0,0,0,0,0,0,-10240,-10240,-8960,-3200]) (![0,0,0,0,0,0,0,-5120,-5120,-4480,-1600]) (![0,0,0,0,0,0,0,-5120,-5120,-4480,-1600])).trans sorted_103
theorem gram_206 : gram (fun a=>dictionary32.getD ((row3 210 209 268) a) 0)=norm_120 := by
  rw [gram_eq_of_entries dictionary32 (row3 210 209 268) _ _ _ dictionary_210 dictionary_209 dictionary_268]
  exact (gram102 (![0,0,0,0,0,0,0,-5120,-5120,-9280,-4000]) (![0,0,0,0,0,0,0,-5120,-5120,-4480,-1600]) (![0,0,0,0,0,0,0,0,0,-4800,-2400])).trans sorted_120
theorem gram_207 : gram (fun a=>dictionary32.getD ((row3 210 210 181) a) 0)=norm_103 := by
  rw [gram_eq_of_entries dictionary32 (row3 210 210 181) _ _ _ dictionary_210 dictionary_210 dictionary_181]
  exact (gram120 (![0,0,0,0,0,0,0,-10240,-10240,-8960,-3200]) (![0,0,0,0,0,0,0,-5120,-5120,-4480,-1600]) (![0,0,0,0,0,0,0,-5120,-5120,-4480,-1600])).trans sorted_103
theorem gram_208 : gram (fun a=>dictionary32.getD ((row3 210 210 508) a) 0)=norm_121 := by
  rw [gram_eq_of_entries dictionary32 (row3 210 210 508) _ _ _ dictionary_210 dictionary_210 dictionary_508]
  exact sorted_121
theorem gram_209 : gram (fun a=>dictionary32.getD ((row3 210 268 209) a) 0)=norm_120 := by
  rw [gram_eq_of_entries dictionary32 (row3 210 268 209) _ _ _ dictionary_210 dictionary_268 dictionary_209]
  exact (gram120 (![0,0,0,0,0,0,0,-5120,-5120,-9280,-4000]) (![0,0,0,0,0,0,0,-5120,-5120,-4480,-1600]) (![0,0,0,0,0,0,0,0,0,-4800,-2400])).trans sorted_120
theorem gram_210 : gram (fun a=>dictionary32.getD ((row3 210 508 210) a) 0)=norm_121 := by
  rw [gram_eq_of_entries dictionary32 (row3 210 508 210) _ _ _ dictionary_210 dictionary_508 dictionary_210]
  exact (gram021 (![0,0,0,0,0,0,0,-5120,-5120,-4480,-1600]) (![0,0,0,0,0,0,0,-5120,-5120,-4480,-1600]) (0)).trans sorted_121
theorem gram_211 : gram (fun a=>dictionary32.getD ((row3 211 189 234) a) 0)=norm_110 := by
  rw [gram_eq_of_entries dictionary32 (row3 211 189 234) _ _ _ dictionary_211 dictionary_189 dictionary_234]
  exact (gram102 (![0,0,0,0,0,0,0,-7680,-7680,-5120,-1600]) (![0,0,0,0,0,0,0,-5120,-5120,-2880,-800]) (![0,0,0,0,0,0,0,-2560,-2560,-2240,-800])).trans sorted_110
theorem gram_212 : gram (fun a=>dictionary32.getD ((row3 211 211 508) a) 0)=norm_122 := by
  rw [gram_eq_of_entries dictionary32 (row3 211 211 508) _ _ _ dictionary_211 dictionary_211 dictionary_508]
  exact sorted_122
theorem gram_213 : gram (fun a=>dictionary32.getD ((row3 211 258 206) a) 0)=norm_115 := by
  rw [gram_eq_of_entries dictionary32 (row3 211 258 206) _ _ _ dictionary_211 dictionary_258 dictionary_206]
  exact (gram120 (![0,0,0,0,0,0,0,-5120,-5120,-17280,-8000]) (![0,0,0,0,0,0,0,-5120,-5120,-2880,-800]) (![0,0,0,0,0,0,0,0,0,-14400,-7200])).trans sorted_115
theorem gram_214 : gram (fun a=>dictionary32.getD ((row3 211 262 207) a) 0)=norm_116 := by
  rw [gram_eq_of_entries dictionary32 (row3 211 262 207) _ _ _ dictionary_211 dictionary_262 dictionary_207]
  exact (gram120 (![0,0,0,0,0,0,0,-5120,-5120,-12480,-5600]) (![0,0,0,0,0,0,0,-5120,-5120,-2880,-800]) (![0,0,0,0,0,0,0,0,0,-9600,-4800])).trans sorted_116
theorem gram_215 : gram (fun a=>dictionary32.getD ((row3 212 221 212) a) 0)=norm_124 := by
  rw [gram_eq_of_entries dictionary32 (row3 212 221 212) _ _ _ dictionary_212 dictionary_221 dictionary_212]
  exact (gram021 (![0,0,0,0,0,0,0,-4864,-5376,-10528,-4528]) (![0,0,0,0,0,0,0,-4864,-5376,-10528,-4528]) (![0,0,0,0,0,0,0,-4608,-5632,-6976,-2656])).trans sorted_124
theorem gram_216 : gram (fun a=>dictionary32.getD ((row3 213 232 214) a) 0)=norm_125 := by
  rw [gram_eq_of_entries dictionary32 (row3 213 232 214) _ _ _ dictionary_213 dictionary_232 dictionary_214]
  exact (gram021 (![0,0,0,0,0,0,0,-4864,-5376,-5728,-2128]) (![0,0,0,0,0,0,0,-4864,-5376,-4928,-1728]) (![0,0,0,0,0,0,0,-2560,-2560,-6240,-2800])).trans sorted_125
theorem gram_217 : gram (fun a=>dictionary32.getD ((row3 214 232 213) a) 0)=norm_125 := by
  rw [gram_eq_of_entries dictionary32 (row3 214 232 213) _ _ _ dictionary_214 dictionary_232 dictionary_213]
  exact (gram120 (![0,0,0,0,0,0,0,-4864,-5376,-5728,-2128]) (![0,0,0,0,0,0,0,-4864,-5376,-4928,-1728]) (![0,0,0,0,0,0,0,-2560,-2560,-6240,-2800])).trans sorted_125
theorem gram_218 : gram (fun a=>dictionary32.getD ((row3 215 11 249) a) 0)=norm_003 := by
  rw [gram_eq_of_entries dictionary32 (row3 215 11 249) _ _ _ dictionary_215 dictionary_11 dictionary_249]
  exact (gram102 (![0,0,0,0,0,0,0,4800,0,0,0]) (![0,0,0,0,0,0,0,-4800,2800,1400,6125]) (![0,0,0,0,0,0,0,0,-2000,-1000,4625])).trans sorted_003
theorem gram_219 : gram (fun a=>dictionary32.getD ((row3 216 11 293) a) 0)=norm_004 := by
  rw [gram_eq_of_entries dictionary32 (row3 216 11 293) _ _ _ dictionary_216 dictionary_11 dictionary_293]
  exact (gram102 (![0,0,0,0,0,0,0,4800,0,0,0]) (![0,0,0,0,0,0,0,-4800,8400,4200,5250]) (![0,0,0,0,0,0,0,0,3600,1800,2250])).trans sorted_004
theorem gram_220 : gram (fun a=>dictionary32.getD ((row3 216 293 11) a) 0)=norm_004 := by
  rw [gram_eq_of_entries dictionary32 (row3 216 293 11) _ _ _ dictionary_216 dictionary_293 dictionary_11]
  exact (gram120 (![0,0,0,0,0,0,0,4800,0,0,0]) (![0,0,0,0,0,0,0,-4800,8400,4200,5250]) (![0,0,0,0,0,0,0,0,3600,1800,2250])).trans sorted_004
theorem gram_221 : gram (fun a=>dictionary32.getD ((row3 217 11 294) a) 0)=norm_005 := by
  rw [gram_eq_of_entries dictionary32 (row3 217 11 294) _ _ _ dictionary_217 dictionary_11 dictionary_294]
  exact (gram102 (![0,0,0,0,0,0,0,4800,0,0,0]) (![0,0,0,0,0,0,0,-4800,8400,4200,35250]) (![0,0,0,0,0,0,0,0,3600,1800,32250])).trans sorted_005
theorem gram_222 : gram (fun a=>dictionary32.getD ((row3 217 294 11) a) 0)=norm_005 := by
  rw [gram_eq_of_entries dictionary32 (row3 217 294 11) _ _ _ dictionary_217 dictionary_294 dictionary_11]
  exact (gram120 (![0,0,0,0,0,0,0,4800,0,0,0]) (![0,0,0,0,0,0,0,-4800,8400,4200,35250]) (![0,0,0,0,0,0,0,0,3600,1800,32250])).trans sorted_005
theorem gram_223 : gram (fun a=>dictionary32.getD ((row3 218 218 223) a) 0)=norm_126 := by
  rw [gram_eq_of_entries dictionary32 (row3 218 218 223) _ _ _ dictionary_218 dictionary_218 dictionary_223]
  exact sorted_126
theorem gram_224 : gram (fun a=>dictionary32.getD ((row3 218 223 218) a) 0)=norm_126 := by
  rw [gram_eq_of_entries dictionary32 (row3 218 223 218) _ _ _ dictionary_218 dictionary_223 dictionary_218]
  exact (gram021 (![0,0,0,0,0,0,0,-4736,-5504,-7552,-2992]) (![0,0,0,0,0,0,0,-4736,-5504,-7552,-2992]) (![0,0,0,0,0,0,0,-3840,-3840,-10560,-4800])).trans sorted_126
theorem gram_225 : gram (fun a=>dictionary32.getD ((row3 219 208 219) a) 0)=norm_118 := by
  rw [gram_eq_of_entries dictionary32 (row3 219 208 219) _ _ _ dictionary_219 dictionary_208 dictionary_219]
  exact (gram102 (![0,0,0,0,0,0,0,-5120,-5120,-10880,-4800]) (![0,0,0,0,0,0,0,-4608,-5632,-21376,-9856]) (![0,0,0,0,0,0,0,-4608,-5632,-21376,-9856])).trans sorted_118
theorem gram_226 : gram (fun a=>dictionary32.getD ((row3 220 207 221) a) 0)=norm_117 := by
  rw [gram_eq_of_entries dictionary32 (row3 220 207 221) _ _ _ dictionary_220 dictionary_207 dictionary_221]
  exact (gram102 (![0,0,0,0,0,0,0,-5120,-5120,-12480,-5600]) (![0,0,0,0,0,0,0,-4608,-5632,-8576,-3456]) (![0,0,0,0,0,0,0,-4608,-5632,-6976,-2656])).trans sorted_117
theorem gram_227 : gram (fun a=>dictionary32.getD ((row3 221 207 220) a) 0)=norm_117 := by
  rw [gram_eq_of_entries dictionary32 (row3 221 207 220) _ _ _ dictionary_221 dictionary_207 dictionary_220]
  exact (gram201 (![0,0,0,0,0,0,0,-5120,-5120,-12480,-5600]) (![0,0,0,0,0,0,0,-4608,-5632,-8576,-3456]) (![0,0,0,0,0,0,0,-4608,-5632,-6976,-2656])).trans sorted_117
theorem gram_228 : gram (fun a=>dictionary32.getD ((row3 221 220 207) a) 0)=norm_117 := by
  rw [gram_eq_of_entries dictionary32 (row3 221 220 207) _ _ _ dictionary_221 dictionary_220 dictionary_207]
  exact (gram210 (![0,0,0,0,0,0,0,-5120,-5120,-12480,-5600]) (![0,0,0,0,0,0,0,-4608,-5632,-8576,-3456]) (![0,0,0,0,0,0,0,-4608,-5632,-6976,-2656])).trans sorted_117
theorem gram_229 : gram (fun a=>dictionary32.getD ((row3 221 221 208) a) 0)=norm_119 := by
  rw [gram_eq_of_entries dictionary32 (row3 221 221 208) _ _ _ dictionary_221 dictionary_221 dictionary_208]
  exact (gram120 (![0,0,0,0,0,0,0,-5120,-5120,-10880,-4800]) (![0,0,0,0,0,0,0,-4608,-5632,-6976,-2656]) (![0,0,0,0,0,0,0,-4608,-5632,-6976,-2656])).trans sorted_119
theorem gram_230 : gram (fun a=>dictionary32.getD ((row3 222 198 200) a) 0)=norm_112 := by
  rw [gram_eq_of_entries dictionary32 (row3 222 198 200) _ _ _ dictionary_222 dictionary_198 dictionary_200]
  exact (gram201 (![0,0,0,0,0,0,0,-6720,-1920,-19680,-9600]) (![0,0,0,0,0,0,0,-6720,-1920,-6880,-3200]) (![0,0,0,0,0,0,0,-3840,-3840,-19360,-9200])).trans sorted_112
theorem gram_231 : gram (fun a=>dictionary32.getD ((row3 222 200 198) a) 0)=norm_112 := by
  rw [gram_eq_of_entries dictionary32 (row3 222 200 198) _ _ _ dictionary_222 dictionary_200 dictionary_198]
  exact (gram210 (![0,0,0,0,0,0,0,-6720,-1920,-19680,-9600]) (![0,0,0,0,0,0,0,-6720,-1920,-6880,-3200]) (![0,0,0,0,0,0,0,-3840,-3840,-19360,-9200])).trans sorted_112
theorem gram_232 : gram (fun a=>dictionary32.getD ((row3 223 218 218) a) 0)=norm_126 := by
  rw [gram_eq_of_entries dictionary32 (row3 223 218 218) _ _ _ dictionary_223 dictionary_218 dictionary_218]
  exact (gram201 (![0,0,0,0,0,0,0,-4736,-5504,-7552,-2992]) (![0,0,0,0,0,0,0,-4736,-5504,-7552,-2992]) (![0,0,0,0,0,0,0,-3840,-3840,-10560,-4800])).trans sorted_126
theorem gram_233 : gram (fun a=>dictionary32.getD ((row3 224 202 199) a) 0)=norm_113 := by
  rw [gram_eq_of_entries dictionary32 (row3 224 202 199) _ _ _ dictionary_224 dictionary_202 dictionary_199]
  exact (gram210 (![0,0,0,0,0,0,0,-6720,-1920,-8880,-4200]) (![0,0,0,0,0,0,0,-6720,-1920,-4880,-2200]) (![0,0,0,0,0,0,0,-3840,-3840,-7760,-3400])).trans sorted_113
theorem gram_234 : gram (fun a=>dictionary32.getD ((row3 225 201 201) a) 0)=norm_114 := by
  rw [gram_eq_of_entries dictionary32 (row3 225 201 201) _ _ _ dictionary_225 dictionary_201 dictionary_201]
  exact (gram201 (![0,0,0,0,0,0,0,-6720,-1920,-5280,-2400]) (![0,0,0,0,0,0,0,-6720,-1920,-5280,-2400]) (![0,0,0,0,0,0,0,-3840,-3840,-3360,-1200])).trans sorted_114
theorem gram_235 : gram (fun a=>dictionary32.getD ((row3 226 10 250) a) 0)=norm_001 := by
  rw [gram_eq_of_entries dictionary32 (row3 226 10 250) _ _ _ dictionary_226 dictionary_10 dictionary_250]
  exact (gram102 (![0,0,0,0,0,0,0,3200,0,0,0]) (![0,0,0,0,0,0,0,-3200,2400,1200,750]) (![0,0,0,0,0,0,0,0,-800,-400,-250])).trans sorted_001
theorem gram_236 : gram (fun a=>dictionary32.getD ((row3 227 288 10) a) 0)=norm_002 := by
  rw [gram_eq_of_entries dictionary32 (row3 227 288 10) _ _ _ dictionary_227 dictionary_288 dictionary_10]
  exact (gram120 (![0,0,0,0,0,0,0,3200,0,0,0]) (![0,0,0,0,0,0,0,-3200,5600,2800,3500]) (![0,0,0,0,0,0,0,0,2400,1200,1500])).trans sorted_002
theorem gram_237 : gram (fun a=>dictionary32.getD ((row3 228 121 366) a) 0)=norm_082 := by
  rw [gram_eq_of_entries dictionary32 (row3 228 121 366) _ _ _ dictionary_228 dictionary_121 dictionary_366]
  exact (gram102 (![0,0,0,0,0,0,-5120,-9280,-1920,-8880,-4200]) (![0,0,0,0,0,0,0,-2880,1920,-6720,-3600]) (![0,0,0,0,0,0,5120,-2560,-5120,-2880,-800])).trans sorted_082
theorem gram_238 : gram (fun a=>dictionary32.getD ((row3 229 262 234) a) 0)=norm_127 := by
  rw [gram_eq_of_entries dictionary32 (row3 229 262 234) _ _ _ dictionary_229 dictionary_262 dictionary_234]
  exact (gram021 (![0,0,0,0,0,0,0,-2560,-2560,-11840,-5600]) (![0,0,0,0,0,0,0,-2560,-2560,-2240,-800]) (![0,0,0,0,0,0,0,0,0,-9600,-4800])).trans sorted_127
theorem gram_239 : gram (fun a=>dictionary32.getD ((row3 231 182 182) a) 0)=norm_104 := by
  rw [gram_eq_of_entries dictionary32 (row3 231 182 182) _ _ _ dictionary_231 dictionary_182 dictionary_182]
  exact (gram201 (![0,0,0,0,0,0,0,-9984,-10496,-8608,-2928]) (![0,0,0,0,0,0,0,-9984,-10496,-8608,-2928]) (![0,0,0,0,0,0,0,-2560,-2560,-7040,-3200])).trans sorted_104
theorem gram_240 : gram (fun a=>dictionary32.getD ((row3 231 238 238) a) 0)=norm_129 := by
  rw [gram_eq_of_entries dictionary32 (row3 231 238 238) _ _ _ dictionary_231 dictionary_238 dictionary_238]
  exact sorted_129
theorem gram_241 : gram (fun a=>dictionary32.getD ((row3 233 271 234) a) 0)=norm_130 := by
  rw [gram_eq_of_entries dictionary32 (row3 233 271 234) _ _ _ dictionary_233 dictionary_271 dictionary_234]
  exact (gram021 (![0,0,0,0,0,0,0,-2560,-2560,-4640,-2000]) (![0,0,0,0,0,0,0,-2560,-2560,-2240,-800]) (![0,0,0,0,0,0,0,0,0,-2400,-1200])).trans sorted_130
theorem gram_242 : gram (fun a=>dictionary32.getD ((row3 234 189 211) a) 0)=norm_110 := by
  rw [gram_eq_of_entries dictionary32 (row3 234 189 211) _ _ _ dictionary_234 dictionary_189 dictionary_211]
  exact (gram201 (![0,0,0,0,0,0,0,-7680,-7680,-5120,-1600]) (![0,0,0,0,0,0,0,-5120,-5120,-2880,-800]) (![0,0,0,0,0,0,0,-2560,-2560,-2240,-800])).trans sorted_110
theorem gram_243 : gram (fun a=>dictionary32.getD ((row3 234 211 189) a) 0)=norm_110 := by
  rw [gram_eq_of_entries dictionary32 (row3 234 211 189) _ _ _ dictionary_234 dictionary_211 dictionary_189]
  exact (gram210 (![0,0,0,0,0,0,0,-7680,-7680,-5120,-1600]) (![0,0,0,0,0,0,0,-5120,-5120,-2880,-800]) (![0,0,0,0,0,0,0,-2560,-2560,-2240,-800])).trans sorted_110
theorem gram_244 : gram (fun a=>dictionary32.getD ((row3 234 229 262) a) 0)=norm_127 := by
  rw [gram_eq_of_entries dictionary32 (row3 234 229 262) _ _ _ dictionary_234 dictionary_229 dictionary_262]
  exact (gram102 (![0,0,0,0,0,0,0,-2560,-2560,-11840,-5600]) (![0,0,0,0,0,0,0,-2560,-2560,-2240,-800]) (![0,0,0,0,0,0,0,0,0,-9600,-4800])).trans sorted_127
theorem gram_245 : gram (fun a=>dictionary32.getD ((row3 234 233 271) a) 0)=norm_130 := by
  rw [gram_eq_of_entries dictionary32 (row3 234 233 271) _ _ _ dictionary_234 dictionary_233 dictionary_271]
  exact (gram102 (![0,0,0,0,0,0,0,-2560,-2560,-4640,-2000]) (![0,0,0,0,0,0,0,-2560,-2560,-2240,-800]) (![0,0,0,0,0,0,0,0,0,-2400,-1200])).trans sorted_130
theorem gram_246 : gram (fun a=>dictionary32.getD ((row3 234 234 508) a) 0)=norm_131 := by
  rw [gram_eq_of_entries dictionary32 (row3 234 234 508) _ _ _ dictionary_234 dictionary_234 dictionary_508]
  exact sorted_131
theorem gram_247 : gram (fun a=>dictionary32.getD ((row3 234 262 229) a) 0)=norm_127 := by
  rw [gram_eq_of_entries dictionary32 (row3 234 262 229) _ _ _ dictionary_234 dictionary_262 dictionary_229]
  exact (gram120 (![0,0,0,0,0,0,0,-2560,-2560,-11840,-5600]) (![0,0,0,0,0,0,0,-2560,-2560,-2240,-800]) (![0,0,0,0,0,0,0,0,0,-9600,-4800])).trans sorted_127
theorem gram_248 : gram (fun a=>dictionary32.getD ((row3 234 271 233) a) 0)=norm_130 := by
  rw [gram_eq_of_entries dictionary32 (row3 234 271 233) _ _ _ dictionary_234 dictionary_271 dictionary_233]
  exact (gram120 (![0,0,0,0,0,0,0,-2560,-2560,-4640,-2000]) (![0,0,0,0,0,0,0,-2560,-2560,-2240,-800]) (![0,0,0,0,0,0,0,0,0,-2400,-1200])).trans sorted_130
theorem gram_249 : gram (fun a=>dictionary32.getD ((row3 234 508 234) a) 0)=norm_131 := by
  rw [gram_eq_of_entries dictionary32 (row3 234 508 234) _ _ _ dictionary_234 dictionary_508 dictionary_234]
  exact (gram021 (![0,0,0,0,0,0,0,-2560,-2560,-2240,-800]) (![0,0,0,0,0,0,0,-2560,-2560,-2240,-800]) (0)).trans sorted_131
theorem gram_250 : gram (fun a=>dictionary32.getD ((row3 235 211 235) a) 0)=norm_123 := by
  rw [gram_eq_of_entries dictionary32 (row3 235 211 235) _ _ _ dictionary_235 dictionary_211 dictionary_235]
  exact (gram102 (![0,0,0,0,0,0,0,-5120,-5120,-2880,-800]) (![0,0,0,0,0,0,0,-2560,-2560,-1440,-400]) (![0,0,0,0,0,0,0,-2560,-2560,-1440,-400])).trans sorted_123
theorem gram_251 : gram (fun a=>dictionary32.getD ((row3 236 230 237) a) 0)=norm_128 := by
  rw [gram_eq_of_entries dictionary32 (row3 236 230 237) _ _ _ dictionary_236 dictionary_230 dictionary_237]
  exact (gram102 (![0,0,0,0,0,0,0,-2560,-2560,-7440,-3400]) (![0,0,0,0,0,0,0,-2304,-2816,-11088,-5128]) (![0,0,0,0,0,0,0,-2304,-2816,-10288,-4728])).trans sorted_128
theorem gram_252 : gram (fun a=>dictionary32.getD ((row3 237 230 236) a) 0)=norm_128 := by
  rw [gram_eq_of_entries dictionary32 (row3 237 230 236) _ _ _ dictionary_237 dictionary_230 dictionary_236]
  exact (gram201 (![0,0,0,0,0,0,0,-2560,-2560,-7440,-3400]) (![0,0,0,0,0,0,0,-2304,-2816,-11088,-5128]) (![0,0,0,0,0,0,0,-2304,-2816,-10288,-4728])).trans sorted_128
theorem gram_253 : gram (fun a=>dictionary32.getD ((row3 238 231 238) a) 0)=norm_129 := by
  rw [gram_eq_of_entries dictionary32 (row3 238 231 238) _ _ _ dictionary_238 dictionary_231 dictionary_238]
  exact (gram102 (![0,0,0,0,0,0,0,-2560,-2560,-7040,-3200]) (![0,0,0,0,0,0,0,-2304,-2816,-6688,-2928]) (![0,0,0,0,0,0,0,-2304,-2816,-6688,-2928])).trans sorted_129
theorem gram_254 : gram (fun a=>dictionary32.getD ((row3 238 238 231) a) 0)=norm_129 := by
  rw [gram_eq_of_entries dictionary32 (row3 238 238 231) _ _ _ dictionary_238 dictionary_238 dictionary_231]
  exact (gram120 (![0,0,0,0,0,0,0,-2560,-2560,-7040,-3200]) (![0,0,0,0,0,0,0,-2304,-2816,-6688,-2928]) (![0,0,0,0,0,0,0,-2304,-2816,-6688,-2928])).trans sorted_129
theorem gram_255 : gram (fun a=>dictionary32.getD ((row3 239 239 243) a) 0)=norm_132 := by
  rw [gram_eq_of_entries dictionary32 (row3 239 239 243) _ _ _ dictionary_239 dictionary_239 dictionary_243]
  exact sorted_132
end BilayerDressed.QuarticIntegerNormCases32
