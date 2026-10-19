import Dressed.QuarticIntegerGramCases
import Dressed.QuarticIntegerGramPermutation
import Dressed.QuarticIntegerMembership32.Dictionary
import Dressed.QuarticIntegerNormSorted32.Group000
import Dressed.QuarticIntegerNormSorted32.Group001
import Dressed.QuarticIntegerNormSorted32.Group002
import Dressed.QuarticIntegerNormSorted32.Group003
set_option Elab.async false
namespace BilayerDressed.QuarticIntegerNormCases32
open QuarticIntegerData QuarticIntegerMembership32 QuarticIntegerNormSorted32
open QuarticIntegerListAggregates QuarticIntegerNorm QuarticIntegerGramPermutation
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem gram_512 : gram (fun a=>dictionary32.getD ((row3 398 423 413) a) 0)=norm_235 := by
  rw [gram_eq_of_entries dictionary32 (row3 398 423 413) _ _ _ dictionary_398 dictionary_423 dictionary_413]
  exact (gram021 (![0,0,0,0,0,0,13824,2496,52368,30408,44235]) (![0,0,0,0,0,0,21504,31296,39168,35328,8640]) (![0,0,0,0,0,0,23040,15360,41040,30120,41655])).trans sorted_235
theorem gram_513 : gram (fun a=>dictionary32.getD ((row3 399 412 420) a) 0)=norm_236 := by
  rw [gram_eq_of_entries dictionary32 (row3 399 412 420) _ _ _ dictionary_399 dictionary_412 dictionary_420]
  exact sorted_236
theorem gram_514 : gram (fun a=>dictionary32.getD ((row3 400 406 392) a) 0)=norm_231 := by
  rw [gram_eq_of_entries dictionary32 (row3 400 406 392) _ _ _ dictionary_400 dictionary_406 dictionary_392]
  exact (gram120 (![0,0,0,0,0,0,9216,1664,24752,11512,7775]) (![0,0,0,0,0,0,14336,20864,11392,8832,2080]) (![0,0,0,0,0,0,15360,10240,17200,11320,4555])).trans sorted_231
theorem gram_515 : gram (fun a=>dictionary32.getD ((row3 401 109 127) a) 0)=norm_070 := by
  rw [gram_eq_of_entries dictionary32 (row3 401 109 127) _ _ _ dictionary_401 dictionary_109 dictionary_127]
  exact (gram201 (![0,0,0,0,0,0,-15360,-78720,-42240,-96960,-43200]) (![0,0,0,0,0,0,0,-64128,-41472,-84576,-36336]) (![0,0,0,0,0,0,15360,-54528,-68352,-86496,-33936])).trans sorted_070
theorem gram_516 : gram (fun a=>dictionary32.getD ((row3 401 127 109) a) 0)=norm_070 := by
  rw [gram_eq_of_entries dictionary32 (row3 401 127 109) _ _ _ dictionary_401 dictionary_127 dictionary_109]
  exact (gram210 (![0,0,0,0,0,0,-15360,-78720,-42240,-96960,-43200]) (![0,0,0,0,0,0,0,-64128,-41472,-84576,-36336]) (![0,0,0,0,0,0,15360,-54528,-68352,-86496,-33936])).trans sorted_070
theorem gram_517 : gram (fun a=>dictionary32.getD ((row3 402 110 133) a) 0)=norm_071 := by
  rw [gram_eq_of_entries dictionary32 (row3 402 110 133) _ _ _ dictionary_402 dictionary_110 dictionary_133]
  exact (gram201 (![0,0,0,0,0,0,-15360,-48000,-11520,-41280,-19200]) (![0,0,0,0,0,0,0,-36480,-7680,-37920,-18000]) (![0,0,0,0,0,0,15360,-26880,-34560,-30240,-10800])).trans sorted_071
theorem gram_518 : gram (fun a=>dictionary32.getD ((row3 402 133 110) a) 0)=norm_071 := by
  rw [gram_eq_of_entries dictionary32 (row3 402 133 110) _ _ _ dictionary_402 dictionary_133 dictionary_110]
  exact (gram210 (![0,0,0,0,0,0,-15360,-48000,-11520,-41280,-19200]) (![0,0,0,0,0,0,0,-36480,-7680,-37920,-18000]) (![0,0,0,0,0,0,15360,-26880,-34560,-30240,-10800])).trans sorted_071
theorem gram_519 : gram (fun a=>dictionary32.getD ((row3 403 111 145) a) 0)=norm_072 := by
  rw [gram_eq_of_entries dictionary32 (row3 403 111 145) _ _ _ dictionary_403 dictionary_111 dictionary_145]
  exact (gram201 (![0,0,0,0,0,0,-15360,-48000,-11520,-34080,-15600]) (![0,0,0,0,0,0,0,-26240,2560,-26160,-13400]) (![0,0,0,0,0,0,15360,-16640,-24320,-13680,-3800])).trans sorted_072
theorem gram_520 : gram (fun a=>dictionary32.getD ((row3 404 112 204) a) 0)=norm_073 := by
  rw [gram_eq_of_entries dictionary32 (row3 404 112 204) _ _ _ dictionary_404 dictionary_112 dictionary_204]
  exact (gram201 (![0,0,0,0,0,0,-15360,-27840,-5760,-14640,-6600]) (![0,0,0,0,0,0,0,-6080,8320,-6720,-4400]) (![0,0,0,0,0,0,15360,-5120,-12800,-7200,-2000])).trans sorted_073
theorem gram_521 : gram (fun a=>dictionary32.getD ((row3 404 113 205) a) 0)=norm_074 := by
  rw [gram_eq_of_entries dictionary32 (row3 404 113 205) _ _ _ dictionary_404 dictionary_113 dictionary_205]
  exact (gram201 (![0,0,0,0,0,0,-15360,-27840,-5760,-12240,-5400]) (![0,0,0,0,0,0,0,-6080,8320,-4320,-3200]) (![0,0,0,0,0,0,15360,-5120,-12800,-7200,-2000])).trans sorted_074
theorem gram_522 : gram (fun a=>dictionary32.getD ((row3 405 114 240) a) 0)=norm_075 := by
  rw [gram_eq_of_entries dictionary32 (row3 405 114 240) _ _ _ dictionary_405 dictionary_114 dictionary_240]
  exact (gram201 (![0,0,0,0,0,0,-15360,-21120,-3840,-8160,-3600]) (![0,0,0,0,0,0,0,-1920,7680,-1680,-1800]) (![0,0,0,0,0,0,15360,-3840,-11520,-6480,-1800])).trans sorted_075
theorem gram_523 : gram (fun a=>dictionary32.getD ((row3 406 400 392) a) 0)=norm_231 := by
  rw [gram_eq_of_entries dictionary32 (row3 406 400 392) _ _ _ dictionary_406 dictionary_400 dictionary_392]
  exact (gram210 (![0,0,0,0,0,0,9216,1664,24752,11512,7775]) (![0,0,0,0,0,0,14336,20864,11392,8832,2080]) (![0,0,0,0,0,0,15360,10240,17200,11320,4555])).trans sorted_231
theorem gram_524 : gram (fun a=>dictionary32.getD ((row3 407 450 104) a) 0)=norm_067 := by
  rw [gram_eq_of_entries dictionary32 (row3 407 450 104) _ _ _ dictionary_407 dictionary_450 dictionary_104]
  exact (gram120 (![0,0,0,0,0,-4096,8704,-64,29360,14040,10550]) (![0,0,0,0,0,0,16384,23616,12928,12288,3040]) (![0,0,0,0,0,4096,27136,16384,19440,14520,3630])).trans sorted_067
theorem gram_525 : gram (fun a=>dictionary32.getD ((row3 408 408 409) a) 0)=norm_237 := by
  rw [gram_eq_of_entries dictionary32 (row3 408 408 409) _ _ _ dictionary_408 dictionary_408 dictionary_409]
  exact sorted_237
theorem gram_526 : gram (fun a=>dictionary32.getD ((row3 409 408 408) a) 0)=norm_237 := by
  rw [gram_eq_of_entries dictionary32 (row3 409 408 408) _ _ _ dictionary_409 dictionary_408 dictionary_408]
  exact (gram201 (![0,0,0,0,0,0,16384,24576,48128,37888,8960]) (![0,0,0,0,0,0,16384,24576,48128,37888,8960]) (![0,0,0,0,0,0,16384,24576,53248,43008,10240])).trans sorted_237
theorem gram_527 : gram (fun a=>dictionary32.getD ((row3 410 88 455) a) 0)=norm_057 := by
  rw [gram_eq_of_entries dictionary32 (row3 410 88 455) _ _ _ dictionary_410 dictionary_88 dictionary_455]
  exact (gram102 (![0,0,0,0,0,-8192,8192,7808,35488,15888,7730]) (![0,0,0,0,0,0,18432,16768,10624,11904,3040]) (![0,0,0,0,0,8192,38912,22528,32160,21200,7450])).trans sorted_057
theorem gram_528 : gram (fun a=>dictionary32.getD ((row3 410 455 88) a) 0)=norm_057 := by
  rw [gram_eq_of_entries dictionary32 (row3 410 455 88) _ _ _ dictionary_410 dictionary_455 dictionary_88]
  exact (gram120 (![0,0,0,0,0,-8192,8192,7808,35488,15888,7730]) (![0,0,0,0,0,0,18432,16768,10624,11904,3040]) (![0,0,0,0,0,8192,38912,22528,32160,21200,7450])).trans sorted_057
theorem gram_529 : gram (fun a=>dictionary32.getD ((row3 411 461 70) a) 0)=norm_048 := by
  rw [gram_eq_of_entries dictionary32 (row3 411 461 70) _ _ _ dictionary_411 dictionary_461 dictionary_70]
  exact (gram120 (![0,0,0,0,0,-15360,17664,23616,43248,19608,12210]) (![0,0,0,0,0,0,19200,11520,28080,19320,11130]) (![0,0,0,0,0,15360,29184,21696,19968,16128,3840])).trans sorted_048
theorem gram_530 : gram (fun a=>dictionary32.getD ((row3 413 423 398) a) 0)=norm_235 := by
  rw [gram_eq_of_entries dictionary32 (row3 413 423 398) _ _ _ dictionary_413 dictionary_423 dictionary_398]
  exact (gram120 (![0,0,0,0,0,0,13824,2496,52368,30408,44235]) (![0,0,0,0,0,0,21504,31296,39168,35328,8640]) (![0,0,0,0,0,0,23040,15360,41040,30120,41655])).trans sorted_235
theorem gram_531 : gram (fun a=>dictionary32.getD ((row3 415 422 397) a) 0)=norm_234 := by
  rw [gram_eq_of_entries dictionary32 (row3 415 422 397) _ _ _ dictionary_415 dictionary_422 dictionary_397]
  exact (gram120 (![0,0,0,0,0,0,13824,-11904,59808,31248,37920]) (![0,0,0,0,0,0,21504,45696,27648,23808,5760]) (![0,0,0,0,0,0,23040,15360,34080,23760,21840])).trans sorted_234
theorem gram_532 : gram (fun a=>dictionary32.getD ((row3 416 396 421) a) 0)=norm_233 := by
  rw [gram_eq_of_entries dictionary32 (row3 416 396 421) _ _ _ dictionary_416 dictionary_396 dictionary_421]
  exact (gram102 (![0,0,0,0,0,0,13824,-11904,58368,33408,50610]) (![0,0,0,0,0,0,21504,45696,39168,35328,8640]) (![0,0,0,0,0,0,23040,15360,32640,25920,43530])).trans sorted_233
theorem gram_533 : gram (fun a=>dictionary32.getD ((row3 416 421 396) a) 0)=norm_233 := by
  rw [gram_eq_of_entries dictionary32 (row3 416 421 396) _ _ _ dictionary_416 dictionary_421 dictionary_396]
  exact (gram120 (![0,0,0,0,0,0,13824,-11904,58368,33408,50610]) (![0,0,0,0,0,0,21504,45696,39168,35328,8640]) (![0,0,0,0,0,0,23040,15360,32640,25920,43530])).trans sorted_233
theorem gram_534 : gram (fun a=>dictionary32.getD ((row3 417 463 61) a) 0)=norm_041 := by
  rw [gram_eq_of_entries dictionary32 (row3 417 463 61) _ _ _ dictionary_417 dictionary_463 dictionary_61]
  exact (gram120 (![0,0,0,0,0,-16384,7168,9152,42544,18584,8515]) (![0,0,0,0,0,0,22528,17472,10496,15616,4160]) (![0,0,0,0,0,16384,62464,34816,38640,27000,8175])).trans sorted_041
theorem gram_535 : gram (fun a=>dictionary32.getD ((row3 418 464 62) a) 0)=norm_042 := by
  rw [gram_eq_of_entries dictionary32 (row3 418 464 62) _ _ _ dictionary_418 dictionary_464 dictionary_62]
  exact (gram120 (![0,0,0,0,0,-16384,7168,9152,51184,24824,18475]) (![0,0,0,0,0,0,22528,17472,18176,23296,6080]) (![0,0,0,0,0,16384,62464,34816,47280,33240,18135])).trans sorted_042
theorem gram_536 : gram (fun a=>dictionary32.getD ((row3 420 412 399) a) 0)=norm_236 := by
  rw [gram_eq_of_entries dictionary32 (row3 420 412 399) _ _ _ dictionary_420 dictionary_412 dictionary_399]
  exact (gram210 (![0,0,0,0,0,0,13824,7296,36768,17808,67710]) (![0,0,0,0,0,0,21504,26496,19968,16128,3840]) (![0,0,0,0,0,0,23040,15360,30240,19920,66630])).trans sorted_236
theorem gram_537 : gram (fun a=>dictionary32.getD ((row3 421 396 416) a) 0)=norm_233 := by
  rw [gram_eq_of_entries dictionary32 (row3 421 396 416) _ _ _ dictionary_421 dictionary_396 dictionary_416]
  exact (gram201 (![0,0,0,0,0,0,13824,-11904,58368,33408,50610]) (![0,0,0,0,0,0,21504,45696,39168,35328,8640]) (![0,0,0,0,0,0,23040,15360,32640,25920,43530])).trans sorted_233
theorem gram_538 : gram (fun a=>dictionary32.getD ((row3 422 415 397) a) 0)=norm_234 := by
  rw [gram_eq_of_entries dictionary32 (row3 422 415 397) _ _ _ dictionary_422 dictionary_415 dictionary_397]
  exact (gram210 (![0,0,0,0,0,0,13824,-11904,59808,31248,37920]) (![0,0,0,0,0,0,21504,45696,27648,23808,5760]) (![0,0,0,0,0,0,23040,15360,34080,23760,21840])).trans sorted_234
theorem gram_539 : gram (fun a=>dictionary32.getD ((row3 424 425 425) a) 0)=norm_238 := by
  rw [gram_eq_of_entries dictionary32 (row3 424 425 425) _ _ _ dictionary_424 dictionary_425 dictionary_425]
  exact sorted_238
theorem gram_540 : gram (fun a=>dictionary32.getD ((row3 425 424 425) a) 0)=norm_238 := by
  rw [gram_eq_of_entries dictionary32 (row3 425 424 425) _ _ _ dictionary_425 dictionary_424 dictionary_425]
  exact (gram102 (![0,0,0,0,0,0,24576,36864,69632,54272,12800]) (![0,0,0,0,0,0,24576,36864,90112,74752,17920]) (![0,0,0,0,0,0,24576,36864,90112,74752,17920])).trans sorted_238
theorem gram_541 : gram (fun a=>dictionary32.getD ((row3 425 425 424) a) 0)=norm_238 := by
  rw [gram_eq_of_entries dictionary32 (row3 425 425 424) _ _ _ dictionary_425 dictionary_425 dictionary_424]
  exact (gram120 (![0,0,0,0,0,0,24576,36864,69632,54272,12800]) (![0,0,0,0,0,0,24576,36864,90112,74752,17920]) (![0,0,0,0,0,0,24576,36864,90112,74752,17920])).trans sorted_238
theorem gram_542 : gram (fun a=>dictionary32.getD ((row3 426 436 434) a) 0)=norm_239 := by
  rw [gram_eq_of_entries dictionary32 (row3 426 436 434) _ _ _ dictionary_426 dictionary_436 dictionary_434]
  exact (gram021 (![0,0,0,0,0,0,27648,4992,52896,23376,10710]) (![0,0,0,0,0,0,43008,62592,32256,24576,5760]) (![0,0,0,0,0,0,46080,30720,30240,22800,5550])).trans sorted_239
theorem gram_543 : gram (fun a=>dictionary32.getD ((row3 427 107 126) a) 0)=norm_068 := by
  rw [gram_eq_of_entries dictionary32 (row3 427 107 126) _ _ _ dictionary_427 dictionary_107 dictionary_126]
  exact (gram201 (![0,0,0,0,0,0,-30720,-111360,-38400,-91200,-40800]) (![0,0,0,0,0,0,0,-71424,-16896,-76128,-35568]) (![0,0,0,0,0,0,30720,-52224,-70656,-70368,-25968])).trans sorted_068
theorem gram_544 : gram (fun a=>dictionary32.getD ((row3 428 108 157) a) 0)=norm_069 := by
  rw [gram_eq_of_entries dictionary32 (row3 428 108 157) _ _ _ dictionary_428 dictionary_108 dictionary_157]
  exact (gram201 (![0,0,0,0,0,0,-30720,-55680,-11520,-29280,-13200]) (![0,0,0,0,0,0,0,-17280,11520,-16320,-9600]) (![0,0,0,0,0,0,30720,-15360,-30720,-17280,-4800])).trans sorted_069
theorem gram_545 : gram (fun a=>dictionary32.getD ((row3 429 456 89) a) 0)=norm_058 := by
  rw [gram_eq_of_entries dictionary32 (row3 429 456 89) _ _ _ dictionary_429 dictionary_456 dictionary_89]
  exact (gram120 (![0,0,0,0,0,-8192,17408,-128,53920,25680,18100]) (![0,0,0,0,0,0,32768,47232,25856,24576,6080]) (![0,0,0,0,0,8192,54272,32768,34080,26640,4260])).trans sorted_058
theorem gram_546 : gram (fun a=>dictionary32.getD ((row3 430 458 91) a) 0)=norm_060 := by
  rw [gram_eq_of_entries dictionary32 (row3 430 458 91) _ _ _ dictionary_430 dictionary_458 dictionary_91]
  exact (gram120 (![0,0,0,0,0,-8192,17408,-128,118720,72480,97300]) (![0,0,0,0,0,0,32768,47232,83456,82176,20480]) (![0,0,0,0,0,8192,54272,32768,98880,73440,83460])).trans sorted_060
theorem gram_547 : gram (fun a=>dictionary32.getD ((row3 431 432 432) a) 0)=norm_240 := by
  rw [gram_eq_of_entries dictionary32 (row3 431 432 432) _ _ _ dictionary_431 dictionary_432 dictionary_432]
  exact sorted_240
theorem gram_548 : gram (fun a=>dictionary32.getD ((row3 432 432 431) a) 0)=norm_240 := by
  rw [gram_eq_of_entries dictionary32 (row3 432 432 431) _ _ _ dictionary_432 dictionary_432 dictionary_431]
  exact (gram120 (![0,0,0,0,0,0,32768,49152,86016,65536,15360]) (![0,0,0,0,0,0,32768,49152,126976,106496,25600]) (![0,0,0,0,0,0,32768,49152,126976,106496,25600])).trans sorted_240
theorem gram_549 : gram (fun a=>dictionary32.getD ((row3 433 440 444) a) 0)=norm_241 := by
  rw [gram_eq_of_entries dictionary32 (row3 433 440 444) _ _ _ dictionary_433 dictionary_440 dictionary_444]
  exact sorted_241
theorem gram_550 : gram (fun a=>dictionary32.getD ((row3 433 444 440) a) 0)=norm_241 := by
  rw [gram_eq_of_entries dictionary32 (row3 433 444 440) _ _ _ dictionary_433 dictionary_444 dictionary_440]
  exact (gram021 (![0,0,0,0,0,0,41472,-6912,108864,50784,35670]) (![0,0,0,0,0,0,64512,108288,52224,40704,9600]) (![0,0,0,0,0,0,69120,46080,60480,42720,14430])).trans sorted_241
theorem gram_551 : gram (fun a=>dictionary32.getD ((row3 434 436 426) a) 0)=norm_239 := by
  rw [gram_eq_of_entries dictionary32 (row3 434 436 426) _ _ _ dictionary_434 dictionary_436 dictionary_426]
  exact (gram120 (![0,0,0,0,0,0,27648,4992,52896,23376,10710]) (![0,0,0,0,0,0,43008,62592,32256,24576,5760]) (![0,0,0,0,0,0,46080,30720,30240,22800,5550])).trans sorted_239
theorem gram_552 : gram (fun a=>dictionary32.getD ((row3 435 63 465) a) 0)=norm_043 := by
  rw [gram_eq_of_entries dictionary32 (row3 435 63 465) _ _ _ dictionary_435 dictionary_63 dictionary_465]
  exact (gram102 (![0,0,0,0,0,-16384,20992,11648,107872,58352,67690]) (![0,0,0,0,0,0,44032,48768,61184,62464,15680]) (![0,0,0,0,0,16384,85504,50176,92640,66480,64770])).trans sorted_043
theorem gram_553 : gram (fun a=>dictionary32.getD ((row3 435 465 63) a) 0)=norm_043 := by
  rw [gram_eq_of_entries dictionary32 (row3 435 465 63) _ _ _ dictionary_435 dictionary_465 dictionary_63]
  exact (gram120 (![0,0,0,0,0,-16384,20992,11648,107872,58352,67690]) (![0,0,0,0,0,0,44032,48768,61184,62464,15680]) (![0,0,0,0,0,16384,85504,50176,92640,66480,64770])).trans sorted_043
theorem gram_554 : gram (fun a=>dictionary32.getD ((row3 437 438 438) a) 0)=norm_242 := by
  rw [gram_eq_of_entries dictionary32 (row3 437 438 438) _ _ _ dictionary_437 dictionary_438 dictionary_438]
  exact sorted_242
theorem gram_555 : gram (fun a=>dictionary32.getD ((row3 438 438 437) a) 0)=norm_242 := by
  rw [gram_eq_of_entries dictionary32 (row3 438 438 437) _ _ _ dictionary_438 dictionary_438 dictionary_437]
  exact (gram120 (![0,0,0,0,0,0,49152,73728,129024,98304,23040]) (![0,0,0,0,0,0,49152,73728,144384,113664,26880]) (![0,0,0,0,0,0,49152,73728,144384,113664,26880])).trans sorted_242
theorem gram_556 : gram (fun a=>dictionary32.getD ((row3 439 446 445) a) 0)=norm_243 := by
  rw [gram_eq_of_entries dictionary32 (row3 439 446 445) _ _ _ dictionary_439 dictionary_446 dictionary_445]
  exact (gram021 (![0,0,0,0,0,0,55296,-47616,148992,68352,34920]) (![0,0,0,0,0,0,86016,182784,64512,49152,11520]) (![0,0,0,0,0,0,92160,61440,46080,38400,6600])).trans sorted_243
theorem gram_557 : gram (fun a=>dictionary32.getD ((row3 440 444 433) a) 0)=norm_241 := by
  rw [gram_eq_of_entries dictionary32 (row3 440 444 433) _ _ _ dictionary_440 dictionary_444 dictionary_433]
  exact (gram120 (![0,0,0,0,0,0,41472,-6912,108864,50784,35670]) (![0,0,0,0,0,0,64512,108288,52224,40704,9600]) (![0,0,0,0,0,0,69120,46080,60480,42720,14430])).trans sorted_241
theorem gram_558 : gram (fun a=>dictionary32.getD ((row3 441 466 65) a) 0)=norm_044 := by
  rw [gram_eq_of_entries dictionary32 (row3 441 466 65) _ _ _ dictionary_441 dictionary_466 dictionary_65]
  exact (gram120 (![0,0,0,0,0,-16384,34816,-256,150080,84000,89960]) (![0,0,0,0,0,0,65536,94464,97792,95232,23680]) (![0,0,0,0,0,16384,108544,65536,110400,85920,62280])).trans sorted_044
theorem gram_559 : gram (fun a=>dictionary32.getD ((row3 442 443 443) a) 0)=norm_244 := by
  rw [gram_eq_of_entries dictionary32 (row3 442 443 443) _ _ _ dictionary_442 dictionary_443 dictionary_443]
  exact sorted_244
theorem gram_560 : gram (fun a=>dictionary32.getD ((row3 444 440 433) a) 0)=norm_241 := by
  rw [gram_eq_of_entries dictionary32 (row3 444 440 433) _ _ _ dictionary_444 dictionary_440 dictionary_433]
  exact (gram210 (![0,0,0,0,0,0,41472,-6912,108864,50784,35670]) (![0,0,0,0,0,0,64512,108288,52224,40704,9600]) (![0,0,0,0,0,0,69120,46080,60480,42720,14430])).trans sorted_241
theorem gram_561 : gram (fun a=>dictionary32.getD ((row3 445 439 446) a) 0)=norm_243 := by
  rw [gram_eq_of_entries dictionary32 (row3 445 439 446) _ _ _ dictionary_445 dictionary_439 dictionary_446]
  exact (gram102 (![0,0,0,0,0,0,55296,-47616,148992,68352,34920]) (![0,0,0,0,0,0,86016,182784,64512,49152,11520]) (![0,0,0,0,0,0,92160,61440,46080,38400,6600])).trans sorted_243
theorem gram_562 : gram (fun a=>dictionary32.getD ((row3 445 446 439) a) 0)=norm_243 := by
  rw [gram_eq_of_entries dictionary32 (row3 445 446 439) _ _ _ dictionary_445 dictionary_446 dictionary_439]
  exact (gram120 (![0,0,0,0,0,0,55296,-47616,148992,68352,34920]) (![0,0,0,0,0,0,86016,182784,64512,49152,11520]) (![0,0,0,0,0,0,92160,61440,46080,38400,6600])).trans sorted_243
theorem gram_563 : gram (fun a=>dictionary32.getD ((row3 447 47 471) a) 0)=norm_034 := by
  rw [gram_eq_of_entries dictionary32 (row3 447 47 471) _ _ _ dictionary_447 dictionary_47 dictionary_471]
  exact (gram102 (![0,0,0,0,0,-32768,69632,-512,202880,89920,42200]) (![0,0,0,0,0,0,131072,188928,85504,80384,19840]) (![0,0,0,0,0,32768,217088,131072,120960,91200,22200])).trans sorted_034
theorem gram_564 : gram (fun a=>dictionary32.getD ((row3 452 99 355) a) 0)=norm_063 := by
  rw [gram_eq_of_entries dictionary32 (row3 452 99 355) _ _ _ dictionary_452 dictionary_99 dictionary_355]
  exact (gram201 (![0,0,0,0,0,-5120,3328,3712,9936,4296,1910]) (![0,0,0,0,0,0,3840,1280,4880,4200,1550]) (![0,0,0,0,0,5120,9728,8832,5376,4096,960])).trans sorted_063
theorem gram_565 : gram (fun a=>dictionary32.getD ((row3 453 100 369) a) 0)=norm_064 := by
  rw [gram_eq_of_entries dictionary32 (row3 453 100 369) _ _ _ dictionary_453 dictionary_100 dictionary_369]
  exact (gram201 (![0,0,0,0,0,-5120,5888,6272,17216,7936,5820]) (![0,0,0,0,0,0,6400,3840,10560,7040,4460]) (![0,0,0,0,0,5120,9728,8832,6656,5376,1280])).trans sorted_064
theorem gram_566 : gram (fun a=>dictionary32.getD ((row3 453 369 100) a) 0)=norm_064 := by
  rw [gram_eq_of_entries dictionary32 (row3 453 369 100) _ _ _ dictionary_453 dictionary_369 dictionary_100]
  exact (gram210 (![0,0,0,0,0,-5120,5888,6272,17216,7936,5820]) (![0,0,0,0,0,0,6400,3840,10560,7040,4460]) (![0,0,0,0,0,5120,9728,8832,6656,5376,1280])).trans sorted_064
theorem gram_567 : gram (fun a=>dictionary32.getD ((row3 455 88 410) a) 0)=norm_057 := by
  rw [gram_eq_of_entries dictionary32 (row3 455 88 410) _ _ _ dictionary_455 dictionary_88 dictionary_410]
  exact (gram201 (![0,0,0,0,0,-8192,8192,7808,35488,15888,7730]) (![0,0,0,0,0,0,18432,16768,10624,11904,3040]) (![0,0,0,0,0,8192,38912,22528,32160,21200,7450])).trans sorted_057
theorem gram_568 : gram (fun a=>dictionary32.getD ((row3 456 429 89) a) 0)=norm_058 := by
  rw [gram_eq_of_entries dictionary32 (row3 456 429 89) _ _ _ dictionary_456 dictionary_429 dictionary_89]
  exact (gram210 (![0,0,0,0,0,-8192,17408,-128,53920,25680,18100]) (![0,0,0,0,0,0,32768,47232,25856,24576,6080]) (![0,0,0,0,0,8192,54272,32768,34080,26640,4260])).trans sorted_058
theorem gram_569 : gram (fun a=>dictionary32.getD ((row3 458 430 91) a) 0)=norm_060 := by
  rw [gram_eq_of_entries dictionary32 (row3 458 430 91) _ _ _ dictionary_458 dictionary_430 dictionary_91]
  exact (gram210 (![0,0,0,0,0,-8192,17408,-128,118720,72480,97300]) (![0,0,0,0,0,0,32768,47232,83456,82176,20480]) (![0,0,0,0,0,8192,54272,32768,98880,73440,83460])).trans sorted_060
theorem gram_570 : gram (fun a=>dictionary32.getD ((row3 461 411 70) a) 0)=norm_048 := by
  rw [gram_eq_of_entries dictionary32 (row3 461 411 70) _ _ _ dictionary_461 dictionary_411 dictionary_70]
  exact (gram210 (![0,0,0,0,0,-15360,17664,23616,43248,19608,12210]) (![0,0,0,0,0,0,19200,11520,28080,19320,11130]) (![0,0,0,0,0,15360,29184,21696,19968,16128,3840])).trans sorted_048
theorem gram_571 : gram (fun a=>dictionary32.getD ((row3 462 68 391) a) 0)=norm_046 := by
  rw [gram_eq_of_entries dictionary32 (row3 462 68 391) _ _ _ dictionary_462 dictionary_68 dictionary_391]
  exact (gram201 (![0,0,0,0,0,-15360,7424,8576,26768,11688,5230]) (![0,0,0,0,0,0,8960,1280,11600,11400,4150]) (![0,0,0,0,0,15360,29184,26496,16128,12288,2880])).trans sorted_046
theorem gram_572 : gram (fun a=>dictionary32.getD ((row3 465 63 435) a) 0)=norm_043 := by
  rw [gram_eq_of_entries dictionary32 (row3 465 63 435) _ _ _ dictionary_465 dictionary_63 dictionary_435]
  exact (gram201 (![0,0,0,0,0,-16384,20992,11648,107872,58352,67690]) (![0,0,0,0,0,0,44032,48768,61184,62464,15680]) (![0,0,0,0,0,16384,85504,50176,92640,66480,64770])).trans sorted_043
theorem gram_573 : gram (fun a=>dictionary32.getD ((row3 466 441 65) a) 0)=norm_044 := by
  rw [gram_eq_of_entries dictionary32 (row3 466 441 65) _ _ _ dictionary_466 dictionary_441 dictionary_65]
  exact (gram210 (![0,0,0,0,0,-16384,34816,-256,150080,84000,89960]) (![0,0,0,0,0,0,65536,94464,97792,95232,23680]) (![0,0,0,0,0,16384,108544,65536,110400,85920,62280])).trans sorted_044
theorem gram_574 : gram (fun a=>dictionary32.getD ((row3 469 71 71) a) 0)=norm_049 := by
  rw [gram_eq_of_entries dictionary32 (row3 469 71 71) _ _ _ dictionary_469 dictionary_71 dictionary_71]
  exact (gram201 (![0,0,0,0,0,-15360,21504,14976,60288,35328,38340]) (![0,0,0,0,0,-15360,21504,14976,60288,35328,38340]) (![0,0,0,0,0,30720,58368,52992,39936,32256,7680])).trans sorted_049
theorem gram_575 : gram (fun a=>dictionary32.getD ((row3 472 50 72) a) 0)=norm_037 := by
  rw [gram_eq_of_entries dictionary32 (row3 472 50 72) _ _ _ dictionary_472 dictionary_50 dictionary_72]
  exact (gram201 (![0,0,0,0,0,-30720,23808,18432,69456,37896,46590]) (![0,0,0,0,0,-15360,25344,15936,54288,37608,45510]) (![0,0,0,0,0,46080,87552,74688,52224,40704,9600])).trans sorted_037
open QuarticIntegerData QuarticIntegerMembership32 QuarticIntegerNormSorted32
open QuarticIntegerListAggregates QuarticIntegerNorm QuarticIntegerGramPermutation
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem gram_576 : gram (fun a=>dictionary32.getD ((row3 473 501 28) a) 0)=norm_017 := by
  rw [gram_eq_of_entries dictionary32 (row3 473 501 28) _ _ _ dictionary_473 dictionary_501 dictionary_28]
  exact (gram120 (![0,0,0,-16384,4096,12288,37120,30400,27472,13032,4145]) (![0,0,0,0,4096,-16384,7424,18560,25680,11080,3925]) (![0,0,0,16384,49152,57344,40960,23232,10816,6336,1360])).trans sorted_017
theorem gram_577 : gram (fun a=>dictionary32.getD ((row3 474 35 488) a) 0)=norm_024 := by
  rw [gram_eq_of_entries dictionary32 (row3 474 35 488) _ _ _ dictionary_474 dictionary_35 dictionary_488]
  exact (gram102 (![0,0,0,0,-24576,-92160,-77312,-73664,-47232,-37168,-11848]) (![0,0,0,0,8192,-23552,-19456,-60928,-55168,-44784,-14664]) (![0,0,0,0,16384,-19456,-19968,-70080,-65280,-41792,-12352])).trans sorted_024
theorem gram_578 : gram (fun a=>dictionary32.getD ((row3 474 488 35) a) 0)=norm_024 := by
  rw [gram_eq_of_entries dictionary32 (row3 474 488 35) _ _ _ dictionary_474 dictionary_488 dictionary_35]
  exact (gram120 (![0,0,0,0,-24576,-92160,-77312,-73664,-47232,-37168,-11848]) (![0,0,0,0,8192,-23552,-19456,-60928,-55168,-44784,-14664]) (![0,0,0,0,16384,-19456,-19968,-70080,-65280,-41792,-12352])).trans sorted_024
theorem gram_579 : gram (fun a=>dictionary32.getD ((row3 475 41 57) a) 0)=norm_030 := by
  rw [gram_eq_of_entries dictionary32 (row3 475 41 57) _ _ _ dictionary_475 dictionary_41 dictionary_57]
  exact (gram201 (![0,0,0,0,-8192,-51200,-34304,-27584,-10368,-6768,-1768]) (![0,0,0,0,0,-23552,-15872,-32192,-28416,-19808,-5968]) (![0,0,0,0,8192,-19456,-21504,-50176,-34176,-23760,-7800])).trans sorted_030
theorem gram_580 : gram (fun a=>dictionary32.getD ((row3 475 57 41) a) 0)=norm_030 := by
  rw [gram_eq_of_entries dictionary32 (row3 475 57 41) _ _ _ dictionary_475 dictionary_57 dictionary_41]
  exact (gram210 (![0,0,0,0,-8192,-51200,-34304,-27584,-10368,-6768,-1768]) (![0,0,0,0,0,-23552,-15872,-32192,-28416,-19808,-5968]) (![0,0,0,0,8192,-19456,-21504,-50176,-34176,-23760,-7800])).trans sorted_030
theorem gram_581 : gram (fun a=>dictionary32.getD ((row3 476 40 56) a) 0)=norm_029 := by
  rw [gram_eq_of_entries dictionary32 (row3 476 40 56) _ _ _ dictionary_476 dictionary_40 dictionary_56]
  exact (gram201 (![0,0,0,0,-8192,-51200,-36864,-45824,-22528,-21408,-7568]) (![0,0,0,0,0,-23552,-15872,-48512,-39936,-38688,-13968]) (![0,0,0,0,8192,-19456,-18944,-54656,-39936,-28800,-9600])).trans sorted_029
theorem gram_582 : gram (fun a=>dictionary32.getD ((row3 476 56 40) a) 0)=norm_029 := by
  rw [gram_eq_of_entries dictionary32 (row3 476 56 40) _ _ _ dictionary_476 dictionary_56 dictionary_40]
  exact (gram210 (![0,0,0,0,-8192,-51200,-36864,-45824,-22528,-21408,-7568]) (![0,0,0,0,0,-23552,-15872,-48512,-39936,-38688,-13968]) (![0,0,0,0,8192,-19456,-18944,-54656,-39936,-28800,-9600])).trans sorted_029
theorem gram_583 : gram (fun a=>dictionary32.getD ((row3 477 42 84) a) 0)=norm_031 := by
  rw [gram_eq_of_entries dictionary32 (row3 477 42 84) _ _ _ dictionary_477 dictionary_42 dictionary_84]
  exact (gram201 (![0,0,0,0,-8192,-30720,-26624,-28480,-19072,-10960,-2840]) (![0,0,0,0,0,-9216,-4608,-15616,-15488,-11920,-3640]) (![0,0,0,0,8192,-5120,-7680,-28224,-24064,-12160,-3200])).trans sorted_031
theorem gram_584 : gram (fun a=>dictionary32.getD ((row3 478 43 106) a) 0)=norm_032 := by
  rw [gram_eq_of_entries dictionary32 (row3 478 43 106) _ _ _ dictionary_478 dictionary_43 dictionary_106]
  exact (gram201 (![0,0,0,0,-8192,-24576,-16896,-16640,-11136,-6080,-1520]) (![0,0,0,0,0,-3072,2560,-5056,-7552,-5440,-1520]) (![0,0,0,0,8192,-1024,-4096,-17472,-14592,-7520,-2000])).trans sorted_032
theorem gram_585 : gram (fun a=>dictionary32.getD ((row3 479 481 491) a) 0)=norm_245 := by
  rw [gram_eq_of_entries dictionary32 (row3 479 481 491) _ _ _ dictionary_479 dictionary_481 dictionary_491]
  exact sorted_245
theorem gram_586 : gram (fun a=>dictionary32.getD ((row3 479 491 481) a) 0)=norm_245 := by
  rw [gram_eq_of_entries dictionary32 (row3 479 491 481) _ _ _ dictionary_479 dictionary_491 dictionary_481]
  exact (gram021 (![0,0,0,0,12288,-1024,30976,28736,47152,24472,15980]) (![0,0,0,0,12288,9216,30464,19328,37168,23768,15100]) (![0,0,0,0,16384,36864,41472,20544,15872,16512,4160])).trans sorted_245
theorem gram_587 : gram (fun a=>dictionary32.getD ((row3 480 480 492) a) 0)=norm_246 := by
  rw [gram_eq_of_entries dictionary32 (row3 480 480 492) _ _ _ dictionary_480 dictionary_480 dictionary_492]
  exact sorted_246
theorem gram_588 : gram (fun a=>dictionary32.getD ((row3 480 492 480) a) 0)=norm_246 := by
  rw [gram_eq_of_entries dictionary32 (row3 480 492 480) _ _ _ dictionary_480 dictionary_492 dictionary_480]
  exact (gram021 (![0,0,0,0,12288,-1024,35840,24192,67600,40680,33200]) (![0,0,0,0,12288,-1024,35840,24192,67600,40680,33200]) (![0,0,0,0,16384,47104,64512,45824,34432,31872,7840])).trans sorted_246
theorem gram_589 : gram (fun a=>dictionary32.getD ((row3 481 491 479) a) 0)=norm_245 := by
  rw [gram_eq_of_entries dictionary32 (row3 481 491 479) _ _ _ dictionary_481 dictionary_491 dictionary_479]
  exact (gram120 (![0,0,0,0,12288,-1024,30976,28736,47152,24472,15980]) (![0,0,0,0,12288,9216,30464,19328,37168,23768,15100]) (![0,0,0,0,16384,36864,41472,20544,15872,16512,4160])).trans sorted_245
theorem gram_590 : gram (fun a=>dictionary32.getD ((row3 482 34 484) a) 0)=norm_023 := by
  rw [gram_eq_of_entries dictionary32 (row3 482 34 484) _ _ _ dictionary_482 dictionary_34 dictionary_484]
  exact (gram102 (![0,0,0,0,-32768,-143360,-111616,-119168,-75520,-93216,-36016]) (![0,0,0,0,16384,-43008,-40960,-126720,-109568,-93056,-31616]) (![0,0,0,0,16384,-43008,-35840,-123008,-119040,-100192,-33872])).trans sorted_023
theorem gram_591 : gram (fun a=>dictionary32.getD ((row3 482 484 34) a) 0)=norm_023 := by
  rw [gram_eq_of_entries dictionary32 (row3 482 484 34) _ _ _ dictionary_482 dictionary_484 dictionary_34]
  exact (gram120 (![0,0,0,0,-32768,-143360,-111616,-119168,-75520,-93216,-36016]) (![0,0,0,0,16384,-43008,-40960,-126720,-109568,-93056,-31616]) (![0,0,0,0,16384,-43008,-35840,-123008,-119040,-100192,-33872])).trans sorted_023
theorem gram_592 : gram (fun a=>dictionary32.getD ((row3 483 33 483) a) 0)=norm_022 := by
  rw [gram_eq_of_entries dictionary32 (row3 483 33 483) _ _ _ dictionary_483 dictionary_33 dictionary_483]
  exact (gram102 (![0,0,0,0,-32768,-143360,-116736,-134656,-79872,-86272,-31872]) (![0,0,0,0,16384,-43008,-35840,-139008,-125440,-108992,-37472]) (![0,0,0,0,16384,-43008,-35840,-139008,-125440,-108992,-37472])).trans sorted_022
theorem gram_593 : gram (fun a=>dictionary32.getD ((row3 483 483 33) a) 0)=norm_022 := by
  rw [gram_eq_of_entries dictionary32 (row3 483 483 33) _ _ _ dictionary_483 dictionary_483 dictionary_33]
  exact (gram120 (![0,0,0,0,-32768,-143360,-116736,-134656,-79872,-86272,-31872]) (![0,0,0,0,16384,-43008,-35840,-139008,-125440,-108992,-37472]) (![0,0,0,0,16384,-43008,-35840,-139008,-125440,-108992,-37472])).trans sorted_022
theorem gram_594 : gram (fun a=>dictionary32.getD ((row3 485 36 44) a) 0)=norm_025 := by
  rw [gram_eq_of_entries dictionary32 (row3 485 36 44) _ _ _ dictionary_485 dictionary_36 dictionary_44]
  exact (gram201 (![0,0,0,0,-16384,-102400,-68608,-55168,-20736,-35936,-14736]) (![0,0,0,0,0,-47104,-31744,-69504,-61952,-66496,-24736]) (![0,0,0,0,16384,-38912,-43008,-95232,-63232,-43040,-14000])).trans sorted_025
theorem gram_595 : gram (fun a=>dictionary32.getD ((row3 485 44 36) a) 0)=norm_025 := by
  rw [gram_eq_of_entries dictionary32 (row3 485 44 36) _ _ _ dictionary_485 dictionary_44 dictionary_36]
  exact (gram210 (![0,0,0,0,-16384,-102400,-68608,-55168,-20736,-35936,-14736]) (![0,0,0,0,0,-47104,-31744,-69504,-61952,-66496,-24736]) (![0,0,0,0,16384,-38912,-43008,-95232,-63232,-43040,-14000])).trans sorted_025
theorem gram_596 : gram (fun a=>dictionary32.getD ((row3 486 37 45) a) 0)=norm_026 := by
  rw [gram_eq_of_entries dictionary32 (row3 486 37 45) _ _ _ dictionary_486 dictionary_37 dictionary_45]
  exact (gram201 (![0,0,0,0,-16384,-90112,-54272,-51200,-27392,-43040,-17840]) (![0,0,0,0,0,-34816,-17408,-43136,-36608,-49600,-19840]) (![0,0,0,0,16384,-30720,-30720,-62848,-45568,-22880,-6000])).trans sorted_026
theorem gram_597 : gram (fun a=>dictionary32.getD ((row3 487 29 502) a) 0)=norm_018 := by
  rw [gram_eq_of_entries dictionary32 (row3 487 29 502) _ _ _ dictionary_487 dictionary_29 dictionary_502]
  exact (gram102 (![0,0,0,-16384,16384,25600,60416,39296,50992,31992,14825]) (![0,0,0,0,16384,-26624,19968,35968,62640,29240,15445]) (![0,0,0,16384,65536,99328,86528,48640,27520,21120,4960])).trans sorted_018
theorem gram_598 : gram (fun a=>dictionary32.getD ((row3 487 502 29) a) 0)=norm_018 := by
  rw [gram_eq_of_entries dictionary32 (row3 487 502 29) _ _ _ dictionary_487 dictionary_502 dictionary_29]
  exact (gram120 (![0,0,0,-16384,16384,25600,60416,39296,50992,31992,14825]) (![0,0,0,0,16384,-26624,19968,35968,62640,29240,15445]) (![0,0,0,16384,65536,99328,86528,48640,27520,21120,4960])).trans sorted_018
theorem gram_599 : gram (fun a=>dictionary32.getD ((row3 488 35 474) a) 0)=norm_024 := by
  rw [gram_eq_of_entries dictionary32 (row3 488 35 474) _ _ _ dictionary_488 dictionary_35 dictionary_474]
  exact (gram201 (![0,0,0,0,-24576,-92160,-77312,-73664,-47232,-37168,-11848]) (![0,0,0,0,8192,-23552,-19456,-60928,-55168,-44784,-14664]) (![0,0,0,0,16384,-19456,-19968,-70080,-65280,-41792,-12352])).trans sorted_024
theorem gram_600 : gram (fun a=>dictionary32.getD ((row3 489 38 51) a) 0)=norm_027 := by
  rw [gram_eq_of_entries dictionary32 (row3 489 38 51) _ _ _ dictionary_489 dictionary_38 dictionary_51]
  exact (gram201 (![0,0,0,0,-16384,-71680,-58368,-56000,-32384,-32080,-11480]) (![0,0,0,0,0,-25600,-14848,-44928,-40192,-43680,-16080]) (![0,0,0,0,16384,-17408,-20992,-58944,-47744,-23760,-6200])).trans sorted_027
theorem gram_601 : gram (fun a=>dictionary32.getD ((row3 490 39 73) a) 0)=norm_028 := by
  rw [gram_eq_of_entries dictionary32 (row3 490 39 73) _ _ _ dictionary_490 dictionary_39 dictionary_73]
  exact (gram201 (![0,0,0,0,-16384,-59392,-38912,-33920,-19712,-14720,-4640]) (![0,0,0,0,0,-13312,-512,-17088,-19200,-16840,-5540]) (![0,0,0,0,16384,-9216,-13824,-39360,-30720,-15560,-4100])).trans sorted_028
theorem gram_602 : gram (fun a=>dictionary32.getD ((row3 491 481 479) a) 0)=norm_245 := by
  rw [gram_eq_of_entries dictionary32 (row3 491 481 479) _ _ _ dictionary_491 dictionary_481 dictionary_479]
  exact (gram210 (![0,0,0,0,12288,-1024,30976,28736,47152,24472,15980]) (![0,0,0,0,12288,9216,30464,19328,37168,23768,15100]) (![0,0,0,0,16384,36864,41472,20544,15872,16512,4160])).trans sorted_245
theorem gram_603 : gram (fun a=>dictionary32.getD ((row3 492 480 480) a) 0)=norm_246 := by
  rw [gram_eq_of_entries dictionary32 (row3 492 480 480) _ _ _ dictionary_492 dictionary_480 dictionary_480]
  exact (gram201 (![0,0,0,0,12288,-1024,35840,24192,67600,40680,33200]) (![0,0,0,0,12288,-1024,35840,24192,67600,40680,33200]) (![0,0,0,0,16384,47104,64512,45824,34432,31872,7840])).trans sorted_246
theorem gram_604 : gram (fun a=>dictionary32.getD ((row3 493 493 500) a) 0)=norm_247 := by
  rw [gram_eq_of_entries dictionary32 (row3 493 493 500) _ _ _ dictionary_493 dictionary_493 dictionary_500]
  exact sorted_247
theorem gram_605 : gram (fun a=>dictionary32.getD ((row3 494 495 499) a) 0)=norm_248 := by
  rw [gram_eq_of_entries dictionary32 (row3 494 495 499) _ _ _ dictionary_494 dictionary_495 dictionary_499]
  exact sorted_248
theorem gram_606 : gram (fun a=>dictionary32.getD ((row3 494 499 495) a) 0)=norm_248 := by
  rw [gram_eq_of_entries dictionary32 (row3 494 499 495) _ _ _ dictionary_494 dictionary_499 dictionary_495]
  exact (gram021 (![0,0,0,0,24576,-2048,58112,51072,111664,65144,55410]) (![0,0,0,0,24576,13312,56576,34688,96752,63832,54010]) (![0,0,0,0,32768,78848,92672,49920,56320,56320,14080])).trans sorted_248
theorem gram_607 : gram (fun a=>dictionary32.getD ((row3 495 499 494) a) 0)=norm_248 := by
  rw [gram_eq_of_entries dictionary32 (row3 495 499 494) _ _ _ dictionary_495 dictionary_499 dictionary_494]
  exact (gram120 (![0,0,0,0,24576,-2048,58112,51072,111664,65144,55410]) (![0,0,0,0,24576,13312,56576,34688,96752,63832,54010]) (![0,0,0,0,32768,78848,92672,49920,56320,56320,14080])).trans sorted_248
theorem gram_608 : gram (fun a=>dictionary32.getD ((row3 496 30 505) a) 0)=norm_019 := by
  rw [gram_eq_of_entries dictionary32 (row3 496 30 505) _ _ _ dictionary_496 dictionary_30 dictionary_505]
  exact (gram102 (![0,0,0,-16384,28672,43008,109312,59392,99840,71840,39620]) (![0,0,0,0,28672,-51200,44800,71168,136448,66848,42260]) (![0,0,0,16384,81920,151552,157696,83968,56064,50944,12480])).trans sorted_019
theorem gram_609 : gram (fun a=>dictionary32.getD ((row3 496 505 30) a) 0)=norm_019 := by
  rw [gram_eq_of_entries dictionary32 (row3 496 505 30) _ _ _ dictionary_496 dictionary_505 dictionary_30]
  exact (gram120 (![0,0,0,-16384,28672,43008,109312,59392,99840,71840,39620]) (![0,0,0,0,28672,-51200,44800,71168,136448,66848,42260]) (![0,0,0,16384,81920,151552,157696,83968,56064,50944,12480])).trans sorted_019
theorem gram_610 : gram (fun a=>dictionary32.getD ((row3 497 31 504) a) 0)=norm_020 := by
  rw [gram_eq_of_entries dictionary32 (row3 497 31 504) _ _ _ dictionary_497 dictionary_31 dictionary_504]
  exact (gram102 (![0,0,0,-16384,28672,48128,127744,72320,105504,74864,33440]) (![0,0,0,0,28672,-51200,51456,63232,151200,70320,40800]) (![0,0,0,16384,81920,146432,162304,105600,55040,48640,11840])).trans sorted_020
theorem gram_611 : gram (fun a=>dictionary32.getD ((row3 497 504 31) a) 0)=norm_020 := by
  rw [gram_eq_of_entries dictionary32 (row3 497 504 31) _ _ _ dictionary_497 dictionary_504 dictionary_31]
  exact (gram120 (![0,0,0,-16384,28672,48128,127744,72320,105504,74864,33440]) (![0,0,0,0,28672,-51200,51456,63232,151200,70320,40800]) (![0,0,0,16384,81920,146432,162304,105600,55040,48640,11840])).trans sorted_020
theorem gram_612 : gram (fun a=>dictionary32.getD ((row3 498 503 32) a) 0)=norm_021 := by
  rw [gram_eq_of_entries dictionary32 (row3 498 503 32) _ _ _ dictionary_498 dictionary_503 dictionary_32]
  exact (gram120 (![0,0,0,-16384,28672,53248,114176,72128,73808,45288,14610]) (![0,0,0,0,28672,-20480,40448,52480,85904,36744,14490]) (![0,0,0,16384,81920,110592,94208,45376,14848,17408,4480])).trans sorted_021
theorem gram_613 : gram (fun a=>dictionary32.getD ((row3 499 495 494) a) 0)=norm_248 := by
  rw [gram_eq_of_entries dictionary32 (row3 499 495 494) _ _ _ dictionary_499 dictionary_495 dictionary_494]
  exact (gram210 (![0,0,0,0,24576,-2048,58112,51072,111664,65144,55410]) (![0,0,0,0,24576,13312,56576,34688,96752,63832,54010]) (![0,0,0,0,32768,78848,92672,49920,56320,56320,14080])).trans sorted_248
theorem gram_614 : gram (fun a=>dictionary32.getD ((row3 500 493 493) a) 0)=norm_247 := by
  rw [gram_eq_of_entries dictionary32 (row3 500 493 493) _ _ _ dictionary_500 dictionary_493 dictionary_493]
  exact (gram201 (![0,0,0,0,24576,-2048,24576,18048,103392,67312,90780]) (![0,0,0,0,24576,-2048,24576,18048,103392,67312,90780]) (![0,0,0,0,32768,94208,92160,58112,78336,70656,17280])).trans sorted_247
theorem gram_615 : gram (fun a=>dictionary32.getD ((row3 502 29 487) a) 0)=norm_018 := by
  rw [gram_eq_of_entries dictionary32 (row3 502 29 487) _ _ _ dictionary_502 dictionary_29 dictionary_487]
  exact (gram201 (![0,0,0,-16384,16384,25600,60416,39296,50992,31992,14825]) (![0,0,0,0,16384,-26624,19968,35968,62640,29240,15445]) (![0,0,0,16384,65536,99328,86528,48640,27520,21120,4960])).trans sorted_018
theorem gram_616 : gram (fun a=>dictionary32.getD ((row3 504 31 497) a) 0)=norm_020 := by
  rw [gram_eq_of_entries dictionary32 (row3 504 31 497) _ _ _ dictionary_504 dictionary_31 dictionary_497]
  exact (gram201 (![0,0,0,-16384,28672,48128,127744,72320,105504,74864,33440]) (![0,0,0,0,28672,-51200,51456,63232,151200,70320,40800]) (![0,0,0,16384,81920,146432,162304,105600,55040,48640,11840])).trans sorted_020
theorem gram_617 : gram (fun a=>dictionary32.getD ((row3 504 497 31) a) 0)=norm_020 := by
  rw [gram_eq_of_entries dictionary32 (row3 504 497 31) _ _ _ dictionary_504 dictionary_497 dictionary_31]
  exact (gram210 (![0,0,0,-16384,28672,48128,127744,72320,105504,74864,33440]) (![0,0,0,0,28672,-51200,51456,63232,151200,70320,40800]) (![0,0,0,16384,81920,146432,162304,105600,55040,48640,11840])).trans sorted_020
theorem gram_618 : gram (fun a=>dictionary32.getD ((row3 508 190 190) a) 0)=norm_111 := by
  rw [gram_eq_of_entries dictionary32 (row3 508 190 190) _ _ _ dictionary_508 dictionary_190 dictionary_190]
  exact (gram201 (![0,0,0,0,0,0,0,-7680,-7680,-4320,-1200]) (![0,0,0,0,0,0,0,-7680,-7680,-4320,-1200]) (0)).trans sorted_111
theorem gram_619 : gram (fun a=>dictionary32.getD ((row3 508 210 210) a) 0)=norm_121 := by
  rw [gram_eq_of_entries dictionary32 (row3 508 210 210) _ _ _ dictionary_508 dictionary_210 dictionary_210]
  exact (gram201 (![0,0,0,0,0,0,0,-5120,-5120,-4480,-1600]) (![0,0,0,0,0,0,0,-5120,-5120,-4480,-1600]) (0)).trans sorted_121
theorem gram_620 : gram (fun a=>dictionary32.getD ((row3 508 211 211) a) 0)=norm_122 := by
  rw [gram_eq_of_entries dictionary32 (row3 508 211 211) _ _ _ dictionary_508 dictionary_211 dictionary_211]
  exact (gram201 (![0,0,0,0,0,0,0,-5120,-5120,-2880,-800]) (![0,0,0,0,0,0,0,-5120,-5120,-2880,-800]) (0)).trans sorted_122
theorem gram_621 : gram (fun a=>dictionary32.getD ((row3 508 234 234) a) 0)=norm_131 := by
  rw [gram_eq_of_entries dictionary32 (row3 508 234 234) _ _ _ dictionary_508 dictionary_234 dictionary_234]
  exact (gram201 (![0,0,0,0,0,0,0,-2560,-2560,-2240,-800]) (![0,0,0,0,0,0,0,-2560,-2560,-2240,-800]) (0)).trans sorted_131
theorem gram_622 : gram (fun a=>dictionary32.getD ((row3 508 258 258) a) 0)=norm_139 := by
  rw [gram_eq_of_entries dictionary32 (row3 508 258 258) _ _ _ dictionary_508 dictionary_258 dictionary_258]
  exact (gram201 (![0,0,0,0,0,0,0,0,0,-14400,-7200]) (![0,0,0,0,0,0,0,0,0,-14400,-7200]) (0)).trans sorted_139
theorem gram_623 : gram (fun a=>dictionary32.getD ((row3 508 262 262) a) 0)=norm_143 := by
  rw [gram_eq_of_entries dictionary32 (row3 508 262 262) _ _ _ dictionary_508 dictionary_262 dictionary_262]
  exact (gram201 (![0,0,0,0,0,0,0,0,0,-9600,-4800]) (![0,0,0,0,0,0,0,0,0,-9600,-4800]) (0)).trans sorted_143
theorem gram_624 : gram (fun a=>dictionary32.getD ((row3 508 265 265) a) 0)=norm_147 := by
  rw [gram_eq_of_entries dictionary32 (row3 508 265 265) _ _ _ dictionary_508 dictionary_265 dictionary_265]
  exact (gram201 (![0,0,0,0,0,0,0,0,0,-7200,-3600]) (![0,0,0,0,0,0,0,0,0,-7200,-3600]) (0)).trans sorted_147
theorem gram_625 : gram (fun a=>dictionary32.getD ((row3 508 268 268) a) 0)=norm_150 := by
  rw [gram_eq_of_entries dictionary32 (row3 508 268 268) _ _ _ dictionary_508 dictionary_268 dictionary_268]
  exact (gram201 (![0,0,0,0,0,0,0,0,0,-4800,-2400]) (![0,0,0,0,0,0,0,0,0,-4800,-2400]) (0)).trans sorted_150
theorem gram_626 : gram (fun a=>dictionary32.getD ((row3 508 271 271) a) 0)=norm_152 := by
  rw [gram_eq_of_entries dictionary32 (row3 508 271 271) _ _ _ dictionary_508 dictionary_271 dictionary_271]
  exact (gram201 (![0,0,0,0,0,0,0,0,0,-2400,-1200]) (![0,0,0,0,0,0,0,0,0,-2400,-1200]) (0)).trans sorted_152
theorem gram_627 : gram (fun a=>dictionary32.getD ((row3 508 272 272) a) 0)=norm_153 := by
  rw [gram_eq_of_entries dictionary32 (row3 508 272 272) _ _ _ dictionary_508 dictionary_272 dictionary_272]
  exact (gram201 (![0,0,0,0,0,0,0,0,0,-1600,-800]) (![0,0,0,0,0,0,0,0,0,-1600,-800]) (0)).trans sorted_153
theorem gram_628 : gram (fun a=>dictionary32.getD ((row3 508 273 273) a) 0)=norm_154 := by
  rw [gram_eq_of_entries dictionary32 (row3 508 273 273) _ _ _ dictionary_508 dictionary_273 dictionary_273]
  exact (gram201 (![0,0,0,0,0,0,0,0,0,-800,-400]) (![0,0,0,0,0,0,0,0,0,-800,-400]) (0)).trans sorted_154
theorem gram_629 : gram (fun a=>dictionary32.getD ((row3 508 275 275) a) 0)=norm_156 := by
  rw [gram_eq_of_entries dictionary32 (row3 508 275 275) _ _ _ dictionary_508 dictionary_275 dictionary_275]
  exact (gram201 (![0,0,0,0,0,0,0,0,0,0,3000]) (![0,0,0,0,0,0,0,0,0,0,3000]) (0)).trans sorted_156
theorem gram_630 : gram (fun a=>dictionary32.getD ((row3 508 276 276) a) 0)=norm_157 := by
  rw [gram_eq_of_entries dictionary32 (row3 508 276 276) _ _ _ dictionary_508 dictionary_276 dictionary_276]
  exact (gram201 (![0,0,0,0,0,0,0,0,0,0,4500]) (![0,0,0,0,0,0,0,0,0,0,4500]) (0)).trans sorted_157
theorem gram_631 : gram (fun a=>dictionary32.getD ((row3 508 277 277) a) 0)=norm_158 := by
  rw [gram_eq_of_entries dictionary32 (row3 508 277 277) _ _ _ dictionary_508 dictionary_277 dictionary_277]
  exact (gram201 (![0,0,0,0,0,0,0,0,0,0,7500]) (![0,0,0,0,0,0,0,0,0,0,7500]) (0)).trans sorted_158
theorem gram_632 : gram (fun a=>dictionary32.getD ((row3 508 278 278) a) 0)=norm_159 := by
  rw [gram_eq_of_entries dictionary32 (row3 508 278 278) _ _ _ dictionary_508 dictionary_278 dictionary_278]
  exact (gram201 (![0,0,0,0,0,0,0,0,0,0,9000]) (![0,0,0,0,0,0,0,0,0,0,9000]) (0)).trans sorted_159
theorem gram_633 : gram (fun a=>dictionary32.getD ((row3 508 279 279) a) 0)=norm_160 := by
  rw [gram_eq_of_entries dictionary32 (row3 508 279 279) _ _ _ dictionary_508 dictionary_279 dictionary_279]
  exact (gram201 (![0,0,0,0,0,0,0,0,0,0,13500]) (![0,0,0,0,0,0,0,0,0,0,13500]) (0)).trans sorted_160
theorem gram_634 : gram (fun a=>dictionary32.getD ((row3 508 280 280) a) 0)=norm_161 := by
  rw [gram_eq_of_entries dictionary32 (row3 508 280 280) _ _ _ dictionary_508 dictionary_280 dictionary_280]
  exact (gram201 (![0,0,0,0,0,0,0,0,0,0,18000]) (![0,0,0,0,0,0,0,0,0,0,18000]) (0)).trans sorted_161
theorem gram_635 : gram (fun a=>dictionary32.getD ((row3 508 285 285) a) 0)=norm_164 := by
  rw [gram_eq_of_entries dictionary32 (row3 508 285 285) _ _ _ dictionary_508 dictionary_285 dictionary_285]
  exact (gram201 (![0,0,0,0,0,0,0,0,1600,800,2500]) (![0,0,0,0,0,0,0,0,1600,800,2500]) (0)).trans sorted_164
theorem gram_636 : gram (fun a=>dictionary32.getD ((row3 508 287 287) a) 0)=norm_166 := by
  rw [gram_eq_of_entries dictionary32 (row3 508 287 287) _ _ _ dictionary_508 dictionary_287 dictionary_287]
  exact (gram201 (![0,0,0,0,0,0,0,0,2400,1200,1000]) (![0,0,0,0,0,0,0,0,2400,1200,1000]) (0)).trans sorted_166
theorem gram_637 : gram (fun a=>dictionary32.getD ((row3 508 289 289) a) 0)=norm_167 := by
  rw [gram_eq_of_entries dictionary32 (row3 508 289 289) _ _ _ dictionary_508 dictionary_289 dictionary_289]
  exact (gram201 (![0,0,0,0,0,0,0,0,2400,1200,15000]) (![0,0,0,0,0,0,0,0,2400,1200,15000]) (0)).trans sorted_167
theorem gram_638 : gram (fun a=>dictionary32.getD ((row3 508 290 290) a) 0)=norm_169 := by
  rw [gram_eq_of_entries dictionary32 (row3 508 290 290) _ _ _ dictionary_508 dictionary_290 dictionary_290]
  exact (gram201 (![0,0,0,0,0,0,0,0,2560,2560,640]) (![0,0,0,0,0,0,0,0,2560,2560,640]) (0)).trans sorted_169
theorem gram_639 : gram (fun a=>dictionary32.getD ((row3 508 303 303) a) 0)=norm_179 := by
  rw [gram_eq_of_entries dictionary32 (row3 508 303 303) _ _ _ dictionary_508 dictionary_303 dictionary_303]
  exact (gram201 (![0,0,0,0,0,0,0,0,4800,2400,1500]) (![0,0,0,0,0,0,0,0,4800,2400,1500]) (0)).trans sorted_179
open QuarticIntegerData QuarticIntegerMembership32 QuarticIntegerNormSorted32
open QuarticIntegerListAggregates QuarticIntegerNorm QuarticIntegerGramPermutation
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem gram_640 : gram (fun a=>dictionary32.getD ((row3 508 304 304) a) 0)=norm_180 := by
  rw [gram_eq_of_entries dictionary32 (row3 508 304 304) _ _ _ dictionary_508 dictionary_304 dictionary_304]
  exact (gram201 (![0,0,0,0,0,0,0,0,4800,2400,3000]) (![0,0,0,0,0,0,0,0,4800,2400,3000]) (0)).trans sorted_180
theorem gram_641 : gram (fun a=>dictionary32.getD ((row3 508 305 305) a) 0)=norm_181 := by
  rw [gram_eq_of_entries dictionary32 (row3 508 305 305) _ _ _ dictionary_508 dictionary_305 dictionary_305]
  exact (gram201 (![0,0,0,0,0,0,0,0,4800,2400,7500]) (![0,0,0,0,0,0,0,0,4800,2400,7500]) (0)).trans sorted_181
theorem gram_642 : gram (fun a=>dictionary32.getD ((row3 508 307 307) a) 0)=norm_185 := by
  rw [gram_eq_of_entries dictionary32 (row3 508 307 307) _ _ _ dictionary_508 dictionary_307 dictionary_307]
  exact (gram201 (![0,0,0,0,0,0,0,0,5120,5120,1280]) (![0,0,0,0,0,0,0,0,5120,5120,1280]) (0)).trans sorted_185
theorem gram_643 : gram (fun a=>dictionary32.getD ((row3 508 316 316) a) 0)=norm_194 := by
  rw [gram_eq_of_entries dictionary32 (row3 508 316 316) _ _ _ dictionary_508 dictionary_316 dictionary_316]
  exact (gram201 (![0,0,0,0,0,0,0,0,9600,4800,3000]) (![0,0,0,0,0,0,0,0,9600,4800,3000]) (0)).trans sorted_194
theorem gram_644 : gram (fun a=>dictionary32.getD ((row3 508 317 317) a) 0)=norm_195 := by
  rw [gram_eq_of_entries dictionary32 (row3 508 317 317) _ _ _ dictionary_508 dictionary_317 dictionary_317]
  exact (gram201 (![0,0,0,0,0,0,0,0,9600,4800,6000]) (![0,0,0,0,0,0,0,0,9600,4800,6000]) (0)).trans sorted_195
theorem gram_645 : gram (fun a=>dictionary32.getD ((row3 508 319 319) a) 0)=norm_197 := by
  rw [gram_eq_of_entries dictionary32 (row3 508 319 319) _ _ _ dictionary_508 dictionary_319 dictionary_319]
  exact (gram201 (![0,0,0,0,0,0,0,0,10240,10240,2560]) (![0,0,0,0,0,0,0,0,10240,10240,2560]) (0)).trans sorted_197
theorem gram_646 : gram (fun a=>dictionary32.getD ((row3 508 326 326) a) 0)=norm_204 := by
  rw [gram_eq_of_entries dictionary32 (row3 508 326 326) _ _ _ dictionary_508 dictionary_326 dictionary_326]
  exact (gram201 (![0,0,0,0,0,0,0,0,14400,7200,4500]) (![0,0,0,0,0,0,0,0,14400,7200,4500]) (0)).trans sorted_204
theorem gram_647 : gram (fun a=>dictionary32.getD ((row3 508 330 330) a) 0)=norm_207 := by
  rw [gram_eq_of_entries dictionary32 (row3 508 330 330) _ _ _ dictionary_508 dictionary_330 dictionary_330]
  exact (gram201 (![0,0,0,0,0,0,0,0,19200,9600,7500]) (![0,0,0,0,0,0,0,0,19200,9600,7500]) (0)).trans sorted_207
theorem gram_648 : gram (fun a=>dictionary32.getD ((row3 508 353 353) a) 0)=norm_218 := by
  rw [gram_eq_of_entries dictionary32 (row3 508 353 353) _ _ _ dictionary_508 dictionary_353 dictionary_353]
  exact (gram201 (![0,0,0,0,0,0,2560,2560,3840,1600,1000]) (![0,0,0,0,0,0,2560,2560,3840,1600,1000]) (0)).trans sorted_218
theorem gram_649 : gram (fun a=>dictionary32.getD ((row3 508 367 367) a) 0)=norm_226 := by
  rw [gram_eq_of_entries dictionary32 (row3 508 367 367) _ _ _ dictionary_508 dictionary_367 dictionary_367]
  exact (gram201 (![0,0,0,0,0,0,5120,5120,6080,2400,1000]) (![0,0,0,0,0,0,5120,5120,6080,2400,1000]) (0)).trans sorted_226
theorem gram_650 : gram (fun a=>dictionary32.getD ((row3 508 508 508) a) 0)=norm_249 := by
  rw [gram_eq_of_entries dictionary32 (row3 508 508 508) _ _ _ dictionary_508 dictionary_508 dictionary_508]
  exact sorted_249
end BilayerDressed.QuarticIntegerNormCases32
