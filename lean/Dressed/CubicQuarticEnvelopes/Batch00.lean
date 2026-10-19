import Dressed.CubicQuarticCoefficientBernstein

/-! Explicit scalar polynomial envelopes, not graph/coefficient identification.
Generated from frozen rational data; every sign and basis coefficient is checked
by the Lean kernel. No oracle, sampling, or floating-point premise is used. -/
noncomputable section
namespace BilayerDressed.CubicQuarticEnvelopes
open CubicResidualCoefficients CubicQuarticCoefficientBernstein
set_option maxHeartbeats 2000000
set_option maxRecDepth 200000

def coefficients0000 : Fin 11 → ℚ := ![0, 0, 0, 0, (-21/8), (-3/4), (-33/16), (-15/16), 0, 0, 0]

def upper0000 : ℚ := (8709/32000000)

def plusWeights0000 : Fin 11 → ℚ := ![(8709/32000000), (8709/3200000), (78381/6400000), (26127/800000), (182049/3200000), (536007/8000000), (212703/4000000), (874413/32000000), (2631/320000), (35217/32000000), 0]

def minusWeights0000 : Fin 11 → ℚ := ![(8709/32000000), (8709/3200000), (78381/6400000), (26127/800000), (183729/3200000), (561327/8000000), (489039/8000000), (1215747/32000000), (52071/3200000), (138963/32000000), (8709/16000000)]

theorem checked0000 :
    (∀ i, 0 ≤ plusWeights0000 i) ∧
    (∀ i, 0 ≤ minusWeights0000 i) ∧
    (∀ i, plusCoefficients coefficients0000 upper0000 i = powerCoefficients10 plusWeights0000 i) ∧
    (∀ i, minusCoefficients coefficients0000 upper0000 i = powerCoefficients10 minusWeights0000 i) := by
  decide +kernel

theorem bound0000 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0000 g| ≤ (upper0000 : ℝ) :=
  abs_of_coefficients coefficients0000 upper0000 powerCoefficients10 plusWeights0000 minusWeights0000
    checked0000.1 checked0000.2.1 checked0000.2.2.1 checked0000.2.2.2
    (power_identity10 plusWeights0000) (power_identity10 minusWeights0000) g hg hmax

def envelope0000 : Envelope := ⟨coefficients0000, upper0000, bound0000⟩

def coefficients0001 : Fin 11 → ℚ := ![0, 0, 0, 0, -1, (1/4), (-19/16), (-5/8), 0, 0, 0]

def upper0001 : ℚ := (79/800000)

def plusWeights0001 : Fin 11 → ℚ := ![(79/800000), (79/80000), (711/160000), (237/20000), (1651/80000), (1943/80000), (307981/16000000), (157923/16000000), (47383/16000000), (6321/16000000), 0]

def minusWeights0001 : Fin 11 → ℚ := ![(79/800000), (79/80000), (711/160000), (237/20000), (1667/80000), (10193/400000), (355619/16000000), (221277/16000000), (94817/16000000), (25279/16000000), (79/400000)]

theorem checked0001 :
    (∀ i, 0 ≤ plusWeights0001 i) ∧
    (∀ i, 0 ≤ minusWeights0001 i) ∧
    (∀ i, plusCoefficients coefficients0001 upper0001 i = powerCoefficients10 plusWeights0001 i) ∧
    (∀ i, minusCoefficients coefficients0001 upper0001 i = powerCoefficients10 minusWeights0001 i) := by
  decide +kernel

theorem bound0001 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0001 g| ≤ (upper0001 : ℝ) :=
  abs_of_coefficients coefficients0001 upper0001 powerCoefficients10 plusWeights0001 minusWeights0001
    checked0001.1 checked0001.2.1 checked0001.2.2.1 checked0001.2.2.2
    (power_identity10 plusWeights0001) (power_identity10 minusWeights0001) g hg hmax

def envelope0001 : Envelope := ⟨coefficients0001, upper0001, bound0001⟩

def coefficients0002 : Fin 11 → ℚ := ![0, 0, 0, 0, (-1/32), (27/64), (9/16), (747/512), 0, 0, 0]

def upper0002 : ℚ := (9227/5120000000)

def plusWeights0002 : Fin 11 → ℚ := ![(9227/5120000000), (9227/512000000), (83043/1024000000), (27681/128000000), (192167/512000000), (562701/1280000000), (36171/102400000), (1015507/5120000000), (25671/320000000), (118031/5120000000), (9227/2560000000)]

def minusWeights0002 : Fin 11 → ℚ := ![(9227/5120000000), (9227/512000000), (83043/1024000000), (27681/128000000), (195367/512000000), (599901/1280000000), (206679/512000000), (1198973/5120000000), (209847/2560000000), (66509/5120000000), 0]

theorem checked0002 :
    (∀ i, 0 ≤ plusWeights0002 i) ∧
    (∀ i, 0 ≤ minusWeights0002 i) ∧
    (∀ i, plusCoefficients coefficients0002 upper0002 i = powerCoefficients10 plusWeights0002 i) ∧
    (∀ i, minusCoefficients coefficients0002 upper0002 i = powerCoefficients10 minusWeights0002 i) := by
  decide +kernel

theorem bound0002 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0002 g| ≤ (upper0002 : ℝ) :=
  abs_of_coefficients coefficients0002 upper0002 powerCoefficients10 plusWeights0002 minusWeights0002
    checked0002.1 checked0002.2.1 checked0002.2.2.1 checked0002.2.2.2
    (power_identity10 plusWeights0002) (power_identity10 minusWeights0002) g hg hmax

def envelope0002 : Envelope := ⟨coefficients0002, upper0002, bound0002⟩

def coefficients0003 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (225/1024), 0, 0, 0]

def upper0003 : ℚ := (9/409600000)

def plusWeights0003 : Fin 11 → ℚ := ![(9/409600000), (9/40960000), (81/81920000), (27/10240000), (189/40960000), (567/102400000), (189/40960000), (1089/409600000), (27/25600000), (117/409600000), (9/204800000)]

def minusWeights0003 : Fin 11 → ℚ := ![(9/409600000), (9/40960000), (81/81920000), (27/10240000), (189/40960000), (567/102400000), (189/40960000), (1071/409600000), (189/204800000), (63/409600000), 0]

theorem checked0003 :
    (∀ i, 0 ≤ plusWeights0003 i) ∧
    (∀ i, 0 ≤ minusWeights0003 i) ∧
    (∀ i, plusCoefficients coefficients0003 upper0003 i = powerCoefficients10 plusWeights0003 i) ∧
    (∀ i, minusCoefficients coefficients0003 upper0003 i = powerCoefficients10 minusWeights0003 i) := by
  decide +kernel

theorem bound0003 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0003 g| ≤ (upper0003 : ℝ) :=
  abs_of_coefficients coefficients0003 upper0003 powerCoefficients10 plusWeights0003 minusWeights0003
    checked0003.1 checked0003.2.1 checked0003.2.2.1 checked0003.2.2.2
    (power_identity10 plusWeights0003) (power_identity10 minusWeights0003) g hg hmax

def envelope0003 : Envelope := ⟨coefficients0003, upper0003, bound0003⟩

def coefficients0004 : Fin 11 → ℚ := ![0, 0, 0, 0, (9/16), (9/64), (21/64), (111/256), 0, 0, 0]

def upper0004 : ℚ := (148551/2560000000)

def plusWeights0004 : Fin 11 → ℚ := ![(148551/2560000000), (148551/256000000), (1336959/512000000), (445653/64000000), (3133971/256000000), (9575613/640000000), (667491/51200000), (20745591/2560000000), (1110771/320000000), (2371203/2560000000), (148551/1280000000)]

def minusWeights0004 : Fin 11 → ℚ := ![(148551/2560000000), (148551/256000000), (1336959/512000000), (445653/64000000), (3105171/256000000), (9141813/640000000), (2901687/256000000), (14906649/2560000000), (2241711/1280000000), (599817/2560000000), 0]

theorem checked0004 :
    (∀ i, 0 ≤ plusWeights0004 i) ∧
    (∀ i, 0 ≤ minusWeights0004 i) ∧
    (∀ i, plusCoefficients coefficients0004 upper0004 i = powerCoefficients10 plusWeights0004 i) ∧
    (∀ i, minusCoefficients coefficients0004 upper0004 i = powerCoefficients10 minusWeights0004 i) := by
  decide +kernel

theorem bound0004 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0004 g| ≤ (upper0004 : ℝ) :=
  abs_of_coefficients coefficients0004 upper0004 powerCoefficients10 plusWeights0004 minusWeights0004
    checked0004.1 checked0004.2.1 checked0004.2.2.1 checked0004.2.2.2
    (power_identity10 plusWeights0004) (power_identity10 minusWeights0004) g hg hmax

def envelope0004 : Envelope := ⟨coefficients0004, upper0004, bound0004⟩

def coefficients0005 : Fin 11 → ℚ := ![0, 0, 0, (-1/16), (-1/16), (-11/64), (-1/8), (-241/1024), (-107/512), (-609/4096), (-373/8192)]

def upper0005 : ℚ := (5785151753/81920000000000)

def plusWeights0005 : Fin 11 → ℚ := ![(5785151753/81920000000000), (5785151753/8192000000000), (52066365777/16384000000000), (17227455259/2048000000000), (117852986813/8192000000000), (336781360439/20480000000000), (102728762813/8192000000000), (12583183059/2048000000000), (28731286737/16384000000000), (363768379/1638400000000), 0]

def minusWeights0005 : Fin 11 → ℚ := ![(5785151753/81920000000000), (5785151753/8192000000000), (52066365777/16384000000000), (17483455259/2048000000000), (125123386813/8192000000000), (392147760439/20480000000000), (140247610813/8192000000000), (22127727459/2048000000000), (75401444817/16384000000000), (9751461611/8192000000000), (5785151753/40960000000000)]

theorem checked0005 :
    (∀ i, 0 ≤ plusWeights0005 i) ∧
    (∀ i, 0 ≤ minusWeights0005 i) ∧
    (∀ i, plusCoefficients coefficients0005 upper0005 i = powerCoefficients10 plusWeights0005 i) ∧
    (∀ i, minusCoefficients coefficients0005 upper0005 i = powerCoefficients10 minusWeights0005 i) := by
  decide +kernel

theorem bound0005 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0005 g| ≤ (upper0005 : ℝ) :=
  abs_of_coefficients coefficients0005 upper0005 powerCoefficients10 plusWeights0005 minusWeights0005
    checked0005.1 checked0005.2.1 checked0005.2.2.1 checked0005.2.2.2
    (power_identity10 plusWeights0005) (power_identity10 minusWeights0005) g hg hmax

def envelope0005 : Envelope := ⟨coefficients0005, upper0005, bound0005⟩

def coefficients0006 : Fin 11 → ℚ := ![0, 0, 0, (-1/16), (1/32), (-1/64), (47/256), (191/1024), (475/2048), (465/4096), (825/16384)]

def upper0006 : ℚ := (388802583/6553600000000)

def plusWeights0006 : Fin 11 → ℚ := ![(388802583/6553600000000), (388802583/655360000000), (3499223247/1310720000000), (1156167749/163840000000), (7880182243/655360000000), (22374626729/1638400000000), (6761582563/655360000000), (6544921/1310720000), (1839815471/1310720000000), (571898247/3276800000000), 0]

def minusWeights0006 : Fin 11 → ℚ := ![(388802583/6553600000000), (388802583/655360000000), (3499223247/1310720000000), (1176647749/163840000000), (8449526243/655360000000), (26614498729/1638400000000), (9568125923/655360000000), (1514700373/163840000000), (5158631023/1310720000000), (3316127583/3276800000000), (388802583/3276800000000)]

theorem checked0006 :
    (∀ i, 0 ≤ plusWeights0006 i) ∧
    (∀ i, 0 ≤ minusWeights0006 i) ∧
    (∀ i, plusCoefficients coefficients0006 upper0006 i = powerCoefficients10 plusWeights0006 i) ∧
    (∀ i, minusCoefficients coefficients0006 upper0006 i = powerCoefficients10 minusWeights0006 i) := by
  decide +kernel

theorem bound0006 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0006 g| ≤ (upper0006 : ℝ) :=
  abs_of_coefficients coefficients0006 upper0006 powerCoefficients10 plusWeights0006 minusWeights0006
    checked0006.1 checked0006.2.1 checked0006.2.2.1 checked0006.2.2.2
    (power_identity10 plusWeights0006) (power_identity10 minusWeights0006) g hg hmax

def envelope0006 : Envelope := ⟨coefficients0006, upper0006, bound0006⟩

def coefficients0007 : Fin 11 → ℚ := ![0, 0, 0, (-1/32), (7/128), (21/256), (261/1024), (307/2048), (2015/8192), (2745/16384), (5965/65536)]

def upper0007 : ℚ := (3235961647/131072000000000)

def plusWeights0007 : Fin 11 → ℚ := ![(3235961647/131072000000000), (3235961647/13107200000000), (29123654823/26214400000000), (9605484941/3276800000000), (65159674587/13107200000000), (183463663761/32768000000000), (54751495387/13107200000000), (6512554861/3276800000000), (14327227783/26214400000000), (866620963/13107200000000), 0]

def minusWeights0007 : Fin 11 → ℚ := ![(3235961647/131072000000000), (3235961647/13107200000000), (29123654823/26214400000000), (9810284941/3276800000000), (70750714587/13107200000000), (224267503761/32768000000000), (81158893787/13107200000000), (12903215021/3276800000000), (43920081863/26214400000000), (5605302331/13107200000000), (3235961647/65536000000000)]

theorem checked0007 :
    (∀ i, 0 ≤ plusWeights0007 i) ∧
    (∀ i, 0 ≤ minusWeights0007 i) ∧
    (∀ i, plusCoefficients coefficients0007 upper0007 i = powerCoefficients10 plusWeights0007 i) ∧
    (∀ i, minusCoefficients coefficients0007 upper0007 i = powerCoefficients10 minusWeights0007 i) := by
  decide +kernel

theorem bound0007 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0007 g| ≤ (upper0007 : ℝ) :=
  abs_of_coefficients coefficients0007 upper0007 powerCoefficients10 plusWeights0007 minusWeights0007
    checked0007.1 checked0007.2.1 checked0007.2.2.1 checked0007.2.2.2
    (power_identity10 plusWeights0007) (power_identity10 minusWeights0007) g hg hmax

def envelope0007 : Envelope := ⟨coefficients0007, upper0007, bound0007⟩

def coefficients0008 : Fin 11 → ℚ := ![0, 0, 0, 0, (-1/16), (-35/128), (-57/256), (-283/1024), (-11/64), (-447/2048), (-349/4096)]

def upper0008 : ℚ := (378331689/40960000000000)

def plusWeights0008 : Fin 11 → ℚ := ![(378331689/40960000000000), (378331689/4096000000000), (3404985201/8192000000000), (1134995067/1024000000000), (7919365469/4096000000000), (23422896407/10240000000000), (7504053469/4096000000000), (978054767/1024000000000), (2401347921/8192000000000), (32945823/819200000000), 0]

def minusWeights0008 : Fin 11 → ℚ := ![(378331689/40960000000000), (378331689/4096000000000), (3404985201/8192000000000), (1134995067/1024000000000), (7970565469/4096000000000), (24246896407/10240000000000), (8385877469/4096000000000), (1291935367/1024000000000), (4408622481/8192000000000), (591934263/4096000000000), (378331689/20480000000000)]

theorem checked0008 :
    (∀ i, 0 ≤ plusWeights0008 i) ∧
    (∀ i, 0 ≤ minusWeights0008 i) ∧
    (∀ i, plusCoefficients coefficients0008 upper0008 i = powerCoefficients10 plusWeights0008 i) ∧
    (∀ i, minusCoefficients coefficients0008 upper0008 i = powerCoefficients10 minusWeights0008 i) := by
  decide +kernel

theorem bound0008 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0008 g| ≤ (upper0008 : ℝ) :=
  abs_of_coefficients coefficients0008 upper0008 powerCoefficients10 plusWeights0008 minusWeights0008
    checked0008.1 checked0008.2.1 checked0008.2.2.1 checked0008.2.2.2
    (power_identity10 plusWeights0008) (power_identity10 minusWeights0008) g hg hmax

def envelope0008 : Envelope := ⟨coefficients0008, upper0008, bound0008⟩

def coefficients0009 : Fin 11 → ℚ := ![0, 0, 0, 0, (-1/32), (-25/128), (-9/64), (-179/1024), (-11/128), (-21/128), (-287/4096)]

def upper0009 : ℚ := (214518207/40960000000000)

def plusWeights0009 : Fin 11 → ℚ := ![(214518207/40960000000000), (214518207/4096000000000), (1930663863/8192000000000), (643554621/1024000000000), (4492082347/4096000000000), (13302647041/10240000000000), (4272306347/4096000000000), (558960721/1024000000000), (1379315223/8192000000000), (19038339/819200000000), 0]

def minusWeights0009 : Fin 11 → ℚ := ![(214518207/40960000000000), (214518207/4096000000000), (1930663863/8192000000000), (643554621/1024000000000), (4517682347/4096000000000), (13726647041/10240000000000), (4737458347/4096000000000), (728148521/1024000000000), (2482012503/8192000000000), (333844719/4096000000000), (214518207/20480000000000)]

theorem checked0009 :
    (∀ i, 0 ≤ plusWeights0009 i) ∧
    (∀ i, 0 ≤ minusWeights0009 i) ∧
    (∀ i, plusCoefficients coefficients0009 upper0009 i = powerCoefficients10 plusWeights0009 i) ∧
    (∀ i, minusCoefficients coefficients0009 upper0009 i = powerCoefficients10 minusWeights0009 i) := by
  decide +kernel

theorem bound0009 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0009 g| ≤ (upper0009 : ℝ) :=
  abs_of_coefficients coefficients0009 upper0009 powerCoefficients10 plusWeights0009 minusWeights0009
    checked0009.1 checked0009.2.1 checked0009.2.2.1 checked0009.2.2.2
    (power_identity10 plusWeights0009) (power_identity10 minusWeights0009) g hg hmax

def envelope0009 : Envelope := ⟨coefficients0009, upper0009, bound0009⟩

def coefficients0010 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (-23/256), (-31/512), (-379/2048), (-39/256), (-471/2048), (-387/4096)]

def upper0010 : ℚ := (40110207/40960000000000)

def plusWeights0010 : Fin 11 → ℚ := ![(40110207/40960000000000), (40110207/4096000000000), (360991863/8192000000000), (120330621/1024000000000), (842314347/4096000000000), (2517743041/10240000000000), (823666347/4096000000000), (110863671/1024000000000), (283948583/8192000000000), (4095477/819200000000), 0]

def minusWeights0010 : Fin 11 → ℚ := ![(40110207/40960000000000), (40110207/4096000000000), (360991863/8192000000000), (120330621/1024000000000), (842314347/4096000000000), (2536143041/10240000000000), (860962347/4096000000000), (129797571/1024000000000), (438035143/8192000000000), (59743029/4096000000000), (40110207/20480000000000)]

theorem checked0010 :
    (∀ i, 0 ≤ plusWeights0010 i) ∧
    (∀ i, 0 ≤ minusWeights0010 i) ∧
    (∀ i, plusCoefficients coefficients0010 upper0010 i = powerCoefficients10 plusWeights0010 i) ∧
    (∀ i, minusCoefficients coefficients0010 upper0010 i = powerCoefficients10 minusWeights0010 i) := by
  decide +kernel

theorem bound0010 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0010 g| ≤ (upper0010 : ℝ) :=
  abs_of_coefficients coefficients0010 upper0010 powerCoefficients10 plusWeights0010 minusWeights0010
    checked0010.1 checked0010.2.1 checked0010.2.2.1 checked0010.2.2.2
    (power_identity10 plusWeights0010) (power_identity10 minusWeights0010) g hg hmax

def envelope0010 : Envelope := ⟨coefficients0010, upper0010, bound0010⟩

def coefficients0011 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (-1/16), (17/128), (-1/1024), (1835/4096), (1755/8192), (5275/32768)]

def upper0011 : ℚ := (6390741/13107200000000)

def plusWeights0011 : Fin 11 → ℚ := ![(6390741/13107200000000), (6390741/1310720000000), (57516669/2621440000000), (19172223/327680000000), (134205561/1310720000000), (400568683/3276800000000), (130283641/1310720000000), (17298271/327680000000), (8646521/524288000000), (15013509/6553600000000), 0]

def minusWeights0011 : Fin 11 → ℚ := ![(6390741/13107200000000), (6390741/1310720000000), (57516669/2621440000000), (19172223/327680000000), (134205561/1310720000000), (404664683/3276800000000), (138127481/1310720000000), (841847/13107200000), (71800733/2621440000000), (48893901/6553600000000), (6390741/6553600000000)]

theorem checked0011 :
    (∀ i, 0 ≤ plusWeights0011 i) ∧
    (∀ i, 0 ≤ minusWeights0011 i) ∧
    (∀ i, plusCoefficients coefficients0011 upper0011 i = powerCoefficients10 plusWeights0011 i) ∧
    (∀ i, minusCoefficients coefficients0011 upper0011 i = powerCoefficients10 minusWeights0011 i) := by
  decide +kernel

theorem bound0011 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0011 g| ≤ (upper0011 : ℝ) :=
  abs_of_coefficients coefficients0011 upper0011 powerCoefficients10 plusWeights0011 minusWeights0011
    checked0011.1 checked0011.2.1 checked0011.2.2.1 checked0011.2.2.2
    (power_identity10 plusWeights0011) (power_identity10 minusWeights0011) g hg hmax

def envelope0011 : Envelope := ⟨coefficients0011, upper0011, bound0011⟩

def coefficients0012 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (-15/256), (21/256), (117/2048), (471/2048), (69/512), (9855/32768)]

def upper0012 : ℚ := (32488077/65536000000000)

def plusWeights0012 : Fin 11 → ℚ := ![(32488077/65536000000000), (32488077/6553600000000), (292392693/13107200000000), (97464231/1638400000000), (682249617/6553600000000), (2037148851/16384000000000), (663587217/6553600000000), (88411191/1638400000000), (222298677/13107200000000), (77909121/32768000000000), 0]

def minusWeights0012 : Fin 11 → ℚ := ![(32488077/65536000000000), (32488077/6553600000000), (292392693/13107200000000), (97464231/1638400000000), (682249617/6553600000000), (2056348851/16384000000000), (700912017/6553600000000), (106517271/1638400000000), (362486709/13107200000000), (246971649/32768000000000), (32488077/32768000000000)]

theorem checked0012 :
    (∀ i, 0 ≤ plusWeights0012 i) ∧
    (∀ i, 0 ≤ minusWeights0012 i) ∧
    (∀ i, plusCoefficients coefficients0012 upper0012 i = powerCoefficients10 plusWeights0012 i) ∧
    (∀ i, minusCoefficients coefficients0012 upper0012 i = powerCoefficients10 minusWeights0012 i) := by
  decide +kernel

theorem bound0012 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0012 g| ≤ (upper0012 : ℝ) :=
  abs_of_coefficients coefficients0012 upper0012 powerCoefficients10 plusWeights0012 minusWeights0012
    checked0012.1 checked0012.2.1 checked0012.2.2.1 checked0012.2.2.2
    (power_identity10 plusWeights0012) (power_identity10 minusWeights0012) g hg hmax

def envelope0012 : Envelope := ⟨coefficients0012, upper0012, bound0012⟩

def coefficients0013 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (-3/64), (-29/256), (-641/2048), (-23/128), (-3033/8192), (-2621/16384)]

def upper0013 : ℚ := (100845681/163840000000000)

def plusWeights0013 : Fin 11 → ℚ := ![(100845681/163840000000000), (100845681/16384000000000), (907611129/32768000000000), (302537043/4096000000000), (2117759301/16384000000000), (6334077903/40960000000000), (2077503301/16384000000000), (281352843/4096000000000), (728603449/32768000000000), (10683667/3276800000000), 0]

def minusWeights0013 : Fin 11 → ℚ := ![(100845681/163840000000000), (100845681/16384000000000), (907611129/32768000000000), (302537043/4096000000000), (2117759301/16384000000000), (6372477903/40960000000000), (2158015301/16384000000000), (323721243/4096000000000), (1086618809/32768000000000), (148273027/16384000000000), (100845681/81920000000000)]

theorem checked0013 :
    (∀ i, 0 ≤ plusWeights0013 i) ∧
    (∀ i, 0 ≤ minusWeights0013 i) ∧
    (∀ i, plusCoefficients coefficients0013 upper0013 i = powerCoefficients10 plusWeights0013 i) ∧
    (∀ i, minusCoefficients coefficients0013 upper0013 i = powerCoefficients10 minusWeights0013 i) := by
  decide +kernel

theorem bound0013 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0013 g| ≤ (upper0013 : ℝ) :=
  abs_of_coefficients coefficients0013 upper0013 powerCoefficients10 plusWeights0013 minusWeights0013
    checked0013.1 checked0013.2.1 checked0013.2.2.1 checked0013.2.2.2
    (power_identity10 plusWeights0013) (power_identity10 minusWeights0013) g hg hmax

def envelope0013 : Envelope := ⟨coefficients0013, upper0013, bound0013⟩

def coefficients0014 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (-1/32), (17/256), (-1/2048), (3455/8192), (4095/16384), (24715/65536)]

def upper0014 : ℚ := (31671897/131072000000000)

def plusWeights0014 : Fin 11 → ℚ := ![(31671897/131072000000000), (31671897/13107200000000), (285047073/26214400000000), (95015691/3276800000000), (665109837/13107200000000), (1985089511/32768000000000), (645500237/13107200000000), (85645931/3276800000000), (213678593/26214400000000), (14785413/13107200000000), 0]

def minusWeights0014 : Fin 11 → ℚ := ![(31671897/131072000000000), (31671897/13107200000000), (285047073/26214400000000), (95015691/3276800000000), (665109837/13107200000000), (2005569511/32768000000000), (684719437/13107200000000), (104385451/3276800000000), (356415553/26214400000000), (48558381/13107200000000), (31671897/65536000000000)]

theorem checked0014 :
    (∀ i, 0 ≤ plusWeights0014 i) ∧
    (∀ i, 0 ≤ minusWeights0014 i) ∧
    (∀ i, plusCoefficients coefficients0014 upper0014 i = powerCoefficients10 plusWeights0014 i) ∧
    (∀ i, minusCoefficients coefficients0014 upper0014 i = powerCoefficients10 minusWeights0014 i) := by
  decide +kernel

theorem bound0014 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0014 g| ≤ (upper0014 : ℝ) :=
  abs_of_coefficients coefficients0014 upper0014 powerCoefficients10 plusWeights0014 minusWeights0014
    checked0014.1 checked0014.2.1 checked0014.2.2.1 checked0014.2.2.2
    (power_identity10 plusWeights0014) (power_identity10 minusWeights0014) g hg hmax

def envelope0014 : Envelope := ⟨coefficients0014, upper0014, bound0014⟩

def coefficients0015 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (-1/32), (9/128), (-29/128), (-37/128), (-657/2048), (-499/4096)]

def upper0015 : ℚ := (10980039/40960000000000)

def plusWeights0015 : Fin 11 → ℚ := ![(10980039/40960000000000), (10980039/4096000000000), (98820351/8192000000000), (32940117/1024000000000), (230580819/4096000000000), (688542457/10240000000000), (224468819/4096000000000), (30004917/1024000000000), (76095871/8192000000000), (1085729/819200000000), 0]

def minusWeights0015 : Fin 11 → ℚ := ![(10980039/40960000000000), (10980039/4096000000000), (98820351/8192000000000), (32940117/1024000000000), (230580819/4096000000000), (694942457/10240000000000), (236692819/4096000000000), (35875317/1024000000000), (121544831/8192000000000), (16531433/4096000000000), (10980039/20480000000000)]

theorem checked0015 :
    (∀ i, 0 ≤ plusWeights0015 i) ∧
    (∀ i, 0 ≤ minusWeights0015 i) ∧
    (∀ i, plusCoefficients coefficients0015 upper0015 i = powerCoefficients10 plusWeights0015 i) ∧
    (∀ i, minusCoefficients coefficients0015 upper0015 i = powerCoefficients10 minusWeights0015 i) := by
  decide +kernel

theorem bound0015 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0015 g| ≤ (upper0015 : ℝ) :=
  abs_of_coefficients coefficients0015 upper0015 powerCoefficients10 plusWeights0015 minusWeights0015
    checked0015.1 checked0015.2.1 checked0015.2.2.1 checked0015.2.2.2
    (power_identity10 plusWeights0015) (power_identity10 minusWeights0015) g hg hmax

def envelope0015 : Envelope := ⟨coefficients0015, upper0015, bound0015⟩

def coefficients0016 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (-15/256), (-495/2048), (-105/1024), (-1155/4096), (-525/4096)]

def upper0016 : ℚ := (137763/1638400000000)

def plusWeights0016 : Fin 11 → ℚ := ![(137763/1638400000000), (137763/163840000000), (1239867/327680000000), (413289/40960000000), (2893023/163840000000), (8679069/409600000000), (2883423/163840000000), (402699/40960000000), (1100571/327680000000), (27219/51200000000), 0]

def minusWeights0016 : Fin 11 → ℚ := ![(137763/1638400000000), (137763/163840000000), (1239867/327680000000), (413289/40960000000), (2893023/163840000000), (8679069/409600000000), (2902623/163840000000), (423879/40960000000), (1379163/327680000000), (471063/409600000000), (137763/819200000000)]

theorem checked0016 :
    (∀ i, 0 ≤ plusWeights0016 i) ∧
    (∀ i, 0 ≤ minusWeights0016 i) ∧
    (∀ i, plusCoefficients coefficients0016 upper0016 i = powerCoefficients10 plusWeights0016 i) ∧
    (∀ i, minusCoefficients coefficients0016 upper0016 i = powerCoefficients10 minusWeights0016 i) := by
  decide +kernel

theorem bound0016 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0016 g| ≤ (upper0016 : ℝ) :=
  abs_of_coefficients coefficients0016 upper0016 powerCoefficients10 plusWeights0016 minusWeights0016
    checked0016.1 checked0016.2.1 checked0016.2.2.1 checked0016.2.2.2
    (power_identity10 plusWeights0016) (power_identity10 minusWeights0016) g hg hmax

def envelope0016 : Envelope := ⟨coefficients0016, upper0016, bound0016⟩

def coefficients0017 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-225/1024), (1575/4096), (1575/8192), (7875/32768)]

def upper0017 : ℚ := (46953/2621440000000)

def plusWeights0017 : Fin 11 → ℚ := ![(46953/2621440000000), (46953/262144000000), (422577/524288000000), (140859/65536000000), (986013/262144000000), (2958039/655360000000), (986013/262144000000), (139419/65536000000), (390033/524288000000), (158697/1310720000000), 0]

def minusWeights0017 : Fin 11 → ℚ := ![(46953/2621440000000), (46953/262144000000), (422577/524288000000), (140859/65536000000), (986013/262144000000), (2958039/655360000000), (986013/262144000000), (142299/65536000000), (455121/524288000000), (310833/1310720000000), (46953/1310720000000)]

theorem checked0017 :
    (∀ i, 0 ≤ plusWeights0017 i) ∧
    (∀ i, 0 ≤ minusWeights0017 i) ∧
    (∀ i, plusCoefficients coefficients0017 upper0017 i = powerCoefficients10 plusWeights0017 i) ∧
    (∀ i, minusCoefficients coefficients0017 upper0017 i = powerCoefficients10 minusWeights0017 i) := by
  decide +kernel

theorem bound0017 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0017 g| ≤ (upper0017 : ℝ) :=
  abs_of_coefficients coefficients0017 upper0017 powerCoefficients10 plusWeights0017 minusWeights0017
    checked0017.1 checked0017.2.1 checked0017.2.2.1 checked0017.2.2.2
    (power_identity10 plusWeights0017) (power_identity10 minusWeights0017) g hg hmax

def envelope0017 : Envelope := ⟨coefficients0017, upper0017, bound0017⟩

def coefficients0018 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-393/2048), (-3/32), (-2589/8192), (-2373/16384)]

def upper0018 : ℚ := (3351753/163840000000000)

def plusWeights0018 : Fin 11 → ℚ := ![(3351753/163840000000000), (3351753/16384000000000), (30165777/32768000000000), (10055259/4096000000000), (70386813/16384000000000), (211160439/40960000000000), (70386813/16384000000000), (9976659/4096000000000), (28248657/32768000000000), (474531/3276800000000), 0]

def minusWeights0018 : Fin 11 → ℚ := ![(3351753/163840000000000), (3351753/16384000000000), (30165777/32768000000000), (10055259/4096000000000), (70386813/16384000000000), (211160439/40960000000000), (70386813/16384000000000), (10133859/4096000000000), (32082897/32768000000000), (4330851/16384000000000), (3351753/81920000000000)]

theorem checked0018 :
    (∀ i, 0 ≤ plusWeights0018 i) ∧
    (∀ i, 0 ≤ minusWeights0018 i) ∧
    (∀ i, plusCoefficients coefficients0018 upper0018 i = powerCoefficients10 plusWeights0018 i) ∧
    (∀ i, minusCoefficients coefficients0018 upper0018 i = powerCoefficients10 minusWeights0018 i) := by
  decide +kernel

theorem bound0018 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0018 g| ≤ (upper0018 : ℝ) :=
  abs_of_coefficients coefficients0018 upper0018 powerCoefficients10 plusWeights0018 minusWeights0018
    checked0018.1 checked0018.2.1 checked0018.2.2.1 checked0018.2.2.2
    (power_identity10 plusWeights0018) (power_identity10 minusWeights0018) g hg hmax

def envelope0018 : Envelope := ⟨coefficients0018, upper0018, bound0018⟩

def coefficients0019 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-21/128), (-3/16), (-2139/4096), (-1923/8192)]

def upper0019 : ℚ := (1542303/81920000000000)

def plusWeights0019 : Fin 11 → ℚ := ![(1542303/81920000000000), (1542303/8192000000000), (13880727/16384000000000), (4626909/2048000000000), (32388363/8192000000000), (97165089/20480000000000), (32388363/8192000000000), (4593309/2048000000000), (13043607/16384000000000), (220821/1638400000000), 0]

def minusWeights0019 : Fin 11 → ℚ := ![(1542303/81920000000000), (1542303/8192000000000), (13880727/16384000000000), (4626909/2048000000000), (32388363/8192000000000), (97165089/20480000000000), (32388363/8192000000000), (4660509/2048000000000), (14717847/16384000000000), (1980501/8192000000000), (1542303/40960000000000)]

theorem checked0019 :
    (∀ i, 0 ≤ plusWeights0019 i) ∧
    (∀ i, 0 ≤ minusWeights0019 i) ∧
    (∀ i, plusCoefficients coefficients0019 upper0019 i = powerCoefficients10 plusWeights0019 i) ∧
    (∀ i, minusCoefficients coefficients0019 upper0019 i = powerCoefficients10 minusWeights0019 i) := by
  decide +kernel

theorem bound0019 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0019 g| ≤ (upper0019 : ℝ) :=
  abs_of_coefficients coefficients0019 upper0019 powerCoefficients10 plusWeights0019 minusWeights0019
    checked0019.1 checked0019.2.1 checked0019.2.2.1 checked0019.2.2.2
    (power_identity10 plusWeights0019) (power_identity10 minusWeights0019) g hg hmax

def envelope0019 : Envelope := ⟨coefficients0019, upper0019, bound0019⟩

def coefficients0020 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (675/4096), (675/8192), (3375/32768)]

def upper0020 : ℚ := (4563/2621440000000)

def plusWeights0020 : Fin 11 → ℚ := ![(4563/2621440000000), (4563/262144000000), (41067/524288000000), (13689/65536000000), (95823/262144000000), (287469/655360000000), (95823/262144000000), (13689/65536000000), (41931/524288000000), (27243/1310720000000), (4563/1310720000000)]

def minusWeights0020 : Fin 11 → ℚ := ![(4563/2621440000000), (4563/262144000000), (41067/524288000000), (13689/65536000000), (95823/262144000000), (287469/655360000000), (95823/262144000000), (13689/65536000000), (40203/524288000000), (18387/1310720000000), 0]

theorem checked0020 :
    (∀ i, 0 ≤ plusWeights0020 i) ∧
    (∀ i, 0 ≤ minusWeights0020 i) ∧
    (∀ i, plusCoefficients coefficients0020 upper0020 i = powerCoefficients10 plusWeights0020 i) ∧
    (∀ i, minusCoefficients coefficients0020 upper0020 i = powerCoefficients10 minusWeights0020 i) := by
  decide +kernel

theorem bound0020 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0020 g| ≤ (upper0020 : ℝ) :=
  abs_of_coefficients coefficients0020 upper0020 powerCoefficients10 plusWeights0020 minusWeights0020
    checked0020.1 checked0020.2.1 checked0020.2.2.1 checked0020.2.2.2
    (power_identity10 plusWeights0020) (power_identity10 minusWeights0020) g hg hmax

def envelope0020 : Envelope := ⟨coefficients0020, upper0020, bound0020⟩

def coefficients0021 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (15/64), (15/64), (15/256)]

def upper0021 : ℚ := (1323/512000000000)

def plusWeights0021 : Fin 11 → ℚ := ![(1323/512000000000), (1323/51200000000), (11907/102400000000), (3969/12800000000), (27783/51200000000), (83349/128000000000), (27783/51200000000), (3969/12800000000), (12147/102400000000), (63/2048000000), (1323/256000000000)]

def minusWeights0021 : Fin 11 → ℚ := ![(1323/512000000000), (1323/51200000000), (11907/102400000000), (3969/12800000000), (27783/51200000000), (83349/128000000000), (27783/51200000000), (3969/12800000000), (11667/102400000000), (1071/51200000000), 0]

theorem checked0021 :
    (∀ i, 0 ≤ plusWeights0021 i) ∧
    (∀ i, 0 ≤ minusWeights0021 i) ∧
    (∀ i, plusCoefficients coefficients0021 upper0021 i = powerCoefficients10 plusWeights0021 i) ∧
    (∀ i, minusCoefficients coefficients0021 upper0021 i = powerCoefficients10 minusWeights0021 i) := by
  decide +kernel

theorem bound0021 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0021 g| ≤ (upper0021 : ℝ) :=
  abs_of_coefficients coefficients0021 upper0021 powerCoefficients10 plusWeights0021 minusWeights0021
    checked0021.1 checked0021.2.1 checked0021.2.2.1 checked0021.2.2.2
    (power_identity10 plusWeights0021) (power_identity10 minusWeights0021) g hg hmax

def envelope0021 : Envelope := ⟨coefficients0021, upper0021, bound0021⟩

def coefficients0022 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (45/128), (45/128), (45/512)]

def upper0022 : ℚ := (3969/1024000000000)

def plusWeights0022 : Fin 11 → ℚ := ![(3969/1024000000000), (3969/102400000000), (35721/204800000000), (11907/25600000000), (83349/102400000000), (250047/256000000000), (83349/102400000000), (11907/25600000000), (36441/204800000000), (189/4096000000), (3969/512000000000)]

def minusWeights0022 : Fin 11 → ℚ := ![(3969/1024000000000), (3969/102400000000), (35721/204800000000), (11907/25600000000), (83349/102400000000), (250047/256000000000), (83349/102400000000), (11907/25600000000), (35001/204800000000), (3213/102400000000), 0]

theorem checked0022 :
    (∀ i, 0 ≤ plusWeights0022 i) ∧
    (∀ i, 0 ≤ minusWeights0022 i) ∧
    (∀ i, plusCoefficients coefficients0022 upper0022 i = powerCoefficients10 plusWeights0022 i) ∧
    (∀ i, minusCoefficients coefficients0022 upper0022 i = powerCoefficients10 minusWeights0022 i) := by
  decide +kernel

theorem bound0022 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0022 g| ≤ (upper0022 : ℝ) :=
  abs_of_coefficients coefficients0022 upper0022 powerCoefficients10 plusWeights0022 minusWeights0022
    checked0022.1 checked0022.2.1 checked0022.2.2.1 checked0022.2.2.2
    (power_identity10 plusWeights0022) (power_identity10 minusWeights0022) g hg hmax

def envelope0022 : Envelope := ⟨coefficients0022, upper0022, bound0022⟩

def coefficients0023 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (405/1024), (585/2048), (1215/2048)]

def upper0023 : ℚ := (17613/4096000000000)

def plusWeights0023 : Fin 11 → ℚ := ![(17613/4096000000000), (17613/409600000000), (158517/819200000000), (52839/102400000000), (369873/409600000000), (1109619/1024000000000), (369873/409600000000), (52839/102400000000), (161757/819200000000), (2097/40960000000), (17613/2048000000000)]

def minusWeights0023 : Fin 11 → ℚ := ![(17613/4096000000000), (17613/409600000000), (158517/819200000000), (52839/102400000000), (369873/409600000000), (1109619/1024000000000), (369873/409600000000), (52839/102400000000), (155277/819200000000), (891/25600000000), 0]

theorem checked0023 :
    (∀ i, 0 ≤ plusWeights0023 i) ∧
    (∀ i, 0 ≤ minusWeights0023 i) ∧
    (∀ i, plusCoefficients coefficients0023 upper0023 i = powerCoefficients10 plusWeights0023 i) ∧
    (∀ i, minusCoefficients coefficients0023 upper0023 i = powerCoefficients10 minusWeights0023 i) := by
  decide +kernel

theorem bound0023 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0023 g| ≤ (upper0023 : ℝ) :=
  abs_of_coefficients coefficients0023 upper0023 powerCoefficients10 plusWeights0023 minusWeights0023
    checked0023.1 checked0023.2.1 checked0023.2.2.1 checked0023.2.2.2
    (power_identity10 plusWeights0023) (power_identity10 minusWeights0023) g hg hmax

def envelope0023 : Envelope := ⟨coefficients0023, upper0023, bound0023⟩

def coefficients0024 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (15/256), (-159/1024), (-201/1024), (-2649/8192), (-2223/16384)]

def upper0024 : ℚ := (6679197/163840000000000)

def plusWeights0024 : Fin 11 → ℚ := ![(6679197/163840000000000), (6679197/16384000000000), (60112773/32768000000000), (20037591/4096000000000), (140263137/16384000000000), (420789411/40960000000000), (141223137/16384000000000), (20933991/4096000000000), (70042053/32768000000000), (9686379/16384000000000), (6679197/81920000000000)]

def minusWeights0024 : Fin 11 → ℚ := ![(6679197/163840000000000), (6679197/16384000000000), (60112773/32768000000000), (20037591/4096000000000), (140263137/16384000000000), (420789411/40960000000000), (139303137/16384000000000), (19141191/4096000000000), (50183493/32768000000000), (734403/3276800000000), 0]

theorem checked0024 :
    (∀ i, 0 ≤ plusWeights0024 i) ∧
    (∀ i, 0 ≤ minusWeights0024 i) ∧
    (∀ i, plusCoefficients coefficients0024 upper0024 i = powerCoefficients10 plusWeights0024 i) ∧
    (∀ i, minusCoefficients coefficients0024 upper0024 i = powerCoefficients10 minusWeights0024 i) := by
  decide +kernel

theorem bound0024 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0024 g| ≤ (upper0024 : ℝ) :=
  abs_of_coefficients coefficients0024 upper0024 powerCoefficients10 plusWeights0024 minusWeights0024
    checked0024.1 checked0024.2.1 checked0024.2.2.1 checked0024.2.2.2
    (power_identity10 plusWeights0024) (power_identity10 minusWeights0024) g hg hmax

def envelope0024 : Envelope := ⟨coefficients0024, upper0024, bound0024⟩

def coefficients0025 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (1/16), (3/32), (13/64), (21/128), (5/128)]

def upper0025 : ℚ := (18963/256000000000)

def plusWeights0025 : Fin 11 → ℚ := ![(18963/256000000000), (18963/25600000000), (170667/51200000000), (56889/6400000000), (398223/25600000000), (1194669/64000000000), (399823/25600000000), (58549/6400000000), (191411/51200000000), (32739/32000000000), (18963/128000000000)]

def minusWeights0025 : Fin 11 → ℚ := ![(18963/256000000000), (18963/25600000000), (170667/51200000000), (56889/6400000000), (398223/25600000000), (1194669/64000000000), (396623/25600000000), (55229/6400000000), (149923/51200000000), (29337/64000000000), 0]

theorem checked0025 :
    (∀ i, 0 ≤ plusWeights0025 i) ∧
    (∀ i, 0 ≤ minusWeights0025 i) ∧
    (∀ i, plusCoefficients coefficients0025 upper0025 i = powerCoefficients10 plusWeights0025 i) ∧
    (∀ i, minusCoefficients coefficients0025 upper0025 i = powerCoefficients10 minusWeights0025 i) := by
  decide +kernel

theorem bound0025 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0025 g| ≤ (upper0025 : ℝ) :=
  abs_of_coefficients coefficients0025 upper0025 powerCoefficients10 plusWeights0025 minusWeights0025
    checked0025.1 checked0025.2.1 checked0025.2.2.1 checked0025.2.2.2
    (power_identity10 plusWeights0025) (power_identity10 minusWeights0025) g hg hmax

def envelope0025 : Envelope := ⟨coefficients0025, upper0025, bound0025⟩

def coefficients0026 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (1/16), (3/32), (41/128), (9/32), (35/512)]

def upper0026 : ℚ := (3087/40960000000)

def plusWeights0026 : Fin 11 → ℚ := ![(3087/40960000000), (3087/4096000000), (27783/8192000000), (9261/1024000000), (64827/4096000000), (194481/10240000000), (65083/4096000000), (47633/5120000000), (777791/204800000000), (531699/512000000000), (3087/20480000000)]

def minusWeights0026 : Fin 11 → ℚ := ![(3087/40960000000), (3087/4096000000), (27783/8192000000), (9261/1024000000), (64827/4096000000), (194481/10240000000), (64571/4096000000), (44977/5120000000), (611359/204800000000), (240051/512000000000), 0]

theorem checked0026 :
    (∀ i, 0 ≤ plusWeights0026 i) ∧
    (∀ i, 0 ≤ minusWeights0026 i) ∧
    (∀ i, plusCoefficients coefficients0026 upper0026 i = powerCoefficients10 plusWeights0026 i) ∧
    (∀ i, minusCoefficients coefficients0026 upper0026 i = powerCoefficients10 minusWeights0026 i) := by
  decide +kernel

theorem bound0026 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0026 g| ≤ (upper0026 : ℝ) :=
  abs_of_coefficients coefficients0026 upper0026 powerCoefficients10 plusWeights0026 minusWeights0026
    checked0026.1 checked0026.2.1 checked0026.2.2.1 checked0026.2.2.2
    (power_identity10 plusWeights0026) (power_identity10 minusWeights0026) g hg hmax

def envelope0026 : Envelope := ⟨coefficients0026, upper0026, bound0026⟩

def coefficients0027 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (27/256), (-93/1024), (1749/4096), (1713/8192), (6615/32768)]

def upper0027 : ℚ := (6611667/65536000000000)

def plusWeights0027 : Fin 11 → ℚ := ![(6611667/65536000000000), (6611667/6553600000000), (59505003/13107200000000), (19835001/1638400000000), (138845007/6553600000000), (416535021/16384000000000), (139536207/6553600000000), (20511321/1638400000000), (67498251/13107200000000), (46276227/32768000000000), (6611667/32768000000000)]

def minusWeights0027 : Fin 11 → ℚ := ![(6611667/65536000000000), (6611667/6553600000000), (59505003/13107200000000), (19835001/1638400000000), (138845007/6553600000000), (416535021/16384000000000), (138153807/6553600000000), (19158681/1638400000000), (10302351/2621440000000), (19840443/32768000000000), 0]

theorem checked0027 :
    (∀ i, 0 ≤ plusWeights0027 i) ∧
    (∀ i, 0 ≤ minusWeights0027 i) ∧
    (∀ i, plusCoefficients coefficients0027 upper0027 i = powerCoefficients10 plusWeights0027 i) ∧
    (∀ i, minusCoefficients coefficients0027 upper0027 i = powerCoefficients10 minusWeights0027 i) := by
  decide +kernel

theorem bound0027 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0027 g| ≤ (upper0027 : ℝ) :=
  abs_of_coefficients coefficients0027 upper0027 powerCoefficients10 plusWeights0027 minusWeights0027
    checked0027.1 checked0027.2.1 checked0027.2.2.1 checked0027.2.2.2
    (power_identity10 plusWeights0027) (power_identity10 minusWeights0027) g hg hmax

def envelope0027 : Envelope := ⟨coefficients0027, upper0027, bound0027⟩

def coefficients0028 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (1/8), (369/2048), (281/1024), (69/256), (275/4096)]

def upper0028 : ℚ := (1196343/8192000000000)

def plusWeights0028 : Fin 11 → ℚ := ![(1196343/8192000000000), (1196343/819200000000), (10767087/1638400000000), (3589029/204800000000), (25123203/819200000000), (75369609/2048000000000), (25225603/819200000000), (3695119/204800000000), (12088943/1638400000000), (8274699/4096000000000), (1196343/4096000000000)]

def minusWeights0028 : Fin 11 → ℚ := ![(1196343/8192000000000), (1196343/819200000000), (10767087/1638400000000), (3589029/204800000000), (25123203/819200000000), (75369609/2048000000000), (25020803/819200000000), (3482939/204800000000), (9445231/1638400000000), (3688731/4096000000000), 0]

theorem checked0028 :
    (∀ i, 0 ≤ plusWeights0028 i) ∧
    (∀ i, 0 ≤ minusWeights0028 i) ∧
    (∀ i, plusCoefficients coefficients0028 upper0028 i = powerCoefficients10 plusWeights0028 i) ∧
    (∀ i, minusCoefficients coefficients0028 upper0028 i = powerCoefficients10 minusWeights0028 i) := by
  decide +kernel

theorem bound0028 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0028 g| ≤ (upper0028 : ℝ) :=
  abs_of_coefficients coefficients0028 upper0028 powerCoefficients10 plusWeights0028 minusWeights0028
    checked0028.1 checked0028.2.1 checked0028.2.2.1 checked0028.2.2.2
    (power_identity10 plusWeights0028) (power_identity10 minusWeights0028) g hg hmax

def envelope0028 : Envelope := ⟨coefficients0028, upper0028, bound0028⟩

def coefficients0029 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (1/8), (3/16), (13/32), (21/64), (5/64)]

def upper0029 : ℚ := (18963/128000000000)

def plusWeights0029 : Fin 11 → ℚ := ![(18963/128000000000), (18963/12800000000), (170667/25600000000), (56889/3200000000), (398223/12800000000), (1194669/32000000000), (399823/12800000000), (58549/3200000000), (191411/25600000000), (32739/16000000000), (18963/64000000000)]

def minusWeights0029 : Fin 11 → ℚ := ![(18963/128000000000), (18963/12800000000), (170667/25600000000), (56889/3200000000), (398223/12800000000), (1194669/32000000000), (396623/12800000000), (55229/3200000000), (149923/25600000000), (29337/32000000000), 0]

theorem checked0029 :
    (∀ i, 0 ≤ plusWeights0029 i) ∧
    (∀ i, 0 ≤ minusWeights0029 i) ∧
    (∀ i, plusCoefficients coefficients0029 upper0029 i = powerCoefficients10 plusWeights0029 i) ∧
    (∀ i, minusCoefficients coefficients0029 upper0029 i = powerCoefficients10 minusWeights0029 i) := by
  decide +kernel

theorem bound0029 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0029 g| ≤ (upper0029 : ℝ) :=
  abs_of_coefficients coefficients0029 upper0029 powerCoefficients10 plusWeights0029 minusWeights0029
    checked0029.1 checked0029.2.1 checked0029.2.2.1 checked0029.2.2.2
    (power_identity10 plusWeights0029) (power_identity10 minusWeights0029) g hg hmax

def envelope0029 : Envelope := ⟨coefficients0029, upper0029, bound0029⟩

def coefficients0030 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (21/128), (357/1024), (39/256), (63/512), (15/512)]

def upper0030 : ℚ := (205389/1024000000000)

def plusWeights0030 : Fin 11 → ℚ := ![(205389/1024000000000), (205389/102400000000), (1848501/204800000000), (616167/25600000000), (4313169/102400000000), (12939507/256000000000), (4329969/102400000000), (1267719/51200000000), (2071833/204800000000), (709059/256000000000), (205389/512000000000)]

def minusWeights0030 : Fin 11 → ℚ := ![(205389/1024000000000), (205389/102400000000), (1848501/204800000000), (616167/25600000000), (4313169/102400000000), (12939507/256000000000), (4296369/102400000000), (1196949/51200000000), (1625169/204800000000), (158943/128000000000), 0]

theorem checked0030 :
    (∀ i, 0 ≤ plusWeights0030 i) ∧
    (∀ i, 0 ≤ minusWeights0030 i) ∧
    (∀ i, plusCoefficients coefficients0030 upper0030 i = powerCoefficients10 plusWeights0030 i) ∧
    (∀ i, minusCoefficients coefficients0030 upper0030 i = powerCoefficients10 minusWeights0030 i) := by
  decide +kernel

theorem bound0030 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0030 g| ≤ (upper0030 : ℝ) :=
  abs_of_coefficients coefficients0030 upper0030 powerCoefficients10 plusWeights0030 minusWeights0030
    checked0030.1 checked0030.2.1 checked0030.2.2.1 checked0030.2.2.2
    (power_identity10 plusWeights0030) (power_identity10 minusWeights0030) g hg hmax

def envelope0030 : Envelope := ⟨coefficients0030, upper0030, bound0030⟩

def coefficients0031 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (45/256), (15/128), (945/4096), (1245/8192), (2595/32768)]

def upper0031 : ℚ := (12449679/65536000000000)

def plusWeights0031 : Fin 11 → ℚ := ![(12449679/65536000000000), (12449679/6553600000000), (112047111/13107200000000), (37349037/1638400000000), (261443259/6553600000000), (784329777/16384000000000), (262595259/6553600000000), (38520237/1638400000000), (126362151/13107200000000), (3463863/1310720000000), (12449679/32768000000000)]

def minusWeights0031 : Fin 11 → ℚ := ![(12449679/65536000000000), (12449679/6553600000000), (112047111/13107200000000), (37349037/1638400000000), (261443259/6553600000000), (784329777/16384000000000), (260291259/6553600000000), (36177837/1638400000000), (97732071/13107200000000), (7580043/6553600000000), 0]

theorem checked0031 :
    (∀ i, 0 ≤ plusWeights0031 i) ∧
    (∀ i, 0 ≤ minusWeights0031 i) ∧
    (∀ i, plusCoefficients coefficients0031 upper0031 i = powerCoefficients10 plusWeights0031 i) ∧
    (∀ i, minusCoefficients coefficients0031 upper0031 i = powerCoefficients10 minusWeights0031 i) := by
  decide +kernel

theorem bound0031 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0031 g| ≤ (upper0031 : ℝ) :=
  abs_of_coefficients coefficients0031 upper0031 powerCoefficients10 plusWeights0031 minusWeights0031
    checked0031.1 checked0031.2.1 checked0031.2.2.1 checked0031.2.2.2
    (power_identity10 plusWeights0031) (power_identity10 minusWeights0031) g hg hmax

def envelope0031 : Envelope := ⟨coefficients0031, upper0031, bound0031⟩

end BilayerDressed.CubicQuarticEnvelopes
