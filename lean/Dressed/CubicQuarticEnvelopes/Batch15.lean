import Dressed.CubicQuarticCoefficientBernstein

/-! Explicit scalar polynomial envelopes, not graph/coefficient identification.
Generated from frozen rational data; every sign and basis coefficient is checked
by the Lean kernel. No oracle, sampling, or floating-point premise is used. -/
noncomputable section
namespace BilayerDressed.CubicQuarticEnvelopes
open CubicResidualCoefficients CubicQuarticCoefficientBernstein
set_option maxHeartbeats 2000000
set_option maxRecDepth 200000

def coefficients0480 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (3/32), (9/64), (141/512), (111/512), (105/2048)]

def upper0480 : ℚ := (453789/4096000000000)

def plusWeights0480 : Fin 11 → ℚ := ![(453789/4096000000000), (453789/409600000000), (4084101/819200000000), (1361367/102400000000), (9529569/409600000000), (28588707/1024000000000), (9567969/409600000000), (1401207/102400000000), (4581717/819200000000), (3135069/2048000000000), (453789/2048000000000)]

def minusWeights0480 : Fin 11 → ℚ := ![(453789/4096000000000), (453789/409600000000), (4084101/819200000000), (1361367/102400000000), (9529569/409600000000), (28588707/1024000000000), (9491169/409600000000), (1321527/102400000000), (717297/163840000000), (1402821/2048000000000), 0]

theorem checked0480 :
    (∀ i, 0 ≤ plusWeights0480 i) ∧
    (∀ i, 0 ≤ minusWeights0480 i) ∧
    (∀ i, plusCoefficients coefficients0480 upper0480 i = powerCoefficients10 plusWeights0480 i) ∧
    (∀ i, minusCoefficients coefficients0480 upper0480 i = powerCoefficients10 minusWeights0480 i) := by
  decide +kernel

theorem bound0480 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0480 g| ≤ (upper0480 : ℝ) :=
  abs_of_coefficients coefficients0480 upper0480 powerCoefficients10 plusWeights0480 minusWeights0480
    checked0480.1 checked0480.2.1 checked0480.2.2.1 checked0480.2.2.2
    (power_identity10 plusWeights0480) (power_identity10 minusWeights0480) g hg hmax

def envelope0480 : Envelope := ⟨coefficients0480, upper0480, bound0480⟩

def coefficients0481 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (27/256), (-93/1024), (291/1024), (267/2048), (4365/65536)]

def upper0481 : ℚ := (13024041/131072000000000)

def plusWeights0481 : Fin 11 → ℚ := ![(13024041/131072000000000), (13024041/13107200000000), (117216369/26214400000000), (39072123/3276800000000), (273504861/13107200000000), (820514583/32768000000000), (274887261/13107200000000), (40424763/3276800000000), (5326617/1048576000000), (91363629/65536000000000), (13024041/65536000000000)]

def minusWeights0481 : Fin 11 → ℚ := ![(13024041/131072000000000), (13024041/13107200000000), (117216369/26214400000000), (39072123/3276800000000), (273504861/13107200000000), (820514583/32768000000000), (272122461/13107200000000), (37719483/3276800000000), (101267313/26214400000000), (38876781/65536000000000), 0]

theorem checked0481 :
    (∀ i, 0 ≤ plusWeights0481 i) ∧
    (∀ i, 0 ≤ minusWeights0481 i) ∧
    (∀ i, plusCoefficients coefficients0481 upper0481 i = powerCoefficients10 plusWeights0481 i) ∧
    (∀ i, minusCoefficients coefficients0481 upper0481 i = powerCoefficients10 minusWeights0481 i) := by
  decide +kernel

theorem bound0481 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0481 g| ≤ (upper0481 : ℝ) :=
  abs_of_coefficients coefficients0481 upper0481 powerCoefficients10 plusWeights0481 minusWeights0481
    checked0481.1 checked0481.2.1 checked0481.2.2.1 checked0481.2.2.2
    (power_identity10 plusWeights0481) (power_identity10 minusWeights0481) g hg hmax

def envelope0481 : Envelope := ⟨coefficients0481, upper0481, bound0481⟩

def coefficients0482 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (63/512), (423/2048), (51/512), (159/2048), (75/4096)]

def upper0482 : ℚ := (1186011/8192000000000)

def plusWeights0482 : Fin 11 → ℚ := ![(1186011/8192000000000), (1186011/819200000000), (10674099/1638400000000), (3558033/204800000000), (24906231/819200000000), (74718693/2048000000000), (25007031/819200000000), (3663063/204800000000), (11986851/1638400000000), (8208333/4096000000000), (1186011/4096000000000)]

def minusWeights0482 : Fin 11 → ℚ := ![(1186011/8192000000000), (1186011/819200000000), (10674099/1638400000000), (3558033/204800000000), (24906231/819200000000), (74718693/2048000000000), (24805431/819200000000), (3453003/204800000000), (9361347/1638400000000), (3651777/4096000000000), 0]

theorem checked0482 :
    (∀ i, 0 ≤ plusWeights0482 i) ∧
    (∀ i, 0 ≤ minusWeights0482 i) ∧
    (∀ i, plusCoefficients coefficients0482 upper0482 i = powerCoefficients10 plusWeights0482 i) ∧
    (∀ i, minusCoefficients coefficients0482 upper0482 i = powerCoefficients10 minusWeights0482 i) := by
  decide +kernel

theorem bound0482 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0482 g| ≤ (upper0482 : ℝ) :=
  abs_of_coefficients coefficients0482 upper0482 powerCoefficients10 plusWeights0482 minusWeights0482
    checked0482.1 checked0482.2.1 checked0482.2.2.1 checked0482.2.2.2
    (power_identity10 plusWeights0482) (power_identity10 minusWeights0482) g hg hmax

def envelope0482 : Envelope := ⟨coefficients0482, upper0482, bound0482⟩

def coefficients0483 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (1/8), (369/2048), (191/1024), (93/512), (185/4096)]

def upper0483 : ℚ := (237681/1638400000000)

def plusWeights0483 : Fin 11 → ℚ := ![(237681/1638400000000), (237681/163840000000), (2139129/327680000000), (713043/40960000000), (4991301/163840000000), (14973903/409600000000), (5011781/163840000000), (734261/40960000000), (12016061/1638400000000), (8227449/4096000000000), (237681/819200000000)]

def minusWeights0483 : Fin 11 → ℚ := ![(237681/1638400000000), (237681/163840000000), (2139129/327680000000), (713043/40960000000), (4991301/163840000000), (14973903/409600000000), (4970821/163840000000), (27673/1638400000), (9375229/1638400000000), (3656601/4096000000000), 0]

theorem checked0483 :
    (∀ i, 0 ≤ plusWeights0483 i) ∧
    (∀ i, 0 ≤ minusWeights0483 i) ∧
    (∀ i, plusCoefficients coefficients0483 upper0483 i = powerCoefficients10 plusWeights0483 i) ∧
    (∀ i, minusCoefficients coefficients0483 upper0483 i = powerCoefficients10 minusWeights0483 i) := by
  decide +kernel

theorem bound0483 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0483 g| ≤ (upper0483 : ℝ) :=
  abs_of_coefficients coefficients0483 upper0483 powerCoefficients10 plusWeights0483 minusWeights0483
    checked0483.1 checked0483.2.1 checked0483.2.2.1 checked0483.2.2.2
    (power_identity10 plusWeights0483) (power_identity10 minusWeights0483) g hg hmax

def envelope0483 : Envelope := ⟨coefficients0483, upper0483, bound0483⟩

def coefficients0484 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (1/8), (3/16), (21/64), (1/4), (15/256)]

def upper0484 : ℚ := (75411/512000000000)

def plusWeights0484 : Fin 11 → ℚ := ![(75411/512000000000), (75411/51200000000), (678699/102400000000), (226233/12800000000), (1583631/51200000000), (4750893/128000000000), (1590031/51200000000), (232873/12800000000), (152319/20480000000), (521199/256000000000), (75411/256000000000)]

def minusWeights0484 : Fin 11 → ℚ := ![(75411/512000000000), (75411/51200000000), (678699/102400000000), (226233/12800000000), (1583631/51200000000), (4750893/128000000000), (1577231/51200000000), (219593/12800000000), (595803/102400000000), (232911/256000000000), 0]

theorem checked0484 :
    (∀ i, 0 ≤ plusWeights0484 i) ∧
    (∀ i, 0 ≤ minusWeights0484 i) ∧
    (∀ i, plusCoefficients coefficients0484 upper0484 i = powerCoefficients10 plusWeights0484 i) ∧
    (∀ i, minusCoefficients coefficients0484 upper0484 i = powerCoefficients10 minusWeights0484 i) := by
  decide +kernel

theorem bound0484 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0484 g| ≤ (upper0484 : ℝ) :=
  abs_of_coefficients coefficients0484 upper0484 powerCoefficients10 plusWeights0484 minusWeights0484
    checked0484.1 checked0484.2.1 checked0484.2.2.1 checked0484.2.2.2
    (power_identity10 plusWeights0484) (power_identity10 minusWeights0484) g hg hmax

def envelope0484 : Envelope := ⟨coefficients0484, upper0484, bound0484⟩

def coefficients0485 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (1/8), (3/16), (47/128), (37/128), (35/512)]

def upper0485 : ℚ := (151263/1024000000000)

def plusWeights0485 : Fin 11 → ℚ := ![(151263/1024000000000), (151263/102400000000), (1361367/204800000000), (453789/25600000000), (3176523/102400000000), (9529569/256000000000), (3189323/102400000000), (467069/25600000000), (1527239/204800000000), (1045023/512000000000), (151263/512000000000)]

def minusWeights0485 : Fin 11 → ℚ := ![(151263/1024000000000), (151263/102400000000), (1361367/204800000000), (453789/25600000000), (3176523/102400000000), (9529569/256000000000), (3163723/102400000000), (440509/25600000000), (239099/40960000000), (467607/512000000000), 0]

theorem checked0485 :
    (∀ i, 0 ≤ plusWeights0485 i) ∧
    (∀ i, 0 ≤ minusWeights0485 i) ∧
    (∀ i, plusCoefficients coefficients0485 upper0485 i = powerCoefficients10 plusWeights0485 i) ∧
    (∀ i, minusCoefficients coefficients0485 upper0485 i = powerCoefficients10 minusWeights0485 i) := by
  decide +kernel

theorem bound0485 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0485 g| ≤ (upper0485 : ℝ) :=
  abs_of_coefficients coefficients0485 upper0485 powerCoefficients10 plusWeights0485 minusWeights0485
    checked0485.1 checked0485.2.1 checked0485.2.2.1 checked0485.2.2.2
    (power_identity10 plusWeights0485) (power_identity10 minusWeights0485) g hg hmax

def envelope0485 : Envelope := ⟨coefficients0485, upper0485, bound0485⟩

def coefficients0486 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (135/1024), (45/512), (945/8192), (1335/16384), (7215/262144)]

def upper0486 : ℚ := (74376963/524288000000000)

def plusWeights0486 : Fin 11 → ℚ := ![(74376963/524288000000000), (74376963/52428800000000), (669392667/104857600000000), (223130889/13107200000000), (1561916223/52428800000000), (4685748669/131072000000000), (1568828223/52428800000000), (230158089/13107200000000), (755222427/104857600000000), (20706519/10485760000000), (74376963/262144000000000)]

def minusWeights0486 : Fin 11 → ℚ := ![(74376963/524288000000000), (74376963/52428800000000), (669392667/104857600000000), (223130889/13107200000000), (1561916223/52428800000000), (4685748669/131072000000000), (1555004223/52428800000000), (216103689/13107200000000), (583562907/104857600000000), (45221331/52428800000000), 0]

theorem checked0486 :
    (∀ i, 0 ≤ plusWeights0486 i) ∧
    (∀ i, 0 ≤ minusWeights0486 i) ∧
    (∀ i, plusCoefficients coefficients0486 upper0486 i = powerCoefficients10 plusWeights0486 i) ∧
    (∀ i, minusCoefficients coefficients0486 upper0486 i = powerCoefficients10 minusWeights0486 i) := by
  decide +kernel

theorem bound0486 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0486 g| ≤ (upper0486 : ℝ) :=
  abs_of_coefficients coefficients0486 upper0486 powerCoefficients10 plusWeights0486 minusWeights0486
    checked0486.1 checked0486.2.1 checked0486.2.2.1 checked0486.2.2.2
    (power_identity10 plusWeights0486) (power_identity10 minusWeights0486) g hg hmax

def envelope0486 : Envelope := ⟨coefficients0486, upper0486, bound0486⟩

def coefficients0487 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (21/128), (357/1024), (63/512), (3/32), (45/2048)]

def upper0487 : ℚ := (820233/4096000000000)

def plusWeights0487 : Fin 11 → ℚ := ![(820233/4096000000000), (820233/409600000000), (7382097/819200000000), (2460699/102400000000), (17224893/409600000000), (51674679/1024000000000), (17292093/409600000000), (2531469/102400000000), (1655037/163840000000), (5664597/2048000000000), (820233/2048000000000)]

def minusWeights0487 : Fin 11 → ℚ := ![(820233/4096000000000), (820233/409600000000), (7382097/819200000000), (2460699/102400000000), (17224893/409600000000), (51674679/1024000000000), (17157693/409600000000), (2389929/102400000000), (6489009/819200000000), (2537733/2048000000000), 0]

theorem checked0487 :
    (∀ i, 0 ≤ plusWeights0487 i) ∧
    (∀ i, 0 ≤ minusWeights0487 i) ∧
    (∀ i, plusCoefficients coefficients0487 upper0487 i = powerCoefficients10 plusWeights0487 i) ∧
    (∀ i, minusCoefficients coefficients0487 upper0487 i = powerCoefficients10 minusWeights0487 i) := by
  decide +kernel

theorem bound0487 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0487 g| ≤ (upper0487 : ℝ) :=
  abs_of_coefficients coefficients0487 upper0487 powerCoefficients10 plusWeights0487 minusWeights0487
    checked0487.1 checked0487.2.1 checked0487.2.2.1 checked0487.2.2.2
    (power_identity10 plusWeights0487) (power_identity10 minusWeights0487) g hg hmax

def envelope0487 : Envelope := ⟨coefficients0487, upper0487, bound0487⟩

def coefficients0488 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (45/256), (15/128), (45/512), (75/1024), (825/65536)]

def upper0488 : ℚ := (4940193/26214400000000)

def plusWeights0488 : Fin 11 → ℚ := ![(4940193/26214400000000), (4940193/2621440000000), (44461737/5242880000000), (14820579/655360000000), (103744053/2621440000000), (311232159/6553600000000), (104204853/2621440000000), (15289059/655360000000), (10036053/1048576000000), (6880353/2621440000000), (4940193/13107200000000)]

def minusWeights0488 : Fin 11 → ℚ := ![(4940193/26214400000000), (4940193/2621440000000), (44461737/5242880000000), (14820579/655360000000), (103744053/2621440000000), (311232159/6553600000000), (103283253/2621440000000), (14352099/655360000000), (38743209/5242880000000), (3000033/2621440000000), 0]

theorem checked0488 :
    (∀ i, 0 ≤ plusWeights0488 i) ∧
    (∀ i, 0 ≤ minusWeights0488 i) ∧
    (∀ i, plusCoefficients coefficients0488 upper0488 i = powerCoefficients10 plusWeights0488 i) ∧
    (∀ i, minusCoefficients coefficients0488 upper0488 i = powerCoefficients10 minusWeights0488 i) := by
  decide +kernel

theorem bound0488 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0488 g| ≤ (upper0488 : ℝ) :=
  abs_of_coefficients coefficients0488 upper0488 powerCoefficients10 plusWeights0488 minusWeights0488
    checked0488.1 checked0488.2.1 checked0488.2.2.1 checked0488.2.2.2
    (power_identity10 plusWeights0488) (power_identity10 minusWeights0488) g hg hmax

def envelope0488 : Envelope := ⟨coefficients0488, upper0488, bound0488⟩

def coefficients0489 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (1/4), (369/1024), (167/1024), (157/1024), (155/4096)]

def upper0489 : ℚ := (2357847/8192000000000)

def plusWeights0489 : Fin 11 → ℚ := ![(2357847/8192000000000), (2357847/819200000000), (21220623/1638400000000), (7073541/204800000000), (49514787/819200000000), (148544361/2048000000000), (49719587/819200000000), (7285721/204800000000), (4771603/327680000000), (16342023/4096000000000), (2357847/4096000000000)]

def minusWeights0489 : Fin 11 → ℚ := ![(2357847/8192000000000), (2357847/819200000000), (21220623/1638400000000), (7073541/204800000000), (49514787/819200000000), (148544361/2048000000000), (49309987/819200000000), (6861361/204800000000), (18583231/1638400000000), (7236447/4096000000000), 0]

theorem checked0489 :
    (∀ i, 0 ≤ plusWeights0489 i) ∧
    (∀ i, 0 ≤ minusWeights0489 i) ∧
    (∀ i, plusCoefficients coefficients0489 upper0489 i = powerCoefficients10 plusWeights0489 i) ∧
    (∀ i, minusCoefficients coefficients0489 upper0489 i = powerCoefficients10 minusWeights0489 i) := by
  decide +kernel

theorem bound0489 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0489 g| ≤ (upper0489 : ℝ) :=
  abs_of_coefficients coefficients0489 upper0489 powerCoefficients10 plusWeights0489 minusWeights0489
    checked0489.1 checked0489.2.1 checked0489.2.2.1 checked0489.2.2.2
    (power_identity10 plusWeights0489) (power_identity10 minusWeights0489) g hg hmax

def envelope0489 : Envelope := ⟨coefficients0489, upper0489, bound0489⟩

def coefficients0490 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (1/128), (23/1024), (3/256), (655/32768), (855/65536), (4335/524288)]

def upper0490 : ℚ := (106924947/1048576000000000)

def plusWeights0490 : Fin 11 → ℚ := ![(106924947/1048576000000000), (106924947/104857600000000), (962324523/209715200000000), (320774841/26214400000000), (2245423887/104857600000000), (6756751661/262144000000000), (2288739087/104857600000000), (343640761/26214400000000), (1155206123/209715200000000), (6308707/4194304000000), (106924947/524288000000000)]

def minusWeights0490 : Fin 11 → ℚ := ![(106924947/1048576000000000), (106924947/104857600000000), (962324523/209715200000000), (320774841/26214400000000), (2245423887/104857600000000), (6715791661/262144000000000), (2202108687/104857600000000), (297908921/26214400000000), (769442923/209715200000000), (56132219/104857600000000), 0]

theorem checked0490 :
    (∀ i, 0 ≤ plusWeights0490 i) ∧
    (∀ i, 0 ≤ minusWeights0490 i) ∧
    (∀ i, plusCoefficients coefficients0490 upper0490 i = powerCoefficients10 plusWeights0490 i) ∧
    (∀ i, minusCoefficients coefficients0490 upper0490 i = powerCoefficients10 minusWeights0490 i) := by
  decide +kernel

theorem bound0490 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0490 g| ≤ (upper0490 : ℝ) :=
  abs_of_coefficients coefficients0490 upper0490 powerCoefficients10 plusWeights0490 minusWeights0490
    checked0490.1 checked0490.2.1 checked0490.2.2.1 checked0490.2.2.2
    (power_identity10 plusWeights0490) (power_identity10 minusWeights0490) g hg hmax

def envelope0490 : Envelope := ⟨coefficients0490, upper0490, bound0490⟩

def coefficients0491 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (1/128), (53/1024), (1/32), (1215/32768), (1815/65536), (1815/262144)]

def upper0491 : ℚ := (69943683/524288000000000)

def plusWeights0491 : Fin 11 → ℚ := ![(69943683/524288000000000), (69943683/52428800000000), (629493147/104857600000000), (209831049/13107200000000), (1468817343/52428800000000), (4416692029/131072000000000), (1492010943/52428800000000), (222825609/13107200000000), (744998267/104857600000000), (20361987/10485760000000), (69943683/262144000000000)]

def minusWeights0491 : Fin 11 → ℚ := ![(69943683/524288000000000), (69943683/52428800000000), (629493147/104857600000000), (209831049/13107200000000), (1468817343/52428800000000), (4396212029/131072000000000), (1445623743/52428800000000), (196836489/13107200000000), (513988027/104857600000000), (38077431/52428800000000), 0]

theorem checked0491 :
    (∀ i, 0 ≤ plusWeights0491 i) ∧
    (∀ i, 0 ≤ minusWeights0491 i) ∧
    (∀ i, plusCoefficients coefficients0491 upper0491 i = powerCoefficients10 plusWeights0491 i) ∧
    (∀ i, minusCoefficients coefficients0491 upper0491 i = powerCoefficients10 minusWeights0491 i) := by
  decide +kernel

theorem bound0491 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0491 g| ≤ (upper0491 : ℝ) :=
  abs_of_coefficients coefficients0491 upper0491 powerCoefficients10 plusWeights0491 minusWeights0491
    checked0491.1 checked0491.2.1 checked0491.2.2.1 checked0491.2.2.2
    (power_identity10 plusWeights0491) (power_identity10 minusWeights0491) g hg hmax

def envelope0491 : Envelope := ⟨coefficients0491, upper0491, bound0491⟩

def coefficients0492 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (5/512), (19/1024), (113/8192), (13/1024), (21/2048), (5/2048)]

def upper0492 : ℚ := (482213/4096000000000)

def plusWeights0492 : Fin 11 → ℚ := ![(482213/4096000000000), (482213/409600000000), (4339917/819200000000), (1446639/102400000000), (10126473/409600000000), (30479419/1024000000000), (10334073/409600000000), (6217521/409600000000), (5234611/819200000000), (3572081/2048000000000), (482213/2048000000000)]

def minusWeights0492 : Fin 11 → ℚ := ![(482213/4096000000000), (482213/409600000000), (4339917/819200000000), (1446639/102400000000), (10126473/409600000000), (30279419/1024000000000), (9918873/409600000000), (5355591/409600000000), (3445223/819200000000), (1250049/2048000000000), 0]

theorem checked0492 :
    (∀ i, 0 ≤ plusWeights0492 i) ∧
    (∀ i, 0 ≤ minusWeights0492 i) ∧
    (∀ i, plusCoefficients coefficients0492 upper0492 i = powerCoefficients10 plusWeights0492 i) ∧
    (∀ i, minusCoefficients coefficients0492 upper0492 i = powerCoefficients10 minusWeights0492 i) := by
  decide +kernel

theorem bound0492 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0492 g| ≤ (upper0492 : ℝ) :=
  abs_of_coefficients coefficients0492 upper0492 powerCoefficients10 plusWeights0492 minusWeights0492
    checked0492.1 checked0492.2.1 checked0492.2.2.1 checked0492.2.2.2
    (power_identity10 plusWeights0492) (power_identity10 minusWeights0492) g hg hmax

def envelope0492 : Envelope := ⟨coefficients0492, upper0492, bound0492⟩

def coefficients0493 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (5/512), (19/1024), (69/4096), (21/2048), (1/128), (15/8192)]

def upper0493 : ℚ := (1933411/16384000000000)

def plusWeights0493 : Fin 11 → ℚ := ![(1933411/16384000000000), (1933411/1638400000000), (17400699/3276800000000), (5800233/409600000000), (40601631/1638400000000), (122204893/4096000000000), (41432031/1638400000000), (6231323/409600000000), (4196479/655360000000), (14318199/8192000000000), (1933411/8192000000000)]

def minusWeights0493 : Fin 11 → ℚ := ![(1933411/16384000000000), (1933411/1638400000000), (17400699/3276800000000), (5800233/409600000000), (40601631/1638400000000), (121404893/4096000000000), (39771231/1638400000000), (5369143/409600000000), (13819003/3276800000000), (5015911/8192000000000), 0]

theorem checked0493 :
    (∀ i, 0 ≤ plusWeights0493 i) ∧
    (∀ i, 0 ≤ minusWeights0493 i) ∧
    (∀ i, plusCoefficients coefficients0493 upper0493 i = powerCoefficients10 plusWeights0493 i) ∧
    (∀ i, minusCoefficients coefficients0493 upper0493 i = powerCoefficients10 minusWeights0493 i) := by
  decide +kernel

theorem bound0493 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0493 g| ≤ (upper0493 : ℝ) :=
  abs_of_coefficients coefficients0493 upper0493 powerCoefficients10 plusWeights0493 minusWeights0493
    checked0493.1 checked0493.2.1 checked0493.2.2.1 checked0493.2.2.2
    (power_identity10 plusWeights0493) (power_identity10 minusWeights0493) g hg hmax

def envelope0493 : Envelope := ⟨coefficients0493, upper0493, bound0493⟩

def coefficients0494 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (5/512), (19/1024), (69/4096), (13/1024), (21/2048), (5/2048)]

def upper0494 : ℚ := (483463/4096000000000)

def plusWeights0494 : Fin 11 → ℚ := ![(483463/4096000000000), (483463/409600000000), (4351167/819200000000), (1450389/102400000000), (10152723/409600000000), (30558169/1024000000000), (10360323/409600000000), (3116323/204800000000), (5246611/819200000000), (1790103/1024000000000), (483463/2048000000000)]

def minusWeights0494 : Fin 11 → ℚ := ![(483463/4096000000000), (483463/409600000000), (4351167/819200000000), (1450389/102400000000), (10152723/409600000000), (30358169/1024000000000), (9945123/409600000000), (2685233/204800000000), (3455723/819200000000), (156803/256000000000), 0]

theorem checked0494 :
    (∀ i, 0 ≤ plusWeights0494 i) ∧
    (∀ i, 0 ≤ minusWeights0494 i) ∧
    (∀ i, plusCoefficients coefficients0494 upper0494 i = powerCoefficients10 plusWeights0494 i) ∧
    (∀ i, minusCoefficients coefficients0494 upper0494 i = powerCoefficients10 minusWeights0494 i) := by
  decide +kernel

theorem bound0494 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0494 g| ≤ (upper0494 : ℝ) :=
  abs_of_coefficients coefficients0494 upper0494 powerCoefficients10 plusWeights0494 minusWeights0494
    checked0494.1 checked0494.2.1 checked0494.2.2.1 checked0494.2.2.2
    (power_identity10 plusWeights0494) (power_identity10 minusWeights0494) g hg hmax

def envelope0494 : Envelope := ⟨coefficients0494, upper0494, bound0494⟩

def coefficients0495 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (1/64), (107/2048), (29/1024), (625/16384), (825/32768), (4625/524288)]

def upper0495 : ℚ := (8880837/41943040000000)

def plusWeights0495 : Fin 11 → ℚ := ![(8880837/41943040000000), (8880837/4194304000000), (79927533/8388608000000), (26642511/1048576000000), (186497577/4194304000000), (561131131/10485760000000), (189993513/4194304000000), (142515083/5242880000000), (478694177/41943040000000), (65365609/20971520000000), (8880837/20971520000000)]

def minusWeights0495 : Fin 11 → ℚ := ![(8880837/41943040000000), (8880837/4194304000000), (79927533/8388608000000), (26642511/1048576000000), (186497577/4194304000000), (557854331/10485760000000), (183001641/4194304000000), (123910027/5242880000000), (320581153/41943040000000), (23442761/20971520000000), 0]

theorem checked0495 :
    (∀ i, 0 ≤ plusWeights0495 i) ∧
    (∀ i, 0 ≤ minusWeights0495 i) ∧
    (∀ i, plusCoefficients coefficients0495 upper0495 i = powerCoefficients10 plusWeights0495 i) ∧
    (∀ i, minusCoefficients coefficients0495 upper0495 i = powerCoefficients10 minusWeights0495 i) := by
  decide +kernel

theorem bound0495 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0495 g| ≤ (upper0495 : ℝ) :=
  abs_of_coefficients coefficients0495 upper0495 powerCoefficients10 plusWeights0495 minusWeights0495
    checked0495.1 checked0495.2.1 checked0495.2.2.1 checked0495.2.2.2
    (power_identity10 plusWeights0495) (power_identity10 minusWeights0495) g hg hmax

def envelope0495 : Envelope := ⟨coefficients0495, upper0495, bound0495⟩

def coefficients0496 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (1/64), (19/256), (11/256), (1005/16384), (1325/32768), (3725/262144)]

def upper0496 : ℚ := (24685669/104857600000000)

def plusWeights0496 : Fin 11 → ℚ := ![(24685669/104857600000000), (24685669/10485760000000), (222171021/20971520000000), (74057007/2621440000000), (518399049/10485760000000), (1559293147/26214400000000), (527369289/10485760000000), (78942511/2621440000000), (264561101/20971520000000), (7227817/2097152000000), (24685669/52428800000000)]

def minusWeights0496 : Fin 11 → ℚ := ![(24685669/104857600000000), (24685669/10485760000000), (222171021/20971520000000), (74057007/2621440000000), (518399049/10485760000000), (1551101147/26214400000000), (509428809/10485760000000), (69171503/2621440000000), (179780941/20971520000000), (13232253/10485760000000), 0]

theorem checked0496 :
    (∀ i, 0 ≤ plusWeights0496 i) ∧
    (∀ i, 0 ≤ minusWeights0496 i) ∧
    (∀ i, plusCoefficients coefficients0496 upper0496 i = powerCoefficients10 plusWeights0496 i) ∧
    (∀ i, minusCoefficients coefficients0496 upper0496 i = powerCoefficients10 minusWeights0496 i) := by
  decide +kernel

theorem bound0496 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0496 g| ≤ (upper0496 : ℝ) :=
  abs_of_coefficients coefficients0496 upper0496 powerCoefficients10 plusWeights0496 minusWeights0496
    checked0496.1 checked0496.2.1 checked0496.2.2.1 checked0496.2.2.2
    (power_identity10 plusWeights0496) (power_identity10 minusWeights0496) g hg hmax

def envelope0496 : Envelope := ⟨coefficients0496, upper0496, bound0496⟩

def coefficients0497 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (1/64), (53/512), (1/16), (1065/16384), (1665/32768), (1065/131072)]

def upper0497 : ℚ := (69918333/262144000000000)

def plusWeights0497 : Fin 11 → ℚ := ![(69918333/262144000000000), (69918333/26214400000000), (629264997/52428800000000), (209754999/6553600000000), (1468284993/26214400000000), (4415094979/65536000000000), (1491478593/26214400000000), (222749559/6553600000000), (744765317/52428800000000), (20355933/5242880000000), (69918333/131072000000000)]

def minusWeights0497 : Fin 11 → ℚ := ![(69918333/262144000000000), (69918333/26214400000000), (629264997/52428800000000), (209754999/6553600000000), (1468284993/26214400000000), (4394614979/65536000000000), (1445091393/26214400000000), (196760439/6553600000000), (513764677/52428800000000), (38057001/26214400000000), 0]

theorem checked0497 :
    (∀ i, 0 ≤ plusWeights0497 i) ∧
    (∀ i, 0 ≤ minusWeights0497 i) ∧
    (∀ i, plusCoefficients coefficients0497 upper0497 i = powerCoefficients10 plusWeights0497 i) ∧
    (∀ i, minusCoefficients coefficients0497 upper0497 i = powerCoefficients10 minusWeights0497 i) := by
  decide +kernel

theorem bound0497 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0497 g| ≤ (upper0497 : ℝ) :=
  abs_of_coefficients coefficients0497 upper0497 powerCoefficients10 plusWeights0497 minusWeights0497
    checked0497.1 checked0497.2.1 checked0497.2.2.1 checked0497.2.2.2
    (power_identity10 plusWeights0497) (power_identity10 minusWeights0497) g hg hmax

def envelope0497 : Envelope := ⟨coefficients0497, upper0497, bound0497⟩

def coefficients0498 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (1/64), (53/512), (1/16), (1215/16384), (1815/32768), (1815/131072)]

def upper0498 : ℚ := (69943683/262144000000000)

def plusWeights0498 : Fin 11 → ℚ := ![(69943683/262144000000000), (69943683/26214400000000), (629493147/52428800000000), (209831049/6553600000000), (1468817343/26214400000000), (4416692029/65536000000000), (1492010943/26214400000000), (222825609/6553600000000), (744998267/52428800000000), (20361987/5242880000000), (69943683/131072000000000)]

def minusWeights0498 : Fin 11 → ℚ := ![(69943683/262144000000000), (69943683/26214400000000), (629493147/52428800000000), (209831049/6553600000000), (1468817343/26214400000000), (4396212029/65536000000000), (1445623743/26214400000000), (196836489/6553600000000), (513988027/52428800000000), (38077431/26214400000000), 0]

theorem checked0498 :
    (∀ i, 0 ≤ plusWeights0498 i) ∧
    (∀ i, 0 ≤ minusWeights0498 i) ∧
    (∀ i, plusCoefficients coefficients0498 upper0498 i = powerCoefficients10 plusWeights0498 i) ∧
    (∀ i, minusCoefficients coefficients0498 upper0498 i = powerCoefficients10 minusWeights0498 i) := by
  decide +kernel

theorem bound0498 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0498 g| ≤ (upper0498 : ℝ) :=
  abs_of_coefficients coefficients0498 upper0498 powerCoefficients10 plusWeights0498 minusWeights0498
    checked0498.1 checked0498.2.1 checked0498.2.2.1 checked0498.2.2.2
    (power_identity10 plusWeights0498) (power_identity10 minusWeights0498) g hg hmax

def envelope0498 : Envelope := ⟨coefficients0498, upper0498, bound0498⟩

def coefficients0499 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (1/64), (53/512), (1/16), (1545/8192), (2295/16384), (20865/131072)]

def upper0499 : ℚ := (70269693/262144000000000)

def plusWeights0499 : Fin 11 → ℚ := ![(70269693/262144000000000), (70269693/26214400000000), (632427237/52428800000000), (210809079/6553600000000), (1475663553/26214400000000), (4437230659/65536000000000), (1498857153/26214400000000), (223803639/6553600000000), (747992357/52428800000000), (20439633/5242880000000), (70269693/131072000000000)]

def minusWeights0499 : Fin 11 → ℚ := ![(70269693/262144000000000), (70269693/26214400000000), (632427237/52428800000000), (210809079/6553600000000), (1475663553/26214400000000), (4416750659/65536000000000), (1452469953/26214400000000), (197814519/6553600000000), (516862117/52428800000000), (38341221/26214400000000), 0]

theorem checked0499 :
    (∀ i, 0 ≤ plusWeights0499 i) ∧
    (∀ i, 0 ≤ minusWeights0499 i) ∧
    (∀ i, plusCoefficients coefficients0499 upper0499 i = powerCoefficients10 plusWeights0499 i) ∧
    (∀ i, minusCoefficients coefficients0499 upper0499 i = powerCoefficients10 minusWeights0499 i) := by
  decide +kernel

theorem bound0499 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0499 g| ≤ (upper0499 : ℝ) :=
  abs_of_coefficients coefficients0499 upper0499 powerCoefficients10 plusWeights0499 minusWeights0499
    checked0499.1 checked0499.2.1 checked0499.2.2.1 checked0499.2.2.2
    (power_identity10 plusWeights0499) (power_identity10 minusWeights0499) g hg hmax

def envelope0499 : Envelope := ⟨coefficients0499, upper0499, bound0499⟩

def coefficients0500 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (5/256), (3/128), (69/4096), (21/2048), (1/128), (15/8192)]

def upper0500 : ℚ := (3613411/16384000000000)

def plusWeights0500 : Fin 11 → ℚ := ![(3613411/16384000000000), (3613411/1638400000000), (32520699/3276800000000), (10840233/409600000000), (75881631/1638400000000), (228444893/4096000000000), (77520031/1638400000000), (11679323/409600000000), (7879679/655360000000), (26878199/8192000000000), (3613411/8192000000000)]

def minusWeights0500 : Fin 11 → ℚ := ![(3613411/16384000000000), (3613411/1638400000000), (32520699/3276800000000), (10840233/409600000000), (75881631/1638400000000), (226844893/4096000000000), (74243231/1638400000000), (10001143/409600000000), (25643003/3276800000000), (9255911/8192000000000), 0]

theorem checked0500 :
    (∀ i, 0 ≤ plusWeights0500 i) ∧
    (∀ i, 0 ≤ minusWeights0500 i) ∧
    (∀ i, plusCoefficients coefficients0500 upper0500 i = powerCoefficients10 plusWeights0500 i) ∧
    (∀ i, minusCoefficients coefficients0500 upper0500 i = powerCoefficients10 minusWeights0500 i) := by
  decide +kernel

theorem bound0500 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0500 g| ≤ (upper0500 : ℝ) :=
  abs_of_coefficients coefficients0500 upper0500 powerCoefficients10 plusWeights0500 minusWeights0500
    checked0500.1 checked0500.2.1 checked0500.2.2.1 checked0500.2.2.2
    (power_identity10 plusWeights0500) (power_identity10 minusWeights0500) g hg hmax

def envelope0500 : Envelope := ⟨coefficients0500, upper0500, bound0500⟩

def coefficients0501 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (15/512), (9/256), (207/8192), (63/4096), (3/256), (45/16384)]

def upper0501 : ℚ := (10840233/32768000000000)

def plusWeights0501 : Fin 11 → ℚ := ![(10840233/32768000000000), (10840233/3276800000000), (97562097/6553600000000), (32520699/819200000000), (227644893/3276800000000), (685334679/8192000000000), (232560093/3276800000000), (35037969/819200000000), (23639037/1310720000000), (80634597/16384000000000), (10840233/16384000000000)]

def minusWeights0501 : Fin 11 → ℚ := ![(10840233/32768000000000), (10840233/3276800000000), (97562097/6553600000000), (32520699/819200000000), (227644893/3276800000000), (680534679/8192000000000), (222729693/3276800000000), (30003429/819200000000), (76929009/6553600000000), (27767733/16384000000000), 0]

theorem checked0501 :
    (∀ i, 0 ≤ plusWeights0501 i) ∧
    (∀ i, 0 ≤ minusWeights0501 i) ∧
    (∀ i, plusCoefficients coefficients0501 upper0501 i = powerCoefficients10 plusWeights0501 i) ∧
    (∀ i, minusCoefficients coefficients0501 upper0501 i = powerCoefficients10 minusWeights0501 i) := by
  decide +kernel

theorem bound0501 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0501 g| ≤ (upper0501 : ℝ) :=
  abs_of_coefficients coefficients0501 upper0501 powerCoefficients10 plusWeights0501 minusWeights0501
    checked0501.1 checked0501.2.1 checked0501.2.2.1 checked0501.2.2.2
    (power_identity10 plusWeights0501) (power_identity10 minusWeights0501) g hg hmax

def envelope0501 : Envelope := ⟨coefficients0501, upper0501, bound0501⟩

def coefficients0502 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (15/512), (57/1024), (339/8192), (39/1024), (63/2048), (15/2048)]

def upper0502 : ℚ := (1446639/4096000000000)

def plusWeights0502 : Fin 11 → ℚ := ![(1446639/4096000000000), (1446639/409600000000), (13019751/819200000000), (4339917/102400000000), (30379419/409600000000), (91438257/1024000000000), (31002219/409600000000), (18652563/409600000000), (15703833/819200000000), (10716243/2048000000000), (1446639/2048000000000)]

def minusWeights0502 : Fin 11 → ℚ := ![(1446639/4096000000000), (1446639/409600000000), (13019751/819200000000), (4339917/102400000000), (30379419/409600000000), (90838257/1024000000000), (29756619/409600000000), (16066773/409600000000), (10335669/819200000000), (3750147/2048000000000), 0]

theorem checked0502 :
    (∀ i, 0 ≤ plusWeights0502 i) ∧
    (∀ i, 0 ≤ minusWeights0502 i) ∧
    (∀ i, plusCoefficients coefficients0502 upper0502 i = powerCoefficients10 plusWeights0502 i) ∧
    (∀ i, minusCoefficients coefficients0502 upper0502 i = powerCoefficients10 minusWeights0502 i) := by
  decide +kernel

theorem bound0502 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0502 g| ≤ (upper0502 : ℝ) :=
  abs_of_coefficients coefficients0502 upper0502 powerCoefficients10 plusWeights0502 minusWeights0502
    checked0502.1 checked0502.2.1 checked0502.2.2.1 checked0502.2.2.2
    (power_identity10 plusWeights0502) (power_identity10 minusWeights0502) g hg hmax

def envelope0502 : Envelope := ⟨coefficients0502, upper0502, bound0502⟩

def coefficients0503 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (15/512), (57/1024), (207/4096), (63/2048), (3/128), (45/8192)]

def upper0503 : ℚ := (5800233/16384000000000)

def plusWeights0503 : Fin 11 → ℚ := ![(5800233/16384000000000), (5800233/1638400000000), (52202097/3276800000000), (17400699/409600000000), (121804893/1638400000000), (366614679/4096000000000), (124296093/1638400000000), (18693969/409600000000), (12589437/655360000000), (42954597/8192000000000), (5800233/8192000000000)]

def minusWeights0503 : Fin 11 → ℚ := ![(5800233/16384000000000), (5800233/1638400000000), (52202097/3276800000000), (17400699/409600000000), (121804893/1638400000000), (364214679/4096000000000), (119313693/1638400000000), (16107429/409600000000), (41457009/3276800000000), (15047733/8192000000000), 0]

theorem checked0503 :
    (∀ i, 0 ≤ plusWeights0503 i) ∧
    (∀ i, 0 ≤ minusWeights0503 i) ∧
    (∀ i, plusCoefficients coefficients0503 upper0503 i = powerCoefficients10 plusWeights0503 i) ∧
    (∀ i, minusCoefficients coefficients0503 upper0503 i = powerCoefficients10 minusWeights0503 i) := by
  decide +kernel

theorem bound0503 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0503 g| ≤ (upper0503 : ℝ) :=
  abs_of_coefficients coefficients0503 upper0503 powerCoefficients10 plusWeights0503 minusWeights0503
    checked0503.1 checked0503.2.1 checked0503.2.2.1 checked0503.2.2.2
    (power_identity10 plusWeights0503) (power_identity10 minusWeights0503) g hg hmax

def envelope0503 : Envelope := ⟨coefficients0503, upper0503, bound0503⟩

def coefficients0504 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (1/32), (61/512), (17/256), (2415/32768), (3375/65536), (8175/524288)]

def upper0504 : ℚ := (92079927/209715200000000)

def plusWeights0504 : Fin 11 → ℚ := ![(92079927/209715200000000), (92079927/20971520000000), (828719343/41943040000000), (276239781/5242880000000), (1933678467/20971520000000), (5817419401/52428800000000), (1968945027/20971520000000), (295157157/5242880000000), (990640559/41943040000000), (135291951/20971520000000), (92079927/104857600000000)]

def minusWeights0504 : Fin 11 → ℚ := ![(92079927/209715200000000), (92079927/20971520000000), (828719343/41943040000000), (276239781/5242880000000), (1933678467/20971520000000), (5784651401/52428800000000), (1898411907/20971520000000), (51464481/1048576000000), (666798127/41943040000000), (48867903/20971520000000), 0]

theorem checked0504 :
    (∀ i, 0 ≤ plusWeights0504 i) ∧
    (∀ i, 0 ≤ minusWeights0504 i) ∧
    (∀ i, plusCoefficients coefficients0504 upper0504 i = powerCoefficients10 plusWeights0504 i) ∧
    (∀ i, minusCoefficients coefficients0504 upper0504 i = powerCoefficients10 minusWeights0504 i) := by
  decide +kernel

theorem bound0504 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0504 g| ≤ (upper0504 : ℝ) :=
  abs_of_coefficients coefficients0504 upper0504 powerCoefficients10 plusWeights0504 minusWeights0504
    checked0504.1 checked0504.2.1 checked0504.2.2.1 checked0504.2.2.2
    (power_identity10 plusWeights0504) (power_identity10 minusWeights0504) g hg hmax

def envelope0504 : Envelope := ⟨coefficients0504, upper0504, bound0504⟩

def coefficients0505 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (1/32), (61/512), (17/256), (2955/32768), (4155/65536), (18135/524288)]

def upper0505 : ℚ := (460586907/1048576000000000)

def plusWeights0505 : Fin 11 → ℚ := ![(460586907/1048576000000000), (460586907/104857600000000), (4145282163/209715200000000), (1381760721/26214400000000), (9672325047/104857600000000), (29098895141/262144000000000), (9848657847/104857600000000), (1476347601/26214400000000), (4954922803/209715200000000), (135336567/20971520000000), (460586907/524288000000000)]

def minusWeights0505 : Fin 11 → ℚ := ![(460586907/1048576000000000), (460586907/104857600000000), (4145282163/209715200000000), (1381760721/26214400000000), (9672325047/104857600000000), (28935055141/262144000000000), (9495992247/104857600000000), (1287173841/26214400000000), (3335641523/209715200000000), (244490979/104857600000000), 0]

theorem checked0505 :
    (∀ i, 0 ≤ plusWeights0505 i) ∧
    (∀ i, 0 ≤ minusWeights0505 i) ∧
    (∀ i, plusCoefficients coefficients0505 upper0505 i = powerCoefficients10 plusWeights0505 i) ∧
    (∀ i, minusCoefficients coefficients0505 upper0505 i = powerCoefficients10 minusWeights0505 i) := by
  decide +kernel

theorem bound0505 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0505 g| ≤ (upper0505 : ℝ) :=
  abs_of_coefficients coefficients0505 upper0505 powerCoefficients10 plusWeights0505 minusWeights0505
    checked0505.1 checked0505.2.1 checked0505.2.2.1 checked0505.2.2.2
    (power_identity10 plusWeights0505) (power_identity10 minusWeights0505) g hg hmax

def envelope0505 : Envelope := ⟨coefficients0505, upper0505, bound0505⟩

def coefficients0506 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (1/32), (167/1024), (49/512), (2895/16384), (4155/32768), (32385/262144)]

def upper0506 : ℚ := (255360957/524288000000000)

def plusWeights0506 : Fin 11 → ℚ := ![(255360957/524288000000000), (255360957/52428800000000), (2298248613/104857600000000), (766082871/13107200000000), (5362580097/52428800000000), (16128700291/131072000000000), (5453050497/52428800000000), (815718711/13107200000000), (2731729253/104857600000000), (74635953/10485760000000), (255360957/262144000000000)]

def minusWeights0506 : Fin 11 → ℚ := ![(255360957/524288000000000), (255360957/52428800000000), (2298248613/104857600000000), (766082871/13107200000000), (5362580097/52428800000000), (16046780291/131072000000000), (5272109697/52428800000000), (716447031/13107200000000), (1864767973/104857600000000), (137542149/52428800000000), 0]

theorem checked0506 :
    (∀ i, 0 ≤ plusWeights0506 i) ∧
    (∀ i, 0 ≤ minusWeights0506 i) ∧
    (∀ i, plusCoefficients coefficients0506 upper0506 i = powerCoefficients10 plusWeights0506 i) ∧
    (∀ i, minusCoefficients coefficients0506 upper0506 i = powerCoefficients10 minusWeights0506 i) := by
  decide +kernel

theorem bound0506 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0506 g| ≤ (upper0506 : ℝ) :=
  abs_of_coefficients coefficients0506 upper0506 powerCoefficients10 plusWeights0506 minusWeights0506
    checked0506.1 checked0506.2.1 checked0506.2.2.1 checked0506.2.2.2
    (power_identity10 plusWeights0506) (power_identity10 minusWeights0506) g hg hmax

def envelope0506 : Envelope := ⟨coefficients0506, upper0506, bound0506⟩

def coefficients0507 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (1/32), (53/256), (1/8), (1725/8192), (2685/16384), (7785/65536)]

def upper0507 : ℚ := (70033437/131072000000000)

def plusWeights0507 : Fin 11 → ℚ := ![(70033437/131072000000000), (70033437/13107200000000), (630300933/26214400000000), (210100311/3276800000000), (1470702177/13107200000000), (4422346531/32768000000000), (1493895777/13107200000000), (223094871/3276800000000), (745822373/26214400000000), (20383341/2621440000000), (70033437/65536000000000)]

def minusWeights0507 : Fin 11 → ℚ := ![(70033437/131072000000000), (70033437/13107200000000), (630300933/26214400000000), (210100311/3276800000000), (1470702177/13107200000000), (4401866531/32768000000000), (1447508577/13107200000000), (197105751/3276800000000), (514779493/26214400000000), (38150169/13107200000000), 0]

theorem checked0507 :
    (∀ i, 0 ≤ plusWeights0507 i) ∧
    (∀ i, 0 ≤ minusWeights0507 i) ∧
    (∀ i, plusCoefficients coefficients0507 upper0507 i = powerCoefficients10 plusWeights0507 i) ∧
    (∀ i, minusCoefficients coefficients0507 upper0507 i = powerCoefficients10 minusWeights0507 i) := by
  decide +kernel

theorem bound0507 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0507 g| ≤ (upper0507 : ℝ) :=
  abs_of_coefficients coefficients0507 upper0507 powerCoefficients10 plusWeights0507 minusWeights0507
    checked0507.1 checked0507.2.1 checked0507.2.2.1 checked0507.2.2.2
    (power_identity10 plusWeights0507) (power_identity10 minusWeights0507) g hg hmax

def envelope0507 : Envelope := ⟨coefficients0507, upper0507, bound0507⟩

def coefficients0508 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (5/128), (19/256), (527/8192), (89/2048), (69/2048), (65/8192)]

def upper0508 : ℚ := (1545817/3276800000000)

def plusWeights0508 : Fin 11 → ℚ := ![(1545817/3276800000000), (1545817/327680000000), (13912353/655360000000), (4637451/81920000000), (32462157/327680000000), (97706471/819200000000), (33126477/327680000000), (2491149/40960000000), (83885629/3276800000000), (57242921/8192000000000), (1545817/1638400000000)]

def minusWeights0508 : Fin 11 → ℚ := ![(1545817/3276800000000), (1545817/327680000000), (13912353/655360000000), (4637451/81920000000), (32462157/327680000000), (97066471/819200000000), (31797837/327680000000), (1073151/20480000000), (55237901/3276800000000), (20047929/8192000000000), 0]

theorem checked0508 :
    (∀ i, 0 ≤ plusWeights0508 i) ∧
    (∀ i, 0 ≤ minusWeights0508 i) ∧
    (∀ i, plusCoefficients coefficients0508 upper0508 i = powerCoefficients10 plusWeights0508 i) ∧
    (∀ i, minusCoefficients coefficients0508 upper0508 i = powerCoefficients10 minusWeights0508 i) := by
  decide +kernel

theorem bound0508 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0508 g| ≤ (upper0508 : ℝ) :=
  abs_of_coefficients coefficients0508 upper0508 powerCoefficients10 plusWeights0508 minusWeights0508
    checked0508.1 checked0508.2.1 checked0508.2.2.1 checked0508.2.2.2
    (power_identity10 plusWeights0508) (power_identity10 minusWeights0508) g hg hmax

def envelope0508 : Envelope := ⟨coefficients0508, upper0508, bound0508⟩

def coefficients0509 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (15/256), (9/128), (207/4096), (63/2048), (3/128), (45/8192)]

def upper0509 : ℚ := (10840233/16384000000000)

def plusWeights0509 : Fin 11 → ℚ := ![(10840233/16384000000000), (10840233/1638400000000), (97562097/3276800000000), (32520699/409600000000), (227644893/1638400000000), (685334679/4096000000000), (232560093/1638400000000), (35037969/409600000000), (23639037/655360000000), (80634597/8192000000000), (10840233/8192000000000)]

def minusWeights0509 : Fin 11 → ℚ := ![(10840233/16384000000000), (10840233/1638400000000), (97562097/3276800000000), (32520699/409600000000), (227644893/1638400000000), (680534679/4096000000000), (222729693/1638400000000), (30003429/409600000000), (76929009/3276800000000), (27767733/8192000000000), 0]

theorem checked0509 :
    (∀ i, 0 ≤ plusWeights0509 i) ∧
    (∀ i, 0 ≤ minusWeights0509 i) ∧
    (∀ i, plusCoefficients coefficients0509 upper0509 i = powerCoefficients10 plusWeights0509 i) ∧
    (∀ i, minusCoefficients coefficients0509 upper0509 i = powerCoefficients10 minusWeights0509 i) := by
  decide +kernel

theorem bound0509 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0509 g| ≤ (upper0509 : ℝ) :=
  abs_of_coefficients coefficients0509 upper0509 powerCoefficients10 plusWeights0509 minusWeights0509
    checked0509.1 checked0509.2.1 checked0509.2.2.1 checked0509.2.2.2
    (power_identity10 plusWeights0509) (power_identity10 minusWeights0509) g hg hmax

def envelope0509 : Envelope := ⟨coefficients0509, upper0509, bound0509⟩

def coefficients0510 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (15/256), (57/512), (207/2048), (39/512), (63/1024), (15/1024)]

def upper0510 : ℚ := (1450389/2048000000000)

def plusWeights0510 : Fin 11 → ℚ := ![(1450389/2048000000000), (1450389/204800000000), (13053501/409600000000), (4351167/51200000000), (30458169/204800000000), (91674507/512000000000), (31080969/204800000000), (9348969/102400000000), (15739833/409600000000), (5370309/512000000000), (1450389/1024000000000)]

def minusWeights0510 : Fin 11 → ℚ := ![(1450389/2048000000000), (1450389/204800000000), (13053501/409600000000), (4351167/51200000000), (30458169/204800000000), (91074507/512000000000), (29835369/204800000000), (8055699/102400000000), (10367169/409600000000), (470409/128000000000), 0]

theorem checked0510 :
    (∀ i, 0 ≤ plusWeights0510 i) ∧
    (∀ i, 0 ≤ minusWeights0510 i) ∧
    (∀ i, plusCoefficients coefficients0510 upper0510 i = powerCoefficients10 plusWeights0510 i) ∧
    (∀ i, minusCoefficients coefficients0510 upper0510 i = powerCoefficients10 minusWeights0510 i) := by
  decide +kernel

theorem bound0510 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0510 g| ≤ (upper0510 : ℝ) :=
  abs_of_coefficients coefficients0510 upper0510 powerCoefficients10 plusWeights0510 minusWeights0510
    checked0510.1 checked0510.2.1 checked0510.2.2.1 checked0510.2.2.2
    (power_identity10 plusWeights0510) (power_identity10 minusWeights0510) g hg hmax

def envelope0510 : Envelope := ⟨coefficients0510, upper0510, bound0510⟩

def coefficients0511 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (1/16), (53/128), (1/4), (915/4096), (1515/8192), (315/32768)]

def upper0511 : ℚ := (69892983/65536000000000)

def plusWeights0511 : Fin 11 → ℚ := ![(69892983/65536000000000), (69892983/6553600000000), (629036847/13107200000000), (209678949/1638400000000), (1467752643/6553600000000), (4413497929/16384000000000), (1490946243/6553600000000), (222673509/1638400000000), (744532367/13107200000000), (20349879/1310720000000), (69892983/32768000000000)]

def minusWeights0511 : Fin 11 → ℚ := ![(69892983/65536000000000), (69892983/6553600000000), (629036847/13107200000000), (209678949/1638400000000), (1467752643/6553600000000), (4393017929/16384000000000), (1444559043/6553600000000), (196684389/1638400000000), (513541327/13107200000000), (38036571/6553600000000), 0]

theorem checked0511 :
    (∀ i, 0 ≤ plusWeights0511 i) ∧
    (∀ i, 0 ≤ minusWeights0511 i) ∧
    (∀ i, plusCoefficients coefficients0511 upper0511 i = powerCoefficients10 plusWeights0511 i) ∧
    (∀ i, minusCoefficients coefficients0511 upper0511 i = powerCoefficients10 minusWeights0511 i) := by
  decide +kernel

theorem bound0511 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0511 g| ≤ (upper0511 : ℝ) :=
  abs_of_coefficients coefficients0511 upper0511 powerCoefficients10 plusWeights0511 minusWeights0511
    checked0511.1 checked0511.2.1 checked0511.2.2.1 checked0511.2.2.2
    (power_identity10 plusWeights0511) (power_identity10 minusWeights0511) g hg hmax

def envelope0511 : Envelope := ⟨coefficients0511, upper0511, bound0511⟩

end BilayerDressed.CubicQuarticEnvelopes
