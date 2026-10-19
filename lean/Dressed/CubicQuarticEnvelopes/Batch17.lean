import Dressed.CubicQuarticCoefficientBernstein

/-! Explicit scalar polynomial envelopes, not graph/coefficient identification.
Generated from frozen rational data; every sign and basis coefficient is checked
by the Lean kernel. No oracle, sampling, or floating-point premise is used. -/
noncomputable section
namespace BilayerDressed.CubicQuarticEnvelopes
open CubicResidualCoefficients CubicQuarticCoefficientBernstein
set_option maxHeartbeats 2000000
set_option maxRecDepth 200000

def coefficients0544 : Fin 11 → ℚ := ![0, 0, 0, (1/32), (5/32), (27/128), (23/128), (709/8192), (29/1024), (17/512), (35/4096)]

def upper0544 : ℚ := (402825499/8192000000000)

def plusWeights0544 : Fin 11 → ℚ := ![(402825499/8192000000000), (402825499/819200000000), (3625429491/1638400000000), (1214876497/204800000000), (8651335479/819200000000), (26918326437/2048000000000), (9556122679/819200000000), (3001890939/409600000000), (1024199779/327680000000), (3340380301/4096000000000), (402825499/4096000000000)]

def minusWeights0544 : Fin 11 → ℚ := ![(402825499/8192000000000), (402825499/819200000000), (3625429491/1638400000000), (1202076497/204800000000), (8267335479/819200000000), (23837686437/2048000000000), (7362548279/819200000000), (1832015049/409600000000), (2129860087/1638400000000), (687874689/4096000000000), 0]

theorem checked0544 :
    (∀ i, 0 ≤ plusWeights0544 i) ∧
    (∀ i, 0 ≤ minusWeights0544 i) ∧
    (∀ i, plusCoefficients coefficients0544 upper0544 i = powerCoefficients10 plusWeights0544 i) ∧
    (∀ i, minusCoefficients coefficients0544 upper0544 i = powerCoefficients10 minusWeights0544 i) := by
  decide +kernel

theorem bound0544 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0544 g| ≤ (upper0544 : ℝ) :=
  abs_of_coefficients coefficients0544 upper0544 powerCoefficients10 plusWeights0544 minusWeights0544
    checked0544.1 checked0544.2.1 checked0544.2.2.1 checked0544.2.2.2
    (power_identity10 plusWeights0544) (power_identity10 minusWeights0544) g hg hmax

def envelope0544 : Envelope := ⟨coefficients0544, upper0544, bound0544⟩

def coefficients0545 : Fin 11 → ℚ := ![0, 0, 0, (1/32), (5/32), (143/512), (317/1024), (825/4096), (215/2048), (95/1024), (185/8192)]

def upper0545 : ℚ := (819180757/16384000000000)

def plusWeights0545 : Fin 11 → ℚ := ![(819180757/16384000000000), (819180757/1638400000000), (7372626813/3276800000000), (2470342271/409600000000), (17586795897/1638400000000), (54691827691/4096000000000), (19402183097/1638400000000), (3045497721/409600000000), (10388834653/3276800000000), (1356192149/1638400000000), (819180757/8192000000000)]

def minusWeights0545 : Fin 11 → ℚ := ![(819180757/16384000000000), (819180757/1638400000000), (7372626813/3276800000000), (2444742271/409600000000), (16818795897/1638400000000), (48524947691/4096000000000), (15003408697/1638400000000), (1869586821/409600000000), (4356418973/3276800000000), (56433873/327680000000), 0]

theorem checked0545 :
    (∀ i, 0 ≤ plusWeights0545 i) ∧
    (∀ i, 0 ≤ minusWeights0545 i) ∧
    (∀ i, plusCoefficients coefficients0545 upper0545 i = powerCoefficients10 plusWeights0545 i) ∧
    (∀ i, minusCoefficients coefficients0545 upper0545 i = powerCoefficients10 minusWeights0545 i) := by
  decide +kernel

theorem bound0545 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0545 g| ≤ (upper0545 : ℝ) :=
  abs_of_coefficients coefficients0545 upper0545 powerCoefficients10 plusWeights0545 minusWeights0545
    checked0545.1 checked0545.2.1 checked0545.2.2.1 checked0545.2.2.2
    (power_identity10 plusWeights0545) (power_identity10 minusWeights0545) g hg hmax

def envelope0545 : Envelope := ⟨coefficients0545, upper0545, bound0545⟩

def coefficients0546 : Fin 11 → ℚ := ![0, 0, 0, (1/32), (5/32), (37/128), (77/256), (41/256), (219/2048), (199/2048), (195/8192)]

def upper0546 : ℚ := (820569551/16384000000000)

def plusWeights0546 : Fin 11 → ℚ := ![(820569551/16384000000000), (820569551/1638400000000), (7385125959/3276800000000), (2474508653/409600000000), (17615960571/1638400000000), (54779721713/4096000000000), (19432133371/1638400000000), (3050048013/409600000000), (10404320503/3276800000000), (6791515671/8192000000000), (820569551/8192000000000)]

def minusWeights0546 : Fin 11 → ℚ := ![(820569551/16384000000000), (820569551/1638400000000), (7385125959/3276800000000), (2448908653/409600000000), (16847960571/1638400000000), (48612041713/4096000000000), (15031787771/1638400000000), (1873369293/409600000000), (873186283/655360000000), (1414179839/8192000000000), 0]

theorem checked0546 :
    (∀ i, 0 ≤ plusWeights0546 i) ∧
    (∀ i, 0 ≤ minusWeights0546 i) ∧
    (∀ i, plusCoefficients coefficients0546 upper0546 i = powerCoefficients10 plusWeights0546 i) ∧
    (∀ i, minusCoefficients coefficients0546 upper0546 i = powerCoefficients10 minusWeights0546 i) := by
  decide +kernel

theorem bound0546 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0546 g| ≤ (upper0546 : ℝ) :=
  abs_of_coefficients coefficients0546 upper0546 powerCoefficients10 plusWeights0546 minusWeights0546
    checked0546.1 checked0546.2.1 checked0546.2.2.1 checked0546.2.2.2
    (power_identity10 plusWeights0546) (power_identity10 minusWeights0546) g hg hmax

def envelope0546 : Envelope := ⟨coefficients0546, upper0546, bound0546⟩

def coefficients0547 : Fin 11 → ℚ := ![0, 0, 0, (1/8), (3/8), (51/128), (65/256), (461/4096), (17/1024), (7/1024), (5/4096)]

def upper0547 : ℚ := (1366013617/8192000000000)

def plusWeights0547 : Fin 11 → ℚ := ![(1366013617/8192000000000), (1366013617/819200000000), (12294122553/1638400000000), (4123640851/204800000000), (29433805957/819200000000), (91903817871/2048000000000), (32747613957/819200000000), (1289002789/51200000000), (3516870829/327680000000), (11421567773/4096000000000), (1366013617/4096000000000)]

def minusWeights0547 : Fin 11 → ℚ := ![(1366013617/8192000000000), (1366013617/819200000000), (12294122553/1638400000000), (4072440851/204800000000), (27938765957/819200000000), (80213897871/2048000000000), (24624957957/819200000000), (1520035273/102400000000), (7003890961/1638400000000), (2238568397/4096000000000), 0]

theorem checked0547 :
    (∀ i, 0 ≤ plusWeights0547 i) ∧
    (∀ i, 0 ≤ minusWeights0547 i) ∧
    (∀ i, plusCoefficients coefficients0547 upper0547 i = powerCoefficients10 plusWeights0547 i) ∧
    (∀ i, minusCoefficients coefficients0547 upper0547 i = powerCoefficients10 minusWeights0547 i) := by
  decide +kernel

theorem bound0547 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0547 g| ≤ (upper0547 : ℝ) :=
  abs_of_coefficients coefficients0547 upper0547 powerCoefficients10 plusWeights0547 minusWeights0547
    checked0547.1 checked0547.2.1 checked0547.2.2.1 checked0547.2.2.2
    (power_identity10 plusWeights0547) (power_identity10 minusWeights0547) g hg hmax

def envelope0547 : Envelope := ⟨coefficients0547, upper0547, bound0547⟩

def coefficients0548 : Fin 11 → ℚ := ![0, 0, 0, 0, (-21/32), (-3/16), (-33/64), (-15/64), 0, 0, 0]

def upper0548 : ℚ := (8709/128000000)

def plusWeights0548 : Fin 11 → ℚ := ![(8709/128000000), (8709/12800000), (78381/25600000), (26127/3200000), (182049/12800000), (536007/32000000), (212703/16000000), (874413/128000000), (2631/1280000), (35217/128000000), 0]

def minusWeights0548 : Fin 11 → ℚ := ![(8709/128000000), (8709/12800000), (78381/25600000), (26127/3200000), (183729/12800000), (561327/32000000), (489039/32000000), (1215747/128000000), (52071/12800000), (138963/128000000), (8709/64000000)]

theorem checked0548 :
    (∀ i, 0 ≤ plusWeights0548 i) ∧
    (∀ i, 0 ≤ minusWeights0548 i) ∧
    (∀ i, plusCoefficients coefficients0548 upper0548 i = powerCoefficients10 plusWeights0548 i) ∧
    (∀ i, minusCoefficients coefficients0548 upper0548 i = powerCoefficients10 minusWeights0548 i) := by
  decide +kernel

theorem bound0548 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0548 g| ≤ (upper0548 : ℝ) :=
  abs_of_coefficients coefficients0548 upper0548 powerCoefficients10 plusWeights0548 minusWeights0548
    checked0548.1 checked0548.2.1 checked0548.2.2.1 checked0548.2.2.2
    (power_identity10 plusWeights0548) (power_identity10 minusWeights0548) g hg hmax

def envelope0548 : Envelope := ⟨coefficients0548, upper0548, bound0548⟩

def coefficients0549 : Fin 11 → ℚ := ![0, 0, 0, 0, (-1/2), (1/8), (-117/256), (-125/512), 0, 0, 0]

def upper0549 : ℚ := (50413/1024000000)

def plusWeights0549 : Fin 11 → ℚ := ![(50413/1024000000), (50413/102400000), (453717/204800000), (151239/25600000), (1053553/102400000), (3099539/256000000), (4912331/512000000), (5036463/1024000000), (755251/512000000), (201383/1024000000), 0]

def minusWeights0549 : Fin 11 → ℚ := ![(50413/1024000000), (50413/102400000), (453717/204800000), (151239/25600000), (1063793/102400000), (3252499/256000000), (5674399/512000000), (7062657/1024000000), (756667/256000000), (806877/1024000000), (50413/512000000)]

theorem checked0549 :
    (∀ i, 0 ≤ plusWeights0549 i) ∧
    (∀ i, 0 ≤ minusWeights0549 i) ∧
    (∀ i, plusCoefficients coefficients0549 upper0549 i = powerCoefficients10 plusWeights0549 i) ∧
    (∀ i, minusCoefficients coefficients0549 upper0549 i = powerCoefficients10 minusWeights0549 i) := by
  decide +kernel

theorem bound0549 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0549 g| ≤ (upper0549 : ℝ) :=
  abs_of_coefficients coefficients0549 upper0549 powerCoefficients10 plusWeights0549 minusWeights0549
    checked0549.1 checked0549.2.1 checked0549.2.2.1 checked0549.2.2.2
    (power_identity10 plusWeights0549) (power_identity10 minusWeights0549) g hg hmax

def envelope0549 : Envelope := ⟨coefficients0549, upper0549, bound0549⟩

def coefficients0550 : Fin 11 → ℚ := ![0, 0, 0, 0, (-7/16), (-1/8), (-1/2), (-15/64), 0, 0, 0]

def upper0550 : ℚ := (5827/128000000)

def plusWeights0550 : Fin 11 → ℚ := ![(5827/128000000), (5827/12800000), (52443/25600000), (17481/3200000), (121807/12800000), (358661/32000000), (569403/64000000), (585381/128000000), (88111/64000000), (4721/25600000), 0]

def minusWeights0550 : Fin 11 → ℚ := ![(5827/128000000), (5827/12800000), (52443/25600000), (17481/3200000), (122927/12800000), (375541/32000000), (654267/64000000), (813099/128000000), (21763/8000000), (18587/25600000), (5827/64000000)]

theorem checked0550 :
    (∀ i, 0 ≤ plusWeights0550 i) ∧
    (∀ i, 0 ≤ minusWeights0550 i) ∧
    (∀ i, plusCoefficients coefficients0550 upper0550 i = powerCoefficients10 plusWeights0550 i) ∧
    (∀ i, minusCoefficients coefficients0550 upper0550 i = powerCoefficients10 minusWeights0550 i) := by
  decide +kernel

theorem bound0550 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0550 g| ≤ (upper0550 : ℝ) :=
  abs_of_coefficients coefficients0550 upper0550 powerCoefficients10 plusWeights0550 minusWeights0550
    checked0550.1 checked0550.2.1 checked0550.2.2.1 checked0550.2.2.2
    (power_identity10 plusWeights0550) (power_identity10 minusWeights0550) g hg hmax

def envelope0550 : Envelope := ⟨coefficients0550, upper0550, bound0550⟩

def coefficients0551 : Fin 11 → ℚ := ![0, 0, 0, 0, (-13/64), (25/128), (11/32), (2527/4096), 0, 0, 0]

def upper0551 : ℚ := (735393/40960000000)

def plusWeights0551 : Fin 11 → ℚ := ![(735393/40960000000), (735393/4096000000), (6618537/8192000000), (2206179/1024000000), (15360053/4096000000), (45101759/10240000000), (14236661/4096000000), (72466007/40960000000), (10752373/20480000000), (2825831/40960000000), 0]

def minusWeights0551 : Fin 11 → ℚ := ![(735393/40960000000), (735393/4096000000), (6618537/8192000000), (2206179/1024000000), (15526453/4096000000), (47557759/10240000000), (3329969/819200000), (104028313/40960000000), (2792539/2560000000), (11882029/40960000000), (735393/20480000000)]

theorem checked0551 :
    (∀ i, 0 ≤ plusWeights0551 i) ∧
    (∀ i, 0 ≤ minusWeights0551 i) ∧
    (∀ i, plusCoefficients coefficients0551 upper0551 i = powerCoefficients10 plusWeights0551 i) ∧
    (∀ i, minusCoefficients coefficients0551 upper0551 i = powerCoefficients10 minusWeights0551 i) := by
  decide +kernel

theorem bound0551 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0551 g| ≤ (upper0551 : ℝ) :=
  abs_of_coefficients coefficients0551 upper0551 powerCoefficients10 plusWeights0551 minusWeights0551
    checked0551.1 checked0551.2.1 checked0551.2.2.1 checked0551.2.2.2
    (power_identity10 plusWeights0551) (power_identity10 minusWeights0551) g hg hmax

def envelope0551 : Envelope := ⟨coefficients0551, upper0551, bound0551⟩

def coefficients0552 : Fin 11 → ℚ := ![0, 0, 0, 0, (-1/8), (1/2), (-39/128), (-55/256), 0, 0, 0]

def upper0552 : ℚ := (4007/512000000)

def plusWeights0552 : Fin 11 → ℚ := ![(4007/512000000), (4007/51200000), (36063/102400000), (12021/12800000), (83507/51200000), (243481/128000000), (379057/256000000), (75561/102400000), (54473/256000000), (13813/512000000), 0]

def minusWeights0552 : Fin 11 → ℚ := ![(4007/512000000), (4007/51200000), (36063/102400000), (12021/12800000), (84787/51200000), (261401/128000000), (462413/256000000), (4671/4096000), (62921/128000000), (66327/512000000), (4007/256000000)]

theorem checked0552 :
    (∀ i, 0 ≤ plusWeights0552 i) ∧
    (∀ i, 0 ≤ minusWeights0552 i) ∧
    (∀ i, plusCoefficients coefficients0552 upper0552 i = powerCoefficients10 plusWeights0552 i) ∧
    (∀ i, minusCoefficients coefficients0552 upper0552 i = powerCoefficients10 minusWeights0552 i) := by
  decide +kernel

theorem bound0552 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0552 g| ≤ (upper0552 : ℝ) :=
  abs_of_coefficients coefficients0552 upper0552 powerCoefficients10 plusWeights0552 minusWeights0552
    checked0552.1 checked0552.2.1 checked0552.2.2.1 checked0552.2.2.2
    (power_identity10 plusWeights0552) (power_identity10 minusWeights0552) g hg hmax

def envelope0552 : Envelope := ⟨coefficients0552, upper0552, bound0552⟩

def coefficients0553 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (-75/256), (-75/512), 0, 0, 0]

def upper0553 : ℚ := (63/204800000)

def plusWeights0553 : Fin 11 → ℚ := ![(63/204800000), (63/20480000), (567/40960000), (189/5120000), (1323/20480000), (3969/51200000), (1317/20480000), (7317/204800000), (1233/102400000), (381/204800000), 0]

def minusWeights0553 : Fin 11 → ℚ := ![(63/204800000), (63/20480000), (567/40960000), (189/5120000), (1323/20480000), (3969/51200000), (1329/20480000), (7803/204800000), (801/51200000), (879/204800000), (63/102400000)]

theorem checked0553 :
    (∀ i, 0 ≤ plusWeights0553 i) ∧
    (∀ i, 0 ≤ minusWeights0553 i) ∧
    (∀ i, plusCoefficients coefficients0553 upper0553 i = powerCoefficients10 plusWeights0553 i) ∧
    (∀ i, minusCoefficients coefficients0553 upper0553 i = powerCoefficients10 minusWeights0553 i) := by
  decide +kernel

theorem bound0553 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0553 g| ≤ (upper0553 : ℝ) :=
  abs_of_coefficients coefficients0553 upper0553 powerCoefficients10 plusWeights0553 minusWeights0553
    checked0553.1 checked0553.2.1 checked0553.2.2.1 checked0553.2.2.2
    (power_identity10 plusWeights0553) (power_identity10 minusWeights0553) g hg hmax

def envelope0553 : Envelope := ⟨coefficients0553, upper0553, bound0553⟩

def coefficients0554 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (-25/128), (-25/256), 0, 0, 0]

def upper0554 : ℚ := (21/102400000)

def plusWeights0554 : Fin 11 → ℚ := ![(21/102400000), (21/10240000), (189/20480000), (63/2560000), (441/10240000), (1323/25600000), (439/10240000), (2439/102400000), (411/51200000), (127/102400000), 0]

def minusWeights0554 : Fin 11 → ℚ := ![(21/102400000), (21/10240000), (189/20480000), (63/2560000), (441/10240000), (1323/25600000), (443/10240000), (2601/102400000), (267/25600000), (293/102400000), (21/51200000)]

theorem checked0554 :
    (∀ i, 0 ≤ plusWeights0554 i) ∧
    (∀ i, 0 ≤ minusWeights0554 i) ∧
    (∀ i, plusCoefficients coefficients0554 upper0554 i = powerCoefficients10 plusWeights0554 i) ∧
    (∀ i, minusCoefficients coefficients0554 upper0554 i = powerCoefficients10 minusWeights0554 i) := by
  decide +kernel

theorem bound0554 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0554 g| ≤ (upper0554 : ℝ) :=
  abs_of_coefficients coefficients0554 upper0554 powerCoefficients10 plusWeights0554 minusWeights0554
    checked0554.1 checked0554.2.1 checked0554.2.2.1 checked0554.2.2.2
    (power_identity10 plusWeights0554) (power_identity10 minusWeights0554) g hg hmax

def envelope0554 : Envelope := ⟨coefficients0554, upper0554, bound0554⟩

def coefficients0555 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (875/4096), 0, 0, 0]

def upper0555 : ℚ := (7/327680000)

def plusWeights0555 : Fin 11 → ℚ := ![(7/327680000), (7/32768000), (63/65536000), (21/8192000), (147/32768000), (441/81920000), (147/32768000), (847/327680000), (21/20480000), (91/327680000), (7/163840000)]

def minusWeights0555 : Fin 11 → ℚ := ![(7/327680000), (7/32768000), (63/65536000), (21/8192000), (147/32768000), (441/81920000), (147/32768000), (833/327680000), (147/163840000), (49/327680000), 0]

theorem checked0555 :
    (∀ i, 0 ≤ plusWeights0555 i) ∧
    (∀ i, 0 ≤ minusWeights0555 i) ∧
    (∀ i, plusCoefficients coefficients0555 upper0555 i = powerCoefficients10 plusWeights0555 i) ∧
    (∀ i, minusCoefficients coefficients0555 upper0555 i = powerCoefficients10 minusWeights0555 i) := by
  decide +kernel

theorem bound0555 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0555 g| ≤ (upper0555 : ℝ) :=
  abs_of_coefficients coefficients0555 upper0555 powerCoefficients10 plusWeights0555 minusWeights0555
    checked0555.1 checked0555.2.1 checked0555.2.2.1 checked0555.2.2.2
    (power_identity10 plusWeights0555) (power_identity10 minusWeights0555) g hg hmax

def envelope0555 : Envelope := ⟨coefficients0555, upper0555, bound0555⟩

def coefficients0556 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (35/128), (45/256), (1405/4096), 0, 0, 0]

def upper0556 : ℚ := (24121/8192000000)

def plusWeights0556 : Fin 11 → ℚ := ![(24121/8192000000), (24121/819200000), (217089/1638400000), (72363/204800000), (506541/819200000), (1525223/2048000000), (103577/163840000), (3124561/8192000000), (82433/512000000), (359813/8192000000), (24121/4096000000)]

def minusWeights0556 : Fin 11 → ℚ := ![(24121/8192000000), (24121/819200000), (217089/1638400000), (72363/204800000), (506541/819200000), (1514023/2048000000), (495197/819200000), (2664479/8192000000), (425981/4096000000), (122607/8192000000), 0]

theorem checked0556 :
    (∀ i, 0 ≤ plusWeights0556 i) ∧
    (∀ i, 0 ≤ minusWeights0556 i) ∧
    (∀ i, plusCoefficients coefficients0556 upper0556 i = powerCoefficients10 plusWeights0556 i) ∧
    (∀ i, minusCoefficients coefficients0556 upper0556 i = powerCoefficients10 minusWeights0556 i) := by
  decide +kernel

theorem bound0556 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0556 g| ≤ (upper0556 : ℝ) :=
  abs_of_coefficients coefficients0556 upper0556 powerCoefficients10 plusWeights0556 minusWeights0556
    checked0556.1 checked0556.2.1 checked0556.2.2.1 checked0556.2.2.2
    (power_identity10 plusWeights0556) (power_identity10 minusWeights0556) g hg hmax

def envelope0556 : Envelope := ⟨coefficients0556, upper0556, bound0556⟩

def coefficients0557 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (35/128), (45/256), (1755/4096), 0, 0, 0]

def upper0557 : ℚ := (24191/8192000000)

def plusWeights0557 : Fin 11 → ℚ := ![(24191/8192000000), (24191/819200000), (217719/1638400000), (72573/204800000), (508011/819200000), (1529633/2048000000), (103871/163840000), (3133031/8192000000), (82643/512000000), (360723/8192000000), (24191/4096000000)]

def minusWeights0557 : Fin 11 → ℚ := ![(24191/8192000000), (24191/819200000), (217719/1638400000), (72573/204800000), (508011/819200000), (1518433/2048000000), (496667/819200000), (2672809/8192000000), (427451/4096000000), (123097/8192000000), 0]

theorem checked0557 :
    (∀ i, 0 ≤ plusWeights0557 i) ∧
    (∀ i, 0 ≤ minusWeights0557 i) ∧
    (∀ i, plusCoefficients coefficients0557 upper0557 i = powerCoefficients10 plusWeights0557 i) ∧
    (∀ i, minusCoefficients coefficients0557 upper0557 i = powerCoefficients10 minusWeights0557 i) := by
  decide +kernel

theorem bound0557 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0557 g| ≤ (upper0557 : ℝ) :=
  abs_of_coefficients coefficients0557 upper0557 powerCoefficients10 plusWeights0557 minusWeights0557
    checked0557.1 checked0557.2.1 checked0557.2.2.1 checked0557.2.2.2
    (power_identity10 plusWeights0557) (power_identity10 minusWeights0557) g hg hmax

def envelope0557 : Envelope := ⟨coefficients0557, upper0557, bound0557⟩

def coefficients0558 : Fin 11 → ℚ := ![0, 0, 0, 0, (3/32), (3/16), (41/256), (1469/4096), 0, 0, 0]

def upper0558 : ℚ := (468829/40960000000)

def plusWeights0558 : Fin 11 → ℚ := ![(468829/40960000000), (468829/4096000000), (4219461/8192000000), (1406487/1024000000), (9883809/4096000000), (30131427/10240000000), (2092093/819200000), (64735189/40960000000), (1729317/2560000000), (7406937/40960000000), (468829/20480000000)]

def minusWeights0558 : Fin 11 → ℚ := ![(468829/40960000000), (468829/4096000000), (4219461/8192000000), (1406487/1024000000), (9807009/4096000000), (28941027/10240000000), (9230353/4096000000), (47783771/40960000000), (7262769/20480000000), (1969643/40960000000), 0]

theorem checked0558 :
    (∀ i, 0 ≤ plusWeights0558 i) ∧
    (∀ i, 0 ≤ minusWeights0558 i) ∧
    (∀ i, plusCoefficients coefficients0558 upper0558 i = powerCoefficients10 plusWeights0558 i) ∧
    (∀ i, minusCoefficients coefficients0558 upper0558 i = powerCoefficients10 minusWeights0558 i) := by
  decide +kernel

theorem bound0558 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0558 g| ≤ (upper0558 : ℝ) :=
  abs_of_coefficients coefficients0558 upper0558 powerCoefficients10 plusWeights0558 minusWeights0558
    checked0558.1 checked0558.2.1 checked0558.2.2.1 checked0558.2.2.2
    (power_identity10 plusWeights0558) (power_identity10 minusWeights0558) g hg hmax

def envelope0558 : Envelope := ⟨coefficients0558, upper0558, bound0558⟩

def coefficients0559 : Fin 11 → ℚ := ![0, 0, 0, 0, (9/32), (-13/64), (-3/256), (683/4096), 0, 0, 0]

def upper0559 : ℚ := (1069003/40960000000)

def plusWeights0559 : Fin 11 → ℚ := ![(1069003/40960000000), (1069003/4096000000), (9621027/8192000000), (3207009/1024000000), (22564263/4096000000), (69054389/10240000000), (4827083/819200000), (150487123/40960000000), (4034519/2560000000), (17186159/40960000000), (1069003/20480000000)]

def minusWeights0559 : Fin 11 → ℚ := ![(1069003/40960000000), (1069003/4096000000), (9621027/8192000000), (3207009/1024000000), (22333863/4096000000), (65639989/10240000000), (20762711/4096000000), (106073597/40960000000), (15828983/20480000000), (4193901/40960000000), 0]

theorem checked0559 :
    (∀ i, 0 ≤ plusWeights0559 i) ∧
    (∀ i, 0 ≤ minusWeights0559 i) ∧
    (∀ i, plusCoefficients coefficients0559 upper0559 i = powerCoefficients10 plusWeights0559 i) ∧
    (∀ i, minusCoefficients coefficients0559 upper0559 i = powerCoefficients10 minusWeights0559 i) := by
  decide +kernel

theorem bound0559 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0559 g| ≤ (upper0559 : ℝ) :=
  abs_of_coefficients coefficients0559 upper0559 powerCoefficients10 plusWeights0559 minusWeights0559
    checked0559.1 checked0559.2.1 checked0559.2.2.1 checked0559.2.2.2
    (power_identity10 plusWeights0559) (power_identity10 minusWeights0559) g hg hmax

def envelope0559 : Envelope := ⟨coefficients0559, upper0559, bound0559⟩

def coefficients0560 : Fin 11 → ℚ := ![0, 0, 0, (1/8), (3/8), (23/64), (23/128), (105/2048), 0, 0, 0]

def upper0560 : ℚ := (681077/4096000000)

def plusWeights0560 : Fin 11 → ℚ := ![(681077/4096000000), (681077/409600000), (6129693/819200000), (2056031/102400000), (14676377/409600000), (45829931/1024000000), (81662253/2048000000), (20574281/819200000), (2741009/256000000), (11392977/4096000000), (681077/2048000000)]

def minusWeights0560 : Fin 11 → ℚ := ![(681077/4096000000), (681077/409600000), (6129693/819200000), (2030431/102400000), (13928857/409600000), (39985771/1024000000), (61363917/2048000000), (2423483/163840000), (8720393/2048000000), (2228563/4096000000), 0]

theorem checked0560 :
    (∀ i, 0 ≤ plusWeights0560 i) ∧
    (∀ i, 0 ≤ minusWeights0560 i) ∧
    (∀ i, plusCoefficients coefficients0560 upper0560 i = powerCoefficients10 plusWeights0560 i) ∧
    (∀ i, minusCoefficients coefficients0560 upper0560 i = powerCoefficients10 minusWeights0560 i) := by
  decide +kernel

theorem bound0560 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0560 g| ≤ (upper0560 : ℝ) :=
  abs_of_coefficients coefficients0560 upper0560 powerCoefficients10 plusWeights0560 minusWeights0560
    checked0560.1 checked0560.2.1 checked0560.2.2.1 checked0560.2.2.2
    (power_identity10 plusWeights0560) (power_identity10 minusWeights0560) g hg hmax

def envelope0560 : Envelope := ⟨coefficients0560, upper0560, bound0560⟩

def coefficients0561 : Fin 11 → ℚ := ![0, 0, 0, (-1/16), (-1/16), (-15/128), (-25/256), (-493/4096), (-99/1024), (-775/16384), (-355/32768)]

def upper0561 : ℚ := (4589655331/65536000000000)

def plusWeights0561 : Fin 11 → ℚ := ![(4589655331/65536000000000), (4589655331/6553600000000), (41306897979/13107200000000), (13666565993/1638400000000), (93474601951/6553600000000), (267010685853/16384000000000), (81393321951/6553600000000), (9960306273/1638400000000), (22713132027/13107200000000), (1435485709/6553600000000), 0]

def minusWeights0561 : Fin 11 → ℚ := ![(4589655331/65536000000000), (4589655331/6553600000000), (41306897979/13107200000000), (13871365993/1638400000000), (99290921951/6553600000000), (311285885853/16384000000000), (111372201951/6553600000000), (17577625713/1638400000000), (59900663931/13107200000000), (7743824953/6553600000000), (4589655331/32768000000000)]

theorem checked0561 :
    (∀ i, 0 ≤ plusWeights0561 i) ∧
    (∀ i, 0 ≤ minusWeights0561 i) ∧
    (∀ i, plusCoefficients coefficients0561 upper0561 i = powerCoefficients10 plusWeights0561 i) ∧
    (∀ i, minusCoefficients coefficients0561 upper0561 i = powerCoefficients10 minusWeights0561 i) := by
  decide +kernel

theorem bound0561 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0561 g| ≤ (upper0561 : ℝ) :=
  abs_of_coefficients coefficients0561 upper0561 powerCoefficients10 plusWeights0561 minusWeights0561
    checked0561.1 checked0561.2.1 checked0561.2.2.1 checked0561.2.2.2
    (power_identity10 plusWeights0561) (power_identity10 minusWeights0561) g hg hmax

def envelope0561 : Envelope := ⟨coefficients0561, upper0561, bound0561⟩

def coefficients0562 : Fin 11 → ℚ := ![0, 0, 0, (-1/16), (-1/16), (-23/256), (-25/512), (-357/4096), (-187/2048), (-3315/65536), (-1555/131072)]

def upper0562 : ℚ := (18273257731/262144000000000)

def plusWeights0562 : Fin 11 → ℚ := ![(18273257731/262144000000000), (18273257731/26214400000000), (164459319579/52428800000000), (54410173193/6553600000000), (372105772351/26214400000000), (1062682757053/65536000000000), (323817772351/26214400000000), (39604356073/6553600000000), (90243500827/52428800000000), (5697803093/26214400000000), 0]

def minusWeights0562 : Fin 11 → ℚ := ![(18273257731/262144000000000), (18273257731/26214400000000), (164459319579/52428800000000), (55229373193/6553600000000), (395371052351/26214400000000), (1239747717053/65536000000000), (443659052351/26214400000000), (70035190313/6553600000000), (238675138331/52428800000000), (30848712369/26214400000000), (18273257731/131072000000000)]

theorem checked0562 :
    (∀ i, 0 ≤ plusWeights0562 i) ∧
    (∀ i, 0 ≤ minusWeights0562 i) ∧
    (∀ i, plusCoefficients coefficients0562 upper0562 i = powerCoefficients10 plusWeights0562 i) ∧
    (∀ i, minusCoefficients coefficients0562 upper0562 i = powerCoefficients10 minusWeights0562 i) := by
  decide +kernel

theorem bound0562 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0562 g| ≤ (upper0562 : ℝ) :=
  abs_of_coefficients coefficients0562 upper0562 powerCoefficients10 plusWeights0562 minusWeights0562
    checked0562.1 checked0562.2.1 checked0562.2.2.1 checked0562.2.2.2
    (power_identity10 plusWeights0562) (power_identity10 minusWeights0562) g hg hmax

def envelope0562 : Envelope := ⟨coefficients0562, upper0562, bound0562⟩

def coefficients0563 : Fin 11 → ℚ := ![0, 0, 0, (-1/16), (1/32), (3/128), (61/512), (543/4096), (829/8192), (673/16384), (1265/131072)]

def upper0563 : ℚ := (15468376499/262144000000000)

def plusWeights0563 : Fin 11 → ℚ := ![(15468376499/262144000000000), (15468376499/26214400000000), (139215388491/52428800000000), (45995529497/6553600000000), (313449026479/26214400000000), (889735879437/65536000000000), (268754549679/26214400000000), (32497299577/6553600000000), (73022685067/52428800000000), (22677029959/131072000000000), 0]

def minusWeights0563 : Fin 11 → ℚ := ![(15468376499/262144000000000), (15468376499/26214400000000), (139215388491/52428800000000), (46814729497/6553600000000), (336222786479/26214400000000), (1059279559437/65536000000000), (380917263279/26214400000000), (60312959417/6553600000000), (41081618383/10485760000000), (132006735031/131072000000000), (15468376499/131072000000000)]

theorem checked0563 :
    (∀ i, 0 ≤ plusWeights0563 i) ∧
    (∀ i, 0 ≤ minusWeights0563 i) ∧
    (∀ i, plusCoefficients coefficients0563 upper0563 i = powerCoefficients10 plusWeights0563 i) ∧
    (∀ i, minusCoefficients coefficients0563 upper0563 i = powerCoefficients10 minusWeights0563 i) := by
  decide +kernel

theorem bound0563 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0563 g| ≤ (upper0563 : ℝ) :=
  abs_of_coefficients coefficients0563 upper0563 powerCoefficients10 plusWeights0563 minusWeights0563
    checked0563.1 checked0563.2.1 checked0563.2.2.1 checked0563.2.2.2
    (power_identity10 plusWeights0563) (power_identity10 minusWeights0563) g hg hmax

def envelope0563 : Envelope := ⟨coefficients0563, upper0563, bound0563⟩

def coefficients0564 : Fin 11 → ℚ := ![0, 0, 0, (-1/32), (1/32), (15/256), (111/1024), (535/8192), (2469/32768), (3253/65536), (8765/524288)]

def upper0564 : ℚ := (28755444119/1048576000000000)

def plusWeights0564 : Fin 11 → ℚ := ![(28755444119/1048576000000000), (28755444119/104857600000000), (258798997071/209715200000000), (85447132357/26214400000000), (581254406499/104857600000000), (1644629779497/262144000000000), (494410092899/104857600000000), (59397869957/26214400000000), (132373260687/209715200000000), (40694036699/524288000000000), 0]

def minusWeights0564 : Fin 11 → ℚ := ![(28755444119/1048576000000000), (28755444119/104857600000000), (258798997071/209715200000000), (87085532357/26214400000000), (626474246499/104857600000000), (1978556179497/262144000000000), (713318560099/104857600000000), (113134794757/26214400000000), (77044946691/41943040000000), (246860404491/524288000000000), (28755444119/524288000000000)]

theorem checked0564 :
    (∀ i, 0 ≤ plusWeights0564 i) ∧
    (∀ i, 0 ≤ minusWeights0564 i) ∧
    (∀ i, plusCoefficients coefficients0564 upper0564 i = powerCoefficients10 plusWeights0564 i) ∧
    (∀ i, minusCoefficients coefficients0564 upper0564 i = powerCoefficients10 minusWeights0564 i) := by
  decide +kernel

theorem bound0564 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0564 g| ≤ (upper0564 : ℝ) :=
  abs_of_coefficients coefficients0564 upper0564 powerCoefficients10 plusWeights0564 minusWeights0564
    checked0564.1 checked0564.2.1 checked0564.2.2.1 checked0564.2.2.2
    (power_identity10 plusWeights0564) (power_identity10 minusWeights0564) g hg hmax

def envelope0564 : Envelope := ⟨coefficients0564, upper0564, bound0564⟩

def coefficients0565 : Fin 11 → ℚ := ![0, 0, 0, (-1/32), (7/128), (13/128), (351/2048), (827/8192), (3173/32768), (4121/65536), (10205/524288)]

def upper0565 : ℚ := (25777259063/1048576000000000)

def plusWeights0565 : Fin 11 → ℚ := ![(25777259063/1048576000000000), (25777259063/104857600000000), (231995331567/209715200000000), (76512577189/26214400000000), (518958280323/104857600000000), (1460803160969/262144000000000), (435786491523/104857600000000), (51811453029/26214400000000), (113925060399/209715200000000), (34440246043/524288000000000), 0]

def minusWeights0565 : Fin 11 → ℚ := ![(25777259063/1048576000000000), (25777259063/104857600000000), (231995331567/209715200000000), (78150977189/26214400000000), (563686600323/104857600000000), (1787131480969/262144000000000), (646858389123/104857600000000), (102852101349/26214400000000), (70013120547/41943040000000), (223332344587/524288000000000), (25777259063/524288000000000)]

theorem checked0565 :
    (∀ i, 0 ≤ plusWeights0565 i) ∧
    (∀ i, 0 ≤ minusWeights0565 i) ∧
    (∀ i, plusCoefficients coefficients0565 upper0565 i = powerCoefficients10 plusWeights0565 i) ∧
    (∀ i, minusCoefficients coefficients0565 upper0565 i = powerCoefficients10 minusWeights0565 i) := by
  decide +kernel

theorem bound0565 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0565 g| ≤ (upper0565 : ℝ) :=
  abs_of_coefficients coefficients0565 upper0565 powerCoefficients10 plusWeights0565 minusWeights0565
    checked0565.1 checked0565.2.1 checked0565.2.2.1 checked0565.2.2.2
    (power_identity10 plusWeights0565) (power_identity10 minusWeights0565) g hg hmax

def envelope0565 : Envelope := ⟨coefficients0565, upper0565, bound0565⟩

def coefficients0566 : Fin 11 → ℚ := ![0, 0, 0, 0, (-3/64), (-45/256), (-141/1024), (-445/4096), (-73/1024), (-1845/32768), (-1165/65536)]

def upper0566 : ℚ := (864373053/131072000000000)

def plusWeights0566 : Fin 11 → ℚ := ![(864373053/131072000000000), (864373053/13107200000000), (7779357477/26214400000000), (2593119159/3276800000000), (18090394113/13107200000000), (53476302339/32768000000000), (17113229313/13107200000000), (2226478759/3276800000000), (5452826789/26214400000000), (372867227/13107200000000), 0]

def minusWeights0566 : Fin 11 → ℚ := ![(864373053/131072000000000), (864373053/13107200000000), (7779357477/26214400000000), (2593119159/3276800000000), (18213274113/13107200000000), (55434702339/32768000000000), (19190438913/13107200000000), (2959759559/3276800000000), (2021177633/5242880000000), (1355878879/13107200000000), (864373053/65536000000000)]

theorem checked0566 :
    (∀ i, 0 ≤ plusWeights0566 i) ∧
    (∀ i, 0 ≤ minusWeights0566 i) ∧
    (∀ i, plusCoefficients coefficients0566 upper0566 i = powerCoefficients10 plusWeights0566 i) ∧
    (∀ i, minusCoefficients coefficients0566 upper0566 i = powerCoefficients10 minusWeights0566 i) := by
  decide +kernel

theorem bound0566 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0566 g| ≤ (upper0566 : ℝ) :=
  abs_of_coefficients coefficients0566 upper0566 powerCoefficients10 plusWeights0566 minusWeights0566
    checked0566.1 checked0566.2.1 checked0566.2.2.1 checked0566.2.2.2
    (power_identity10 plusWeights0566) (power_identity10 minusWeights0566) g hg hmax

def envelope0566 : Envelope := ⟨coefficients0566, upper0566, bound0566⟩

def coefficients0567 : Fin 11 → ℚ := ![0, 0, 0, 0, (-1/32), (-35/256), (-13/128), (-265/4096), (-69/2048), (-925/32768), (-585/65536)]

def upper0567 : ℚ := (603007977/131072000000000)

def plusWeights0567 : Fin 11 → ℚ := ![(603007977/131072000000000), (603007977/13107200000000), (5427071793/26214400000000), (1809023931/3276800000000), (12622207517/13107200000000), (37330302551/32768000000000), (11957836317/13107200000000), (1558071531/3276800000000), (3823379761/26214400000000), (10482383/524288000000), 0]

def minusWeights0567 : Fin 11 → ℚ := ![(603007977/131072000000000), (603007977/13107200000000), (5427071793/26214400000000), (1809023931/3276800000000), (12704127517/13107200000000), (38648702551/32768000000000), (13368498717/13107200000000), (2059976331/3276800000000), (281230553/1048576000000), (943956379/13107200000000), (603007977/65536000000000)]

theorem checked0567 :
    (∀ i, 0 ≤ plusWeights0567 i) ∧
    (∀ i, 0 ≤ minusWeights0567 i) ∧
    (∀ i, plusCoefficients coefficients0567 upper0567 i = powerCoefficients10 plusWeights0567 i) ∧
    (∀ i, minusCoefficients coefficients0567 upper0567 i = powerCoefficients10 minusWeights0567 i) := by
  decide +kernel

theorem bound0567 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0567 g| ≤ (upper0567 : ℝ) :=
  abs_of_coefficients coefficients0567 upper0567 powerCoefficients10 plusWeights0567 minusWeights0567
    checked0567.1 checked0567.2.1 checked0567.2.2.1 checked0567.2.2.2
    (power_identity10 plusWeights0567) (power_identity10 minusWeights0567) g hg hmax

def envelope0567 : Envelope := ⟨coefficients0567, upper0567, bound0567⟩

def coefficients0568 : Fin 11 → ℚ := ![0, 0, 0, 0, (-1/32), (-29/256), (-19/256), (-245/4096), (-67/2048), (-415/16384), (-265/32768)]

def upper0568 : ℚ := (284319153/65536000000000)

def plusWeights0568 : Fin 11 → ℚ := ![(284319153/65536000000000), (284319153/6553600000000), (2558872377/13107200000000), (852957459/1638400000000), (5950222213/6553600000000), (17586346639/16384000000000), (5625895813/6553600000000), (731501259/1638400000000), (1789916089/13107200000000), (122251499/6553600000000), 0]

def minusWeights0568 : Fin 11 → ℚ := ![(284319153/65536000000000), (284319153/6553600000000), (2558872377/13107200000000), (852957459/1638400000000), (5991182213/6553600000000), (18237866639/16384000000000), (6315508613/6553600000000), (974413659/1638400000000), (665565733/2621440000000), (446386807/6553600000000), (284319153/32768000000000)]

theorem checked0568 :
    (∀ i, 0 ≤ plusWeights0568 i) ∧
    (∀ i, 0 ≤ minusWeights0568 i) ∧
    (∀ i, plusCoefficients coefficients0568 upper0568 i = powerCoefficients10 plusWeights0568 i) ∧
    (∀ i, minusCoefficients coefficients0568 upper0568 i = powerCoefficients10 minusWeights0568 i) := by
  decide +kernel

theorem bound0568 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0568 g| ≤ (upper0568 : ℝ) :=
  abs_of_coefficients coefficients0568 upper0568 powerCoefficients10 plusWeights0568 minusWeights0568
    checked0568.1 checked0568.2.1 checked0568.2.2.1 checked0568.2.2.2
    (power_identity10 plusWeights0568) (power_identity10 minusWeights0568) g hg hmax

def envelope0568 : Envelope := ⟨coefficients0568, upper0568, bound0568⟩

def coefficients0569 : Fin 11 → ℚ := ![0, 0, 0, 0, (-1/64), (-25/256), (-67/1024), (-145/4096), (-11/1024), (-275/32768), (-155/65536)]

def upper0569 : ℚ := (341855211/131072000000000)

def plusWeights0569 : Fin 11 → ℚ := ![(341855211/131072000000000), (341855211/13107200000000), (3076696899/26214400000000), (1025565633/3276800000000), (7158479431/13107200000000), (21197678293/32768000000000), (6806901831/13107200000000), (890296433/3276800000000), (2195724483/26214400000000), (30280537/2621440000000), 0]

def minusWeights0569 : Fin 11 → ℚ := ![(341855211/131072000000000), (341855211/13107200000000), (3076696899/26214400000000), (1025565633/3276800000000), (7199439431/13107200000000), (21876078293/32768000000000), (7551017031/13107200000000), (1160834833/3276800000000), (791533863/5242880000000), (532307737/13107200000000), (341855211/65536000000000)]

theorem checked0569 :
    (∀ i, 0 ≤ plusWeights0569 i) ∧
    (∀ i, 0 ≤ minusWeights0569 i) ∧
    (∀ i, plusCoefficients coefficients0569 upper0569 i = powerCoefficients10 plusWeights0569 i) ∧
    (∀ i, minusCoefficients coefficients0569 upper0569 i = powerCoefficients10 minusWeights0569 i) := by
  decide +kernel

theorem bound0569 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0569 g| ≤ (upper0569 : ℝ) :=
  abs_of_coefficients coefficients0569 upper0569 powerCoefficients10 plusWeights0569 minusWeights0569
    checked0569.1 checked0569.2.1 checked0569.2.2.1 checked0569.2.2.2
    (power_identity10 plusWeights0569) (power_identity10 minusWeights0569) g hg hmax

def envelope0569 : Envelope := ⟨coefficients0569, upper0569, bound0569⟩

def coefficients0570 : Fin 11 → ℚ := ![0, 0, 0, 0, (-1/64), (-11/128), (-53/1024), (-25/512), (-107/4096), (-335/16384), (-55/8192)]

def upper0570 : ℚ := (20306313/8192000000000)

def plusWeights0570 : Fin 11 → ℚ := ![(20306313/8192000000000), (20306313/819200000000), (182756817/1638400000000), (60918939/204800000000), (425152573/819200000000), (1258337719/2048000000000), (403670173/819200000000), (52715539/204800000000), (129743589/1638400000000), (35697073/3276800000000), 0]

def minusWeights0570 : Fin 11 → ℚ := ![(20306313/8192000000000), (20306313/819200000000), (182756817/1638400000000), (60918939/204800000000), (427712573/819200000000), (1300257719/2048000000000), (449194973/819200000000), (69122339/204800000000), (47154009/327680000000), (126753431/3276800000000), (20306313/4096000000000)]

theorem checked0570 :
    (∀ i, 0 ≤ plusWeights0570 i) ∧
    (∀ i, 0 ≤ minusWeights0570 i) ∧
    (∀ i, plusCoefficients coefficients0570 upper0570 i = powerCoefficients10 plusWeights0570 i) ∧
    (∀ i, minusCoefficients coefficients0570 upper0570 i = powerCoefficients10 minusWeights0570 i) := by
  decide +kernel

theorem bound0570 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0570 g| ≤ (upper0570 : ℝ) :=
  abs_of_coefficients coefficients0570 upper0570 powerCoefficients10 plusWeights0570 minusWeights0570
    checked0570.1 checked0570.2.1 checked0570.2.2.1 checked0570.2.2.2
    (power_identity10 plusWeights0570) (power_identity10 minusWeights0570) g hg hmax

def envelope0570 : Envelope := ⟨coefficients0570, upper0570, bound0570⟩

def coefficients0571 : Fin 11 → ℚ := ![0, 0, 0, 0, (-1/64), (-15/256), (-47/1024), (-195/4096), (-9/256), (-625/32768), (-305/65536)]

def upper0571 : ℚ := (288288641/131072000000000)

def plusWeights0571 : Fin 11 → ℚ := ![(288288641/131072000000000), (288288641/13107200000000), (2594597769/26214400000000), (864865923/3276800000000), (6033581461/13107200000000), (17835784383/32768000000000), (5707859861/13107200000000), (742648723/3276800000000), (1818994953/26214400000000), (4976223/524288000000), 0]

def minusWeights0571 : Fin 11 → ℚ := ![(288288641/131072000000000), (288288641/13107200000000), (2594597769/26214400000000), (864865923/3276800000000), (6074541461/13107200000000), (18488584383/32768000000000), (6400263061/13107200000000), (987083123/3276800000000), (674040117/5242880000000), (452171707/13107200000000), (288288641/65536000000000)]

theorem checked0571 :
    (∀ i, 0 ≤ plusWeights0571 i) ∧
    (∀ i, 0 ≤ minusWeights0571 i) ∧
    (∀ i, plusCoefficients coefficients0571 upper0571 i = powerCoefficients10 plusWeights0571 i) ∧
    (∀ i, minusCoefficients coefficients0571 upper0571 i = powerCoefficients10 minusWeights0571 i) := by
  decide +kernel

theorem bound0571 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0571 g| ≤ (upper0571 : ℝ) :=
  abs_of_coefficients coefficients0571 upper0571 powerCoefficients10 plusWeights0571 minusWeights0571
    checked0571.1 checked0571.2.1 checked0571.2.2.1 checked0571.2.2.2
    (power_identity10 plusWeights0571) (power_identity10 minusWeights0571) g hg hmax

def envelope0571 : Envelope := ⟨coefficients0571, upper0571, bound0571⟩

def coefficients0572 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (-15/256), (-15/512), (-25/4096), (25/2048), (225/32768), (125/65536)]

def upper0572 : ℚ := (3228123/5242880000000)

def plusWeights0572 : Fin 11 → ℚ := ![(3228123/5242880000000), (3228123/524288000000), (29053107/1048576000000), (9684369/131072000000), (67790583/524288000000), (202603749/1310720000000), (66239223/524288000000), (8900929/131072000000), (4544599/209715200000), (8149273/2621440000000), 0]

def minusWeights0572 : Fin 11 → ℚ := ![(3228123/5242880000000), (3228123/524288000000), (29053107/1048576000000), (9684369/131072000000), (67790583/524288000000), (204139749/1310720000000), (69341943/524288000000), (10467809/131072000000), (35383219/1048576000000), (24131957/2621440000000), (3228123/2621440000000)]

theorem checked0572 :
    (∀ i, 0 ≤ plusWeights0572 i) ∧
    (∀ i, 0 ≤ minusWeights0572 i) ∧
    (∀ i, plusCoefficients coefficients0572 upper0572 i = powerCoefficients10 plusWeights0572 i) ∧
    (∀ i, minusCoefficients coefficients0572 upper0572 i = powerCoefficients10 minusWeights0572 i) := by
  decide +kernel

theorem bound0572 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0572 g| ≤ (upper0572 : ℝ) :=
  abs_of_coefficients coefficients0572 upper0572 powerCoefficients10 plusWeights0572 minusWeights0572
    checked0572.1 checked0572.2.1 checked0572.2.2.1 checked0572.2.2.2
    (power_identity10 plusWeights0572) (power_identity10 minusWeights0572) g hg hmax

def envelope0572 : Envelope := ⟨coefficients0572, upper0572, bound0572⟩

def coefficients0573 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (-25/512), (-29/1024), (-497/8192), (-249/4096), (-1575/32768), (-985/65536)]

def upper0573 : ℚ := (68593377/131072000000000)

def plusWeights0573 : Fin 11 → ℚ := ![(68593377/131072000000000), (68593377/13107200000000), (617340393/26214400000000), (205780131/3276800000000), (1440460917/13107200000000), (4305382751/32768000000000), (1408089717/13107200000000), (189389051/3276800000000), (484392937/26214400000000), (34853451/13107200000000), 0]

def minusWeights0573 : Fin 11 → ℚ := ![(68593377/131072000000000), (68593377/13107200000000), (617340393/26214400000000), (205780131/3276800000000), (1440460917/13107200000000), (4337382751/32768000000000), (1472832117/13107200000000), (222171211/3276800000000), (750287849/26214400000000), (102333303/13107200000000), (68593377/65536000000000)]

theorem checked0573 :
    (∀ i, 0 ≤ plusWeights0573 i) ∧
    (∀ i, 0 ≤ minusWeights0573 i) ∧
    (∀ i, plusCoefficients coefficients0573 upper0573 i = powerCoefficients10 plusWeights0573 i) ∧
    (∀ i, minusCoefficients coefficients0573 upper0573 i = powerCoefficients10 minusWeights0573 i) := by
  decide +kernel

theorem bound0573 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0573 g| ≤ (upper0573 : ℝ) :=
  abs_of_coefficients coefficients0573 upper0573 powerCoefficients10 plusWeights0573 minusWeights0573
    checked0573.1 checked0573.2.1 checked0573.2.2.1 checked0573.2.2.2
    (power_identity10 plusWeights0573) (power_identity10 minusWeights0573) g hg hmax

def envelope0573 : Envelope := ⟨coefficients0573, upper0573, bound0573⟩

def coefficients0574 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (-3/64), (-43/512), (-883/8192), (-249/4096), (-1397/16384), (-69/2048)]

def upper0574 : ℚ := (46220061/81920000000000)

def plusWeights0574 : Fin 11 → ℚ := ![(46220061/81920000000000), (46220061/8192000000000), (415980549/16384000000000), (138660183/2048000000000), (970621281/8192000000000), (2902263843/20480000000000), (950733281/8192000000000), (32087527/512000000000), (330384789/16384000000000), (9597001/3276800000000), 0]

def minusWeights0574 : Fin 11 → ℚ := ![(46220061/81920000000000), (46220061/8192000000000), (415980549/16384000000000), (138660183/2048000000000), (970621281/8192000000000), (2921463843/20480000000000), (990509281/8192000000000), (74485129/1024000000000), (501576309/16384000000000), (136895239/16384000000000), (46220061/40960000000000)]

theorem checked0574 :
    (∀ i, 0 ≤ plusWeights0574 i) ∧
    (∀ i, 0 ≤ minusWeights0574 i) ∧
    (∀ i, plusCoefficients coefficients0574 upper0574 i = powerCoefficients10 plusWeights0574 i) ∧
    (∀ i, minusCoefficients coefficients0574 upper0574 i = powerCoefficients10 minusWeights0574 i) := by
  decide +kernel

theorem bound0574 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0574 g| ≤ (upper0574 : ℝ) :=
  abs_of_coefficients coefficients0574 upper0574 powerCoefficients10 plusWeights0574 minusWeights0574
    checked0574.1 checked0574.2.1 checked0574.2.2.1 checked0574.2.2.2
    (power_identity10 plusWeights0574) (power_identity10 minusWeights0574) g hg hmax

def envelope0574 : Envelope := ⟨coefficients0574, upper0574, bound0574⟩

def coefficients0575 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (-23/512), (-31/1024), (-417/8192), (-175/4096), (-1815/65536), (-1035/131072)]

def upper0575 : ℚ := (127149867/262144000000000)

def plusWeights0575 : Fin 11 → ℚ := ![(127149867/262144000000000), (127149867/26214400000000), (1144348803/52428800000000), (381449601/6553600000000), (2670147207/26214400000000), (7981001621/65536000000000), (2610473607/26214400000000), (351182641/6553600000000), (898482563/52428800000000), (64672021/26214400000000), 0]

def minusWeights0575 : Fin 11 → ℚ := ![(127149867/262144000000000), (127149867/26214400000000), (1144348803/52428800000000), (381449601/6553600000000), (2670147207/26214400000000), (8039881621/65536000000000), (2729820807/26214400000000), (411716561/6553600000000), (1390215043/52428800000000), (189627713/26214400000000), (127149867/131072000000000)]

theorem checked0575 :
    (∀ i, 0 ≤ plusWeights0575 i) ∧
    (∀ i, 0 ≤ minusWeights0575 i) ∧
    (∀ i, plusCoefficients coefficients0575 upper0575 i = powerCoefficients10 plusWeights0575 i) ∧
    (∀ i, minusCoefficients coefficients0575 upper0575 i = powerCoefficients10 minusWeights0575 i) := by
  decide +kernel

theorem bound0575 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0575 g| ≤ (upper0575 : ℝ) :=
  abs_of_coefficients coefficients0575 upper0575 powerCoefficients10 plusWeights0575 minusWeights0575
    checked0575.1 checked0575.2.1 checked0575.2.2.1 checked0575.2.2.2
    (power_identity10 plusWeights0575) (power_identity10 minusWeights0575) g hg hmax

def envelope0575 : Envelope := ⟨coefficients0575, upper0575, bound0575⟩

end BilayerDressed.CubicQuarticEnvelopes
