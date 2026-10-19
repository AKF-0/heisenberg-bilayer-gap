import Dressed.CubicResidualBernstein
import Dressed.ScalarTrialMajorants

/-! Exact whole-interval bounds for the displayed rational polynomials only.
Bernstein identities and coefficient signs are checked here. Identification with
the actual graph residual is proved separately in CubicResidualIntervals and
CubicResidualIntervalBounds; this module alone proves no physical bound. -/
noncomputable section
open scoped BigOperators
namespace BilayerDressed.CubicResidualIntervalCertificates
open BilayerGap BilayerDressed.CubicResidualCoefficients
open BilayerDressed.CubicResidualBernstein
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

def pairPoly0 : Fin 8 → ℚ := ![0,0,0,0,0,0,0,0]
def pairBound0 : ℚ := 0

theorem pair_bound0 (g : ℝ) (_hg : 0≤g) (_hmax : g≤1/10) :
    |evalCoeff pairPoly0 g|≤(pairBound0 : ℝ) := by
  simp [evalCoeff,pairPoly0,pairBound0,Fin.sum_univ_succ]

def pairPoly1 : Fin 8 → ℚ := ![0,0,0,0,(-1/32),(27/64),(9/16),(747/512)]
def pairBound1 : ℚ := (9227/5120000000)

def pairPlus1Weights0 : Fin 8 → ℚ := ![(9227/5120000000),(64589/5120000000),(193767/5120000000),(64589/1024000000),(61389/1024000000),(167367/5120000000),(62669/5120000000),(9227/2560000000)]

theorem pairPlus1Weights0_nonneg : ∀ i,0≤pairPlus1Weights0 i := by
  decide +kernel

theorem pairPlus1Identity0 (x : ℝ) :
    (pairBound1 : ℝ)+evalCoeff pairPoly1 x=bernsteinValue pairPlus1Weights0
      ((x-(0 : ℚ))/(((1/10) : ℚ)-(0 : ℚ))) := by
  norm_num [evalCoeff,bernsteinValue,pairPlus1Weights0,pairBound1,pairPoly1,Fin.sum_univ_succ]
  ring

theorem pairPlus1_nonneg (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    0≤(pairBound1 : ℝ)+evalCoeff pairPoly1 g := by
  exact interval_nonneg (fun x => (pairBound1 : ℝ)+evalCoeff pairPoly1 x) 0 (1/10)
    (by norm_num) pairPlus1Weights0 pairPlus1Weights0_nonneg
    pairPlus1Identity0 g (by simpa using hg) (by simpa using hmax)

def pairMinus1Weights0 : Fin 8 → ℚ := ![(9227/5120000000),(64589/5120000000),(193767/5120000000),(64589/1024000000),(67789/1024000000),(220167/5120000000),(66509/5120000000),0]

theorem pairMinus1Weights0_nonneg : ∀ i,0≤pairMinus1Weights0 i := by
  decide +kernel

theorem pairMinus1Identity0 (x : ℝ) :
    (pairBound1 : ℝ)-evalCoeff pairPoly1 x=bernsteinValue pairMinus1Weights0
      ((x-(0 : ℚ))/(((1/10) : ℚ)-(0 : ℚ))) := by
  norm_num [evalCoeff,bernsteinValue,pairMinus1Weights0,pairBound1,pairPoly1,Fin.sum_univ_succ]
  ring

theorem pairMinus1_nonneg (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    0≤(pairBound1 : ℝ)-evalCoeff pairPoly1 g := by
  exact interval_nonneg (fun x => (pairBound1 : ℝ)-evalCoeff pairPoly1 x) 0 (1/10)
    (by norm_num) pairMinus1Weights0 pairMinus1Weights0_nonneg
    pairMinus1Identity0 g (by simpa using hg) (by simpa using hmax)

theorem pair_bound1 (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    |evalCoeff pairPoly1 g|≤(pairBound1 : ℝ) := by
  have hlo := pairPlus1_nonneg g hg hmax
  have hhi := pairMinus1_nonneg g hg hmax
  exact abs_le.mpr ⟨by linarith,by linarith⟩

def pairPoly2 : Fin 8 → ℚ := ![0,0,0,0,-1,(1/4),(-19/16),(-5/8)]
def pairBound2 : ℚ := (79/800000)

def pairPlus2Weights0 : Fin 8 → ℚ := ![(79/800000),(553/800000),(1659/800000),(553/160000),(537/160000),(1421/800000),(6321/16000000),0]

theorem pairPlus2Weights0_nonneg : ∀ i,0≤pairPlus2Weights0 i := by
  decide +kernel

theorem pairPlus2Identity0 (x : ℝ) :
    (pairBound2 : ℝ)+evalCoeff pairPoly2 x=bernsteinValue pairPlus2Weights0
      ((x-(0 : ℚ))/(((1/10) : ℚ)-(0 : ℚ))) := by
  norm_num [evalCoeff,bernsteinValue,pairPlus2Weights0,pairBound2,pairPoly2,Fin.sum_univ_succ]
  ring

theorem pairPlus2_nonneg (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    0≤(pairBound2 : ℝ)+evalCoeff pairPoly2 g := by
  exact interval_nonneg (fun x => (pairBound2 : ℝ)+evalCoeff pairPoly2 x) 0 (1/10)
    (by norm_num) pairPlus2Weights0 pairPlus2Weights0_nonneg
    pairPlus2Identity0 g (by simpa using hg) (by simpa using hmax)

def pairMinus2Weights0 : Fin 8 → ℚ := ![(79/800000),(553/800000),(1659/800000),(553/160000),(569/160000),(1897/800000),(15799/16000000),(79/400000)]

theorem pairMinus2Weights0_nonneg : ∀ i,0≤pairMinus2Weights0 i := by
  decide +kernel

theorem pairMinus2Identity0 (x : ℝ) :
    (pairBound2 : ℝ)-evalCoeff pairPoly2 x=bernsteinValue pairMinus2Weights0
      ((x-(0 : ℚ))/(((1/10) : ℚ)-(0 : ℚ))) := by
  norm_num [evalCoeff,bernsteinValue,pairMinus2Weights0,pairBound2,pairPoly2,Fin.sum_univ_succ]
  ring

theorem pairMinus2_nonneg (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    0≤(pairBound2 : ℝ)-evalCoeff pairPoly2 g := by
  exact interval_nonneg (fun x => (pairBound2 : ℝ)-evalCoeff pairPoly2 x) 0 (1/10)
    (by norm_num) pairMinus2Weights0 pairMinus2Weights0_nonneg
    pairMinus2Identity0 g (by simpa using hg) (by simpa using hmax)

theorem pair_bound2 (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    |evalCoeff pairPoly2 g|≤(pairBound2 : ℝ) := by
  have hlo := pairPlus2_nonneg g hg hmax
  have hhi := pairMinus2_nonneg g hg hmax
  exact abs_le.mpr ⟨by linarith,by linarith⟩

def pairPoly3 : Fin 8 → ℚ := ![0,0,0,0,(9/16),(9/64),(21/64),(111/256)]
def pairBound3 : ℚ := (148551/2560000000)

def pairPlus3Weights0 : Fin 8 → ℚ := ![(148551/2560000000),(1039857/2560000000),(3119571/2560000000),(1039857/512000000),(1068657/512000000),(3555171/2560000000),(1479897/2560000000),(148551/1280000000)]

theorem pairPlus3Weights0_nonneg : ∀ i,0≤pairPlus3Weights0 i := by
  decide +kernel

theorem pairPlus3Identity0 (x : ℝ) :
    (pairBound3 : ℝ)+evalCoeff pairPoly3 x=bernsteinValue pairPlus3Weights0
      ((x-(0 : ℚ))/(((1/10) : ℚ)-(0 : ℚ))) := by
  norm_num [evalCoeff,bernsteinValue,pairPlus3Weights0,pairBound3,pairPoly3,Fin.sum_univ_succ]
  ring

theorem pairPlus3_nonneg (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    0≤(pairBound3 : ℝ)+evalCoeff pairPoly3 g := by
  exact interval_nonneg (fun x => (pairBound3 : ℝ)+evalCoeff pairPoly3 x) 0 (1/10)
    (by norm_num) pairPlus3Weights0 pairPlus3Weights0_nonneg
    pairPlus3Identity0 g (by simpa using hg) (by simpa using hmax)

def pairMinus3Weights0 : Fin 8 → ℚ := ![(148551/2560000000),(1039857/2560000000),(3119571/2560000000),(1039857/512000000),(1011057/512000000),(2683971/2560000000),(599817/2560000000),0]

theorem pairMinus3Weights0_nonneg : ∀ i,0≤pairMinus3Weights0 i := by
  decide +kernel

theorem pairMinus3Identity0 (x : ℝ) :
    (pairBound3 : ℝ)-evalCoeff pairPoly3 x=bernsteinValue pairMinus3Weights0
      ((x-(0 : ℚ))/(((1/10) : ℚ)-(0 : ℚ))) := by
  norm_num [evalCoeff,bernsteinValue,pairMinus3Weights0,pairBound3,pairPoly3,Fin.sum_univ_succ]
  ring

theorem pairMinus3_nonneg (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    0≤(pairBound3 : ℝ)-evalCoeff pairPoly3 g := by
  exact interval_nonneg (fun x => (pairBound3 : ℝ)-evalCoeff pairPoly3 x) 0 (1/10)
    (by norm_num) pairMinus3Weights0 pairMinus3Weights0_nonneg
    pairMinus3Identity0 g (by simpa using hg) (by simpa using hmax)

theorem pair_bound3 (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    |evalCoeff pairPoly3 g|≤(pairBound3 : ℝ) := by
  have hlo := pairPlus3_nonneg g hg hmax
  have hhi := pairMinus3_nonneg g hg hmax
  exact abs_le.mpr ⟨by linarith,by linarith⟩

def pairPoly4 : Fin 8 → ℚ := ![0,0,0,0,(-21/8),(-3/4),(-33/16),(-15/16)]
def pairBound4 : ℚ := (8709/32000000)

def pairPlus4Weights0 : Fin 8 → ℚ := ![(8709/32000000),(60963/32000000),(182889/32000000),(60963/6400000),(59283/6400000),(157449/32000000),(35217/32000000),0]

theorem pairPlus4Weights0_nonneg : ∀ i,0≤pairPlus4Weights0 i := by
  decide +kernel

theorem pairPlus4Identity0 (x : ℝ) :
    (pairBound4 : ℝ)+evalCoeff pairPoly4 x=bernsteinValue pairPlus4Weights0
      ((x-(0 : ℚ))/(((1/10) : ℚ)-(0 : ℚ))) := by
  norm_num [evalCoeff,bernsteinValue,pairPlus4Weights0,pairBound4,pairPoly4,Fin.sum_univ_succ]
  ring

theorem pairPlus4_nonneg (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    0≤(pairBound4 : ℝ)+evalCoeff pairPoly4 g := by
  exact interval_nonneg (fun x => (pairBound4 : ℝ)+evalCoeff pairPoly4 x) 0 (1/10)
    (by norm_num) pairPlus4Weights0 pairPlus4Weights0_nonneg
    pairPlus4Identity0 g (by simpa using hg) (by simpa using hmax)

def pairMinus4Weights0 : Fin 8 → ℚ := ![(8709/32000000),(60963/32000000),(182889/32000000),(60963/6400000),(62643/6400000),(208329/32000000),(86709/32000000),(8709/16000000)]

theorem pairMinus4Weights0_nonneg : ∀ i,0≤pairMinus4Weights0 i := by
  decide +kernel

theorem pairMinus4Identity0 (x : ℝ) :
    (pairBound4 : ℝ)-evalCoeff pairPoly4 x=bernsteinValue pairMinus4Weights0
      ((x-(0 : ℚ))/(((1/10) : ℚ)-(0 : ℚ))) := by
  norm_num [evalCoeff,bernsteinValue,pairMinus4Weights0,pairBound4,pairPoly4,Fin.sum_univ_succ]
  ring

theorem pairMinus4_nonneg (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    0≤(pairBound4 : ℝ)-evalCoeff pairPoly4 g := by
  exact interval_nonneg (fun x => (pairBound4 : ℝ)-evalCoeff pairPoly4 x) 0 (1/10)
    (by norm_num) pairMinus4Weights0 pairMinus4Weights0_nonneg
    pairMinus4Identity0 g (by simpa using hg) (by simpa using hmax)

theorem pair_bound4 (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    |evalCoeff pairPoly4 g|≤(pairBound4 : ℝ) := by
  have hlo := pairPlus4_nonneg g hg hmax
  have hhi := pairMinus4_nonneg g hg hmax
  exact abs_le.mpr ⟨by linarith,by linarith⟩

def pairPoly5 : Fin 8 → ℚ := ![0,0,0,0,(-1/32),(39/128),(119/256),(1873/2048)]
def pairBound5 : ℚ := (9793/20480000000)

def pairPlus5Weights0 : Fin 8 → ℚ := ![(9793/20480000000),(68551/20480000000),(205653/20480000000),(68551/4096000000),(55751/4096000000),(76053/20480000000),(10871/20480000000),(9793/10240000000)]

theorem pairPlus5Weights0_nonneg : ∀ i,0≤pairPlus5Weights0 i := by
  decide +kernel

theorem pairPlus5Identity0 (x : ℝ) :
    (pairBound5 : ℝ)+evalCoeff pairPoly5 x=bernsteinValue pairPlus5Weights0
      ((x-(0 : ℚ))/(((1/10) : ℚ)-(0 : ℚ))) := by
  norm_num [evalCoeff,bernsteinValue,pairPlus5Weights0,pairBound5,pairPoly5,Fin.sum_univ_succ]
  ring

theorem pairPlus5_nonneg (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    0≤(pairBound5 : ℝ)+evalCoeff pairPoly5 g := by
  exact interval_nonneg (fun x => (pairBound5 : ℝ)+evalCoeff pairPoly5 x) 0 (1/10)
    (by norm_num) pairPlus5Weights0 pairPlus5Weights0_nonneg
    pairPlus5Identity0 g (by simpa using hg) (by simpa using hmax)

def pairMinus5Weights0 : Fin 8 → ℚ := ![(9793/20480000000),(68551/20480000000),(205653/20480000000),(68551/4096000000),(81351/4096000000),(335253/20480000000),(126231/20480000000),0]

theorem pairMinus5Weights0_nonneg : ∀ i,0≤pairMinus5Weights0 i := by
  decide +kernel

theorem pairMinus5Identity0 (x : ℝ) :
    (pairBound5 : ℝ)-evalCoeff pairPoly5 x=bernsteinValue pairMinus5Weights0
      ((x-(0 : ℚ))/(((1/10) : ℚ)-(0 : ℚ))) := by
  norm_num [evalCoeff,bernsteinValue,pairMinus5Weights0,pairBound5,pairPoly5,Fin.sum_univ_succ]
  ring

theorem pairMinus5_nonneg (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    0≤(pairBound5 : ℝ)-evalCoeff pairPoly5 g := by
  exact interval_nonneg (fun x => (pairBound5 : ℝ)-evalCoeff pairPoly5 x) 0 (1/10)
    (by norm_num) pairMinus5Weights0 pairMinus5Weights0_nonneg
    pairMinus5Identity0 g (by simpa using hg) (by simpa using hmax)

theorem pair_bound5 (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    |evalCoeff pairPoly5 g|≤(pairBound5 : ℝ) := by
  have hlo := pairPlus5_nonneg g hg hmax
  have hhi := pairMinus5_nonneg g hg hmax
  exact abs_le.mpr ⟨by linarith,by linarith⟩

def pairPoly6 : Fin 8 → ℚ := ![0,0,0,0,-1,(1/4),(-97/128),(-105/256)]
def pairBound6 : ℚ := (50329/512000000)

def pairPlus6Weights0 : Fin 8 → ℚ := ![(50329/512000000),(352303/512000000),(1056909/512000000),(352303/102400000),(342063/102400000),(904589/512000000),(1607/4096000),0]

theorem pairPlus6Weights0_nonneg : ∀ i,0≤pairPlus6Weights0 i := by
  decide +kernel

theorem pairPlus6Identity0 (x : ℝ) :
    (pairBound6 : ℝ)+evalCoeff pairPoly6 x=bernsteinValue pairPlus6Weights0
      ((x-(0 : ℚ))/(((1/10) : ℚ)-(0 : ℚ))) := by
  norm_num [evalCoeff,bernsteinValue,pairPlus6Weights0,pairBound6,pairPoly6,Fin.sum_univ_succ]
  ring

theorem pairPlus6_nonneg (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    0≤(pairBound6 : ℝ)+evalCoeff pairPoly6 g := by
  exact interval_nonneg (fun x => (pairBound6 : ℝ)+evalCoeff pairPoly6 x) 0 (1/10)
    (by norm_num) pairPlus6Weights0 pairPlus6Weights0_nonneg
    pairPlus6Identity0 g (by simpa using hg) (by simpa using hmax)

def pairMinus6Weights0 : Fin 8 → ℚ := ![(50329/512000000),(352303/512000000),(1056909/512000000),(352303/102400000),(362543/102400000),(1209229/512000000),(503731/512000000),(50329/256000000)]

theorem pairMinus6Weights0_nonneg : ∀ i,0≤pairMinus6Weights0 i := by
  decide +kernel

theorem pairMinus6Identity0 (x : ℝ) :
    (pairBound6 : ℝ)-evalCoeff pairPoly6 x=bernsteinValue pairMinus6Weights0
      ((x-(0 : ℚ))/(((1/10) : ℚ)-(0 : ℚ))) := by
  norm_num [evalCoeff,bernsteinValue,pairMinus6Weights0,pairBound6,pairPoly6,Fin.sum_univ_succ]
  ring

theorem pairMinus6_nonneg (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    0≤(pairBound6 : ℝ)-evalCoeff pairPoly6 g := by
  exact interval_nonneg (fun x => (pairBound6 : ℝ)-evalCoeff pairPoly6 x) 0 (1/10)
    (by norm_num) pairMinus6Weights0 pairMinus6Weights0_nonneg
    pairMinus6Identity0 g (by simpa using hg) (by simpa using hmax)

theorem pair_bound6 (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    |evalCoeff pairPoly6 g|≤(pairBound6 : ℝ) := by
  have hlo := pairPlus6_nonneg g hg hmax
  have hhi := pairMinus6_nonneg g hg hmax
  exact abs_le.mpr ⟨by linarith,by linarith⟩

def pairPoly7 : Fin 8 → ℚ := ![0,0,0,0,(-13/64),(5/16),(113/256),(2041/2048)]
def pairBound7 : ℚ := (340919/20480000000)

def pairPlus7Weights0 : Fin 8 → ℚ := ![(340919/20480000000),(2386433/20480000000),(7159299/20480000000),(2386433/4096000000),(2303233/4096000000),(5975299/20480000000),(1275473/20480000000),0]

theorem pairPlus7Weights0_nonneg : ∀ i,0≤pairPlus7Weights0 i := by
  decide +kernel

theorem pairPlus7Identity0 (x : ℝ) :
    (pairBound7 : ℝ)+evalCoeff pairPoly7 x=bernsteinValue pairPlus7Weights0
      ((x-(0 : ℚ))/(((1/10) : ℚ)-(0 : ℚ))) := by
  norm_num [evalCoeff,bernsteinValue,pairPlus7Weights0,pairBound7,pairPoly7,Fin.sum_univ_succ]
  ring

theorem pairPlus7_nonneg (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    0≤(pairBound7 : ℝ)+evalCoeff pairPoly7 g := by
  exact interval_nonneg (fun x => (pairBound7 : ℝ)+evalCoeff pairPoly7 x) 0 (1/10)
    (by norm_num) pairPlus7Weights0 pairPlus7Weights0_nonneg
    pairPlus7Identity0 g (by simpa using hg) (by simpa using hmax)

def pairMinus7Weights0 : Fin 8 → ℚ := ![(340919/20480000000),(2386433/20480000000),(7159299/20480000000),(2386433/4096000000),(2469633/4096000000),(8343299/20480000000),(3497393/20480000000),(340919/10240000000)]

theorem pairMinus7Weights0_nonneg : ∀ i,0≤pairMinus7Weights0 i := by
  decide +kernel

theorem pairMinus7Identity0 (x : ℝ) :
    (pairBound7 : ℝ)-evalCoeff pairPoly7 x=bernsteinValue pairMinus7Weights0
      ((x-(0 : ℚ))/(((1/10) : ℚ)-(0 : ℚ))) := by
  norm_num [evalCoeff,bernsteinValue,pairMinus7Weights0,pairBound7,pairPoly7,Fin.sum_univ_succ]
  ring

theorem pairMinus7_nonneg (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    0≤(pairBound7 : ℝ)-evalCoeff pairPoly7 g := by
  exact interval_nonneg (fun x => (pairBound7 : ℝ)-evalCoeff pairPoly7 x) 0 (1/10)
    (by norm_num) pairMinus7Weights0 pairMinus7Weights0_nonneg
    pairMinus7Identity0 g (by simpa using hg) (by simpa using hmax)

theorem pair_bound7 (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    |evalCoeff pairPoly7 g|≤(pairBound7 : ℝ) := by
  have hlo := pairPlus7_nonneg g hg hmax
  have hhi := pairMinus7_nonneg g hg hmax
  exact abs_le.mpr ⟨by linarith,by linarith⟩

def pairPoly8 : Fin 8 → ℚ := ![0,0,0,0,(-9/16),(3/8),(-83/128),(-95/256)]
def pairBound8 : ℚ := (27231/512000000)

def pairPlus8Weights0 : Fin 8 → ℚ := ![(27231/512000000),(190617/512000000),(571851/512000000),(190617/102400000),(184857/102400000),(487371/512000000),(4309/20480000),0]

theorem pairPlus8Weights0_nonneg : ∀ i,0≤pairPlus8Weights0 i := by
  decide +kernel

theorem pairPlus8Identity0 (x : ℝ) :
    (pairBound8 : ℝ)+evalCoeff pairPoly8 x=bernsteinValue pairPlus8Weights0
      ((x-(0 : ℚ))/(((1/10) : ℚ)-(0 : ℚ))) := by
  norm_num [evalCoeff,bernsteinValue,pairPlus8Weights0,pairBound8,pairPoly8,Fin.sum_univ_succ]
  ring

theorem pairPlus8_nonneg (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    0≤(pairBound8 : ℝ)+evalCoeff pairPoly8 g := by
  exact interval_nonneg (fun x => (pairBound8 : ℝ)+evalCoeff pairPoly8 x) 0 (1/10)
    (by norm_num) pairPlus8Weights0 pairPlus8Weights0_nonneg
    pairPlus8Identity0 g (by simpa using hg) (by simpa using hmax)

def pairMinus8Weights0 : Fin 8 → ℚ := ![(27231/512000000),(190617/512000000),(571851/512000000),(190617/102400000),(196377/102400000),(656331/512000000),(273509/512000000),(27231/256000000)]

theorem pairMinus8Weights0_nonneg : ∀ i,0≤pairMinus8Weights0 i := by
  decide +kernel

theorem pairMinus8Identity0 (x : ℝ) :
    (pairBound8 : ℝ)-evalCoeff pairPoly8 x=bernsteinValue pairMinus8Weights0
      ((x-(0 : ℚ))/(((1/10) : ℚ)-(0 : ℚ))) := by
  norm_num [evalCoeff,bernsteinValue,pairMinus8Weights0,pairBound8,pairPoly8,Fin.sum_univ_succ]
  ring

theorem pairMinus8_nonneg (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    0≤(pairBound8 : ℝ)-evalCoeff pairPoly8 g := by
  exact interval_nonneg (fun x => (pairBound8 : ℝ)-evalCoeff pairPoly8 x) 0 (1/10)
    (by norm_num) pairMinus8Weights0 pairMinus8Weights0_nonneg
    pairMinus8Identity0 g (by simpa using hg) (by simpa using hmax)

theorem pair_bound8 (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    |evalCoeff pairPoly8 g|≤(pairBound8 : ℝ) := by
  have hlo := pairPlus8_nonneg g hg hmax
  have hhi := pairMinus8_nonneg g hg hmax
  exact abs_le.mpr ⟨by linarith,by linarith⟩

def pairPoly9 : Fin 8 → ℚ := ![0,0,0,0,(9/16),(-13/32),(-3/128),(83/2048)]
def pairBound9 : ℚ := (1068403/20480000000)

def pairPlus9Weights0 : Fin 8 → ℚ := ![(1068403/20480000000),(7478821/20480000000),(22436463/20480000000),(7478821/4096000000),(7709221/4096000000),(25809263/20480000000),(10767941/20480000000),(1068403/10240000000)]

theorem pairPlus9Weights0_nonneg : ∀ i,0≤pairPlus9Weights0 i := by
  decide +kernel

theorem pairPlus9Identity0 (x : ℝ) :
    (pairBound9 : ℝ)+evalCoeff pairPoly9 x=bernsteinValue pairPlus9Weights0
      ((x-(0 : ℚ))/(((1/10) : ℚ)-(0 : ℚ))) := by
  norm_num [evalCoeff,bernsteinValue,pairPlus9Weights0,pairBound9,pairPoly9,Fin.sum_univ_succ]
  ring

theorem pairPlus9_nonneg (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    0≤(pairBound9 : ℝ)+evalCoeff pairPoly9 g := by
  exact interval_nonneg (fun x => (pairBound9 : ℝ)+evalCoeff pairPoly9 x) 0 (1/10)
    (by norm_num) pairPlus9Weights0 pairPlus9Weights0_nonneg
    pairPlus9Identity0 g (by simpa using hg) (by simpa using hmax)

def pairMinus9Weights0 : Fin 8 → ℚ := ![(1068403/20480000000),(7478821/20480000000),(22436463/20480000000),(7478821/4096000000),(7248421/4096000000),(19063663/20480000000),(4189701/20480000000),0]

theorem pairMinus9Weights0_nonneg : ∀ i,0≤pairMinus9Weights0 i := by
  decide +kernel

theorem pairMinus9Identity0 (x : ℝ) :
    (pairBound9 : ℝ)-evalCoeff pairPoly9 x=bernsteinValue pairMinus9Weights0
      ((x-(0 : ℚ))/(((1/10) : ℚ)-(0 : ℚ))) := by
  norm_num [evalCoeff,bernsteinValue,pairMinus9Weights0,pairBound9,pairPoly9,Fin.sum_univ_succ]
  ring

theorem pairMinus9_nonneg (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    0≤(pairBound9 : ℝ)-evalCoeff pairPoly9 g := by
  exact interval_nonneg (fun x => (pairBound9 : ℝ)-evalCoeff pairPoly9 x) 0 (1/10)
    (by norm_num) pairMinus9Weights0 pairMinus9Weights0_nonneg
    pairMinus9Identity0 g (by simpa using hg) (by simpa using hmax)

theorem pair_bound9 (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    |evalCoeff pairPoly9 g|≤(pairBound9 : ℝ) := by
  have hlo := pairPlus9_nonneg g hg hmax
  have hhi := pairMinus9_nonneg g hg hmax
  exact abs_le.mpr ⟨by linarith,by linarith⟩

def pairPoly10 : Fin 8 → ℚ := ![0,0,0,0,(-1/2),(1/8),(-43/64),(-45/128)]
def pairBound10 : ℚ := (12661/256000000)

def pairPlus10Weights0 : Fin 8 → ℚ := ![(12661/256000000),(88627/256000000),(265881/256000000),(88627/51200000),(86067/51200000),(227801/256000000),(10139/51200000),0]

theorem pairPlus10Weights0_nonneg : ∀ i,0≤pairPlus10Weights0 i := by
  decide +kernel

theorem pairPlus10Identity0 (x : ℝ) :
    (pairBound10 : ℝ)+evalCoeff pairPoly10 x=bernsteinValue pairPlus10Weights0
      ((x-(0 : ℚ))/(((1/10) : ℚ)-(0 : ℚ))) := by
  norm_num [evalCoeff,bernsteinValue,pairPlus10Weights0,pairBound10,pairPoly10,Fin.sum_univ_succ]
  ring

theorem pairPlus10_nonneg (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    0≤(pairBound10 : ℝ)+evalCoeff pairPoly10 g := by
  exact interval_nonneg (fun x => (pairBound10 : ℝ)+evalCoeff pairPoly10 x) 0 (1/10)
    (by norm_num) pairPlus10Weights0 pairPlus10Weights0_nonneg
    pairPlus10Identity0 g (by simpa using hg) (by simpa using hmax)

def pairMinus10Weights0 : Fin 8 → ℚ := ![(12661/256000000),(88627/256000000),(265881/256000000),(88627/51200000),(91187/51200000),(303961/256000000),(126559/256000000),(12661/128000000)]

theorem pairMinus10Weights0_nonneg : ∀ i,0≤pairMinus10Weights0 i := by
  decide +kernel

theorem pairMinus10Identity0 (x : ℝ) :
    (pairBound10 : ℝ)-evalCoeff pairPoly10 x=bernsteinValue pairMinus10Weights0
      ((x-(0 : ℚ))/(((1/10) : ℚ)-(0 : ℚ))) := by
  norm_num [evalCoeff,bernsteinValue,pairMinus10Weights0,pairBound10,pairPoly10,Fin.sum_univ_succ]
  ring

theorem pairMinus10_nonneg (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    0≤(pairBound10 : ℝ)-evalCoeff pairPoly10 g := by
  exact interval_nonneg (fun x => (pairBound10 : ℝ)-evalCoeff pairPoly10 x) 0 (1/10)
    (by norm_num) pairMinus10Weights0 pairMinus10Weights0_nonneg
    pairMinus10Identity0 g (by simpa using hg) (by simpa using hmax)

theorem pair_bound10 (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    |evalCoeff pairPoly10 g|≤(pairBound10 : ℝ) := by
  have hlo := pairPlus10_nonneg g hg hmax
  have hhi := pairMinus10_nonneg g hg hmax
  exact abs_le.mpr ⟨by linarith,by linarith⟩

def pairPoly11 : Fin 8 → ℚ := ![0,0,0,0,(9/32),(9/128),(21/128),(93/256)]
def pairBound11 : ℚ := (74313/2560000000)

def pairPlus11Weights0 : Fin 8 → ℚ := ![(74313/2560000000),(520191/2560000000),(1560573/2560000000),(520191/512000000),(534591/512000000),(1778373/2560000000),(740211/2560000000),(74313/1280000000)]

theorem pairPlus11Weights0_nonneg : ∀ i,0≤pairPlus11Weights0 i := by
  decide +kernel

theorem pairPlus11Identity0 (x : ℝ) :
    (pairBound11 : ℝ)+evalCoeff pairPoly11 x=bernsteinValue pairPlus11Weights0
      ((x-(0 : ℚ))/(((1/10) : ℚ)-(0 : ℚ))) := by
  norm_num [evalCoeff,bernsteinValue,pairPlus11Weights0,pairBound11,pairPoly11,Fin.sum_univ_succ]
  ring

theorem pairPlus11_nonneg (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    0≤(pairBound11 : ℝ)+evalCoeff pairPoly11 g := by
  exact interval_nonneg (fun x => (pairBound11 : ℝ)+evalCoeff pairPoly11 x) 0 (1/10)
    (by norm_num) pairPlus11Weights0 pairPlus11Weights0_nonneg
    pairPlus11Identity0 g (by simpa using hg) (by simpa using hmax)

def pairMinus11Weights0 : Fin 8 → ℚ := ![(74313/2560000000),(520191/2560000000),(1560573/2560000000),(520191/512000000),(505791/512000000),(1342773/2560000000),(300171/2560000000),0]

theorem pairMinus11Weights0_nonneg : ∀ i,0≤pairMinus11Weights0 i := by
  decide +kernel

theorem pairMinus11Identity0 (x : ℝ) :
    (pairBound11 : ℝ)-evalCoeff pairPoly11 x=bernsteinValue pairMinus11Weights0
      ((x-(0 : ℚ))/(((1/10) : ℚ)-(0 : ℚ))) := by
  norm_num [evalCoeff,bernsteinValue,pairMinus11Weights0,pairBound11,pairPoly11,Fin.sum_univ_succ]
  ring

theorem pairMinus11_nonneg (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    0≤(pairBound11 : ℝ)-evalCoeff pairPoly11 g := by
  exact interval_nonneg (fun x => (pairBound11 : ℝ)-evalCoeff pairPoly11 x) 0 (1/10)
    (by norm_num) pairMinus11Weights0 pairMinus11Weights0_nonneg
    pairMinus11Identity0 g (by simpa using hg) (by simpa using hmax)

theorem pair_bound11 (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    |evalCoeff pairPoly11 g|≤(pairBound11 : ℝ) := by
  have hlo := pairPlus11_nonneg g hg hmax
  have hhi := pairMinus11_nonneg g hg hmax
  exact abs_le.mpr ⟨by linarith,by linarith⟩

def pairPoly12 : Fin 8 → ℚ := ![0,0,0,0,(-21/16),(-3/8),(-33/32),(-15/32)]
def pairBound12 : ℚ := (8709/64000000)

def pairPlus12Weights0 : Fin 8 → ℚ := ![(8709/64000000),(60963/64000000),(182889/64000000),(60963/12800000),(59283/12800000),(157449/64000000),(35217/64000000),0]

theorem pairPlus12Weights0_nonneg : ∀ i,0≤pairPlus12Weights0 i := by
  decide +kernel

theorem pairPlus12Identity0 (x : ℝ) :
    (pairBound12 : ℝ)+evalCoeff pairPoly12 x=bernsteinValue pairPlus12Weights0
      ((x-(0 : ℚ))/(((1/10) : ℚ)-(0 : ℚ))) := by
  norm_num [evalCoeff,bernsteinValue,pairPlus12Weights0,pairBound12,pairPoly12,Fin.sum_univ_succ]
  ring

theorem pairPlus12_nonneg (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    0≤(pairBound12 : ℝ)+evalCoeff pairPoly12 g := by
  exact interval_nonneg (fun x => (pairBound12 : ℝ)+evalCoeff pairPoly12 x) 0 (1/10)
    (by norm_num) pairPlus12Weights0 pairPlus12Weights0_nonneg
    pairPlus12Identity0 g (by simpa using hg) (by simpa using hmax)

def pairMinus12Weights0 : Fin 8 → ℚ := ![(8709/64000000),(60963/64000000),(182889/64000000),(60963/12800000),(62643/12800000),(208329/64000000),(86709/64000000),(8709/32000000)]

theorem pairMinus12Weights0_nonneg : ∀ i,0≤pairMinus12Weights0 i := by
  decide +kernel

theorem pairMinus12Identity0 (x : ℝ) :
    (pairBound12 : ℝ)-evalCoeff pairPoly12 x=bernsteinValue pairMinus12Weights0
      ((x-(0 : ℚ))/(((1/10) : ℚ)-(0 : ℚ))) := by
  norm_num [evalCoeff,bernsteinValue,pairMinus12Weights0,pairBound12,pairPoly12,Fin.sum_univ_succ]
  ring

theorem pairMinus12_nonneg (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    0≤(pairBound12 : ℝ)-evalCoeff pairPoly12 g := by
  exact interval_nonneg (fun x => (pairBound12 : ℝ)-evalCoeff pairPoly12 x) 0 (1/10)
    (by norm_num) pairMinus12Weights0 pairMinus12Weights0_nonneg
    pairMinus12Identity0 g (by simpa using hg) (by simpa using hmax)

theorem pair_bound12 (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    |evalCoeff pairPoly12 g|≤(pairBound12 : ℝ) := by
  have hlo := pairPlus12_nonneg g hg hmax
  have hhi := pairMinus12_nonneg g hg hmax
  exact abs_le.mpr ⟨by linarith,by linarith⟩

def pairPoly13 : Fin 8 → ℚ := ![0,0,0,0,(3/32),(3/16),(41/256),(67/128)]
def pairBound13 : ℚ := (917/80000000)

def pairPlus13Weights0 : Fin 8 → ℚ := ![(917/80000000),(6419/80000000),(19257/80000000),(6419/16000000),(6569/16000000),(21657/80000000),(143709/1280000000),(917/40000000)]

theorem pairPlus13Weights0_nonneg : ∀ i,0≤pairPlus13Weights0 i := by
  decide +kernel

theorem pairPlus13Identity0 (x : ℝ) :
    (pairBound13 : ℝ)+evalCoeff pairPoly13 x=bernsteinValue pairPlus13Weights0
      ((x-(0 : ℚ))/(((1/10) : ℚ)-(0 : ℚ))) := by
  norm_num [evalCoeff,bernsteinValue,pairPlus13Weights0,pairBound13,pairPoly13,Fin.sum_univ_succ]
  ring

theorem pairPlus13_nonneg (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    0≤(pairBound13 : ℝ)+evalCoeff pairPoly13 g := by
  exact interval_nonneg (fun x => (pairBound13 : ℝ)+evalCoeff pairPoly13 x) 0 (1/10)
    (by norm_num) pairPlus13Weights0 pairPlus13Weights0_nonneg
    pairPlus13Identity0 g (by simpa using hg) (by simpa using hmax)

def pairMinus13Weights0 : Fin 8 → ℚ := ![(917/80000000),(6419/80000000),(19257/80000000),(6419/16000000),(6269/16000000),(16857/80000000),(61699/1280000000),0]

theorem pairMinus13Weights0_nonneg : ∀ i,0≤pairMinus13Weights0 i := by
  decide +kernel

theorem pairMinus13Identity0 (x : ℝ) :
    (pairBound13 : ℝ)-evalCoeff pairPoly13 x=bernsteinValue pairMinus13Weights0
      ((x-(0 : ℚ))/(((1/10) : ℚ)-(0 : ℚ))) := by
  norm_num [evalCoeff,bernsteinValue,pairMinus13Weights0,pairBound13,pairPoly13,Fin.sum_univ_succ]
  ring

theorem pairMinus13_nonneg (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    0≤(pairBound13 : ℝ)-evalCoeff pairPoly13 g := by
  exact interval_nonneg (fun x => (pairBound13 : ℝ)-evalCoeff pairPoly13 x) 0 (1/10)
    (by norm_num) pairMinus13Weights0 pairMinus13Weights0_nonneg
    pairMinus13Identity0 g (by simpa using hg) (by simpa using hmax)

theorem pair_bound13 (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    |evalCoeff pairPoly13 g|≤(pairBound13 : ℝ) := by
  have hlo := pairPlus13_nonneg g hg hmax
  have hhi := pairMinus13_nonneg g hg hmax
  exact abs_le.mpr ⟨by linarith,by linarith⟩

def pairPoly14 : Fin 8 → ℚ := ![0,0,0,0,(-7/16),(-1/8),(-89/128),(-85/256)]
def pairBound14 : ℚ := (23413/512000000)

def pairPlus14Weights0 : Fin 8 → ℚ := ![(23413/512000000),(163891/512000000),(491673/512000000),(163891/102400000),(159411/102400000),(423833/512000000),(19011/102400000),0]

theorem pairPlus14Weights0_nonneg : ∀ i,0≤pairPlus14Weights0 i := by
  decide +kernel

theorem pairPlus14Identity0 (x : ℝ) :
    (pairBound14 : ℝ)+evalCoeff pairPoly14 x=bernsteinValue pairPlus14Weights0
      ((x-(0 : ℚ))/(((1/10) : ℚ)-(0 : ℚ))) := by
  norm_num [evalCoeff,bernsteinValue,pairPlus14Weights0,pairBound14,pairPoly14,Fin.sum_univ_succ]
  ring

theorem pairPlus14_nonneg (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    0≤(pairBound14 : ℝ)+evalCoeff pairPoly14 g := by
  exact interval_nonneg (fun x => (pairBound14 : ℝ)+evalCoeff pairPoly14 x) 0 (1/10)
    (by norm_num) pairPlus14Weights0 pairPlus14Weights0_nonneg
    pairPlus14Identity0 g (by simpa using hg) (by simpa using hmax)

def pairMinus14Weights0 : Fin 8 → ℚ := ![(23413/512000000),(163891/512000000),(491673/512000000),(163891/102400000),(168371/102400000),(559513/512000000),(232727/512000000),(23413/256000000)]

theorem pairMinus14Weights0_nonneg : ∀ i,0≤pairMinus14Weights0 i := by
  decide +kernel

theorem pairMinus14Identity0 (x : ℝ) :
    (pairBound14 : ℝ)-evalCoeff pairPoly14 x=bernsteinValue pairMinus14Weights0
      ((x-(0 : ℚ))/(((1/10) : ℚ)-(0 : ℚ))) := by
  norm_num [evalCoeff,bernsteinValue,pairMinus14Weights0,pairBound14,pairPoly14,Fin.sum_univ_succ]
  ring

theorem pairMinus14_nonneg (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    0≤(pairBound14 : ℝ)-evalCoeff pairPoly14 g := by
  exact interval_nonneg (fun x => (pairBound14 : ℝ)-evalCoeff pairPoly14 x) 0 (1/10)
    (by norm_num) pairMinus14Weights0 pairMinus14Weights0_nonneg
    pairMinus14Identity0 g (by simpa using hg) (by simpa using hmax)

theorem pair_bound14 (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    |evalCoeff pairPoly14 g|≤(pairBound14 : ℝ) := by
  have hlo := pairPlus14_nonneg g hg hmax
  have hhi := pairMinus14_nonneg g hg hmax
  exact abs_le.mpr ⟨by linarith,by linarith⟩

def pairPoly15 : Fin 8 → ℚ := ![0,0,0,0,0,(35/64),(45/128),(1405/2048)]
def pairBound15 : ℚ := (24121/4096000000)

def pairPlus15Weights0 : Fin 8 → ℚ := ![(24121/4096000000),(168847/4096000000),(506541/4096000000),(168847/819200000),(168847/819200000),(528941/4096000000),(215087/4096000000),(24121/2048000000)]

theorem pairPlus15Weights0_nonneg : ∀ i,0≤pairPlus15Weights0 i := by
  decide +kernel

theorem pairPlus15Identity0 (x : ℝ) :
    (pairBound15 : ℝ)+evalCoeff pairPoly15 x=bernsteinValue pairPlus15Weights0
      ((x-(0 : ℚ))/(((1/10) : ℚ)-(0 : ℚ))) := by
  norm_num [evalCoeff,bernsteinValue,pairPlus15Weights0,pairBound15,pairPoly15,Fin.sum_univ_succ]
  ring

theorem pairPlus15_nonneg (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    0≤(pairBound15 : ℝ)+evalCoeff pairPoly15 g := by
  exact interval_nonneg (fun x => (pairBound15 : ℝ)+evalCoeff pairPoly15 x) 0 (1/10)
    (by norm_num) pairPlus15Weights0 pairPlus15Weights0_nonneg
    pairPlus15Identity0 g (by simpa using hg) (by simpa using hmax)

def pairMinus15Weights0 : Fin 8 → ℚ := ![(24121/4096000000),(168847/4096000000),(506541/4096000000),(168847/819200000),(168847/819200000),(484141/4096000000),(122607/4096000000),0]

theorem pairMinus15Weights0_nonneg : ∀ i,0≤pairMinus15Weights0 i := by
  decide +kernel

theorem pairMinus15Identity0 (x : ℝ) :
    (pairBound15 : ℝ)-evalCoeff pairPoly15 x=bernsteinValue pairMinus15Weights0
      ((x-(0 : ℚ))/(((1/10) : ℚ)-(0 : ℚ))) := by
  norm_num [evalCoeff,bernsteinValue,pairMinus15Weights0,pairBound15,pairPoly15,Fin.sum_univ_succ]
  ring

theorem pairMinus15_nonneg (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    0≤(pairBound15 : ℝ)-evalCoeff pairPoly15 g := by
  exact interval_nonneg (fun x => (pairBound15 : ℝ)-evalCoeff pairPoly15 x) 0 (1/10)
    (by norm_num) pairMinus15Weights0 pairMinus15Weights0_nonneg
    pairMinus15Identity0 g (by simpa using hg) (by simpa using hmax)

theorem pair_bound15 (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    |evalCoeff pairPoly15 g|≤(pairBound15 : ℝ) := by
  have hlo := pairPlus15_nonneg g hg hmax
  have hhi := pairMinus15_nonneg g hg hmax
  exact abs_le.mpr ⟨by linarith,by linarith⟩

def pairPoly16 : Fin 8 → ℚ := ![0,0,0,0,(-7/32),(-1/16),(-31/64),(-15/64)]
def pairBound16 : ℚ := (589/25600000)

def pairPlus16Weights0 : Fin 8 → ℚ := ![(589/25600000),(4123/25600000),(12369/25600000),(4123/5120000),(4011/5120000),(10673/25600000),(11993/128000000),0]

theorem pairPlus16Weights0_nonneg : ∀ i,0≤pairPlus16Weights0 i := by
  decide +kernel

theorem pairPlus16Identity0 (x : ℝ) :
    (pairBound16 : ℝ)+evalCoeff pairPoly16 x=bernsteinValue pairPlus16Weights0
      ((x-(0 : ℚ))/(((1/10) : ℚ)-(0 : ℚ))) := by
  norm_num [evalCoeff,bernsteinValue,pairPlus16Weights0,pairBound16,pairPoly16,Fin.sum_univ_succ]
  ring

theorem pairPlus16_nonneg (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    0≤(pairBound16 : ℝ)+evalCoeff pairPoly16 g := by
  exact interval_nonneg (fun x => (pairBound16 : ℝ)+evalCoeff pairPoly16 x) 0 (1/10)
    (by norm_num) pairPlus16Weights0 pairPlus16Weights0_nonneg
    pairPlus16Identity0 g (by simpa using hg) (by simpa using hmax)

def pairMinus16Weights0 : Fin 8 → ℚ := ![(589/25600000),(4123/25600000),(12369/25600000),(4123/5120000),(847/1024000),(2813/5120000),(29237/128000000),(589/12800000)]

theorem pairMinus16Weights0_nonneg : ∀ i,0≤pairMinus16Weights0 i := by
  decide +kernel

theorem pairMinus16Identity0 (x : ℝ) :
    (pairBound16 : ℝ)-evalCoeff pairPoly16 x=bernsteinValue pairMinus16Weights0
      ((x-(0 : ℚ))/(((1/10) : ℚ)-(0 : ℚ))) := by
  norm_num [evalCoeff,bernsteinValue,pairMinus16Weights0,pairBound16,pairPoly16,Fin.sum_univ_succ]
  ring

theorem pairMinus16_nonneg (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    0≤(pairBound16 : ℝ)-evalCoeff pairPoly16 g := by
  exact interval_nonneg (fun x => (pairBound16 : ℝ)-evalCoeff pairPoly16 x) 0 (1/10)
    (by norm_num) pairMinus16Weights0 pairMinus16Weights0_nonneg
    pairMinus16Identity0 g (by simpa using hg) (by simpa using hmax)

theorem pair_bound16 (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    |evalCoeff pairPoly16 g|≤(pairBound16 : ℝ) := by
  have hlo := pairPlus16_nonneg g hg hmax
  have hhi := pairMinus16_nonneg g hg hmax
  exact abs_le.mpr ⟨by linarith,by linarith⟩

def pairPoly17 : Fin 8 → ℚ := ![0,0,0,0,0,(35/128),(45/256),(1315/2048)]
def pairBound17 : ℚ := (12183/4096000000)

def pairPlus17Weights0 : Fin 8 → ℚ := ![(12183/4096000000),(85281/4096000000),(255843/4096000000),(85281/819200000),(85281/819200000),(267043/4096000000),(108401/4096000000),(12183/2048000000)]

theorem pairPlus17Weights0_nonneg : ∀ i,0≤pairPlus17Weights0 i := by
  decide +kernel

theorem pairPlus17Identity0 (x : ℝ) :
    (pairBound17 : ℝ)+evalCoeff pairPoly17 x=bernsteinValue pairPlus17Weights0
      ((x-(0 : ℚ))/(((1/10) : ℚ)-(0 : ℚ))) := by
  norm_num [evalCoeff,bernsteinValue,pairPlus17Weights0,pairBound17,pairPoly17,Fin.sum_univ_succ]
  ring

theorem pairPlus17_nonneg (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    0≤(pairBound17 : ℝ)+evalCoeff pairPoly17 g := by
  exact interval_nonneg (fun x => (pairBound17 : ℝ)+evalCoeff pairPoly17 x) 0 (1/10)
    (by norm_num) pairPlus17Weights0 pairPlus17Weights0_nonneg
    pairPlus17Identity0 g (by simpa using hg) (by simpa using hmax)

def pairMinus17Weights0 : Fin 8 → ℚ := ![(12183/4096000000),(85281/4096000000),(255843/4096000000),(85281/819200000),(85281/819200000),(244643/4096000000),(62161/4096000000),0]

theorem pairMinus17Weights0_nonneg : ∀ i,0≤pairMinus17Weights0 i := by
  decide +kernel

theorem pairMinus17Identity0 (x : ℝ) :
    (pairBound17 : ℝ)-evalCoeff pairPoly17 x=bernsteinValue pairMinus17Weights0
      ((x-(0 : ℚ))/(((1/10) : ℚ)-(0 : ℚ))) := by
  norm_num [evalCoeff,bernsteinValue,pairMinus17Weights0,pairBound17,pairPoly17,Fin.sum_univ_succ]
  ring

theorem pairMinus17_nonneg (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    0≤(pairBound17 : ℝ)-evalCoeff pairPoly17 g := by
  exact interval_nonneg (fun x => (pairBound17 : ℝ)-evalCoeff pairPoly17 x) 0 (1/10)
    (by norm_num) pairMinus17Weights0 pairMinus17Weights0_nonneg
    pairMinus17Identity0 g (by simpa using hg) (by simpa using hmax)

theorem pair_bound17 (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    |evalCoeff pairPoly17 g|≤(pairBound17 : ℝ) := by
  have hlo := pairPlus17_nonneg g hg hmax
  have hhi := pairMinus17_nonneg g hg hmax
  exact abs_le.mpr ⟨by linarith,by linarith⟩

def pairPoly18 : Fin 8 → ℚ := ![0,0,0,0,0,0,(-75/128),(-75/256)]
def pairBound18 : ℚ := (63/102400000)

def pairPlus18Weights0 : Fin 8 → ℚ := ![(63/102400000),(441/102400000),(1323/102400000),(441/20480000),(441/20480000),(1323/102400000),(381/102400000),0]

theorem pairPlus18Weights0_nonneg : ∀ i,0≤pairPlus18Weights0 i := by
  decide +kernel

theorem pairPlus18Identity0 (x : ℝ) :
    (pairBound18 : ℝ)+evalCoeff pairPoly18 x=bernsteinValue pairPlus18Weights0
      ((x-(0 : ℚ))/(((1/10) : ℚ)-(0 : ℚ))) := by
  norm_num [evalCoeff,bernsteinValue,pairPlus18Weights0,pairBound18,pairPoly18,Fin.sum_univ_succ]
  ring

theorem pairPlus18_nonneg (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    0≤(pairBound18 : ℝ)+evalCoeff pairPoly18 g := by
  exact interval_nonneg (fun x => (pairBound18 : ℝ)+evalCoeff pairPoly18 x) 0 (1/10)
    (by norm_num) pairPlus18Weights0 pairPlus18Weights0_nonneg
    pairPlus18Identity0 g (by simpa using hg) (by simpa using hmax)

def pairMinus18Weights0 : Fin 8 → ℚ := ![(63/102400000),(441/102400000),(1323/102400000),(441/20480000),(441/20480000),(1323/102400000),(501/102400000),(63/51200000)]

theorem pairMinus18Weights0_nonneg : ∀ i,0≤pairMinus18Weights0 i := by
  decide +kernel

theorem pairMinus18Identity0 (x : ℝ) :
    (pairBound18 : ℝ)-evalCoeff pairPoly18 x=bernsteinValue pairMinus18Weights0
      ((x-(0 : ℚ))/(((1/10) : ℚ)-(0 : ℚ))) := by
  norm_num [evalCoeff,bernsteinValue,pairMinus18Weights0,pairBound18,pairPoly18,Fin.sum_univ_succ]
  ring

theorem pairMinus18_nonneg (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    0≤(pairBound18 : ℝ)-evalCoeff pairPoly18 g := by
  exact interval_nonneg (fun x => (pairBound18 : ℝ)-evalCoeff pairPoly18 x) 0 (1/10)
    (by norm_num) pairMinus18Weights0 pairMinus18Weights0_nonneg
    pairMinus18Identity0 g (by simpa using hg) (by simpa using hmax)

theorem pair_bound18 (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    |evalCoeff pairPoly18 g|≤(pairBound18 : ℝ) := by
  have hlo := pairPlus18_nonneg g hg hmax
  have hhi := pairMinus18_nonneg g hg hmax
  exact abs_le.mpr ⟨by linarith,by linarith⟩

def pairPoly19 : Fin 8 → ℚ := ![0,0,0,0,(-13/64),(25/128),(11/32),(2527/4096)]
def pairBound19 : ℚ := (735393/40960000000)

def pairPlus19Weights0 : Fin 8 → ℚ := ![(735393/40960000000),(5147751/40960000000),(15443253/40960000000),(5147751/8192000000),(4981351/8192000000),(13027253/40960000000),(2825831/40960000000),0]

theorem pairPlus19Weights0_nonneg : ∀ i,0≤pairPlus19Weights0 i := by
  decide +kernel

theorem pairPlus19Identity0 (x : ℝ) :
    (pairBound19 : ℝ)+evalCoeff pairPoly19 x=bernsteinValue pairPlus19Weights0
      ((x-(0 : ℚ))/(((1/10) : ℚ)-(0 : ℚ))) := by
  norm_num [evalCoeff,bernsteinValue,pairPlus19Weights0,pairBound19,pairPoly19,Fin.sum_univ_succ]
  ring

theorem pairPlus19_nonneg (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    0≤(pairBound19 : ℝ)+evalCoeff pairPoly19 g := by
  exact interval_nonneg (fun x => (pairBound19 : ℝ)+evalCoeff pairPoly19 x) 0 (1/10)
    (by norm_num) pairPlus19Weights0 pairPlus19Weights0_nonneg
    pairPlus19Identity0 g (by simpa using hg) (by simpa using hmax)

def pairMinus19Weights0 : Fin 8 → ℚ := ![(735393/40960000000),(5147751/40960000000),(15443253/40960000000),(5147751/8192000000),(5314151/8192000000),(17859253/40960000000),(7469671/40960000000),(735393/20480000000)]

theorem pairMinus19Weights0_nonneg : ∀ i,0≤pairMinus19Weights0 i := by
  decide +kernel

theorem pairMinus19Identity0 (x : ℝ) :
    (pairBound19 : ℝ)-evalCoeff pairPoly19 x=bernsteinValue pairMinus19Weights0
      ((x-(0 : ℚ))/(((1/10) : ℚ)-(0 : ℚ))) := by
  norm_num [evalCoeff,bernsteinValue,pairMinus19Weights0,pairBound19,pairPoly19,Fin.sum_univ_succ]
  ring

theorem pairMinus19_nonneg (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    0≤(pairBound19 : ℝ)-evalCoeff pairPoly19 g := by
  exact interval_nonneg (fun x => (pairBound19 : ℝ)-evalCoeff pairPoly19 x) 0 (1/10)
    (by norm_num) pairMinus19Weights0 pairMinus19Weights0_nonneg
    pairMinus19Identity0 g (by simpa using hg) (by simpa using hmax)

theorem pair_bound19 (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    |evalCoeff pairPoly19 g|≤(pairBound19 : ℝ) := by
  have hlo := pairPlus19_nonneg g hg hmax
  have hhi := pairMinus19_nonneg g hg hmax
  exact abs_le.mpr ⟨by linarith,by linarith⟩

def pairPoly20 : Fin 8 → ℚ := ![0,0,0,0,(-1/2),(1/8),(-117/256),(-125/512)]
def pairBound20 : ℚ := (50413/1024000000)

def pairPlus20Weights0 : Fin 8 → ℚ := ![(50413/1024000000),(352891/1024000000),(1058673/1024000000),(352891/204800000),(342651/204800000),(906353/1024000000),(201383/1024000000),0]

theorem pairPlus20Weights0_nonneg : ∀ i,0≤pairPlus20Weights0 i := by
  decide +kernel

theorem pairPlus20Identity0 (x : ℝ) :
    (pairBound20 : ℝ)+evalCoeff pairPoly20 x=bernsteinValue pairPlus20Weights0
      ((x-(0 : ℚ))/(((1/10) : ℚ)-(0 : ℚ))) := by
  norm_num [evalCoeff,bernsteinValue,pairPlus20Weights0,pairBound20,pairPoly20,Fin.sum_univ_succ]
  ring

theorem pairPlus20_nonneg (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    0≤(pairBound20 : ℝ)+evalCoeff pairPoly20 g := by
  exact interval_nonneg (fun x => (pairBound20 : ℝ)+evalCoeff pairPoly20 x) 0 (1/10)
    (by norm_num) pairPlus20Weights0 pairPlus20Weights0_nonneg
    pairPlus20Identity0 g (by simpa using hg) (by simpa using hmax)

def pairMinus20Weights0 : Fin 8 → ℚ := ![(50413/1024000000),(352891/1024000000),(1058673/1024000000),(352891/204800000),(363131/204800000),(1210993/1024000000),(504399/1024000000),(50413/512000000)]

theorem pairMinus20Weights0_nonneg : ∀ i,0≤pairMinus20Weights0 i := by
  decide +kernel

theorem pairMinus20Identity0 (x : ℝ) :
    (pairBound20 : ℝ)-evalCoeff pairPoly20 x=bernsteinValue pairMinus20Weights0
      ((x-(0 : ℚ))/(((1/10) : ℚ)-(0 : ℚ))) := by
  norm_num [evalCoeff,bernsteinValue,pairMinus20Weights0,pairBound20,pairPoly20,Fin.sum_univ_succ]
  ring

theorem pairMinus20_nonneg (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    0≤(pairBound20 : ℝ)-evalCoeff pairPoly20 g := by
  exact interval_nonneg (fun x => (pairBound20 : ℝ)-evalCoeff pairPoly20 x) 0 (1/10)
    (by norm_num) pairMinus20Weights0 pairMinus20Weights0_nonneg
    pairMinus20Identity0 g (by simpa using hg) (by simpa using hmax)

theorem pair_bound20 (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    |evalCoeff pairPoly20 g|≤(pairBound20 : ℝ) := by
  have hlo := pairPlus20_nonneg g hg hmax
  have hhi := pairMinus20_nonneg g hg hmax
  exact abs_le.mpr ⟨by linarith,by linarith⟩

def pairPoly21 : Fin 8 → ℚ := ![0,0,0,0,(3/32),(3/16),(41/256),(1469/4096)]
def pairBound21 : ℚ := (468829/40960000000)

def pairPlus21Weights0 : Fin 8 → ℚ := ![(468829/40960000000),(3281803/40960000000),(9845409/40960000000),(3281803/8192000000),(3358603/8192000000),(11074209/40960000000),(4593963/40960000000),(468829/20480000000)]

theorem pairPlus21Weights0_nonneg : ∀ i,0≤pairPlus21Weights0 i := by
  decide +kernel

theorem pairPlus21Identity0 (x : ℝ) :
    (pairBound21 : ℝ)+evalCoeff pairPoly21 x=bernsteinValue pairPlus21Weights0
      ((x-(0 : ℚ))/(((1/10) : ℚ)-(0 : ℚ))) := by
  norm_num [evalCoeff,bernsteinValue,pairPlus21Weights0,pairBound21,pairPoly21,Fin.sum_univ_succ]
  ring

theorem pairPlus21_nonneg (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    0≤(pairBound21 : ℝ)+evalCoeff pairPoly21 g := by
  exact interval_nonneg (fun x => (pairBound21 : ℝ)+evalCoeff pairPoly21 x) 0 (1/10)
    (by norm_num) pairPlus21Weights0 pairPlus21Weights0_nonneg
    pairPlus21Identity0 g (by simpa using hg) (by simpa using hmax)

def pairMinus21Weights0 : Fin 8 → ℚ := ![(468829/40960000000),(3281803/40960000000),(9845409/40960000000),(3281803/8192000000),(3205003/8192000000),(8616609/40960000000),(1969643/40960000000),0]

theorem pairMinus21Weights0_nonneg : ∀ i,0≤pairMinus21Weights0 i := by
  decide +kernel

theorem pairMinus21Identity0 (x : ℝ) :
    (pairBound21 : ℝ)-evalCoeff pairPoly21 x=bernsteinValue pairMinus21Weights0
      ((x-(0 : ℚ))/(((1/10) : ℚ)-(0 : ℚ))) := by
  norm_num [evalCoeff,bernsteinValue,pairMinus21Weights0,pairBound21,pairPoly21,Fin.sum_univ_succ]
  ring

theorem pairMinus21_nonneg (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    0≤(pairBound21 : ℝ)-evalCoeff pairPoly21 g := by
  exact interval_nonneg (fun x => (pairBound21 : ℝ)-evalCoeff pairPoly21 x) 0 (1/10)
    (by norm_num) pairMinus21Weights0 pairMinus21Weights0_nonneg
    pairMinus21Identity0 g (by simpa using hg) (by simpa using hmax)

theorem pair_bound21 (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    |evalCoeff pairPoly21 g|≤(pairBound21 : ℝ) := by
  have hlo := pairPlus21_nonneg g hg hmax
  have hhi := pairMinus21_nonneg g hg hmax
  exact abs_le.mpr ⟨by linarith,by linarith⟩

def pairPoly22 : Fin 8 → ℚ := ![0,0,0,0,(-1/8),(1/2),(-39/128),(-55/256)]
def pairBound22 : ℚ := (4007/512000000)

def pairPlus22Weights0 : Fin 8 → ℚ := ![(4007/512000000),(28049/512000000),(84147/512000000),(28049/102400000),(26769/102400000),(67507/512000000),(13813/512000000),0]

theorem pairPlus22Weights0_nonneg : ∀ i,0≤pairPlus22Weights0 i := by
  decide +kernel

theorem pairPlus22Identity0 (x : ℝ) :
    (pairBound22 : ℝ)+evalCoeff pairPoly22 x=bernsteinValue pairPlus22Weights0
      ((x-(0 : ℚ))/(((1/10) : ℚ)-(0 : ℚ))) := by
  norm_num [evalCoeff,bernsteinValue,pairPlus22Weights0,pairBound22,pairPoly22,Fin.sum_univ_succ]
  ring

theorem pairPlus22_nonneg (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    0≤(pairBound22 : ℝ)+evalCoeff pairPoly22 g := by
  exact interval_nonneg (fun x => (pairBound22 : ℝ)+evalCoeff pairPoly22 x) 0 (1/10)
    (by norm_num) pairPlus22Weights0 pairPlus22Weights0_nonneg
    pairPlus22Identity0 g (by simpa using hg) (by simpa using hmax)

def pairMinus22Weights0 : Fin 8 → ℚ := ![(4007/512000000),(28049/512000000),(84147/512000000),(28049/102400000),(29329/102400000),(100787/512000000),(8457/102400000),(4007/256000000)]

theorem pairMinus22Weights0_nonneg : ∀ i,0≤pairMinus22Weights0 i := by
  decide +kernel

theorem pairMinus22Identity0 (x : ℝ) :
    (pairBound22 : ℝ)-evalCoeff pairPoly22 x=bernsteinValue pairMinus22Weights0
      ((x-(0 : ℚ))/(((1/10) : ℚ)-(0 : ℚ))) := by
  norm_num [evalCoeff,bernsteinValue,pairMinus22Weights0,pairBound22,pairPoly22,Fin.sum_univ_succ]
  ring

theorem pairMinus22_nonneg (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    0≤(pairBound22 : ℝ)-evalCoeff pairPoly22 g := by
  exact interval_nonneg (fun x => (pairBound22 : ℝ)-evalCoeff pairPoly22 x) 0 (1/10)
    (by norm_num) pairMinus22Weights0 pairMinus22Weights0_nonneg
    pairMinus22Identity0 g (by simpa using hg) (by simpa using hmax)

theorem pair_bound22 (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    |evalCoeff pairPoly22 g|≤(pairBound22 : ℝ) := by
  have hlo := pairPlus22_nonneg g hg hmax
  have hhi := pairMinus22_nonneg g hg hmax
  exact abs_le.mpr ⟨by linarith,by linarith⟩

def pairPoly23 : Fin 8 → ℚ := ![0,0,0,0,(9/32),(-13/64),(-3/256),(683/4096)]
def pairBound23 : ℚ := (1069003/40960000000)

def pairPlus23Weights0 : Fin 8 → ℚ := ![(1069003/40960000000),(7483021/40960000000),(22449063/40960000000),(7483021/8192000000),(7713421/8192000000),(25821863/40960000000),(10772141/40960000000),(1069003/20480000000)]

theorem pairPlus23Weights0_nonneg : ∀ i,0≤pairPlus23Weights0 i := by
  decide +kernel

theorem pairPlus23Identity0 (x : ℝ) :
    (pairBound23 : ℝ)+evalCoeff pairPoly23 x=bernsteinValue pairPlus23Weights0
      ((x-(0 : ℚ))/(((1/10) : ℚ)-(0 : ℚ))) := by
  norm_num [evalCoeff,bernsteinValue,pairPlus23Weights0,pairBound23,pairPoly23,Fin.sum_univ_succ]
  ring

theorem pairPlus23_nonneg (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    0≤(pairBound23 : ℝ)+evalCoeff pairPoly23 g := by
  exact interval_nonneg (fun x => (pairBound23 : ℝ)+evalCoeff pairPoly23 x) 0 (1/10)
    (by norm_num) pairPlus23Weights0 pairPlus23Weights0_nonneg
    pairPlus23Identity0 g (by simpa using hg) (by simpa using hmax)

def pairMinus23Weights0 : Fin 8 → ℚ := ![(1069003/40960000000),(7483021/40960000000),(22449063/40960000000),(7483021/8192000000),(7252621/8192000000),(19076263/40960000000),(4193901/40960000000),0]

theorem pairMinus23Weights0_nonneg : ∀ i,0≤pairMinus23Weights0 i := by
  decide +kernel

theorem pairMinus23Identity0 (x : ℝ) :
    (pairBound23 : ℝ)-evalCoeff pairPoly23 x=bernsteinValue pairMinus23Weights0
      ((x-(0 : ℚ))/(((1/10) : ℚ)-(0 : ℚ))) := by
  norm_num [evalCoeff,bernsteinValue,pairMinus23Weights0,pairBound23,pairPoly23,Fin.sum_univ_succ]
  ring

theorem pairMinus23_nonneg (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    0≤(pairBound23 : ℝ)-evalCoeff pairPoly23 g := by
  exact interval_nonneg (fun x => (pairBound23 : ℝ)-evalCoeff pairPoly23 x) 0 (1/10)
    (by norm_num) pairMinus23Weights0 pairMinus23Weights0_nonneg
    pairMinus23Identity0 g (by simpa using hg) (by simpa using hmax)

theorem pair_bound23 (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    |evalCoeff pairPoly23 g|≤(pairBound23 : ℝ) := by
  have hlo := pairPlus23_nonneg g hg hmax
  have hhi := pairMinus23_nonneg g hg hmax
  exact abs_le.mpr ⟨by linarith,by linarith⟩

def pairPoly24 : Fin 8 → ℚ := ![0,0,0,0,(-7/16),(-1/8),(-1/2),(-15/64)]
def pairBound24 : ℚ := (5827/128000000)

def pairPlus24Weights0 : Fin 8 → ℚ := ![(5827/128000000),(40789/128000000),(122367/128000000),(40789/25600000),(39669/25600000),(105407/128000000),(4721/25600000),0]

theorem pairPlus24Weights0_nonneg : ∀ i,0≤pairPlus24Weights0 i := by
  decide +kernel

theorem pairPlus24Identity0 (x : ℝ) :
    (pairBound24 : ℝ)+evalCoeff pairPoly24 x=bernsteinValue pairPlus24Weights0
      ((x-(0 : ℚ))/(((1/10) : ℚ)-(0 : ℚ))) := by
  norm_num [evalCoeff,bernsteinValue,pairPlus24Weights0,pairBound24,pairPoly24,Fin.sum_univ_succ]
  ring

theorem pairPlus24_nonneg (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    0≤(pairBound24 : ℝ)+evalCoeff pairPoly24 g := by
  exact interval_nonneg (fun x => (pairBound24 : ℝ)+evalCoeff pairPoly24 x) 0 (1/10)
    (by norm_num) pairPlus24Weights0 pairPlus24Weights0_nonneg
    pairPlus24Identity0 g (by simpa using hg) (by simpa using hmax)

def pairMinus24Weights0 : Fin 8 → ℚ := ![(5827/128000000),(40789/128000000),(122367/128000000),(40789/25600000),(41909/25600000),(139327/128000000),(57973/128000000),(5827/64000000)]

theorem pairMinus24Weights0_nonneg : ∀ i,0≤pairMinus24Weights0 i := by
  decide +kernel

theorem pairMinus24Identity0 (x : ℝ) :
    (pairBound24 : ℝ)-evalCoeff pairPoly24 x=bernsteinValue pairMinus24Weights0
      ((x-(0 : ℚ))/(((1/10) : ℚ)-(0 : ℚ))) := by
  norm_num [evalCoeff,bernsteinValue,pairMinus24Weights0,pairBound24,pairPoly24,Fin.sum_univ_succ]
  ring

theorem pairMinus24_nonneg (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    0≤(pairBound24 : ℝ)-evalCoeff pairPoly24 g := by
  exact interval_nonneg (fun x => (pairBound24 : ℝ)-evalCoeff pairPoly24 x) 0 (1/10)
    (by norm_num) pairMinus24Weights0 pairMinus24Weights0_nonneg
    pairMinus24Identity0 g (by simpa using hg) (by simpa using hmax)

theorem pair_bound24 (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    |evalCoeff pairPoly24 g|≤(pairBound24 : ℝ) := by
  have hlo := pairPlus24_nonneg g hg hmax
  have hhi := pairMinus24_nonneg g hg hmax
  exact abs_le.mpr ⟨by linarith,by linarith⟩

def pairPoly25 : Fin 8 → ℚ := ![0,0,0,0,0,(35/128),(45/256),(1755/4096)]
def pairBound25 : ℚ := (24191/8192000000)

def pairPlus25Weights0 : Fin 8 → ℚ := ![(24191/8192000000),(169337/8192000000),(508011/8192000000),(169337/1638400000),(169337/1638400000),(530411/8192000000),(215577/8192000000),(24191/4096000000)]

theorem pairPlus25Weights0_nonneg : ∀ i,0≤pairPlus25Weights0 i := by
  decide +kernel

theorem pairPlus25Identity0 (x : ℝ) :
    (pairBound25 : ℝ)+evalCoeff pairPoly25 x=bernsteinValue pairPlus25Weights0
      ((x-(0 : ℚ))/(((1/10) : ℚ)-(0 : ℚ))) := by
  norm_num [evalCoeff,bernsteinValue,pairPlus25Weights0,pairBound25,pairPoly25,Fin.sum_univ_succ]
  ring

theorem pairPlus25_nonneg (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    0≤(pairBound25 : ℝ)+evalCoeff pairPoly25 g := by
  exact interval_nonneg (fun x => (pairBound25 : ℝ)+evalCoeff pairPoly25 x) 0 (1/10)
    (by norm_num) pairPlus25Weights0 pairPlus25Weights0_nonneg
    pairPlus25Identity0 g (by simpa using hg) (by simpa using hmax)

def pairMinus25Weights0 : Fin 8 → ℚ := ![(24191/8192000000),(169337/8192000000),(508011/8192000000),(169337/1638400000),(169337/1638400000),(485611/8192000000),(123097/8192000000),0]

theorem pairMinus25Weights0_nonneg : ∀ i,0≤pairMinus25Weights0 i := by
  decide +kernel

theorem pairMinus25Identity0 (x : ℝ) :
    (pairBound25 : ℝ)-evalCoeff pairPoly25 x=bernsteinValue pairMinus25Weights0
      ((x-(0 : ℚ))/(((1/10) : ℚ)-(0 : ℚ))) := by
  norm_num [evalCoeff,bernsteinValue,pairMinus25Weights0,pairBound25,pairPoly25,Fin.sum_univ_succ]
  ring

theorem pairMinus25_nonneg (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    0≤(pairBound25 : ℝ)-evalCoeff pairPoly25 g := by
  exact interval_nonneg (fun x => (pairBound25 : ℝ)-evalCoeff pairPoly25 x) 0 (1/10)
    (by norm_num) pairMinus25Weights0 pairMinus25Weights0_nonneg
    pairMinus25Identity0 g (by simpa using hg) (by simpa using hmax)

theorem pair_bound25 (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    |evalCoeff pairPoly25 g|≤(pairBound25 : ℝ) := by
  have hlo := pairPlus25_nonneg g hg hmax
  have hhi := pairMinus25_nonneg g hg hmax
  exact abs_le.mpr ⟨by linarith,by linarith⟩

def pairPoly26 : Fin 8 → ℚ := ![0,0,0,0,(-21/32),(-3/16),(-33/64),(-15/64)]
def pairBound26 : ℚ := (8709/128000000)

def pairPlus26Weights0 : Fin 8 → ℚ := ![(8709/128000000),(60963/128000000),(182889/128000000),(60963/25600000),(59283/25600000),(157449/128000000),(35217/128000000),0]

theorem pairPlus26Weights0_nonneg : ∀ i,0≤pairPlus26Weights0 i := by
  decide +kernel

theorem pairPlus26Identity0 (x : ℝ) :
    (pairBound26 : ℝ)+evalCoeff pairPoly26 x=bernsteinValue pairPlus26Weights0
      ((x-(0 : ℚ))/(((1/10) : ℚ)-(0 : ℚ))) := by
  norm_num [evalCoeff,bernsteinValue,pairPlus26Weights0,pairBound26,pairPoly26,Fin.sum_univ_succ]
  ring

theorem pairPlus26_nonneg (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    0≤(pairBound26 : ℝ)+evalCoeff pairPoly26 g := by
  exact interval_nonneg (fun x => (pairBound26 : ℝ)+evalCoeff pairPoly26 x) 0 (1/10)
    (by norm_num) pairPlus26Weights0 pairPlus26Weights0_nonneg
    pairPlus26Identity0 g (by simpa using hg) (by simpa using hmax)

def pairMinus26Weights0 : Fin 8 → ℚ := ![(8709/128000000),(60963/128000000),(182889/128000000),(60963/25600000),(62643/25600000),(208329/128000000),(86709/128000000),(8709/64000000)]

theorem pairMinus26Weights0_nonneg : ∀ i,0≤pairMinus26Weights0 i := by
  decide +kernel

theorem pairMinus26Identity0 (x : ℝ) :
    (pairBound26 : ℝ)-evalCoeff pairPoly26 x=bernsteinValue pairMinus26Weights0
      ((x-(0 : ℚ))/(((1/10) : ℚ)-(0 : ℚ))) := by
  norm_num [evalCoeff,bernsteinValue,pairMinus26Weights0,pairBound26,pairPoly26,Fin.sum_univ_succ]
  ring

theorem pairMinus26_nonneg (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    0≤(pairBound26 : ℝ)-evalCoeff pairPoly26 g := by
  exact interval_nonneg (fun x => (pairBound26 : ℝ)-evalCoeff pairPoly26 x) 0 (1/10)
    (by norm_num) pairMinus26Weights0 pairMinus26Weights0_nonneg
    pairMinus26Identity0 g (by simpa using hg) (by simpa using hmax)

theorem pair_bound26 (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    |evalCoeff pairPoly26 g|≤(pairBound26 : ℝ) := by
  have hlo := pairPlus26_nonneg g hg hmax
  have hhi := pairMinus26_nonneg g hg hmax
  exact abs_le.mpr ⟨by linarith,by linarith⟩

def pairPoly27 : Fin 8 → ℚ := ![0,0,0,0,0,(35/128),(45/256),(1405/4096)]
def pairBound27 : ℚ := (24121/8192000000)

def pairPlus27Weights0 : Fin 8 → ℚ := ![(24121/8192000000),(168847/8192000000),(506541/8192000000),(168847/1638400000),(168847/1638400000),(528941/8192000000),(215087/8192000000),(24121/4096000000)]

theorem pairPlus27Weights0_nonneg : ∀ i,0≤pairPlus27Weights0 i := by
  decide +kernel

theorem pairPlus27Identity0 (x : ℝ) :
    (pairBound27 : ℝ)+evalCoeff pairPoly27 x=bernsteinValue pairPlus27Weights0
      ((x-(0 : ℚ))/(((1/10) : ℚ)-(0 : ℚ))) := by
  norm_num [evalCoeff,bernsteinValue,pairPlus27Weights0,pairBound27,pairPoly27,Fin.sum_univ_succ]
  ring

theorem pairPlus27_nonneg (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    0≤(pairBound27 : ℝ)+evalCoeff pairPoly27 g := by
  exact interval_nonneg (fun x => (pairBound27 : ℝ)+evalCoeff pairPoly27 x) 0 (1/10)
    (by norm_num) pairPlus27Weights0 pairPlus27Weights0_nonneg
    pairPlus27Identity0 g (by simpa using hg) (by simpa using hmax)

def pairMinus27Weights0 : Fin 8 → ℚ := ![(24121/8192000000),(168847/8192000000),(506541/8192000000),(168847/1638400000),(168847/1638400000),(484141/8192000000),(122607/8192000000),0]

theorem pairMinus27Weights0_nonneg : ∀ i,0≤pairMinus27Weights0 i := by
  decide +kernel

theorem pairMinus27Identity0 (x : ℝ) :
    (pairBound27 : ℝ)-evalCoeff pairPoly27 x=bernsteinValue pairMinus27Weights0
      ((x-(0 : ℚ))/(((1/10) : ℚ)-(0 : ℚ))) := by
  norm_num [evalCoeff,bernsteinValue,pairMinus27Weights0,pairBound27,pairPoly27,Fin.sum_univ_succ]
  ring

theorem pairMinus27_nonneg (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    0≤(pairBound27 : ℝ)-evalCoeff pairPoly27 g := by
  exact interval_nonneg (fun x => (pairBound27 : ℝ)-evalCoeff pairPoly27 x) 0 (1/10)
    (by norm_num) pairMinus27Weights0 pairMinus27Weights0_nonneg
    pairMinus27Identity0 g (by simpa using hg) (by simpa using hmax)

theorem pair_bound27 (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    |evalCoeff pairPoly27 g|≤(pairBound27 : ℝ) := by
  have hlo := pairPlus27_nonneg g hg hmax
  have hhi := pairMinus27_nonneg g hg hmax
  exact abs_le.mpr ⟨by linarith,by linarith⟩

def pairPoly28 : Fin 8 → ℚ := ![0,0,0,0,0,0,(-75/256),(-75/512)]
def pairBound28 : ℚ := (63/204800000)

def pairPlus28Weights0 : Fin 8 → ℚ := ![(63/204800000),(441/204800000),(1323/204800000),(441/40960000),(441/40960000),(1323/204800000),(381/204800000),0]

theorem pairPlus28Weights0_nonneg : ∀ i,0≤pairPlus28Weights0 i := by
  decide +kernel

theorem pairPlus28Identity0 (x : ℝ) :
    (pairBound28 : ℝ)+evalCoeff pairPoly28 x=bernsteinValue pairPlus28Weights0
      ((x-(0 : ℚ))/(((1/10) : ℚ)-(0 : ℚ))) := by
  norm_num [evalCoeff,bernsteinValue,pairPlus28Weights0,pairBound28,pairPoly28,Fin.sum_univ_succ]
  ring

theorem pairPlus28_nonneg (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    0≤(pairBound28 : ℝ)+evalCoeff pairPoly28 g := by
  exact interval_nonneg (fun x => (pairBound28 : ℝ)+evalCoeff pairPoly28 x) 0 (1/10)
    (by norm_num) pairPlus28Weights0 pairPlus28Weights0_nonneg
    pairPlus28Identity0 g (by simpa using hg) (by simpa using hmax)

def pairMinus28Weights0 : Fin 8 → ℚ := ![(63/204800000),(441/204800000),(1323/204800000),(441/40960000),(441/40960000),(1323/204800000),(501/204800000),(63/102400000)]

theorem pairMinus28Weights0_nonneg : ∀ i,0≤pairMinus28Weights0 i := by
  decide +kernel

theorem pairMinus28Identity0 (x : ℝ) :
    (pairBound28 : ℝ)-evalCoeff pairPoly28 x=bernsteinValue pairMinus28Weights0
      ((x-(0 : ℚ))/(((1/10) : ℚ)-(0 : ℚ))) := by
  norm_num [evalCoeff,bernsteinValue,pairMinus28Weights0,pairBound28,pairPoly28,Fin.sum_univ_succ]
  ring

theorem pairMinus28_nonneg (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    0≤(pairBound28 : ℝ)-evalCoeff pairPoly28 g := by
  exact interval_nonneg (fun x => (pairBound28 : ℝ)-evalCoeff pairPoly28 x) 0 (1/10)
    (by norm_num) pairMinus28Weights0 pairMinus28Weights0_nonneg
    pairMinus28Identity0 g (by simpa using hg) (by simpa using hmax)

theorem pair_bound28 (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    |evalCoeff pairPoly28 g|≤(pairBound28 : ℝ) := by
  have hlo := pairPlus28_nonneg g hg hmax
  have hhi := pairMinus28_nonneg g hg hmax
  exact abs_le.mpr ⟨by linarith,by linarith⟩

def pairPoly29 : Fin 8 → ℚ := ![0,0,0,0,0,0,(-25/128),(-25/256)]
def pairBound29 : ℚ := (21/102400000)

def pairPlus29Weights0 : Fin 8 → ℚ := ![(21/102400000),(147/102400000),(441/102400000),(147/20480000),(147/20480000),(441/102400000),(127/102400000),0]

theorem pairPlus29Weights0_nonneg : ∀ i,0≤pairPlus29Weights0 i := by
  decide +kernel

theorem pairPlus29Identity0 (x : ℝ) :
    (pairBound29 : ℝ)+evalCoeff pairPoly29 x=bernsteinValue pairPlus29Weights0
      ((x-(0 : ℚ))/(((1/10) : ℚ)-(0 : ℚ))) := by
  norm_num [evalCoeff,bernsteinValue,pairPlus29Weights0,pairBound29,pairPoly29,Fin.sum_univ_succ]
  ring

theorem pairPlus29_nonneg (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    0≤(pairBound29 : ℝ)+evalCoeff pairPoly29 g := by
  exact interval_nonneg (fun x => (pairBound29 : ℝ)+evalCoeff pairPoly29 x) 0 (1/10)
    (by norm_num) pairPlus29Weights0 pairPlus29Weights0_nonneg
    pairPlus29Identity0 g (by simpa using hg) (by simpa using hmax)

def pairMinus29Weights0 : Fin 8 → ℚ := ![(21/102400000),(147/102400000),(441/102400000),(147/20480000),(147/20480000),(441/102400000),(167/102400000),(21/51200000)]

theorem pairMinus29Weights0_nonneg : ∀ i,0≤pairMinus29Weights0 i := by
  decide +kernel

theorem pairMinus29Identity0 (x : ℝ) :
    (pairBound29 : ℝ)-evalCoeff pairPoly29 x=bernsteinValue pairMinus29Weights0
      ((x-(0 : ℚ))/(((1/10) : ℚ)-(0 : ℚ))) := by
  norm_num [evalCoeff,bernsteinValue,pairMinus29Weights0,pairBound29,pairPoly29,Fin.sum_univ_succ]
  ring

theorem pairMinus29_nonneg (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    0≤(pairBound29 : ℝ)-evalCoeff pairPoly29 g := by
  exact interval_nonneg (fun x => (pairBound29 : ℝ)-evalCoeff pairPoly29 x) 0 (1/10)
    (by norm_num) pairMinus29Weights0 pairMinus29Weights0_nonneg
    pairMinus29Identity0 g (by simpa using hg) (by simpa using hmax)

theorem pair_bound29 (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    |evalCoeff pairPoly29 g|≤(pairBound29 : ℝ) := by
  have hlo := pairPlus29_nonneg g hg hmax
  have hhi := pairMinus29_nonneg g hg hmax
  exact abs_le.mpr ⟨by linarith,by linarith⟩

def pairPoly30 : Fin 8 → ℚ := ![0,0,0,0,0,0,0,(875/4096)]
def pairBound30 : ℚ := (7/327680000)

def pairPlus30Weights0 : Fin 8 → ℚ := ![(7/327680000),(49/327680000),(147/327680000),(49/65536000),(49/65536000),(147/327680000),(49/327680000),(7/163840000)]

theorem pairPlus30Weights0_nonneg : ∀ i,0≤pairPlus30Weights0 i := by
  decide +kernel

theorem pairPlus30Identity0 (x : ℝ) :
    (pairBound30 : ℝ)+evalCoeff pairPoly30 x=bernsteinValue pairPlus30Weights0
      ((x-(0 : ℚ))/(((1/10) : ℚ)-(0 : ℚ))) := by
  norm_num [evalCoeff,bernsteinValue,pairPlus30Weights0,pairBound30,pairPoly30,Fin.sum_univ_succ]
  ring

theorem pairPlus30_nonneg (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    0≤(pairBound30 : ℝ)+evalCoeff pairPoly30 g := by
  exact interval_nonneg (fun x => (pairBound30 : ℝ)+evalCoeff pairPoly30 x) 0 (1/10)
    (by norm_num) pairPlus30Weights0 pairPlus30Weights0_nonneg
    pairPlus30Identity0 g (by simpa using hg) (by simpa using hmax)

def pairMinus30Weights0 : Fin 8 → ℚ := ![(7/327680000),(49/327680000),(147/327680000),(49/65536000),(49/65536000),(147/327680000),(49/327680000),0]

theorem pairMinus30Weights0_nonneg : ∀ i,0≤pairMinus30Weights0 i := by
  decide +kernel

theorem pairMinus30Identity0 (x : ℝ) :
    (pairBound30 : ℝ)-evalCoeff pairPoly30 x=bernsteinValue pairMinus30Weights0
      ((x-(0 : ℚ))/(((1/10) : ℚ)-(0 : ℚ))) := by
  norm_num [evalCoeff,bernsteinValue,pairMinus30Weights0,pairBound30,pairPoly30,Fin.sum_univ_succ]
  ring

theorem pairMinus30_nonneg (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    0≤(pairBound30 : ℝ)-evalCoeff pairPoly30 g := by
  exact interval_nonneg (fun x => (pairBound30 : ℝ)-evalCoeff pairPoly30 x) 0 (1/10)
    (by norm_num) pairMinus30Weights0 pairMinus30Weights0_nonneg
    pairMinus30Identity0 g (by simpa using hg) (by simpa using hmax)

theorem pair_bound30 (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    |evalCoeff pairPoly30 g|≤(pairBound30 : ℝ) := by
  have hlo := pairPlus30_nonneg g hg hmax
  have hhi := pairMinus30_nonneg g hg hmax
  exact abs_le.mpr ⟨by linarith,by linarith⟩

def pairPoly : Fin 31 → Fin 8 → ℚ := ![pairPoly0,pairPoly1,pairPoly2,pairPoly3,pairPoly4,pairPoly5,pairPoly6,pairPoly7,pairPoly8,pairPoly9,pairPoly10,pairPoly11,pairPoly12,pairPoly13,pairPoly14,pairPoly15,pairPoly16,pairPoly17,pairPoly18,pairPoly19,pairPoly20,pairPoly21,pairPoly22,pairPoly23,pairPoly24,pairPoly25,pairPoly26,pairPoly27,pairPoly28,pairPoly29,pairPoly30]

def pairBound : Fin 31 → ℚ := ![pairBound0,pairBound1,pairBound2,pairBound3,pairBound4,pairBound5,pairBound6,pairBound7,pairBound8,pairBound9,pairBound10,pairBound11,pairBound12,pairBound13,pairBound14,pairBound15,pairBound16,pairBound17,pairBound18,pairBound19,pairBound20,pairBound21,pairBound22,pairBound23,pairBound24,pairBound25,pairBound26,pairBound27,pairBound28,pairBound29,pairBound30]

theorem pair_bound (i : Fin 31) (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    |evalCoeff (pairPoly i) g|≤(pairBound i : ℝ) := by
  fin_cases i
  · exact pair_bound0 g hg hmax
  · exact pair_bound1 g hg hmax
  · exact pair_bound2 g hg hmax
  · exact pair_bound3 g hg hmax
  · exact pair_bound4 g hg hmax
  · exact pair_bound5 g hg hmax
  · exact pair_bound6 g hg hmax
  · exact pair_bound7 g hg hmax
  · exact pair_bound8 g hg hmax
  · exact pair_bound9 g hg hmax
  · exact pair_bound10 g hg hmax
  · exact pair_bound11 g hg hmax
  · exact pair_bound12 g hg hmax
  · exact pair_bound13 g hg hmax
  · exact pair_bound14 g hg hmax
  · exact pair_bound15 g hg hmax
  · exact pair_bound16 g hg hmax
  · exact pair_bound17 g hg hmax
  · exact pair_bound18 g hg hmax
  · exact pair_bound19 g hg hmax
  · exact pair_bound20 g hg hmax
  · exact pair_bound21 g hg hmax
  · exact pair_bound22 g hg hmax
  · exact pair_bound23 g hg hmax
  · exact pair_bound24 g hg hmax
  · exact pair_bound25 g hg hmax
  · exact pair_bound26 g hg hmax
  · exact pair_bound27 g hg hmax
  · exact pair_bound28 g hg hmax
  · exact pair_bound29 g hg hmax
  · exact pair_bound30 g hg hmax

def certNorm16 : Fin 15 → ℚ := ![0,0,0,0,0,0,0,0,(10875/32),(1125/32),(43227/64),(97119/256),(237825/512),(125811/256),(2455479/8192)]

def norm16Weights0 : Fin 15 → ℚ := ![(2871661602999/819200000000000000),(20101631220993/409600000000000000),(261321205872909/819200000000000000),(261321205872909/204800000000000000),(2874533264601999/819200000000000000),(2874533264601999/409600000000000000),(8623599793805997/819200000000000000),(1231942827686571/102400000000000000),(8620815793805997/819200000000000000),(2866166864601999/409600000000000000),(2832573934041999/819200000000000000),(247273098360909/204800000000000000),(218931518568909/819200000000000000),(11561907739233/409600000000000000),0]

theorem norm16Weights0_nonneg : ∀ i,0≤norm16Weights0 i := by
  decide +kernel

theorem norm16Identity0 (x : ℝ) :
    (ScalarTrial.F16_2 : ℝ)-evalCoeff certNorm16 x=bernsteinValue norm16Weights0
      ((x-(0 : ℚ))/(((1/10) : ℚ)-(0 : ℚ))) := by
  norm_num [evalCoeff,bernsteinValue,norm16Weights0,ScalarTrial.F16_2,certNorm16,Fin.sum_univ_succ]
  ring

theorem norm16_nonneg (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    0≤(ScalarTrial.F16_2 : ℝ)-evalCoeff certNorm16 g := by
  exact interval_nonneg (fun x => (ScalarTrial.F16_2 : ℝ)-evalCoeff certNorm16 x) 0 (1/10)
    (by norm_num) norm16Weights0 norm16Weights0_nonneg
    norm16Identity0 g (by simpa using hg) (by simpa using hmax)

def certNorm32 : Fin 15 → ℚ := ![0,0,0,0,0,0,0,0,(49617/128),(-3015/64),(200901/256),(891855/2048),(1352007/2048),(5319045/8192),(53424615/131072)]

def norm32Weights0 : Fin 15 → ℚ := ![(10257117031323/2621440000000000000),(71799819219261/1310720000000000000),(933397649850393/2621440000000000000),(933397649850393/655360000000000000),(10267374148354323/2621440000000000000),(10267374148354323/1310720000000000000),(30802122445062969/2621440000000000000),(4400303206437567/327680000000000000),(30791960883462969/2621440000000000000),(10236951210754323/1310720000000000000),(10115362473730323/2621440000000000000),(882690001290393/655360000000000000),(780938856305433/2621440000000000000),(41193485881581/1310720000000000000),0]

theorem norm32Weights0_nonneg : ∀ i,0≤norm32Weights0 i := by
  decide +kernel

theorem norm32Identity0 (x : ℝ) :
    (ScalarTrial.F32_2 : ℝ)-evalCoeff certNorm32 x=bernsteinValue norm32Weights0
      ((x-(0 : ℚ))/(((1/10) : ℚ)-(0 : ℚ))) := by
  norm_num [evalCoeff,bernsteinValue,norm32Weights0,ScalarTrial.F32_2,certNorm32,Fin.sum_univ_succ]
  ring

theorem norm32_nonneg (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    0≤(ScalarTrial.F32_2 : ℝ)-evalCoeff certNorm32 g := by
  exact interval_nonneg (fun x => (ScalarTrial.F32_2 : ℝ)-evalCoeff certNorm32 x) 0 (1/10)
    (by norm_num) norm32Weights0 norm32Weights0_nonneg
    norm32Identity0 g (by simpa using hg) (by simpa using hmax)

def certNorm64 : Fin 15 → ℚ := ![0,0,0,0,0,0,0,0,(16113/32),(-543/32),(8547/8),(636237/1024),(919731/1024),(874929/1024),(2136597/4096)]

def norm64Weights0 : Fin 15 → ℚ := ![(2102224214157/409600000000000000),(14715569499099/204800000000000000),(191302403488287/409600000000000000),(191302403488287/102400000000000000),(2104326438371157/409600000000000000),(2104326438371157/204800000000000000),(6312979315113471/409600000000000000),(901854187873353/51200000000000000),(6310916851113471/409600000000000000),(2098142521571157/204800000000000000),(2073380469731157/409600000000000000),(180963062611287/102400000000000000),(160164380911887/409600000000000000),(8453829406119/204800000000000000),0]

theorem norm64Weights0_nonneg : ∀ i,0≤norm64Weights0 i := by
  decide +kernel

theorem norm64Identity0 (x : ℝ) :
    (ScalarTrial.F64_2 : ℝ)-evalCoeff certNorm64 x=bernsteinValue norm64Weights0
      ((x-(0 : ℚ))/(((1/10) : ℚ)-(0 : ℚ))) := by
  norm_num [evalCoeff,bernsteinValue,norm64Weights0,ScalarTrial.F64_2,certNorm64,Fin.sum_univ_succ]
  ring

theorem norm64_nonneg (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    0≤(ScalarTrial.F64_2 : ℝ)-evalCoeff certNorm64 g := by
  exact interval_nonneg (fun x => (ScalarTrial.F64_2 : ℝ)-evalCoeff certNorm64 x) 0 (1/10)
    (by norm_num) norm64Weights0 norm64Weights0_nonneg
    norm64Identity0 g (by simpa using hg) (by simpa using hmax)

end BilayerDressed.CubicResidualIntervalCertificates
