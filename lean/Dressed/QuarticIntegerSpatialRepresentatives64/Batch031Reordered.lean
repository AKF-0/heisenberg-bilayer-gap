import Dressed.QuarticIntegerSpatialRepresentatives64.Base
set_option Elab.async false
namespace BilayerDressed.QuarticIntegerSpatialRepresentatives64
open BilayerGap QuarticIntegerArrays QuarticIntegerDirect QuarticIntegerData
open QuarticIntegerLocalCases QuarticIntegerZeroCases QuarticIntegerBalancedKernel QuarticIntegerMembership64
open QuarticIntegerSpatialListCertificate QuarticIntegerRepresentativeTree
set_option maxHeartbeats 0
set_option maxRecDepth 200000
def representative_1984 : Rep := ⟨![0,9,20,37],462⟩
def representative_1985 : Rep := ⟨![0,9,20,38],462⟩
def representative_1986 : Rep := ⟨![0,9,20,39],462⟩
def representative_1987 : Rep := ⟨![0,9,20,42],462⟩
def representative_1988 : Rep := ⟨![0,9,20,43],462⟩
def representative_1989 : Rep := ⟨![0,9,20,45],462⟩
def representative_1990 : Rep := ⟨![0,9,20,46],462⟩
def representative_1991 : Rep := ⟨![0,9,20,47],462⟩
def representative_1992 : Rep := ⟨![0,9,20,50],462⟩
def representative_1993 : Rep := ⟨![0,9,20,51],462⟩
def representative_1994 : Rep := ⟨![0,9,20,53],462⟩
def representative_1995 : Rep := ⟨![0,9,20,54],462⟩
def representative_1996 : Rep := ⟨![0,9,20,58],232⟩
def representative_1997 : Rep := ⟨![0,9,20,59],462⟩
def representative_1998 : Rep := ⟨![0,9,20,61],462⟩
def representative_1999 : Rep := ⟨![0,9,21,27],462⟩
def representative_2000 : Rep := ⟨![0,9,21,28],462⟩
def representative_2001 : Rep := ⟨![0,9,21,30],462⟩
def representative_2002 : Rep := ⟨![0,9,21,31],462⟩
def representative_2003 : Rep := ⟨![0,9,21,35],462⟩
def representative_2004 : Rep := ⟨![0,9,21,36],462⟩
def representative_2005 : Rep := ⟨![0,9,21,38],462⟩
def representative_2006 : Rep := ⟨![0,9,21,39],462⟩
def representative_2007 : Rep := ⟨![0,9,21,42],462⟩
def representative_2008 : Rep := ⟨![0,9,21,43],462⟩
def representative_2009 : Rep := ⟨![0,9,21,44],462⟩
def representative_2010 : Rep := ⟨![0,9,21,46],462⟩
def representative_2011 : Rep := ⟨![0,9,21,50],462⟩
def representative_2012 : Rep := ⟨![0,9,21,51],462⟩
def representative_2013 : Rep := ⟨![0,9,21,52],462⟩
def representative_2014 : Rep := ⟨![0,9,21,54],462⟩
def representative_2015 : Rep := ⟨![0,9,21,58],462⟩
def representative_2016 : Rep := ⟨![0,9,21,59],462⟩
def representative_2017 : Rep := ⟨![0,9,21,60],462⟩
def representative_2018 : Rep := ⟨![0,9,22,27],462⟩
def representative_2019 : Rep := ⟨![0,9,22,28],462⟩
def representative_2020 : Rep := ⟨![0,9,22,31],462⟩
def representative_2021 : Rep := ⟨![0,9,22,35],462⟩
def representative_2022 : Rep := ⟨![0,9,22,36],462⟩
def representative_2023 : Rep := ⟨![0,9,22,37],462⟩
def representative_2024 : Rep := ⟨![0,9,22,43],462⟩
def representative_2025 : Rep := ⟨![0,9,22,44],462⟩
def representative_2026 : Rep := ⟨![0,9,22,45],462⟩
def representative_2027 : Rep := ⟨![0,9,22,50],462⟩
def representative_2028 : Rep := ⟨![0,9,22,51],462⟩
def representative_2029 : Rep := ⟨![0,9,22,52],462⟩
def representative_2030 : Rep := ⟨![0,9,22,53],462⟩
def representative_2031 : Rep := ⟨![0,9,22,58],223⟩
def representative_2032 : Rep := ⟨![0,9,22,59],462⟩
def representative_2033 : Rep := ⟨![0,9,23,27],228⟩
def representative_2034 : Rep := ⟨![0,9,23,28],462⟩
def representative_2035 : Rep := ⟨![0,9,23,29],224⟩
def representative_2036 : Rep := ⟨![0,9,23,35],462⟩
def representative_2037 : Rep := ⟨![0,9,23,36],462⟩
def representative_2038 : Rep := ⟨![0,9,23,37],462⟩
def representative_2039 : Rep := ⟨![0,9,23,43],462⟩
def representative_2040 : Rep := ⟨![0,9,23,44],462⟩
def representative_2041 : Rep := ⟨![0,9,23,51],462⟩
def representative_2042 : Rep := ⟨![0,9,23,58],321⟩
def representative_2043 : Rep := ⟨![0,9,27,36],462⟩
def representative_2044 : Rep := ⟨![0,9,27,37],462⟩
def representative_2045 : Rep := ⟨![0,9,27,38],462⟩
def representative_2046 : Rep := ⟨![0,9,27,45],462⟩
def representative_2047 : Rep := ⟨![0,9,27,46],462⟩
theorem coefficient_1984 : validRep representative_1984 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1984)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1985 : validRep representative_1985 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1985)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1986 : validRep representative_1986 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1986)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1987 : validRep representative_1987 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1987)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1988 : validRep representative_1988 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1988)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1989 : validRep representative_1989 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1989)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1990 : validRep representative_1990 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1990)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1991 : validRep representative_1991 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1991)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1992 : validRep representative_1992 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1992)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1993 : validRep representative_1993 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1993)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1994 : validRep representative_1994 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1994)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1995 : validRep representative_1995 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1995)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1996 : validRep representative_1996 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1996)=dictionary64.getD 232 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_232]
  decide +kernel
theorem coefficient_1997 : validRep representative_1997 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1997)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1998 : validRep representative_1998 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1998)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1999 : validRep representative_1999 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1999)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2000 : validRep representative_2000 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2000)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2001 : validRep representative_2001 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2001)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2002 : validRep representative_2002 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2002)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2003 : validRep representative_2003 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2003)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2004 : validRep representative_2004 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2004)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2005 : validRep representative_2005 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2005)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2006 : validRep representative_2006 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2006)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2007 : validRep representative_2007 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2007)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2008 : validRep representative_2008 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2008)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2009 : validRep representative_2009 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2009)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2010 : validRep representative_2010 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2010)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2011 : validRep representative_2011 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2011)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2012 : validRep representative_2012 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2012)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2013 : validRep representative_2013 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2013)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2014 : validRep representative_2014 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2014)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2015 : validRep representative_2015 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2015)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2016 : validRep representative_2016 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2016)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2017 : validRep representative_2017 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2017)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2018 : validRep representative_2018 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2018)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2019 : validRep representative_2019 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2019)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2020 : validRep representative_2020 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2020)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2021 : validRep representative_2021 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2021)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2022 : validRep representative_2022 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2022)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2023 : validRep representative_2023 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2023)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2024 : validRep representative_2024 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2024)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2025 : validRep representative_2025 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2025)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2026 : validRep representative_2026 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2026)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2027 : validRep representative_2027 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2027)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2028 : validRep representative_2028 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2028)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2029 : validRep representative_2029 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2029)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2030 : validRep representative_2030 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2030)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2031 : validRep representative_2031 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2031)=dictionary64.getD 223 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_223]
  decide +kernel
theorem coefficient_2032 : validRep representative_2032 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2032)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2033 : validRep representative_2033 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2033)=dictionary64.getD 228 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_228]
  decide +kernel
theorem coefficient_2034 : validRep representative_2034 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2034)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2035 : validRep representative_2035 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2035)=dictionary64.getD 224 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_224]
  decide +kernel
theorem coefficient_2036 : validRep representative_2036 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2036)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2037 : validRep representative_2037 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2037)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2038 : validRep representative_2038 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2038)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2039 : validRep representative_2039 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2039)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2040 : validRep representative_2040 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2040)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2041 : validRep representative_2041 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2041)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2042 : validRep representative_2042 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2042)=dictionary64.getD 321 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_321]
  decide +kernel
theorem coefficient_2043 : validRep representative_2043 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2043)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2044 : validRep representative_2044 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2044)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2045 : validRep representative_2045 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2045)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2046 : validRep representative_2046 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2046)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_2047 : validRep representative_2047 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_2047)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
def tree_031 : QuarticIntegerRepresentativeTree.Tree Rep := (QuarticIntegerRepresentativeTree.Tree.branch 2016 (QuarticIntegerRepresentativeTree.Tree.branch 2000 (QuarticIntegerRepresentativeTree.Tree.branch 1992 (QuarticIntegerRepresentativeTree.Tree.branch 1988 (QuarticIntegerRepresentativeTree.Tree.branch 1986 (QuarticIntegerRepresentativeTree.Tree.branch 1985 (QuarticIntegerRepresentativeTree.Tree.leaf 1984 representative_1984) (QuarticIntegerRepresentativeTree.Tree.leaf 1985 representative_1985)) (QuarticIntegerRepresentativeTree.Tree.branch 1987 (QuarticIntegerRepresentativeTree.Tree.leaf 1986 representative_1986) (QuarticIntegerRepresentativeTree.Tree.leaf 1987 representative_1987))) (QuarticIntegerRepresentativeTree.Tree.branch 1990 (QuarticIntegerRepresentativeTree.Tree.branch 1989 (QuarticIntegerRepresentativeTree.Tree.leaf 1988 representative_1988) (QuarticIntegerRepresentativeTree.Tree.leaf 1989 representative_1989)) (QuarticIntegerRepresentativeTree.Tree.branch 1991 (QuarticIntegerRepresentativeTree.Tree.leaf 1990 representative_1990) (QuarticIntegerRepresentativeTree.Tree.leaf 1991 representative_1991)))) (QuarticIntegerRepresentativeTree.Tree.branch 1996 (QuarticIntegerRepresentativeTree.Tree.branch 1994 (QuarticIntegerRepresentativeTree.Tree.branch 1993 (QuarticIntegerRepresentativeTree.Tree.leaf 1992 representative_1992) (QuarticIntegerRepresentativeTree.Tree.leaf 1993 representative_1993)) (QuarticIntegerRepresentativeTree.Tree.branch 1995 (QuarticIntegerRepresentativeTree.Tree.leaf 1994 representative_1994) (QuarticIntegerRepresentativeTree.Tree.leaf 1995 representative_1995))) (QuarticIntegerRepresentativeTree.Tree.branch 1998 (QuarticIntegerRepresentativeTree.Tree.branch 1997 (QuarticIntegerRepresentativeTree.Tree.leaf 1996 representative_1996) (QuarticIntegerRepresentativeTree.Tree.leaf 1997 representative_1997)) (QuarticIntegerRepresentativeTree.Tree.branch 1999 (QuarticIntegerRepresentativeTree.Tree.leaf 1998 representative_1998) (QuarticIntegerRepresentativeTree.Tree.leaf 1999 representative_1999))))) (QuarticIntegerRepresentativeTree.Tree.branch 2008 (QuarticIntegerRepresentativeTree.Tree.branch 2004 (QuarticIntegerRepresentativeTree.Tree.branch 2002 (QuarticIntegerRepresentativeTree.Tree.branch 2001 (QuarticIntegerRepresentativeTree.Tree.leaf 2000 representative_2000) (QuarticIntegerRepresentativeTree.Tree.leaf 2001 representative_2001)) (QuarticIntegerRepresentativeTree.Tree.branch 2003 (QuarticIntegerRepresentativeTree.Tree.leaf 2002 representative_2002) (QuarticIntegerRepresentativeTree.Tree.leaf 2003 representative_2003))) (QuarticIntegerRepresentativeTree.Tree.branch 2006 (QuarticIntegerRepresentativeTree.Tree.branch 2005 (QuarticIntegerRepresentativeTree.Tree.leaf 2004 representative_2004) (QuarticIntegerRepresentativeTree.Tree.leaf 2005 representative_2005)) (QuarticIntegerRepresentativeTree.Tree.branch 2007 (QuarticIntegerRepresentativeTree.Tree.leaf 2006 representative_2006) (QuarticIntegerRepresentativeTree.Tree.leaf 2007 representative_2007)))) (QuarticIntegerRepresentativeTree.Tree.branch 2012 (QuarticIntegerRepresentativeTree.Tree.branch 2010 (QuarticIntegerRepresentativeTree.Tree.branch 2009 (QuarticIntegerRepresentativeTree.Tree.leaf 2008 representative_2008) (QuarticIntegerRepresentativeTree.Tree.leaf 2009 representative_2009)) (QuarticIntegerRepresentativeTree.Tree.branch 2011 (QuarticIntegerRepresentativeTree.Tree.leaf 2010 representative_2010) (QuarticIntegerRepresentativeTree.Tree.leaf 2011 representative_2011))) (QuarticIntegerRepresentativeTree.Tree.branch 2014 (QuarticIntegerRepresentativeTree.Tree.branch 2013 (QuarticIntegerRepresentativeTree.Tree.leaf 2012 representative_2012) (QuarticIntegerRepresentativeTree.Tree.leaf 2013 representative_2013)) (QuarticIntegerRepresentativeTree.Tree.branch 2015 (QuarticIntegerRepresentativeTree.Tree.leaf 2014 representative_2014) (QuarticIntegerRepresentativeTree.Tree.leaf 2015 representative_2015)))))) (QuarticIntegerRepresentativeTree.Tree.branch 2032 (QuarticIntegerRepresentativeTree.Tree.branch 2024 (QuarticIntegerRepresentativeTree.Tree.branch 2020 (QuarticIntegerRepresentativeTree.Tree.branch 2018 (QuarticIntegerRepresentativeTree.Tree.branch 2017 (QuarticIntegerRepresentativeTree.Tree.leaf 2016 representative_2016) (QuarticIntegerRepresentativeTree.Tree.leaf 2017 representative_2017)) (QuarticIntegerRepresentativeTree.Tree.branch 2019 (QuarticIntegerRepresentativeTree.Tree.leaf 2018 representative_2018) (QuarticIntegerRepresentativeTree.Tree.leaf 2019 representative_2019))) (QuarticIntegerRepresentativeTree.Tree.branch 2022 (QuarticIntegerRepresentativeTree.Tree.branch 2021 (QuarticIntegerRepresentativeTree.Tree.leaf 2020 representative_2020) (QuarticIntegerRepresentativeTree.Tree.leaf 2021 representative_2021)) (QuarticIntegerRepresentativeTree.Tree.branch 2023 (QuarticIntegerRepresentativeTree.Tree.leaf 2022 representative_2022) (QuarticIntegerRepresentativeTree.Tree.leaf 2023 representative_2023)))) (QuarticIntegerRepresentativeTree.Tree.branch 2028 (QuarticIntegerRepresentativeTree.Tree.branch 2026 (QuarticIntegerRepresentativeTree.Tree.branch 2025 (QuarticIntegerRepresentativeTree.Tree.leaf 2024 representative_2024) (QuarticIntegerRepresentativeTree.Tree.leaf 2025 representative_2025)) (QuarticIntegerRepresentativeTree.Tree.branch 2027 (QuarticIntegerRepresentativeTree.Tree.leaf 2026 representative_2026) (QuarticIntegerRepresentativeTree.Tree.leaf 2027 representative_2027))) (QuarticIntegerRepresentativeTree.Tree.branch 2030 (QuarticIntegerRepresentativeTree.Tree.branch 2029 (QuarticIntegerRepresentativeTree.Tree.leaf 2028 representative_2028) (QuarticIntegerRepresentativeTree.Tree.leaf 2029 representative_2029)) (QuarticIntegerRepresentativeTree.Tree.branch 2031 (QuarticIntegerRepresentativeTree.Tree.leaf 2030 representative_2030) (QuarticIntegerRepresentativeTree.Tree.leaf 2031 representative_2031))))) (QuarticIntegerRepresentativeTree.Tree.branch 2040 (QuarticIntegerRepresentativeTree.Tree.branch 2036 (QuarticIntegerRepresentativeTree.Tree.branch 2034 (QuarticIntegerRepresentativeTree.Tree.branch 2033 (QuarticIntegerRepresentativeTree.Tree.leaf 2032 representative_2032) (QuarticIntegerRepresentativeTree.Tree.leaf 2033 representative_2033)) (QuarticIntegerRepresentativeTree.Tree.branch 2035 (QuarticIntegerRepresentativeTree.Tree.leaf 2034 representative_2034) (QuarticIntegerRepresentativeTree.Tree.leaf 2035 representative_2035))) (QuarticIntegerRepresentativeTree.Tree.branch 2038 (QuarticIntegerRepresentativeTree.Tree.branch 2037 (QuarticIntegerRepresentativeTree.Tree.leaf 2036 representative_2036) (QuarticIntegerRepresentativeTree.Tree.leaf 2037 representative_2037)) (QuarticIntegerRepresentativeTree.Tree.branch 2039 (QuarticIntegerRepresentativeTree.Tree.leaf 2038 representative_2038) (QuarticIntegerRepresentativeTree.Tree.leaf 2039 representative_2039)))) (QuarticIntegerRepresentativeTree.Tree.branch 2044 (QuarticIntegerRepresentativeTree.Tree.branch 2042 (QuarticIntegerRepresentativeTree.Tree.branch 2041 (QuarticIntegerRepresentativeTree.Tree.leaf 2040 representative_2040) (QuarticIntegerRepresentativeTree.Tree.leaf 2041 representative_2041)) (QuarticIntegerRepresentativeTree.Tree.branch 2043 (QuarticIntegerRepresentativeTree.Tree.leaf 2042 representative_2042) (QuarticIntegerRepresentativeTree.Tree.leaf 2043 representative_2043))) (QuarticIntegerRepresentativeTree.Tree.branch 2046 (QuarticIntegerRepresentativeTree.Tree.branch 2045 (QuarticIntegerRepresentativeTree.Tree.leaf 2044 representative_2044) (QuarticIntegerRepresentativeTree.Tree.leaf 2045 representative_2045)) (QuarticIntegerRepresentativeTree.Tree.branch 2047 (QuarticIntegerRepresentativeTree.Tree.leaf 2046 representative_2046) (QuarticIntegerRepresentativeTree.Tree.leaf 2047 representative_2047)))))))
theorem accepted_031 : All validRep tree_031 := ⟨⟨⟨⟨⟨⟨coefficient_1984,coefficient_1985⟩,⟨coefficient_1986,coefficient_1987⟩⟩,⟨⟨coefficient_1988,coefficient_1989⟩,⟨coefficient_1990,coefficient_1991⟩⟩⟩,⟨⟨⟨coefficient_1992,coefficient_1993⟩,⟨coefficient_1994,coefficient_1995⟩⟩,⟨⟨coefficient_1996,coefficient_1997⟩,⟨coefficient_1998,coefficient_1999⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_2000,coefficient_2001⟩,⟨coefficient_2002,coefficient_2003⟩⟩,⟨⟨coefficient_2004,coefficient_2005⟩,⟨coefficient_2006,coefficient_2007⟩⟩⟩,⟨⟨⟨coefficient_2008,coefficient_2009⟩,⟨coefficient_2010,coefficient_2011⟩⟩,⟨⟨coefficient_2012,coefficient_2013⟩,⟨coefficient_2014,coefficient_2015⟩⟩⟩⟩⟩,⟨⟨⟨⟨⟨coefficient_2016,coefficient_2017⟩,⟨coefficient_2018,coefficient_2019⟩⟩,⟨⟨coefficient_2020,coefficient_2021⟩,⟨coefficient_2022,coefficient_2023⟩⟩⟩,⟨⟨⟨coefficient_2024,coefficient_2025⟩,⟨coefficient_2026,coefficient_2027⟩⟩,⟨⟨coefficient_2028,coefficient_2029⟩,⟨coefficient_2030,coefficient_2031⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_2032,coefficient_2033⟩,⟨coefficient_2034,coefficient_2035⟩⟩,⟨⟨coefficient_2036,coefficient_2037⟩,⟨coefficient_2038,coefficient_2039⟩⟩⟩,⟨⟨⟨coefficient_2040,coefficient_2041⟩,⟨coefficient_2042,coefficient_2043⟩⟩,⟨⟨coefficient_2044,coefficient_2045⟩,⟨coefficient_2046,coefficient_2047⟩⟩⟩⟩⟩⟩
end BilayerDressed.QuarticIntegerSpatialRepresentatives64
