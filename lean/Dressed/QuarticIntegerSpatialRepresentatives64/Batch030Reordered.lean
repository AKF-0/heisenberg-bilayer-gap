import Dressed.QuarticIntegerSpatialRepresentatives64.Base
set_option Elab.async false
namespace BilayerDressed.QuarticIntegerSpatialRepresentatives64
open BilayerGap QuarticIntegerArrays QuarticIntegerDirect QuarticIntegerData
open QuarticIntegerLocalCases QuarticIntegerZeroCases QuarticIntegerBalancedKernel QuarticIntegerMembership64
open QuarticIntegerSpatialListCertificate QuarticIntegerRepresentativeTree
set_option maxHeartbeats 0
set_option maxRecDepth 200000
def representative_1920 : Rep := ⟨![0,9,7,35],462⟩
def representative_1921 : Rep := ⟨![0,9,7,36],462⟩
def representative_1922 : Rep := ⟨![0,9,7,37],462⟩
def representative_1923 : Rep := ⟨![0,9,7,38],462⟩
def representative_1924 : Rep := ⟨![0,9,7,42],462⟩
def representative_1925 : Rep := ⟨![0,9,7,43],462⟩
def representative_1926 : Rep := ⟨![0,9,7,44],462⟩
def representative_1927 : Rep := ⟨![0,9,7,45],462⟩
def representative_1928 : Rep := ⟨![0,9,7,46],462⟩
def representative_1929 : Rep := ⟨![0,9,7,50],138⟩
def representative_1930 : Rep := ⟨![0,9,7,51],462⟩
def representative_1931 : Rep := ⟨![0,9,7,52],462⟩
def representative_1932 : Rep := ⟨![0,9,7,53],462⟩
def representative_1933 : Rep := ⟨![0,9,7,54],135⟩
def representative_1934 : Rep := ⟨![0,9,7,58],408⟩
def representative_1935 : Rep := ⟨![0,9,7,59],160⟩
def representative_1936 : Rep := ⟨![0,9,7,60],462⟩
def representative_1937 : Rep := ⟨![0,9,7,61],157⟩
def representative_1938 : Rep := ⟨![0,9,7,62],412⟩
def representative_1939 : Rep := ⟨![0,9,18,27],319⟩
def representative_1940 : Rep := ⟨![0,9,18,28],228⟩
def representative_1941 : Rep := ⟨![0,9,18,29],462⟩
def representative_1942 : Rep := ⟨![0,9,18,30],462⟩
def representative_1943 : Rep := ⟨![0,9,18,31],295⟩
def representative_1944 : Rep := ⟨![0,9,18,36],462⟩
def representative_1945 : Rep := ⟨![0,9,18,37],462⟩
def representative_1946 : Rep := ⟨![0,9,18,38],462⟩
def representative_1947 : Rep := ⟨![0,9,18,39],462⟩
def representative_1948 : Rep := ⟨![0,9,18,45],462⟩
def representative_1949 : Rep := ⟨![0,9,18,46],462⟩
def representative_1950 : Rep := ⟨![0,9,18,47],462⟩
def representative_1951 : Rep := ⟨![0,9,18,54],462⟩
def representative_1952 : Rep := ⟨![0,9,18,55],228⟩
def representative_1953 : Rep := ⟨![0,9,18,63],319⟩
def representative_1954 : Rep := ⟨![0,9,19,26],306⟩
def representative_1955 : Rep := ⟨![0,9,19,28],462⟩
def representative_1956 : Rep := ⟨![0,9,19,29],462⟩
def representative_1957 : Rep := ⟨![0,9,19,30],462⟩
def representative_1958 : Rep := ⟨![0,9,19,31],228⟩
def representative_1959 : Rep := ⟨![0,9,19,34],232⟩
def representative_1960 : Rep := ⟨![0,9,19,36],462⟩
def representative_1961 : Rep := ⟨![0,9,19,37],462⟩
def representative_1962 : Rep := ⟨![0,9,19,38],462⟩
def representative_1963 : Rep := ⟨![0,9,19,39],462⟩
def representative_1964 : Rep := ⟨![0,9,19,42],462⟩
def representative_1965 : Rep := ⟨![0,9,19,44],462⟩
def representative_1966 : Rep := ⟨![0,9,19,45],462⟩
def representative_1967 : Rep := ⟨![0,9,19,46],462⟩
def representative_1968 : Rep := ⟨![0,9,19,47],462⟩
def representative_1969 : Rep := ⟨![0,9,19,50],232⟩
def representative_1970 : Rep := ⟨![0,9,19,52],462⟩
def representative_1971 : Rep := ⟨![0,9,19,53],462⟩
def representative_1972 : Rep := ⟨![0,9,19,54],462⟩
def representative_1973 : Rep := ⟨![0,9,19,55],462⟩
def representative_1974 : Rep := ⟨![0,9,19,58],306⟩
def representative_1975 : Rep := ⟨![0,9,19,60],462⟩
def representative_1976 : Rep := ⟨![0,9,19,61],462⟩
def representative_1977 : Rep := ⟨![0,9,19,62],462⟩
def representative_1978 : Rep := ⟨![0,9,20,27],462⟩
def representative_1979 : Rep := ⟨![0,9,20,29],462⟩
def representative_1980 : Rep := ⟨![0,9,20,30],462⟩
def representative_1981 : Rep := ⟨![0,9,20,31],462⟩
def representative_1982 : Rep := ⟨![0,9,20,34],462⟩
def representative_1983 : Rep := ⟨![0,9,20,35],462⟩
theorem coefficient_1920 : validRep representative_1920 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1920)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1921 : validRep representative_1921 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1921)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1922 : validRep representative_1922 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1922)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1923 : validRep representative_1923 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1923)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1924 : validRep representative_1924 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1924)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1925 : validRep representative_1925 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1925)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1926 : validRep representative_1926 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1926)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1927 : validRep representative_1927 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1927)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1928 : validRep representative_1928 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1928)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1929 : validRep representative_1929 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1929)=dictionary64.getD 138 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_138]
  decide +kernel
theorem coefficient_1930 : validRep representative_1930 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1930)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1931 : validRep representative_1931 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1931)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1932 : validRep representative_1932 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1932)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1933 : validRep representative_1933 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1933)=dictionary64.getD 135 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_135]
  decide +kernel
theorem coefficient_1934 : validRep representative_1934 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1934)=dictionary64.getD 408 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_408]
  decide +kernel
theorem coefficient_1935 : validRep representative_1935 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1935)=dictionary64.getD 160 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_160]
  decide +kernel
theorem coefficient_1936 : validRep representative_1936 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1936)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1937 : validRep representative_1937 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1937)=dictionary64.getD 157 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_157]
  decide +kernel
theorem coefficient_1938 : validRep representative_1938 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1938)=dictionary64.getD 412 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_412]
  decide +kernel
theorem coefficient_1939 : validRep representative_1939 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1939)=dictionary64.getD 319 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_319]
  decide +kernel
theorem coefficient_1940 : validRep representative_1940 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1940)=dictionary64.getD 228 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_228]
  decide +kernel
theorem coefficient_1941 : validRep representative_1941 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1941)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1942 : validRep representative_1942 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1942)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1943 : validRep representative_1943 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1943)=dictionary64.getD 295 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_295]
  decide +kernel
theorem coefficient_1944 : validRep representative_1944 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1944)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1945 : validRep representative_1945 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1945)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1946 : validRep representative_1946 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1946)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1947 : validRep representative_1947 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1947)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1948 : validRep representative_1948 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1948)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1949 : validRep representative_1949 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1949)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1950 : validRep representative_1950 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1950)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1951 : validRep representative_1951 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1951)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1952 : validRep representative_1952 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1952)=dictionary64.getD 228 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_228]
  decide +kernel
theorem coefficient_1953 : validRep representative_1953 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1953)=dictionary64.getD 319 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_319]
  decide +kernel
theorem coefficient_1954 : validRep representative_1954 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1954)=dictionary64.getD 306 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_306]
  decide +kernel
theorem coefficient_1955 : validRep representative_1955 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1955)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1956 : validRep representative_1956 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1956)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1957 : validRep representative_1957 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1957)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1958 : validRep representative_1958 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1958)=dictionary64.getD 228 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_228]
  decide +kernel
theorem coefficient_1959 : validRep representative_1959 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1959)=dictionary64.getD 232 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_232]
  decide +kernel
theorem coefficient_1960 : validRep representative_1960 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1960)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1961 : validRep representative_1961 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1961)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1962 : validRep representative_1962 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1962)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1963 : validRep representative_1963 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1963)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1964 : validRep representative_1964 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1964)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1965 : validRep representative_1965 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1965)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1966 : validRep representative_1966 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1966)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1967 : validRep representative_1967 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1967)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1968 : validRep representative_1968 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1968)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1969 : validRep representative_1969 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1969)=dictionary64.getD 232 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_232]
  decide +kernel
theorem coefficient_1970 : validRep representative_1970 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1970)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1971 : validRep representative_1971 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1971)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1972 : validRep representative_1972 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1972)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1973 : validRep representative_1973 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1973)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1974 : validRep representative_1974 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1974)=dictionary64.getD 306 0
  rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel),cachedKernel64_eq_tree,dictionary_306]
  decide +kernel
theorem coefficient_1975 : validRep representative_1975 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1975)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1976 : validRep representative_1976 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1976)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1977 : validRep representative_1977 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1977)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1978 : validRep representative_1978 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1978)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1979 : validRep representative_1979 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1979)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1980 : validRep representative_1980 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1980)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1981 : validRep representative_1981 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1981)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1982 : validRep representative_1982 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1982)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
theorem coefficient_1983 : validRep representative_1983 := by
  change forward (cachedKernel 4 4 kernelData64) (Torus.xNext 4 4) (Torus.yNext 4 4) (repTuple 4 4 representative_1983)=dictionary64.getD 462 0
  rw [cachedKernel64_eq_tree,dictionary_462]
  first
  | exact forward_zero_of_check _ _ _ _ (by decide +kernel) (by decide +kernel)
  | rw [←fastForward_eq_forward _ _ _ _ (by decide +kernel)]
    decide +kernel
def tree_030 : QuarticIntegerRepresentativeTree.Tree Rep := (QuarticIntegerRepresentativeTree.Tree.branch 1952 (QuarticIntegerRepresentativeTree.Tree.branch 1936 (QuarticIntegerRepresentativeTree.Tree.branch 1928 (QuarticIntegerRepresentativeTree.Tree.branch 1924 (QuarticIntegerRepresentativeTree.Tree.branch 1922 (QuarticIntegerRepresentativeTree.Tree.branch 1921 (QuarticIntegerRepresentativeTree.Tree.leaf 1920 representative_1920) (QuarticIntegerRepresentativeTree.Tree.leaf 1921 representative_1921)) (QuarticIntegerRepresentativeTree.Tree.branch 1923 (QuarticIntegerRepresentativeTree.Tree.leaf 1922 representative_1922) (QuarticIntegerRepresentativeTree.Tree.leaf 1923 representative_1923))) (QuarticIntegerRepresentativeTree.Tree.branch 1926 (QuarticIntegerRepresentativeTree.Tree.branch 1925 (QuarticIntegerRepresentativeTree.Tree.leaf 1924 representative_1924) (QuarticIntegerRepresentativeTree.Tree.leaf 1925 representative_1925)) (QuarticIntegerRepresentativeTree.Tree.branch 1927 (QuarticIntegerRepresentativeTree.Tree.leaf 1926 representative_1926) (QuarticIntegerRepresentativeTree.Tree.leaf 1927 representative_1927)))) (QuarticIntegerRepresentativeTree.Tree.branch 1932 (QuarticIntegerRepresentativeTree.Tree.branch 1930 (QuarticIntegerRepresentativeTree.Tree.branch 1929 (QuarticIntegerRepresentativeTree.Tree.leaf 1928 representative_1928) (QuarticIntegerRepresentativeTree.Tree.leaf 1929 representative_1929)) (QuarticIntegerRepresentativeTree.Tree.branch 1931 (QuarticIntegerRepresentativeTree.Tree.leaf 1930 representative_1930) (QuarticIntegerRepresentativeTree.Tree.leaf 1931 representative_1931))) (QuarticIntegerRepresentativeTree.Tree.branch 1934 (QuarticIntegerRepresentativeTree.Tree.branch 1933 (QuarticIntegerRepresentativeTree.Tree.leaf 1932 representative_1932) (QuarticIntegerRepresentativeTree.Tree.leaf 1933 representative_1933)) (QuarticIntegerRepresentativeTree.Tree.branch 1935 (QuarticIntegerRepresentativeTree.Tree.leaf 1934 representative_1934) (QuarticIntegerRepresentativeTree.Tree.leaf 1935 representative_1935))))) (QuarticIntegerRepresentativeTree.Tree.branch 1944 (QuarticIntegerRepresentativeTree.Tree.branch 1940 (QuarticIntegerRepresentativeTree.Tree.branch 1938 (QuarticIntegerRepresentativeTree.Tree.branch 1937 (QuarticIntegerRepresentativeTree.Tree.leaf 1936 representative_1936) (QuarticIntegerRepresentativeTree.Tree.leaf 1937 representative_1937)) (QuarticIntegerRepresentativeTree.Tree.branch 1939 (QuarticIntegerRepresentativeTree.Tree.leaf 1938 representative_1938) (QuarticIntegerRepresentativeTree.Tree.leaf 1939 representative_1939))) (QuarticIntegerRepresentativeTree.Tree.branch 1942 (QuarticIntegerRepresentativeTree.Tree.branch 1941 (QuarticIntegerRepresentativeTree.Tree.leaf 1940 representative_1940) (QuarticIntegerRepresentativeTree.Tree.leaf 1941 representative_1941)) (QuarticIntegerRepresentativeTree.Tree.branch 1943 (QuarticIntegerRepresentativeTree.Tree.leaf 1942 representative_1942) (QuarticIntegerRepresentativeTree.Tree.leaf 1943 representative_1943)))) (QuarticIntegerRepresentativeTree.Tree.branch 1948 (QuarticIntegerRepresentativeTree.Tree.branch 1946 (QuarticIntegerRepresentativeTree.Tree.branch 1945 (QuarticIntegerRepresentativeTree.Tree.leaf 1944 representative_1944) (QuarticIntegerRepresentativeTree.Tree.leaf 1945 representative_1945)) (QuarticIntegerRepresentativeTree.Tree.branch 1947 (QuarticIntegerRepresentativeTree.Tree.leaf 1946 representative_1946) (QuarticIntegerRepresentativeTree.Tree.leaf 1947 representative_1947))) (QuarticIntegerRepresentativeTree.Tree.branch 1950 (QuarticIntegerRepresentativeTree.Tree.branch 1949 (QuarticIntegerRepresentativeTree.Tree.leaf 1948 representative_1948) (QuarticIntegerRepresentativeTree.Tree.leaf 1949 representative_1949)) (QuarticIntegerRepresentativeTree.Tree.branch 1951 (QuarticIntegerRepresentativeTree.Tree.leaf 1950 representative_1950) (QuarticIntegerRepresentativeTree.Tree.leaf 1951 representative_1951)))))) (QuarticIntegerRepresentativeTree.Tree.branch 1968 (QuarticIntegerRepresentativeTree.Tree.branch 1960 (QuarticIntegerRepresentativeTree.Tree.branch 1956 (QuarticIntegerRepresentativeTree.Tree.branch 1954 (QuarticIntegerRepresentativeTree.Tree.branch 1953 (QuarticIntegerRepresentativeTree.Tree.leaf 1952 representative_1952) (QuarticIntegerRepresentativeTree.Tree.leaf 1953 representative_1953)) (QuarticIntegerRepresentativeTree.Tree.branch 1955 (QuarticIntegerRepresentativeTree.Tree.leaf 1954 representative_1954) (QuarticIntegerRepresentativeTree.Tree.leaf 1955 representative_1955))) (QuarticIntegerRepresentativeTree.Tree.branch 1958 (QuarticIntegerRepresentativeTree.Tree.branch 1957 (QuarticIntegerRepresentativeTree.Tree.leaf 1956 representative_1956) (QuarticIntegerRepresentativeTree.Tree.leaf 1957 representative_1957)) (QuarticIntegerRepresentativeTree.Tree.branch 1959 (QuarticIntegerRepresentativeTree.Tree.leaf 1958 representative_1958) (QuarticIntegerRepresentativeTree.Tree.leaf 1959 representative_1959)))) (QuarticIntegerRepresentativeTree.Tree.branch 1964 (QuarticIntegerRepresentativeTree.Tree.branch 1962 (QuarticIntegerRepresentativeTree.Tree.branch 1961 (QuarticIntegerRepresentativeTree.Tree.leaf 1960 representative_1960) (QuarticIntegerRepresentativeTree.Tree.leaf 1961 representative_1961)) (QuarticIntegerRepresentativeTree.Tree.branch 1963 (QuarticIntegerRepresentativeTree.Tree.leaf 1962 representative_1962) (QuarticIntegerRepresentativeTree.Tree.leaf 1963 representative_1963))) (QuarticIntegerRepresentativeTree.Tree.branch 1966 (QuarticIntegerRepresentativeTree.Tree.branch 1965 (QuarticIntegerRepresentativeTree.Tree.leaf 1964 representative_1964) (QuarticIntegerRepresentativeTree.Tree.leaf 1965 representative_1965)) (QuarticIntegerRepresentativeTree.Tree.branch 1967 (QuarticIntegerRepresentativeTree.Tree.leaf 1966 representative_1966) (QuarticIntegerRepresentativeTree.Tree.leaf 1967 representative_1967))))) (QuarticIntegerRepresentativeTree.Tree.branch 1976 (QuarticIntegerRepresentativeTree.Tree.branch 1972 (QuarticIntegerRepresentativeTree.Tree.branch 1970 (QuarticIntegerRepresentativeTree.Tree.branch 1969 (QuarticIntegerRepresentativeTree.Tree.leaf 1968 representative_1968) (QuarticIntegerRepresentativeTree.Tree.leaf 1969 representative_1969)) (QuarticIntegerRepresentativeTree.Tree.branch 1971 (QuarticIntegerRepresentativeTree.Tree.leaf 1970 representative_1970) (QuarticIntegerRepresentativeTree.Tree.leaf 1971 representative_1971))) (QuarticIntegerRepresentativeTree.Tree.branch 1974 (QuarticIntegerRepresentativeTree.Tree.branch 1973 (QuarticIntegerRepresentativeTree.Tree.leaf 1972 representative_1972) (QuarticIntegerRepresentativeTree.Tree.leaf 1973 representative_1973)) (QuarticIntegerRepresentativeTree.Tree.branch 1975 (QuarticIntegerRepresentativeTree.Tree.leaf 1974 representative_1974) (QuarticIntegerRepresentativeTree.Tree.leaf 1975 representative_1975)))) (QuarticIntegerRepresentativeTree.Tree.branch 1980 (QuarticIntegerRepresentativeTree.Tree.branch 1978 (QuarticIntegerRepresentativeTree.Tree.branch 1977 (QuarticIntegerRepresentativeTree.Tree.leaf 1976 representative_1976) (QuarticIntegerRepresentativeTree.Tree.leaf 1977 representative_1977)) (QuarticIntegerRepresentativeTree.Tree.branch 1979 (QuarticIntegerRepresentativeTree.Tree.leaf 1978 representative_1978) (QuarticIntegerRepresentativeTree.Tree.leaf 1979 representative_1979))) (QuarticIntegerRepresentativeTree.Tree.branch 1982 (QuarticIntegerRepresentativeTree.Tree.branch 1981 (QuarticIntegerRepresentativeTree.Tree.leaf 1980 representative_1980) (QuarticIntegerRepresentativeTree.Tree.leaf 1981 representative_1981)) (QuarticIntegerRepresentativeTree.Tree.branch 1983 (QuarticIntegerRepresentativeTree.Tree.leaf 1982 representative_1982) (QuarticIntegerRepresentativeTree.Tree.leaf 1983 representative_1983)))))))
theorem accepted_030 : All validRep tree_030 := ⟨⟨⟨⟨⟨⟨coefficient_1920,coefficient_1921⟩,⟨coefficient_1922,coefficient_1923⟩⟩,⟨⟨coefficient_1924,coefficient_1925⟩,⟨coefficient_1926,coefficient_1927⟩⟩⟩,⟨⟨⟨coefficient_1928,coefficient_1929⟩,⟨coefficient_1930,coefficient_1931⟩⟩,⟨⟨coefficient_1932,coefficient_1933⟩,⟨coefficient_1934,coefficient_1935⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_1936,coefficient_1937⟩,⟨coefficient_1938,coefficient_1939⟩⟩,⟨⟨coefficient_1940,coefficient_1941⟩,⟨coefficient_1942,coefficient_1943⟩⟩⟩,⟨⟨⟨coefficient_1944,coefficient_1945⟩,⟨coefficient_1946,coefficient_1947⟩⟩,⟨⟨coefficient_1948,coefficient_1949⟩,⟨coefficient_1950,coefficient_1951⟩⟩⟩⟩⟩,⟨⟨⟨⟨⟨coefficient_1952,coefficient_1953⟩,⟨coefficient_1954,coefficient_1955⟩⟩,⟨⟨coefficient_1956,coefficient_1957⟩,⟨coefficient_1958,coefficient_1959⟩⟩⟩,⟨⟨⟨coefficient_1960,coefficient_1961⟩,⟨coefficient_1962,coefficient_1963⟩⟩,⟨⟨coefficient_1964,coefficient_1965⟩,⟨coefficient_1966,coefficient_1967⟩⟩⟩⟩,⟨⟨⟨⟨coefficient_1968,coefficient_1969⟩,⟨coefficient_1970,coefficient_1971⟩⟩,⟨⟨coefficient_1972,coefficient_1973⟩,⟨coefficient_1974,coefficient_1975⟩⟩⟩,⟨⟨⟨coefficient_1976,coefficient_1977⟩,⟨coefficient_1978,coefficient_1979⟩⟩,⟨⟨coefficient_1980,coefficient_1981⟩,⟨coefficient_1982,coefficient_1983⟩⟩⟩⟩⟩⟩
end BilayerDressed.QuarticIntegerSpatialRepresentatives64
