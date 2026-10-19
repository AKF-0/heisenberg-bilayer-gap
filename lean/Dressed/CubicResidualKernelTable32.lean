import Dressed.CubicResidualCoefficients
noncomputable section
open scoped BigOperators
namespace BilayerDressed.CubicResidualSeedCoefficients
open BilayerGap BilayerDressed.CubicResidualCoefficients
set_option maxHeartbeats 0
set_option maxRecDepth 200000
def walkTable32 (q : Torus.Vertex 4 2) : Fin 3 → ℕ :=
  (![![![0,0,0],![1,0,10],![0,2,0],![1,0,10]],
    ![![1,0,9],![0,2,0],![0,0,6],![0,2,0]],
    ![![0,1,0],![0,0,3],![0,0,0],![0,0,3]],
    ![![0,0,1],![0,0,0],![0,0,0],![0,0,0]],
    ![![0,0,0],![0,0,0],![0,0,0],![0,0,0]],
    ![![0,0,1],![0,0,0],![0,0,0],![0,0,0]],
    ![![0,1,0],![0,0,3],![0,0,0],![0,0,3]],
    ![![1,0,9],![0,2,0],![0,0,6],![0,2,0]]]) q.1 q.2

def kernelTable32 (q : Torus.Vertex 4 2) : Fin 3 → ℚ :=
  (![![![0,0,0],![(-1/4),(-1/8),(-5/32)],![0,(1/4),(1/8)],![(-1/4),(-1/8),(-5/32)]],
    ![![(-1/4),(-1/8),(-5/64)],![0,(1/4),(1/8)],![0,0,(-15/32)],![0,(1/4),(1/8)]],
    ![![0,(1/8),(1/16)],![0,0,(-15/64)],![0,0,0],![0,0,(-15/64)]],
    ![![0,0,(-5/64)],![0,0,0],![0,0,0],![0,0,0]],
    ![![0,0,0],![0,0,0],![0,0,0],![0,0,0]],
    ![![0,0,(-5/64)],![0,0,0],![0,0,0],![0,0,0]],
    ![![0,(1/8),(1/16)],![0,0,(-15/64)],![0,0,0],![0,0,(-15/64)]],
    ![![(-1/4),(-1/8),(-5/64)],![0,(1/4),(1/8)],![0,0,(-15/32)],![0,(1/4),(1/8)]]]) q.1 q.2

theorem walk_table32 : ∀ q : Torus.Vertex 4 2,
    SeedGraphs.adjacencyNat 4 2 0 q=walkTable32 q 0 ∧
      CubicSeedChecks.offWalk2 4 2 0 q=walkTable32 q 1 ∧
      CubicSeedChecks.walk3 4 2 0 q=walkTable32 q 2 := by
  intro ⟨x,y⟩
  fin_cases x <;> fin_cases y <;> decide +kernel

theorem kernel_table32 : ∀ q : Torus.Vertex 4 2,
    k1 4 2 q=kernelTable32 q 0 ∧ k2 4 2 q=kernelTable32 q 1 ∧
      k3 4 2 q=kernelTable32 q 2 := by
  intro q
  simp only [k1,k2,k3,(walk_table32 q).1,(walk_table32 q).2.1,(walk_table32 q).2.2]
  rcases q with ⟨x,y⟩
  fin_cases x <;> fin_cases y <;> decide +kernel

#check kernel_table32
end BilayerDressed.CubicResidualSeedCoefficients
