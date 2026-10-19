import Dressed.CubicResidualCoefficients
noncomputable section
open scoped BigOperators
namespace BilayerDressed.CubicResidualSeedCoefficients
open BilayerGap BilayerDressed.CubicResidualCoefficients
set_option maxHeartbeats 0
set_option maxRecDepth 200000
def walkTable16 (q : Torus.Vertex 2 2) : Fin 3 → ℕ :=
  (![![![0,0,0],![1,0,10],![0,2,0],![1,0,10]],
    ![![1,0,10],![0,2,0],![0,0,6],![0,2,0]],
    ![![0,2,0],![0,0,6],![0,0,0],![0,0,6]],
    ![![1,0,10],![0,2,0],![0,0,6],![0,2,0]]]) q.1 q.2

def kernelTable16 (q : Torus.Vertex 2 2) : Fin 3 → ℚ :=
  (![![![0,0,0],![(-1/4),(-1/8),(-5/32)],![0,(1/4),(1/8)],![(-1/4),(-1/8),(-5/32)]],
    ![![(-1/4),(-1/8),(-5/32)],![0,(1/4),(1/8)],![0,0,(-15/32)],![0,(1/4),(1/8)]],
    ![![0,(1/4),(1/8)],![0,0,(-15/32)],![0,0,0],![0,0,(-15/32)]],
    ![![(-1/4),(-1/8),(-5/32)],![0,(1/4),(1/8)],![0,0,(-15/32)],![0,(1/4),(1/8)]]]) q.1 q.2

theorem walk_table16 : ∀ q : Torus.Vertex 2 2,
    SeedGraphs.adjacencyNat 2 2 0 q=walkTable16 q 0 ∧
      CubicSeedChecks.offWalk2 2 2 0 q=walkTable16 q 1 ∧
      CubicSeedChecks.walk3 2 2 0 q=walkTable16 q 2 := by
  intro ⟨x,y⟩
  fin_cases x <;> fin_cases y <;> decide +kernel

theorem kernel_table16 : ∀ q : Torus.Vertex 2 2,
    k1 2 2 q=kernelTable16 q 0 ∧ k2 2 2 q=kernelTable16 q 1 ∧
      k3 2 2 q=kernelTable16 q 2 := by
  intro q
  simp only [k1,k2,k3,(walk_table16 q).1,(walk_table16 q).2.1,(walk_table16 q).2.2]
  rcases q with ⟨x,y⟩
  fin_cases x <;> fin_cases y <;> decide +kernel

#check kernel_table16
end BilayerDressed.CubicResidualSeedCoefficients
