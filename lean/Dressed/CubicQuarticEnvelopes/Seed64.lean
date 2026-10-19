import Dressed.CubicQuarticEnvelopes.Batch01
import Dressed.CubicQuarticEnvelopes.Batch02
import Dressed.CubicQuarticEnvelopes.Batch03
import Dressed.CubicQuarticEnvelopes.Batch04
import Dressed.CubicQuarticEnvelopes.Batch05
import Dressed.CubicQuarticEnvelopes.Batch06
import Dressed.CubicQuarticEnvelopes.Batch07
import Dressed.CubicQuarticEnvelopes.Batch08
import Dressed.CubicQuarticEnvelopes.Batch09
import Dressed.CubicQuarticEnvelopes.Batch10
import Dressed.CubicQuarticEnvelopes.Batch11
import Dressed.CubicQuarticEnvelopes.Batch12
import Dressed.CubicQuarticEnvelopes.Batch13
import Dressed.CubicQuarticEnvelopes.Batch14
import Dressed.CubicQuarticEnvelopes.Batch15
import Dressed.CubicQuarticEnvelopes.Batch16
import Dressed.CubicQuarticEnvelopes.Batch17
import Dressed.CubicQuarticEnvelopes.Batch18
import Dressed.CubicQuarticEnvelopes.Batch19
import Dressed.CubicQuarticEnvelopes.Batch20
import Dressed.CubicQuarticEnvelopes.Batch21
import Dressed.CubicQuarticEnvelopes.Batch22
import Dressed.CubicQuarticEnvelopes.Batch23
import Dressed.CubicQuarticEnvelopes.Batch24
import Dressed.CubicQuarticEnvelopes.Batch25
import Dressed.CubicQuarticEnvelopes.Batch26
import Dressed.CubicQuarticEnvelopes.Batch27


/-! Source-order displayed rational envelopes only. Physical residual polynomial
identification is a separate theorem and is not assumed or asserted here. -/
noncomputable section
namespace BilayerDressed.CubicQuarticEnvelopes
open CubicResidualCoefficients CubicQuarticCoefficientBernstein
set_option maxRecDepth 200000

def entries64 : Fin 462 → Envelope := ![envelope0548, envelope0549, envelope0550, envelope0048, envelope0551, envelope0552, envelope0553, envelope0554, envelope0052, envelope0053, envelope0054, envelope0056, envelope0555, envelope0556, envelope0557, envelope0558, envelope0559, envelope0560, envelope0561, envelope0562, envelope0563, envelope0070, envelope0564, envelope0565, envelope0566, envelope0567, envelope0568, envelope0569, envelope0570, envelope0571, envelope0085, envelope0572, envelope0573, envelope0574, envelope0575, envelope0576, envelope0577, envelope0578, envelope0579, envelope0580, envelope0581, envelope0109, envelope0582, envelope0583, envelope0584, envelope0585, envelope0586, envelope0115, envelope0587, envelope0588, envelope0589, envelope0590, envelope0591, envelope0592, envelope0593, envelope0594, envelope0595, envelope0596, envelope0597, envelope0598, envelope0599, envelope0600, envelope0601, envelope0602, envelope0603, envelope0604, envelope0605, envelope0606, envelope0607, envelope0608, envelope0140, envelope0609, envelope0610, envelope0611, envelope0612, envelope0145, envelope0613, envelope0614, envelope0615, envelope0616, envelope0148, envelope0617, envelope0154, envelope0155, envelope0618, envelope0619, envelope0620, envelope0159, envelope0621, envelope0622, envelope0163, envelope0623, envelope0624, envelope0625, envelope0626, envelope0166, envelope0167, envelope0627, envelope0628, envelope0629, envelope0630, envelope0631, envelope0632, envelope0191, envelope0633, envelope0634, envelope0635, envelope0636, envelope0637, envelope0638, envelope0639, envelope0640, envelope0641, envelope0642, envelope0643, envelope0206, envelope0207, envelope0644, envelope0645, envelope0646, envelope0647, envelope0648, envelope0649, envelope0650, envelope0651, envelope0652, envelope0218, envelope0653, envelope0654, envelope0655, envelope0656, envelope0657, envelope0658, envelope0659, envelope0660, envelope0661, envelope0662, envelope0663, envelope0664, envelope0232, envelope0665, envelope0666, envelope0667, envelope0668, envelope0237, envelope0669, envelope0238, envelope0239, envelope0670, envelope0671, envelope0672, envelope0241, envelope0673, envelope0244, envelope0674, envelope0675, envelope0246, envelope0247, envelope0676, envelope0677, envelope0678, envelope0679, envelope0680, envelope0253, envelope0681, envelope0682, envelope0255, envelope0683, envelope0684, envelope0257, envelope0685, envelope0686, envelope0687, envelope0688, envelope0689, envelope0690, envelope0691, envelope0692, envelope0265, envelope0266, envelope0693, envelope0694, envelope0695, envelope0696, envelope0697, envelope0268, envelope0698, envelope0270, envelope0699, envelope0274, envelope0700, envelope0701, envelope0276, envelope0277, envelope0278, envelope0702, envelope0703, envelope0704, envelope0705, envelope0706, envelope0707, envelope0708, envelope0709, envelope0710, envelope0711, envelope0284, envelope0712, envelope0713, envelope0714, envelope0715, envelope0716, envelope0717, envelope0288, envelope0289, envelope0718, envelope0719, envelope0720, envelope0291, envelope0721, envelope0292, envelope0722, envelope0723, envelope0301, envelope0302, envelope0303, envelope0724, envelope0305, envelope0306, envelope0307, envelope0308, envelope0725, envelope0309, envelope0310, envelope0311, envelope0312, envelope0313, envelope0314, envelope0726, envelope0315, envelope0727, envelope0728, envelope0729, envelope0730, envelope0316, envelope0731, envelope0732, envelope0318, envelope0733, envelope0734, envelope0319, envelope0735, envelope0320, envelope0736, envelope0322, envelope0737, envelope0738, envelope0739, envelope0740, envelope0741, envelope0742, envelope0743, envelope0325, envelope0744, envelope0745, envelope0746, envelope0328, envelope0747, envelope0748, envelope0749, envelope0750, envelope0330, envelope0751, envelope0752, envelope0332, envelope0753, envelope0334, envelope0754, envelope0338, envelope0339, envelope0755, envelope0340, envelope0341, envelope0342, envelope0756, envelope0345, envelope0757, envelope0758, envelope0759, envelope0349, envelope0350, envelope0760, envelope0351, envelope0761, envelope0762, envelope0763, envelope0352, envelope0764, envelope0353, envelope0765, envelope0766, envelope0767, envelope0768, envelope0769, envelope0358, envelope0361, envelope0770, envelope0363, envelope0771, envelope0364, envelope0772, envelope0773, envelope0774, envelope0365, envelope0366, envelope0775, envelope0776, envelope0368, envelope0777, envelope0778, envelope0369, envelope0779, envelope0377, envelope0780, envelope0380, envelope0781, envelope0389, envelope0390, envelope0782, envelope0783, envelope0784, envelope0785, envelope0786, envelope0787, envelope0788, envelope0789, envelope0394, envelope0790, envelope0791, envelope0792, envelope0793, envelope0794, envelope0795, envelope0796, envelope0797, envelope0798, envelope0799, envelope0800, envelope0399, envelope0801, envelope0802, envelope0400, envelope0803, envelope0804, envelope0805, envelope0806, envelope0405, envelope0807, envelope0408, envelope0808, envelope0809, envelope0810, envelope0811, envelope0812, envelope0813, envelope0413, envelope0814, envelope0414, envelope0815, envelope0816, envelope0817, envelope0818, envelope0420, envelope0421, envelope0819, envelope0424, envelope0820, envelope0821, envelope0822, envelope0823, envelope0824, envelope0427, envelope0428, envelope0429, envelope0825, envelope0826, envelope0827, envelope0828, envelope0829, envelope0830, envelope0831, envelope0832, envelope0833, envelope0834, envelope0835, envelope0836, envelope0837, envelope0838, envelope0839, envelope0840, envelope0446, envelope0841, envelope0842, envelope0843, envelope0844, envelope0450, envelope0845, envelope0846, envelope0847, envelope0848, envelope0849, envelope0850, envelope0851, envelope0459, envelope0460, envelope0852, envelope0853, envelope0854, envelope0855, envelope0856, envelope0857, envelope0858, envelope0473, envelope0476, envelope0859, envelope0860, envelope0490, envelope0861, envelope0862, envelope0863, envelope0864, envelope0865, envelope0866, envelope0867, envelope0868, envelope0500, envelope0501, envelope0869, envelope0870, envelope0871, envelope0872, envelope0873, envelope0514, envelope0874, envelope0875, envelope0876, envelope0877, envelope0519, envelope0878, envelope0879, envelope0880, envelope0881, envelope0882, envelope0883, envelope0884, envelope0885, envelope0886, envelope0887, envelope0888, envelope0889, envelope0542, envelope0890, envelope0891]

def coefficients64 (i : Fin 462) : Fin 11 → ℚ := (entries64 i).coefficients

def upper64 (i : Fin 462) : ℚ := (entries64 i).upper

theorem bound64 (i : Fin 462) (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff (coefficients64 i) g| ≤ (upper64 i : ℝ) :=
  (entries64 i).bound g hg hmax

end BilayerDressed.CubicQuarticEnvelopes
