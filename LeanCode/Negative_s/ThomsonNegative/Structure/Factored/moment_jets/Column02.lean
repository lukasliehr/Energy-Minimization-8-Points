import ThomsonNegative.Structure.Factored.moment_jets.Config
namespace ThomsonNegative.Structure.Factored.moment_jets
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
theorem column_2 : columnCheck 2 = true := by decide +kernel
end ThomsonNegative.Structure.Factored.moment_jets
