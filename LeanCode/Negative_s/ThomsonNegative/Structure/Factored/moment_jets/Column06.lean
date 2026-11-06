import ThomsonNegative.Structure.Factored.moment_jets.Config
namespace ThomsonNegative.Structure.Factored.moment_jets
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
theorem column_6 : columnCheck 6 = true := by decide +kernel
end ThomsonNegative.Structure.Factored.moment_jets
