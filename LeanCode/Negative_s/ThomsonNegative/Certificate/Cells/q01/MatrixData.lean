import ThomsonNegative.Certificate.MatrixCellKernel
import ThomsonNegative.Certificate.Cells.q01.Factors
import ThomsonNegative.Certificate.Cells.q01.ResidualData
import ThomsonNegative.Certificate.Cells.q01.Stored0
import ThomsonNegative.Certificate.Cells.q01.Stored1
import ThomsonNegative.Certificate.Cells.q01.Stored2
import ThomsonNegative.Certificate.Cells.q01.Stored3
import ThomsonNegative.Certificate.Cells.q01.Stored4
import ThomsonNegative.Certificate.Cells.q01.Stored5
import ThomsonNegative.Certificate.Cells.q01.Stored6
import ThomsonNegative.Certificate.Cells.q01.Stored7

namespace ThomsonNegative.Certificate.Cells.q01
noncomputable def matrixData : MatrixCell where
  metric := fun b => [metric0, metric1, metric2, metric3, metric4, metric5, metric6, metric7].getD b metric0
  factor := fun b r => ([factors0, factors1, factors2, factors3, factors4, factors5, factors6, factors7].getD b []).getD r ([metric0, metric1, metric2, metric3, metric4, metric5, metric6, metric7].getD b metric0)
  checkpoint := fun b => [checkpoint0, checkpoint1, checkpoint2, checkpoint3, checkpoint4, checkpoint5, checkpoint6, checkpoint7].getD b []
  residualCheckpoint := residualCheckpoint
end ThomsonNegative.Certificate.Cells.q01
