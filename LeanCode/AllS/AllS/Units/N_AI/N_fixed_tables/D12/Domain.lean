import AllS.Units.N_AI.N_fixed_tables.D12.Data
import AllS.Units.N_AI.N_fixed_tables.LinearSupport
import AllS.Units.N_AI.N_fixed_tables.TableDenominators.Entry000
import AllS.Units.N_AI.N_fixed_tables.TableDenominators.Entry001
import AllS.Units.N_AI.N_fixed_tables.TableDenominators.Entry002
import AllS.Units.N_AI.N_fixed_tables.TableDenominators.Entry003
import AllS.Units.N_AI.N_fixed_tables.TableDenominators.Entry004
import AllS.Units.N_AI.N_fixed_tables.TableDenominators.Entry005
import AllS.Units.N_AI.N_fixed_tables.TableDenominators.Entry006
import AllS.Units.N_AI.N_fixed_tables.TableDenominators.Entry007
import AllS.Units.N_AI.N_fixed_tables.TableDenominators.Entry008
import AllS.Units.N_AI.N_fixed_tables.TableDenominators.Entry009
import AllS.Units.N_AI.N_fixed_tables.TableDenominators.Entry010
import AllS.Units.N_AI.N_fixed_tables.TableDenominators.Entry011
import AllS.Units.N_AI.N_fixed_tables.TableDenominators.Entry012
import AllS.Units.N_AI.N_fixed_tables.TableDenominators.Entry013
import AllS.Units.N_AI.N_fixed_tables.TableDenominators.Entry014
import AllS.Units.N_AI.N_fixed_tables.TableDenominators.Entry015
import AllS.Units.N_AI.N_fixed_tables.TableDenominators.Entry016
import AllS.Units.N_AI.N_fixed_tables.TableDenominators.Entry017
import AllS.Units.N_AI.N_fixed_tables.TableDenominators.Entry018
import AllS.Units.N_AI.N_fixed_tables.TableDenominators.Entry019
import AllS.Units.N_AI.N_fixed_tables.TableDenominators.Entry020
import AllS.Units.N_AI.N_fixed_tables.TableDenominators.Entry021
import AllS.Units.N_AI.N_fixed_tables.TableDenominators.Entry022
import AllS.Units.N_AI.N_fixed_tables.TableDenominators.Entry023
import AllS.Units.N_AI.N_fixed_tables.TableDenominators.Entry024
noncomputable section
open scoped BigOperators
open Blueprint.CAP Blueprint.CAP.FixedTableDenominators Blueprint.Thomson.Finite
namespace Blueprint.CAP.FixedTables.D12
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem commonDenominator_nonzero (a : ℝ) (ha : physical a) : evalRationalList commonDenominator a≠0 := by
  exact common12_nonzero a ha
theorem tableDenominators_nonzero (a : ℝ) (ha : physical a) (j : Fin 100) : evalRationalList (tableDenominators j) a≠0 := by
  fin_cases j
  · change evalRationalList tableDen000 a≠0
    exact tableDen000_nonzero a ha
  · change evalRationalList tableDen000 a≠0
    exact tableDen000_nonzero a ha
  · change evalRationalList tableDen000 a≠0
    exact tableDen000_nonzero a ha
  · change evalRationalList tableDen000 a≠0
    exact tableDen000_nonzero a ha
  · change evalRationalList tableDen000 a≠0
    exact tableDen000_nonzero a ha
  · change evalRationalList tableDen000 a≠0
    exact tableDen000_nonzero a ha
  · change evalRationalList tableDen000 a≠0
    exact tableDen000_nonzero a ha
  · change evalRationalList tableDen000 a≠0
    exact tableDen000_nonzero a ha
  · change evalRationalList tableDen000 a≠0
    exact tableDen000_nonzero a ha
  · change evalRationalList tableDen000 a≠0
    exact tableDen000_nonzero a ha
  · change evalRationalList tableDen000 a≠0
    exact tableDen000_nonzero a ha
  · change evalRationalList tableDen001 a≠0
    exact tableDen001_nonzero a ha
  · change evalRationalList tableDen002 a≠0
    exact tableDen002_nonzero a ha
  · change evalRationalList tableDen003 a≠0
    exact tableDen003_nonzero a ha
  · change evalRationalList tableDen003 a≠0
    exact tableDen003_nonzero a ha
  · change evalRationalList tableDen004 a≠0
    exact tableDen004_nonzero a ha
  · change evalRationalList tableDen005 a≠0
    exact tableDen005_nonzero a ha
  · change evalRationalList tableDen006 a≠0
    exact tableDen006_nonzero a ha
  · change evalRationalList tableDen004 a≠0
    exact tableDen004_nonzero a ha
  · change evalRationalList tableDen007 a≠0
    exact tableDen007_nonzero a ha
  · change evalRationalList tableDen008 a≠0
    exact tableDen008_nonzero a ha
  · change evalRationalList tableDen009 a≠0
    exact tableDen009_nonzero a ha
  · change evalRationalList tableDen006 a≠0
    exact tableDen006_nonzero a ha
  · change evalRationalList tableDen010 a≠0
    exact tableDen010_nonzero a ha
  · change evalRationalList tableDen006 a≠0
    exact tableDen006_nonzero a ha
  · change evalRationalList tableDen011 a≠0
    exact tableDen011_nonzero a ha
  · change evalRationalList tableDen012 a≠0
    exact tableDen012_nonzero a ha
  · change evalRationalList tableDen008 a≠0
    exact tableDen008_nonzero a ha
  · change evalRationalList tableDen005 a≠0
    exact tableDen005_nonzero a ha
  · change evalRationalList tableDen012 a≠0
    exact tableDen012_nonzero a ha
  · change evalRationalList tableDen006 a≠0
    exact tableDen006_nonzero a ha
  · change evalRationalList tableDen013 a≠0
    exact tableDen013_nonzero a ha
  · change evalRationalList tableDen005 a≠0
    exact tableDen005_nonzero a ha
  · change evalRationalList tableDen014 a≠0
    exact tableDen014_nonzero a ha
  · change evalRationalList tableDen005 a≠0
    exact tableDen005_nonzero a ha
  · change evalRationalList tableDen008 a≠0
    exact tableDen008_nonzero a ha
  · change evalRationalList tableDen006 a≠0
    exact tableDen006_nonzero a ha
  · change evalRationalList tableDen015 a≠0
    exact tableDen015_nonzero a ha
  · change evalRationalList tableDen009 a≠0
    exact tableDen009_nonzero a ha
  · change evalRationalList tableDen016 a≠0
    exact tableDen016_nonzero a ha
  · change evalRationalList tableDen000 a≠0
    exact tableDen000_nonzero a ha
  · change evalRationalList tableDen017 a≠0
    exact tableDen017_nonzero a ha
  · change evalRationalList tableDen017 a≠0
    exact tableDen017_nonzero a ha
  · change evalRationalList tableDen018 a≠0
    exact tableDen018_nonzero a ha
  · change evalRationalList tableDen019 a≠0
    exact tableDen019_nonzero a ha
  · change evalRationalList tableDen017 a≠0
    exact tableDen017_nonzero a ha
  · change evalRationalList tableDen020 a≠0
    exact tableDen020_nonzero a ha
  · change evalRationalList tableDen017 a≠0
    exact tableDen017_nonzero a ha
  · change evalRationalList tableDen017 a≠0
    exact tableDen017_nonzero a ha
  · change evalRationalList tableDen017 a≠0
    exact tableDen017_nonzero a ha
  · change evalRationalList tableDen017 a≠0
    exact tableDen017_nonzero a ha
  · change evalRationalList tableDen021 a≠0
    exact tableDen021_nonzero a ha
  · change evalRationalList tableDen017 a≠0
    exact tableDen017_nonzero a ha
  · change evalRationalList tableDen017 a≠0
    exact tableDen017_nonzero a ha
  · change evalRationalList tableDen017 a≠0
    exact tableDen017_nonzero a ha
  · change evalRationalList tableDen017 a≠0
    exact tableDen017_nonzero a ha
  · change evalRationalList tableDen017 a≠0
    exact tableDen017_nonzero a ha
  · change evalRationalList tableDen017 a≠0
    exact tableDen017_nonzero a ha
  · change evalRationalList tableDen021 a≠0
    exact tableDen021_nonzero a ha
  · change evalRationalList tableDen021 a≠0
    exact tableDen021_nonzero a ha
  · change evalRationalList tableDen017 a≠0
    exact tableDen017_nonzero a ha
  · change evalRationalList tableDen017 a≠0
    exact tableDen017_nonzero a ha
  · change evalRationalList tableDen017 a≠0
    exact tableDen017_nonzero a ha
  · change evalRationalList tableDen021 a≠0
    exact tableDen021_nonzero a ha
  · change evalRationalList tableDen021 a≠0
    exact tableDen021_nonzero a ha
  · change evalRationalList tableDen017 a≠0
    exact tableDen017_nonzero a ha
  · change evalRationalList tableDen017 a≠0
    exact tableDen017_nonzero a ha
  · change evalRationalList tableDen021 a≠0
    exact tableDen021_nonzero a ha
  · change evalRationalList tableDen017 a≠0
    exact tableDen017_nonzero a ha
  · change evalRationalList tableDen017 a≠0
    exact tableDen017_nonzero a ha
  · change evalRationalList tableDen017 a≠0
    exact tableDen017_nonzero a ha
  · change evalRationalList tableDen021 a≠0
    exact tableDen021_nonzero a ha
  · change evalRationalList tableDen017 a≠0
    exact tableDen017_nonzero a ha
  · change evalRationalList tableDen017 a≠0
    exact tableDen017_nonzero a ha
  · change evalRationalList tableDen017 a≠0
    exact tableDen017_nonzero a ha
  · change evalRationalList tableDen017 a≠0
    exact tableDen017_nonzero a ha
  · change evalRationalList tableDen017 a≠0
    exact tableDen017_nonzero a ha
  · change evalRationalList tableDen017 a≠0
    exact tableDen017_nonzero a ha
  · change evalRationalList tableDen017 a≠0
    exact tableDen017_nonzero a ha
  · change evalRationalList tableDen017 a≠0
    exact tableDen017_nonzero a ha
  · change evalRationalList tableDen017 a≠0
    exact tableDen017_nonzero a ha
  · change evalRationalList tableDen017 a≠0
    exact tableDen017_nonzero a ha
  · change evalRationalList tableDen017 a≠0
    exact tableDen017_nonzero a ha
  · change evalRationalList tableDen017 a≠0
    exact tableDen017_nonzero a ha
  · change evalRationalList tableDen017 a≠0
    exact tableDen017_nonzero a ha
  · change evalRationalList tableDen017 a≠0
    exact tableDen017_nonzero a ha
  · change evalRationalList tableDen017 a≠0
    exact tableDen017_nonzero a ha
  · change evalRationalList tableDen017 a≠0
    exact tableDen017_nonzero a ha
  · change evalRationalList tableDen017 a≠0
    exact tableDen017_nonzero a ha
  · change evalRationalList tableDen017 a≠0
    exact tableDen017_nonzero a ha
  · change evalRationalList tableDen017 a≠0
    exact tableDen017_nonzero a ha
  · change evalRationalList tableDen017 a≠0
    exact tableDen017_nonzero a ha
  · change evalRationalList tableDen017 a≠0
    exact tableDen017_nonzero a ha
  · change evalRationalList tableDen017 a≠0
    exact tableDen017_nonzero a ha
  · change evalRationalList tableDen022 a≠0
    exact tableDen022_nonzero a ha
  · change evalRationalList tableDen023 a≠0
    exact tableDen023_nonzero a ha
  · change evalRationalList tableDen024 a≠0
    exact tableDen024_nonzero a ha
  · change evalRationalList tableDen017 a≠0
    exact tableDen017_nonzero a ha
  · change evalRationalList tableDen017 a≠0
    exact tableDen017_nonzero a ha
  · change evalRationalList tableDen017 a≠0
    exact tableDen017_nonzero a ha
theorem clearScale_real_nonzero : (clearScale:ℝ)≠0 := by exact_mod_cast (ne_of_gt clearScale_positive)
theorem tableScales_real_nonzero (j : Fin 100) : (tableScales j:ℝ)≠0 := by exact_mod_cast (ne_of_gt (tableScales_positive j))
theorem target_eval (a : ℝ) : evalIntegerList target a=(clearScale:ℝ)*evalRationalList commonDenominator a := by
  norm_num [evalIntegerList,target,clearScale,commonDenominator,evalRationalList,listPolynomial_cons,listPolynomial_nil]
  all_goals ring
#print axioms tableDenominators_nonzero
#print axioms target_eval
end Blueprint.CAP.FixedTables.D12
