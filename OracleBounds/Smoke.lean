import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

/-- Smoke test: the shared Mathlib is importable and `Real.binEntropy` exists. -/
example : Real.binEntropy 2⁻¹ = Real.log 2 := Real.binEntropy_two_inv
