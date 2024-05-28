# 2ControlVerification

This repository is a formal verification of the paper:
[_Optimal Implementation of Quantum Gates with Two Controls_](https://www.sciencedirect.com/science/article/pii/S0024379524001356).

All work is derivative of YT Jeong's original work. The fundamental linear
algebra and quantum concepts are taken from
[QuantumLib](https://github.com/inQWIRE/QuantumLib).

## Project Structure

The lemmas found in the main body of the paper (sections 3 through 7) can be
found in `Main.v`.

The `Appendix/` subdirectory contains proofs for the lemmas found in the
[appendix of the paper](https://www.sciencedirect.com/science/article/pii/S0024379524001356#se0090).

- Appendix 1: SquareMatrices
- Appendix 2: UnitaryMatrices
- Appendix 3: Swaps
- Appendix 4: Vectors
- Appendix 5: ControlledUnitaries
- Appendix 6: TensorProducts
- Appendix 7: OtherProperties

The `Helpers/` subdirectory contains proofs for some helper lemmas used in
proving parts of the appendix or main body of the paper:

- AlgebraHelpers - Helper lemmas having to do with real and complex numbers.
- UnitaryHelpers - Helper lemmas having to do with unitary matrices.
- EigenvalueHelpers - Helper lemmas having to do with eigenvalues, with
  hermitian and positive semi-definite matrices.
- ExplicitDecompositions - Helper lemmas for expanding fixed size calculations.
- GateHelpers - Helper lemmas for dealing with quantum gates.
- MatrixHelpers - Helper lemmas for matrix calculations.
- QubitHelpers - Helper lemmas for unit vectors.
- SwapHelpers - Helper lemmas for properties of swaps.
- PartialTraceDefinitions - Adding the functions for tracing out qubits, and
  properties of the function.
- TraceoutHelpers - Contains helper lemmas for tracing out qubits.
