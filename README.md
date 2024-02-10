# 2ControlVerification
A proof verification of "Optimal Implementation of Quantum Gates with Two Controls".

All work is derivative of YT Jeongs original work on this verification.
The fundamental linear algebra and quantum concepts are taken from Robert Rand's QuantumLib library (https://github.com/inQWIRE/QuantumLib).

Helper Files: 

- AlgebraHelpers - Helper lemmas having to do with real and complex numbers. 
- EigenvalueHelpers - Helper lemmas having to do with eigenvalues, with hermitian and PSD matrices.
- ExplicitDecompositions - Helper lemmas for expanding fixed size calculations.
- GateHelpers - Helper lemmas for dealing with quantum gates. 
- MatrixHelpers - Helper lemmas for matrix calculations. 
- QubitHelpers - Helper lemmas for unit vectors.
- SwapHelpers - Helper lemmas for properties of swaps.
- SwapProperty - Particular swap property that takes a long time to compile.
- PartialTraceDefinitions - Adding the functions for tracing out qubits, and properties of the function.
- TraceoutHelpers - Contains helper lemmas for tracing out qubits.

Proof Appendixes:

- Appendix 1: SquareMatrices
- Appendix 2: UnitaryMatrices
- Appendix 3: Swaps
- Appendix 4: Vectors
- Appendix 5: ControlledUnitaries
- Appendix 6: TensorProducts
- Appendix 7: OtherProperties

Main Proof: 

- Lemma 3.2, 4.2 - Main