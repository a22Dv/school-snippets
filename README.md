# sprog
![MIT](https://img.shields.io/badge/license-MIT-green?style=flat)


Some small programs based on school topics compiled into one repository.

## logical-evaluator
![C++23](https://img.shields.io/badge/C%2B%2B-23-blue?style=flat&logo=cplusplus&logoColor=white)

Takes a given expression as an argument, and outputs the truth table belonging to that expression.
To build it, run `make`, then run the resulting binary `./logeval <EXPR>`.

Sample output:

```
./logical-evaluator/logeval "A & B | C"
A   B   C   (A & B)   ((A & B) | C)
===================================
T   T   T      T            T
T   T   F      T            T
T   F   T      F            T
T   F   F      F            F
F   T   T      F            T
F   T   F      F            F
F   F   T      F            T
F   F   F      F            F
```

## z3mincirc.py
![Python](https://img.shields.io/badge/Python->=3.13-blue?style=flat&logo=python&logoColor=white)

Takes a given input and output as binary columns, and tries to solve for the smallest possible
circuit it takes to map the input to the output.

Sample output (With default configuration):

```
ATTEMPTING: 20 gate(s) - ['NAND', 'NOR', 'XNOR', 'XOR', 'AND', 'OR'] ...
ATTEMPT: 20 gate(s) - SAT.
G0: XNOR(I2, I2) -> 0xFFFF
G1: XOR(I0, I0) -> 0x0
G2: XNOR(I0, G1) -> 0x5555
G3: NOR(I0, I1) -> 0x1111
G4: XNOR(I0, I1) -> 0x9999
G5: NOR(I2, I3) -> 0xF
G6: OR(G4, G5) -> 0x999F
G7: XNOR(G3, G6) -> 0x7771
G8: NOR(I1, G7) -> 0x2
G9: AND(I2, G4) -> 0x9090
G10: NOR(G8, G9) -> 0x6F6D
G11: OR(I0, G7) -> 0xFFFB
G12: OR(I3, G6) -> 0xFF9F
G13: NOR(G7, G8) -> 0x888C
G14: OR(I1, G10) -> 0xEFED
G15: XOR(I1, I2) -> 0x3C3C
G16: XNOR(G5, G13) -> 0x777C
G17: NOR(I0, G9) -> 0x4545
G18: XNOR(I2, G1) -> 0xF0F
G19: XNOR(I1, I1) -> 0xFFFF
A: G14
B: G12
C: G11
D: G10
E: G17
F: G7
G: G16
```

Requires `z3-solver`. Install it using `pip`.
