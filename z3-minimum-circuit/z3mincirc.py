# z3mincirc.py

from z3 import *

# fmt: off
# Column-wise. 4-bit input, 7-bit output. 
COLSIZE = 16
INPUTS = [BitVecVal(v, COLSIZE) for v in (0xAAAA, 0xCCCC, 0xF0F0, 0xFF00)] # Standard.
OUTPUTS = [BitVecVal(v, COLSIZE) for v in (0x3ED, 0x39F, 0x3FB, 0x36D, 0x145, 0x371, 0x37C)]
OUTPUT_MASKS = [BitVecVal(0x03FF, COLSIZE) for _ in range(len(OUTPUTS))]
# fmt: on


INPUT_BITSIZE = len(INPUTS)
OUTPUT_BITSIZE = len(OUTPUTS)


# Gatecount includes the final nodes of the result.
MAX_GATECOUNT = 20
GATES = ["NAND", "NOR", "XNOR", "XOR", "AND", "OR"]


def egate(v1: BitVecRef, v2: BitVecRef, op: BitVecRef):

    # fmt: off
    return If(op == 0, ~(v1 & v2),
           If(op == 1, ~(v1 | v2),
           If(op == 2, ~(v1 ^ v2),
           If(op == 3, v1 ^ v2, 
           If(op == 4, v1 & v2, v1 | v2)))))
    # fmt: on


def zsel(l, id: BitVecRef):
    e = l[0]
    for i in range(len(l)):
        e = If(i == id, l[i], e)
    return e


def pprintr(
    smodel: ModelRef,
    n: int,
    gt: list[BitVecRef],
    gr: list[BitVecRef],
    gs1: list[BitVecRef],
    gs2: list[BitVecRef],
    gsr: list[BitVecRef],
    os: list[BitVecRef],
) -> None:
    for i in range(n):
        gid: str = GATES[smodel[gt[i]].as_long()]
        gr = f"0x{(smodel[gsr[i]].as_long()):X}"
        gs1n = smodel[gs1[i]].as_long()
        gs2n = smodel[gs2[i]].as_long()
        gs1ns = f"I{gs1n}" if gs1n < INPUT_BITSIZE else f"G{gs1n - INPUT_BITSIZE}"
        gs2ns = f"I{gs2n}" if gs2n < INPUT_BITSIZE else f"G{gs2n - INPUT_BITSIZE}"
        print(f"G{i}: {gid}({gs1ns}, {gs2ns}) -> {gr}")

    for i in range(OUTPUT_BITSIZE):
        sm = smodel[os[i]].as_long()
        sms = f"I{sm}" if sm < INPUT_BITSIZE else f"G{sm - INPUT_BITSIZE}"
        print(f"{chr(ord('A') + i)}: {sms}")


def main():
    for n in range(MAX_GATECOUNT, 0, -1):

        print(f"ATTEMPTING: {n} gate(s) - {GATES} ...")
        s = Then("simplify", "bit-blast", "sat").solver()

        gt = [BitVec(f"gt{i}", 4) for i in range(n)]
        gr = [BitVec(f"gr{i}", COLSIZE) for i in range(n)]

        # Constrain gate-type.
        s.add(And(gt[i] >= 0, gt[i] < len(GATES)) for i in range(n))

        gs1 = [BitVec(f"gs1_{i}", 8) for i in range(n)]
        gs2 = [BitVec(f"gs2_{i}", 8) for i in range(n)]
        os = [BitVec(f"os{i}", 8) for i in range(OUTPUT_BITSIZE)]
        s.add(And(os[i] >= 0, os[i] < INPUT_BITSIZE + n) for i in range(OUTPUT_BITSIZE))

        # Discard redundant permutations.
        s.add(And(gs1[i] <= gs2[i]) for i in range(n))

        mlist = INPUTS + gr
        for i in range(n):
            gti = gt[i]
            gi = INPUTS + gr[:i]
            gli = len(gi)

            # Limit gate stacking results
            # to chronological order. (Prevent forward-dependencies)
            s.add(And(gs1[i] >= 0, gs1[i] < gli))
            s.add(And(gs2[i] >= 0, gs2[i] < gli))

            # Assign results
            s.add(gr[i] == egate(zsel(gi, gs1[i]), zsel(gi, gs2[i]), gti))

        for i in range(OUTPUT_BITSIZE):
            sw = zsel(mlist, os[i])
            s.add(sw & OUTPUT_MASKS[i] == OUTPUTS[i] & OUTPUT_MASKS[i])

        if s.check() == unsat:
            print(f"ATTEMPT: {n} gate(s) - UNSAT.")
            break
        print(f"ATTEMPT: {n} gate(s) - SAT.")
        pprintr(s.model(), n, gt, gr, gs1, gs2, gr, os)


if __name__ == "__main__":
    main()
