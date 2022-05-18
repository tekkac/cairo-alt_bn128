from typing import List

from starkware.cairo.common.math_utils import as_int

PRIME = 2 ** 251 + 17 * 2 ** 192 + 1
ALTBN_PRIME = 0x30644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd47

def split(num: int) -> List[int]:
    BASE = 2 ** 86
    a = []
    for _ in range(3):
        num, residue = divmod(num, BASE)
        a.append(residue)
    assert num == 0
    return a

def pack(z):
    limbs = z.d0, z.d1, z.d2
    return sum(as_int(limb, PRIME) * 2 ** (86 * i) for i, limb in enumerate(limbs)) % ALTBN_PRIME

def print_fq(name, e): 
    print(name, pack(e))

def parse_fq2(e):
    e0,e1 = pack(e.e0), pack(e.e1)
    return [e0 , e1]

def print_fq2(name, e):
    res = parse_fq2(e)
    print(name, res)

def parse_fq12(e):
    e0,e1,e2,e3 = pack(e.e0), pack(e.e1), pack(e.e2), pack(e.e3)
    e4,e5,e6,e7 = pack(e.e4), pack(e.e5), pack(e.e6), pack(e.e7)
    e8,e9,eA,eB = pack(e.e8), pack(e.e9), pack(e.eA), pack(e.eB)
    return [e0,e1,e2,e3,e4,e5,e6,e7,e8,e9,eA,eB]

def parse_ufq23(e):
    e00,e01,e02,e03 = pack(e.e00), pack(e.e01), pack(e.e02), pack(e.e03)
    e04,e05,e06,e07 = pack(e.e04), pack(e.e05), pack(e.e06), pack(e.e07)
    e08,e09,e0A,e0B = pack(e.e08), pack(e.e09), pack(e.e0A), pack(e.e0B)
    e0C,e0D,e0E,e0F = pack(e.e0C), pack(e.e0D), pack(e.e0A), pack(e.e0B)
    e10,e11,e12,e13 = pack(e.e10), pack(e.e11), pack(e.e12), pack(e.e13)
    e14,e15,e16     = pack(e.e14), pack(e.e15), pack(e.e16)
    
    return [e00,e01,e02,e03,e04,e05,e06,e07,e08,e09,e0A,e0B,
            e0C,e0D,e0E,e0F,e10,e11,e12,e13,e14,e15,e16]

def print_fq12(name, e):
    res = parse_fq12(e)
    print(name, res)

def print_g1(name, e):
    print(name)
    print_fq("  x", e.x) 
    print_fq("  y", e.y) 

def print_g2(name, e):
    print(name)
    print_fq2("  x", e.x) 
    print_fq2("  y", e.y) 

def print_g12(name, e):
    print(name)
    print_fq12("  x", e.x) 
    print_fq12("  y", e.y) 