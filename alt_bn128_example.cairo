%builtins output range_check
from starkware.cairo.common.serialize import serialize_word

from bigint import BigInt3, nondet_bigint3
from alt_bn128 import verify_ecdsa, mul_s_inv
from alt_bn128_def import N0, N1, N2, P0, P1, P2
from alt_bn128_ec import EcPoint, compute_doubling_slope, ec_double, ec_add, ec_mul, G1
from alt_bn128_pair import linefunc
from alt_bn128_field import is_zero

func G1two() -> (res : EcPoint):
    return (
        EcPoint(
        BigInt3(0x71ca8d3c208c16d87cfd3, 0x116da060561765e05aa45a, 0x30644e72e131a029b850),
        BigInt3(0x138fc7ff3ebf7a5a18a2c4, 0x3e5acaba7029a29a91278d, 0x15ed738c0e0a7c92e7845)))
end

func G1three() -> (res : EcPoint):
    return (
        EcPoint(
        BigInt3(0x38e679f2d355961915abf0, 0xaf2c6daf4564c57611c56, 0x769bf9ac56bea3ff4023),
        BigInt3(0x1c5b57cdf1ff3dd9fe2261, 0x2df2342191d4c6798ed02e, 0x2ab799bee0489429554fd)))
end

func G1negone() -> (res : EcPoint):
    return (
        EcPoint(
        BigInt3(0x1, 0x0, 0x0),
        BigInt3(0x31ca8d3c208c16d87cfd45, 0x16da060561765e05aa45a1, 0x30644e72e131a029b8504)))
end

func G1negtwo() -> (res : EcPoint):
    return (
        EcPoint(
        BigInt3(0x71ca8d3c208c16d87cfd3, 0x116da060561765e05aa45a, 0x30644e72e131a029b850),
        BigInt3(0x1e3ac53ce1cc9c7e645a83, 0x187f3b4af14cbb6b191e14, 0x1a76dae6d3272396d0cbe)))
end

func G1negthree() -> (res : EcPoint):
    return (
        EcPoint(
        BigInt3(0x38e679f2d355961915abf0, 0xaf2c6daf4564c57611c56, 0x769bf9ac56bea3ff4023),
        BigInt3(0x156f356e2e8cd8fe7edae6, 0x28e7d1e3cfa1978c1b7573, 0x5acb4b400e90c0063006)))
end

func linefunc_test{range_check_ptr}():
    alloc_locals
    let (local one : EcPoint) = G1()
    let (two : EcPoint) = G1two()
    let (three : EcPoint) = G1three()

    let (negone : EcPoint) = G1negone()
    let (negtwo : EcPoint) = G1negtwo()
    let (negthree : EcPoint) = G1negthree()

    # let (two : EcPoint) = ec_double(one)
    # let (three : EcPoint) = ec_mul(one, BigInt3(3, 0, 0))

    # let (negone : EcPoint) = ec_mul(one, BigInt3(N0 - 1, N1, N2))
    # let (negtwo : EcPoint) = ec_mul(one, BigInt3(N0 - 2, N1, N2))
    # let (negthree : EcPoint) = ec_mul(one, BigInt3(N0 - 3, N1, N2))

    let (val) = linefunc(one, two, one)
    let (val_is0) = is_zero(val)
    assert val_is0 = 1
    let (val) = linefunc(one, two, two)
    let (val_is0) = is_zero(val)
    assert val_is0 = 1
    let (val) = linefunc(one, two, three)
    let (val_is0) = is_zero(val)
    assert val_is0 = 0
    let (val) = linefunc(one, two, negthree)
    let (val_is0) = is_zero(val)
    assert val_is0 = 1
    let (val) = linefunc(one, negone, one)
    let (val_is0) = is_zero(val)
    assert val_is0 = 1
    let (val) = linefunc(one, negone, two)
    let (val_is0) = is_zero(val)
    assert val_is0 = 0
    let (val) = linefunc(one, negone, negone)
    let (val_is0) = is_zero(val)
    assert val_is0 = 1
    let (val) = linefunc(one, one, one)
    let (val_is0) = is_zero(val)
    assert val_is0 = 1
    let (val) = linefunc(one, one, two)
    let (val_is0) = is_zero(val)
    assert val_is0 = 0
    let (val) = linefunc(one, one, negtwo)
    let (val_is0) = is_zero(val)
    assert val_is0 = 1
    # assert linefunc(one, two, negthree) ==
    # assert linefunc(one, negone, one) ==
    # assert linefunc(one, negone, negone) ==
    # assert linefunc(one, negone, two) !=
    # assert linefunc(one, one, one) ==
    # assert linefunc(one, one, two) !=
    # assert linefunc(one, one, negtwo) ==
    return ()
end

func main{output_ptr : felt*, range_check_ptr}():
    # linefunc_test()

    %{
        import sys
        import os 
        cwd = os.getcwd()
        sys.path.append(cwd)

        from tmp.utils.alt_utils import FQ 
        print(FQ(1337))
    %}

    let public_key_pt = EcPoint(
        BigInt3(0xc505bebf0ed670fa5ae45, 0x36b2ae5bb3ea65786b2adb, 0x1aea85bef3a108a3322fb),
        BigInt3(0x123ebd558a24597cd41241, 0x1e6a1a0d4c134ea9b90bc8, 0x2bda5f6606e99ae96be86))

    let r = BigInt3(0x30fe324162d69e7a2df8a7, 0x21b6b44f128ec090ee24da, 0x2de2c2e65a3caab91185)
    let s = BigInt3(0xa21e2703c2b208405bff8, 0x10c6b092586c347bed269d, 0x1011f2d442e2c65ce89a)
    let msg_hash = BigInt3(
        0x19b120d29c1246446dfdd4, 0x3f1afd887d951181d25adc, 0x51daaedd17508efc249c)

    verify_ecdsa(public_key_pt=public_key_pt, msg_hash=msg_hash, r=r, s=s)
    return ()
end
