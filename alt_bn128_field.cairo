from starkware.cairo.common.bitwise import bitwise_and
from starkware.cairo.common.cairo_builtins import BitwiseBuiltin

from bigint import BASE, BigInt3, UnreducedBigInt3, UnreducedBigInt5, nondet_bigint3, bigint_mul
from alt_bn128_def import P0, P1, P2

# FIELD STRUCTURES
struct FQ2:
    member e0 : BigInt3
    member e1 : BigInt3
end

struct FQ12:
    member e0 : BigInt3
    member e1 : BigInt3
    member e2 : BigInt3
    member e3 : BigInt3
    member e4 : BigInt3
    member e5 : BigInt3
    member e6 : BigInt3
    member e7 : BigInt3
    member e8 : BigInt3
    member e9 : BigInt3
    member eA : BigInt3
    member eB : BigInt3
end

struct UnreducedFQ23:
    member e00 : UnreducedBigInt5
    member e01 : UnreducedBigInt5
    member e02 : UnreducedBigInt5
    member e03 : UnreducedBigInt5
    member e04 : UnreducedBigInt5
    member e05 : UnreducedBigInt5
    member e06 : UnreducedBigInt5
    member e07 : UnreducedBigInt5
    member e08 : UnreducedBigInt5
    member e09 : UnreducedBigInt5
    member e0A : UnreducedBigInt5
    member e0B : UnreducedBigInt5
    member e0C : UnreducedBigInt5
    member e0D : UnreducedBigInt5
    member e0E : UnreducedBigInt5
    member e0F : UnreducedBigInt5
    member e10 : UnreducedBigInt5
    member e11 : UnreducedBigInt5
    member e12 : UnreducedBigInt5
    member e13 : UnreducedBigInt5
    member e14 : UnreducedBigInt5
    member e15 : UnreducedBigInt5
    member e16 : UnreducedBigInt5
end

# FIELD CONSTANTS
func fq_zero() -> (res : BigInt3):
    return (BigInt3(0, 0, 0))
end

func fq2_zero() -> (res : FQ2):
    return (FQ2(
        e0=BigInt3(0, 0, 0),
        e1=BigInt3(0, 0, 0),
        ))
end

func fq12_zero() -> (res : FQ12):
    return (
        FQ12(
        e0=BigInt3(0, 0, 0), e1=BigInt3(0, 0, 0), e2=BigInt3(0, 0, 0),
        e3=BigInt3(0, 0, 0), e4=BigInt3(0, 0, 0), e5=BigInt3(0, 0, 0),
        e6=BigInt3(0, 0, 0), e7=BigInt3(0, 0, 0), e8=BigInt3(0, 0, 0),
        e9=BigInt3(0, 0, 0), eA=BigInt3(0, 0, 0), eB=BigInt3(0, 0, 0),
        ))
end

func fq12_one() -> (res : FQ12):
    return (
        FQ12(
        e0=BigInt3(1, 0, 0), e1=BigInt3(0, 0, 0), e2=BigInt3(0, 0, 0),
        e3=BigInt3(0, 0, 0), e4=BigInt3(0, 0, 0), e5=BigInt3(0, 0, 0),
        e6=BigInt3(0, 0, 0), e7=BigInt3(0, 0, 0), e8=BigInt3(0, 0, 0),
        e9=BigInt3(0, 0, 0), eA=BigInt3(0, 0, 0), eB=BigInt3(0, 0, 0),
        ))
end

func verify_zero3{range_check_ptr}(val : BigInt3):
    alloc_locals
    local flag
    local q
    %{
        from starkware.cairo.common.cairo_secp.secp_utils import pack
        from starkware.cairo.common.math_utils import as_int

        P = 0x30644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd47

        v = pack(ids.val, PRIME) 
        q, r = divmod(v, P)
        assert r == 0, f"verify_zero: Invalid input {ids.val.d0, ids.val.d1, ids.val.d2}."

        ids.flag = 1 if q > 0 else 0
        q = q if q > 0 else 0-q
        ids.q = q % PRIME
    %}
    assert [range_check_ptr] = q + 2 ** 127

    tempvar carry1 = ((2 * flag - 1) * q * P0 - val.d0) / BASE
    assert [range_check_ptr + 1] = carry1 + 2 ** 127

    tempvar carry2 = ((2 * flag - 1) * q * P1 - val.d1 + carry1) / BASE
    assert [range_check_ptr + 2] = carry2 + 2 ** 127

    assert (2 * flag - 1) * q * P2 - val.d2 + carry2 = 0

    let range_check_ptr = range_check_ptr + 3

    return ()
end

func verify_zero5{range_check_ptr}(val : UnreducedBigInt5):
    alloc_locals
    local flag
    local q1
    %{
        from starkware.cairo.common.cairo_secp.secp_utils import pack
        from starkware.cairo.common.math_utils import as_int

        P = 0x30644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd47

        v3 = as_int(ids.val.d3, PRIME)
        v4 = as_int(ids.val.d4, PRIME)
        v = pack(ids.val, PRIME) + v3*2**258 + v4*2**344

        q, r = divmod(v, P)
        assert r == 0, f"verify_zero: Invalid input {ids.val.d0, ids.val.d1, ids.val.d2, ids.val.d3, ids.val.d4}."

        # Since q usually doesn't fit BigInt3, divide it again
        ids.flag = 1 if q > 0 else 0
        q = q if q > 0 else 0-q
        q1, q2 = divmod(q, P)
        ids.q1 = q1
        value = k = q2
    %}
    let (k) = nondet_bigint3()
    let fullk = BigInt3(q1 * P0 + k.d0, q1 * P1 + k.d1, q1 * P2 + k.d2)
    let P = BigInt3(P0, P1, P2)
    let (k_n) = bigint_mul(fullk, P)

    # val mod n = 0, so val = k_n
    tempvar carry1 = ((2 * flag - 1) * k_n.d0 - val.d0) / BASE
    assert [range_check_ptr + 0] = carry1 + 2 ** 127

    tempvar carry2 = ((2 * flag - 1) * k_n.d1 - val.d1 + carry1) / BASE
    assert [range_check_ptr + 1] = carry2 + 2 ** 127

    tempvar carry3 = ((2 * flag - 1) * k_n.d2 - val.d2 + carry2) / BASE
    assert [range_check_ptr + 2] = carry3 + 2 ** 127

    tempvar carry4 = ((2 * flag - 1) * k_n.d3 - val.d3 + carry3) / BASE
    assert [range_check_ptr + 3] = carry4 + 2 ** 127

    assert (2 * flag - 1) * k_n.d4 - val.d4 + carry4 = 0

    let range_check_ptr = range_check_ptr + 4

    return ()
end

# returns 1 if x == 0 mod alt_bn128 prime
func is_zero{range_check_ptr}(x : BigInt3) -> (res : felt):
    %{
        from starkware.cairo.common.cairo_secp.secp_utils import pack
        P = 0x30644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd47
        x = pack(ids.x, PRIME) % P
    %}
    if nondet %{ x == 0 %} != 0:
        verify_zero3(x)
        # verify_zero5(UnreducedBigInt5(d0=x.d0, d1=x.d1, d2=x.d2, d3=0, d4=0))
        return (res=1)
    end

    %{
        from starkware.python.math_utils import div_mod
        value = x_inv = div_mod(1, x, P)
    %}
    let (x_inv) = nondet_bigint3()
    let (x_x_inv) = bigint_mul(x, x_inv)

    # Check that x * x_inv = 1 to verify that x != 0.
    verify_zero5(
        UnreducedBigInt5(
        d0=x_x_inv.d0 - 1,
        d1=x_x_inv.d1,
        d2=x_x_inv.d2,
        d3=x_x_inv.d3,
        d4=x_x_inv.d4))
    return (res=0)
end

# FQ12 verify

func verify_zero_fq12{range_check_ptr}(x : FQ12):
    verify_zero3(x.e0)
    verify_zero3(x.e1)
    verify_zero3(x.e2)
    verify_zero3(x.e3)
    verify_zero3(x.e4)
    verify_zero3(x.e5)
    verify_zero3(x.e6)
    verify_zero3(x.e7)
    verify_zero3(x.e8)
    verify_zero3(x.e9)
    verify_zero3(x.eA)
    verify_zero3(x.eB)
    return ()
end

func fq_eq_zero(x : BigInt3) -> (res : felt):
    if x.d0 != 0:
        return (res=0)
    end
    if x.d1 != 0:
        return (res=0)
    end
    if x.d2 != 0:
        return (res=0)
    end
    return (res=1)
end

func fq12_eq_zero(x : FQ12) -> (res : felt):
    let (e0_is_zero) = fq_eq_zero(x.e0)
    if e0_is_zero == 0:
        return (res=0)
    end
    let (e1_is_zero) = fq_eq_zero(x.e1)
    if e1_is_zero == 0:
        return (res=0)
    end
    let (e2_is_zero) = fq_eq_zero(x.e2)
    if e2_is_zero == 0:
        return (res=0)
    end
    let (e3_is_zero) = fq_eq_zero(x.e3)
    if e3_is_zero == 0:
        return (res=0)
    end
    let (e4_is_zero) = fq_eq_zero(x.e4)
    if e4_is_zero == 0:
        return (res=0)
    end
    let (e5_is_zero) = fq_eq_zero(x.e5)
    if e5_is_zero == 0:
        return (res=0)
    end
    let (e6_is_zero) = fq_eq_zero(x.e6)
    if e6_is_zero == 0:
        return (res=0)
    end
    let (e7_is_zero) = fq_eq_zero(x.e7)
    if e7_is_zero == 0:
        return (res=0)
    end
    let (e8_is_zero) = fq_eq_zero(x.e8)
    if e8_is_zero == 0:
        return (res=0)
    end
    let (e9_is_zero) = fq_eq_zero(x.e9)
    if e9_is_zero == 0:
        return (res=0)
    end
    let (eA_is_zero) = fq_eq_zero(x.eA)
    if eA_is_zero == 0:
        return (res=0)
    end
    let (eB_is_zero) = fq_eq_zero(x.eB)
    if eB_is_zero == 0:
        return (res=0)
    end
    return (res=1)
end

func fq12_is_zero{range_check_ptr}(x : FQ12) -> (res : felt):
    %{
        import sys, os 
        cwd = os.getcwd()
        sys.path.append(cwd)

        from utils.bn128_field import FQ, FQ12
        from utils.bn128_utils import parse_fq12

        val = list(map(FQ, parse_fq12(ids.x)))

        if FQ12(val) == FQ12([0]*12):
            x = 0
        else: 
            x = 1
    %}
    if nondet %{ x == 0 %} != 0:
        verify_zero_fq12(x)
        return (res=1)
    end

    %{
        val = list(map(FQ, parse_fq12(ids.x)))
        val = FQ12(val).inv()
        value = list(map(lambda x: x.n, val.coeffs))
    %}
    let (x_inv) = nondet_fq12()

    # TODO VERIF x * x_inv - 1 = 0
    return (res=0)
end

# Difference of two FQ12, resulting FQ12 BigInt3 limbs can be negative
func fq12_diff(x : FQ12, y : FQ12) -> (res : FQ12):
    return (
        res=FQ12(
        BigInt3(d0=x.e0.d0 - y.e0.d0, d1=x.e0.d1 - y.e0.d1, d2=x.e0.d2 - y.e0.d2),
        BigInt3(d0=x.e1.d0 - y.e1.d0, d1=x.e1.d1 - y.e1.d1, d2=x.e1.d2 - y.e1.d2),
        BigInt3(d0=x.e2.d0 - y.e2.d0, d1=x.e2.d1 - y.e2.d1, d2=x.e2.d2 - y.e2.d2),
        BigInt3(d0=x.e3.d0 - y.e3.d0, d1=x.e3.d1 - y.e3.d1, d2=x.e3.d2 - y.e3.d2),
        BigInt3(d0=x.e4.d0 - y.e4.d0, d1=x.e4.d1 - y.e4.d1, d2=x.e4.d2 - y.e4.d2),
        BigInt3(d0=x.e5.d0 - y.e5.d0, d1=x.e5.d1 - y.e5.d1, d2=x.e5.d2 - y.e5.d2),
        BigInt3(d0=x.e6.d0 - y.e6.d0, d1=x.e6.d1 - y.e6.d1, d2=x.e6.d2 - y.e6.d2),
        BigInt3(d0=x.e7.d0 - y.e7.d0, d1=x.e7.d1 - y.e7.d1, d2=x.e7.d2 - y.e7.d2),
        BigInt3(d0=x.e8.d0 - y.e8.d0, d1=x.e8.d1 - y.e8.d1, d2=x.e8.d2 - y.e8.d2),
        BigInt3(d0=x.e9.d0 - y.e9.d0, d1=x.e9.d1 - y.e9.d1, d2=x.e9.d2 - y.e9.d2),
        BigInt3(d0=x.eA.d0 - y.eA.d0, d1=x.eA.d1 - y.eA.d1, d2=x.eA.d2 - y.eA.d2),
        BigInt3(d0=x.eB.d0 - y.eB.d0, d1=x.eB.d1 - y.eB.d1, d2=x.eB.d2 - y.eB.d2)))
end

func fq12_sum(x : FQ12, y : FQ12) -> (res : FQ12):
    return (
        res=FQ12(
        BigInt3(d0=x.e0.d0 + y.e0.d0, d1=x.e0.d1 + y.e0.d1, d2=x.e0.d2 + y.e0.d2),
        BigInt3(d0=x.e1.d0 + y.e1.d0, d1=x.e1.d1 + y.e1.d1, d2=x.e1.d2 + y.e1.d2),
        BigInt3(d0=x.e2.d0 + y.e2.d0, d1=x.e2.d1 + y.e2.d1, d2=x.e2.d2 + y.e2.d2),
        BigInt3(d0=x.e3.d0 + y.e3.d0, d1=x.e3.d1 + y.e3.d1, d2=x.e3.d2 + y.e3.d2),
        BigInt3(d0=x.e4.d0 + y.e4.d0, d1=x.e4.d1 + y.e4.d1, d2=x.e4.d2 + y.e4.d2),
        BigInt3(d0=x.e5.d0 + y.e5.d0, d1=x.e5.d1 + y.e5.d1, d2=x.e5.d2 + y.e5.d2),
        BigInt3(d0=x.e6.d0 + y.e6.d0, d1=x.e6.d1 + y.e6.d1, d2=x.e6.d2 + y.e6.d2),
        BigInt3(d0=x.e7.d0 + y.e7.d0, d1=x.e7.d1 + y.e7.d1, d2=x.e7.d2 + y.e7.d2),
        BigInt3(d0=x.e8.d0 + y.e8.d0, d1=x.e8.d1 + y.e8.d1, d2=x.e8.d2 + y.e8.d2),
        BigInt3(d0=x.e9.d0 + y.e9.d0, d1=x.e9.d1 + y.e9.d1, d2=x.e9.d2 + y.e9.d2),
        BigInt3(d0=x.eA.d0 + y.eA.d0, d1=x.eA.d1 + y.eA.d1, d2=x.eA.d2 + y.eA.d2),
        BigInt3(d0=x.eB.d0 + y.eB.d0, d1=x.eB.d1 + y.eB.d1, d2=x.eB.d2 + y.eB.d2)))
end

# Unchecked FQ12 multiplication for testing only
func fq12_mul{range_check_ptr}(a : FQ12, b : FQ12) -> (res : FQ12):
    %{
        import sys, os
        cwd = os.getcwd()
        sys.path.append(cwd)
        from utils.bn128_field import FQ, FQ12
        from utils.bn128_utils import parse_fq12, print_g12
        a = FQ12(list(map(FQ, parse_fq12(ids.a))))
        b = FQ12(list(map(FQ, parse_fq12(ids.b))))
        value = res = list(map(lambda x: x.n, (a*b).coeffs))
        # print("a*b =", value)
    %}
    let (res) = nondet_fq12()

    return (res=res)
end

func fq12_pow_inner{range_check_ptr}(x : FQ12, n : felt, m : felt) -> (pow2 : FQ12, res : FQ12):
    if m == 0:
        assert n = 0
        let (one) = fq12_one()
        return (pow2=x, res=one)
    end

    alloc_locals
    let (x_sqr) = fq12_mul(x, x)

    %{ memory[ap] = (ids.n % PRIME) % 2 %}
    jmp odd if [ap] != 0; ap++
    return fq12_pow_inner(x=x_sqr, n=n / 2, m=m - 1)

    odd:
    let (inner_pow, inner_res) = fq12_pow_inner(x=x_sqr, n=(n - 1) / 2, m=m - 1)
    let (res) = fq12_mul(inner_res, x)
    return (inner_pow, res)
end

func fq12_pow_3{range_check_ptr}(x : FQ12, n : BigInt3) -> (pow2 : FQ12, res : FQ12):
    alloc_locals
    let (pow2_0 : FQ12, local res0 : FQ12) = fq12_pow_inner(x, n.d0, 86)
    let (pow2_1 : FQ12, local res1 : FQ12) = fq12_pow_inner(pow2_0, n.d1, 86)
    let (pow2_2, local res2 : FQ12) = fq12_pow_inner(pow2_1, n.d2, 86)
    let (res : FQ12) = fq12_mul(res0, res1)
    let (res : FQ12) = fq12_mul(res, res2)
    return (pow2_2, res)
end

func fq12_pow_12{range_check_ptr}(x : FQ12, n : FQ12) -> (res : FQ12):
    alloc_locals
    let (pow2_0 : FQ12, local res0 : FQ12) = fq12_pow_3(x, n.e0)
    let (pow2_1 : FQ12, local res1 : FQ12) = fq12_pow_3(pow2_0, n.e1)
    let (pow2_2 : FQ12, local res2 : FQ12) = fq12_pow_3(pow2_1, n.e2)
    let (pow2_3 : FQ12, local res3 : FQ12) = fq12_pow_3(pow2_2, n.e3)
    let (pow2_4 : FQ12, local res4 : FQ12) = fq12_pow_3(pow2_3, n.e4)
    let (pow2_5 : FQ12, local res5 : FQ12) = fq12_pow_3(pow2_4, n.e5)
    let (pow2_6 : FQ12, local res6 : FQ12) = fq12_pow_3(pow2_5, n.e6)
    let (pow2_7 : FQ12, local res7 : FQ12) = fq12_pow_3(pow2_6, n.e7)
    let (pow2_8 : FQ12, local res8 : FQ12) = fq12_pow_3(pow2_7, n.e8)
    let (pow2_9 : FQ12, local res9 : FQ12) = fq12_pow_3(pow2_8, n.e9)
    let (pow2_A : FQ12, local resA : FQ12) = fq12_pow_3(pow2_9, n.eA)
    # Simplifications since eB = 0
    # let (pow2_B : FQ12, local resB : FQ12) = fq12_pow_3(pow2_A, n.eB)
    let (local res01 : FQ12) = fq12_mul(res0, res1)
    let (local res23 : FQ12) = fq12_mul(res2, res3)
    let (local res45 : FQ12) = fq12_mul(res4, res5)
    let (local res67 : FQ12) = fq12_mul(res6, res7)
    let (local res89 : FQ12) = fq12_mul(res8, res9)
    # let (local resAB : FQ12) = fq12_mul(resA, resB)
    let (local res0123 : FQ12) = fq12_mul(res01, res23)
    let (local res4567 : FQ12) = fq12_mul(res45, res67)
    # let (local res89AB : FQ12) = fq12_mul(res89, resAB)
    let (local res89A : FQ12) = fq12_mul(res89, resA)
    let (local res0123 : FQ12) = fq12_mul(res01, res23)
    let (local res0__7 : FQ12) = fq12_mul(res0123, res4567)
    let (res : FQ12) = fq12_mul(res0__7, res89A)
    return (res)
end

# Hint argument: value
# a 12 element list of field elements
func nondet_fq12{range_check_ptr}() -> (res : FQ12):
    let res : FQ12 = [cast(ap + 38, FQ12*)]
    %{
        from starkware.cairo.common.cairo_secp.secp_utils import split

        r = ids.res
        var_list = [r.e0, r.e1, r.e2, r.e3, r.e4, r.e5, 
                    r.e6, r.e7, r.e8, r.e9, r.eA, r.eB]
        #segments.write_arg(ids.res.e0.address_, split(val[0]))
        for (var, val) in zip(var_list, value):
            segments.write_arg(var.address_, split(val))
    %}
    const MAX_SUM = 12 * 3 * (2 ** 86 - 1)

    assert [range_check_ptr] = MAX_SUM - (res.e0.d0 + res.e0.d1 + res.e0.d2 + res.e1.d0 + res.e1.d1 + res.e1.d2 +
        res.e2.d0 + res.e2.d1 + res.e2.d2 + res.e3.d0 + res.e3.d1 + res.e3.d2 +
        res.e4.d0 + res.e4.d1 + res.e4.d2 + res.e5.d0 + res.e5.d1 + res.e5.d2 +
        res.e6.d0 + res.e6.d1 + res.e6.d2 + res.e7.d0 + res.e7.d1 + res.e7.d2 +
        res.e8.d0 + res.e8.d1 + res.e8.d2 + res.e9.d0 + res.e9.d1 + res.e9.d2 +
        res.eA.d0 + res.eA.d1 + res.eA.d2 + res.eB.d0 + res.eB.d1 + res.eB.d2)

    tempvar range_check_ptr = range_check_ptr + 37
    [range_check_ptr - 1] = res.e0.d0; ap++
    [range_check_ptr - 2] = res.e0.d1; ap++
    [range_check_ptr - 3] = res.e0.d2; ap++
    [range_check_ptr - 4] = res.e1.d0; ap++
    [range_check_ptr - 5] = res.e1.d1; ap++
    [range_check_ptr - 6] = res.e1.d2; ap++
    [range_check_ptr - 7] = res.e2.d0; ap++
    [range_check_ptr - 8] = res.e2.d1; ap++
    [range_check_ptr - 9] = res.e2.d2; ap++
    [range_check_ptr - 10] = res.e3.d0; ap++
    [range_check_ptr - 11] = res.e3.d1; ap++
    [range_check_ptr - 12] = res.e3.d2; ap++
    [range_check_ptr - 13] = res.e4.d0; ap++
    [range_check_ptr - 14] = res.e4.d1; ap++
    [range_check_ptr - 15] = res.e4.d2; ap++
    [range_check_ptr - 16] = res.e5.d0; ap++
    [range_check_ptr - 17] = res.e5.d1; ap++
    [range_check_ptr - 18] = res.e5.d2; ap++
    [range_check_ptr - 19] = res.e6.d0; ap++
    [range_check_ptr - 20] = res.e6.d1; ap++
    [range_check_ptr - 21] = res.e6.d2; ap++
    [range_check_ptr - 22] = res.e7.d0; ap++
    [range_check_ptr - 23] = res.e7.d1; ap++
    [range_check_ptr - 24] = res.e7.d2; ap++
    [range_check_ptr - 25] = res.e8.d0; ap++
    [range_check_ptr - 26] = res.e8.d1; ap++
    [range_check_ptr - 27] = res.e8.d2; ap++
    [range_check_ptr - 28] = res.e9.d0; ap++
    [range_check_ptr - 29] = res.e9.d1; ap++
    [range_check_ptr - 30] = res.e9.d2; ap++
    [range_check_ptr - 31] = res.eA.d0; ap++
    [range_check_ptr - 32] = res.eA.d1; ap++
    [range_check_ptr - 33] = res.eA.d2; ap++
    [range_check_ptr - 34] = res.eB.d0; ap++
    [range_check_ptr - 35] = res.eB.d1; ap++
    [range_check_ptr - 36] = res.eB.d2; ap++
    static_assert &res + FQ12.SIZE == ap
    return (res=res)
end

# # UNREDUCED "FQ23" OPERATIONS

# FIELD MULTIPLICATION
func ufq12_mul{range_check_ptr}(a : FQ12, b : FQ12) -> (res : UnreducedFQ23):
    let (ab00) = bigint_mul(a.e0, b.e0)
    let (ab01) = bigint_mul(a.e0, b.e1)
    let (ab02) = bigint_mul(a.e0, b.e2)
    let (ab03) = bigint_mul(a.e0, b.e3)
    let (ab04) = bigint_mul(a.e0, b.e4)
    let (ab05) = bigint_mul(a.e0, b.e5)
    let (ab06) = bigint_mul(a.e0, b.e6)
    let (ab07) = bigint_mul(a.e0, b.e7)
    let (ab08) = bigint_mul(a.e0, b.e8)
    let (ab09) = bigint_mul(a.e0, b.e9)
    let (ab0A) = bigint_mul(a.e0, b.eA)
    let (ab0B) = bigint_mul(a.e0, b.eB)
    let (ab10) = bigint_mul(a.e1, b.e0)
    let (ab11) = bigint_mul(a.e1, b.e1)
    let (ab12) = bigint_mul(a.e1, b.e2)
    let (ab13) = bigint_mul(a.e1, b.e3)
    let (ab14) = bigint_mul(a.e1, b.e4)
    let (ab15) = bigint_mul(a.e1, b.e5)
    let (ab16) = bigint_mul(a.e1, b.e6)
    let (ab17) = bigint_mul(a.e1, b.e7)
    let (ab18) = bigint_mul(a.e1, b.e8)
    let (ab19) = bigint_mul(a.e1, b.e9)
    let (ab1A) = bigint_mul(a.e1, b.eA)
    let (ab1B) = bigint_mul(a.e1, b.eB)
    let (ab20) = bigint_mul(a.e2, b.e0)
    let (ab21) = bigint_mul(a.e2, b.e1)
    let (ab22) = bigint_mul(a.e2, b.e2)
    let (ab23) = bigint_mul(a.e2, b.e3)
    let (ab24) = bigint_mul(a.e2, b.e4)
    let (ab25) = bigint_mul(a.e2, b.e5)
    let (ab26) = bigint_mul(a.e2, b.e6)
    let (ab27) = bigint_mul(a.e2, b.e7)
    let (ab28) = bigint_mul(a.e2, b.e8)
    let (ab29) = bigint_mul(a.e2, b.e9)
    let (ab2A) = bigint_mul(a.e2, b.eA)
    let (ab2B) = bigint_mul(a.e2, b.eB)
    let (ab30) = bigint_mul(a.e3, b.e0)
    let (ab31) = bigint_mul(a.e3, b.e1)
    let (ab32) = bigint_mul(a.e3, b.e2)
    let (ab33) = bigint_mul(a.e3, b.e3)
    let (ab34) = bigint_mul(a.e3, b.e4)
    let (ab35) = bigint_mul(a.e3, b.e5)
    let (ab36) = bigint_mul(a.e3, b.e6)
    let (ab37) = bigint_mul(a.e3, b.e7)
    let (ab38) = bigint_mul(a.e3, b.e8)
    let (ab39) = bigint_mul(a.e3, b.e9)
    let (ab3A) = bigint_mul(a.e3, b.eA)
    let (ab3B) = bigint_mul(a.e3, b.eB)
    let (ab40) = bigint_mul(a.e4, b.e0)
    let (ab41) = bigint_mul(a.e4, b.e1)
    let (ab42) = bigint_mul(a.e4, b.e2)
    let (ab43) = bigint_mul(a.e4, b.e3)
    let (ab44) = bigint_mul(a.e4, b.e4)
    let (ab45) = bigint_mul(a.e4, b.e5)
    let (ab46) = bigint_mul(a.e4, b.e6)
    let (ab47) = bigint_mul(a.e4, b.e7)
    let (ab48) = bigint_mul(a.e4, b.e8)
    let (ab49) = bigint_mul(a.e4, b.e9)
    let (ab4A) = bigint_mul(a.e4, b.eA)
    let (ab4B) = bigint_mul(a.e4, b.eB)
    let (ab50) = bigint_mul(a.e5, b.e0)
    let (ab51) = bigint_mul(a.e5, b.e1)
    let (ab52) = bigint_mul(a.e5, b.e2)
    let (ab53) = bigint_mul(a.e5, b.e3)
    let (ab54) = bigint_mul(a.e5, b.e4)
    let (ab55) = bigint_mul(a.e5, b.e5)
    let (ab56) = bigint_mul(a.e5, b.e6)
    let (ab57) = bigint_mul(a.e5, b.e7)
    let (ab58) = bigint_mul(a.e5, b.e8)
    let (ab59) = bigint_mul(a.e5, b.e9)
    let (ab5A) = bigint_mul(a.e5, b.eA)
    let (ab5B) = bigint_mul(a.e5, b.eB)
    let (ab60) = bigint_mul(a.e6, b.e0)
    let (ab61) = bigint_mul(a.e6, b.e1)
    let (ab62) = bigint_mul(a.e6, b.e2)
    let (ab63) = bigint_mul(a.e6, b.e3)
    let (ab64) = bigint_mul(a.e6, b.e4)
    let (ab65) = bigint_mul(a.e6, b.e5)
    let (ab66) = bigint_mul(a.e6, b.e6)
    let (ab67) = bigint_mul(a.e6, b.e7)
    let (ab68) = bigint_mul(a.e6, b.e8)
    let (ab69) = bigint_mul(a.e6, b.e9)
    let (ab6A) = bigint_mul(a.e6, b.eA)
    let (ab6B) = bigint_mul(a.e6, b.eB)
    let (ab70) = bigint_mul(a.e7, b.e0)
    let (ab71) = bigint_mul(a.e7, b.e1)
    let (ab72) = bigint_mul(a.e7, b.e2)
    let (ab73) = bigint_mul(a.e7, b.e3)
    let (ab74) = bigint_mul(a.e7, b.e4)
    let (ab75) = bigint_mul(a.e7, b.e5)
    let (ab76) = bigint_mul(a.e7, b.e6)
    let (ab77) = bigint_mul(a.e7, b.e7)
    let (ab78) = bigint_mul(a.e7, b.e8)
    let (ab79) = bigint_mul(a.e7, b.e9)
    let (ab7A) = bigint_mul(a.e7, b.eA)
    let (ab7B) = bigint_mul(a.e7, b.eB)
    let (ab80) = bigint_mul(a.e8, b.e0)
    let (ab81) = bigint_mul(a.e8, b.e1)
    let (ab82) = bigint_mul(a.e8, b.e2)
    let (ab83) = bigint_mul(a.e8, b.e3)
    let (ab84) = bigint_mul(a.e8, b.e4)
    let (ab85) = bigint_mul(a.e8, b.e5)
    let (ab86) = bigint_mul(a.e8, b.e6)
    let (ab87) = bigint_mul(a.e8, b.e7)
    let (ab88) = bigint_mul(a.e8, b.e8)
    let (ab89) = bigint_mul(a.e8, b.e9)
    let (ab8A) = bigint_mul(a.e8, b.eA)
    let (ab8B) = bigint_mul(a.e8, b.eB)
    let (ab90) = bigint_mul(a.e9, b.e0)
    let (ab91) = bigint_mul(a.e9, b.e1)
    let (ab92) = bigint_mul(a.e9, b.e2)
    let (ab93) = bigint_mul(a.e9, b.e3)
    let (ab94) = bigint_mul(a.e9, b.e4)
    let (ab95) = bigint_mul(a.e9, b.e5)
    let (ab96) = bigint_mul(a.e9, b.e6)
    let (ab97) = bigint_mul(a.e9, b.e7)
    let (ab98) = bigint_mul(a.e9, b.e8)
    let (ab99) = bigint_mul(a.e9, b.e9)
    let (ab9A) = bigint_mul(a.e9, b.eA)
    let (ab9B) = bigint_mul(a.e9, b.eB)
    let (abA0) = bigint_mul(a.eA, b.e0)
    let (abA1) = bigint_mul(a.eA, b.e1)
    let (abA2) = bigint_mul(a.eA, b.e2)
    let (abA3) = bigint_mul(a.eA, b.e3)
    let (abA4) = bigint_mul(a.eA, b.e4)
    let (abA5) = bigint_mul(a.eA, b.e5)
    let (abA6) = bigint_mul(a.eA, b.e6)
    let (abA7) = bigint_mul(a.eA, b.e7)
    let (abA8) = bigint_mul(a.eA, b.e8)
    let (abA9) = bigint_mul(a.eA, b.e9)
    let (abAA) = bigint_mul(a.eA, b.eA)
    let (abAB) = bigint_mul(a.eA, b.eB)
    let (abB0) = bigint_mul(a.eB, b.e0)
    let (abB1) = bigint_mul(a.eB, b.e1)
    let (abB2) = bigint_mul(a.eB, b.e2)
    let (abB3) = bigint_mul(a.eB, b.e3)
    let (abB4) = bigint_mul(a.eB, b.e4)
    let (abB5) = bigint_mul(a.eB, b.e5)
    let (abB6) = bigint_mul(a.eB, b.e6)
    let (abB7) = bigint_mul(a.eB, b.e7)
    let (abB8) = bigint_mul(a.eB, b.e8)
    let (abB9) = bigint_mul(a.eB, b.e9)
    let (abBA) = bigint_mul(a.eB, b.eA)
    let (abBB) = bigint_mul(a.eB, b.eB)
    let res = UnreducedFQ23(
        e00=UnreducedBigInt5(
        d0=ab00.d0,
        d1=ab00.d1,
        d2=ab00.d2,
        d3=ab00.d3,
        d4=ab00.d4),
        e01=UnreducedBigInt5(
        d0=ab10.d0 + ab01.d0,
        d1=ab10.d1 + ab01.d1,
        d2=ab10.d2 + ab01.d2,
        d3=ab10.d3 + ab01.d3,
        d4=ab10.d4 + ab01.d4),
        e02=UnreducedBigInt5(
        d0=ab20.d0 + ab11.d0 + ab02.d0,
        d1=ab20.d1 + ab11.d1 + ab02.d1,
        d2=ab20.d2 + ab11.d2 + ab02.d2,
        d3=ab20.d3 + ab11.d3 + ab02.d3,
        d4=ab20.d4 + ab11.d4 + ab02.d4),
        e03=UnreducedBigInt5(
        d0=ab30.d0 + ab21.d0 + ab12.d0 + ab03.d0,
        d1=ab30.d1 + ab21.d1 + ab12.d1 + ab03.d1,
        d2=ab30.d2 + ab21.d2 + ab12.d2 + ab03.d2,
        d3=ab30.d3 + ab21.d3 + ab12.d3 + ab03.d3,
        d4=ab30.d4 + ab21.d4 + ab12.d4 + ab03.d4),
        e04=UnreducedBigInt5(
        d0=ab40.d0 + ab31.d0 + ab22.d0 + ab13.d0 + ab04.d0,
        d1=ab40.d1 + ab31.d1 + ab22.d1 + ab13.d1 + ab04.d1,
        d2=ab40.d2 + ab31.d2 + ab22.d2 + ab13.d2 + ab04.d2,
        d3=ab40.d3 + ab31.d3 + ab22.d3 + ab13.d3 + ab04.d3,
        d4=ab40.d4 + ab31.d4 + ab22.d4 + ab13.d4 + ab04.d4),
        e05=UnreducedBigInt5(
        d0=ab50.d0 + ab41.d0 + ab32.d0 + ab23.d0 + ab14.d0 + ab05.d0,
        d1=ab50.d1 + ab41.d1 + ab32.d1 + ab23.d1 + ab14.d1 + ab05.d1,
        d2=ab50.d2 + ab41.d2 + ab32.d2 + ab23.d2 + ab14.d2 + ab05.d2,
        d3=ab50.d3 + ab41.d3 + ab32.d3 + ab23.d3 + ab14.d3 + ab05.d3,
        d4=ab50.d4 + ab41.d4 + ab32.d4 + ab23.d4 + ab14.d4 + ab05.d4),
        e06=UnreducedBigInt5(
        d0=ab60.d0 + ab51.d0 + ab42.d0 + ab33.d0 + ab24.d0 + ab15.d0 + ab06.d0,
        d1=ab60.d1 + ab51.d1 + ab42.d1 + ab33.d1 + ab24.d1 + ab15.d1 + ab06.d1,
        d2=ab60.d2 + ab51.d2 + ab42.d2 + ab33.d2 + ab24.d2 + ab15.d2 + ab06.d2,
        d3=ab60.d3 + ab51.d3 + ab42.d3 + ab33.d3 + ab24.d3 + ab15.d3 + ab06.d3,
        d4=ab60.d4 + ab51.d4 + ab42.d4 + ab33.d4 + ab24.d4 + ab15.d4 + ab06.d4),
        e07=UnreducedBigInt5(
        d0=ab70.d0 + ab61.d0 + ab52.d0 + ab43.d0 + ab34.d0 + ab25.d0 + ab16.d0 + ab07.d0,
        d1=ab70.d1 + ab61.d1 + ab52.d1 + ab43.d1 + ab34.d1 + ab25.d1 + ab16.d1 + ab07.d1,
        d2=ab70.d2 + ab61.d2 + ab52.d2 + ab43.d2 + ab34.d2 + ab25.d2 + ab16.d2 + ab07.d2,
        d3=ab70.d3 + ab61.d3 + ab52.d3 + ab43.d3 + ab34.d3 + ab25.d3 + ab16.d3 + ab07.d3,
        d4=ab70.d4 + ab61.d4 + ab52.d4 + ab43.d4 + ab34.d4 + ab25.d4 + ab16.d4 + ab07.d4),
        e08=UnreducedBigInt5(
        d0=ab80.d0 + ab71.d0 + ab62.d0 + ab53.d0 + ab44.d0 + ab35.d0 + ab26.d0 + ab17.d0 + ab08.d0,
        d1=ab80.d1 + ab71.d1 + ab62.d1 + ab53.d1 + ab44.d1 + ab35.d1 + ab26.d1 + ab17.d1 + ab08.d1,
        d2=ab80.d2 + ab71.d2 + ab62.d2 + ab53.d2 + ab44.d2 + ab35.d2 + ab26.d2 + ab17.d2 + ab08.d2,
        d3=ab80.d3 + ab71.d3 + ab62.d3 + ab53.d3 + ab44.d3 + ab35.d3 + ab26.d3 + ab17.d3 + ab08.d3,
        d4=ab80.d4 + ab71.d4 + ab62.d4 + ab53.d4 + ab44.d4 + ab35.d4 + ab26.d4 + ab17.d4 + ab08.d4),
        e09=UnreducedBigInt5(
        d0=ab90.d0 + ab81.d0 + ab72.d0 + ab63.d0 + ab54.d0 + ab45.d0 + ab36.d0 + ab27.d0 + ab18.d0 + ab09.d0,
        d1=ab90.d1 + ab81.d1 + ab72.d1 + ab63.d1 + ab54.d1 + ab45.d1 + ab36.d1 + ab27.d1 + ab18.d1 + ab09.d1,
        d2=ab90.d2 + ab81.d2 + ab72.d2 + ab63.d2 + ab54.d2 + ab45.d2 + ab36.d2 + ab27.d2 + ab18.d2 + ab09.d2,
        d3=ab90.d3 + ab81.d3 + ab72.d3 + ab63.d3 + ab54.d3 + ab45.d3 + ab36.d3 + ab27.d3 + ab18.d3 + ab09.d3,
        d4=ab90.d4 + ab81.d4 + ab72.d4 + ab63.d4 + ab54.d4 + ab45.d4 + ab36.d4 + ab27.d4 + ab18.d4 + ab09.d4),
        e0A=UnreducedBigInt5(
        d0=abA0.d0 + ab91.d0 + ab82.d0 + ab73.d0 + ab64.d0 + ab55.d0 + ab46.d0 + ab37.d0 + ab28.d0 + ab19.d0 + ab0A.d0,
        d1=abA0.d1 + ab91.d1 + ab82.d1 + ab73.d1 + ab64.d1 + ab55.d1 + ab46.d1 + ab37.d1 + ab28.d1 + ab19.d1 + ab0A.d1,
        d2=abA0.d2 + ab91.d2 + ab82.d2 + ab73.d2 + ab64.d2 + ab55.d2 + ab46.d2 + ab37.d2 + ab28.d2 + ab19.d2 + ab0A.d2,
        d3=abA0.d3 + ab91.d3 + ab82.d3 + ab73.d3 + ab64.d3 + ab55.d3 + ab46.d3 + ab37.d3 + ab28.d3 + ab19.d3 + ab0A.d3,
        d4=abA0.d4 + ab91.d4 + ab82.d4 + ab73.d4 + ab64.d4 + ab55.d4 + ab46.d4 + ab37.d4 + ab28.d4 + ab19.d4 + ab0A.d4),
        e0B=UnreducedBigInt5(
        d0=abB0.d0 + abA1.d0 + ab92.d0 + ab83.d0 + ab74.d0 + ab65.d0 + ab56.d0 + ab47.d0 + ab38.d0 + ab29.d0 + ab1A.d0 + ab0B.d0,
        d1=abB0.d1 + abA1.d1 + ab92.d1 + ab83.d1 + ab74.d1 + ab65.d1 + ab56.d1 + ab47.d1 + ab38.d1 + ab29.d1 + ab1A.d1 + ab0B.d1,
        d2=abB0.d2 + abA1.d2 + ab92.d2 + ab83.d2 + ab74.d2 + ab65.d2 + ab56.d2 + ab47.d2 + ab38.d2 + ab29.d2 + ab1A.d2 + ab0B.d2,
        d3=abB0.d3 + abA1.d3 + ab92.d3 + ab83.d3 + ab74.d3 + ab65.d3 + ab56.d3 + ab47.d3 + ab38.d3 + ab29.d3 + ab1A.d3 + ab0B.d3,
        d4=abB0.d4 + abA1.d4 + ab92.d4 + ab83.d4 + ab74.d4 + ab65.d4 + ab56.d4 + ab47.d4 + ab38.d4 + ab29.d4 + ab1A.d4 + ab0B.d4),
        e0C=UnreducedBigInt5(
        d0=abB1.d0 + abA2.d0 + ab93.d0 + ab84.d0 + ab75.d0 + ab66.d0 + ab57.d0 + ab48.d0 + ab39.d0 + ab2A.d0 + ab1B.d0,
        d1=abB1.d1 + abA2.d1 + ab93.d1 + ab84.d1 + ab75.d1 + ab66.d1 + ab57.d1 + ab48.d1 + ab39.d1 + ab2A.d1 + ab1B.d1,
        d2=abB1.d2 + abA2.d2 + ab93.d2 + ab84.d2 + ab75.d2 + ab66.d2 + ab57.d2 + ab48.d2 + ab39.d2 + ab2A.d2 + ab1B.d2,
        d3=abB1.d3 + abA2.d3 + ab93.d3 + ab84.d3 + ab75.d3 + ab66.d3 + ab57.d3 + ab48.d3 + ab39.d3 + ab2A.d3 + ab1B.d3,
        d4=abB1.d4 + abA2.d4 + ab93.d4 + ab84.d4 + ab75.d4 + ab66.d4 + ab57.d4 + ab48.d4 + ab39.d4 + ab2A.d4 + ab1B.d4),
        e0D=UnreducedBigInt5(
        d0=abB2.d0 + abA3.d0 + ab94.d0 + ab85.d0 + ab76.d0 + ab67.d0 + ab58.d0 + ab49.d0 + ab3A.d0 + ab2B.d0,
        d1=abB2.d1 + abA3.d1 + ab94.d1 + ab85.d1 + ab76.d1 + ab67.d1 + ab58.d1 + ab49.d1 + ab3A.d1 + ab2B.d1,
        d2=abB2.d2 + abA3.d2 + ab94.d2 + ab85.d2 + ab76.d2 + ab67.d2 + ab58.d2 + ab49.d2 + ab3A.d2 + ab2B.d2,
        d3=abB2.d3 + abA3.d3 + ab94.d3 + ab85.d3 + ab76.d3 + ab67.d3 + ab58.d3 + ab49.d3 + ab3A.d3 + ab2B.d3,
        d4=abB2.d4 + abA3.d4 + ab94.d4 + ab85.d4 + ab76.d4 + ab67.d4 + ab58.d4 + ab49.d4 + ab3A.d4 + ab2B.d4),
        e0E=UnreducedBigInt5(
        d0=abB3.d0 + abA4.d0 + ab95.d0 + ab86.d0 + ab77.d0 + ab68.d0 + ab59.d0 + ab4A.d0 + ab3B.d0,
        d1=abB3.d1 + abA4.d1 + ab95.d1 + ab86.d1 + ab77.d1 + ab68.d1 + ab59.d1 + ab4A.d1 + ab3B.d1,
        d2=abB3.d2 + abA4.d2 + ab95.d2 + ab86.d2 + ab77.d2 + ab68.d2 + ab59.d2 + ab4A.d2 + ab3B.d2,
        d3=abB3.d3 + abA4.d3 + ab95.d3 + ab86.d3 + ab77.d3 + ab68.d3 + ab59.d3 + ab4A.d3 + ab3B.d3,
        d4=abB3.d4 + abA4.d4 + ab95.d4 + ab86.d4 + ab77.d4 + ab68.d4 + ab59.d4 + ab4A.d4 + ab3B.d4),
        e0F=UnreducedBigInt5(
        d0=abB4.d0 + abA5.d0 + ab96.d0 + ab87.d0 + ab78.d0 + ab69.d0 + ab5A.d0 + ab4B.d0,
        d1=abB4.d1 + abA5.d1 + ab96.d1 + ab87.d1 + ab78.d1 + ab69.d1 + ab5A.d1 + ab4B.d1,
        d2=abB4.d2 + abA5.d2 + ab96.d2 + ab87.d2 + ab78.d2 + ab69.d2 + ab5A.d2 + ab4B.d2,
        d3=abB4.d3 + abA5.d3 + ab96.d3 + ab87.d3 + ab78.d3 + ab69.d3 + ab5A.d3 + ab4B.d3,
        d4=abB4.d4 + abA5.d4 + ab96.d4 + ab87.d4 + ab78.d4 + ab69.d4 + ab5A.d4 + ab4B.d4),
        e10=UnreducedBigInt5(
        d0=abB5.d0 + abA6.d0 + ab97.d0 + ab88.d0 + ab79.d0 + ab6A.d0 + ab5B.d0,
        d1=abB5.d1 + abA6.d1 + ab97.d1 + ab88.d1 + ab79.d1 + ab6A.d1 + ab5B.d1,
        d2=abB5.d2 + abA6.d2 + ab97.d2 + ab88.d2 + ab79.d2 + ab6A.d2 + ab5B.d2,
        d3=abB5.d3 + abA6.d3 + ab97.d3 + ab88.d3 + ab79.d3 + ab6A.d3 + ab5B.d3,
        d4=abB5.d4 + abA6.d4 + ab97.d4 + ab88.d4 + ab79.d4 + ab6A.d4 + ab5B.d4),
        e11=UnreducedBigInt5(
        d0=abB6.d0 + abA7.d0 + ab98.d0 + ab89.d0 + ab7A.d0 + ab6B.d0,
        d1=abB6.d1 + abA7.d1 + ab98.d1 + ab89.d1 + ab7A.d1 + ab6B.d1,
        d2=abB6.d2 + abA7.d2 + ab98.d2 + ab89.d2 + ab7A.d2 + ab6B.d2,
        d3=abB6.d3 + abA7.d3 + ab98.d3 + ab89.d3 + ab7A.d3 + ab6B.d3,
        d4=abB6.d4 + abA7.d4 + ab98.d4 + ab89.d4 + ab7A.d4 + ab6B.d4),
        e12=UnreducedBigInt5(
        d0=abB7.d0 + abA8.d0 + ab99.d0 + ab8A.d0 + ab7B.d0,
        d1=abB7.d1 + abA8.d1 + ab99.d1 + ab8A.d1 + ab7B.d1,
        d2=abB7.d2 + abA8.d2 + ab99.d2 + ab8A.d2 + ab7B.d2,
        d3=abB7.d3 + abA8.d3 + ab99.d3 + ab8A.d3 + ab7B.d3,
        d4=abB7.d4 + abA8.d4 + ab99.d4 + ab8A.d4 + ab7B.d4),
        e13=UnreducedBigInt5(
        d0=abB8.d0 + abA9.d0 + ab9A.d0 + ab8B.d0,
        d1=abB8.d1 + abA9.d1 + ab9A.d1 + ab8B.d1,
        d2=abB8.d2 + abA9.d2 + ab9A.d2 + ab8B.d2,
        d3=abB8.d3 + abA9.d3 + ab9A.d3 + ab8B.d3,
        d4=abB8.d4 + abA9.d4 + ab9A.d4 + ab8B.d4),
        e14=UnreducedBigInt5(
        d0=abB9.d0 + abAA.d0 + ab9B.d0,
        d1=abB9.d1 + abAA.d1 + ab9B.d1,
        d2=abB9.d2 + abAA.d2 + ab9B.d2,
        d3=abB9.d3 + abAA.d3 + ab9B.d3,
        d4=abB9.d4 + abAA.d4 + ab9B.d4),
        e15=UnreducedBigInt5(
        d0=abBA.d0 + abAB.d0,
        d1=abBA.d1 + abAB.d1,
        d2=abBA.d2 + abAB.d2,
        d3=abBA.d3 + abAB.d3,
        d4=abBA.d4 + abAB.d4),
        e16=UnreducedBigInt5(
        d0=abBB.d0,
        d1=abBB.d1,
        d2=abBB.d2,
        d3=abBB.d3,
        d4=abBB.d4))
    return (res)
end

func verify_zero_ufq23(x : UnreducedFQ23):
    %{
        import sys, os
        cwd = os.getcwd()
        sys.path.append(cwd)
        import numpy as np

        from utils.bn128_field import FQ, FQ12, poly_rounded_div
        from utils.bn128_utils import parse_ufq23, print_g12

        modulus_coeffs = [82, 0, 0, 0, 0, 0, -18, 0, 0, 0, 0, 0, 1]
        x = parse_ufq23(ids.x)
        res = np.polydiv(x, modulus_coeffs)
        print(res, len(res))
    %}
    return ()
end

func ufq23_diff(x : UnreducedFQ23, y : UnreducedFQ23) -> (res : UnreducedFQ23):
    return (
        res=UnreducedFQ23(
        UnreducedBigInt5(x.e00.d0 - y.e00.d0, x.e00.d1 - y.e00.d1, x.e00.d2 - y.e00.d2, x.e00.d3 - y.e00.d3, x.e00.d4 - y.e00.d4),
        UnreducedBigInt5(x.e01.d0 - y.e01.d0, x.e01.d1 - y.e01.d1, x.e01.d2 - y.e01.d2, x.e01.d3 - y.e01.d3, x.e01.d4 - y.e01.d4),
        UnreducedBigInt5(x.e02.d0 - y.e02.d0, x.e02.d1 - y.e02.d1, x.e02.d2 - y.e02.d2, x.e02.d3 - y.e02.d3, x.e02.d4 - y.e02.d4),
        UnreducedBigInt5(x.e03.d0 - y.e03.d0, x.e03.d1 - y.e03.d1, x.e03.d2 - y.e03.d2, x.e03.d3 - y.e03.d3, x.e03.d4 - y.e03.d4),
        UnreducedBigInt5(x.e04.d0 - y.e04.d0, x.e04.d1 - y.e04.d1, x.e04.d2 - y.e04.d2, x.e04.d3 - y.e04.d3, x.e04.d4 - y.e04.d4),
        UnreducedBigInt5(x.e05.d0 - y.e05.d0, x.e05.d1 - y.e05.d1, x.e05.d2 - y.e05.d2, x.e05.d3 - y.e05.d3, x.e05.d4 - y.e05.d4),
        UnreducedBigInt5(x.e06.d0 - y.e06.d0, x.e06.d1 - y.e06.d1, x.e06.d2 - y.e06.d2, x.e06.d3 - y.e06.d3, x.e06.d4 - y.e06.d4),
        UnreducedBigInt5(x.e07.d0 - y.e07.d0, x.e07.d1 - y.e07.d1, x.e07.d2 - y.e07.d2, x.e07.d3 - y.e07.d3, x.e07.d4 - y.e07.d4),
        UnreducedBigInt5(x.e08.d0 - y.e08.d0, x.e08.d1 - y.e08.d1, x.e08.d2 - y.e08.d2, x.e08.d3 - y.e08.d3, x.e08.d4 - y.e08.d4),
        UnreducedBigInt5(x.e09.d0 - y.e09.d0, x.e09.d1 - y.e09.d1, x.e09.d2 - y.e09.d2, x.e09.d3 - y.e09.d3, x.e09.d4 - y.e09.d4),
        UnreducedBigInt5(x.e0A.d0 - y.e0A.d0, x.e0A.d1 - y.e0A.d1, x.e0A.d2 - y.e0A.d2, x.e0A.d3 - y.e0A.d3, x.e0A.d4 - y.e0A.d4),
        UnreducedBigInt5(x.e0B.d0 - y.e0B.d0, x.e0B.d1 - y.e0B.d1, x.e0B.d2 - y.e0B.d2, x.e0B.d3 - y.e0B.d3, x.e0B.d4 - y.e0B.d4),
        UnreducedBigInt5(x.e0C.d0 - y.e0C.d0, x.e0C.d1 - y.e0C.d1, x.e0C.d2 - y.e0C.d2, x.e0C.d3 - y.e0C.d3, x.e0C.d4 - y.e0C.d4),
        UnreducedBigInt5(x.e0D.d0 - y.e0D.d0, x.e0D.d1 - y.e0D.d1, x.e0D.d2 - y.e0D.d2, x.e0D.d3 - y.e0D.d3, x.e0D.d4 - y.e0D.d4),
        UnreducedBigInt5(x.e0E.d0 - y.e0E.d0, x.e0E.d1 - y.e0E.d1, x.e0E.d2 - y.e0E.d2, x.e0E.d3 - y.e0E.d3, x.e0E.d4 - y.e0E.d4),
        UnreducedBigInt5(x.e0F.d0 - y.e0F.d0, x.e0F.d1 - y.e0F.d1, x.e0F.d2 - y.e0F.d2, x.e0F.d3 - y.e0F.d3, x.e0F.d4 - y.e0F.d4),
        UnreducedBigInt5(x.e10.d0 - y.e10.d0, x.e10.d1 - y.e10.d1, x.e10.d2 - y.e10.d2, x.e10.d3 - y.e10.d3, x.e10.d4 - y.e10.d4),
        UnreducedBigInt5(x.e11.d0 - y.e11.d0, x.e11.d1 - y.e11.d1, x.e11.d2 - y.e11.d2, x.e11.d3 - y.e11.d3, x.e11.d4 - y.e11.d4),
        UnreducedBigInt5(x.e12.d0 - y.e12.d0, x.e12.d1 - y.e12.d1, x.e12.d2 - y.e12.d2, x.e12.d3 - y.e12.d3, x.e12.d4 - y.e12.d4),
        UnreducedBigInt5(x.e13.d0 - y.e13.d0, x.e13.d1 - y.e13.d1, x.e13.d2 - y.e13.d2, x.e13.d3 - y.e13.d3, x.e13.d4 - y.e13.d4),
        UnreducedBigInt5(x.e14.d0 - y.e14.d0, x.e14.d1 - y.e14.d1, x.e14.d2 - y.e14.d2, x.e14.d3 - y.e14.d3, x.e14.d4 - y.e14.d4),
        UnreducedBigInt5(x.e15.d0 - y.e15.d0, x.e15.d1 - y.e15.d1, x.e15.d2 - y.e15.d2, x.e15.d3 - y.e15.d3, x.e15.d4 - y.e15.d4),
        UnreducedBigInt5(x.e16.d0 - y.e16.d0, x.e16.d1 - y.e16.d1, x.e16.d2 - y.e16.d2, x.e16.d3 - y.e16.d3, x.e16.d4 - y.e16.d4),
        ))
end

func ufq23_sul(x : UnreducedFQ23, y : UnreducedFQ23) -> (res : UnreducedFQ23):
    return (
        res=UnreducedFQ23(
        UnreducedBigInt5(x.e00.d0 + y.e00.d0, x.e00.d1 + y.e00.d1, x.e00.d2 + y.e00.d2, x.e00.d3 + y.e00.d3, x.e00.d4 + y.e00.d4),
        UnreducedBigInt5(x.e01.d0 + y.e01.d0, x.e01.d1 + y.e01.d1, x.e01.d2 + y.e01.d2, x.e01.d3 + y.e01.d3, x.e01.d4 + y.e01.d4),
        UnreducedBigInt5(x.e02.d0 + y.e02.d0, x.e02.d1 + y.e02.d1, x.e02.d2 + y.e02.d2, x.e02.d3 + y.e02.d3, x.e02.d4 + y.e02.d4),
        UnreducedBigInt5(x.e03.d0 + y.e03.d0, x.e03.d1 + y.e03.d1, x.e03.d2 + y.e03.d2, x.e03.d3 + y.e03.d3, x.e03.d4 + y.e03.d4),
        UnreducedBigInt5(x.e04.d0 + y.e04.d0, x.e04.d1 + y.e04.d1, x.e04.d2 + y.e04.d2, x.e04.d3 + y.e04.d3, x.e04.d4 + y.e04.d4),
        UnreducedBigInt5(x.e05.d0 + y.e05.d0, x.e05.d1 + y.e05.d1, x.e05.d2 + y.e05.d2, x.e05.d3 + y.e05.d3, x.e05.d4 + y.e05.d4),
        UnreducedBigInt5(x.e06.d0 + y.e06.d0, x.e06.d1 + y.e06.d1, x.e06.d2 + y.e06.d2, x.e06.d3 + y.e06.d3, x.e06.d4 + y.e06.d4),
        UnreducedBigInt5(x.e07.d0 + y.e07.d0, x.e07.d1 + y.e07.d1, x.e07.d2 + y.e07.d2, x.e07.d3 + y.e07.d3, x.e07.d4 + y.e07.d4),
        UnreducedBigInt5(x.e08.d0 + y.e08.d0, x.e08.d1 + y.e08.d1, x.e08.d2 + y.e08.d2, x.e08.d3 + y.e08.d3, x.e08.d4 + y.e08.d4),
        UnreducedBigInt5(x.e09.d0 + y.e09.d0, x.e09.d1 + y.e09.d1, x.e09.d2 + y.e09.d2, x.e09.d3 + y.e09.d3, x.e09.d4 + y.e09.d4),
        UnreducedBigInt5(x.e0A.d0 + y.e0A.d0, x.e0A.d1 + y.e0A.d1, x.e0A.d2 + y.e0A.d2, x.e0A.d3 + y.e0A.d3, x.e0A.d4 + y.e0A.d4),
        UnreducedBigInt5(x.e0B.d0 + y.e0B.d0, x.e0B.d1 + y.e0B.d1, x.e0B.d2 + y.e0B.d2, x.e0B.d3 + y.e0B.d3, x.e0B.d4 + y.e0B.d4),
        UnreducedBigInt5(x.e0C.d0 + y.e0C.d0, x.e0C.d1 + y.e0C.d1, x.e0C.d2 + y.e0C.d2, x.e0C.d3 + y.e0C.d3, x.e0C.d4 + y.e0C.d4),
        UnreducedBigInt5(x.e0D.d0 + y.e0D.d0, x.e0D.d1 + y.e0D.d1, x.e0D.d2 + y.e0D.d2, x.e0D.d3 + y.e0D.d3, x.e0D.d4 + y.e0D.d4),
        UnreducedBigInt5(x.e0E.d0 + y.e0E.d0, x.e0E.d1 + y.e0E.d1, x.e0E.d2 + y.e0E.d2, x.e0E.d3 + y.e0E.d3, x.e0E.d4 + y.e0E.d4),
        UnreducedBigInt5(x.e0F.d0 + y.e0F.d0, x.e0F.d1 + y.e0F.d1, x.e0F.d2 + y.e0F.d2, x.e0F.d3 + y.e0F.d3, x.e0F.d4 + y.e0F.d4),
        UnreducedBigInt5(x.e10.d0 + y.e10.d0, x.e10.d1 + y.e10.d1, x.e10.d2 + y.e10.d2, x.e10.d3 + y.e10.d3, x.e10.d4 + y.e10.d4),
        UnreducedBigInt5(x.e11.d0 + y.e11.d0, x.e11.d1 + y.e11.d1, x.e11.d2 + y.e11.d2, x.e11.d3 + y.e11.d3, x.e11.d4 + y.e11.d4),
        UnreducedBigInt5(x.e12.d0 + y.e12.d0, x.e12.d1 + y.e12.d1, x.e12.d2 + y.e12.d2, x.e12.d3 + y.e12.d3, x.e12.d4 + y.e12.d4),
        UnreducedBigInt5(x.e13.d0 + y.e13.d0, x.e13.d1 + y.e13.d1, x.e13.d2 + y.e13.d2, x.e13.d3 + y.e13.d3, x.e13.d4 + y.e13.d4),
        UnreducedBigInt5(x.e14.d0 + y.e14.d0, x.e14.d1 + y.e14.d1, x.e14.d2 + y.e14.d2, x.e14.d3 + y.e14.d3, x.e14.d4 + y.e14.d4),
        UnreducedBigInt5(x.e15.d0 + y.e15.d0, x.e15.d1 + y.e15.d1, x.e15.d2 + y.e15.d2, x.e15.d3 + y.e15.d3, x.e15.d4 + y.e15.d4),
        UnreducedBigInt5(x.e16.d0 + y.e16.d0, x.e16.d1 + y.e16.d1, x.e16.d2 + y.e16.d2, x.e16.d3 + y.e16.d3, x.e16.d4 + y.e16.d4),
        ))
end

func ufq23_12_diff(x : UnreducedFQ23, y : FQ12) -> (res : UnreducedFQ23):
    return (
        res=UnreducedFQ23(
        UnreducedBigInt5(x.e00.d0 - y.e0.d0, x.e00.d1 - y.e0.d1, x.e00.d2 - y.e0.d2, x.e00.d3, x.e00.d4),
        UnreducedBigInt5(x.e01.d0 - y.e1.d0, x.e01.d1 - y.e1.d1, x.e01.d2 - y.e1.d2, x.e01.d3, x.e01.d4),
        UnreducedBigInt5(x.e02.d0 - y.e2.d0, x.e02.d1 - y.e2.d1, x.e02.d2 - y.e2.d2, x.e02.d3, x.e02.d4),
        UnreducedBigInt5(x.e03.d0 - y.e3.d0, x.e03.d1 - y.e3.d1, x.e03.d2 - y.e3.d2, x.e03.d3, x.e03.d4),
        UnreducedBigInt5(x.e04.d0 - y.e4.d0, x.e04.d1 - y.e4.d1, x.e04.d2 - y.e4.d2, x.e04.d3, x.e04.d4),
        UnreducedBigInt5(x.e05.d0 - y.e5.d0, x.e05.d1 - y.e5.d1, x.e05.d2 - y.e5.d2, x.e05.d3, x.e05.d4),
        UnreducedBigInt5(x.e06.d0 - y.e6.d0, x.e06.d1 - y.e6.d1, x.e06.d2 - y.e6.d2, x.e06.d3, x.e06.d4),
        UnreducedBigInt5(x.e07.d0 - y.e7.d0, x.e07.d1 - y.e7.d1, x.e07.d2 - y.e7.d2, x.e07.d3, x.e07.d4),
        UnreducedBigInt5(x.e08.d0 - y.e8.d0, x.e08.d1 - y.e8.d1, x.e08.d2 - y.e8.d2, x.e08.d3, x.e08.d4),
        UnreducedBigInt5(x.e09.d0 - y.e9.d0, x.e09.d1 - y.e9.d1, x.e09.d2 - y.e9.d2, x.e09.d3, x.e09.d4),
        UnreducedBigInt5(x.e0A.d0 - y.eA.d0, x.e0A.d1 - y.eA.d1, x.e0A.d2 - y.eA.d2, x.e0A.d3, x.e0A.d4),
        UnreducedBigInt5(x.e0B.d0 - y.eB.d0, x.e0B.d1 - y.eB.d1, x.e0B.d2 - y.eB.d2, x.e0B.d3, x.e0B.d4),
        x.e0C,
        x.e0D,
        x.e0E,
        x.e0F,
        x.e10,
        x.e11,
        x.e12,
        x.e13,
        x.e14,
        x.e15,
        x.e16,
        ))
end
