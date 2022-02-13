from bigint import BigInt3, UnreducedBigInt3, nondet_bigint3, UnreducedBigInt5, bigint_mul
from alt_bn128_field import is_zero, verify_zero5
from alt_bn128_def import P0, P1, P2

# Represents a point on the elliptic curve.
# The zero point is represented using pt.x=0, as there is no point on the curve with this x value.
struct EcPoint:
    member x : BigInt3
    member y : BigInt3
end

func G1() -> (res : EcPoint):
    return (res=EcPoint(BigInt3(1, 0, 0), BigInt3(2, 0, 0)))
end

# Returns the slope of the elliptic curve at the given point.
# The slope is used to compute pt + pt.
# Assumption: pt != 0.
func compute_doubling_slope{range_check_ptr}(pt : EcPoint) -> (slope : BigInt3):
    # Note that y cannot be zero: assume that it is, then pt = -pt, so 2 * pt = 0, which
    # contradicts the fact that the size of the curve is odd.
    %{
        from starkware.cairo.common.cairo_secp.secp_utils import pack
        from starkware.python.math_utils import div_mod

        P = 0x30644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd47

        # Compute the slope.
        x = pack(ids.pt.x, PRIME)
        y = pack(ids.pt.y, PRIME)
        value = slope = div_mod(3 * x ** 2, 2 * y, P)
        # print(len(f'{x:b}'), len(f'{y:b}'), value, len(f'{value:b}'))
    %}
    let (slope : BigInt3) = nondet_bigint3()

    let (x_sqr : UnreducedBigInt5) = bigint_mul(pt.x, pt.x)
    let (slope_y : UnreducedBigInt5) = bigint_mul(slope, pt.y)

    verify_zero5(
        UnreducedBigInt5(
        d0=3 * x_sqr.d0 - 2 * slope_y.d0,
        d1=3 * x_sqr.d1 - 2 * slope_y.d1,
        d2=3 * x_sqr.d2 - 2 * slope_y.d2,
        d3=3 * x_sqr.d3 - 2 * slope_y.d3,
        d4=3 * x_sqr.d4 - 2 * slope_y.d4))

    return (slope=slope)
end

# Returns the slope of the line connecting the two given points.
# The slope is used to compute pt0 + pt1.
# Assumption: pt0.x != pt1.x (mod field prime).
func compute_slope{range_check_ptr}(pt0 : EcPoint, pt1 : EcPoint) -> (slope : BigInt3):
    %{
        from starkware.cairo.common.cairo_secp.secp_utils import pack
        from starkware.python.math_utils import div_mod

        P = 0x30644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd47
        # Compute the slope.
        x0 = pack(ids.pt0.x, PRIME)
        y0 = pack(ids.pt0.y, PRIME)
        x1 = pack(ids.pt1.x, PRIME)
        y1 = pack(ids.pt1.y, PRIME)
        value = slope = div_mod(y0 - y1, x0 - x1, P)
    %}
    let (slope) = nondet_bigint3()

    let x_diff = BigInt3(d0=pt0.x.d0 - pt1.x.d0, d1=pt0.x.d1 - pt1.x.d1, d2=pt0.x.d2 - pt1.x.d2)
    let (x_diff_slope : UnreducedBigInt5) = bigint_mul(x_diff, slope)

    verify_zero5(
        UnreducedBigInt5(
        d0=x_diff_slope.d0 - pt0.y.d0 + pt1.y.d0,
        d1=x_diff_slope.d1 - pt0.y.d1 + pt1.y.d1,
        d2=x_diff_slope.d2 - pt0.y.d2 + pt1.y.d2,
        d3=x_diff_slope.d3,
        d4=x_diff_slope.d4))

    return (slope)
end

# Given a point 'pt' on the elliptic curve, computes pt + pt.
func ec_double{range_check_ptr}(pt : EcPoint) -> (res : EcPoint):
    if pt.x.d0 == 0:
        if pt.x.d1 == 0:
            if pt.x.d2 == 0:
                return (pt)
            end
        end
    end

    let (slope : BigInt3) = compute_doubling_slope(pt)
    let (slope_sqr : UnreducedBigInt5) = bigint_mul(slope, slope)

    %{
        from starkware.cairo.common.cairo_secp.secp_utils import pack

        P = 0x30644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd47
        slope = pack(ids.slope, PRIME)
        x = pack(ids.pt.x, PRIME)
        y = pack(ids.pt.y, PRIME)

        value = new_x = (pow(slope, 2, P) - 2 * x) % P
    %}
    let (new_x : BigInt3) = nondet_bigint3()

    %{ value = new_y = (slope * (x - new_x) - y) % P %}
    let (new_y : BigInt3) = nondet_bigint3()

    verify_zero5(
        UnreducedBigInt5(
        d0=slope_sqr.d0 - new_x.d0 - 2 * pt.x.d0,
        d1=slope_sqr.d1 - new_x.d1 - 2 * pt.x.d1,
        d2=slope_sqr.d2 - new_x.d2 - 2 * pt.x.d2,
        d3=slope_sqr.d3,
        d4=slope_sqr.d4))

    let (x_diff_slope : UnreducedBigInt5) = bigint_mul(
        BigInt3(d0=pt.x.d0 - new_x.d0, d1=pt.x.d1 - new_x.d1, d2=pt.x.d2 - new_x.d2), slope)

    verify_zero5(
        UnreducedBigInt5(
        d0=x_diff_slope.d0 - pt.y.d0 - new_y.d0,
        d1=x_diff_slope.d1 - pt.y.d1 - new_y.d1,
        d2=x_diff_slope.d2 - pt.y.d2 - new_y.d2,
        d3=x_diff_slope.d3,
        d4=x_diff_slope.d4))

    return (EcPoint(new_x, new_y))
end

# Adds two points on the elliptic curve.
# Assumption: pt0.x != pt1.x (however, pt0 = pt1 = 0 is allowed).
# Note that this means that the function cannot be used if pt0 = pt1
# (use ec_double() in this case) or pt0 = -pt1 (the result is 0 in this case).
func fast_ec_add{range_check_ptr}(pt0 : EcPoint, pt1 : EcPoint) -> (res : EcPoint):
    if pt0.x.d0 == 0:
        if pt0.x.d1 == 0:
            if pt0.x.d2 == 0:
                return (pt1)
            end
        end
    end
    if pt1.x.d0 == 0:
        if pt1.x.d1 == 0:
            if pt1.x.d2 == 0:
                return (pt0)
            end
        end
    end

    let (slope : BigInt3) = compute_slope(pt0, pt1)
    let (slope_sqr : UnreducedBigInt5) = bigint_mul(slope, slope)

    %{
        from starkware.cairo.common.cairo_secp.secp_utils import pack

        P = 0x30644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd47
        slope = pack(ids.slope, PRIME)
        x0 = pack(ids.pt0.x, PRIME)
        x1 = pack(ids.pt1.x, PRIME)
        y0 = pack(ids.pt0.y, PRIME)

        value = new_x = (pow(slope, 2, P) - x0 - x1) % P
    %}
    let (new_x : BigInt3) = nondet_bigint3()

    %{ value = new_y = (slope * (x0 - new_x) - y0) % P %}
    let (new_y : BigInt3) = nondet_bigint3()

    verify_zero5(
        UnreducedBigInt5(
        d0=slope_sqr.d0 - new_x.d0 - pt0.x.d0 - pt1.x.d0,
        d1=slope_sqr.d1 - new_x.d1 - pt0.x.d1 - pt1.x.d1,
        d2=slope_sqr.d2 - new_x.d2 - pt0.x.d2 - pt1.x.d2,
        d3=slope_sqr.d3,
        d4=slope_sqr.d4))

    let (x_diff_slope : UnreducedBigInt5) = bigint_mul(
        BigInt3(d0=pt0.x.d0 - new_x.d0, d1=pt0.x.d1 - new_x.d1, d2=pt0.x.d2 - new_x.d2), slope)

    verify_zero5(
        UnreducedBigInt5(
        d0=x_diff_slope.d0 - pt0.y.d0 - new_y.d0,
        d1=x_diff_slope.d1 - pt0.y.d1 - new_y.d1,
        d2=x_diff_slope.d2 - pt0.y.d2 - new_y.d2,
        d3=x_diff_slope.d3,
        d4=x_diff_slope.d4))

    return (EcPoint(new_x, new_y))
end

# Same as fast_ec_add, except that the cases pt0 = ±pt1 are supported.
func ec_add{range_check_ptr}(pt0 : EcPoint, pt1 : EcPoint) -> (res : EcPoint):
    let x_diff = BigInt3(d0=pt0.x.d0 - pt1.x.d0, d1=pt0.x.d1 - pt1.x.d1, d2=pt0.x.d2 - pt1.x.d2)
    let (same_x : felt) = is_zero(x_diff)
    if same_x == 0:
        # pt0.x != pt1.x so we can use fast_ec_add.
        return fast_ec_add(pt0, pt1)
    end

    # We have pt0.x = pt1.x. This implies pt0.y = ±pt1.y.
    # Check whether pt0.y = -pt1.y.
    let y_sum = BigInt3(d0=pt0.y.d0 + pt1.y.d0, d1=pt0.y.d1 + pt1.y.d1, d2=pt0.y.d2 + pt1.y.d2)
    let (opposite_y : felt) = is_zero(y_sum)
    if opposite_y != 0:
        # pt0.y = -pt1.y.
        # Note that the case pt0 = pt1 = 0 falls into this branch as well.
        let ZERO_POINT = EcPoint(BigInt3(0, 0, 0), BigInt3(0, 0, 0))
        return (ZERO_POINT)
    else:
        # pt0.y = pt1.y.
        return ec_double(pt0)
    end
end

# Given 0 <= m < 250, a scalar and a point on the elliptic curve, pt,
# verifies that 0 <= scalar < 2**m and returns (2**m * pt, scalar * pt).
func ec_mul_inner{range_check_ptr}(pt : EcPoint, scalar : felt, m : felt) -> (
        pow2 : EcPoint, res : EcPoint):
    if m == 0:
        assert scalar = 0
        let ZERO_POINT = EcPoint(BigInt3(0, 0, 0), BigInt3(0, 0, 0))
        return (pow2=pt, res=ZERO_POINT)
    end

    alloc_locals
    let (double_pt : EcPoint) = ec_double(pt)
    %{ memory[ap] = (ids.scalar % PRIME) % 2 %}
    jmp odd if [ap] != 0; ap++
    return ec_mul_inner(pt=double_pt, scalar=scalar / 2, m=m - 1)

    odd:
    let (local inner_pow2 : EcPoint, inner_res : EcPoint) = ec_mul_inner(
        pt=double_pt, scalar=(scalar - 1) / 2, m=m - 1)
    # Here inner_res = (scalar - 1) / 2 * double_pt = (scalar - 1) * pt.
    # Assume pt != 0 and that inner_res = ±pt. We obtain (scalar - 1) * pt = ±pt =>
    # scalar - 1 = ±1 (mod N) => scalar = 0 or 2.
    # In both cases (scalar - 1) / 2 cannot be in the range [0, 2**(m-1)), so we get a
    # contradiction.
    let (res : EcPoint) = fast_ec_add(pt0=pt, pt1=inner_res)
    return (pow2=inner_pow2, res=res)
end

func ec_mul{range_check_ptr}(pt : EcPoint, scalar : BigInt3) -> (res : EcPoint):
    alloc_locals
    let (pow2_0 : EcPoint, local res0 : EcPoint) = ec_mul_inner(pt, scalar.d0, 86)
    let (pow2_1 : EcPoint, local res1 : EcPoint) = ec_mul_inner(pow2_0, scalar.d1, 86)
    let (_, local res2 : EcPoint) = ec_mul_inner(pow2_1, scalar.d2, 84)
    let (res : EcPoint) = ec_add(res0, res1)
    let (res : EcPoint) = ec_add(res, res2)
    return (res)
end

struct G2Point:
    member x0 : BigInt3
    member x1 : BigInt3
    member y0 : BigInt3
    member y1 : BigInt3
end

struct FQ12:
    member b0 : BigInt3
    member b1 : BigInt3
    member b2 : BigInt3
    member b3 : BigInt3
    member b4 : BigInt3
    member b5 : BigInt3
    member b6 : BigInt3
    member b7 : BigInt3
    member b8 : BigInt3
    member b9 : BigInt3
    member bA : BigInt3
    member bB : BigInt3
    member bC : BigInt3
end

struct G12Point:
    member x : FQ12
    member y : FQ12
end

func G2() -> (res : G2Point):
    return (
        res=G2Point(
        x0=BigInt3(0x29e71297e485b7aef312c2, 0x3edcc7ed7497c6a924ccd6, 0x198e9393920d483a7260b),
        x1=BigInt3(0x1edadd46debd5cd992f6ed, 0x199797111e59d0c8b53dd, 0x1800deef121f1e76426a0),
        y0=BigInt3(0x338ef355acdadcd122975b, 0x26b5a430ce56f12cc4cdc2, 0x90689d0585ff075ec9e9),
        y1=BigInt3(0x3d37b4ce6cc0166fa7daa, 0x602372d023f8f479da431, 0x12c85ea5db8c6deb4aab7)))
end
