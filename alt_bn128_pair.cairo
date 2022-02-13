from bigint import BigInt3, nondet_bigint3, bigint_mul, UnreducedBigInt5
from alt_bn128_field import is_zero
from alt_bn128_ec import (
    EcPoint, compute_slope, compute_doubling_slope, verify_zero5, G12Point, FQ12)

const ate_loop_count = 29793968203157093288
const log_ate_loop_count = 63

# TODO

func bigZero() -> (res : BigInt3):
    return (BigInt3(0, 0, 0))
end

func linehelp{range_check_ptr}(pt0 : EcPoint, pt1 : EcPoint, t : EcPoint, slope : BigInt3) -> (
        res : BigInt3):
    %{
        from starkware.cairo.common.cairo_secp.secp_utils import pack
        from starkware.python.math_utils import div_mod

        P = 0x30644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd47
        # Compute the point.
        x1 = pack(ids.pt1.x, PRIME)
        y1 = pack(ids.pt1.y, PRIME)
        xt = pack(ids.t.x, PRIME)
        yt = pack(ids.t.y, PRIME)
        slope = pack(ids.slope, PRIME)

        value = res = (slope * (xt - x1) - (yt - y1)) % P
    %}
    let (res : BigInt3) = nondet_bigint3()
    let (x_diff_slope : UnreducedBigInt5) = bigint_mul(
        BigInt3(d0=t.x.d0 - pt1.x.d0, d1=t.x.d1 - pt1.x.d1, d2=t.x.d2 - pt1.x.d2), slope)

    verify_zero5(
        UnreducedBigInt5(
        d0=x_diff_slope.d0 - t.y.d0 + pt1.y.d0 - res.d0,
        d1=x_diff_slope.d1 - t.y.d1 + pt1.y.d1 - res.d1,
        d2=x_diff_slope.d2 - t.y.d2 + pt1.y.d2 - res.d2,
        d3=x_diff_slope.d3,
        d4=x_diff_slope.d4))

    return (res)
end

# Evaluates the line through pt1 -- pt2 at t
func linefunc{range_check_ptr}(pt0 : EcPoint, pt1 : EcPoint, t : EcPoint) -> (res : BigInt3):
    let x_diff = BigInt3(d0=pt0.x.d0 - pt1.x.d0, d1=pt0.x.d1 - pt1.x.d1, d2=pt0.x.d2 - pt1.x.d2)
    let (same_x : felt) = is_zero(x_diff)

    if same_x == 0:
        let (slope : BigInt3) = compute_slope(pt0, pt1)
        let (res : BigInt3) = linehelp(pt0, pt1, t, slope)
        return (res=res)
    else:
        let y_diff = BigInt3(d0=pt0.y.d0 - pt1.y.d0, d1=pt0.y.d1 - pt1.y.d1, d2=pt0.y.d2 - pt1.y.d2)
        let (same_y : felt) = is_zero(y_diff)
        if same_y == 1:
            let (slope : BigInt3) = compute_doubling_slope(pt0)
            let (res : BigInt3) = linehelp(pt0, pt1, t, slope)
            return (res=res)
        else:
            return (
                res=BigInt3(
                d0=t.x.d0 - pt0.x.d0, d1=t.x.d1 - pt0.x.d1, d2=t.x.d2 - pt0.x.d2))
        end
    end
end

func to_fq12(pt : EcPoint) -> (res : G12Point):
    # Point should not be zero
    let (zero) = is_zero(pt)
    assert zero = 0

    return (
        G12Point(
        x=FQ12(pt.x, bigZero(), bigZero(), bigZero(),
            bigZero(), bigZero(), bigZero(), bigZero(),
            bigZero(), bigZero(), bigZero(), bigZero()),
        y=FQ12(pt.y, bigZero(), bigZero(), bigZero(),
            bigZero(), bigZero(), bigZero(), bigZero(),
            bigZero(), bigZero(), bigZero(), bigZero())))
end

# # "Twist" a point in E(FQ2) into a point in E(FQ12)
# w = FQ12([0, 1] + [0] * 10)

func w() -> (res : FQ12):
    return (
        res=FQ12(
        bigZero(), BigInt3(1, 0, 0), bigZero(), bigZero(),
        bigZero(), bigZero(), bigZero(), bigZero(),
        bigZero(), bigZero(), bigZero(), bigZero()))
end

# def twist(pt):
#     if pt is None:
#         return None
#     _x, _y = pt
#     # Field isomorphism from Z[p] / x**2 to Z[p] / x**2 - 18*x + 82
#     xcoeffs = [_x.coeffs[0] - _x.coeffs[1] * 9, _x.coeffs[1]]
#     ycoeffs = [_y.coeffs[0] - _y.coeffs[1] * 9, _y.coeffs[1]]
#     # Isomorphism into subfield of Z[p] / w**12 - 18 * w**6 + 82,
#     # where w**6 = x
#     nx = FQ12([xcoeffs[0]] + [0] * 5 + [xcoeffs[1]] + [0] * 5)
#     ny = FQ12([ycoeffs[0]] + [0] * 5 + [ycoeffs[1]] + [0] * 5)
#     # Divide x coord by w**2 and y coord by w**3
#    return (nx * w **2, ny * w**3)

func twist(P : EcPoint):
end

func miller_loop():
end

func pairing(Q : EcPoint, P : EcPoint):
    return miller_loop(twist(Q), to_fq12(P))
end
