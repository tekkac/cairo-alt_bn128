from bigint import BigInt3, nondet_bigint3
from alt_bn128_field import is_zero
from alt_bn128_ec import EcPoint, compute_slope

const ate_loop_count = 29793968203157093288
const log_ate_loop_count = 63

# TODO

# Evaluates the line through pt1 -- pt2 at t
func linefunc{range_check_ptr}(pt0 : EcPoint, pt1 : EcPoint, t : EcPoint) -> (res : BigInt3):
    # if x1 != x2:
    #     m = (y2 - y1) / (x2 - x1)
    #     return m * (xt - x1) - (yt - y1)
    # elif y1 == y2:
    #     m = 3 * x1**2 / (2 * y1)
    #     return m * (xt - x1) - (yt - y1)
    # else:
    #     return xt - x1

    let x_diff = BigInt3(d0=pt0.x.d0 - pt1.x.d0, d1=pt0.x.d1 - pt1.x.d1, d2=pt0.x.d2 - pt1.x.d2)
    let (same_x : felt) = is_zero(x_diff)
    if same_x == 0:
        # pt0.x != pt1.x
        let (slope : BigInt3) = compute_slope(pt0, pt1)
        %{
            from starkware.cairo.common.cairo_secp.secp_utils import pack
            from starkware.python.math_utils import div_mod

            P = 0x30644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd47
            # Compute the slope.
            x0 = pack(ids.pt0.x, PRIME)
            y0 = pack(ids.pt0.y, PRIME)
            xt = pack(ids.pt0.t, PRIME)
            x1 = pack(ids.pt1.x, PRIME)
            y1 = pack(ids.pt1.y, PRIME)
            yt = pack(ids.pt1.t, PRIME)

            value = res = slope * (xt - x1) - (yt - y1)
        %}
        let (res : BigInt3) = nondet_bigint3()
        return (res=res)
    end
    return (res=BigInt3(0, 0, 0))
end

func to_fq12(p : EcPoint):
    if p.x == 0:
        if p.y == 0:
            return (EcPoint(BigInt3(0, 0, 0), BigInt3(0, 0, 0)))
        end
    end
    return ()
    # x=[pt.x,0,0, 0,0,0, 0,0,0, 0,0,0],
    #        y=[pt.y,0,0, 0,0,0, 0,0,0, 0,0,0]))
end

func miller_loop():
end

# Put in EC?
func twist(P : EcPoint):
end

func pairing(Q : EcPoint, P : EcPoint):
    return miller_loop(twist(Q), to_fq12(P))
end
