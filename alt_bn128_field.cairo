from bigint import BASE, BigInt3, UnreducedBigInt3, UnreducedBigInt5, nondet_bigint3, bigint_mul
from alt_bn128_def import P0, P1, P2

# is val = 0 mod n ?
func verify_zero5{range_check_ptr}(val : UnreducedBigInt5):
    alloc_locals
    local flag
    local q1
    %{
        from starkware.cairo.common.cairo_secp.secp_utils import pack

        P = 0x30644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd47

        v3 = ids.val.d3 if ids.val.d3 < PRIME//2 else ids.val.d3 - PRIME
        v4 = ids.val.d4 if ids.val.d4 < PRIME//2 else ids.val.d4 - PRIME
        rv = ids.val
        v = pack(rv, PRIME) + v3*2**258 + v4*2**344

        q, r = divmod(v, P)
        # Since q usually doesn't git bigint_3, divide it again
        q1, q2 = divmod(q, P)
        ids.q1 = q1 if q > 0 else 0-q1

        assert r == 0, f"verify_zero: Invalid input {ids.val.d0, ids.val.d1, ids.val.d2, ids.val.d3, ids.val.d4}."
        value = q2 if q > 0 else 0 - q2
        ids.flag = 1 if q > 0 else 0
        # print(len(f'{value:b}'), f'{value:b}')
        # print(ids.q1, q2, ids.flag)
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

# return 1 if x ==0 mod alt_bn128 prime
func is_zero{range_check_ptr}(x : BigInt3) -> (res : felt):
    %{
        from starkware.cairo.common.cairo_secp.secp_utils import pack
        P = 0x30644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd47
        x = pack(ids.x, PRIME) % P
    %}
    if nondet %{ x == 0 %} != 0:
        verify_zero5(UnreducedBigInt5(d0=x.d0, d1=x.d1, d2=x.d2, d3=0, d4=0))
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
