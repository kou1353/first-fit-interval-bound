"""Exact column accounting for First-Fit walls. Python 3.10+, standard library.

Run alongside anchored_walls.py. The default rebuilds the small anchor
certificates and checks random, recursively constructed and endpoint-tie cases.
"""

from bisect import bisect_left, bisect_right
from fractions import Fraction
from itertools import accumulate
from random import Random
from time import process_time

import anchored_walls as walls


def maximal_cover(intervals):
    """Ordered maximal cliques, followed by a minimum-cardinality stabbing set."""
    # At successive left endpoints, the active clique is maximal if an end
    # is encountered before the next start. Starts precede ends at ties.
    starts = sorted({l for l, _ in intervals})
    ends = sorted(r for _, r in intervals)
    points = [x for j, x in enumerate(starts)
              if j + 1 == len(starts) or ends[bisect_left(ends, x)] < starts[j+1]]
    chosen = []
    for l, r in sorted(intervals, key=lambda v: v[1]):
        if not chosen or chosen[-1] < l:
            p = points[bisect_right(points, r)-1]
            assert l <= p <= r
            chosen.append(p)
    return chosen


def check_minimal_cover_rule(intervals, colors, pts):
    """NSB row 1 and adjacency-window fill test, lambda=4 (paper, section 2).

    rho counts the real labels from the first row of the current adjacency
    up to and including the preceding row. All labels are assigned in parallel.
    """
    m = max(colors)
    masks = [set() for _ in range(m+1)]
    spans = []
    for (l,r), c in zip(intervals, colors):
        lo, hi = bisect_left(pts,l), bisect_right(pts,r)
        spans.append((lo,hi,c))
        masks[c].update(range(lo,hi))
    active = list(range(len(pts)))
    first = {}
    real_prefix = [[0] for _ in active]
    row = 0
    while active:
        row += 1
        live = []
        hits = masks[row] if row <= m else set()
        for i,x in enumerate(active):
            neighbors = active[max(i-1,0):i] + active[i+1:i+2]
            occupied = x in hits
            keep = row == 1 or occupied or any(y in hits for y in neighbors)
            for y in neighbors:
                key = (min(x,y),max(x,y))
                if row == 1:
                    first[key] = 1
                else:
                    h = first.setdefault(key,row-1)
                    keep |= 4*(real_prefix[x][-1]-real_prefix[x][h-1]) > row-h
            real_prefix[x].append(real_prefix[x][-1]+occupied)
            if keep:
                live.append(x)
        if row <= m:
            for lo,hi,c in spans:
                if c >= row:
                    at = bisect_left(live,lo)
                    assert at < len(live) and live[at] < hi
        if not live:
            break
        active = live
    assert all(8*real_prefix[x][-1] >= m for x in active)


def columns(intervals, colors, points, epsilon=Fraction(1, 4), *, check_cover=True,
            credit_borrow=False):
    """All-suffix credit rule of Joret--Milans on an ordered point cover.

    Rows beyond the last color are processed until extinction. For every
    terminal column, record both friends' hits, including hits which are
    redundant, and borrowed rows on which positive credit was spent.
    """
    m = max(colors)
    num, den = epsilon.numerator, epsilon.denominator
    real_by_row = [set() for _ in range(m+1)]
    spans = []
    edge_load = [0]*(len(points)+1)
    for (l, r), c in zip(intervals, colors):
        a, b = bisect_left(points, l), bisect_right(points, r)
        assert a < b
        real_by_row[c].update(range(a, b))
        edge_load[a] += 1
        edge_load[b] -= 1
        spans.append((a, b, c))
    count = len(points)
    active = list(range(count))
    bank = [0] * count
    records = [[0] * 6 for _ in active]  # real, borrowed, fill, left, right, paid
    row = 0
    while active:
        row += 1
        occupied = real_by_row[row] if row <= m else set()
        alive = []
        for i, j in enumerate(active):
            real = j in occupied
            left = i > 0 and active[i-1] in occupied
            right = i+1 < len(active) and active[i+1] in occupied
            old = bank[j]
            borrowed = bool(not real and (left or right))
            bank[j] = max(0, old + den*real + num*(borrowed and credit_borrow) - num)
            if real:
                kind = 0
            elif left or right:
                kind = 1
            elif bank[j]:
                kind = 2
            else:
                continue
            rec = records[j]
            rec[kind] += 1
            rec[3] += left
            rec[4] += right
            rec[5] += min(num, old) if kind == 1 else 0
            alive.append(j)
        if check_cover and row <= m:
            for a, b, c in spans:
                if c >= row:
                    i = bisect_left(alive, a)
                    assert i < len(alive) and alive[i] < b, "a higher vertex lost its cover"
        if not alive:
            break
        active = alive
    cap = max(accumulate(edge_load))
    for j in active:
        r, b, f, left, right, paid = records[j]
        assert r+b+f == row-1 and cap >= r
        assert b <= left+right
        assert max(left, right) <= epsilon*row
        assert r >= epsilon*(r+f)
        if credit_borrow:
            lam = Fraction(den,num)
            assert lam*b + 2*r <= 2*row, ("coupled charge",row,records[j],points[j])
            assert lam*r+b >= row-1
            assert (lam**2-2)*r >= (lam-2)*row-lam
            if 3 < lam <= 4:
                assert row >= m+3
                assert (lam-2)*m <= (lam**2-2)*r + 6-2*lam
        elif epsilon == Fraction(1, 4):
            assert row >= m+3 and row <= 8*r
            assert 8*cap-m == 8*(cap-r) + (row-m) + (row-2*b) + 2*paid
    return row, cap, [tuple(records[j]) for j in active]


def exact_small_bounds(deadline):
    A = [0]
    for d, h in enumerate((3, 7, 11), 1):
        status, _, _ = walls.search(d, h+1, deadline)
        if status != "excluded":
            raise RuntimeError(f"anchor certificate incomplete at d={d}: {status}")
        A.append(h)
    U = [0]
    for k in range(1, 14):
        U.append(min(A[b-1]+1+2*(k-b)+U[k-b] for b in range(1, min(4,k)+1)))
    return A, U


def depth_everywhere(interval, family):
    """Minimum closed-interval load, including every open cell between events."""
    l, r = interval
    ends = sorted({l, r} | {x for pair in family for x in pair if l < x < r})
    sites = [2*x for x in ends] + [a+b for a, b in zip(ends, ends[1:])]
    return min(sum(2*a <= p <= 2*b for a, b in family) for p in sites)


def check_cut(intervals, colors, k, h, b, bound):
    """Check the entire localization argument, including the recoloring."""
    m = max(colors)
    if h > m:
        return
    cutoff = m - h
    high = [v for v, c in zip(intervals, colors) if c > cutoff]
    I = next(v for v in high if depth_everywhere(v, high) >= b)
    l, r = I
    endpoint = {c for (a, z), c in zip(intervals, colors)
                if c <= cutoff and (a <= l <= z or a <= r <= z)}
    assert len(endpoint) <= 2*(k-b)
    kept = [(v,c) for v,c in zip(intervals, colors)
            if c <= cutoff and c not in endpoint and l < v[0] <= v[1] < r]
    width, actual = walls.verify([v for v,c in kept])
    palette = sorted(set(range(1,cutoff+1)) - endpoint)
    assert {c for v,c in kept} == set(palette)
    assert actual == [bisect_left(palette,c)+1 for _,c in kept]
    assert width <= k-b and len(palette) <= bound


def recursive_samples():
    for d, h, levels in [(1,3,5), (2,7,3), (3,11,2)]:
        status, bags, _ = walls.search(d,h,process_time()+4)
        if status != "found":
            raise RuntimeError("could not reconstruct test wall")
        base, _, depth = walls.replay(bags,h)
        pts = walls.attachment_points(base,len(bags),depth)
        _, labels = walls.verify(base)
        _, measured_depth, _ = columns(base,labels,pts,Fraction(5,17),credit_borrow=True)
        assert measured_depth == depth and 35*h+20 <= 239*depth
        for t in range(1,levels+1):
            yield f"anchored({d},{t})", walls.expand(base,pts,t)


def run():
    start = process_time()
    A, U = exact_small_bounds(start+12)
    rng = Random(8127)
    cases = []
    for trial in range(220):
        n = rng.randrange(3,35)
        scope = rng.randrange(3,24)
        seq = [tuple(sorted((rng.randrange(scope),rng.randrange(scope)))) for _ in range(n)]
        rng.shuffle(seq)
        cases.append((f"random-{trial}",seq))
    cases.extend(recursive_samples())
    cuts = 0
    extreme = (Fraction(-1), None)
    for name, seq in cases:
        k, colors = walls.verify(seq)
        m = max(colors)
        pts = maximal_cover(seq)
        check_minimal_cover_rule(seq,colors,pts)
        n, cap, terminal = columns(seq,colors,pts)
        assert m <= 8*cap-3
        for rate in (Fraction(1,4),Fraction(2,7),Fraction(5,17)):
            n1, d1, term1 = columns(seq, colors, pts, rate, credit_borrow=True)
            lam = 1/rate
            assert (lam-2)*m <= (lam*lam-2)*d1 + lam
        if k <= 13:
            assert m <= U[k]
        if k >= 6:
            assert m <= 8*k-27
        if k >= 7:
            assert 35*m+544 <= 239*k
        if len(seq) <= 130:
            for b in range(1,min(k,4)+1):
                check_cut(seq, colors, k, A[b-1]+1, b,
                          U[k-b] if k-b < len(U) else 8*(k-b))
                cuts += (A[b-1]+1 <= m)
            for eps in (Fraction(1,3),Fraction(2,7)):
                columns(seq,colors,pts,eps)
        for r, beta, f, left, right, paid in terminal:
            if Fraction(beta,n) > extreme[0]:
                extreme = (Fraction(beta,n),(name,m,k,n,r,beta,f,left,right,paid))
        if name.startswith("anchored"):
            print(f"{name}: vertices={len(seq)} FF={m} omega={k}")
    for x in [Fraction(i,j) for j in range(3,32) for i in range(1,(j+1)//2)]:
        assert Fraction(1,8)-x*(1-2*x) == 2*(x-Fraction(1,4))**2
    assert U[7] == 25
    assert -8*8-3+1+14+U[7] == -27
    assert U[5] == 15
    assert -6*239-20 + 35*(1+10+U[5]) == -544
    print(f"checked={len(cases)}, nonvacuous geometric cuts={cuts}, F(7)<={U[7]}")
    print("largest observed borrowed fraction:", *extreme)
    print("reciprocal bound: 35*FF+20 <= 239*omega; hybrid for omega>=7: 35*FF+544 <= 239*omega")
    print(f"cpu_seconds={process_time()-start:.3f}")


if __name__ == "__main__":
    run()
