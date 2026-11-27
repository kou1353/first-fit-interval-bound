"""Independent, exact audit of the reciprocal charges in the interval proof.

Run with Python 3.10+. This script uses no external modules or workspace
imports. Directions are recomputed from snapshots of the active point list.
"""

from fractions import Fraction as Q
from itertools import groupby, product
from random import Random
from time import process_time


def history(masks, point_count, price):
    active = list(range(point_count))
    cash = [Q(0)] * point_count
    rounds = []
    while active:
        step = len(rounds)
        mask = masks[step] if step < len(masks) else 0
        hit = {x for x in active if mask >> x & 1}
        events = {}
        following = []
        for i, x in enumerate(active):
            adjacent = active[max(0, i-1):i] + active[i+1:i+2]
            if x in hit:
                event, income = "R", price
            elif any(y in hit for y in adjacent):
                event, income = "B", Q(1)
            else:
                event, income = "F", Q(0)
            cash[x] += income - 1
            if event == "F" and cash[x] <= 0:
                event = "D"
            else:
                following.append(x)
            events[x] = event
        rounds.append((active, events))
        active = following
    return rounds


def audit(rounds, price):
    n = len(rounds)
    switches = missing = 0
    for t in rounds[-1][0]:
        terminal = [events[t] for _,events in rounds]
        r, b = terminal.count("R"), terminal.count("B")
        assert n-1 <= price*r + b
        side_charges = [Q(0) for _ in rounds]
        for direction in (-1, 1):
            slots = []
            for active, events in rounds:
                i = active.index(t) + direction
                slots.append(active[i] if 0 <= i < len(active) else None)
            epochs = [(y, list(times)) for y,times in
                      groupby(range(n), key=lambda i: slots[i])]
            switches += sum(y is not None for y,_ in epochs[1:])
            for y, times in epochs:
                missing += y is None
                cost = Q(0)
                for i in times:
                    events = rounds[i][1]
                    if y is None:
                        contribution = Q(1) if events[t] == "R" else Q(0)
                    else:
                        contribution = {"R": price, "B": 1, "F": 0, "D": 0}[events[y]]
                    side_charges[i] += contribution
                    cost += contribution
                if y is not None:
                    assert rounds[times[-1]][1][y] == "D", "friendship ended before death"
                assert cost <= len(times), "overdrawn completed epoch"
        for e, charge in zip(terminal, side_charges):
            demand = {"R": 2, "B": price, "F": 0, "D": 0}[e]
            assert charge >= demand
        assert 2*r + price*b <= sum(side_charges) <= 2*n
        assert (price-2)*n <= (price*price-2)*r + price
    return switches, missing


def color(intervals):
    assigned = []
    for i, (l,r) in enumerate(intervals):
        seen = {c for (a,b),c in zip(intervals[:i],assigned) if a <= r and l <= b}
        c = 1
        while c in seen:
            c += 1
        assigned.append(c)
    return assigned


def graph_case(intervals, price):
    colors = color(intervals)
    # All left endpoints are a point cover, including nonmaximal cliques.
    pts = sorted({a for a,b in intervals})
    m = max(colors)
    masks = [0]*m
    spans = []
    loads = [0]*len(pts)
    for (a,b),c in zip(intervals,colors):
        live = {i for i,p in enumerate(pts) if a <= p <= b}
        spans.append(live)
        for i in live:
            masks[c-1] |= 1 << i
            loads[i] += 1
    omega = max(loads)
    rounds = history(masks,len(pts),price)
    for i in range(m):
        before, events = rounds[i]
        after = {x for x in before if events[x] != "D"}
        assert all(s & after for s,c in zip(spans,colors) if c >= i+1)
    assert len(rounds) >= m+3
    switches, missing = audit(rounds,price)
    assert (price-2)*m <= (price**2-2)*omega + 6-2*price
    return m, omega, switches, missing


def kst_wall(level):
    # Four intervals with private attachment points, KST Fig. 4 (the
    # Chrobak--Slusarek/Witsenhausen three-color increment), with T_0=K_1.
    seq = [(0,1)]
    for _ in range(level):
        w = max(r for _,r in seq)-min(l for l,_ in seq)+1
        offset = min(l for l,_ in seq)
        copies = [(p*w+l-offset,p*w+r-offset) for p in (1,3,5,7) for l,r in seq]
        seq = copies + [(w*l,w*r) for l,r in ((0,2),(6,8),(2,4),(4,6))]
    return seq


def mixed_cases(rng):
    # R-open < closed endpoints < L-open at the same coordinate.
    for _ in range(80):
        mixed, closed = [], []
        for _ in range(rng.randrange(4,24)):
            l,r = sorted((rng.randrange(9),rng.randrange(9)))
            lc,rc = (True,True) if l == r else (rng.choice((False,True)),rng.choice((False,True)))
            mixed.append((l,r,lc,rc))
            closed.append((3*l+(not lc),3*r-(not rc)))
        def contains(v,x):
            l,r,lc,rc = v
            return (l<x or lc and l==x) and (x<r or rc and x==r)
        for i,u in enumerate(mixed):
            for j,v in enumerate(mixed):
                l,r = max(u[0],v[0]),min(u[1],v[1])
                intersects = l < r or l == r and contains(u,l) and contains(v,l)
                a,b = closed[i]
                c,d = closed[j]
                assert intersects == (a<=d and c<=b)
        yield closed


def check_lp():
    for p in (Q(4), Q(7,2), Q(17,5), Q(99,29)):
        # Normalized homogeneous LP, primal and dual certificates.
        det = p*p-2
        r,b = (p-2)/det, (2*p-2)/det
        u,v = p/det, 1/det
        assert min(r,b,u,v) >= 0
        assert p*r+b == 1 and 2*r+p*b == 2
        assert p*u-2*v == 1 and u-p*v == 0 and u-2*v == r
        assert 1/r == 4+(p-2)+2/(p-2)
    p = Q(17,5)
    assert (p*p-2)/(p-2) == Q(239,35)
    assert (6-2*p)/(p-2) == -Q(4,7)
    # Exact symbolic minimization: for t>0, t+2/t>0, and
    # (t+2/t)^2-8 = (t-2/t)^2 with equality when t^2=2.
    for t in (Q(1), Q(7,5), Q(3,2), Q(2)):
        assert (t+2/t)**2-8 == (t-2/t)**2


def main():
    start = process_time()
    check_lp()
    rng = Random(1705)
    switches = missing = cases = 0
    for p in (Q(4), Q(17,5)):
        for masks in product(range(8),repeat=3):
            a,b = audit(history(masks,3,p),p)
            switches += a
            missing += b
            cases += 1
    for _ in range(250):
        q = rng.randrange(4,12)
        masks = [rng.randrange(1<<q) for _ in range(rng.randrange(4,15))]
        a,b = audit(history(masks,q,Q(17,5)),Q(17,5))
        switches += a
        missing += b
        cases += 1
    assert switches and missing
    print(f"abstract histories={cases}, slot replacements={switches}, vacant epochs={missing}")
    for seq in mixed_cases(rng):
        graph_case(seq,Q(17,5))
    seq = kst_wall(4)
    m,k,_,_ = graph_case(seq,Q(17,5))
    assert (m,k) == (13,5)
    print(f"mixed-endpoint graphs=80, KST T4 intervals={len(seq)} FF={m} omega={k}")
    # Completed-epoch bound fails on a prefix, even on two disjoint intervals.
    prefix = history([3],2,Q(17,5))
    assert prefix[0][1] == {0:"R",1:"R"} and Q(17,5) > 1
    print("one-round prefix charge=17/5 > 1; completed epochs passed")
    print("exact LP coefficient=239/35, additive=-4/7")
    print(f"cpu_seconds={process_time()-start:.3f}")


if __name__ == "__main__":
    main()
