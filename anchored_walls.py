"""Search multi-way interval gadgets with a depth-d attachment point per interval.

Bag i is placed at coordinate 4*i. Each consecutive run a..b of a color
has closed interval [4*a-2, 4*b+2]. Items in consecutive bags therefore
intersect, even when they share only a boundary point. Each bag has at most
d colors. Search by sweeping bags, then independently replay in color order.
Only standard-library Python 3.10 or later is required.

Why the search covers arbitrary size: choose one low-depth point per
interval and list their distinct positions. An interval occurs in a run of
bags. Two originally intersecting intervals have runs that overlap or are
adjacent (otherwise a chosen point separates them). Take maximal runs of
each color to merge adjacent runs of that color. The resulting intervals
retain every lower-color witness. Pad each bag to d using the lowest absent
colors and merge runs again: every added color has local lower witnesses.
Thus full bags suffice for exact height h (use min(d,h) when necessary).
If more than h colors are attainable, keep only the lowest h.

At a cut, an interval ending earlier has met all its required colors. A
crossing interval records the lower colors it still needs. Two prefixes
at the same bag glue, after reflection, precisely when no required bit is
missing on both sides. A table closed under every transition, with no such
pair at a target bag, certifies impossibility for arbitrarily long layouts.

To iterate a gadget, place a full copy of the previous wall in a tiny
chamber at every selected attachment point, then present the gadget.
Every gadget interval sees every old color. If its palette has size h and
the largest selected point load is d, an iteration gains h colors with
at most d additional overlap. The test for a finite witness always uses
the expanded list, closed-endpoint overlap and the integer inequality FF>5*w.
"""

import argparse
import json
from bisect import bisect_right, insort
from fractions import Fraction
from functools import lru_cache
from heapq import heappop, heappush
from itertools import combinations
from math import comb, lcm
from time import process_time


def colors(mask):
    while mask:
        bit = mask & -mask
        yield bit
        mask ^= bit


def check_exclusion(depth, height, table, deadline):
    """Inductively check ALL full-bag transitions, including decreasing maxima."""
    palette = (1 << height) - 1
    bags = [sum(1 << c for c in group) for group in combinations(range(height), depth)]
    if table.get(0) != {0} or set(bags) - table.keys():
        return False
    for before, states in table.items():
        if process_time() >= deadline:
            return False
        if before & (1 << (height - 1)):
            if any(not (a & b) for a in states for b in states):
                raise RuntimeError("compatible prefixes at a target bag")
        for after in bags:
            blocked = retained = fresh = 0
            for c in range(height):
                bit = 1 << c
                shift = c * height
                if before & bit:
                    if after & bit:
                        retained |= (palette ^ after) << shift
                    else:
                        blocked |= (palette ^ after) << shift
                elif after & bit:
                    fresh |= ((bit - 1) & ~(before | after)) << shift
            candidates = table[after]
            for debt in states:
                if debt & blocked:
                    continue
                successor = (debt & retained) | fresh
                if successor not in candidates and not any(
                    successor & small == small for small in candidates
                ):
                    return False
    return True


def search(depth, height, deadline, state_limit=60000):
    """Return a bag sequence, or report exhaustion separately from a cutoff."""
    palette = (1 << height) - 1
    depth = min(depth, height)
    staged = comb(height, depth) > 3000
    # In a partial layout each active color owns a field of 'height' bits.
    # A set bit there denotes a lower color the interval still needs to meet.
    @lru_cache(maxsize=None)
    def field_mask(bag):
        return sum(palette << ((bit.bit_length() - 1) * height)
                   for bit in colors(bag))

    start = (0, 0)
    queue = [(0, 0, 0, 0)]
    minimal = {0: {0}}
    parent = {start: None}
    target = 1 << (height - 1)

    def prefix(state):
        path = []
        while state != start:
            path.append(state[0])
            state = parent[state]
        return path[::-1]

    while queue:
        if process_time() >= deadline or len(parent) >= state_limit:
            return "cutoff", None, len(parent)
        _, _, bag, debt = heappop(queue)
        state = (bag, debt)
        if debt not in minimal[bag]:
            continue
        kept = bag
        while True:
            departing = bag ^ kept
            required = 0
            for bit in colors(departing):
                required |= (debt >> ((bit.bit_length() - 1) * height)) & palette
            slots = depth - kept.bit_count() - required.bit_count()
            if slots >= 0:
                available = palette & ~(bag | required)
                if staged:
                    # Start large searches with the lowest bag and explore
                    # modest palette increases before hitting the state budget.
                    # This heuristic never certifies a negative answer.
                    available &= (1 << (bag.bit_length() + depth)) - 1
                for group in combinations(colors(available), slots):
                    added = required | sum(group)
                    following = kept | added
                    # This speeds discovery. The exclusion checker separately
                    # validates every transition without the ordering shortcut.
                    if following == bag or following.bit_length() < bag.bit_length():
                        continue
                    new_debt = debt & field_mask(kept)
                    for bit in colors(kept):
                        new_debt &= ~(added << ((bit.bit_length() - 1) * height))
                    for bit in colors(added):
                        missing = (bit - 1) & ~(bag | following)
                        new_debt |= missing << ((bit.bit_length() - 1) * height)
                    previous = minimal.setdefault(following, set())
                    # A prefix with fewer obligations can perform any suffix
                    # that a prefix with more obligations could perform.
                    if any(old & new_debt == old for old in previous):
                        continue
                    previous.difference_update(
                        [old for old in previous if old & new_debt == new_debt])
                    previous.add(new_debt)
                    new_state = (following, new_debt)
                    parent[new_state] = state
                    if len(parent) >= state_limit or (
                        len(parent) % 256 == 0 and process_time() >= deadline
                    ):
                        return "cutoff", None, len(parent)
                    # Reflect a second prefix at the same bag. Every interval
                    # crossing that cut must have all its debts paid on at
                    # least one side, bit by bit.
                    if following & target:
                        for other in previous:
                            if other & new_debt == 0:
                                backward = prefix((following, other))
                                return ("found", prefix(new_state) + backward[-2::-1],
                                        len(parent))
                    heappush(queue, (following.bit_length(), new_debt.bit_count(),
                                     following, new_debt))
            if not kept:
                break
            kept = (kept - 1) & bag
    if not check_exclusion(depth, height, minimal, deadline):
        return "inconclusive", None, len(parent)
    return "excluded", None, len(parent)


def intervals_from_bags(bags):
    starts = {}
    labeled = []
    previous = 0
    for at, bag in enumerate([*bags, 0]):
        for bit in colors(previous & ~bag):
            labeled.append((bit.bit_length(), 4 * starts.pop(bit) - 2, 4 * at - 2))
        for bit in colors(bag & ~previous):
            starts[bit] = at
        previous = bag
    return sorted(labeled)


def verify(intervals):
    events, by_color, assigned = [], [], []
    for left, right in intervals:
        if left > right:
            raise ValueError("reversed endpoints")
        events.extend(((left, 0), (right, 1)))  # Starts before ends at ties.
        for index, row in enumerate(by_color):
            # Each color class is disjoint. Of its intervals starting by
            # 'right', the last one has the largest right endpoint.
            at = bisect_right(row, right, key=lambda pair: pair[0])
            if at == 0 or row[at - 1][1] < left:
                break
        else:
            index = len(by_color)
            by_color.append([])
        insort(by_color[index], (left, right))
        assigned.append(index + 1)
    live = peak = 0
    for _, end in sorted(events):
        live += -1 if end else 1
        peak = max(peak, live)
    return peak, assigned


def replay(bags, height):
    labeled = intervals_from_bags(bags)
    intervals = [(lo, hi) for _, lo, hi in labeled]
    omega, assigned = verify(intervals)
    if assigned != [c for c, _, _ in labeled] or max(assigned) != height:
        raise RuntimeError("the independent First-Fit replay disagrees")
    # Keep one top interval and one witness of each lower color it needs,
    # recursively. Reuse witnesses already retained for other intervals.
    selected = {assigned.index(height)}
    for index in reversed(range(len(intervals))):
        if index not in selected:
            continue
        left, right = intervals[index]
        witnesses = {}
        for j in range(index):
            l, r = intervals[j]
            if assigned[j] < assigned[index] and l <= right and left <= r:
                if assigned[j] not in witnesses or j in selected:
                    witnesses[assigned[j]] = j
        selected.update(witnesses.values())
    ids = sorted(selected)
    intervals = [intervals[i] for i in ids]
    omega, trimmed_colors = verify(intervals)
    if trimmed_colors != [assigned[i] for i in ids]:
        raise RuntimeError("witness trimming changed a retained color")
    anchor_positions = [4 * i for i in range(len(bags))]
    loads = {p: sum(l <= p <= r for l, r in intervals) for p in anchor_positions}
    depth = max(min(n for p, n in loads.items() if l <= p <= r) for l, r in intervals)
    return intervals, omega, depth


def attachment_points(template, bag_count, depth):
    # Greedily hit every template interval at a permitted integer bag center.
    ports = [p for p in range(0, 4 * bag_count, 4)
             if sum(l <= p <= r for l, r in template) <= depth]
    chosen = []
    for left, right in sorted(template, key=lambda interval: interval[1]):
        if not chosen or chosen[-1] < left:
            chosen.append(ports[bisect_right(ports, right) - 1])
            if chosen[-1] < left:
                raise RuntimeError("missing attachment point")
    return chosen


def optimize_weights(template, ports):
    """Maximize color multiplicity per unit port load, with an exact LP dual."""
    _, assigned = verify(template)
    h = max(assigned)
    masks = sorted({sum(1 << (c-1) for (l, r), c in zip(template, assigned) if l <= p <= r)
                    for p in ports})
    m = len(masks)
    rows = []
    basis = list(range(h, h + m))
    for i, mask in enumerate(masks):
        rows.append(list(map(Fraction, [int(bool(mask & (1 << c))) for c in range(h)]
                             + [int(i == j) for j in range(m)] + [1])))
    objective = list(map(Fraction, [-1] * h + [0] * (m + 1)))
    while True:
        entering = next((j for j, x in enumerate(objective[:-1]) if x < 0), None)
        if entering is None:
            break
        leaving = min((i for i, row in enumerate(rows) if row[entering] > 0),
                      key=lambda i: (rows[i][-1] / rows[i][entering], basis[i]))
        pivot = rows[leaving][entering]
        pivot_row = [v / pivot for v in rows[leaving]]
        rows[leaving] = pivot_row
        for row in [objective, *(r for i, r in enumerate(rows) if i != leaving)]:
            coeff = row[entering]
            if coeff:
                row[:] = [a - coeff * b for a, b in zip(row, pivot_row)]
        basis[leaving] = entering
    x = [Fraction(0)] * h
    for i, j in enumerate(basis):
        if j < h:
            x[j] = rows[i][-1]
    y = objective[h:h+m]
    if (min(x + y) < 0 or sum(x) != sum(y) or
        any(sum(x[c] for c in range(h) if mask & (1 << c)) > 1 for mask in masks) or
        any(sum(y[i] for i, mask in enumerate(masks) if mask & (1 << c)) < 1
            for c in range(h))):
        raise RuntimeError("invalid primal or dual weight certificate")
    denominator = lcm(*(v.denominator for v in x))
    copies = [int(v * denominator) for v in x]
    if sum(copies[c-1] for c in assigned) > 30000:
        raise ValueError("weighted template exceeds the laptop limit of 30000 intervals")
    weighted = [interval for interval, c in zip(template, assigned) for _ in range(copies[c-1])]
    return weighted, sum(x), copies


def cover_bound(template):
    """Bound all reweightings even after zero-weight colors and their ports disappear."""
    _, assigned = verify(template)
    full = (1 << max(assigned)) - 1
    containers = set()
    for (l, r), owner in zip(template, assigned):
        mask = 0
        for (a, b), color in zip(template, assigned):
            if a <= l and r <= b:
                mask |= 1 << (color - 1)
        containers.add((1 << (owner - 1), mask))
    worst = 0
    for palette in range(1, full + 1):
        # At ANY port of a surviving owner, all these containers are present.
        masks = {mask & palette for owner, mask in containers if owner & palette}
        masks = [m for m in masks if not any(m != n and m & n == m for n in masks)]

        @lru_cache(maxsize=None)
        def cover(missing):
            if not missing:
                return 0
            first = missing & -missing
            return 1 + min(cover(missing & ~m) for m in masks if m & first)

        worst = max(worst, cover(palette))
        cover.cache_clear()
    return full, worst


def expand(template, chosen, levels):
    intervals = template
    for _ in range(1, levels):
        if len(chosen) * len(intervals) + len(template) > 30000:
            raise ValueError("expansion exceeds the laptop limit of 30000 intervals")
        offset = min(l for l, _ in intervals)
        scale = max(r for _, r in intervals) - offset + 1
        copies = [(p * scale + l - offset, p * scale + r - offset)
                  for p in chosen for l, r in intervals]
        intervals = copies + [(l * scale, r * scale) for l, r in template]
    return intervals


def small_bounds(deadline):
    # A(d) is maximum height at attachment depth d, F(k) at clique bound k.
    anchor_bounds = [0]
    for depth, height in enumerate((3, 7, 11), start=1):
        for target in (height, height + 1):
            status, bags, states = search(depth, target, deadline)
            print(f"d={depth} target={target} status={status} states={states}")
            if status in ("cutoff", "inconclusive"):
                print("Certificate incomplete within the run limits.")
                return
            if target == height:
                if status != "found" or replay(bags, target)[2] > depth:
                    raise RuntimeError("missing or invalid lower witness")
            elif status != "excluded":
                raise RuntimeError("unexpected larger gadget")
        anchor_bounds.append(height)
    # Take the highest A(b-1)+1 colors. Some interval I is covered everywhere
    # by >= b of these high intervals. Among the remaining colors at most
    # 2(k-b) occur at its endpoints. After deleting those color classes, the
    # lower intervals inside I give a supported wall of width at most k-b.
    upper = [0]
    for k in range(1, 14):
        upper.append(min(anchor_bounds[b-1] + 1 + 2*(k-b) + upper[k-b]
                         for b in range(1, min(k, len(anchor_bounds)) + 1)))
    print("widths 1..13, First-Fit upper bounds:", *upper[1:])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--depth", type=int, default=2)
    parser.add_argument("--height", type=int, default=0,
                        help="target color count (default: 5*depth+1)")
    parser.add_argument("--seconds", type=float, default=12.0,
                        help="total CPU budget for search and certificate checking")
    parser.add_argument("--levels", type=int, choices=(1, 2, 3), default=1,
                        help="recursion levels to generate from a found gadget")
    parser.add_argument("--bounds", action="store_true",
                        help="recheck the small-depth results and width recurrence")
    parser.add_argument("--weights", action="store_true",
                        help="optimize color multiplicities at the selected attachment points")
    parser.add_argument("--emit", action="store_true", help="print arrival order as JSON")
    args = parser.parse_args()
    if not 1 <= args.depth <= 5 or not 0 < args.seconds <= 15:
        parser.error("depth must be in 1..5 and seconds in (0, 15]")
    height = args.height or 5 * args.depth + 1
    if not 1 <= height <= 30:
        parser.error("height must be in 1..30")
    start = process_time()
    if args.bounds:
        small_bounds(start + args.seconds)
        print(f"cpu_seconds={process_time() - start:.3f}")
        return
    status, bags, states = search(args.depth, height, start + args.seconds)
    print(f"d={args.depth} target={height} status={status} states={states}")
    if status == "found":
        template, _, anchor_depth = replay(bags, height)
        if anchor_depth > args.depth:
            raise RuntimeError("attachment depth exceeds budget")
        ports = attachment_points(template, len(bags), anchor_depth)
        if args.weights:
            if height <= 12:
                count, bound = cover_bound(template)
                print(f"all-port reweighting upper bound={bound} palettes_checked={count}")
            try:
                template, optimal, copies = optimize_weights(template, ports)
            except ValueError as error:
                parser.error(str(error))
            height = sum(copies)
            anchor_depth = max(sum(l <= p <= r for l, r in template) for p in ports)
            if Fraction(height, anchor_depth) != optimal or max(verify(template)[1]) != height:
                raise RuntimeError("weighted gadget replay disagrees with its LP certificate")
            print(f"optimal gain per unit port load={optimal} multiplicities={copies}")
        try:
            intervals = expand(template, ports, args.levels)
        except ValueError as error:
            parser.error(str(error))
        omega, assigned = verify(intervals)
        if max(assigned) != height * args.levels:
            raise RuntimeError("expanded wall has incorrect First-Fit height")
        print(f"intervals={len(intervals)} omega={omega} FF={max(assigned)} "
              f"FF/omega={Fraction(max(assigned), omega)} "
              f"FF>5*omega={max(assigned) > 5*omega}")
        print(f"attachment_depth={anchor_depth} gain/depth={Fraction(height, anchor_depth)}")
        if args.emit:
            print(json.dumps(intervals))
    print(f"cpu_seconds={process_time() - start:.3f}")


if __name__ == "__main__":
    main()
