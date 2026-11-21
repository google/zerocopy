#!/usr/bin/env python3
"""Toy probe: debts computed from averaged annual employer-reported income versus
entitlement computed from actual fortnightly income, on synthetic income histories.

This is a stylised model of a single-person, no-dependants unemployment payment with a
two-band income test. It is NOT a reimplementation of any agency system and gives no
benefits advice. Parameters (maximum fortnightly rate, income free area, upper taper
threshold, taper rates) are passed in so that the cited values can be audited.

For each synthetic person over N fortnights:
  * benefit_fortnights: fortnights in which the payment was received;
  * actual_income[f]: income actually earned in fortnight f; reported_income[f] is what
    the person declared (equal to actual, except for a 30% subgroup in the synthetic cohort
    that declares zero earnings while on payment); the amount paid is the entitlement
    computed from the declared income;
  * the employer-reported total and period (start..end fortnight) are what an annual
    tax-record match would provide; the "averaged" method spreads the total evenly over
    the reported period and recomputes entitlement for each benefit fortnight in it.
Debt(method) = sum over benefit fortnights of max(0, paid - entitlement(method income)),
where "actual" uses actual fortnightly income (the correct debt under a fortnightly test).
A debt is "false" if the averaged debt is positive while the actual-income debt is zero,
and "overstated" if it exceeds the actual-income debt.
Usage: python3 averaging_probe.py <max_rate> <free_area> <upper_threshold> [<taper1> <taper2>]
"""
import json
import random
import sys


def entitlement(income, max_rate, free_area, upper, t1, t2):
    reduction = t1 * max(0.0, min(income, upper) - free_area) + t2 * max(0.0, income - upper)
    return max(0.0, max_rate - reduction)


def debts(person, p):
    n = person["n"]
    reported = person.get("reported", person["actual"])
    paid = {f: entitlement(reported[f], *p) for f in person["benefit"]}
    s, e = person["reported_period"]
    total = sum(person["actual"][f] for f in range(n) if person["employed"][f])
    avg = total / (e - s + 1)
    debt_avg = debt_act = 0.0
    for f in person["benefit"]:
        inc_avg = avg if s <= f <= e else person["actual"][f]
        debt_avg += max(0.0, paid[f] - entitlement(inc_avg, *p))
        debt_act += max(0.0, paid[f] - entitlement(person["actual"][f], *p))
    return round(debt_avg, 2), round(debt_act, 2)


def worked_example(p):
    """26 fortnights: works full-time fortnights 0-9 (not on payment) at $1,800/fortnight,
    then unemployed and on payment for fortnights 10-25 with no income. The employer's
    annual record reports $18,000 for the whole financial year (fortnights 0-25)."""
    n = 26
    actual = [1800.0 if f < 10 else 0.0 for f in range(n)]
    person = {"n": n, "actual": actual, "employed": [f < 10 for f in range(n)],
              "benefit": list(range(10, 26)), "reported_period": (0, 25)}
    return person, debts(person, p)


def synthetic_cohort(n_people=2000, seed=20261121):
    """Irregular earners: each person has 1-3 employment spells of random length and pay;
    while on payment, earnings are declared truthfully except by a 30% subgroup that declares
    zero (so some actual-income debts are genuinely positive). The employer-reported period is
    either the true spell span (50%) or the whole 26-fortnight year (50%), mimicking
    imprecise employment dates in annual records."""
    rng = random.Random(seed)
    cohort = []
    for _ in range(n_people):
        n = 26
        employed = [False] * n
        actual = [0.0] * n
        for _ in range(rng.randint(1, 3)):
            start = rng.randrange(n)
            length = rng.randint(1, 8)
            pay = rng.choice([300.0, 600.0, 1000.0, 1600.0, 2200.0])
            for f in range(start, min(n, start + length)):
                employed[f] = True
                actual[f] += round(pay * rng.uniform(0.6, 1.4), 2)
        # on payment when not employed full-time; part-time earners (<= $600) may stay on payment
        benefit = [f for f in range(n) if (not employed[f]) or actual[f] <= 600.0]
        if not benefit or not any(employed):
            continue
        emp_f = [f for f in range(n) if employed[f]]
        reported = (min(emp_f), max(emp_f)) if rng.random() < 0.5 else (0, n - 1)
        # 30% of people fail to report part-time earnings while on payment (report 0)
        under = rng.random() < 0.3
        reported_income = [0.0 if (under and f in benefit) else actual[f] for f in range(n)]
        cohort.append({"n": n, "actual": actual, "employed": employed, "benefit": benefit,
                       "reported_period": reported, "reported": reported_income})
    return cohort


def main(args):
    max_rate, free_area, upper = (float(x) for x in args[:3])
    t1, t2 = (float(args[3]), float(args[4])) if len(args) >= 5 else (0.5, 0.6)
    p = (max_rate, free_area, upper, t1, t2)
    person, (d_avg, d_act) = worked_example(p)
    cohort = synthetic_cohort()
    res = [debts(x, p) for x in cohort]
    with_avg_debt = [(a, b) for a, b in res if a > 0]
    false = [(a, b) for a, b in with_avg_debt if b == 0]
    over = [(a, b) for a, b in with_avg_debt if a > b + 0.005]
    under = [(a, b) for a, b in res if a + 0.005 < b]
    out = {
        "parameters": {"max_rate": max_rate, "free_area": free_area, "upper_threshold": upper,
                       "taper_1": t1, "taper_2": t2},
        "worked_example": {"averaged_fortnightly_income": round(18000 / 26, 2),
                           "debt_averaged": d_avg, "debt_actual": d_act,
                           "debt_averaged_plus_10pct_fee": round(d_avg * 1.10, 2)},
        "cohort": {
            "people": len(cohort),
            "with_averaged_debt": len(with_avg_debt),
            "false_debts_actual_zero": len(false),
            "overstated_debts": len(over),
            "understated_vs_actual": len(under),
            "sum_averaged_debt": round(sum(a for a, _ in res), 2),
            "sum_actual_debt": round(sum(b for _, b in res), 2),
        },
    }
    print(json.dumps(out, indent=1))


if __name__ == "__main__":
    main(sys.argv[1:])
