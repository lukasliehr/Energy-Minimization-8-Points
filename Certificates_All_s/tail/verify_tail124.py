"""Exact scalar driver for global uniqueness on every real s>=124.

Quartic SOS packing separation, absorbed-cubic variance,
and a concave scalar outer-annulus comparison. Retains the accepted packing
classification proof, weighted two-value lemma, candidate stationarity argument,
and whole-convex-set full-energy Hessian argument. All computational inputs
are verified directly in this package; no historical acceptance records.
"""

from pathlib import Path
import sys, json, hashlib, time

sys.dont_write_bytecode = True
from exact_geometry import I, F, sqrt, exp, log, ser, HELPER

if not __debug__:
    raise SystemExit("Run without -O")
t0 = time.time()
HERE = Path(__file__).parent
checks = {}
values = {}
deps = {}


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def ck(name, test):
    assert name not in checks
    checks[name] = bool(test)
    if not test:
        raise AssertionError(name)


rt = sqrt(2)
a = (2 * rt - 1) / 7
tau = 2 * (1 - a)
kap = 1 + 1 / rt
W = 8 * (kap + 1)
degree = W / 4
p0 = F(62)
rho = F(3, 10)
gap = F(289, 10000)
higher = F(11, 50)
gamma = F(3, 2)
eta = F(1, 5)
mu = F(59546, 15625)
mu0 = F(37, 10)
quartic = F(132, 25)
residual = F(1, 10**7)
sigma = 2 + higher * sqrt(degree)
sigma_higher = higher * sqrt(degree)
C = F(9669627, 625000)
d = log(kap) / (kap + 1)
lam = exp(-kap * d)
Cmin = lam * W
D = (kap * d) ** 2 / 2
N = d / sqrt(2 * a * (1 - a))
Z = sqrt(8 * kap * d * d + 8 * kap * kap * d * d)

# Bind the complete newly checked certificates, including their source and witnesses.
new_paths = [HERE / "verify_variance.json", HERE / "sos_gap.witness.verified.json"]
new_records = []
for path in new_paths:
    rec = json.loads(path.read_text())
    new_records.append(rec)
    deps[str(path)] = sha(path)
    for name, h in rec["source_sha256"].items():
        src = HELPER if name == HELPER.name else HERE / name
        ck("new_source_" + path.name + "_" + name, sha(src) == h)
        deps[str(src)] = h
    wp = HERE / (
        "variance_witness.json"
        if path.name == "verify_variance.json"
        else "sos_gap.witness.json"
    )
    ck("new_witness_" + path.name, sha(wp) == rec["witness_sha256"])
    deps[str(wp)] = rec["witness_sha256"]
vr, gr = new_records
ck("variance_report_status", vr["status"] == "PASS_VARIANCE_SUBLEMMA_ONLY")
ck("packing_report_status", gr["status"] == "PASS_GLOBAL_PACKING_GAP_SUBLEMMA_ONLY")
ck(
    "variance_constants",
    F(vr["constants"]["mu0"]) == mu0
    and F(vr["constants"]["quartic_penalty"]) == quartic
    and F(vr["constants"]["cubic_residual_allowance"]) == residual
    and F(vr["constants"]["radius"]) == rho
    and F(vr["constants"]["higher_remainder"]) == higher,
)
ck(
    "packing_constants",
    F(gr["constants"]["gap"]) == gap
    and F(gr["constants"]["orbit_radius"]) == rho
    and F(gr["constants"]["higher_remainder"]) == higher,
)
ck("weighted_spectrum_constant", F(vr["constants"]["weighted_spectral_lower"]) == mu)
ck("unweighted_spectrum_constant", F(vr["constants"]["unweighted_spectral_lower"]) == 3)
ck(
    "centered_quadratic_constant",
    F(vr["constants"]["centered_quadratic_norm_bound"]) == 2,
)

# Direct computational prerequisites: whole-ball mean and packing enumeration.
mean_path = HERE / "verify_wholeball_mean.json"
mr = json.loads(mean_path.read_text())
ck("wholemean_status", mr["status"] == "PASS_WHOLE_BALL_MEAN_SUBLEMMA_ONLY")
ck(
    "wholemean_all_checks",
    len(mr["checks"]) == mr["number_of_checks"]
    and all(v is True for v in mr["checks"].values()),
)
ck(
    "wholemean_source_binding",
    sha(HERE / "verify_wholeball_mean.py") == mr["source_sha256"],
)
deps[str(mean_path)] = sha(mean_path)
deps[str(HERE / "verify_wholeball_mean.py")] = mr["source_sha256"]
for name, h in mr["dependencies_sha256"].items():
    ck("wholemean_helper_" + name, sha(HERE / name) == h)
    deps[str(HERE / name)] = h
ck(
    "wholemean_constants",
    mr["constants"]
    == {
        "lambda0": "413/100",
        "tensor_norm_squared": "3",
        "B_norm_upper": "4",
        "D_eigen_upper": "231/100",
    },
)
ck("wholemean_radius", F(mr["values"]["full_chart"]["radius"]) == rho)
packing_path = HERE / "verify_packing.json"
pr = json.loads(packing_path.read_text())
ck("packing_enumeration_status", pr["status"] == "PASS_PACKING_ENUMERATION")
ck(
    "packing_enumeration_complete",
    pr["all_surviving_graphs_have_verified_spanning_cubes"] is True
    and [r["k"] for r in pr["runs"]] == [6, 4, 2],
)
ck(
    "packing_no_isomorphism_pruning",
    pr["canonical_pruning"] is False
    and all(r["deduplicate"] is False for r in pr["runs"]),
)
ck(
    "packing_topology_predicates",
    pr["topology_pruning"] is True
    and pr["adjacent_degree_four_angle_pruning"] is False,
)
deps[str(packing_path)] = sha(packing_path)
for name, h in pr["source_sha256"].items():
    ck("packing_source_" + name, sha(HERE / name) == h)
    deps[str(HERE / name)] = h

# Uniform valid trial ceiling and elementary force entry.
ck("p0_positive", p0 > 0)
ck("packing_distance_bound", tau.hi < F(3, 2))
ck("trial_height", a.lo > 0 and d.lo > 0 and (a + tau * d / (2 * p0)).hi < F(1, 3))
ck("trial_log_remainder", (d * d / (2 * (1 - d / p0))).hi < D.lo)
ck("trial_noncontact_multiplier", exp(d + D / p0).hi < 2)
ck("trial_noncontact_tail", 16 * F(1, 2) ** 62 < F(1, 10**6))
trial = Cmin * exp(D / p0) + F(1, 10**6)
ck("trial_ceiling", trial.hi < C)
m0 = tau - gap
entry = (6 - m0) * exp(p0 * log(tau / m0))
ck("force_entry_distance_positive", m0.lo > 0 and (tau / m0).lo > 1)
ck("force_entry_energy", entry.lo > C)
ck("classification_alternative_gap", gap < (2 * (F(3, 10) - a)).lo)
# For m<=m0, (6-m)(tau/m)^p is strictly decreasing in m; at fixedm0 it
# increases in p. The positive accepted force correction is discarded.
values.update(trial=ser(trial), entry_lower=ser(entry), closest_distance_cutoff=ser(m0))

# Candidate stationarity is proved analytically; the same force entry applies.

# Directly verified whole-ball mean bound, independent of localization.
mean_actual = (
    F(413, 100)
    + F(3, 4) * rho * rho
    + (4 * rho + F(231, 100)) * rho * rho / (1 + sqrt(1 - rho * rho)) ** 2
) / W
ck("whole_chart_signed_mean", mean_actual.hi < eta)
abs_remainder = 1 + (2 * a + sqrt(2 * (1 - a * a)) * rho) / (1 + sqrt(1 - rho * rho))
ck("absolute_contact_remainder", abs_remainder.hi < gamma)

# New outer annulus: r in [L/p,rho], for every real p>=p0.
L = F(6)
aa = 1 / sqrt(W * (W - 1))


def radicand(r):
    return mu0 - residual * r - quartic * r * r


def Froot(r):
    return r * sqrt(radicand(r)) - sigma_higher * r * r


def H(r):
    return aa * Froot(r) - eta * r * r


ck("outer_radicand_positive", radicand(rho) > 0)
ck("outer_annulus_nonempty", L / p0 < rho)
ck("outer_F_over_r_positive", Froot(rho).lo > 0)
vfloor = L * Froot(rho) / (rho * tau) - Z
ck("outer_variance_above_sqrtW", vfloor.lo > sqrt(W).hi)
ck("outer_H_rho_positive", H(rho).lo > 0)
outer_records = []
for label, r in [("inner_endpoint", L / p0), ("outer_endpoint", rho)]:
    lower = lam * (W - 1) * exp(-aa * Z + p0 * H(r) / tau)
    ck("outer_comparison_" + label, lower.lo > C)
    outer_records.append({"endpoint": label, "radius": str(r), "lower": ser(lower)})
# F(r)/r decreases. H''(r)<0 because h=mu0-eps*r-k*r² has h'<0,h''<0,
# and (r*sqrt(h))''=h'/sqrt(h)+r*h''/(2sqrt(h))-r*h'^2/(4h^(3/2))<0.
# Thus min H on [L/p,rho] is at an endpoint. pH(rho) increases; also
# pH(L/p)=aa*L*sqrt(mu0-eps*L/p-k*L²/p²)-(aa*sigma_higher+eta)*L²/p
# increases. Both comparisons consequently hold on the whole half-line.
# For v>=sqrtW, d/dz log[(W-z)e^(v sqrt(z/(W(W-z))))]>=0 on[1,W-1],
# because its exact condition v>=2sqrt(z(W-z)/W) follows from4z(W-z)<=W².
values.update(
    whole_chart_mean=ser(mean_actual),
    outer_variance_floor=ser(vfloor),
    outer_comparisons=outer_records,
)

# Four accepted weighted mean/variance contractions fromr<6/p tor<3/(4p).
ck("old_variance_radius_increasing", (sqrt(mu) - 2 * sigma * rho).lo > 0)
seq = [F(6), F(27, 10), F(13, 10), F(43, 50), F(3, 4)]
ck("annulus_chain", seq[0] == L and all(k > l for k, l in zip(seq, seq[1:])))
steps = []
for old, new in zip(seq, seq[1:]):
    upper = I(C) * exp(eta * old * old / (tau * p0))
    vroot = sqrt(mu) * (I(new) / tau - N) - sigma * new * new / (tau * p0)
    ck("positive_variance_" + str(new), vroot.lo > 0)
    records = []
    for i in range(9):
        for j in range(9):
            if (i, j) in [(0, 0), (8, 8)]:
                continue
            z = i * kap + j
            other = W - z
            pos = sqrt(vroot * vroot * other / (W * z))
            neg = sqrt(vroot * vroot * z / (W * other))
            lower = lam * (z * exp(-pos) + other * exp(neg))
            ck(
                "annulus_" + str(old) + "_" + str(new) + "_" + str(i) + "_" + str(j),
                lower.lo > upper.hi,
            )
            records.append({"mass": [i, j], "lower": ser(lower)})
    ck("all_79_masses_" + str(new), len(records) == 79)
    steps.append(
        {
            "old": str(old),
            "new": str(new),
            "upper": ser(upper),
            "vroot": ser(vroot),
            "comparisons": records,
        }
    )
    print("PASS annulus", old, "->", new, flush=True)

# Recompute every retained full-Hessian condition at the new endpoint.
K = F(3, 4)
rf = K / p0
epsilon = gamma * K * K / (tau * p0)
Cstar = I(C) * exp(epsilon)
for kind, weight, z0 in [("square", kap, -d), ("cross", I(1), kap * d)]:
    u = F(11, 10) - z0
    ck(kind + "_positive_test_argument", u.lo > 0)
    lower = lam * (weight * exp(-u) + (W - weight) * exp(weight * u / (W - weight)))
    ck(kind + "_linear_exponent_below_eleven_tenths", lower.lo > Cstar.hi)
hesspower = exp((F(11, 10) + epsilon) * (1 + F(2, p0)))
ck("all_contact_Hessian_weights_above_three_tenths", hesspower.hi < F(10, 3))
ck("contact_lower_exponent_bound", (log(I(C)) + 2 * epsilon).hi < 3)
ck("contact_upper_exponent_bound", (F(11, 10) + epsilon).hi < 3)
logerr = epsilon + F(9, 2 * p0) / (1 - F(3, p0))
log_bound = F(1, 11)
ck("contact_energy_log_error", logerr.hi < log_bound)
ck("noncontact_distance_ratio", (4 * K / (tau * p0)).hi < F(1, 2))
ck("noncontact_incident_weight", 3 * F(2, 3) ** 30 < F(1, 1000) and p0 + 1 >= 30)
Bincident = F(5)
ck("incident_quartic_monotonicity", Cstar.hi / 4 < Bincident < Cstar.lo)
left = Bincident * (Cstar - Bincident) ** 3
right = F(27, 256) * Cmin**4
ck("incident_exponential_energy_below_five", left.hi < right.lo)
incident = exp(log_bound) * Bincident / (1 - F(3, p0)) + F(1, 1000)
ck("actual_incident_weight_below_six", incident.hi < 6)
ck("chart_displacement_factor", (2 / (1 + sqrt(1 - rf * rf))).hi < F(101, 100) ** 2)
upper_hess = 2 / (1 - rf * rf) + 2 * (a + F(101, 100) * rf) / (
    (1 - rf * rf) * sqrt(1 - rf * rf)
)
ck("pair_upper_Hessian_below_eight_thirds", upper_hess.hi < F(8, 3))
ck("contact_derivative_positive", (sqrt(3) - 12 * rf).lo > 0)
deriv = (sqrt(3) - 12 * rf) ** 2
ck("contact_derivative_square_above_five_halves", deriv.lo > F(5, 2))
margin = F(3, 4) * (p0 + 1) - 16 * tau
ck("full_Hessian_positive", margin.lo > 0)
values.update(
    epsilon=ser(epsilon),
    Cstar=ser(Cstar),
    contact_log_error=ser(logerr),
    incident_weight=ser(incident),
    contact_derivative_lower=ser(deriv),
    pair_upper_Hessian=ser(upper_hess),
    Hessian_bracket_margin=ser(margin),
)
if (any(Path(path).resolve().parent != HERE.resolve() for path in deps)
        or len({Path(path).name for path in deps}) != len(deps)):
    raise ValueError("Tail dependencies must have distinct names in the replay directory")
for path, h in deps.items():
    ck("final_dependency_" + Path(path).name, sha(Path(path)) == h)
out = {
    "status": "PASS_STANDALONE_GLOBAL_TAIL_124",
    "acceptance": "FRESH_COMPUTATIONAL_CHECKS_PASSED",
    "global_s_cutoff": 124,
    "global_p_cutoff": str(p0),
    "scope": "Global uniqueness up to O(3) and relabeling; also uniqueness of local minima below the stated energy ceiling.",
    "number_of_checks": len(checks),
    "checks": checks,
    "values": values,
    "bootstrap": steps,
    "constants": {
        "C": str(C),
        "rho": str(rho),
        "gap": str(gap),
        "eta": str(eta),
        "final_log_error_bound": str(log_bound),
    },
    "dependency_sha256": {Path(name).name: h for name, h in deps.items()},
    "source_sha256": sha(Path(__file__)),
    "runtime_seconds_diagnostic": time.time() - t0,
}
Path(__file__).with_suffix(".json").write_text(json.dumps(out, indent=2) + "\n")
print(out["status"], len(checks), "checks", "seconds", time.time() - t0, flush=True)
