from z3 import *
import random
import numpy as np
from fractions import Fraction
from scipy.optimize import linprog

# multiplies two 2D arrays as matrices
def mult(A, B):
    m = len(A)
    n = len(A[0])
    if len(B) != n:
        return None
    p = len(B[0])

    C = [[None for _ in range(p)] for _ in range(m)]

    for i in range(m):
        for j in range(p):
            C[i][j] = Sum([A[i][k] * B[k][j] for k in range(n)])

    return C


# A <= B
# creates inequalities that represent that matrix A <= then matrix B
# (compares each position)
def cmpr_mtrx(A, B):
    m = len(A)
    n = len(A[0])
    if (len(A) != len(B)):
        return None
    for i in range(len(A)):
        if len(A[i]) != len(B[0]):
            return None
        if len(B[i]) != len(A[0]):
            return None

    constrs = (1 == 1)
    for i in range(m):
        for j in range(n):
            constrs = And(constrs, A[i][j] <= B[i][j])
    return constrs


#v2 on beam of v1
#v2 == v1 * k, k >= 0
def on_beam(v1, v2):
    return Or(
        And(
            v1[0] * v2[1] == v1[1] * v2[0],
            v1[0] * v2[0] >= 0,
            v1[1] * v2[1] >= 0,
            Or(                
                v1[0] != 0,
                v1[1] != 0
            )
        ),
        And(
            v1[0] == 0,
            v1[1] == 0,
            v2[0] == 0,
            v2[1] == 0
        )
    )


#creates constarins so given vector x belongs to the cone
#defined by vectors s and t
def belongs_to_C(s, t, x):
    return And(
        Implies(
            s[0] * t[1] - s[1] * t[0] > 0,
            And(
                x[0] * t[1] - x[1] * t[0] >= 0,
                s[0] * x[1] - s[1] * x[0] >= 0
            )
        ),
        Implies(
            s[0] * t[1] - s[1] * t[0] == 0,
            Or(
                on_beam(s, x),
                on_beam(t, x)
            )
        )
    )


def format_model(model, is_180=False):
    """Formats a Z3 model into a human-readable string representation, including the

    accumulated witness orbit sequence (v, w, w+M(w-v), ...).

    Supports both regular witness checks and 180-degree half-plane checks
    (is_180=True).
    """
    if model is None or isinstance(model, str) or str(model) == "unsat":
        return str(model)

    # 1. Helper function to fetch raw Z3 string representation
    def get_val_str(var_name):
        for decl in model.decls():
            if decl.name() == var_name:
                return str(model[decl])
        return "0"

    # 2. Helper function to parse Z3 numeric values safely into floats
    def parse_num(num_str):
        try:
            return float(Fraction(num_str))
        except (ValueError, ZeroDivisionError):
            return 0.0

    # Extract Matrix M string values
    m00_s, m01_s = get_val_str("M(0, 0)"), get_val_str("M(0, 1)")
    m10_s, m11_s = get_val_str("M(1, 0)"), get_val_str("M(1, 1)")

    # Extract Vector s & Starting Points v, w
    s0_s, s1_s = get_val_str("s0"), get_val_str("s1")
    v0_s, v1_s = get_val_str("v0"), get_val_str("v1")
    w0_s, w1_s = get_val_str("w0"), get_val_str("w1")

    # Handle Vector display section depending on mode
    if is_180:
        s0, s1 = parse_num(s0_s), parse_num(s1_s)
        u0, u1 = -s1, s0
        t0, t1 = -s0, -s1

        vectors_block = f"""Vectors (180° Half-Plane):
  s = ({s0_s}, {s1_s})
  u = ({u0:.4g}, {u1:.4g}) [perpendicular]
  t = ({t0:.4g}, {t1:.4g}) [opposite]"""
    else:
        t0_s, t1_s = get_val_str("t0"), get_val_str("t1")
        vectors_block = f"""Vectors:
  s = ({s0_s}, {s1_s})
  t = ({t0_s}, {t1_s})"""

    # 3. Parse numbers for orbit computation
    M = np.array(
        [
            [parse_num(m00_s), parse_num(m01_s)],
            [parse_num(m10_s), parse_num(m11_s)],
        ]
    )

    v = np.array([parse_num(v0_s), parse_num(v1_s)])
    w = np.array([parse_num(w0_s), parse_num(w1_s)])

    # 4. Compute Accumulated Orbit Sequence
    diff = w - v
    current_term = diff.copy()
    current_sum = w.copy()

    orbit = [v, w]

    for _ in range(3):  # Calculates x_2, x_3, x_4
        current_term = M @ current_term
        current_sum = current_sum + current_term
        orbit.append(current_sum.copy())

    # Format orbit output
    labels = [
        "v",
        "w",
        "w + M(w-v)",
        "w + M(w-v) + M²(w-v)",
        "w + M(w-v) + M²(w-v) + M³(w-v)",
    ]
    orbit_str = "\n".join(
        [
            f"  x_{i} ({labels[i]}): ({vec[0]:.4g}, {vec[1]:.4g})"
            for i, vec in enumerate(orbit)
        ]
    )

    # 5. Construct Final Output String
    formatted_output = f"""
Matrix M:
  [ {m00_s:>5}, {m01_s:>5} ]
  [ {m10_s:>5}, {m11_s:>5} ]

{vectors_block}

Starting Points:
  v = ({v0_s}, {v1_s})
  w = ({w0_s}, {w1_s})

Witness Orbit:
{orbit_str}
""".strip()

    return formatted_output

def format_model_180(model):
    """Formats a Z3 model for the 180-degree half-plane witness (calculates u and t from s)."""
    if model is None or isinstance(model, str) or model == unsat:
        return str(model)

    def get_val(var_name):
        for decl in model.decls():
            if decl.name() == var_name:
                # Handle fraction strings from Z3 like '1/2' or standard numbers
                val_str = str(model[decl])
                try:
                    return float(RealVal(val_str).as_fraction()) if '/' in val_str else float(val_str)
                except Exception:
                    return val_str
        return 0.0

    m00, m01 = get_val("M(0, 0)"), get_val("M(0, 1)")
    m10, m11 = get_val("M(1, 0)"), get_val("M(1, 1)")

    # Extract base vector s
    s0, s1 = get_val("s0"), get_val("s1")
    
    # Calculate derived perpendicular u and opposite t
    u0, u1 = -s1, s0
    t0, t1 = -s0, -s1

    v0, v1 = get_val("v0"), get_val("v1")
    w0, w1 = get_val("w0"), get_val("w1")

    formatted_output = f"""
Matrix M:
  [ {m00:>5}, {m01:>5} ]
  [ {m10:>5}, {m11:>5} ]

Vectors (180° Half-Plane):
  s = ({s0}, {s1})
  u = ({u0}, {u1}) [perpendicular]
  t = ({t0}, {t1}) [opposite]

Starting Points:
  v = ({v0}, {v1})
  w = ({w0}, {w1})
""".strip()

    return formatted_output


def is_not_empty(A_list, b_list):
    A = np.array(A_list)
    b = np.array(b_list)
    m, n = A.shape

    A_ub = -A
    b_ub = -b

    # Feasibility LP: minimize zero objective over unconstrained x \in R^n
    c_zero = np.zeros(n)
    res = linprog(
        c_zero,
        A_ub=A_ub,
        b_ub=b_ub,
        bounds=(None, None),  # Allows negative coordinates
        method="highs"
    )

    return res.success

def is_bounded(A_list, b_list):
    A = np.array(A_list)
    b = np.array(b_list)
    m, n = A.shape

    A_ub = -A
    b_ub = -b

    # Explicitly set variables to be unbounded (-inf, +inf) unless constrained by A
    unbounded_bounds = (None, None)

    # 1. Check feasibility (non-emptiness)
    c_zero = np.zeros(n)
    res_init = linprog(c_zero, A_ub=A_ub, b_ub=b_ub, bounds=unbounded_bounds, method="highs")

    if not res_init.success:
        return False  # Infeasible / Empty set

    # 2. Check upper and lower bounds for every coordinate variable x_i
    for i in range(n):
        # Upper bound: Maximize x_i (Minimize -x_i)
        c_max = np.zeros(n)
        c_max[i] = -1.0
        res_max = linprog(c_max, A_ub=A_ub, b_ub=b_ub, bounds=unbounded_bounds, method="highs")

        if res_max.status == 3:  # HiGHS status 3 = Unbounded
            return False

        # Lower bound: Minimize x_i
        c_min = np.zeros(n)
        c_min[i] = 1.0
        res_min = linprog(c_min, A_ub=A_ub, b_ub=b_ub, bounds=unbounded_bounds, method="highs")

        if res_min.status == 3:  # Unbounded
            return False

    return True


#tries to find witnesses for given matrices (Ax >= b)
#returns a dictionary of for ettempts to find witness with cone of form
#or a point, ray, line and any two vectors
#returns unsat for no solution and a solution for a soluton
def find_witnesses(A, b):
    if (len(A) != len(b)):
        return None
    for i in range(len(A)):
        if len(A[i]) != 4:
            return None

    results = {}

    not_empty = is_not_empty(A, b)
    results["not_empty"] = not_empty
    if not not_empty:
        return results

    bounded = is_bounded(A, b)
    results["bounded"] = bounded
        
    if bounded:
        return results

    b_t = [[b[i]] for i in range(len(b))]

    M = [
        [Real("M(0, 0)"), Real("M(0, 1)")],
        [Real("M(1, 0)"), Real("M(1, 1)")]
    ]
    s = [Real("s0"), Real("s1")]
    t = [Real("t0"), Real("t1")]
    v = [Real("v0"), Real("v1")]
    w = [Real("w0"), Real("w1")]

    t_180 = [s[0] * -1, s[1] * -1]
    u_180 = [s[1] * -1, s[0]]

    Ms = mult(M, [[s[0]], [s[1]]])
    Ms = [Ms[0][0], Ms[1][0]]
    Mt = mult(M, [[t[0]], [t[1]]])
    Mt = [Mt[0][0], Mt[1][0]]

    Mt_180 = mult(M, [[t_180[0]], [t_180[1]]])
    Mt_180 = [Mt_180[0][0], Mt_180[1][0]]
    Mu_180 = mult(M, [[u_180[0]], [u_180[1]]])
    Mu_180 = [Mu_180[0][0], Mu_180[1][0]]

    #MC belongs to C
    wt1 = And(
        belongs_to_C(s, t, Ms),
        belongs_to_C(s, t, Mt)
    )

    wt1_180 = And(
        Or(
            belongs_to_C(s, u_180, Ms),
            belongs_to_C(u_180, t_180, Ms)
        ),
        Or(
            belongs_to_C(s, u_180, Mu_180),
            belongs_to_C(u_180, t_180, Mu_180)
        ),
        Or(
            belongs_to_C(s, u_180, Mt_180),
            belongs_to_C(u_180, t_180, Mt_180)
        )
    )

    zero_m = [[0] for i in range(len(A))]

    #ForAll x belonging to C, (x, Mx) belongs to rec(K)
    wt2 = And(
        cmpr_mtrx(zero_m, mult(A, [[s[0]], [s[1]], [Ms[0]], [Ms[1]]])),
        cmpr_mtrx(zero_m, mult(A, [[t[0]], [t[1]], [Mt[0]], [Mt[1]]]))
    )

    wt2_180 = And(
        cmpr_mtrx(zero_m, mult(A, [[s[0]], [s[1]], [Ms[0]], [Ms[1]]])),
        cmpr_mtrx(zero_m, mult(A, [[t_180[0]], [t_180[1]], [Mt_180[0]], [Mt_180[1]]])),
        cmpr_mtrx(zero_m, mult(A, [[u_180[0]], [u_180[1]], [Mu_180[0]], [Mu_180[1]]]))
    )

    #(v, w) belongs to K
    wt3 = cmpr_mtrx(b_t, mult(A, [[v[0]], [v[1]], [w[0]], [w[1]]]))

    #(w - v) belongs to C
    wt4 = belongs_to_C(s, t, [w[0] - v[0], w[1] - v[1]])

    wt4_180 = Or(
        belongs_to_C(s, u_180, [w[0] - v[0], w[1] - v[1]]),
        belongs_to_C(u_180, t_180, [w[0] - v[0], w[1] - v[1]])
    )

    C_constr = (s[0] * t[1] - s[1] * t[0] >= 0)

    witness = And(wt1, wt2, wt3, wt4, C_constr)

    witness_180 = And(wt1_180, wt2_180, wt3, wt4_180, Or(s[0] != 0, s[1] != 0))

    s_p = Solver()
    s_p.add(And(witness, s[0] == 0, s[1] == 0, t[0] == 0, t[1] == 0))
    s_r = Solver()
    s_r.add(And(witness, s[0] == t[0], s[1] == t[1], Not(And(s[0] == 0, s[1] == 0, t[0] == 0, t[1] == 0))))
    s_l = Solver()
    s_l.add(And(witness, s[0] == t[0] * -1, s[1] == t[1] * -1, Not(And(s[0] == 0, s[1] == 0, t[0] == 0, t[1] == 0))))
    s_cone = Solver()
    s_cone.add(witness, Not(And(s[0] == t[0], s[1] == t[1])), Not(And(s[0] == t[0] * -1, s[1] == t[1] * -1)), Not(And(s[0] == 0, s[1] == 0)), Not(And(t[0] == 0, t[1] == 0)))
    s_180 = Solver()
    s_180.add(witness_180)

    res = {
        "point": s_p.check(),
        "ray": s_r.check(),
        "line": s_l.check(),
        "cone": s_cone.check(),
        "half_plane": s_180.check(),
        "bounded": bounded,
        "not_empty": not_empty
    }

    if res["point"] == sat:
        res["point"] = format_model(s_p.model())
    if res["ray"] == sat:
        res["ray"] = format_model(s_r.model())
    if res["line"] == sat:
        res["line"] = format_model(s_l.model())
    if res["cone"] == sat:
        res["cone"] = format_model(s_cone.model())
    if res["half_plane"] == sat:
        res["half_plane"] = format_model(s_180.model(), is_180=True)

    return res