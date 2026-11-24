from ngsolve import *
from xfem import *
from math import pi
from ngsolve.solvers import *
from ngsolve.meshes import *
from xfem.lset_spacetime import *
from time import perf_counter, process_time
from mkl_pardiso import PardisoMetis

# Unfitted space-time method on moving domains, DG in time.
#  space="DG": DG in space (upwind + symmetric interior penalty), GP on cut facets only (the DGDG method of the paper)
#  space="CG": H1 in space, GP on cut facets (as in st_paper_comp)
#  space="CGall": H1 in space, GP on all active facets (as in st_transport, CIP-type stabilisation for alpha -> 0)

def GetProblem(geom, t, alpha, space_refs):
    prob = {}
    if geom == 'kite':
        from netgen.geom2d import SplineGeometry
        geometry = SplineGeometry()
        geometry.AddRectangle([-1.05,-1.05],[1.55,1.05])
        prob["geometry"] = geometry
        prob["maxh"] = 0.9
        prob["D"] = 2
        prob["tend"] = 0.5
        r0 = 1
        rho = (1 - y**2)*t
        w = CoefficientFunction((rho.Diff(t),0))
        prob["wmax"] = 1
        r = sqrt((x- rho)**2+y**2)
        prob["levelset"] = r - r0
        u_exact = cos(pi/r0*r) * sin(pi*t)
    elif geom.startswith('kite_ring'):
        # kite geometry with a steep ring-shaped layer of width delta, u = g(r). As r is transported with w,
        # this is an exact solution for alpha = 0 and f = 0; g'(r0) ~ 0, so the Neumann condition holds
        # (up to machine precision). geom = 'kite_ring<delta>', e.g. kite_ring0.02
        delta = float(geom[len('kite_ring'):] or 0.02)
        from netgen.geom2d import SplineGeometry
        geometry = SplineGeometry()
        geometry.AddRectangle([-1.05,-1.05],[1.55,1.05])
        prob["geometry"] = geometry
        prob["maxh"] = 0.9
        prob["D"] = 2
        prob["tend"] = 0.5
        r0 = 1
        rho = (1 - y**2)*t
        w = CoefficientFunction((rho.Diff(t),0))
        prob["wmax"] = 1
        r = sqrt((x- rho)**2+y**2)
        prob["levelset"] = r - r0
        u_exact = 1 / (1 + exp(2 * (r - 0.5) / delta))  # = (1 - tanh((r-0.5)/delta)) / 2
        prob["range"] = (0., 1.)
        # region away from the layer, to measure how far (spurious) oscillations spread
        prob["far"] = IfPos((r - 0.5)**2 - 0.2**2, 1., 0.)
    elif geom == 'moving_sphere':
        from netgen.csg import OrthoBrick, Pnt, CSGeometry
        geometry = CSGeometry()
        geometry.Add (OrthoBrick(Pnt(-0.6,-1,-0.6), Pnt(0.6,1,0.6)))
        prob["geometry"] = geometry
        prob["maxh"] = 0.5
        prob["D"] = 3
        prob["tend"] = 0.5
        R = 0.5
        rho = (1 / (pi)) * sin(2 * pi * t)
        w = CoefficientFunction((0, rho.Diff(t), 0))
        prob["wmax"] = 2
        r = sqrt(x**2 + (y - rho)**2 + z**2)
        prob["levelset"] = r - R
        u_exact = cos(pi * r / R) * sin(pi * t)
    else:
        raise Exception("unknown geometry " + geom)

    D = prob["D"]
    coords = [x, y, z][:D]
    lapl = sum(u_exact.Diff(c).Diff(c) for c in coords)
    conv = sum(w[i] * u_exact.Diff(coords[i]) for i in range(D))
    # div(w) = 0 for all examples
    prob["f"] = (u_exact.Diff(t) - alpha * lapl + conv).Compile()
    prob["w"] = w
    prob["u_exact"] = u_exact
    prob["grad_u_exact"] = CF(tuple(u_exact.Diff(c) for c in coords))
    prob["dt_u_exact"] = u_exact.Diff(t)
    return prob


def Solve(i_t=2, i_s=2, k_t=3, k_s=3, space="DG", geom='kite', alpha=1., gamma=0.05, lam=10.,
          n_threads=6, solver="pardiso", curved=True, nsteps_fac=4, verbose=True, linefile=None, max_slabs=None):

    SetNumThreads(n_threads)
    n_steps = nsteps_fac * 2**i_t
    k_lset = k_s if curved else 1
    time_order = 2 * max(k_t, k_lset) + 2
    tstart = 0
    told = Parameter(tstart)
    # placeholder for delta_t to build the problem (tend known only afterwards)
    dtpar = Parameter(1.)
    t = told + dtpar * tref
    prob = GetProblem(geom, t, alpha, i_s)
    tend = prob["tend"]
    delta_t = (tend - tstart) / n_steps
    dtpar.Set(delta_t)
    D = prob["D"]
    w, wmax, levelset, u_exact, coeff_f = prob["w"], prob["wmax"], prob["levelset"], prob["u_exact"], prob["f"]

    ngmesh = prob["geometry"].GenerateMesh(maxh=prob["maxh"]*0.5**i_s, quad_dominated=False)
    mesh = Mesh(ngmesh)

    if space == "DG":
        fes1 = L2(mesh, order=k_s, dgjumps=True)
    else:
        fes1 = H1(mesh, order=k_s, dgjumps=True)
    tfe = ScalarTimeFE(k_t)
    st_fes = tfe * fes1

    lsetadap = LevelSetMeshAdaptation_Spacetime(mesh, order_space=k_lset, order_time=k_lset,
                                                threshold=0.5, discontinuous_qn=True)

    gfu = GridFunction(st_fes)
    u_last = CreateTimeRestrictedGF(gfu, 1)
    fes_l2 = L2(mesh, order=k_s)
    u_last_l2 = GridFunction(fes_l2)

    u, v = st_fes.TnT()
    h = specialcf.mesh_size
    n = specialcf.normal(D)

    ci = CutInfo(mesh, time_order=0)
    ba_gp_facets = BitArray(mesh.nfacet)
    ba_act_facets = BitArray(mesh.nfacet)
    els_hasneg = ci.GetElementsOfType(HASNEG)

    dQ = delta_t * dCut(lsetadap.levelsetp1[INTERVAL], NEG, time_order=time_order,
                        deformation=lsetadap.deformation[INTERVAL], definedonelements=els_hasneg)
    dF = delta_t * dCut(lsetadap.levelsetp1[INTERVAL], NEG, time_order=time_order, skeleton=True,
                        deformation=lsetadap.deformation[INTERVAL], definedonelements=ba_act_facets)
    dOmold = dCut(lsetadap.levelsetp1[BOTTOM], NEG, deformation=lsetadap.deformation[BOTTOM],
                  definedonelements=els_hasneg, tref=0)
    dw = delta_t * dFacetPatch(definedonelements=ba_gp_facets, time_order=time_order,
                               deformation=lsetadap.deformation[INTERVAL])

    def dt(u):
        return 1.0 / delta_t * dtref(u)

    # velocity relative to the (time-dependent) mesh deformation
    w_rel = w - dt(lsetadap.deform)

    a = RestrictedBilinearForm(st_fes, "a", check_unused=False, element_restriction=els_hasneg,
                               facet_restriction=ba_act_facets)
    a += v * (dt(u) + InnerProduct(w_rel, grad(u))) * dQ
    if alpha > 0:
        a += alpha * InnerProduct(grad(u), grad(v)) * dQ
    a += u * v * dOmold
    n_vol_integrators = len(a.integrators)
    if space == "DG":
        wn = InnerProduct(w_rel, n)
        # upwind: (|w.n| (u_down - u_up), v_down)
        a += IfPos(wn, wn * (u.Other() - u) * v.Other(), -wn * (u - u.Other()) * v) * dF
        if alpha > 0:
            jump_u = u - u.Other()
            jump_v = v - v.Other()
            avg_du = 0.5 * InnerProduct(grad(u) + grad(u.Other()), n)
            avg_dv = 0.5 * InnerProduct(grad(v) + grad(v.Other()), n)
            a += alpha * (-avg_du * jump_v - avg_dv * jump_u + lam * k_s**2 / h * jump_u * jump_v) * dF
    # SIMD evaluation of space-time elements on cut facets is not available; without this, every facet matrix
    # would throw (and log) before falling back to the non-SIMD path
    for bfi in a.integrators[n_vol_integrators:]:
        bfi.simd_evaluate = False
    c_J = gamma * (alpha / h**2 + wmax / h)
    a += c_J * (u - u.Other()) * (v - v.Other()) * dw

    f = LinearForm(st_fes)
    f += coeff_f * v * dQ
    f += u_last_l2 * v * dOmold

    u_last_l2.Set(fix_tref(u_exact, 0))
    lsetadap.ProjectOnUpdate(u_last_l2)

    def dCutQ():
        return delta_t * dCut(lsetadap.levelsetp1[INTERVAL], NEG, time_order=time_order,
                              deformation=lsetadap.deformation[INTERVAL], definedonelements=els_hasneg, order=2*k_s+2)

    err = {"l2l2": 0., "h1": 0., "dt": 0., "mat": 0.}
    stats = {"ndofs_max": 0, "ndofs_sum": 0, "nze_max": 0, "nze_sum": 0,
             "t_method": 0., "t_cpu": 0., "t_asm": 0., "t_sol": 0., "n_steps": n_steps,
             "nnzlu_max": 0, "mflop_sum": 0}
    umin_ex, umax_ex = prob.get("range", (-1., 1.))
    l2error = None

    n_slabs = 0
    while tend - told.Get() > delta_t / 2:
        if max_slabs is not None and n_slabs >= max_slabs:
            break
        n_slabs += 1
        t0 = perf_counter()
        c0 = process_time()
        lsetadap.CalcDeformation(levelset)
        ci.Update(lsetadap.levelsetp1[INTERVAL], time_order=0)

        act = GetFacetsWithNeighborTypes(mesh, a=els_hasneg, b=els_hasneg)
        ba_act_facets[:] = act
        if space == "CGall":
            ba_gp_facets[:] = act
        else:
            ba_gp_facets[:] = GetFacetsWithNeighborTypes(mesh, a=els_hasneg, b=ci.GetElementsOfType(IF))
        active_dofs = GetDofsOfElements(st_fes, els_hasneg)

        t1 = perf_counter()
        with TaskManager():
            a.Assemble(reallocate=True)
            f.Assemble()
        stats["t_asm"] += perf_counter() - t1

        t1 = perf_counter()
        res = f.vec.CreateVector()
        if solver == "pardiso_metis":
            inv = PardisoMetis(a.mat, active_dofs, n_threads)
            stats["nnzlu_max"] = max(stats["nnzlu_max"], inv.nnz_lu)
            stats["mflop_sum"] += inv.mflop
            inv.Solve(f.vec, gfu.vec)
            # one step of iterative refinement (direct solves on high order space-time systems can lose digits)
            res.data = f.vec - a.mat * gfu.vec
            corr = f.vec.CreateVector()
            inv.Solve(res, corr)
            gfu.vec.data += corr
        else:
            inv = a.mat.Inverse(active_dofs, inverse=solver)
            gfu.vec.data = inv * f.vec
            # one step of iterative refinement (direct solves on high order space-time systems can lose digits)
            res.data = f.vec - a.mat * gfu.vec
            gfu.vec.data += inv * res
        stats["t_sol"] += perf_counter() - t1
        del inv

        RestrictGFInTime(spacetime_gf=gfu, reference_time=1.0, space_gf=u_last)
        u_last_l2.Set(u_last)
        stats["t_method"] += perf_counter() - t0
        stats["t_cpu"] += process_time() - c0

        nd = active_dofs.NumSet()
        stats["ndofs_max"] = max(stats["ndofs_max"], nd)
        stats["ndofs_sum"] += nd
        stats["nze_max"] = max(stats["nze_max"], a.mat.nze)
        stats["nze_sum"] += a.mat.nze

        with TaskManager():
            dOmnew_err = dCut(lsetadap.levelsetp1[TOP], NEG, deformation=lsetadap.deformation[TOP],
                              definedonelements=els_hasneg, tref=1, order=2*k_s+2)
            l2error = sqrt(Integrate((u_exact - u_last)**2 * dOmnew_err, mesh))
            l1error = Integrate(sqrt((u_exact - u_last)**2) * dOmnew_err, mesh)
            # L1 measures of over- and undershoot w.r.t. the range of the exact solution
            over = Integrate(IfPos(u_last - umax_ex, u_last - umax_ex, 0) * dOmnew_err, mesh)
            under = Integrate(IfPos(umin_ex - u_last, umin_ex - u_last, 0) * dOmnew_err, mesh)
            l2far = sqrt(Integrate(prob.get("far", CF(1.)) * (u_exact - u_last)**2 * dOmnew_err, mesh))
            dQe = dCutQ()
            e = u_exact - gfu
            ge = prob["grad_u_exact"] - grad(gfu)
            # time derivative at fixed x: dt(u) - dt(deform) . grad(u) in reference configuration
            dte = prob["dt_u_exact"] - (dt(gfu) - InnerProduct(dt(lsetadap.deform), grad(gfu)))
            mate = dte + InnerProduct(w, ge)
            err["l2l2"] += Integrate(e**2 * dQe, mesh)
            err["h1"] += Integrate(InnerProduct(ge, ge) * dQe, mesh)
            err["dt"] += Integrate(dte**2 * dQe, mesh)
            err["mat"] += Integrate(mate**2 * dQe, mesh)

        told.Set(told.Get() + delta_t)
        if verbose:
            print("\rt = {0:12.9f}, L2 error = {1:12.9e}".format(told.Get(), l2error), end="")
    if verbose:
        print()

    if linefile is not None and D == 2:
        # final time solution along y = 0: u_h is evaluated in the reference configuration, the exact solution at the
        # corresponding (deformed) point x + Theta_h(x), so that the pointwise error is not polluted by the mapping
        # (told has already been advanced after the last time slab; reset it, so that fix_tref(., 1) is t = T)
        told.Set(tend - delta_t)
        lset_T, defo_T, uex_T = fix_tref(levelset, 1), lsetadap.deformation[TOP], fix_tref(u_exact, 1)
        with open(linefile, "w") as fh:
            fh.write("x\tuh\tu\n")
            for xi in [-1.05 + 2.6 * j / 2000 for j in range(2001)]:
                d = defo_T(mesh(xi, 0.))
                mip = mesh(xi + d[0], d[1])
                if mip.nr < 0:  # mapped point outside of the background mesh (far outside of the domain)
                    continue
                if lset_T(mip) < 0:
                    fh.write("{:.6e}\t{:.15e}\t{:.15e}\n".format(xi + d[0], u_last(mesh(xi, 0.)), uex_T(mip)))

    res = {"l2final": l2error, "l2l2": sqrt(err["l2l2"]), "h1": sqrt(err["h1"]),
           "dt": sqrt(err["dt"]), "mat": sqrt(err["mat"]), "l1final": l1error, "over": over, "under": under, "l2far": l2far, "h": prob["maxh"]*0.5**i_s, "delta_t": delta_t}
    res.update(stats)
    return res


if __name__ == "__main__":
    import sys
    for i in range(3):
        print(Solve(i_t=i, i_s=i, k_t=2, k_s=2, space=sys.argv[1] if len(sys.argv) > 1 else "DG"))
