"""Blender (4.2, headless, Cycles) rendering of fig:spacetime_kite from vis/scene.npz (export_kite_st.py).

  ~/.local/blender/blender-4.2.3-linux-x64/blender -b --python blender_kite_st.py -- [abcd] [samples] [mask] [threads]

Writes ../../graphics/spacetime-kite-{a,b}-blender.png (transparent background) and next to each an .anchors.json
with label anchors projected to normalized image coordinates; crop_kite_st.py crops and writes TikZ coordinates.
With "mask", panel (b) is rendered without the background mesh to vis/spacetime-kite-b-mask.png (used by
crop_kite_st.py to fade the mesh out away from the prisms).
Colours: blue = Omega(t) / Q, orange = cut prisms, dark grey = remaining active prisms, light grey = background mesh.
Style and lighting as in the proposal figure (dfg-unfitted/numexa/blender_spacetime.py).
"""
import sys, os, json
import numpy as np
import bpy
from mathutils import Vector
from bpy_extras.object_utils import world_to_camera_view

args = sys.argv[sys.argv.index("--") + 1:] if "--" in sys.argv else []
PANELS = args[0] if args else "ab"
SAMPLES = int(args[1]) if len(args) > 1 else 128
MASK = len(args) > 2 and args[2] == "mask"
THREADS = int(args[3]) if len(args) > 3 else 24
HERE = os.path.dirname(os.path.abspath(__file__))
D = np.load(os.path.join(HERE, "vis", "scene.npz"))
OUT = os.path.join(HERE, "..", "..", "graphics")

BLUE = (0.26, 0.45, 0.78, 1)
BLUE_LIGHT = (0.55, 0.72, 0.95, 1)
ORANGE = (1.0, 0.55, 0.08, 1)
DARK = (0.06, 0.06, 0.07, 1)
GREY = (0.45, 0.45, 0.48, 1)


def lin(c):
    return tuple([x ** 2.2 for x in c[:3]] + [c[3]])


def clear_scene():
    bpy.ops.wm.read_factory_settings(use_empty=True)


def new_mesh(name, verts, faces=(), edges=()):
    me = bpy.data.meshes.new(name)
    me.from_pydata([tuple(map(float, v)) for v in verts], [tuple(map(int, e)) for e in edges],
                   [tuple(int(i) for i in f if i >= 0) for f in faces])
    me.update()
    ob = bpy.data.objects.new(name, me)
    bpy.context.scene.collection.objects.link(ob)
    return ob


def material(name, color, alpha=1.0, roughness=0.45):
    m = bpy.data.materials.new(name)
    m.use_nodes = True
    b = m.node_tree.nodes["Principled BSDF"]
    b.inputs["Base Color"].default_value = lin(color)
    b.inputs["Roughness"].default_value = roughness
    b.inputs["Alpha"].default_value = alpha
    if alpha < 1.0:
        m.blend_method = "BLEND"
    return m


def surface(name, v, f, mat, smooth_shading=True):
    ob = new_mesh(name, v, f)
    ob.data.materials.append(mat)
    if smooth_shading:
        for p in ob.data.polygons:
            p.use_smooth = True
    return ob


def polyline(name, pts, radius, mat, closed=True):
    cu = bpy.data.curves.new(name, type="CURVE"); cu.dimensions = "3D"
    sp = cu.splines.new("POLY"); sp.points.add(len(pts) - 1)
    for i, p in enumerate(pts):
        sp.points[i].co = (float(p[0]), float(p[1]), float(p[2]), 1.0)
    sp.use_cyclic_u = closed
    cu.bevel_depth = radius; cu.bevel_resolution = 4; cu.fill_mode = "FULL"
    ob = bpy.data.objects.new(name, cu); bpy.context.scene.collection.objects.link(ob)
    ob.data.materials.append(mat)
    return ob


def edges(name, pts, E, radius, mat):
    cu = bpy.data.curves.new(name, type="CURVE"); cu.dimensions = "3D"
    for a, b in E:
        sp = cu.splines.new("POLY"); sp.points.add(1)
        sp.points[0].co = (*map(float, pts[a]), 1.0); sp.points[1].co = (*map(float, pts[b]), 1.0)
    cu.bevel_depth = radius; cu.bevel_resolution = 3; cu.fill_mode = "FULL"
    ob = bpy.data.objects.new(name, cu); bpy.context.scene.collection.objects.link(ob)
    ob.data.materials.append(mat)
    return ob


def curves(name, C, radius, mat):
    cu = bpy.data.curves.new(name, type="CURVE"); cu.dimensions = "3D"
    for c in C:
        sp = cu.splines.new("POLY"); sp.points.add(len(c) - 1)
        for i, p in enumerate(c):
            sp.points[i].co = (float(p[0]), float(p[1]), float(p[2]), 1.0)
    cu.bevel_depth = radius; cu.bevel_resolution = 3; cu.fill_mode = "FULL"
    ob = bpy.data.objects.new(name, cu); bpy.context.scene.collection.objects.link(ob)
    ob.data.materials.append(mat)
    return ob


def arrow(name, origin, direction, length, radius, mat):
    o = Vector([float(x) for x in origin]); d = Vector(direction).normalized()
    tip = o + d * length
    shaft_end = o + d * (length - 6 * radius)
    edges(name + "_shaft", [o, shaft_end], [(0, 1)], radius, mat)
    bpy.ops.mesh.primitive_cone_add(radius1=2.6 * radius, radius2=0, depth=6 * radius, location=shaft_end + d * 3 * radius)
    cone = bpy.context.active_object
    cone.rotation_euler = d.to_track_quat("Z", "Y").to_euler()
    cone.data.materials.append(mat)
    return tip


def scene_setup(target, cam_dir, dist, lens, res):
    sc = bpy.context.scene
    sc.render.engine = "CYCLES"; sc.cycles.device = "CPU"; sc.cycles.samples = SAMPLES
    sc.cycles.use_denoising = True
    sc.render.threads_mode = "FIXED"; sc.render.threads = THREADS
    sc.render.film_transparent = True
    sc.render.resolution_x, sc.render.resolution_y = res
    sc.view_settings.view_transform = "Standard"
    world = bpy.data.worlds.new("World"); sc.world = world; world.use_nodes = True
    bg = world.node_tree.nodes["Background"]
    bg.inputs["Color"].default_value = (1, 1, 1, 1); bg.inputs["Strength"].default_value = 0.45
    t = Vector([float(x) for x in target])

    def area(name, off, energy, size, shadow=True):
        L = bpy.data.lights.new(name, "AREA"); L.energy = energy; L.size = size
        L.cycles.cast_shadow = shadow
        ob = bpy.data.objects.new(name, L); sc.collection.objects.link(ob)
        ob.location = t + Vector(off)
        ob.rotation_euler = (t - ob.location).to_track_quat("-Z", "Y").to_euler()
    area("Key", (-3.0, -3.5, 5.0), 520, 7.0)
    area("Fill", (4.0, -2.5, 2.0), 320, 7.0, shadow=False)
    area("Rim", (1.0, 5.0, 4.0), 300, 5.0, shadow=False)
    cam = bpy.data.cameras.new("Cam"); cam.lens = lens
    co = bpy.data.objects.new("Cam", cam); sc.collection.objects.link(co)
    co.location = t + Vector(cam_dir).normalized() * dist
    co.rotation_euler = (t - co.location).to_track_quat("-Z", "Y").to_euler()
    sc.camera = co


def render(path, anchors):
    sc = bpy.context.scene
    if MASK:
        path = os.path.join(HERE, "vis", os.path.basename(path).replace("-blender.png", "-mask.png"))
    sc.render.filepath = path
    bpy.ops.render.render(write_still=True)
    if MASK:
        print("rendered", path, flush=True)
        return
    proj = {}
    for k, p in anchors.items():
        p = np.asarray(p, dtype=float)
        if p.ndim == 2:      # candidate set: the point that projects furthest to the left
            v = min((world_to_camera_view(sc, sc.camera, Vector(q)) for q in p), key=lambda w: w.x)
        else:
            v = world_to_camera_view(sc, sc.camera, Vector(p))
        proj[k] = [v.x, v.y]
    with open(path.replace(".png", ".anchors.json"), "w") as f:
        json.dump({"res": [sc.render.resolution_x, sc.render.resolution_y], "anchors": proj}, f, indent=1)
    print("rendered", path, flush=True)


CAM_A = [float(s) for s in os.environ.get("CAM_A", "-0.95,-2.3,1.35").split(",")]
CAM_B = [float(s) for s in os.environ.get("CAM_B", "-0.55,-2.1,1.45").split(",")]
CAM_G = [float(s) for s in os.environ.get("CAM_G", "-0.5,-1.9,2.1").split(",")]
DIST_A, DIST_B = float(os.environ.get("DIST_A", 7.6)), float(os.environ.get("DIST_B", 6.0))


def panel_a():
    clear_scene()
    surface("lat", D["a_lat_v"], D["a_lat_f"], material("Q", BLUE, roughness=0.35))
    surface("slab", D["a_slab_v"], D["a_slab_f"], material("Qslab", BLUE_LIGHT, roughness=0.35))
    surface("top", D["a_top_v"], D["a_top_f"], material("Qtop", BLUE_LIGHT, roughness=0.4), smooth_shading=False)
    m_ring = material("ring", DARK, roughness=0.6)
    for k, r in enumerate(D["a_rings"]):
        polyline(f"ring{k}", r, 0.011 if k in D["a_mark"] else 0.008, m_ring)
    curves("bg", D["bg_curves"], 0.007, material("bg", GREY, roughness=0.8))
    m_ax = material("axis", DARK, roughness=0.6)
    o = D["a_axis_o"]; L = float(D["a_axis_len"])
    tx = arrow("ax", o, (1, 0, 0), L, 0.011, m_ax)
    ty = arrow("ay", o, (0, 1, 0), L, 0.011, m_ax)
    tt = arrow("at", o, (0, 0, 1), L, 0.011, m_ax)
    zmax = float(D["a_lat_v"][:, 2].max())
    scene_setup((0.25, 0.0, 0.42 * zmax), CAM_A, DIST_A, 62, res=(1600, 1700))
    render(os.path.join(OUT, "spacetime-kite-a-blender.png"),
           {"Q": D["a_anchor_Q"], "In": D["a_anchor_In"], "T": D["a_anchor_T"], "x": tx, "y": ty, "t": tt})


def panel_b():
    clear_scene()
    m_q = material("Q", BLUE, roughness=0.35)
    surface("lat", D["b_lat_v"], D["b_lat_f"], m_q)
    surface("top", D["b_top_v"], D["b_top_f"], material("Qtop", BLUE_LIGHT, roughness=0.4), smooth_shading=False)
    surface("bot", D["b_bot_v"], D["b_bot_f"], m_q, smooth_shading=False)
    m_ring = material("ring", DARK, roughness=0.6)
    for k, r in enumerate(D["b_rings"]):
        polyline(f"ring{k}", r, 0.009, m_ring)
    surface("cutf", D["b_cut_fv"], D["b_cut_ff"], material("cutf", ORANGE, alpha=0.25, roughness=0.6))
    curves("cute", D["b_cut_curves"], 0.0055, material("cute", (0.55, 0.28, 0.02, 1), roughness=0.6))
    curves("ine", D["b_in_curves"], 0.0050, material("ine", (0.25, 0.25, 0.28, 1), roughness=0.6))
    if not MASK:
        curves("bg", D["b_bg_curves"], 0.0050, material("bg", GREY, roughness=0.8))
    scene_setup(D["b_center"], CAM_B, DIST_B, 62, res=(1800, 1450))
    render(os.path.join(OUT, "spacetime-kite-b-blender.png"),
           {"tlo": D["b_cand_lo"], "thi": D["b_cand_hi"], "Om": D["b_anchor_Om"], "cut": D["b_anchor_cut"]})


def panel_gp(which, fname):
    """Panels (b), (c): active prisms (wireframe) and the Ghost penalty space-time facets F x I_n (filled):
    which = "gp_cut" (DG and CG_Gamma) or "gp_all" (CG)."""
    clear_scene()
    m_q = material("Q", BLUE, alpha=0.30, roughness=0.35)          # translucent: interior facets visible
    surface("lat", D["b_lat_v"], D["b_lat_f"], m_q)
    surface("top", D["b_top_v"], D["b_top_f"], material("Qtop", BLUE_LIGHT, alpha=0.30, roughness=0.4), smooth_shading=False)
    m_ring = material("ring", DARK, roughness=0.6)
    for k, r in enumerate(D["b_rings"]):
        polyline(f"ring{k}", r, 0.009, m_ring)
    surface("gpf", D[f"b_{which}_fv"], D[f"b_{which}_ff"], material("gpf", ORANGE, alpha=0.55, roughness=0.6))
    curves("gpe", D[f"b_{which}_frame"], 0.0060, material("gpe", (0.62, 0.30, 0.03, 1), roughness=0.6))
    curves("act", D["b_act_curves"], 0.0040, material("act", (0.30, 0.30, 0.33, 1), roughness=0.6))
    if not MASK:
        curves("bg", D["b_bg_curves"], 0.0050, material("bg", GREY, roughness=0.8))
    scene_setup(D["b_center"], CAM_G, DIST_B, 62, res=(1800, 1500))
    render(os.path.join(OUT, fname), {"tlo": D["b_cand_lo"], "thi": D["b_cand_hi"], "Om": D["b_anchor_Om"]})


if "a" in PANELS:
    panel_a()
if "b" in PANELS:
    panel_b()
if "c" in PANELS:
    panel_gp("gp_cut", "spacetime-kite-c-blender.png")
if "d" in PANELS:
    panel_gp("gp_all", "spacetime-kite-d-blender.png")
