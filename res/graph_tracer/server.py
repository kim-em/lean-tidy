import random
import math
import sys
import os
import atexit

from enum import Enum
from pygraphvis import *
from threading import *

SPAWN_DIST = 10
MAX_DEFAULT_DRAW_NODES = 20

draw_name_default = True

class NodePrivateData():
    real_name = None
    force_draw_name = False
    manually_static = False

    def __init__(self, real_name, force_draw_name, manually_static):
        self.real_name = real_name
        self.force_draw_name = force_draw_name
        self.manually_static = manually_static

# Called under v.lock()
def update_node_name(n):
    should_draw = n.private.force_draw_name or draw_name_default
    n.style.value.name = n.private.real_name if should_draw else ""
    n.style.invalidate()

# Called under v.lock()
def update_node_names():
    for n in v.graph.nodes:
        update_node_name(n)

# Called under v.lock()
def create_new_node(parent_pos, name, random_off = True, static = False, force_draw_name = False):
    if len(v.graph.nodes) >= MAX_DEFAULT_DRAW_NODES:
        global draw_name_default
        draw_name_default = False
        update_node_names()

    spawn_dist = SPAWN_DIST if random_off else 0
    angle = random.uniform(0, 2 * math.pi)
    pos = vec.add(parent_pos, vec.rotate2d((spawn_dist, 0), angle))
    n = Node(pos = pos, colour = (100, 100, 100), static = static)
    n.private = NodePrivateData(name, force_draw_name, static)

    update_node_name(n)
    v.graph.nodes.add(n)
    return n

def event_handler(e):
    if e.type == InputType.QUIT:
        v.stop()
    elif e.type == InputType.M_MOVE:
        return

    node = v.get_mousedover_node()
    if node == None:
        return

    if e.type == InputType.MB_RIGHT and e.state == MouseState.UP:
        node.private.force_draw_name = not node.private.force_draw_name

        v.lock.acquire()
        update_node_name(node)
        v.lock.release()
    elif e.type == InputType.MB_MIDDLE and e.state == MouseState.UP:
        node.private.manually_static = not node.private.manually_static
        node.static = node.private.manually_static

verts = {}

def clear_viewport():
    v.lock.acquire()
    v.graph.nodes = set()
    v.lock.release()
    verts = {}

def process_line(line):
    parts = line.split("|")

    if parts[0] == "V":
        id, side, name = parts[1:]

        v.lock.acquire()
        if id in ["0", "1"]:
            colour = (140, 101, 211) if side == "L" else (0, 197, 144)
            pos = (-20, 0) if side == "L" else (20, 0)

            vert = create_new_node((0, 0), name, False, static = True, force_draw_name = False)
            vert.pos = pos
            vert.style.value.colour = colour
        else:
            root = verts["0"] if side == "L" else verts["1"]
            vert = create_new_node(root.pos, name)
            vert.style.value.colour = (202, 185, 241) if side == "L" else (181, 249, 211)
        v.lock.release()

        verts[id] = vert

        # print("V|" + str(id) + "|" + str(side) + "|" + str(name))
    elif parts[0] == "E":
        l, r = parts[1:]
        vl = verts[l]
        vr = verts[r]

        v.lock.acquire()
        vl.adj[vr] = None
        vr.adj[vl] = None
        v.lock.release()

        # print("E|" + str(l) + "|" + str(r))
    elif parts[0] == "F":
        l, r = parts[1:]
        vl = verts[l]
        vr = verts[r]

        v.lock.acquire()
        vl.adj[vr] = (2, (230, 0, 0))
        vr.adj[vl] = (2, (230, 0, 0))
        v.lock.release()

        # print("E|" + str(l) + "|" + str(r))
    elif parts[0] == "P":
        l, r = parts[1:]
        vl = verts[l]
        vr = verts[r]

        # v.lock.acquire()
        # vl.adj[vr] = None
        # vr.adj[vl] = None
        # v.lock.release()

        # print("P|" + str(l) + "|" + str(r))
    elif parts[0] == "D":
        clear_viewport()
    else:
        print("unknown line:" + line, file = sys.stderr)

FIFO_PATH = "rewrite_search.fifo"

def listen_loop():
    try:
        while True:
            fifo = open(FIFO_PATH, "r", encoding = "utf-8")
            for line in fifo:
                sys.stderr.flush()
                process_line(line[:-1])
    except OSError as ex:
        v.stop()
        raise ex

def delete_fifo():
    try:
        os.remove(FIFO_PATH)
    except OSError:
        pass

if __name__ == "__main__":
    if os.path.exists(FIFO_PATH):
        sys.exit(0)

    highest_degree = 1
    v = vis.Visualiser(graphs.DynamicGraph(), size = (1200, 1000),
        event_handler = event_handler, title = "leangraphvis")

    atexit.register(delete_fifo)
    os.mkfifo(FIFO_PATH)

    listener = Thread(target = listen_loop)
    listener.daemon = True
    listener.start()

    v.render_loop()
