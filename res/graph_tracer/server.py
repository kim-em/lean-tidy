import random
import math
import sys
import os
import atexit

from pygraphvis import *
from threading import *

SPAWN_DIST = 5

global search_completed
search_completed = False

class NodePrivateData():
    manually_static = False

# Called under v.lock()
def create_new_node(parent_pos, name, random_off = True):
    spawn_dist = SPAWN_DIST if random_off else 0
    angle = random.uniform(0, 2 * math.pi)
    pos = vec.add(parent_pos, vec.rotate2d((spawn_dist, 0), angle))
    n = Node(name = name, pos = pos, colour = (100, 100, 100))
    n.private = NodePrivateData()
    v.graph.nodes.add(n)
    return n

def set_static(node, static):
    node.private.manually_static = static
    node.static = static

def toggle_static(node):
    set_static(node, not node.private.manually_static)

def event_handler(e):
    if e.type == InputType.QUIT:
        v.stop()
    elif e.type == InputType.M_MOVE:
        return

    node = v.get_mousedover_node()
    if node == None:
        return

    if e.type == InputType.MB_RIGHT and e.state == MouseState.UP:
        toggle_static(node)
    elif e.type == InputType.MB_MIDDLE and e.state == MouseState.UP:
        toggle_static(node)

verts = {}

def clear_viewport():
    global search_completed

    search_completed = False
    v.lock.acquire()
    v.graph.nodes = set()
    v.lock.release()
    verts = {}

def get_root(side):
    return verts["0"] if side == "L" else verts["1"]

def process_line(line):
    global search_completed

    parts = line.split("|")

    if parts[0] == "V":
        id, side, name = parts[1:]

        if not search_completed:
            v.lock.acquire()
            if id in ["0", "1"]:
                pos = (-20, 0) if side == "L" else (20, 0)
                vert = create_new_node(pos, name, False)
                vert.side = side
                vert.style.value.radius = 12
                vert.style.value.colour = (140, 101, 211) if side == "L" else (0, 197, 144)
                set_static(vert, True)
            else:
                vert = create_new_node(get_root(side).pos, name, False)
                vert.side = side
                vert.style.value.colour = (202, 185, 241) if side == "L" else (181, 249, 211)
            v.lock.release()
        else:
            vert = create_new_node(get_root(side).pos, name, False)
            vert.side = side
            vert.style.value.radius = 7
            vert.style.value.colour = (100, 100, 100)

        verts[id] = vert

        # print("V|" + str(id) + "|" + str(side) + "|" + str(name))
    elif parts[0] == "B":
        id, = parts[1:]

        vert = verts[id]

        if not search_completed:
            vert.style.value.colour = (160, 145, 225) if vert.side == "L" else (90, 225, 175)

        # print("B|" + str(id))
    elif parts[0] == "E":
        l, r = parts[1:]
        vl = verts[l]
        vr = verts[r]

        v.lock.acquire()
        if not vr in vl.adj:
            vl.adj[vr] = None
        if not vl in vr.adj:
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
    elif parts[0] == "S":
        clear_viewport()
    elif parts[0] == "D":
        search_completed = True
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

    v = vis.Visualiser(graphs.DynamicGraph(), size = (1200, 1000),
        event_handler = event_handler, title = "leangraphvis")
    v.hide_names = True

    atexit.register(delete_fifo)
    os.mkfifo(FIFO_PATH)

    listener = Thread(target = listen_loop)
    listener.daemon = True
    listener.start()

    v.render_loop()
