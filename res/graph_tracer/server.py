import random
import math
import sys
import os
import atexit

from enum import Enum
from pygraphvis import *
from threading import *

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

def event_handler(e):
    if e.type == InputType.QUIT:
        v.stop()
    elif e.type == InputType.M_MOVE:
        return

    node = v.get_mousedover_node()
    if node == None:
        return

    if e.type == InputType.MB_MIDDLE and e.state == MouseState.UP:
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

            vert = create_new_node((0, 0), name, False)
            vert.static = True
            vert.pos = pos
            vert.style.value.colour = colour
        else:
            root = verts["0"] if side == "L" else verts["1"]
            vert = create_new_node(root.pos, name, False)
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
            fifo = open(FIFO_PATH, "r")
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
