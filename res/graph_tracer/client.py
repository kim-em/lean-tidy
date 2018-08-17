import os
import time
import sys
import subprocess

FIFO_PATH = "rewrite_search.fifo"

if __name__ == "__main__":
    dir_path = os.path.dirname(os.path.realpath(__file__))
    subprocess.Popen(["python3", dir_path + "/server.py"])

    while not os.path.exists(FIFO_PATH):
        time.sleep(0.05)

    print("S")
    sys.stdout.flush()

    fifo = open(FIFO_PATH, "w", encoding = "utf-8")
    
    for line in sys.stdin:
        fifo.write(line)
        fifo.flush()