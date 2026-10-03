import subprocess
import random
import sys

LEAN_BIN = "./spec/.lake/build/bin/Harness"
C_BIN = "./harness"

NUM_TESTS = 1000
MAX_TREE_DEPTH = 3
CONTAINER_WIDTH = 1000
CONTAINER_HEIGHT = 500

EPSILON = 1e-3
SEED = 6767

ALIGN_TOKENS = ["s", "e", "c", "t"]
JUSTIFY_TOKENS = ["s", "e", "c", "p"]

if SEED is not None:
    random.seed(SEED)

class Node:
    def __init__(self, kind, name=None, w=0, h=0, g=0, a="s", j="s", children=None):
        self.kind = kind  # 'O', 'R', 'C'
        self.name = name
        self.w = w
        self.h = h
        self.g = g
        self.a = a
        self.j = j
        self.children = children or []

    def to_spec(self) -> str:
        if self.kind == "O":
            return f"O {self.name} {self.w} {self.h} {self.g} {self.a}"

        children_str = " ".join(c.to_spec() for c in self.children)
        return f"{self.kind} {self.g} {self.a} {self.j} {len(self.children)} {children_str}".strip()

def gen_random_tree(depth=0, obj_counter=None) -> Node:
    if obj_counter is None:
        obj_counter = [0]

    if depth >= MAX_TREE_DEPTH or (depth > 0 and random.random() < 0.4):
        obj_counter[0] += 1
        return Node(
            kind="O",
            name=f"Obj{obj_counter[0]}",
            w=random.randint(10, 300),
            h=random.randint(10, 300),
            g=random.choice([0, 1, 2]),
            a=random.choice(ALIGN_TOKENS),
        )

    kind = random.choice(["R", "C"])
    num_children = random.randint(1, 4)
    children = [gen_random_tree(depth + 1, obj_counter) for _ in range(num_children)]

    return Node(
        kind=kind,
        g=random.choice([0, 1, 2]),
        a=random.choice(ALIGN_TOKENS),
        j=random.choice(JUSTIFY_TOKENS),
        children=children,
    )

def run_command(cmd_list) -> str:
    res = subprocess.run(cmd_list, capture_output=True, text=True)
    if res.returncode != 0:
        raise RuntimeError(f"Command failed ({' '.join(cmd_list)}):\n{res.stderr}")
    return res.stdout.strip()

def parse_placement(s):
    records = [r for r in s.split("|") if r.strip()]
    placements = []
    for rec in records:
        parts = rec.split(",")
        name = parts[0]
        x, y, w, h = map(float, parts[1:])
        placements.append((name, x, y, w, h))
    return placements

def compare_out(a, b) -> bool:
    a = parse_placement(a)
    b = parse_placement(b)
    
    for oa, ob in zip(a, b):
        if oa[0] != ob[0]:
            return False
        for xa, xb in zip(oa[1:], ob[1:]):
            if abs(xa - xb) > EPSILON:
                return False
    return True

def main():
    fail_count = 0

    print(f"Starting differential fuzzing ({NUM_TESTS} iterations)...\n")

    for i in range(1, NUM_TESTS + 1):
        tree = gen_random_tree()
        spec = tree.to_spec()

        x, y = 0, 0
        w, h = CONTAINER_WIDTH, CONTAINER_HEIGHT

        print(f"Test {i}: \"{spec}\" {x} {y} {w} {h}")

        try:
            lean_out = run_command([LEAN_BIN, spec, str(x), str(y), str(w), str(h)])
            c_out = run_command([C_BIN, spec, str(x), str(y), str(w), str(h)])

            if compare_out(lean_out, c_out):
                print("  -> OK\n")
            else:
                fail_count += 1
                print("  -> FAIL")
                print(f"     Lean output : {lean_out}")
                print(f"     C output    : {c_out}\n")

        except Exception as err:
            fail_count += 1
            print(f"  -> FAIL (Execution Error: {err})\n")

    print("=" * 40)
    print(f"Completed {NUM_TESTS} tests.")
    print(f"Total Failures: {fail_count}")
    print("=" * 40)

    if fail_count > 0:
        sys.exit(1)


if __name__ == "__main__":
    main()
