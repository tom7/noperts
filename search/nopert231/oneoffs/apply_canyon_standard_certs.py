import json
import shutil
import os

tree_path = ".artifacts/nopert229/tree_0.json"
backup_path = ".artifacts/nopert229/tree_0.json.bak_decomp"

if not os.path.exists(backup_path):
    shutil.copyfile(tree_path, backup_path)
    print(f"Backed up {tree_path} to {backup_path}")

with open(tree_path) as f:
    tree_data = json.load(f)

with open("canyon_standard_certs.json") as f:
    certs = json.load(f)

def find_node(node, path):
    if not path:
        return node
    idx = int(path[0])
    return find_node(node["children"][idx], path[1:])

# 1. Update 5 direct canyon leaves:
direct_paths = [
    "3121303021",
    "3121303022",
    "3121303023",
    "3121303200",
    "312130332"
]

for p in direct_paths:
    n = find_node(tree_data["tree"], p)
    assert "decomposed_certificate" in n or "certificate" in n
    if "decomposed_certificate" in n:
        del n["decomposed_certificate"]
    c = certs[p]
    n["certificate"] = c
    n["direct_bounds"] = {
        "r_lower": c["r"],
        "c_lower": c["c"]
    }
    print(f"Updated {p} with standard certificate (r={c['r']}, c={c['c']})")

# 2. Update path 3121300 by splitting into 4 children:
p_split = "3121300"
n_split = find_node(tree_data["tree"], p_split)
if "decomposed_certificate" in n_split:
    del n_split["decomposed_certificate"]
if "certificate" in n_split:
    del n_split["certificate"]
if "direct_bounds" in n_split:
    del n_split["direct_bounds"]

n_split["children"] = []
for c_idx in range(4):
    c_path = p_split + str(c_idx)
    c_cert = certs[c_path]
    child_node = {
        "path": c_path,
        "direct_bounds": {
            "r_lower": c_cert["r"],
            "c_lower": c_cert["c"]
        },
        "certificate": c_cert
    }
    n_split["children"].append(child_node)
    print(f"Added child {c_path} with standard certificate (r={c_cert['r']}, c={c_cert['c']})")

# 3. Audit entire tree:
leaves_total = 0
leaves_standard = 0
leaves_decomp = 0
leaves_missing = 0

def audit(n, path):
    global leaves_total, leaves_standard, leaves_decomp, leaves_missing
    if n.get("children"):
        for i, c in enumerate(n["children"]):
            audit(c, path + str(i))
    else:
        leaves_total += 1
        if "certificate" in n:
            leaves_standard += 1
        elif "decomposed_certificate" in n:
            leaves_decomp += 1
        else:
            leaves_missing += 1

audit(tree_data["tree"], "")

print("\n--- Tree 0 Final Audit ---")
print(f"Total leaves: {leaves_total}")
print(f"Standard leaves (Tag 1): {leaves_standard}")
print(f"Decomposed leaves: {leaves_decomp}")
print(f"Missing certificates: {leaves_missing}")

assert leaves_decomp == 0, "Found decomposed leaves!"
assert leaves_missing == 0, "Found missing leaves!"
assert leaves_standard == leaves_total, "Not all leaves are standard!"

with open(tree_path, "w") as f:
    json.dump(tree_data, f, indent=2)

print(f"Successfully saved updated {tree_path}!")
