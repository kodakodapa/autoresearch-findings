# ar-timeout: 1800
# The embedded import Programme selects the full library mount in ProgrammeCheckRunner.
import os, re, subprocess, tempfile
from pathlib import Path
SOURCE = 'import Programme.«20261102-1249-proof-complexity».UniformC3.Main\n#print axioms Programme.«20261102-1249-proof-complexity».UniformC3.no_standard_degree_two\n'
THEOREMS = ['Programme.«20261102-1249-proof-complexity».UniformC3.no_standard_degree_two']
with tempfile.TemporaryDirectory() as d:
    path = os.path.join(d, "Check.lean")
    with open(path, "w", encoding="utf-8") as f:
        f.write(SOURCE)
    library = os.environ.get("AR_LIBRARY", "/library")
    root = Path(library)
    libs = [root / ".lake/build/lib/lean"]
    libs += sorted(root.glob(".lake/packages/*/.lake/build/lib/lean"))
    env = dict(os.environ, LEAN_PATH=os.pathsep.join(str(p) for p in libs))
    # elan picks the pinned toolchain from cwd; a plain lean binary ignores it.
    cwd = library if (root / "lean-toolchain").is_file() else d
    result = subprocess.run(["lean", path], cwd=cwd, capture_output=True, text=True, env=env)
output = result.stdout + result.stderr
print(output[-3000:])
assert result.returncode == 0, "Lean compilation failed"
assert "error:" not in output and "sorryAx" not in output
for name in THEOREMS:
    pattern = re.escape("'" + name + "'") + r"\s+depends on axioms:\s*\[([^\]]*)\]"
    match = re.search(pattern, output)
    if match:
        actual = {a.strip() for a in match[1].split(',') if a.strip()}
    else:
        assert "'" + name + "' does not depend on any axioms" in output, "missing axiom output"
        actual = set()
    assert actual <= {"propext", "Classical.choice", "Quot.sound"}, actual
