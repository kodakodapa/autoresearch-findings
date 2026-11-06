# ar-timeout: 1800
# The embedded import Programme selects the full library mount in ProgrammeCheckRunner.
import os, re, subprocess, tempfile
SOURCE = 'import Programme.«20261028-0841-proof-complexity».L3.Main\n#print axioms Programme.«20261028-0841-proof-complexity».L3.Main.no_deg4\n'
THEOREMS = ['Programme.«20261028-0841-proof-complexity».L3.Main.no_deg4']
with tempfile.TemporaryDirectory() as d:
    path = os.path.join(d, "Check.lean")
    with open(path, "w", encoding="utf-8") as f:
        f.write(SOURCE)
    result = subprocess.run(["lean", path], cwd=d, capture_output=True, text=True,
                            env=dict(os.environ, LEAN_PATH="/library/.lake/build/lib/lean"))
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
