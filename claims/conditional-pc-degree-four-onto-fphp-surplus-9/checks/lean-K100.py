# ar-timeout: 1800
# The embedded import Programme selects the full library mount in ProgrammeCheckRunner.
import os, re, subprocess, tempfile
from pathlib import Path
SOURCE = 'import Programme.«20261104-1627-proof-complexity».ConcreteDegreeFour\nimport Programme.«20261104-1627-proof-complexity».RemainingSpanning\n#eval IO.println "AR_STATEMENT_BEGIN"\n#check @Programme.«20261104-1627-proof-complexity».ConcreteDegreeFour.nodrop\n#check @Programme.«20261104-1627-proof-complexity».ConcreteDegreeFour.invariant\n#check @Programme.«20261104-1627-proof-complexity».ConcreteDegreeFour.no_stdpc\n#check @Programme.«20261104-1627-proof-complexity».ConcreteDegreeFour.no_ppc\n#check @Programme.«20261104-1627-proof-complexity».RemainingSpanning.invariant\n#check @Programme.«20261104-1627-proof-complexity».RemainingSpanning.no_stdpc_le\n#eval IO.println "AR_STATEMENT_END"\n#print axioms Programme.«20261104-1627-proof-complexity».ConcreteDegreeFour.nodrop\n#print axioms Programme.«20261104-1627-proof-complexity».ConcreteDegreeFour.invariant\n#print axioms Programme.«20261104-1627-proof-complexity».ConcreteDegreeFour.no_stdpc\n#print axioms Programme.«20261104-1627-proof-complexity».ConcreteDegreeFour.no_ppc\n#print axioms Programme.«20261104-1627-proof-complexity».RemainingSpanning.invariant\n#print axioms Programme.«20261104-1627-proof-complexity».RemainingSpanning.no_stdpc_le\n'
THEOREMS = ['Programme.«20261104-1627-proof-complexity».ConcreteDegreeFour.nodrop', 'Programme.«20261104-1627-proof-complexity».ConcreteDegreeFour.invariant', 'Programme.«20261104-1627-proof-complexity».ConcreteDegreeFour.no_stdpc', 'Programme.«20261104-1627-proof-complexity».ConcreteDegreeFour.no_ppc', 'Programme.«20261104-1627-proof-complexity».RemainingSpanning.invariant', 'Programme.«20261104-1627-proof-complexity».RemainingSpanning.no_stdpc_le']
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
print(output)
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
