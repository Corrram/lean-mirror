#!/usr/bin/env python3
"""Build and export the checked classical examples, or reject a stale companion."""
import argparse
import os
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
OUTPUT = ROOT / "examples" / "classical.tex"
LAKE = os.environ.get("LAKE", "lake")

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    subprocess.run([LAKE, "build", "LeanMirror.Examples.Classical"], cwd=ROOT, check=True)
    temporary = ROOT / ".lake" / "classical-export"
    temporary.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(dir=temporary) as directory:
        Path(directory).resolve().relative_to(temporary.resolve())
        fresh = Path(directory) / "classical.tex"
        subprocess.run([LAKE, "env", "lean", "--run", "scripts/ExportClassical.lean", str(fresh)], cwd=ROOT, check=True)
        text = fresh.read_text(encoding="utf-8")
        if args.check:
            if not OUTPUT.exists() or OUTPUT.read_text(encoding="utf-8") != text:
                raise SystemExit("Stale companion. Run python scripts/classical.py")
            print("Classical companion matches the checked expressions.")
        else:
            OUTPUT.parent.mkdir(parents=True, exist_ok=True)
            OUTPUT.write_text(text, encoding="utf-8", newline="\n")
            print(f"Wrote {OUTPUT}")

if __name__ == "__main__":
    main()
