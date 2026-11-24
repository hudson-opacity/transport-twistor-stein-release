#!/usr/bin/env python3
"""Package the verified Steinness proof. Run with an optional output ZIP path."""

import argparse
import hashlib
import os
import tempfile
from pathlib import Path
from zipfile import ZipFile, ZipInfo


ROOT = Path(__file__).resolve().parents[1]
PREFIX = "stein-transport-twistor-lean"
VERIFICATION = Path("output/verification")
SOURCE_MANIFEST = VERIFICATION / "lean-sources.sha256"
EXECUTABLES = {"scripts/check-stein.sh", "scripts/package-stein.py", "scripts/build-stein-pdf.py"}


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def submission_files():
    proof_inputs = {
        *ROOT.glob("*.lean"),
        *(ROOT / "TransportOkaGrauert").rglob("*.lean"),
        *(ROOT / name for name in (
            "lakefile.toml", "lake-manifest.json", "lean-toolchain", "scripts/check-stein.sh"
        )),
    }
    files = {p.relative_to(ROOT).as_posix(): p.read_bytes() for p in proof_inputs}
    manifest = (ROOT / SOURCE_MANIFEST).read_bytes()
    expected = {}
    for line in manifest.decode().splitlines():
        digest, name = line.split("  ", 1)
        if name in expected:
            raise ValueError(f"Duplicate source manifest entry: {name}")
        expected[name] = digest
    if expected != {name: sha256(data) for name, data in files.items()}:
        raise ValueError("Proof inputs differ from their verification manifest.")

    files[SOURCE_MANIFEST.as_posix()] = manifest
    for path in (
        Path("STEIN-INTERIOR.md"), Path("STEIN-FORMALIZATION.md"),
        Path("output/pdf/stein-transport-twistor.pdf"), Path("scripts/package-stein.py"),
        Path("scripts/build-stein-pdf.py"),
        VERIFICATION / "stein-check.txt", VERIFICATION / "stein-clean-build.txt",
        VERIFICATION / "stein-endpoints.txt", VERIFICATION / "stein-upstream-replay.txt",
        VERIFICATION / "stein-release-extraction.txt",
    ):
        files[path.as_posix()] = (ROOT / path).read_bytes()
    # Inside an extracted submission, the reviewer guide is already at its root.
    guide = "README.md" if (ROOT / "SHA256SUMS").is_file() else "submission/README.md"
    files["README.md"] = (ROOT / guide).read_bytes()
    for name in ("formalization.yaml", "LICENSE", "LICENSE-MANUSCRIPT", "LICENSE-MANUSCRIPT.txt", "NOTICE"):
        if (ROOT / name).is_file():
            files[name] = (ROOT / name).read_bytes()
    files["SHA256SUMS"] = "".join(
        f"{sha256(files[name])}  {name}\n" for name in sorted(files)
    ).encode()
    return files


def package(destination):
    if destination.suffix.lower() != ".zip":
        raise ValueError("Choose an output path ending in .zip.")
    files = submission_files()
    destination.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(dir=destination.parent) as temporary:
        stage = Path(temporary) / "submission.zip"
        with ZipFile(stage, "w") as bundle:
            for name in sorted(files):
                # Fixed ZIP_STORED entries, date and UNIX modes make packaging
                # independent of the source mtimes, host and zlib version.
                entry = ZipInfo(f"{PREFIX}/{name}", date_time=(1980, 1, 1, 0, 0, 0))
                entry.create_system = 3
                entry.external_attr = (0o100755 if name in EXECUTABLES else 0o100644) << 16
                bundle.writestr(entry, files[name])
        with ZipFile(stage) as bundle:
            error = bundle.testzip()
            if error:
                raise ValueError(f"CRC failure: {error}")
            for name, data in files.items():
                if bundle.read(f"{PREFIX}/{name}") != data:
                    raise ValueError(f"Archived bytes differ: {name}")
        os.replace(stage, destination)
    print(f"{sha256(destination.read_bytes())}  {destination}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("zip_path", type=Path, nargs="?",
                        default=ROOT / "output/submission" / f"{PREFIX}.zip")
    package(parser.parse_args().zip_path.resolve())
