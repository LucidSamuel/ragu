"""Check the Poseidon tables ragu runs with against the generator that produced them.

    python3 qa/params/check_poseidon_params.py [--halo2-dir DIR] [--udon-dir DIR]

The tables are `udon`'s (`crates/udon/src/poseidon/` in the udon repository, at the revision
this workspace pins; located through `cargo metadata` unless `--udon-dir` names
the crate). The default run checks them three ways: the committed Rust tables,
the pinned Sage output under `reference/`, and the Python port's regeneration
must all agree. `--halo2-dir` adds a self-test of the port against halo2's
P128Pow5T3 tables, deployed Orchard parameters from the same script at t=3; it
needs a halo2 checkout and is not run in CI.
"""

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path

from gen_halo2_vectors import parse_constants as parse_halo2
from poseidon_params import PALLAS_BASE, VESTA_BASE, generate

HEX_LITERAL = re.compile(r"(?:fp|fq)_hex!\(\"0x([0-9a-fA-F]{64})\"\)")
SAGE_HEX = re.compile(r"0x([0-9a-f]{1,64})")
INSTANCE = re.compile(
    r"pub const (?P<name>PALLAS_BASE|PALLAS_SCALAR): PoseidonParameters<F[pq], (?P<t>\d+)> ="
    r" PoseidonParameters \{(?P<fields>.*?)\};",
    re.DOTALL,
)
FIELD = re.compile(r"(full_rounds|partial_rounds|alpha):\s*(\d+)")


def parse_udon(udon_src, instance, tables, *, t, r_f, r_p, alpha):
    """ROUND_CONSTANTS and MDS from udon's poseidon tables, checked against the
    instance's declared shape in `poseidon/mod.rs`."""
    shapes = {
        m.group("name"): (int(m.group("t")), {k: int(v) for k, v in FIELD.findall(m.group("fields"))})
        for m in INSTANCE.finditer((udon_src / "poseidon" / "mod.rs").read_text())
    }
    actual = shapes.get(instance)
    expected = (t, {"full_rounds": r_f, "partial_rounds": r_p, "alpha": alpha})
    if actual != expected:
        raise ValueError(f"udon poseidon/mod.rs: {instance} declares {actual}, expected {expected}")
    rounds = r_f + r_p
    text = (udon_src / "poseidon" / tables).read_text()
    head, _, tail = text.partition("pub(super) const MDS")
    rc_flat = [int(m, 16) for m in HEX_LITERAL.findall(head)]
    mds_flat = [int(m, 16) for m in HEX_LITERAL.findall(tail)]
    if len(rc_flat) != rounds * t or len(mds_flat) != t * t:
        raise ValueError(f"{tables}: parsed {len(rc_flat)} constants and {len(mds_flat)} MDS entries")
    return (
        [rc_flat[r * t : (r + 1) * t] for r in range(rounds)],
        [mds_flat[i * t : (i + 1) * t] for i in range(t)],
    )


def locate_udon(ragu_dir):
    """The `src/` directory of the udon crate this workspace resolves."""
    metadata = json.loads(
        subprocess.run(
            ["cargo", "metadata", "--format-version", "1", "--manifest-path", str(ragu_dir / "Cargo.toml")],
            check=True, capture_output=True, text=True,
        ).stdout
    )
    for package in metadata["packages"]:
        if package["name"] == "zakura-udon":
            return Path(package["manifest_path"]).parent / "src"
    raise ValueError("udon is not a dependency of this workspace")


def parse_sage(path, t, p, rounds=64):
    """ROUND_CONSTANTS and MDS from verbatim `generate_parameters_grain.sage` stdout."""
    text = path.read_text()
    constants = text[text.index("Round constants for GF(p):") : text.index("\nn: ")]
    matrix = text[text.index("MDS matrix:") : text.index("Inverse MDS matrix:")]

    header = dict(
        n=int(re.search(r"^n: (\d+)$", text, re.MULTILINE).group(1)),
        t=int(re.search(r"^t: (\d+)$", text, re.MULTILINE).group(1)),
    )
    if header["t"] != t or header["n"] != 255:
        raise ValueError(f"{path}: header says n={header['n']} t={header['t']}, expected n=255 t={t}")

    prime_match = re.search(
        r"^Prime number:\s+(?:0x)?(0x[0-9a-fA-F]+)$", text, re.MULTILINE
    )
    if prime_match is None or int(prime_match.group(1), 16) != p:
        actual = prime_match.group(1) if prime_match else "missing"
        raise ValueError(f"{path}: prime is {actual}, expected {p:#x}")

    rc_flat = [int(h, 16) for h in SAGE_HEX.findall(constants)]
    mds_flat = [int(h, 16) for h in SAGE_HEX.findall(matrix)]
    if len(rc_flat) != rounds * t or len(mds_flat) != t * t:
        raise ValueError(f"{path}: parsed {len(rc_flat)} constants and {len(mds_flat)} MDS entries")

    return (
        [rc_flat[r * t : (r + 1) * t] for r in range(rounds)],
        [mds_flat[i * t : (i + 1) * t] for i in range(t)],
    )


def check(label, expected_rc, expected_mds, t, r_f, r_p, p, reference=None):
    actual_rc, actual_mds = generate(t=t, r_f=r_f, r_p=r_p, p=p)
    ok = True

    if len(actual_rc) != len(expected_rc):
        print(f"  {label}: round count {len(expected_rc)} != generated {len(actual_rc)}")
        ok = False
    else:
        bad = [r for r in range(len(actual_rc)) if actual_rc[r] != expected_rc[r]]
        if bad:
            r = bad[0]
            print(f"  {label}: round constants differ in {len(bad)} round(s); first is round {r}")
            print(f"    committed {[hex(v) for v in expected_rc[r]]}")
            print(f"    generated {[hex(v) for v in actual_rc[r]]}")
            ok = False
        else:
            print(f"  {label}: {len(actual_rc) * t} round constants reproduced")

    if actual_mds == expected_mds:
        print(f"  {label}: MDS matrix reproduced")
    else:
        print(f"  {label}: MDS matrix differs from the committed one")
        ok = False

    if reference is not None:
        ref_rc, ref_mds = reference
        if (ref_rc, ref_mds) == (expected_rc, expected_mds):
            print(f"  {label}: committed tables match the pinned Sage output")
        else:
            print(f"  {label}: committed tables DIFFER from the pinned Sage output")
            ok = False
        if (ref_rc, ref_mds) == (actual_rc, actual_mds):
            print(f"  {label}: port agrees with the pinned Sage output")
        else:
            print(f"  {label}: port DIFFERS from the pinned Sage output")
            ok = False

    return ok


def main():
    here = Path(__file__).resolve().parent
    parser = argparse.ArgumentParser()
    parser.add_argument("--halo2-dir", type=Path, default=None,
                        help="path to a halo2 checkout, for the port self-test")
    parser.add_argument("--udon-dir", type=Path, default=None,
                        help="path to the udon crate; default: the one this workspace pins")
    args = parser.parse_args()

    all_ok = True

    if args.halo2_dir:
        print("halo2_poseidon P128Pow5T3 (t=3), self-test of the port:")
        for name, field, p in (("fp", "Fp", PALLAS_BASE), ("fq", "Fq", VESTA_BASE)):
            path = args.halo2_dir / "halo2_poseidon" / "src" / f"{name}.rs"
            if not path.is_file():
                print(f"  {field}: {path} not found")
                all_ok = False
                continue
            rc, mds = parse_halo2(path, 3, modulus=p)
            all_ok &= check(field, rc, mds, t=3, r_f=8, r_p=56, p=p)

    udon_src = (args.udon_dir / "src") if args.udon_dir else locate_udon(here.parents[1])
    print(f"udon (t=5), {udon_src}:")
    for instance, tables, field, curve, p in (
        ("PALLAS_BASE", "pallas_base.rs", "Fp", "pallas", PALLAS_BASE),
        ("PALLAS_SCALAR", "pallas_scalar.rs", "Fq", "vesta", VESTA_BASE),
    ):
        rc, mds = parse_udon(udon_src, instance, tables, t=5, r_f=8, r_p=56, alpha=5)
        reference = parse_sage(here / "reference" / f"{curve}-t5.txt", 5, p)
        all_ok &= check(field, rc, mds, t=5, r_f=8, r_p=56, p=p, reference=reference)

    return 0 if all_ok else 1


if __name__ == "__main__":
    sys.exit(main())
