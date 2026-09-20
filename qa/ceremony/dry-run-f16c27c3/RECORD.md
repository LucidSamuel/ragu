# Registry tag ceremony — dry run for commit `f16c27c3`

A run of the procedure in the book's "Registry Tags → Ceremony" section,
against `origin/main` at `f16c27c3bf6f1b51570cb41e2e66ed6087c5c066`, with one
shortcut: the beacon block is the first block mined after the stamp was
submitted, not the 100th after the attestation. It is a dry run. The branch
that adds this record was not merged when the code was frozen, Ragu's
internal circuits still change between releases, and the shortcut means the
ordering between code and beacon rests on the submission time rather than on
a Bitcoin attestation. The tags below validate the procedure and the tooling;
they are not for deployment.

## Step 1 — freeze

- Commit: `f16c27c3bf6f1b51570cb41e2e66ed6087c5c066` (merge of #882).
- Description covered: every circuit `ragu_pcd` registers at that commit
  (native and nested registries). The `registry-tag-param` branch changes
  where κ comes from, not any circuit, so its diff does not alter the
  pre-keyed description.

## Step 2 — public commitment

- `commit.txt` holds the commit id;
  `sha256(commit.txt) = b687ade16137eb8d693721b0c498a486ec5cf417138e37235da809a735a9ef87`.
- `ots stamp commit.txt` submitted at **2026-09-20 03:39:05 UTC** to
  `a.pool.opentimestamps.org`, `b.pool.opentimestamps.org`,
  `a.pool.eternitywall.com`, `ots.btc.catallaxy.com`.
- Bitcoin tip at submission: height 967790, hash
  `000000000000000000011e5254174eb4229bda1693b0e8e5a2871014d7db4e35`
  (mempool.space and blockstream.info agree).
- `commit.txt.ots` is the proof. At the time of this record it is still
  **pending**: no calendar transaction had confirmed, so the attestation
  block `N` is not yet known. `./continue.sh` upgrades it once one has.

## Step 3 — beacon output (shortcut: tip + 1)

- Beacon block: **967791**, the first block mined after submission
  (2026-09-20 04:02:28 UTC), selected with `./continue.sh 967791`.
- Hash `B`, from mempool.space and blockstream.info in agreement:
  `0000000000000000000038916afdcfcbc96ddbc3e2c11f7e5d566da548b755d8`
  (`beacon.txt`; the selection rule is recorded in `attestation.txt`).
- A real ceremony uses block `N + 100`; running `./continue.sh` with no
  argument after the attestation lands does exactly that.

## Step 4 — tags

`cargo run -p ragu_pcd --example registry_tags -- B` (`tags.txt`):

- native (Fp): `0x036c4c4b629858e85bc634851206ce640ec4faea673150f5a5cbb7607705241f`
- nested (Fq): `0x1cf9eff85d9fc437495a9a22d185a0e9c5e022f8b6c1968dd654fdc1e862f7a4`

## Step 5 — publish

This directory is the bundle: `commit.txt`, `commit.txt.ots`,
`attestation.txt`, `beacon.txt`, `tags.txt`. To check it: `ots info
commit.txt.ots` for the attestation (pending until upgraded), block 967791's
hash on an explorer of your choosing against `beacon.txt`, and the example
above against `tags.txt`.
