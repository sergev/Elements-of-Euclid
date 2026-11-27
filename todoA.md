# Book 1 Lean proofs: improvement tasks

Do them in order. After each task:
- run `make check BOOK=1` under `systemd-run --user --scope -p MemoryMax=6G -p MemorySwapMax=0`;
- when a statement or name changes, also check Book 2;
- commit.

## 10. SMT-free push
- Use `tools/gaps.sh` to target the short proofs first: Props 1–4, 8, 13–15, 17, 19, 25.
- Then regenerate the SMT-free list.
- Optionally, add a table to `Book00/Lean.typ` showing which propositions are kernel-checked and which trust the solvers.
