# Book 1 Lean proofs: improvement tasks

Do them in order. After each task:
- run `make check BOOK=1` under `systemd-run --user --scope -p MemoryMax=6G -p MemorySwapMax=0`;
- when a statement or name changes, also check Book 2;
- commit.

## 7. Rename the multi-primed theorems
- Give descriptive names to `proposition_29′` through `29′′′′′`, `11″`/`11‴`, `42″`/`42‴`, and the other multi-primed theorems. Example: `proposition_29_interior_sum`.
- Update Book 2 in the same commit: `29''''` and `29'''''` are used 15 times each.
- Optionally, keep the old names as aliases.

## 8. Clarify scope in comments
- **Prop 45:** note that System E limits it to a figure made of two triangles.
- **Prop 35:** note that `g` is a given intersection point, and that 35′ is the general form.

## 9. Formatting pass
- Use 2-space indentation everywhere (Props 8, 15 and 29′–29″ differ).
- Use the `·` bullet only.
- Use `∃`, not `exists` (Props 11, 12).
- Remove stray spaces: `( line_from_points … )`, and `△ e :b :c` in Prop 41.
- Make doc-comment style consistent (`/-` vs `/--`).
- Check: rebuild `ElementsLean.pdf` and look at a few pages.

## 10. SMT-free push
- Use `tools/gaps.sh` to target the short proofs first: Props 1–4, 8, 13–15, 17, 19, 25.
- Then regenerate the SMT-free list.
- Optionally, add a table to `Book00/Lean.typ` showing which propositions are kernel-checked and which trust the solvers.
