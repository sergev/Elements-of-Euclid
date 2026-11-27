# Book 1 Lean proofs: improvement tasks

Do them in order. After each task:
- run `make check BOOK=1` under `systemd-run --user --scope -p MemoryMax=6G -p MemorySwapMax=0`;
- when a statement or name changes, also check Book 2;
- commit.

## 3. Strengthen statements
Do this before task 4, because it changes the theorems that other proofs depend on.
- **Prop 4:** add `△abc = △def` to the conclusion, via `area_congruence`.
- **Prop 26:** add the same area equality.
- **Prop 1:** add `¬ c.onLine AB`, so the conclusion is a real triangle.
- Fix any callers that break.

## 4. Derive weaker variants from stronger ones
Replace each duplicated proof with a 2–3 line derivation:
- `proposition_9` from `9′`. This also fixes 9, which the opposite ray of the bisector currently satisfies.
- `proposition_11` from `11′`.
- `proposition_22′` from `22″`.
- `proposition_23` from `23′`.
- `proposition_42″` from `42‴`.
- `proposition_44` from `44′`.
- `proposition_46` from `46′`, after first picking a point off AB.

Done when: none of these proofs repeats another one's construction.

## 5. Remove redundant steps
- **Props 46 and 46′:** delete the second `proposition_34'` call, which repeats the first with identical arguments.
- **Props 24 and 39:**
  - run `tools/gaps.sh 1 24 39`;
  - remove `euclid_assert` steps that saturation no longer needs;
  - replace the "Not clear why…" and "Not sure why…" comments with what each remaining step supplies.

## 6. Speed up the other slow proofs
- Same recipe as task 2, in this order:

  | Prop | Build time |
  |---|---|
  | 45 | 65–115 s |
  | 24 | 92–100 s |
  | 44 | 82–95 s |
  | 42 | 60–67 s |
  | 48 | 21–58 s |
  | 35 | 45 s |
  | 43 | 36 s |

- Target: each under 30 s.

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
