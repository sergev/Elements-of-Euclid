// https://forum.typst.app/t/how-to-get-a-footer-with-alternating-alignment-and-custom-text-per-page/3749/10
#let footer-text = state("footer-text")

// Edition: `typst compile --input greek=no` drops the Greek column;
// `--input lean=yes` is the English Book 1 with Lean proofs
#let with-lean = sys.inputs.at("lean", default: "no") == "yes"
#let with-greek = sys.inputs.at("greek", default: "yes") != "no" and not with-lean

// Books with Lean proofs; the Lean edition contains only these
#let lean-books = (1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11)

// The books of an edition: all thirteen, or the Lean ones
#let edition-books = if with-lean { lean-books } else { range(1, 14) }

// lean-books as text: "Book 1", "Books 1–3, 7"
#let lean-books-text = {
  let runs = ()
  for n in lean-books {
    if runs.len() > 0 and runs.at(-1).at(1) == n - 1 { runs.at(-1).at(1) = n } else { runs.push((n, n)) }
  }
  let parts = runs.map(((a, b)) => if a == b { str(a) } else if b == a + 1 { str(a) + ", " + str(b) } else { str(a) + "–" + str(b) })
  (if lean-books.len() == 1 { "Book " } else { "Books " }) + parts.join(", ")
}
#let set-footer-text(content) = footer-text.update(content)
#let no-footer() = set-footer-text([])

// https://github.com/typst/typst/issues/1889#issuecomment-2401334041
#let chapter(alt, body, depth: 1) = {
  heading(outlined: false, body, depth: depth)
  show heading: none
  heading(alt, depth: depth)
}

// https://forum.typst.app/t/how-to-display-footnotes-at-the-end-of-a-list-rather-than-the-page/3555/2
#let notes = state("notes", ())
#let content-box(body) = block(
  stroke: 0pt,
  width: auto,
  inset: 0pt,
  {
    body
    parbreak()
    set text(size: 9pt)
    set par(first-line-indent: 0em)
    
    context for (i, e) in notes.get().enumerate() {
      [#super[#numbering("*", i+2)] #e]
      parbreak()
    }
    notes.update(())
  },
)
#let content-box-note(text) = {
  notes.update(s => {
    s.push(text)
    s
  })
  context super(numbering("*", notes.get().len()+1))
}

#let parallel(a, b, n: none) = if not with-greek {
  if n != none { enum(numbering: "1.", start: n, b) } else { b }
} else {
  grid(
    columns: (1fr, 1fr),
    gutter: 1em,
    if n != none {
      [#enum(numbering: "αʹ.", start: n, [#a])]
    } else {a},
    if n != none {
      [#enum(numbering: "1.", start: n, [#b])]
    } else {b},
  )
}

#let parallel-heading(left, right, depth) = (
  parallel(
    [#heading(depth: depth, left)],
    [#heading(depth: depth, right)],
  )
)

#let parallel-proposition(n, note: none) = (
  parallel(
    [#heading(depth: 2, outlined: false, [#enum(numbering: "αʹ.", start: n, [])])],
    [#heading(depth: 2, [Proposition #n#if note != none {content-box-note[#note]}])],
  )
)

// Lemma, Corollary, etc. inside a proposition
#let parallel-subheading(left, right) = (
  parallel(
    [#heading(depth: 3, outlined: false, left)],
    [#heading(depth: 3, outlined: false, right)],
  )
)

// EPS-derived figure pair: name is a root path without suffix, e.g. "/Book02/fig01"
#let parallel-image(name, height, greek: true) = {
  let img(suffix) = align(center, image(name + suffix + ".svg", height: height, width: 100%, fit: "contain"))
  if with-greek { parallel(img(if greek { "g" } else { "e" }), img("e")) } else { img("e") }
}

// Running header: Greek title left, English right; English only centered
#let running-header(greek, english) = [
  #if with-greek {
    grid(columns: (1fr, 1fr), align: (left, right), greek, english)
  } else {
    align(center, english)
  }
  #line(length: 100%, stroke: 0.85pt)
]

// Lean proof of a proposition, typeset from its .lean file (Lean edition only)
#let lean-proof(path, title: [Formalization]) = if with-lean {
  let skip(l) = l.starts-with("import ") or l.starts-with("namespace ") or l.starts-with("open ") or l.starts-with("end ")
  let lines = ()
  for l in read(path).split("\n").filter(l => not skip(l)) {
    // one blank line where skipped lines leave two
    if not (l.trim() == "" and lines.len() > 0 and lines.last().trim() == "") { lines.push(l) }
  }
  while lines.len() > 0 and lines.first().trim() == "" { lines.remove(0) }
  while lines.len() > 0 and lines.last().trim() == "" { let _ = lines.pop() }
  heading(depth: 3, outlined: false, title)
  block(
    width: 100%,
    breakable: true,
    inset: (x: 8pt, y: 6pt),
    fill: luma(245),
    raw(lines.join("\n"), block: true, lang: "lean"),
  )
}
