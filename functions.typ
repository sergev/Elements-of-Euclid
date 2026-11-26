// https://forum.typst.app/t/how-to-get-a-footer-with-alternating-alignment-and-custom-text-per-page/3749/10
#let footer-text = state("footer-text")
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

#let parallel(a, b, n: none) = (
  grid(
    columns: (1fr, 1fr),
    gutter: 1em,
    if n != none {
      [#enum(numbering: "αʹ.", start: n, [#a])]
    } else {a},
    if n != none {
      [#enum(numbering: "1.", start: n, [#b])]
    } else {b},
    
    // [#if n != none {numbering("1.", n)} #b],
  )
)

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
  parallel(img(if greek { "g" } else { "e" }), img("e"))
}
