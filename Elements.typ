// https://github.com/rfitzp/Elements

#import "functions.typ": footer-text, no-footer, with-greek, with-lean, edition-books


#show heading: set align(center)
#show heading.where(level: 2): set block(below: 1em)
#set page(
  footer: context {
    let text = footer-text.get() // get current footer text
    footer-text.update(none)     // reset footer text so it does not show next time
    let page-num = counter(page).get().first()
    text = if text != none {text} else {page-num}
    align(center, emph[#text])
  },
  paper: "us-letter",
  margin: (
    inside: 0.75in + 10pt,
    outside: 0.75in + 15pt
  ),
)
#set text(
  // font: "New Computer Modern",
  size: if with-lean { 11pt } else { 10pt }
)
#set par(
  first-line-indent: (amount: 2em, all: true,), // https://github.com/typst/typst/pull/5768
  justify: true,
)




#set raw(syntaxes: "/lean/lean4.sublime-syntax")
#show raw: set text(font: "DejaVu Sans Mono", size: 8.5pt)
#show raw.where(block: true): set par(justify: false)

#include "Book00/Introduction.typ"

#no-footer()

#outline(
  title: [Contents],
  depth: 1, // only show main headers
)

#pagebreak()

#if with-lean {
  include "Book00/Lean.typ"
  pagebreak()
}

#for (i, n) in edition-books.enumerate() {
  if i > 0 { pagebreak() }
  include "Book" + (if n < 10 { "0" } else { "" }) + str(n) + "/Book" + str(n) + ".typ"
}

#if with-greek {
  pagebreak()
  include "Book99/Lexicon.typ"
}
