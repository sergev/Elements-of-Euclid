#import "../functions.typ": parallel, no-footer, chapter, content-box, content-box-note

#chapter([Book 2], [ELEMENTS BOOK 2])

== _Fundamentals of Geometric Algebra_

#v(2cm)
#align(center, image("front.svg", height: 5in))

#no-footer()

#pagebreak()

#set page(
  header: [#grid(
    columns: (1fr, 1fr),
    align: (left, right),
    [ΣΤΟΙΧΕΙΩΝ βʹ.], [ELEMENTS BOOK 2]
  )
  #line(length: 100%, stroke: 0.85pt)]
)

#include "Definitions.typ"

#pagebreak()

#include "Prop01.typ"
#include "Prop02.typ"
#include "Prop03.typ"
#include "Prop04.typ"
#include "Prop05.typ"
#include "Prop06.typ"
#include "Prop07.typ"
#include "Prop08.typ"
#include "Prop09.typ"
#include "Prop10.typ"
#include "Prop11.typ"
#include "Prop12.typ"
#include "Prop13.typ"
#include "Prop14.typ"
