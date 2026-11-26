#import "../functions.typ": parallel, no-footer, set-footer-text, with-greek, with-lean

// TITLEPAGE

#set align(center)
#set document(title: [EUCLID'S ELEMENTS OF GEOMETRY])
#show title: set text(size: 24pt)

#no-footer()


#align(
  horizon,
  [ 
    #title()
    
    #v(3cm)
    
    #text(16pt, if with-greek [
      The Greek text of J.L.~Heiberg (1883--1885)
      
      from _Euclidis Elementa, edidit et Latine interpretatus est I.L.~Heiberg, in aedibus B.G.~Teubneri, 1883--1885_
      
      edited, and provided with a modern English translation, by
       
        _Richard Fitzpatrick_
    ] else [
      A modern English translation of the Greek text of J.L.~Heiberg (1883--1885)

      from _Euclidis Elementa, edidit et Latine interpretatus est I.L.~Heiberg, in aedibus B.G.~Teubneri, 1883--1885_

      by

        _Richard Fitzpatrick_
    ])

    #if with-lean {
      v(5mm)
      text(14pt)[Book 1, with proofs formalized in Lean]
    }

    #v(1cm)

    #image("/euclid.jpg", height: 4.5in)
  ]
)


#pagebreak()

#no-footer()

// COPYRIGHT PAGE
#set align(left)

#set list(
  marker: [],
  indent: 0em,
  body-indent: 0em,
)

- First edition - 2007
- Revised and corrected - 2008
- Second edition - 2014


// ISBN 978-0-6151-7984-1

#pagebreak()
