#import "../functions.typ": *

#content-box[
  #parallel-proposition(38)
  #parallel(
    [Τὰ τρίγωνα τὰ ἐπὶ ἴσων βάσεων ὄντα καὶ ἐν ταῖς αὐταῖς παραλλήλοις ἴσα ἀλλήλοις ἐστίν.],
    [Triangles which are on equal bases and between the same parallels are equal to one another.],
  )
  #parallel(
    [Ἔστω τρίγωνα τὰ ΑΒΓ, ΔΕΖ ἐπὶ ἴσων βάσεων τῶν ΒΓ, ΕΖ καὶ ἐν ταῖς αὐταῖς παραλλήλοις ταῖς ΒΖ, ΑΔ· λέγω, ὅτι ἴσον ἐστὶ τὸ ΑΒΓ τρίγωνον τῷ ΔΕΖ τριγώνῳ.],
    [Let $A B C$ and $D E F$ be triangles on the equal bases $B C$ and $E F$, and between the same parallels $B F$ and $A D$. I say that triangle $A B C$ is equal to triangle $D E F$.],
  )
  #parallel-image("/Book01/fig38", 1.5in)
  #parallel(
    [Ἐκβεβλήσθω γὰρ ἡ ΑΔ ἐφ᾿ ἑκάτερα τὰ μέρη ἐπὶ τὰ Η, Θ, καὶ διὰ μὲν τοῦ Β τῇ ΓΑ παράλληλος ἤχθω ἡ ΒΗ, δὶα δὲ τοῦ Ζ τῇ ΔΕ παράλληλος ἤχθω ἡ ΖΘ. παραλληλόγραμμον ἄρα ἐστὶν ἑκάτερον τῶν ΗΒΓΑ, ΔΕΖΘ· καὶ ἴσον τὸ ΗΒΓΑ τῷ ΔΕΖΘ· ἐπί τε γὰρ ἴσων βάσεών εἰσι τῶν ΒΓ, ΕΖ καὶ ἐν ταῖς αὐταῖς παραλλήλοις ταῖς ΒΖ, ΗΘ· καί ἐστι τοῦ μὲν ΗΒΓΑ παραλληλογράμμου ἥμισυ τὸ ΑΒΓ τρίγωνον. ἡ γὰρ ΑΒ διάμετρος αὐτὸ δίχα τέμνει· τοῦ δὲ ΔΕΖΘ παραλληλογράμμου ἥμισυ τὸ ΖΕΔ τρίγωνον· ἡ γὰρ ΔΖ δίαμετρος αὐτὸ δίχα τέμνει [τὰ δὲ τῶν ἴσων ἡμίση ἴσα ἀλλήλοις ἐστίν]. ἴσον ἄρα ἐστὶ τὸ ΑΒΓ τρίγωνον τῷ ΔΕΖ τριγώνῳ.],
    [For let $A D$ be produced in both directions to $G$ and $H$, and let the (straight-line) $B G$ be drawn through $B$ parallel to $C A$ [Prop.~1.31], and let the (straight-line) $F H$ be drawn through $F$ parallel to $D E$ [Prop.~1.31]. Thus, $G B C A$ and $D E F H$ are each parallelograms. And $G B C A$ is equal to $D E F H$. For they are on the equal bases $B C$ and $E F$, and between the same parallels $B F$ and $G H$ [Prop.~1.36]. And triangle $A B C$ is half of the parallelogram $G B C A$. For the diagonal $A B$ cuts the latter in half [Prop.~1.34]. And triangle $F E D$ (is) half of parallelogram $D E F H$. For the diagonal $D F$ cuts the latter in half [Prop.~1.34]. [And the halves of equal things are equal to one another.] Thus, triangle $A B C$ is equal to triangle $D E F$.],
  )
  #parallel(
    [Τὰ ἄρα τρίγωνα τὰ ἐπὶ ἴσων βάσεων ὄντα καὶ ἐν ταῖς αὐταῖς παραλλήλοις ἴσα ἀλλήλοις ἐστίν· ὅπερ ἔδει δεῖξαι.],
    [Thus, triangles which are on equal bases and between the same parallels are equal to one another. (Which is) the very thing it was required to show.],
  )
]
#lean-proof("/lean/Elements/Book1/Prop38.lean")
