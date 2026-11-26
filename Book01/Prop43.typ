#import "../functions.typ": *

#content-box[
  #parallel-proposition(43)
  #parallel(
    [Παντὸς παραλληλογράμμου τῶν περὶ τὴν διάμετρον παραλληλογράμμων τὰ παραπληρώματα ἴσα ἀλλήλοις ἐστίν.],
    [For any parallelogram, the complements of the parallelograms about the diagonal are equal to one another.],
  )
  #parallel(
    [Ἔστω παραλληλόγραμμον τὸ ΑΒΓΔ, διάμετρος δὲ αὐτοῦ ἡ ΑΓ, περὶ δὲ τὴν ΑΓ παραλληλόγραμμα μὲν ἔστω τὰ ΕΘ, ΖΗ, τὰ δὲ λεγόμενα παραπληρώματα τὰ ΒΚ, ΚΔ· λέγω, ὅτι ἴσον ἐστὶ τὸ ΒΚ παραπλήρωμα τῷ ΚΔ παραπληρώματι.],
    [Let $A B C D$ be a parallelogram, and $A C$ its diagonal. And let $E H$ and $F G$ be the parallelograms about $A C$, and $B K$ and $K D$ the so-called complements (about $A C$). I say that the complement $B K$ is equal to the complement $K D$.],
  )
  #parallel-image("/Book01/fig43", 1.7in)
  #parallel(
    [Ἐπεὶ γὰρ παραλληλόγραμμόν ἐστι τὸ ΑΒΓΔ, διάμετρος δὲ αὐτοῦ ἡ ΑΓ, ἴσον ἐστὶ τὸ ΑΒΓ τρίγωνον τῷ ΑΓΔ τριγώνῳ. πάλιν, ἐπεὶ παραλληλόγραμμόν ἐστι τὸ ΕΘ, διάμετρος δὲ αὐτοῦ ἐστιν ἡ ΑΚ, ἴσον ἐστὶ τὸ ΑΕΚ τρίγωνον τῷ ΑΘΚ τριγώνῳ. διὰ τὰ αὐτὰ δὴ καὶ τὸ ΚΖΓ τρίγωνον τῷ ΚΗΓ ἐστιν ἴσον. ἐπεὶ οὖν τὸ μὲν ΑΕΚ τρίγωνον τῷ ΑΘΚ τριγώνῳ ἐστὶν ἴσον, τὸ δὲ ΚΖΓ τῷ ΚΗΓ, τὸ ΑΕΚ τρίγωνον μετὰ τοῦ ΚΗΓ ἴσον ἐστὶ τῷ ΑΘΚ τριγώνῳ μετὰ τοῦ ΚΖΓ· ἔστι δὲ καὶ ὅλον τὸ ΑΒΓ τρίγωνον ὅλῳ τῷ ΑΔΓ ἴσον· λοιπὸν ἄρα τὸ ΒΚ παραπλήρωμα λοιπῷ τῷ ΚΔ παραπληρώματί ἐστιν ἴσον.],
    [For since $A B C D$ is a parallelogram, and $A C$ its diagonal, triangle $A B C$ is equal to triangle $A C D$ [Prop.~1.34]. Again, since $E H$ is a parallelogram, and $A K$ is its diagonal, triangle $A E K$ is equal to triangle $A H K$ [Prop.~1.34]. So, for the same (reasons), triangle $K F C$ is also equal to (triangle) $K G C$. Therefore, since triangle $A E K$ is equal to triangle $A H K$, and $K F C$ to $K G C$, triangle $A E K$ plus $K G C$ is equal to triangle $A H K$ plus $K F C$. And the whole triangle $A B C$ is also equal to the whole (triangle) $A D C$. Thus, the remaining complement $B K$ is equal to the remaining complement $K D$.],
  )
  #parallel(
    [Παντὸς ἄρα παραλληλογράμμου χωρίου τῶν περὶ τὴν διάμετρον παραλληλογράμμων τὰ παραπληρώματα ἴσα ἀλλήλοις ἐστίν· ὅπερ ἔδει δεῖξαι.],
    [Thus, for any parallelogram, the complements of the parallelograms about the diagonal are equal to one another. (Which is) the very thing it was required to show.],
  )
]
#lean-proof("/lean/Elements/Book1/Prop43.lean")
