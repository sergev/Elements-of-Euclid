#import "../functions.typ": *

#content-box[
  #parallel-proposition(15)
  #parallel(
    [Ἐὰν δύο μεγέθη σύμμετρα συντεθῇ, καὶ τὸ ὅλον ἑκατέρῳ αὐτῶν σύμμετρον ἔσται· κἂν τὸ ὅλον ἑνὶ αὐτῶν σύμμετρον ᾖ, καὶ τὰ ἐξ ἀρχῆς μεγέθη σύμμετρα ἔσται.],
    [If two commensurable magnitudes are added together then the whole will also be commensurable with each of them. And if the whole is commensurable with one of them then the original magnitudes will also be commensurable (with one another).],
  )
  #parallel(
    [Συγκείσθω γὰρ δύο μεγέθη σύμμετρα τὰ ΑΒ, ΒΓ· λέγω, ὅτι καὶ ὅλον τὸ ΑΓ ἑκατέρῳ τῶν ΑΒ, ΒΓ ἐστι σύμμετρον.],
    [For let the two commensurable magnitudes $A B$ and $B C$ be laid down together. I say that the whole $A C$ is also commensurable with each of $A B$ and $B C$.],
  )
  #parallel-image("/Book10/fig015", 0.6in)
  #parallel(
    [Ἐπεὶ γὰρ σύμμετρά ἐστι τὰ ΑΒ, ΒΓ, μετρήσει τι αὐτὰ μέγεθος. μετρείτω, καὶ ἔστω τὸ Δ. ἐπεὶ οὖν τὸ Δ τὰ ΑΒ, ΒΓ μετρεῖ, καὶ ὅλον τὸ ΑΓ μετρήσει. μετρεῖ δὲ καὶ τὰ ΑΒ, ΒΓ. τὸ Δ ἄρα τὰ ΑΒ, ΒΓ, ΑΓ μετρεῖ· σύμμετρον ἄρα ἐστὶ τὸ ΑΓ ἑκατέρῳ τῶν ΑΒ, ΒΓ.],
    [For since $A B$ and $B C$ are commensurable, some magnitude will measure them. Let it (so) measure (them), and let it be $D$. Therefore, since $D$ measures (both) $A B$ and $B C$, it will also measure the whole $A C$. And it also measures $A B$ and $B C$. Thus, $D$ measures $A B$, $B C$, and $A C$. Thus, $A C$ is commensurable with each of $A B$ and $B C$ [Def.~10.1].],
  )
  #parallel(
    [Ἀλλὰ δὴ τὸ ΑΓ ἔστω σύμμετρον τῷ ΑΒ· λέγω δή, ὅτι καὶ τὰ ΑΒ, ΒΓ σύμμετρά ἐστιν.],
    [And so let $A C$ be commensurable with $A B$. I say that $A B$ and $B C$ are also commensurable.],
  )
  #parallel(
    [Ἐπεὶ γὰρ σύμμετρά ἐστι τὰ ΑΓ, ΑΒ, μετρήσει τι αὐτὰ μέγεθος. μετρείτω, καὶ ἔστω τὸ Δ. ἐπεὶ οὖν τὸ Δ τὰ ΓΑ, ΑΒ μετρεῖ, καὶ λοιπὸν ἄρα τὸ ΒΓ μετρήσει. μετρεῖ δὲ καὶ τὸ ΑΒ· τὸ Δ ἄρα τὰ ΑΒ, ΒΓ μετρήσει· σύμμετρα ἄρα ἐστὶ τὰ ΑΒ, ΒΓ.],
    [For since $A C$ and $A B$ are commensurable, some magnitude will measure them. Let it (so) measure (them), and let it be $D$. Therefore, since $D$ measures (both) $C A$ and $A B$, it will thus also measure the remainder $B C$. And it also measures $A B$. Thus, $D$ will measure (both) $A B$ and $B C$. Thus, $A B$ and $B C$ are commensurable [Def.~10.1].],
  )
  #parallel(
    [Ἐὰν ἄρα δύο μεγέθη, καὶ τὰ ἑξῆς.],
    [Thus, if two magnitudes, and so on ....],
  )
]
#lean-proof("/lean/Elements/Book10/Prop015.lean")
