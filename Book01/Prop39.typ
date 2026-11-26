#import "../functions.typ": *
#import "@preview/cetz:0.4.2"

#let fig39(letters) = fig({
  
})

#content-box[
  #parallel-proposition(39)
  #parallel(
    [Τὰ ἴσα τρίγωνα τὰ ἐπὶ τῆς αὐτῆς βάσεως ὄντα καὶ ἐπὶ τὰ αὐτὰ μέρη καὶ ἐν ταῖς αὐταῖς παραλλήλοις ἐστίν.],
    [Equal triangles which are on the same base, and on the same side, are also between the same parallels.],
  )
  #parallel(
    [Ἔστω ἴσα τρίγωνα τὰ ΑΒΓ, ΔΒΓ ἐπὶ τῆς αὐτῆς βάσεως ὄντα καὶ ἐπὶ τὰ αὐτὰ μέρη τῆς ΒΓ· λέγω, ὅτι καὶ ἐν ταῖς αὐταῖς παραλλήλοις ἐστίν.],
    [Let $A B C$ and $D B C$ be equal triangles which are on the same base $B C$, and on the same side (of it). I say that they are also between the same parallels.],
  )
  #parallel(
    [Ἐπεζεύχθω γὰρ ἡ ΑΔ· λέγω, ὅτι παράλληλός ἐστιν ἡ ΑΔ τῇ ΒΓ.],
    [For let $A D$ be joined. I say that $A D$ and $B C$ are parallel.],
  )
  #parallel(
    [Εἰ γὰρ μή, ἤχθω διὰ τοῦ Α σημείου τῇ ΒΓ εὐθείᾳ παράλληλος ἡ ΑΕ, καὶ ἐπεζεύχθω ἡ ΕΓ. ἴσον ἄρα ἐστὶ τὸ ΑΒΓ τρίγωνον τῷ ΕΒΓ τριγώνῳ· ἐπί τε γὰρ τῆς αὐτῆς βάσεώς ἐστιν αὐτῷ τῆς ΒΓ καὶ ἐν ταῖς αὐταῖς παραλλήλοις. ἀλλὰ τὸ ΑΒΓ τῷ ΔΒΓ ἐστιν ἴσον· καὶ τὸ ΔΒΓ ἄρα τῷ ΕΒΓ ἴσον ἐστὶ τὸ μεῖζον τῷ ἐλάσσονι· ὅπερ ἐστὶν ἀδύνατον· οὐκ ἄρα παράλληλός ἐστιν ἡ ΑΕ τῇ ΒΓ. ὁμοίως δὴ δείξομεν, ὅτι οὐδ᾿ ἄλλη τις πλὴν τῆς ΑΔ· ἡ ΑΔ ἄρα τῇ ΒΓ ἐστι παράλληλος.],
    [For, if not, let $A E$ be drawn through point $A$ parallel to the straight-line $B C$ [Prop.~1.31], and let $E C$ be joined. Thus, triangle $A B C$ is equal to triangle $E B C$. For it is on the same base as it, $B C$, and between the same parallels [Prop.~1.37]. But $A B C$ is equal to $D B C$. Thus, $D B C$ is also equal to $E B C$, the greater to the lesser. The very thing is impossible. Thus, $A E$ is not parallel to $B C$. Similarly, we can show that neither (is) any other (straight-line) than $A D$. Thus, $A D$ is parallel to $B C$.],
  )
  #parallel-fig(fig39)
  #parallel(
    [Τὰ ἄρα ἴσα τρίγωνα τὰ ἐπὶ τῆς αὐτῆς βάσεως ὄντα καὶ ἐπὶ τὰ αὐτὰ μέρη καὶ ἐν ταῖς αὐταῖς παραλλήλοις ἐστίν· ὅπερ ἔδει δεῖξαι.],
    [Thus, equal triangles which are on the same base, and on the same side, are also between the same parallels. (Which is) the very thing it was required to show.],
  )
]