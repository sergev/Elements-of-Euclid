#import "../functions.typ": *
#import "@preview/cetz:0.4.2"

#let fig33(letters) = fig({
  
})

#content-box[ 
  #parallel-proposition(33)
  #parallel(
    [Αἱ τὰς ἴσας τε καὶ παραλλήλους ἐπὶ τὰ αὐτὰ μέρη ἐπιζευγνύουσαι εὐθεῖαι καὶ αὐταὶ ἴσαι τε καὶ παράλληλοί εἰσιν.],
    [Straight-lines joining equal and parallel (straight-lines) on the same sides are themselves also equal and parallel.],
  )
  #parallel(
    [῎Εστωσαν ἴσαι τε καὶ παράλληλοι αἱ ΑΒ, ΓΔ, καὶ ἐπιζευγνύτωσαν αὐτὰς ἐπὶ τὰ αὐτὰ μέρη εὐθεῖαι αἱ ΑΓ, ΒΔ· λέγω, ὅτι καὶ αἱ ΑΓ, ΒΔ ἴσαι τε καὶ παράλληλοί εἰσιν.],
    [Let $A B$ and $C D$ be equal and parallel (straight-lines), and let the straight-lines $A C$ and $B D$ join them on the same sides. I say that $A C$ and $B D$ are also equal and parallel.],
  )
  #parallel-fig(fig33)
  #parallel(
    [᾿Επεζεύχθω ἡ ΒΓ. καὶ ἐπεὶ παράλληλός ἐστιν ἡ ΑΒ τῇ ΓΔ, καὶ εἰς αὐτὰς ἐμπέπτωκεν ἡ ΒΓ, αἱ ἐναλλὰξ γωνίαι αἱ ὑπὸ ΑΒΓ, ΒΓΔ ἴσαι ἀλλήλαις εἰσίν. καὶ ἐπεὶ ἴση ἐστὶν ἡ ΑΒ τῇ ΓΔ κοινὴ δὲ ἡ ΒΓ, δύο δὴ αἱ ΑΒ, ΒΓ δύο ταῖς ΒΓ, ΓΔ ἴσαι εἰσίν· καὶ γωνία ἡ ὑπὸ ΑΒΓ γωνίᾳ τῇ ὑπὸ ΒΓΔ ἴση· βάσις ἄρα ἡ ΑΓ βάσει τῇ ΒΔ ἐστιν ἴση, καὶ τὸ ΑΒΓ τρίγωνον τῷ ΒΓΔ τριγώνῳ ἴσον ἐστίν, καὶ αἱ λοιπαὶ γωνίαι ταῖς λοιπαῖς γωνίαις ἴσαι ἔσονται ἑκατέρα ἑκατέρᾳ, ὑφ᾿ ἃς αἱ ἴσαι πλευραὶ ὑποτείνουσιν· ἴση ἄρα ἡ ὑπὸ ΑΓΒ γωνία τῇ ὑπὸ ΓΒΔ. καὶ ἐπεὶ εἰς δύο εὐθείας τὰς ΑΓ, ΒΔ εὐθεῖα ἐμπίπτουσα ἡ ΒΓ τὰς ἐναλλὰξ γωνίας ἴσας ἀλλήλαις πεποίηκεν, παράλληλος ἄρα ἐστὶν ἡ ΑΓ τῇ ΒΔ. ἐδείχθη δὲ αὐτῇ καὶ ἴση.],
    [Let $B C$ be joined. And since $A B$ is parallel to $C D$, and $B C$ has fallen across them, the alternate angles $A B C$ and $B C D$ are equal to one another [Prop.~1.29]. And since $A B$ is equal to $C D$, and $B C$ is common, the two (straight-lines) $A B$, $B C$ are equal to the two (straight-lines) $D C$, $C B$.#content-box-note[The Greek text has "$B C$, $C D$", which is obviously a mistake.] And the angle $A B C$ is equal to the angle $B C D$. Thus, the base $A C$ is equal to the base $B D$, and triangle $A B C$ is equal to triangle $D C B$#content-box-note[The Greek text has "$D C B$", which is obviously a mistake.], and the remaining angles will be equal to the corresponding remaining angles subtended by the equal sides [Prop.~1.4]. Thus, angle $A C B$ is equal to $C B D$. Also, since the straight-line $B C$, (in) falling across the two straight-lines $A C$ and $B D$, has made the alternate angles ($A C B$ and $C B D$) equal to one another, $A C$ is thus parallel to $B D$ [Prop.~1.27]. And ($A C$) was also shown (to be) equal to ($B D$).],
  )
  #parallel(
    [Αἱ ἄρα τὰς ἴσας τε καὶ παραλλήλους ἐπὶ τὰ αὐτὰ μέρη ἐπιζευγνύουσαι εὐθεῖαι καὶ αὐταὶ ἴσαι τε καὶ παράλληλοί εἰσιν· ὅπερ ἔδει δεῖξαι.],
    [Thus, straight-lines joining equal and parallel (straight-lines) on the same sides are themselves also equal and parallel. (Which is) the very thing it was required to show.],
  )
]