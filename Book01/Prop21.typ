#import "../functions.typ": *
#import "@preview/cetz:0.4.2"

#let fig21(letters) = fig({
  
})

#content-box[
  #parallel-proposition(21)
  
  #parallel(
    [᾿Εὰν τριγώνου ἐπὶ μιᾶς τῶν πλευρῶν ἀπὸ τῶν περάτων δύο εὐθεῖαι ἐντὸς συσταθῶσιν, αἱ συσταθεῖσαι τῶν λοιπῶν τοῦ τριγώνου δύο πλευρῶν ἐλάττονες μὲν ἔσονται, μείζονα δὲ γωνίαν περιέξουσιν.],
    [If two internal straight-lines are constructed on one of the sides of a triangle, from its ends, the constructed (straight-lines) will be less than the two remaining sides of the triangle, but will encompass a greater angle.],
  )
  #parallel(
    [Τριγώνου γὰρ τοῦ ΑΒΓ ἐπὶ μιᾶς τῶν πλευρῶν τῆς ΒΓ ἀπὸ τῶν περάτων τῶν Β, Γ δύο εὐθεῖαι ἐντὸς συνεστάτωσαν αἱ ΒΔ, ΔΓ· λέγω, ὅτι αἱ ΒΔ, ΔΓ τῶν λοιπῶν τοῦ τριγώνου δύο πλευρῶν τῶν ΒΑ, ΑΓ ἐλάσσονες μέν εἰσιν, μείζονα δὲ γωνίαν περιέχουσι τὴν ὑπὸ ΒΔΓ τῆς ὑπὸ ΒΑΓ.],
    [For let the two internal straight-lines $B D$ and $D C$ be constructed on one of the sides $B C$ of the triangle $A B C$, from its ends $B$ and $C$ (respectively). I say that $B D$ and $D C$ are less than the (sum of the) two remaining sides of the triangle $B A$ and $A C$, but encompass an angle $B D C$ greater than $B A C$.],
  )
καʹ.


#parallel-fig(fig21)
  #parallel(
    [Διήχθω γὰρ ἡ ΒΔ ἐπὶ τὸ Ε. καὶ ἐπεὶ παντὸς τριγώνου αἱ δύο πλευραὶ τῆς λοιπῆς μείζονές εἰσιν, τοῦ ΑΒΕ ἄρα τριγώνου αἱ δύο πλευραὶ αἱ ΑΒ, ΑΕ τῆς ΒΕ μείζονές εἰσιν· κοινὴ προσκείσθω ἡ ΕΓ· αἱ ἄρα ΒΑ, ΑΓ τῶν ΒΕ, ΕΓ μείζονές εἰσιν. πάλιν, ἐπεὶ τοῦ ΓΕΔ τριγώνου αἱ δύο πλευραὶ αἱ ΓΕ, ΕΔ τῆς ΓΔ μείζονές εἰσιν, κοινὴ προσκείσθω ἡ ΔΒ· αἱ ΓΕ, ΕΒ ἄρα τῶν ΓΔ, ΔΒ μείζονές εἰσιν. ἀλλὰ τῶν ΒΕ, ΕΓ μείζονες ἐδείχθησαν αἱ ΒΑ, ΑΓ· πολλῷ ἄρα αἱ ΒΑ, ΑΓ τῶν ΒΔ, ΔΓ μείζονές εἰσιν.],
    [For let $B D$ be drawn through to $E$. And since in any triangle (the sum of any) two sides is greater than the remaining (side) [Prop.~1.20], in triangle $A B E$ the (sum of the) two sides $A B$ and $A E$ is thus greater than $B E$. Let $E C$ be added to both. Thus, (the sum of) $B A$ and $A C$ is greater than (the sum of) $B E$ and $E C$. Again, since in triangle $C E D$ the (sum of the) two sides $C E$ and $E D$ is greater than $C D$, let $D B$ be added to both. Thus, (the sum of) $C E$ and $E B$ is greater than (the sum of) $C D$ and $D B$. But, (the sum of) $B A$ and $A C$ was shown (to be) greater than (the sum of) $B E$ and $E C$. Thus, (the sum of) $B A$ and $A C$ is much greater than (the sum of) $B D$ and $D C$.],
  )
  #parallel(
    [Πάλιν, ἐπεὶ παντὸς τριγώνου ἡ ἐκτὸς γωνία τῆς ἐντὸς καὶ ἀπεναντίον μείζων ἐστίν, τοῦ ΓΔΕ ἄρα τριγώνου ἡ ἐκτὸς γωνία ἡ ὑπὸ ΒΔΓ μείζων ἐστὶ τῆς ὑπὸ ΓΕΔ. διὰ ταὐτὰ τοίνυν καὶ τοῦ ΑΒΕ τριγώνου ἡ ἐκτὸς γωνία ἡ ὑπὸ ΓΕΒ μείζων ἐστὶ τῆς ὑπὸ ΒΑΓ. ἀλλὰ τῆς ὑπὸ ΓΕΒ μείζων ἐδείχθη ἡ ὑπὸ ΒΔΓ· πολλῷ ἄρα ἡ ὑπὸ ΒΔΓ μείζων ἐστὶ τῆς ὑπὸ ΒΑΓ.],
    [Again, since in any triangle the external angle is greater than the internal and opposite (angles) [Prop.~1.16], in triangle $C D E$ the external angle $B D C$ is thus greater than $C E D$. Accordingly, for the same (reason), the external angle $C E B$ of the triangle $A B E$ is also greater than $B A C$. But, $B D C$ was shown (to be) greater than $C E B$. Thus, $B D C$ is much greater than $B A C$.],
  )
  #parallel(
    [᾿Εὰν ἄρα τριγώνου ἐπὶ μιᾶς τῶν πλευρῶν ἀπὸ τῶν περάτων δύο εὐθεῖαι ἐντὸς συσταθῶσιν, αἱ συσταθεῖσαι τῶν λοιπῶν τοῦ τριγώνου δύο πλευρῶν ἐλάττονες μέν εἰσιν, μείζονα δὲ γωνίαν περιέχουσιν· ὅπερ ἔδει δεῖξαι.],
    [Thus, if two internal straight-lines are constructed on one of the sides of a triangle, from its ends, the constructed (straight-lines) are less than the two remaining sides of the triangle, but encompass a greater angle. (Which is) the very thing it was required to show.],
  )


]
