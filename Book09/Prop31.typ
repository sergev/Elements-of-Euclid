#import "../functions.typ": *

#content-box[
  #parallel-proposition(31)
  #parallel(
    [Ἐὰν περισσὸς ἀριθμὸς πρός τινα ἀριθμὸν πρῶτος ᾖ, καὶ πρὸς τὸν διπλασίονα αὐτοῦ πρῶτος ἔσται.],
    [If an odd number is prime to some number then it will also be prime to its double.],
  )
  #parallel-image("/Book09/fig31", 1.1in)
  #parallel(
    [Περισσὸς γὰρ ἀριθμὸς ὁ Α πρός τινα ἀριθμὸν τὸν Β πρῶτος ἔστω, τοῦ δὲ Β διπλασίων ἔστω ὁ Γ· λέγω, ὅτι ὁ Α [καὶ] πρὸς τὸν Γ πρῶτός ἐστιν.],
    [For let the odd number $A$ be prime to some number $B$. And let $C$ be double $B$. I say that $A$ is [also] prime to $C$.],
  )
  #parallel(
    [Εἰ γὰρ μή εἰσιν [οἱ Α, Γ] πρῶτοι, μετρήσει τις αὐτοὺς ἀριθμός. μετρείτω, καὶ ἔστω ὁ Δ. καί ἐστιν ὁ Α περισσός· περισσὸς ἄρα καὶ ὁ Δ. καὶ ἐπεὶ ὁ Δ περισσὸς ὢν τὸν Γ μετρεῖ, καί ἐστιν ὁ Γ ἄρτιος, καὶ τὸν ἥμισυν ἄρα τοῦ Γ μετρήσει [ὁ Δ]. τοῦ δὲ Γ ἥμισύ ἐστιν ὁ Β· ὁ Δ ἄρα τὸν Β μετρεῖ. μετρεῖ δὲ καὶ τὸν Α. ὁ Δ ἄρα τοὺς Α, Β μετρεῖ πρώτους ὄντας πρὸς ἀλλήλους· ὅπερ ἐστὶν ἀδύνατον. οὐκ ἄρα ὁ Α πρὸς τὸν Γ πρῶτος οὔκ ἐστιν. οἱ Α, Γ ἄρα πρῶτοι πρὸς ἀλλήλους εἰσίν· ὅπερ ἔδει δεῖξαι.],
    [For if [$A$ and $C$] are not prime (to one another) then some number will measure them. Let it measure (them), and let it be $D$. And $A$ is odd. Thus, $D$ (is) also odd. And since $D$, which is odd, measures $C$, and $C$ is even, [$D$] will thus also measure half of $C$ [Prop.~9.30]. And $B$ is half of $C$. Thus, $D$ measures $B$. And it also measures $A$. Thus, $D$ measures (both) $A$ and $B$, (despite) them being prime to one another. The very thing is impossible. Thus, $A$ is not unprime to $C$. Thus, $A$ and $C$ are prime to one another. (Which is) the very thing it was required to show.],
  )
]
#lean-proof("/lean/Elements/Book9/Prop31.lean")
