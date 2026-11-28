#import "../functions.typ": *

#content-box[
  #parallel-proposition(29)
  #parallel(
    [Ἐὰν περισσὸς ἀριθμὸς περισσὸν ἀριθμὸν πολλαπλασιάσας ποιῇ τινα, ὁ γενόμενος περισσὸς ἔσται.],
    [If an odd number makes some (number by) multiplying an odd (number) then the created (number) will be odd.],
  )
  #parallel-image("/Book09/fig28", 0.8in)
  #parallel(
    [Περισσὸς γὰρ ἀριθμὸς ὁ Α περισσὸν τὸν Β πολλαπλασιάσας τὸν Γ ποιείτω· λέγω, ὅτι ὁ Γ περισσός ἐστιν.],
    [For let the odd number $A$ make $C$ (by) multiplying the odd (number) $B$. I say that $C$ is odd.],
  )
  #parallel(
    [Ἐπεὶ γὰρ ὁ Α τὸν Β πολλαπλασιάσας τὸν Γ πεποίηκεν, ὁ Γ ἄρα σύγκειται ἐκ τοσούτων ἴσων τῷ Β, ὅσαι εἰσὶν ἐν τῷ Α μονάδες. καί ἐστιν ἑκάτερος τῶν Α, Β περισσός· ὁ Γ ἄρα σύγκειται ἐκ περισσῶν ἀριθμῶν, ὧν τὸ πλῆθος περισσόν ἐστιν. ὥστε ὁ Γ περισσός ἐστιν· ὅπερ ἔδει δεῖξαι.],
    [For since $A$ has made $C$ (by) multiplying $B$, $C$ is thus composed out of so many (magnitudes) equal to $B$, as many as (there) are units in $A$ [Def.~7.15]. And each of $A$, $B$ is odd. Thus, $C$ is composed out of odd (numbers), (and) the multitude of them is odd. Hence $C$ is odd [Prop.~9.23]. (Which is) the very thing it was required to show.],
  )
]
#lean-proof("/lean/Elements/Book9/Prop29.lean")
