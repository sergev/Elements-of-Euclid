#import "../functions.typ": *

#content-box[
  #parallel-proposition(33)
  #parallel(
    [Ἐὰν ἀριθμὸς τὸν ἥμισυν ἔχῃ περισσόν, ἀρτιάκις περισσός ἐστι μόνον.],
    [If a number has an odd half then it is an even-times-odd (number) only.],
  )
  #parallel-image("/Book09/fig33", 0.175in)
  #parallel(
    [Ἀριθμὸς γὰρ ὁ Α τὸν ἥμισυν ἐχέτω περισσόν· λέγω, ὅτι ὁ Α ἀρτιάκις περισσός ἐστι μόνον.],
    [For let the number $A$ have an odd half. I say that $A$ is an even-times-odd (number) only.],
  )
  #parallel(
    [Ὅτι μὲν οὖν ἀρτιάκις περισσός ἐστιν, φανερόν· ὁ γὰρ ἥμισυς αὐτοῦ περισσὸς ὢν μετρεῖ αὐτὸν ἀρτιάκις, λέγω δή, ὅτι καὶ μόνον. εἰ γὰρ ἔσται ὁ Α καὶ ἀρτιάκις ἄρτιος, μετρηθήσεται ὑπὸ ἀρτίου κατὰ ἄρτιον ἀριθμόν· ὥστε καὶ ὁ ἥμισυς αὐτοῦ μετρηθήσεται ὑπὸ ἀρτίου ἀριθμοῦ περισσὸς ὤν· ὅπερ ἐστὶν ἄτοπον. ὁ Α ἄρα ἀρτιάκις περισσός ἐστι μόνον· ὅπερ ἔδει δεῖξαι.],
    [In fact, (it is) clear that ($A$) is an even-times-odd (number). For its half, being odd, measures it an even number of times [Def.~7.9]. So I also say that (it is an even-times-odd number) only. For if $A$ is also an even-times-even (number) then it will be measured by an even (number) according to an even number [Def.~7.8]. Hence, its half will also be measured by an even number, (despite) being odd. The very thing is absurd. Thus, $A$ is an even-times-odd (number) only. (Which is) the very thing it was required to show.],
  )
]
#lean-proof("/lean/Elements/Book9/Prop33.lean")
