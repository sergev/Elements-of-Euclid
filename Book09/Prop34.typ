#import "../functions.typ": *

#content-box[
  #parallel-proposition(34)
  #parallel(
    [Ἐὰν ἀριθμὸς μήτε τῶν ἀπὸ δυάδος διπλασιαζομένων ᾖ, μήτε τὸν ἥμισυν ἔχῃ περισσόν, ἀρτιάκις τε ἄρτιός ἐστι καὶ ἀρτιάκις περισσός.],
    [If a number is neither (one) of the (numbers) doubled from a dyad, nor has an odd half, then it is (both) an even-times-even and an even-times-odd (number).],
  )
  #parallel-image("/Book09/fig33", 0.175in)
  #parallel(
    [Ἀριθμὸς γὰρ ὁ Α μήτε τῶν ἀπὸ δυάδος διπλασιαζομένων ἔστω μήτε τὸν ἥμισυν ἐχέτω περισσόν· λέγω, ὅτι ὁ Α ἀρτιάκις τέ ἐστιν ἄρτιος καὶ ἀρτιάκις περισσός.],
    [For let the number $A$ neither be (one) of the (numbers) doubled from a dyad, nor let it have an odd half. I say that $A$ is (both) an even-times-even and an even-times-odd (number).],
  )
  #parallel(
    [Ὅτι μὲν οὖν ὁ Α ἀρτιάκις ἐστὶν ἄρτιος, φανερόν· τὸν γὰρ ἥμισυν οὐκ ἔχει περισσόν. λέγω δή, ὅτι καὶ ἀρτιάκις περισσός ἐστιν. ἐὰν γὰρ τὸν Α τέμνωμεν δίχα καὶ τὸν ἥμισυν αὐτοῦ δίχα καὶ τοῦτο ἀεὶ ποιῶμεν, καταντήσομεν εἴς τινα ἀριθμὸν περισσόν, ὃς μετρήσει τὸν Α κατὰ ἄρτιον ἀριθμόν. εἰ γὰρ οὔ, καταντήσομεν εἰς δυάδα, καὶ ἔσται ὁ Α τῶν ἀπὸ δυάδος διπλασιαζομένων· ὅπερ οὐχ ὑπόκειται. ὥστε ὁ Α ἀρτιάκις περισσόν ἐστιν. ἐδείχθη δὲ καὶ ἀρτιάκις ἄρτιος. ὁ Α ἄρα ἀρτιάκις τε ἄρτιός ἐστι καὶ ἀρτιάκις περισσός· ὅπερ ἔδει δεῖξαι.],
    [In fact, (it is) clear that $A$ is an even-times-even (number) [Def.~7.8]. For it does not have an odd half. So I say that it is also an even-times-odd (number). For if we cut $A$ in half, and (then cut) its half in half, and we do this continually, then we will arrive at some odd number which will measure $A$ according to an even number. For if not, we will arrive at a dyad, and $A$ will be (one) of the (numbers) doubled from a dyad. The very opposite thing (was) assumed. Hence, $A$ is an even-times-odd (number) [Def.~7.9]. And it was also shown (to be) an even-times-even (number). Thus, $A$ is (both) an even-times-even and an even-times-odd (number). (Which is) the very thing it was required to show.],
  )
]
#lean-proof("/lean/Elements/Book9/Prop34.lean")
