#import "../functions.typ": *

#content-box[
  #parallel-proposition(32)
  #parallel(
    [Ἅπας ἀριθμὸς ἤτοι πρῶτός ἐστιν ἢ ὑπὸ πρώτου τινὸς ἀριθμοῦ μετρεῖται.],
    [Every number is either prime, or is measured by some prime number.],
  )
  #parallel-image("/Book07/fig32", 0.2in)
  #parallel(
    [Ἔστω ἀριθμὸς ὁ Α· λέγω, ὅτι ὁ Α ἤτοι πρῶτός ἐστιν ἢ ὑπὸ πρώτου τινὸς ἀριθμοῦ μετρεῖται.],
    [Let $A$ be a number. I say that $A$ is either prime, or is measured by some prime number.],
  )
  #parallel(
    [Εἰ μὲν οὖν πρῶτός ἐστιν ὁ Α, γεγονὸς ἂν εἴη τό ἐπιταχθέν. εἰ δὲ σύνθετος, μετρήσει τις αὐτὸν πρῶτος ἀριθμός.],
    [In fact, if $A$ is prime, (then) that which was prescribed has happened. And if (it is) composite, (then) some prime number will measure it [Prop.~7.31].],
  )
  #parallel(
    [Ἅπας ἄρα ἀριθμὸς ἤτοι πρῶτός ἐστιν ἢ ὑπὸ πρώτου τινὸς ἀριθμοῦ μετρεῖται· ὅπερ ἔδει δεῖξαι.],
    [Thus, every number is either prime, or is measured by some prime number. (Which is) the very thing it was required to show.],
  )
]
#lean-proof("/lean/Elements/Book7/Prop32.lean")
