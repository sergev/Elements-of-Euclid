#import "../functions.typ": *

#content-box[
  #parallel-proposition(8)
  #parallel(
    [Ἐὰν δύο μεγέθη πρὸς ἄλληλα λόγον μὴ ἔχῃ, ὃν ἀριθμὸς πρὸς ἀριθμόν, ἀσύμμετρα ἔσται τὰ μεγέθη.],
    [If two magnitudes do not have to one another the ratio which (some) number (has) to (some) number then the magnitudes will be incommensurable.],
  )
  #parallel-image("/Book10/fig007", 0.5in)
  #parallel(
    [Δύο γὰρ μεγέθη τὰ Α, Β πρὸς ἄλληλα λόγον μὴ ἐχέτω, ὃν ἀριθμὸς πρὸς ἀριθμόν· λέγω, ὅτι ἀσύμμετρά ἐστι τὰ Α, Β μεγέθη.],
    [For let the two magnitudes $A$ and $B$ not have to one another the ratio which (some) number (has) to (some) number. I say that the magnitudes $A$ and $B$ are incommensurable.],
  )
  #parallel(
    [Εἰ γὰρ ἔσται σύμμετρα, τὸ Α πρὸς τὸ Β λόγον ἕξει, ὃν ἀριθμὸς πρὸς ἀριθμόν. οὐκ ἔχει δέ. ἀσύμμετρα ἄρα ἐστὶ τὰ Α, Β μεγέθη.],
    [For if they are commensurable, $A$ will have to $B$ the ratio which (some) number (has) to (some) number [Prop.~10.5]. But it does not have (such a ratio). Thus, the magnitudes $A$ and $B$ are incommensurable.],
  )
  #parallel(
    [Ἐὰν ἄρα δύο μεγέθη πρὸς ἄλληλα, καὶ τὰ ἑξῆς.],
    [Thus, if two magnitudes ... to one another, and so on ....],
  )
]
#lean-proof("/lean/Elements/Book10/Prop008.lean")
