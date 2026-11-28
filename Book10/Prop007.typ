#import "../functions.typ": *

#content-box[
  #parallel-proposition(7)
  #parallel(
    [Τὰ ἀσύμμετρα μεγέθη πρὸς ἄλληλα λόγον οὐκ ἔχει, ὃν ἀριθμὸς πρὸς ἀριθμόν.],
    [Incommensurable magnitudes do not have to one another the ratio which (some) number (has) to (some) number.],
  )
  #parallel(
    [Ἔστω ἀσύμμετρα μεγέθη τὰ Α, Β· λέγω, ὅτι τὸ Α πρὸς τὸ Β λόγον οὐκ ἔχει, ὃν ἀριθμὸς πρὸς ἀριθμόν.],
    [Let $A$ and $B$ be incommensurable magnitudes. I say that $A$ does not have to $B$ the ratio which (some) number (has) to (some) number.],
  )
  #parallel-image("/Book10/fig007", 0.5in)
  #parallel(
    [Εἰ γὰρ ἔχει τὸ Α πρὸς τὸ Β λόγον, ὃν ἀριθμὸς πρὸς ἀριθμόν, σύμμετρον ἔσται τὸ Α τῷ Β. οὐκ ἔστι δέ· οὐκ ἄρα τὸ Α πρὸς τὸ Β λόγον ἔχει, ὃν ἀριθμὸς πρὸς ἀριθμόν.],
    [For if $A$ has to $B$ the ratio which (some) number (has) to (some) number then $A$ will be commensurable with $B$ [Prop.~10.6]. But it is not. Thus, $A$ does not have to $B$ the ratio which (some) number (has) to (some) number.],
  )
  #parallel(
    [Τὰ ἄρα ἀσύμμετρα μεγέθη πρὸς ἄλληλα λόγον οὐκ ἔχει, καὶ τὰ ἑξῆς.],
    [Thus, incommensurable magnitudes do not have to one another, and so on ....],
  )
]
#lean-proof("/lean/Elements/Book10/Prop007.lean")
