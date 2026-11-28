#import "../functions.typ": *

#content-box[
  #parallel-proposition(5)
  #parallel(
    [Τὰ σύμμετρα μεγέθη πρὸς ἄλληλα λόγον ἔχει, ὃν ἀριθμὸς πρὸς ἀριθμόν.],
    [Commensurable magnitudes have to one another the ratio which (some) number (has) to (some) number.],
  )
  #parallel-image("/Book10/fig005", 0.8in)
  #parallel(
    [Ἔστω σύμμετρα μεγέθη τὰ Α, Β· λέγω, ὅτι τὸ Α πρὸς τὸ Β λόγον ἔχει, ὃν ἀριθμὸς πρὸς ἀριθμόν.],
    [Let $A$ and $B$ be commensurable magnitudes. I say that $A$ has to $B$ the ratio which (some) number (has) to (some) number.],
  )
  #parallel(
    [Ἐπεὶ γὰρ σύμμετρά ἐστι τὰ Α, Β, μετρήσει τι αὐτὰ μέγεθος. μετρείτω, καὶ ἔστω τὸ Γ. καὶ ὁσάκις τὸ Γ τὸ Α μετρεῖ, τοσαῦται μονάδες ἔστωσαν ἐν τῷ Δ, ὁσάκις δὲ τὸ Γ τὸ Β μετρεῖ, τοσαῦται μονάδες ἔστωσαν ἐν τῷ Ε.],
    [For if $A$ and $B$ are commensurable (magnitudes) then some magnitude will measure them. Let it (so) measure (them), and let it be $C$. And as many times as $C$ measures $A$, so many units let there be in $D$. And as many times as $C$ measures $B$, so many units let there be in $E$.],
  )
  #parallel(
    [Ἐπεὶ οὖν τὸ Γ τὸ Α μετρεῖ κατὰ τὰς ἐν τῷ Δ μονάδας, μετρεῖ δὲ καὶ ἡ μονὰς τὸν Δ κατὰ τὰς ἐν αὐτῷ μονάδας, ἰσάκις ἄρα ἡ μονὰς τὸν Δ μετρεῖ ἀριθμὸν καὶ τὸ Γ μέγεθος τὸ Α· ἔστιν ἄρα ὡς τὸ Γ πρὸς τὸ Α, οὕτως ἡ μονὰς πρὸς τὸν Δ· ἀνάπαλιν ἄρα, ὡς τὸ Α πρὸς τὸ Γ, οὕτως ὁ Δ πρὸς τὴν μονάδα. πάλιν ἐπεὶ τὸ Γ τὸ Β μετρεῖ κατὰ τὰς ἐν τῷ Ε μονάδας, μετρεῖ δὲ καὶ ἡ μονὰς τὸν Ε κατὰ τὰς ἐν αὐτῷ μονάδας, ἰσάκις ἄρα ἡ μονὰς τὸν Ε μετρεῖ καὶ τὸ Γ τὸ Β· ἔστιν ἄρα ὡς τὸ Γ πρὸς τὸ Β, οὕτως ἡ μονὰς πρὸς τὸν Ε. ἐδείχθη δὲ καὶ ὡς τὸ Α πρὸς τὸ Γ, ὁ Δ πρὸς τὴν μονάδα· δι᾿ ἴσου ἄρα ἐστὶν ὡς τὸ Α πρὸς τὸ Β, οὕτως ὁ Δ ἀριθμὸς πρὸς τὸν Ε.],
    [Therefore, since $C$ measures $A$ according to the units in $D$, and a unit also measures $D$ according to the units in it, a unit thus measures the number $D$ as many times as the magnitude $C$ (measures) $A$. Thus, as $C$ is to $A$, so a unit (is) to $D$ [Def.~7.20].#content-box-note[There is a slight logical gap here, since Def.~7.20 applies to four numbers, rather than two numbers and two magnitudes.] Thus, inversely, as $A$ (is) to $C$, so $D$ (is) to a unit [Prop.~5.7 corr.]. Again, since $C$ measures $B$ according to the units in $E$, and a unit also measures $E$ according to the units in it, a unit thus measures $E$ the same number of times that $C$ (measures) $B$. Thus, as $C$ is to $B$, so a unit (is) to $E$ [Def.~7.20]. And it was also shown that as $A$ (is) to $C$, so $D$ (is) to a unit. Thus, via equality, as $A$ is to $B$, so the number $D$ (is) to the (number) $E$ [Prop.~5.22].],
  )
  #parallel(
    [Τὰ ἄρα σύμμετρα μεγέθη τὰ Α, Β πρὸς ἄλληλα λόγον ἔχει, ὃν ἀριθμὸς ὁ Δ πρὸς ἀριθμὸν τὸν Ε· ὅπερ ἔδει δεῖξαι.],
    [Thus, the commensurable magnitudes $A$ and $B$ have to one another the ratio which the number $D$ (has) to the number $E$. (Which is) the very thing it was required to show.],
  )
]
#lean-proof("/lean/Elements/Book10/Prop005.lean")
