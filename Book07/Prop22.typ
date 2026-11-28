#import "../functions.typ": *

#content-box[
  #parallel-proposition(22)
  #parallel(
    [Οἱ ἐλάχιστοι ἀριθμοὶ τῶν τὸν αὐτὸν λόγον ἐχόντων αὐτοῖς πρῶτοι πρὸς ἀλλήλους εἰσίν.],
    [The least numbers of those (numbers) having the same ratio as them are prime to one another.],
  )
  #parallel-image("/Book07/fig22", 1.6in)
  #parallel(
    [Ἔστωσαν ἐλάχιστοι ἀριθμοὶ τῶν τὸν αὐτὸν λόγον ἐχόντων αὐτοῖς οἱ Α, Β· λέγω, ὅτι οἱ Α, Β πρῶτοι πρὸς ἀλλήλους εἰσίν.],
    [Let $A$ and $B$ be the least numbers of those (numbers) having the same ratio as them. I say that $A$ and $B$ are prime to one another.],
  )
  #parallel(
    [Εἰ γὰρ μή εἰσι πρῶτοι πρὸς ἀλλήλους, μετρήσει τις αὐτοὺς ἀριθμός. μετρείτω, καὶ ἔστω ὁ Γ. καὶ ὁσάκις μὲν ὁ Γ τὸν Α μετρεῖ, τοσαῦται μονάδες ἔστωσαν ἐν τῷ Δ, ὁσάκις δὲ ὁ Γ τὸν Β μετρεῖ, τοσαῦται μονάδες ἔστωσαν ἐν τῷ Ε.],
    [For if they are not prime to one another, (then) some number will measure them. Let it (so measure them), and let it be $C$. And as many times as $C$ measures $A$, so many units let there be in $D$. And as many times as $C$ measures $B$, so many units let there be in $E$.],
  )
  #parallel(
    [Ἐπεὶ ὁ Γ τὸν Α μετρεῖ κατὰ τὰς ἐν τῷ Δ μονάδας, ὁ Γ ἄρα τὸν Δ πολλαπλασιάσας τὸν Α πεποίηκεν. διὰ τὰ αὐτὰ δὴ καὶ ὁ Γ τὸν Ε πολλαπλασιάσας τὸν Β πεποίηκεν. ἀριθμὸς δὴ ὁ Γ δύο ἀριθμοὺς τοὺς Δ, Ε πολλαπλασιάσας τοὺς Α, Β πεποίηκεν· ἔστιν ἄρα ὡς ὁ Δ πρὸς τὸν Ε, οὕτως ὁ Α πρὸς τὸν Β· οἱ Δ, Ε ἄρα τοῖς Α, Β ἐν τῷ αὐτῷ λόγῳ εἰσὶν ἐλάσσονες ὄντες αὐτῶν· ὅπερ ἐστὶν ἀδύνατον. οὐκ ἄρα τοὺς Α, Β ἀριθμοὺς ἀριθμός τις μετρήσει. οἱ Α, Β ἄρα πρῶτοι πρὸς ἀλλήλους εἰσίν· ὅπερ ἔδει δεῖξαι.],
    [Since $C$ measures $A$ according to the units in $D$, $C$ has thus made $A$ (by) multiplying $D$ [Def.~7.15]. So, for the same (reasons), $C$ has also made $B$ (by) multiplying $E$. So the number $C$ has made $A$ and $B$ (by) multiplying the two numbers $D$ and $E$ (respectively). Thus, as $D$ is to $E$, so $A$ (is) to $B$ [Prop.~7.17]. Thus, $D$ and $E$ are in the same ratio as $A$ and $B$, being less than them. The very thing is impossible. Thus, some number does not measure the numbers $A$ and $B$. Thus, $A$ and $B$ are prime to one another. (Which is) the very thing it was required to show.],
  )
]
#lean-proof("/lean/Elements/Book7/Prop22.lean")
