#import "../functions.typ": *

#content-box[
  #parallel-proposition(35, note: [This proposition allows us to sum a geometric series of the form $a$, $a thin r$, $a thin r^2$, $a thin r^3, dots.c a thin r^(n-1)$. According to Euclid, the sum, $S_n$, satisfies $(a thin r-a) \/ a = (a thin r^n-a) \/ S_n$. Hence, $S_n= a thin (r^n-1) \/ (r-1)$.])
  #parallel(
    [Ἐὰν ὦσιν ὁσοιδηποτοῦν ἀριθμοὶ ἑξῆς ἀνάλογον, ἀφαιρεθῶσι δὲ ἀπό τε τοῦ δευτέρου καὶ τοῦ ἐσχάτου ἴσοι τῷ πρώτῳ, ἔσται ὡς ἡ τοῦ δευτέρου ὑπεροχὴ πρὸς τὸν πρῶτον, οὕτως ἡ τοῦ ἐσχάτου ὑπεροχὴ πρὸς τοὺς πρὸ ἑαυτοῦ πάντας.],
    [If there is any multitude whatsoever of continually proportional numbers, and (numbers) equal to the first are subtracted from (both) the second and the last, then as the excess of the second (number is) to the first, so the excess of the last will be to (the sum of) all those (numbers) before it.],
  )
  #parallel-image("/Book09/fig35", 1.6in)
  #parallel(
    [Ἔστωσαν ὁποσοιδηποτοῦν ἀριθμοὶ ἑξῆς ἀνάλογον οἱ Α, ΒΓ, Δ, ΕΖ ἀφχόμενοι ἀπὸ ἐλαχίστου τοῦ Α, καὶ ἀφῃρήσθω ἀπὸ τοῦ ΒΓ καὶ τοῦ ΕΖ τῲ Α ἴσος ἑκάτερος τῶν ΒΗ, ΖΘ· λέγω, ὅτι ἐστὶν ὡς ὁ ΗΓ πρὸς τὸν Α, οὕτως ὁ ΕΘ πρὸς τοὺς Α, ΒΓ, Δ.],
    [Let $A$, $B C$, $D$, $E F$ be any multitude whatsoever of continuously proportional numbers, beginning from the least $A$. And let $B G$ and $F H$, each equal to $A$, be subtracted from $B C$ and $E F$ (respectively). I say that as $G C$ is to $A$, so $E H$ is to $A$, $B C$, $D$.],
  )
  #parallel(
    [Κείσθω γὰρ τῷ μὲν ΒΓ ἴσος ὁ ΖΚ, τῷ δὲ Δ ἴσος ὁ ΖΛ. καὶ ἐπεὶ ὁ ΖΚ τῷ ΒΓ ἴσος ἐστίν, ὧν ὁ ΖΘ τῷ ΒΗ ἴσος ἐστίν, λοιπὸς ἄρα ὁ ΘΚ λοιπῷ τῷ ΗΓ ἐστιν ἴσος. καὶ ἐπεί ἐστιν ὡς ὁ ΕΖ πρὸς τὸν Δ, οὕτως ὁ Δ πρὸς τὸν ΒΓ καὶ ὁ ΒΓ πρὸς τὸν Α, ἴσος δὲ ὁ μὲν Δ τῷ ΖΛ, ὁ δὲ ΒΓ τῷ ΖΚ, ὁ δὲ Α τῷ ΖΘ, ἔστιν ἄρα ὡς ὁ ΕΖ πρὸς τὸν ΖΛ, οὕτως ὁ ΛΖ πρὸς τὸν ΖΚ καὶ ὁ ΖΚ πρὸς τὸν ΖΘ. διελόντι, ὡς ὁ ΕΛ πρὸς τὸν ΛΖ, οὕτως ὁ ΛΚ πρὸς τὸν ΖΚ καὶ ὁ ΚΘ πρὸς τὸν ΖΘ. ἔστιν ἄρα καὶ ὡς εἷς τῶν ἡγουμένων πρὸς ἕνα τῶν ἑπομένων, οὕτως ἅπαντες οἱ ἡγούμενοι πρὸς ἅπαντας τοὺς ἑπομένους· ἔστιν ἄρα ὡς ὁ ΚΘ πρὸς τὸν ΖΘ, οὕτως οἱ ΕΛ, ΛΚ, ΚΘ πρὸς τοὺς ΛΖ, ΖΚ, ΘΖ. ἴσος δὲ ὁ μὲν ΚΘ τῷ ΓΗ, ὁ δὲ ΖΘ τῷ Α, οἱ δὲ ΛΖ, ΖΚ, ΘΖ τοὶς Δ, ΒΓ, Α· ἔστιν ἄρα ὡς ὁ ΓΗ πρὸς τὸν Α, οὕτως ὁ ΕΘ πρὸς τοὺς Δ, ΒΓ, Α. ἔστιν ἄρα ὡς ἡ τοῦ δευτέρου ὑπεροχὴ πρὸς τὸν πρῶτον, οὕτως ἡ τοῦ ἐσχάτου ὑπεροχὴ πρὸς τοὺς πρὸ ἑαυτοῦ πάντας· ὅπερ ἔδει δεῖξαι.],
    [For let $F K$ be made equal to $B C$, and $F L$ to $D$. And since $F K$ is equal to $B C$, of which $F H$ is equal to $B G$, the remainder, $H K$, is thus equal to the remainder, $G C$. And since as $E F$ is to $D$, so $D$ (is) to $B C$, and $B C$ to $A$ [Prop.~7.13], and $D$ (is) equal to $F L$, and $B C$ to $F K$, and $A$ to $F H$, thus as $E F$ is to $F L$, so $L F$ (is) to $F K$, and $F K$ to $F H$. By separation, as $E L$ (is) to $L F$, so $L K$ (is) to $F K$, and $K H$ to $F H$ [Props.~7.11, 7.13]. And thus as one of the leading (numbers) is to one of the following, so (the sum of) all of the leading (numbers is) to (the sum of) all of the following [Prop.~7.12]. Thus, as $K H$ is to $F H$, so $E L$, $L K$, $K H$ (are) to $L F$, $F K$, $H F$. And $K H$ (is) equal to $C G$, and $F H$ to $A$, and $L F$, $F K$, $H F$ to $D$, $B C$, $A$. Thus, as $C G$ is to $A$, so $E H$ (is) to $D$, $B C$, $A$. Thus, as the excess of the second (number) is to the first, so the excess of the last (is) to (the sum of) all those (numbers) before it. (Which is) the very thing it was required to show.],
  )
]
