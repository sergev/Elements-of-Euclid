#import "../functions.typ": *

#content-box[
  #parallel-proposition(23)
  #parallel(
    [Ἐπὶ τῆς αὐτῆς εὐθείας δύο τμήματα κύκλων ὅμοια καὶ ἄνισα οὐ συσταθήσεται ἐπὶ τὰ αὐτὰ μέρη.],
    [Two similar and unequal segments of circles cannot be constructed on the same side of the same straight-line.],
  )
  #parallel(
    [Εἰ γὰρ δυνατόν, ἐπὶ τῆς αὐτῆς εὐθείας τῆς ΑΒ δύο τμήματα κύκλων ὅμοια καὶ ἄνισα συνεστάτω ἐπὶ τὰ αὐτὰ μέρη τὰ ΑΓΒ, ΑΔΒ, καὶ διήχθω ἡ ΑΓΔ, καὶ ἐπεζεύχθωσαν αἱ ΓΒ, ΔΒ.],
    [For, if possible, let the two similar and unequal segments of circles, $A C B$ and $A D B$, be constructed on the same side of the same straight-line $A B$. And let $A C D$ be drawn through (the segments), and let $C B$ and $D B$ be joined.],
  )
  #parallel-image("/Book03/fig23", 1.25in)
  #parallel(
    [Ἐπεὶ οὖν ὅμοιόν ἐστι τὸ ΑΓΒ τμῆμα τῷ ΑΔΒ τμήματι, ὅμοια δὲ τμήματα κύκλων ἐστὶ τὰ δεχόμενα γωνίας ἴσας, ἴση ἄρα ἐστὶν ἡ ὑπὸ ΑΓΒ γωνία τῇ ὑπὸ ΑΔΒ ἡ ἐκτὸς τῇ ἐντός· ὅπερ ἐστὶν ἀδύνατον.],
    [Therefore, since segment $A C B$ is similar to segment $A D B$, and similar segments of circles are those accepting equal angles [Def.~3.11], angle $A C B$ is thus equal to $A D B$, the external to the internal. The very thing is impossible [Prop.~1.16].],
  )
  #parallel(
    [Οὐκ ἄρα ἐπὶ τῆς αὐτῆς εὐθείας δύο τμήματα κύκλων ὅμοια καὶ ἄνισα συσταθήσεται ἐπὶ τὰ αὐτὰ μέρη· ὅπερ ἔδει δεῖξαι.],
    [Thus, two similar and unequal segments of circles cannot be constructed on the same side of the same straight-line.],
  )
]
#lean-proof("/lean/Elements/Book3/Prop23.lean")
