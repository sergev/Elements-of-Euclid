#import "../functions.typ": *

#content-box[
  #parallel-proposition(10)
  #parallel(
    [Τῶν πρὸς τὸ αὐτὸ λόγον ἐχόντων τὸ μείζονα λόγον ἔχον ἐκεῖνο μεῖζόν ἐστιν· πρὸς ὃ δὲ τὸ αὐτὸ μείζονα λόγον ἔχει, ἐκεῖνο ἔλαττόν ἐστιν.],
    [For (magnitudes) having a ratio to the same (magnitude), that (magnitude which) has the greater ratio is (the) greater. And that (magnitude) to which the latter (magnitude) has a greater ratio is (the) lesser.],
  )
  #parallel-image("/Book05/fig10", 0.5in)
  #parallel(
    [Ἐχέτω γὰρ τὸ Α πρὸς τὸ Γ μείζονα λόγον ἤπερ τὸ Β πρὸς τὸ Γ· λέγω, ὅτι μεῖζόν ἐστι τὸ Α τοῦ Β.],
    [For let $A$ have a greater ratio to $C$ than $B$ (has) to $C$. I say that $A$ is greater than $B$.],
  )
  #parallel(
    [Εἰ γὰρ μή, ἤτοι ἴσον ἐστὶ τὸ Α τῷ Β ἢ ἔλασσον. ἴσον μὲν οὖν οὔκ ἐστὶ τὸ Α τῷ Β· ἑκάτερον γὰρ ἂν τῶν Α, Β πρὸς τὸ Γ τὸν αὐτὸν εἶχε λόγον. οὐκ ἔχει δέ· οὐκ ἄρα ἴσον ἐστὶ τὸ Α τῷ Β. οὐδὲ μὴν ἔλασσόν ἐστι τὸ Α τοῦ Β· τὸ Α γὰρ ἂν πρὸς τὸ Γ ἐλάσσονα λόγον εἶχεν ἤπερ τὸ Β πρὸς τὸ Γ. οὐκ ἔχει δέ· οὐκ ἄρα ἔλασσόν ἐστι τὸ Α τοῦ Β. ἐδείχθη δὲ οὐδὲ ἴσον· μεῖζον ἄρα ἐστὶ τὸ Α τοῦ Β.],
    [For if not, $A$ is surely either equal to or less than $B$. In fact, $A$ is not equal to $B$. For (then) $A$ and $B$ would each have the same ratio to $C$ [Prop.~5.7]. But they do not. Thus, $A$ is not equal to $B$. Neither, indeed, is $A$ less than $B$. For (then) $A$ would have a lesser ratio to $C$ than $B$ (has) to $C$ [Prop.~5.8]. But it does not. Thus, $A$ is not less than $B$. And it was shown not (to be) equal either. Thus, $A$ is greater than $B$.],
  )
  #parallel(
    [Ἐχέτω δὴ πάλιν τὸ Γ πρὸς τὸ Β μείζονα λόγον ἤπερ τὸ Γ πρὸς τὸ Α· λέγω, ὅτι ἔλασσόν ἐστι τὸ Β τοῦ Α.],
    [So, again, let $C$ have a greater ratio to $B$ than $C$ (has) to $A$. I say that $B$ is less than $A$.],
  )
  #parallel(
    [Εἰ γὰρ μή, ἤτοι ἴσον ἐστὶν ἢ μεῖζον. ἴσον μὲν οὖν οὔκ ἐστι τὸ Β τῷ Α· τὸ Γ γὰρ ἂν πρὸς ἑκάτερον τῶν Α, Β τὸν αὐτὸν εἶχε λόγον. οὐκ ἔχει δέ· οὐκ ἄρα ἴσον ἐστὶ τὸ Α τῷ Β. οὐδὲ μὴν μεῖζόν ἐστι τὸ Β τοῦ Α· τὸ Γ γὰρ ἂν πρὸς τὸ Β ἐλάσσονα λόγον εἶχεν ἤπερ πρὸς τὸ Α. οὐκ ἔχει δέ· οὐκ ἄρα μεῖζόν ἐστι τὸ Β τοῦ Α. ἐδείχθη δέ, ὅτι οὐδὲ ἴσον· ἔλαττον ἄρα ἐστὶ τὸ Β τοῦ Α.],
    [For if not, (it is) surely either equal or greater. In fact, $B$ is not equal to $A$. For (then) $C$ would have the same ratio to each of $A$ and $B$ [Prop.~5.7]. But it does not. Thus, $A$ is not equal to $B$. Neither, indeed, is $B$ greater than $A$. For (then) $C$ would have a lesser ratio to $B$ than (it has) to $A$ [Prop.~5.8]. But it does not. Thus, $B$ is not greater than $A$. And it was shown that (it is) not equal (to $A$) either. Thus, $B$ is less than $A$.],
  )
  #parallel(
    [Τῶν ἄρα πρὸς τὸ αὐτὸ λόγον ἐχόντων τὸ μείζονα λόγον ἔχον μεῖζόν ἐστιν· καὶ πρὸς ὃ τὸ αὐτὸ μείζονα λόγον ἔχει, ἐκεῖνο ἔλαττόν ἐστιν· ὅπερ ἔδει δεῖξαι.],
    [Thus, for (magnitudes) having a ratio to the same (magnitude), that (magnitude which) has the greater ratio is (the) greater. And that (magnitude) to which the latter (magnitude) has a greater ratio is (the) lesser. (Which is) the very thing it was required to show.],
  )
]
#lean-proof("/lean/Elements/Book5/Prop10.lean")
