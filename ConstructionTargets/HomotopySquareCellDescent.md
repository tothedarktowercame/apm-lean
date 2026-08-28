# Common-coordinate descent around grid cells

This target transports the labelled cell-boundary homotopy into the common
object coordinates of `TwoOpenDescentDatum.mapPath`.  The resulting
`cell_mapPath_square` says that bottom followed by right equals left followed
by top.  `shared_vertical_mapPath_eq` proves that adjacent cell labels assign
the same common-coordinate morphism to their shared vertical edge, using the
datum's overlap equation when the labels differ.

The next step is to identify the horizontal terms with the mapped pieces of
the bottom and top row subdivisions and telescope these local squares with
`composeFin`, leaving only the two structural endpoint vertical morphisms.
